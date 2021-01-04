module Deriving.Eq

import Deriving.Utils
import Language.Reflection.Utils
import Debug.Trace



ifc : TTName
ifc = `{{Prelude.Interfaces.Eq}}

genClause : TTName -> Datatype -> (TTName, List CtorArg, Raw) -> Elab (FunClause Raw)
genClause fname dt (cname, ctorArgs, _) = do
  let NS (UN cnameStr) _ = cname
  let ctorArgs1 = map getFunArg ctorArgs
  renamed <- renameAll (argsExceptTyConArgs ctorArgs1 dt)
  let ctorArgs2 = (argsOfTyConArgs ctorArgs1 dt) ++ renamed
  tyParams <- makeTypeParametersFrom ifc $ argsOfTyConArgs ctorArgs1 dt
  let tyVars = tyParams ++ (argsExceptTyConArgs ctorArgs1 dt) ++ (argsExceptTyConArgs ctorArgs2 dt)
  -- (Ctor x y ...)
  let ctor1 = wrapWithParameters (Var cname) ctorArgs1
  let ctor2 = wrapWithParameters (Var cname) ctorArgs2
  -- (=) (Ctor x y ...) (Ctor x y ...)
  let funClause = wrapWithPatBind (RApp (RApp (wrapWithParameters (Var fname) tyParams) ctor1) ctor2) tyVars
  -- perhaps we should test if the arg isn't erased too
  let effectiveArgs1 = filter (\arg => (type arg) /= RType) ctorArgs1
  let effectiveArgs2 = filter (\arg => (type arg) /= RType) ctorArgs2
  let effectiveArgs1 = map (\arg => (findIndex (\t => (type arg) == (Var (name t))) ctorArgs1, arg)) effectiveArgs1
  let effectiveArgs2 = map (\arg => (findIndex (\t => (type arg) == (Var (name t))) ctorArgs2, arg)) effectiveArgs2
  -- = "Ctor" ++ " " ++ (show x) ++ " " ++ (show y) ...
  eqedArgs <- sequence $ map (\((i, arg1), (_, arg2)) => eqArg i tyParams arg1 arg2) (zip effectiveArgs1 effectiveArgs2)
  let funBody = foldr (\arg, acc => land arg acc) (Var `{{Prelude.Bool.True}}) eqedArgs
  let funBody = wrapWithPatBind funBody tyVars
  pure $ MkFunClause funClause funBody
where
  eqArg : Maybe Nat -> List FunArg -> FunArg -> FunArg -> Elab Raw
  eqArg i tyParams arg1 arg2 = do
    -- get the instance of `Show type`
    inst <- case findInstanceFor i tyParams dt of
        Just name => pure (Var name)
        Nothing   => lookupInstanceFor fname ifc (type arg1)
    -- `(==) type (instance of Show type) arg`
    pure (RApp (RApp (RApp (RApp (Var `{{Prelude.Interfaces.(==)}}) (type arg1)) inst) (Var (name arg1))) (Var (name arg2)))
  delay : Raw -> Raw
  delay t =
    (RApp (RApp (RApp (Var `{{Delay}}) (Var `{{LazyValue}})) (Var `{{Prelude.Bool.Bool}})) t)
  land : Raw -> Raw -> Raw
  land l r =
    let fand = (Var `{{Prelude.Bool.(&&)}}) in
    (RApp (RApp fand l) (delay r))

genEq : TTName -> Datatype -> List FunArg -> Elab TTName
genEq tname dt tyParams = do
  feq <- gensym $ (showFQN tname) ++ ".(==)"
  let feq = SN $ MethodN feq
  x <- gensym "x"
  y <- gensym "y"
  -- (==) : (x: name) -> (y: name) -> Bool
  let ty = tyParams ++ [MkFunArg x (resultType dt) Explicit NotErased, MkFunArg y (resultType dt) Explicit NotErased]
  let tyDecl = Declare feq ty (Var `{{Prelude.Bool.Bool}})
  clauses <- sequence $ map (genClause feq dt) $ constructors dt
  -- (==) _ _ = False
  let params = ty
  let defaultClause = MkFunClause (wrapWithPatBind (wrapWithParameters (Var feq) params) params) (wrapWithPatBind (Var `{{Prelude.Bool.False}}) params)
  let f = DefineFun feq (clauses ++ [defaultClause])
  declareType tyDecl
  defineFunction f
  pure feq

genNeq : TTName -> TTName -> Datatype -> List FunArg -> Elab TTName
genNeq tname feq dt tyParams = do
  fneq <- gensym $ (showFQN tname) ++ ".(/=)"
  let fneq = SN $ MethodN fneq
  x <- gensym "x"
  y <- gensym "y"
  -- (/=) : (x: name) -> (y: name) -> Bool
  let funParam = tyParams ++ [MkFunArg x (resultType dt) Explicit NotErased, MkFunArg y (resultType dt) Explicit NotErased]
  let ty = Declare fneq funParam (Var `{{Prelude.Bool.Bool}})
  -- (/=) x y =
  let clauseArg  = wrapWithPatBind (wrapWithParameters (Var feq) funParam) funParam
  -- = not (x == y)
  let clauseBody = wrapWithPatBind (RApp (Var `{{Prelude.Bool.not}}) (RApp (RApp (wrapWithParameters (Var feq) tyParams) (Var x)) (Var y))) funParam
  let clause = MkFunClause clauseArg clauseBody
  let f = DefineFun fneq [clause]
  declareType ty
  defineFunction f
  pure fneq


export
deriveEq : TTName -> Datatype -> Elab ()
deriveEq name dt = do
  let inst = SN $ ImplementationN ifc [showFQN name]
  tyParams <- makeTypeParameters ifc dt

  -- define (==)
  feq <- genEq name dt tyParams
  -- define (/==)
  fneq <- genNeq name feq dt tyParams

  -- get the constructor of Eq
  ctor <- lookupCtorExact ifc
  -- eqInst : Eq name
  let instTy = Declare inst tyParams (RApp (Var ifc) (resultType dt))
  let clauseArg = (Var inst)
  let clauseArg = wrapWithPatBind (wrapWithParameters clauseArg tyParams) tyParams
  let feq  = wrapWithParameters (Var feq) tyParams
  let fneq = wrapWithParameters (Var fneq) tyParams
  let clauseBody = RApp (RApp (RApp (Var ctor) (resultType dt)) feq) fneq
  let clauseBody = wrapWithPatBind clauseBody tyParams
  let instClause = MkFunClause clauseArg clauseBody
  let instF = DefineFun inst [instClause]
  declareType instTy
  defineFunction instF
  -- register the instance to the interface DB
  addImplementation ifc inst

