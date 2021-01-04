module Deriving.Show

import Deriving.Utils
import Language.Reflection.Utils
import Debug.Trace



ifc : TTName
ifc = `{{Prelude.Show.Show}}

genClause : TTName -> Datatype -> (TTName, List CtorArg, Raw) -> Elab (FunClause Raw)
genClause fname dt (cname, ctorArgs, _) = do
  let NS (UN cnameStr) _ = cname
  let ctorArgs = map getFunArg ctorArgs
  tyParams <- makeTypeParametersFrom ifc $ argsOfTyConArgs ctorArgs dt
  let tyVars = tyParams ++ (argsExceptTyConArgs ctorArgs dt)
  -- (Ctor x y ...)
  let ctor = wrapWithParameters (Var cname) ctorArgs
  -- show (Ctor x y ...)
  let funClause = wrapWithPatBind (RApp (wrapWithParameters (Var fname) tyParams) ctor) tyVars
  -- perhaps we should test if the arg isn't erased too
  let effectiveArgs = filter (\arg => (type arg) /= RType) ctorArgs
  let effectiveArgs = map (\arg => (findIndex (\t => (type arg) == (Var (name t))) ctorArgs, arg)) effectiveArgs
  -- = "Ctor" ++ " " ++ (show x) ++ " " ++ (show y) ...
  showedArgs <- sequence $ map (\(i, arg) => showArg i tyParams arg) effectiveArgs
  let funBody = foldl (\acc, arg => concat acc arg) (RConstant (Str cnameStr)) showedArgs
  let funBody = wrapWithPatBind funBody tyVars
  pure $ MkFunClause funClause funBody
where
  showArg : Maybe Nat -> List FunArg -> FunArg -> Elab Raw
  showArg i tyParams arg = do
    -- get the instance of `Show type`
    inst <- case findInstanceFor i tyParams dt of
        Just name => pure (Var name)
        Nothing   => lookupInstanceFor fname ifc (type arg)
    -- `show type (instance of Show type) arg`
    pure (RApp (RApp (RApp (Var `{{Prelude.Show.show}}) (type arg)) inst) (Var (name arg)))
  concat : Raw -> Raw -> Raw
  concat l r =
    let fconcat = (Var `{{Prelude.Strings.(++)}}) in
    (RApp (RApp fconcat (RApp (RApp fconcat l) (RConstant (Str " "))))) r

genShow : TTName -> Datatype -> List FunArg -> Elab TTName
genShow tname dt tyParams = do
  fshow <- gensym $ (showFQN tname) ++ ".show"
  let fshow = SN $ MethodN fshow
  x <- gensym "x"
  -- show : (x: name) -> String
  let ty = Declare fshow (tyParams ++ [MkFunArg x (resultType dt) Explicit NotErased]) (RConstant StrType)
  clauses <- sequence $ map (genClause fshow dt) $ constructors dt
  let f = DefineFun fshow clauses
  declareType ty
  defineFunction f
  pure fshow

genShowPrec : TTName -> TTName -> Datatype -> List FunArg -> Elab TTName
genShowPrec tname fshow dt tyParams = do
  fshowPrec <- gensym $ (showFQN tname) ++ ".showPrec"
  let fshowPrec = SN $ MethodN fshowPrec
  let prec = `{{Prelude.Show.Prec}}
  x <- gensym "x"
  ign <- gensym "ignore"
  -- showPrec : Prec -> name -> String
  let funParam = tyParams ++ [MkFunArg ign (Var prec) Explicit NotErased, MkFunArg x (resultType dt) Explicit NotErased]
  let ty = Declare fshowPrec funParam (RConstant StrType)
  -- showPrec _ x =
  let clauseArg  = wrapWithPatBind (wrapWithParameters (Var fshowPrec) funParam) funParam
  -- = show x
  let clauseBody = wrapWithPatBind (RApp (wrapWithParameters (Var fshow) tyParams) (Var x)) funParam
  let clause = MkFunClause clauseArg clauseBody
  let f = DefineFun fshowPrec [clause]
  declareType ty
  defineFunction f
  pure fshowPrec


export
deriveShow : TTName -> Datatype -> Elab ()
deriveShow name dt = do
  let inst = SN $ ImplementationN ifc [showFQN name]
  tyParams <- makeTypeParameters ifc dt

  -- define show
  fshow <- genShow name dt tyParams
  -- define showPrec
  fshowPrec <- genShowPrec name fshow dt tyParams

  -- get the constructor of Show
  ctor <- lookupCtorExact ifc
  -- showInst : Show name
  let instTy = Declare inst tyParams (RApp (Var ifc) (resultType dt))
  -- showInst = ctor show showPrec
  let clauseArg = (Var inst)
  let clauseArg = wrapWithPatBind (wrapWithParameters clauseArg tyParams) tyParams
  let fshow     = wrapWithParameters (Var fshow) tyParams
  let fshowPrec = wrapWithParameters (Var fshowPrec) tyParams
  let clauseBody = RApp (RApp (RApp (Var ctor) (resultType dt)) fshow) fshowPrec
  let clauseBody = wrapWithPatBind clauseBody tyParams
  let instClause = MkFunClause clauseArg clauseBody
  let instF = DefineFun inst [instClause]
  declareType instTy
  defineFunction instF
  -- register the instance to the interface DB
  addImplementation ifc inst

