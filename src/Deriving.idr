import Language.Reflection.Utils
import Debug.Trace

showFQN : TTName -> String
showFQN (UN n) = n
showFQN (MN i s) = "{" ++ s ++ "_" ++ (show i) ++ "}"
showFQN (NS tn ns) = (concat $ intersperse "." ns) ++ "." ++ (showFQN tn)
-- showFQN (SN _) = "unsuported"

namespace CtorArg
  getFunArg : CtorArg -> FunArg
  getFunArg (CtorParameter funArg) = funArg
  getFunArg (CtorField funArg)     = funArg

namespace TyConArg
  getFunArg : TyConArg -> FunArg
  getFunArg (TyConParameter x) = x
  getFunArg (TyConIndex x) = x


makeTypeParametersFrom : TTName -> List FunArg -> Elab (List FunArg)
makeTypeParametersFrom ifc tyconArgs = do
  let typeParameter = map (record {plicity = Implicit}) tyconArgs
  instanceParameter <- sequence $ map makeInstanceParameter (reverse tyconArgs)
  pure $ typeParameter ++ instanceParameter
where
  makeInstanceParameter : FunArg -> Elab FunArg
  makeInstanceParameter arg = do
    inst <- gensym "inst"
    pure $ MkFunArg inst (RApp (Var ifc) (Var (name arg))) Constraint NotErased

makeTypeParameters : TTName -> Datatype -> Elab (List FunArg)
makeTypeParameters ifc dt = do
  let tyconArgs = map getFunArg $ tyConArgs dt
  makeTypeParametersFrom ifc (reverse tyconArgs)


wrapWithParameters : Raw -> (List FunArg) -> Raw
wrapWithParameters  body args =
  foldl (\acc,arg => RApp acc (Var (name arg))) body args

wrapWithPatBind : Raw -> (List FunArg) -> Raw
wrapWithPatBind body args =
  foldr (\arg,acc => RBind (name arg) (PVar $ type arg) acc) body args

||| query the instance of the interface to idris
lookupInstanceFor : TTName -> TTName -> Raw -> Elab Raw
lookupInstanceFor fname ifc ty = do
    (inst, _) <- runElab (RApp (Var ifc) ty) $ do
      resolveTC fname
    -- TT -> Raw
    let Just inst = forget inst
    pure inst

||| find an instance of the interface in listed arguments
findInstanceFor : Maybe Nat -> List FunArg -> Datatype-> Maybe TTName
findInstanceFor Nothing  _        dt = Nothing
findInstanceFor (Just i) tyParams dt =
  let pad = length $ tyConArgs dt in
  map name $ index' (minus (2 * pad)  (1 + i)) tyParams


lookupCtorExact : TTName -> Elab TTName
lookupCtorExact ifc = do
  ifcData <- lookupDatatypeExact ifc
  let [(ctor, _, _)] = constructors ifcData
  pure ctor

resultType : Datatype -> Raw
resultType (MkDatatype name tyConArgs tyConRes constructors) = wrapWithParameters (Var name) (map getFunArg tyConArgs)

argsOfTyConArgs : List FunArg -> Datatype -> List FunArg
argsOfTyConArgs args dt =
  let pad = length $ tyConArgs dt in
  take pad args

argsExceptTyConArgs : List FunArg -> Datatype -> List FunArg
argsExceptTyConArgs args dt =
  let pad = length $ tyConArgs dt in
  drop pad args



ifc : TTName
ifc = `{{Prelude.Show.Show}}

genClause : TTName -> Datatype -> (TTName, List CtorArg, Raw) -> Elab (FunClause Raw)
genClause fname dt (cname, ctorArgs, _) = do
  let NS (UN cnameStr) _ = cname
  let ctorArgs = map getFunArg ctorArgs
  tyParams <- makeTypeParametersFrom `{{Prelude.Show.Show}} $ argsOfTyConArgs ctorArgs dt
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


public export
data Deriver = MkDeriver (TTName -> Datatype -> Elab ())

export
derive : List Deriver -> TTName -> Elab ()
derive derivers name = do
  qname <- quorifyName name
  dt <- lookupDatatypeExact qname
  for_ {b=()} derivers $ \(MkDeriver d) => d qname dt
where
  quorifyName : TTName -> Elab TTName
  quorifyName (UN un) = do
    ns <- currentNamespace
    pure $ NS (UN un) ns
  quorifyName n = pure n

export
Show : Deriver
Show = MkDeriver deriveShow

-- hoge : Elab ()
-- hoge = ?hole
-- dt <- lookupDatatypeExact `{{Main.Result}}
-- tyParams <- makeTypeParameters ifc dt
-- let ctors = constructors dt
-- let ctor = index 0 ctors
-- let args = map getFunArg (fst (snd ctor))
-- let effectiveArgs = filter (\arg => (type arg) /= RType) args
-- let effectiveArgs = map (\arg => (findIndex (\t => (type arg) == (Var (name t))) args, arg)) effectiveArgs
-- let effectiveArg = index 0 effectiveArgs
-- let ret = findInstanceFor (fst effectiveArg) tyParams
-- inst <- lookupInstanceFor `{{hoge}} ifc (type (snd effectiveArg))
-- let body = (RApp (RApp (RApp (Var `{{Prelude.Show.show}}) (type (snd effectiveArg))) inst) (Var (name (snd effectiveArg))))
-- debug {a=()}
