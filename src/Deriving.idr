import Language.Reflection.Utils

showFQN : TTName -> String
showFQN (UN n) = n
showFQN (MN i s) = "{" ++ s ++ "_" ++ (show i) ++ "}"
showFQN (NS tn ns) = (concatWith "." ns) ++ "." ++ (showFQN tn)
-- showFQN (SN _) = "unsuported"
where
  concatWith : String -> List String -> String
  concatWith sep [] = ""
  concatWith sep [x] = x
  concatWith sep (x :: xs) = x ++ sep ++ (concatWith sep xs)

namespace CtorArg
  getFunArg : CtorArg -> FunArg
  getFunArg (CtorParameter funArg) = funArg
  getFunArg (CtorField funArg)     = funArg

namespace TyConArg
  getFunArg : TyConArg -> FunArg
  getFunArg (TyConParameter x) = x
  getFunArg (TyConIndex x) = x


makeTypeParameters : TTName -> Datatype -> Elab (List FunArg)
makeTypeParameters name dt = do
  let tyconArgs = map getFunArg $ tyConArgs dt
  let typeParameter = tyconArgs
  instanceParameter <- sequence $ map makeInstanceParameter tyconArgs
  pure $ typeParameter ++ instanceParameter
where
  makeInstanceParameter : FunArg -> Elab FunArg
  makeInstanceParameter (MkFunArg n type plicity erasure) = do
    inst <- gensym "inst"
    pure $ MkFunArg inst (RApp (Var name) (Var n)) plicity erasure

wrapWithParameters : Raw -> (List FunArg) -> Raw
wrapWithParameters  body args =
  foldl (\acc,arg => RApp acc (Var (name arg))) body args

wrapWithPatBind : Raw -> (List FunArg) -> Raw
wrapWithPatBind body args =
  foldl (\acc,arg => RBind (name arg) (PVar $ type arg) acc) body args

getInstanceFor : TTName -> TTName -> Raw -> Elab Raw
getInstanceFor fname ifc ty = do
    (inst, _) <- runElab (RApp (Var ifc) ty) $ do
      resolveTC fname
    -- TT -> Raw
    let Just inst = forget inst
    pure inst

genClause : TTName -> (TTName, List CtorArg, Raw) -> Elab (FunClause Raw)
genClause fname (cname, args, _) = do
  let NS (UN cnameStr) _ = cname
  let args = map getFunArg args
  -- show (Ctor x y ...)
  let funClause = wrapWithParameters (Var cname) args
  -- wrap with patbind
  let funClause = wrapWithPatBind (RApp (Var fname) funClause) args
  -- = "Ctor" ++ " " ++ (show x) ++ " " ++ (show y) ...
  showedArgs <- sequence $ map (\arg => showArg fname arg) args
  let funBody = foldl (\acc, arg => concat acc arg) (RConstant (Str cnameStr)) showedArgs
  -- wrap with patbind
  let funBody = wrapWithPatBind funBody args
  pure $ MkFunClause funClause funBody
where
  showArg : TTName -> FunArg -> Elab Raw
  showArg fname arg = do
    -- get the instance of `Show type`
    inst <- getInstanceFor fname `{{Prelude.Show.Show}} (type arg)
    -- `show type (instance of Show type) arg`
    pure (RApp (RApp (RApp (Var `{{Prelude.Show.show}}) (type arg)) inst) (Var (name arg)))
  concat : Raw -> Raw -> Raw
  concat l r =
    let fconcat = (Var `{{Prelude.Strings.(++)}}) in
    (RApp (RApp fconcat (RApp (RApp fconcat l) (RConstant (Str " "))))) r

genShow : TTName -> Datatype -> Elab TTName
genShow tname dt = do
  fshow <- gensym $ (showFQN tname) ++ ".show"
  let fshow = SN $ MethodN fshow
  x <- gensym "x"
  -- show : (x: name) -> String
  let ty = Declare fshow [MkFunArg x (Var tname) Explicit Erased] (RConstant StrType)
  clauses <- sequence $ map (genClause fshow) $ constructors dt
  let f = DefineFun fshow clauses
  declareType ty
  defineFunction f
  pure fshow

genShowPrec : TTName -> TTName -> Datatype -> Elab TTName
genShowPrec tname fshow dt = do
  fshowPrec <- gensym $ (showFQN tname) ++ ".showPrec"
  let fshowPrec = SN $ MethodN fshowPrec
  let prec = `{{Prelude.Show.Prec}}
  x <- gensym "x"
  ign <- gensym "ignore"
  -- showPrec : Prec -> name -> String
  let funParam = [MkFunArg ign (Var prec) Explicit Erased, MkFunArg x (Var tname) Explicit Erased]
  let ty = Declare fshowPrec funParam (RConstant StrType)
  -- showPrec _ x =
  let clauseArg  = wrapWithPatBind (wrapWithParameters (Var fshowPrec) funParam) funParam
  -- = show x
  let clauseBody = wrapWithPatBind (RApp (Var fshow) (Var x)) funParam
  let clause = MkFunClause clauseArg clauseBody
  let f = DefineFun fshowPrec [clause]
  declareType ty
  defineFunction f
  pure fshowPrec


export
deriveShow : TTName -> Datatype -> Elab ()
deriveShow name dt = do
  let ifc = `{{Prelude.Show.Show}}
  let inst = SN $ ImplementationN ifc [showFQN name]

  -- tyParams <- makeTypeParameters ifc dt

  -- define show
  fshow <- genShow name dt
  -- define showPrec
  fshowPrec <- genShowPrec name fshow dt

  -- get the constructor of Show
  ifcData <- lookupDatatypeExact ifc
  let [(ctor, _, _)] = constructors ifcData
  -- showInst : Show name
  let instTy = Declare inst [] (RApp (Var ifc) (Var name))
  -- showInst = ctor show showPrec
  let instClause = MkFunClause (Var inst) (RApp (RApp (RApp (Var ctor) (Var name)) (Var fshow)) (Var fshowPrec))
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

-- Show List -> ty -> Show ty -> Show List ty
-- Show Either -> String -> Int -> Show String -> Show Int -> Show (Either String Int)

export
Show : Deriver
Show = MkDeriver deriveShow
