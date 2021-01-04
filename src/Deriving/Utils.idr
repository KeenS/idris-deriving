module Deriving.Utils

import Language.Reflection.Utils

%access export

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


