module Deriving

import Deriving.Show

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
