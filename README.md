# WIP deriving facility for Idris

deriving statement implemented in `Elab` .

Currently, `Show` and `Eq` is supported.


```idris
import Deriving

%language ElabReflection

data Janken = Gu | Choki | Pa

%runElab derive [Show, Eq] `{{Janken}}

data StringMaybe = Some String | None

data Result a b = Ok a | Err b

%runElab do
  derive [Show, Eq] `{{StringMaybe}}
  derive [Show, Eq] `{{Result}}
```
