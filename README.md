# WIP deriving facility for Idris

deriving statement implemented in `Elab` .

Currently, only `Show` is supported.


```idris
import Deriving

%language ElabReflection

data Janken = Gu | Choki | Pa

%runElab derive [Show] `{{Janken}}

data StringMaybe = Some String | None
data Result a b = Ok a | Err b

%runElab do
  derive [Show] `{{StringMaybe}}
  derive [Show] `{{Result}}
```
