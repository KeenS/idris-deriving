# WIP deriving facility for Idris

deriving statement implemented in `Elab` .

Currently, only show for non-generic types are supported.


```idris
import Deriving

%language ElabReflection

data Janken = Gu | Choki | Pa

%runElab derive [Show] `{{Janken}}

data StringMaybe = Some String | None

%runElab derive [Show] `{{StringMaybe}}
```
