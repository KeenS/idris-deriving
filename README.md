# Deriving facility for Idris

Deriving statement implemented in `Elab` .
You can derive some interfaces for datatypes by ``%runElab derive [deriveName, ...] `{{dataType}}`` .

Currently, `Show` and `Eq` is supported.

Because this is implemented in Elaborator Reflaction, you must enabele ElabReflection by `%language ElabReflection` before writing `%runElab ...`.


```idris
import Deriving

-- enable ElabReflection
%language ElabReflection

data Janken = Gu | Choki | Pa

-- implement Show and Eq for Janken
%runElab derive [Show, Eq] `{{Janken}}

data StringMaybe = Some String | None

data Result a b = Ok a | Err b

-- implement Show and Eq for StringMaybe
-- and implement Show and Eq for Result a b
%runElab do
  derive [Show, Eq] `{{StringMaybe}}
  derive [Show, Eq] `{{Result}}
```

# Installation

``` idris
git clone https://github.com/KeenS/idris-deriving.git
cd idris-dervinig
idris --install deriving.ipkg
```

Then add `-p deriving` flag when compiling your modules.
