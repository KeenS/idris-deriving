module Tests.Deriving

import Test.Unit.Assertions
import Deriving

%language ElabReflection

data Janken = Gu | Choki | Pa

%runElab derive [Show] `{{Janken}}

data StringMaybe = Some String | None

%runElab derive [Show] `{{StringMaybe}}

testJanken : IO ()
testJanken = do
  assertEquals (show Gu) "Gu"
  assertEquals (show Choki) "Choki"
  assertEquals (show Pa) "Pa"
  pure ()

testStringMaybe : IO ()
testStringMaybe = do
  assertEquals (show $ Some "foo") "Some \"foo\""
  assertEquals (show None) "None"
  pure()

export
test : IO ()
test = do
  testJanken
  testStringMaybe
