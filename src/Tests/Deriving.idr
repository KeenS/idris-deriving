module Tests.Deriving

import Test.Unit.Assertions
import Deriving

%language ElabReflection

data Janken = Gu | Choki | Pa

%runElab derive [Show] `{{Janken}}

data StringMaybe = Some String | None

data Result a b = Ok a | Err b

%runElab do
  derive [Show] `{{StringMaybe}}
  derive [Show] `{{Result}}

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

testResult : IO ()
testResult = do
  assertEquals (show $ the (Result String Int) $ Ok "foo") "Ok \"foo\""
  assertEquals (show $ the (Result String Int) $ Err 1)  "Err 1"
  pure()

export
test : IO ()
test = do
  testJanken
  testStringMaybe
  testResult
