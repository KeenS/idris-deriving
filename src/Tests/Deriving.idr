module Tests.Deriving

import Test.Unit.Assertions
import Deriving

%language ElabReflection

data Janken = Gu | Choki | Pa

%runElab derive [Show, Eq] `{{Janken}}

data StringMaybe = Some String | None

data Result a b = Ok a | Err b

%runElab do
  derive [Show, Eq] `{{StringMaybe}}
  derive [Show, Eq] `{{Result}}

testShowJanken : IO ()
testShowJanken = do
  assertEquals (show Gu) "Gu"
  assertEquals (show Choki) "Choki"
  assertEquals (show Pa) "Pa"
  pure ()

testEqJanken : IO ()
testEqJanken = do
  assertTrue  $ Gu    == Gu
  assertTrue  $ Choki == Choki
  assertTrue  $ Pa    == Pa
  assertFalse $ Gu    == Choki
  assertFalse $ Choki == Gu
  assertFalse $ Choki == Pa
  assertFalse $ Pa    == Choki
  assertFalse $ Pa    == Gu
  assertFalse $ Gu    == Pa
  assertFalse $ Gu    /= Gu
  assertFalse $ Choki /= Choki
  assertFalse $ Pa    /= Pa
  assertTrue  $ Gu    /= Choki
  assertTrue  $ Choki /= Gu
  assertTrue  $ Choki /= Pa
  assertTrue  $ Pa    /= Choki
  assertTrue  $ Pa    /= Gu
  assertTrue  $ Gu    /= Pa
  pure ()

testShowStringMaybe : IO ()
testShowStringMaybe = do
  assertEquals (show $ Some "foo") "Some \"foo\""
  assertEquals (show None) "None"
  pure()

testEqStringMaybe : IO ()
testEqStringMaybe = do
  assertTrue  $ (Some "foo") == (Some "foo")
  assertFalse $ (Some "foo") == (Some "bar")
  assertTrue  $ None         == None
  assertFalse $ (Some "foo") == None
  assertFalse $ None         == (Some "foo")
  assertFalse $ (Some "foo") /= (Some "foo")
  assertTrue  $ (Some "foo") /= (Some "bar")
  assertFalse $ None         /= None
  assertTrue  $ (Some "foo") /= None
  assertTrue  $ None         /= (Some "foo")

  pure()

testShowResult : IO ()
testShowResult = do
  assertEquals (show $ the (Result String Int) $ Ok "foo") "Ok \"foo\""
  assertEquals (show $ the (Result String Int) $ Err 1)  "Err 1"
  pure()

testEqResult : IO ()
testEqResult = do
  let t = the (Result String Int)
  assertTrue  $ t (Ok "foo") == (Ok "foo")
  assertFalse $ t (Ok "foo") == (Ok "bar")
  assertTrue  $ t (Err 0)    == (Err 0)
  assertFalse $ t (Err 0)    == (Err 1)
  assertFalse $ t (Ok "foo") == (Err 0)
  assertFalse $ t (Err 0)    == (Ok "foo")
  assertFalse $ t (Ok "foo") /= (Ok "foo")
  assertTrue  $ t (Ok "foo") /= (Ok "bar")
  assertFalse $ t (Err 0)    /= (Err 0)
  assertTrue  $ t (Err 0)    /= (Err 1)
  assertTrue  $ t (Ok "foo") /= (Err 1)
  assertTrue  $ t (Err 0)    /= (Ok "foo")
  pure()

export
test : IO ()
test = do
  testShowJanken
  testShowStringMaybe
  testShowResult
  testEqJanken
  testEqStringMaybe
  testEqResult
