module Tests.Deriving

import Test.Unit
import Test.Unit.Assertions
import Deriving
import System


%language ElabReflection

data Janken = Gu | Choki | Pa

%runElab derive [Show, Eq] `{{Janken}}

data StringMaybe = Some String | None

data Result a b = Ok a | Err b

%runElab do
  derive [Show, Eq] `{{StringMaybe}}
  derive [Show, Eq] `{{Result}}

exitIfFail : IO (List Bool) -> IO ()
exitIfFail action = do
  results <- action
  if not (all id results)
  then do
    putStrLn "Some tests failed"
    exit 1
  else pure ()


testShowJanken : IO ()
testShowJanken = exitIfFail $ runTests
  [assertEquals (show Gu) "Gu"
  , assertEquals (show Choki) "Choki"
  , assertEquals (show Pa) "Pa"
  ]


testEqJanken : IO ()
testEqJanken = exitIfFail $ runTests
  [ assertTrue  $ Gu    == Gu
  , assertTrue  $ Choki == Choki
  , assertTrue  $ Pa    == Pa
  , assertFalse $ Gu    == Choki
  , assertFalse $ Choki == Gu
  , assertFalse $ Choki == Pa
  , assertFalse $ Pa    == Choki
  , assertFalse $ Pa    == Gu
  , assertFalse $ Gu    == Pa
  , assertFalse $ Gu    /= Gu
  , assertFalse $ Choki /= Choki
  , assertFalse $ Pa    /= Pa
  , assertTrue  $ Gu    /= Choki
  , assertTrue  $ Choki /= Gu
  , assertTrue  $ Choki /= Pa
  , assertTrue  $ Pa    /= Choki
  , assertTrue  $ Pa    /= Gu
  , assertTrue  $ Gu    /= Pa
  ]

testShowStringMaybe : IO ()
testShowStringMaybe = exitIfFail $ runTests
  [ assertEquals (show $ Some "foo") "Some \"foo\""
  , assertEquals (show None) "None"
  ]

testEqStringMaybe : IO ()
testEqStringMaybe = exitIfFail $ runTests
  [ assertTrue  $ (Some "foo") == (Some "foo")
  , assertFalse $ (Some "foo") == (Some "bar")
  , assertTrue  $ None         == None
  , assertFalse $ (Some "foo") == None
  , assertFalse $ None         == (Some "foo")
  , assertFalse $ (Some "foo") /= (Some "foo")
  , assertTrue  $ (Some "foo") /= (Some "bar")
  , assertFalse $ None         /= None
  , assertTrue  $ (Some "foo") /= None
  , assertTrue  $ None         /= (Some "foo")
  ]

testShowResult : IO ()
testShowResult =
  let t = the (Result String Int) in
  exitIfFail $ runTests
  [ assertEquals (show $ t (Ok "foo")) "Ok \"foo\""
  , assertEquals (show $ t (Err 1))  "Err 1"
  ]

testEqResult : IO ()
testEqResult =
  let t = the (Result String Int) in
  exitIfFail $ runTests
  [ assertTrue  $ t (Ok "foo") == (Ok "foo")
  , assertFalse $ t (Ok "foo") == (Ok "bar")
  , assertTrue  $ t (Err 0)    == (Err 0)
  , assertFalse $ t (Err 0)    == (Err 1)
  , assertFalse $ t (Ok "foo") == (Err 0)
  , assertFalse $ t (Err 0)    == (Ok "foo")
  , assertFalse $ t (Ok "foo") /= (Ok "foo")
  , assertTrue  $ t (Ok "foo") /= (Ok "bar")
  , assertFalse $ t (Err 0)    /= (Err 0)
  , assertTrue  $ t (Err 0)    /= (Err 1)
  , assertTrue  $ t (Ok "foo") /= (Err 1)
  , assertTrue  $ t (Err 0)    /= (Ok "foo")
  ]

export
test : IO ()
test = do
  testShowJanken
  testShowStringMaybe
  testShowResult
  testEqJanken
  testEqStringMaybe
  testEqResult
