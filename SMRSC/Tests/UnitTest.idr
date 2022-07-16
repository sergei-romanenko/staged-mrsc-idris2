module SMRSC.Tests.UnitTest

%default total

public export
assertTrue: (msg: String) -> (actual : Bool) -> IO ()
assertTrue msg True = pure ()
assertTrue msg False = do
  putStrLn $ "=== assertTrue failed ==="
  putStrLn $ msg

public export
assertFalse: (msg: String) -> (actual : Bool) -> IO ()
assertFalse msg False = pure ()
assertFalse msg True = do
  putStrLn $ "=== assertFalse failed ==="
  putStrLn $ msg

public export
assertEq: (Show a, Eq a) => (msg: String) ->
  (actual : a) -> (expected: a) -> IO ()
assertEq msg actual expected with (actual == expected)
  _ | True  =
    pure ()
  _ | False =  do
    putStrLn $ "=== assertEq failed ==="
    putStrLn $ msg
    putStrLn $ "expected: "
    putStrLn $ show expected
    putStrLn $ "actual: "
    putStrLn $ show actual

public export
assertNotEq: (Show a, Eq a) => (msg: String) ->
  (actual : a) -> (expected: a) -> IO ()
assertNotEq msg actual given with (actual /= given)
  _| True  =
    pure ()
  _| False =  do
    putStrLn $ "=== assertNotEq failed ==="
    putStrLn $ msg
    putStrLn $ "given: "
    putStrLn $ show given
    putStrLn $ "actual: "
    putStrLn $ show actual
