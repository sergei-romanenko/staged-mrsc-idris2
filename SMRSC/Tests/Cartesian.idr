module SMRSC.Tests.Cartesian

import SMRSC.Tests.UnitTest
import SMRSC.Util

%default total

testCartesian : (msg : String) ->
  (g : List (List Nat)) -> (e : List (List Nat)) -> IO ()
testCartesian msg g e =
  assertEq msg (cartesian g) e

export
runCartesian : IO ()
runCartesian = do
  testCartesian "cartesian0" [] [[]]
  testCartesian "cartesian1" [[], [10, 20]] []
  testCartesian "cartesian2" [[1, 2], []] []
  testCartesian "cartesian3" [[1, 2]]  [[1], [2]]
  testCartesian "cartesian4" [[1], [10, 20]] [[1, 10], [1, 20]]
  testCartesian "cartesian5"
    [[1, 2], [10, 20, 30], [100, 200]]
      [
        [1, 10, 100], [1, 10, 200],
        [1, 20, 100], [1, 20, 200],
        [1, 30, 100], [1, 30, 200],
        [2, 10, 100], [2, 10, 200],
        [2, 20, 100], [2, 20, 200],
        [2, 30, 100], [2, 30, 200]]
