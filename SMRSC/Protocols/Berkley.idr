module SMRSC.Protocols.Berkley

import Data.List
import Data.Vect

import SMRSC.Tests.UnitTest
import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Counters
import SMRSC.Cographs
import SMRSC.Statistics

%default total

Berkley : CountersWorld
Berkley =
  let
    k = 4

    start : Conf 4
    start = [ω, ^0, ^0, ^0]

    rules : (c : Conf 4) -> List ((Bool, Lazy (Conf 4)))
    rules [i, n, u, e] = [
        -- rm
        (i >=^ 1, [i - ^1, n + e, u + ^1, ^0]),
        -- wm
        (i >=^ 1, [i + n + u + e - ^1, ^0, ^0, ^1]),
        -- wh1
    (n + u >=^ 1, [i + n + u - ^1, ^0, ^0, e + ^1])]

    unsafe : (c : Conf 4) -> Bool
    unsafe [i, n, u, e] =
        (e >=^ 1 && u + n >=^ 1) || (e >=^ 2)

  in MkCountersWorld 4 start rules unsafe

expected : String
expected = """
Berkley (62247, 3135052)
|__[W, 0, 0, 0]
  |
  |__[W, W, W, 0]
    |
    |__[W, W, W, 0]*
    |
    |__[W, 0, 0, 1]
      |
      |__[W, 1, 1, 0]*
      |
      |__[W, 0, 0, 1]*
    |
    |__[W, 0, 0, 1]
      |
      |__[W, 1, 1, 0]*
      |
      |__[W, 0, 0, 1]*
"""

export
runBerkley : IO ()
runBerkley = do
  assertEq "Berkley" (run_min_sc "Berkley" Berkley 3 10) expected

export
runBerkley8 : IO ()
runBerkley8 = do
  assertEq "Berkley" (run_min_sc8 "Berkley" Berkley 3 10) expected
