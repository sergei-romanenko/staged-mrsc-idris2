module SMRSC.Protocols.MESI

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

MESI : CountersWorld
MESI =
  let
    k = 4

    start : Conf 4
    start = [ω, ^0, ^0, ^0]

    rules : (c : Conf 4) -> List ((Bool, Lazy (Conf 4)))
    rules [i, e, s, m] = [
        (i >=^ 1, [i - ^1, ^0, s + e + m + ^1, ^0]),
        (e >=^ 1, [i, e - ^1, s, m + ^1]),
        (s >=^ 1, [i + e + s + m - ^1, ^1, ^0, ^0]),
        (i >=^ 1, [i + e + s + m - ^1, ^1, ^0, ^0])]

    unsafe : (c : Conf 4) -> Bool
    unsafe [i, e, s, m] =
        m >=^ 2 || (s >=^ 1 && m >=^ 1)

  in MkCountersWorld 4 start rules unsafe

expected : String
expected = """
MESI (3, 104)
|__[W, 0, 0, 0]
  |
  |__[W, 0, W, 0]
    |
    |__[W, 0, W, 0]*
    |
    |__[W, 1, 0, 0]
      |
      |__[W, 0, 2, 0]*
      |
      |__[W, 0, 0, 1]
        |
        |__[W, 0, 2, 0]*
        |
        |__[W, 1, 0, 0]*
      |
      |__[W, 1, 0, 0]*
    |
    |__[W, 1, 0, 0]
      |
      |__[W, 0, 2, 0]*
      |
      |__[W, 0, 0, 1]
        |
        |__[W, 0, 2, 0]*
        |
        |__[W, 1, 0, 0]*
      |
      |__[W, 1, 0, 0]*
"""

export
runMESI : IO ()
runMESI = do
  assertEq "MESI" (run_min_sc "MESI" MESI 3 10) expected

export
runMESI8 : IO ()
runMESI8 = do
  assertEq "MESI" (run_min_sc8 "MESI" MESI 3 10) expected
