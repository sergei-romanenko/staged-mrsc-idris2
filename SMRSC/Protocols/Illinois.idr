module SMRSC.Protocols.Illinois

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

Illinois : CountersWorld
Illinois =
  let
    k = 4

    start : Conf 4
    start = [ω, ^0, ^0, ^0]

    rules : (c : Conf 4) -> List ((Bool, Lazy (Conf 4)))
    rules [i, e, d, s] = [
        -- r2
        (i >=^ 1 && e =^ 0 && d =^ 0 && s =^ 0,
            [i - ^1, ^1, ^0, ^0]),
        -- r3
        (i >=^ 1 && d >=^ 1,
            [i - ^1, e, d - ^1, s + ^2]),
        -- r4
        (i >=^ 1 && s + e >=^ 1,
            [i - ^1, ^0, d, s + e + ^1]),
        -- r6
        (e >=^ 1,
            [i, e - ^1, d + ^1, s]),
        -- r7
        (s >=^ 1,
            [i + s - ^1, e, d + ^1, ^0]),
        -- r8
        (i >=^ 1,
            [i + e + d + s - ^1, ^0, ^1, ^0]),
        -- r9
        (d >=^ 1,
            [i + ^1, e, d - ^1, s]),
        -- r10
        (s >=^ 1,
            [i + ^1, e, d, s - ^1]),
        -- r11
        (e >=^ 1,
            [i + ^1, e - ^1, d, s])]

    unsafe : (c : Conf 4) -> Bool
    unsafe [i, e, d, s] =
        (d >=^ 1 && s >=^ 1) || (d >=^ 2)

  in MkCountersWorld 4 start rules unsafe

expected : String
expected = """
Illinois (2, 73)
|__[W, 0, 0, 0]
  |
  |__[W, 0, 0, W]
    |
    |__[W, 1, 0, 0]
      |
      |__[W, 0, 0, 2]*
      |
      |__[W, 0, 1, 0]
        |
        |__[W, 0, 0, 2]*
        |
        |__[W, 0, 1, 0]*
        |
        |__[W, 0, 0, 0]*
      |
      |__[W, 0, 1, 0]
        |
        |__[W, 0, 0, 2]*
        |
        |__[W, 0, 1, 0]*
        |
        |__[W, 0, 0, 0]*
      |
      |__[W, 0, 0, 0]*
    |
    |__[W, 0, 0, W]*
    |
    |__[W, 0, 1, 0]
      |
      |__[W, 0, 0, 2]*
      |
      |__[W, 0, 1, 0]*
      |
      |__[W, 0, 0, 0]*
    |
    |__[W, 0, 1, 0]
      |
      |__[W, 0, 0, 2]*
      |
      |__[W, 0, 1, 0]*
      |
      |__[W, 0, 0, 0]*
    |
    |__[W, 0, 0, W]*
"""

export
runIllinois : IO ()
runIllinois = do
  assertEq "Illinois" (run_min_sc "Illinois" Illinois 3 10) expected

export
runIllinois8 : IO ()
runIllinois8 = do
  assertEq "Illinois" (run_min_sc8 "Illinois" Illinois 3 10) expected
