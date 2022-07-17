module SMRSC.Protocols.MOSI

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

MOSI : CountersWorld
MOSI =
  let
    k = 4

    start : Conf 4
    start = [ω, ^0, ^0, ^0]

    rules : (c : Conf 4) -> List ((Bool, Lazy (Conf 4)))
    rules [i, o, s, m] = [
        (i >=^ 1, [i - ^1, m + o, s + ^1, ^0]),
        (o >=^ 1, [i + o + s + m - ^1, ^0, ^0, ^1]),
        -- wI
        (i >=^ 1, [i + o + s + m - ^1, ^0, ^0, ^1]),
        -- wS
        (s >=^ 1, [i + o + s + m - ^1, ^0, ^0, ^1]),
        -- se
        (s >=^ 1, [i + ^1, o, s - ^1, m]),
        -- wbm
        (m >=^ 1, [i + ^1, o, s, m - ^1]),
        -- wbo
        (o >=^ 1, [i + ^1, o - ^1, s, m])]

    unsafe : (c : Conf 4) -> Bool
    -- unsafe [i, m, s] =
    --     (m >=^ 1 && s >=^ 1) || (m >=^ 2)
    unsafe [i, o, s, m] =
        (o >=^ 2) || (m >=^ 2) || (s >=^ 1 && m >=^ 1)

  in MkCountersWorld 4 start rules unsafe

expected : String
expected = """
MOSI (459, 53802)
|__[W, 0, 0, 0]
  |
  |__[W, 0, W, 0]
    |
    |__[W, 0, W, 0]*
    |
    |__[W, 0, 0, 1]
      |
      |__[W, 1, 1, 0]
        |
        |__[W, 1, W, 0]
          |
          |__[W, 1, W, 0]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 1, W, 0]*
          |
          |__[W, 0, W, 0]*
      |
      |__[W, 0, 0, 1]*
      |
      |__[W, 0, 0, 0]*
    |
    |__[W, 0, 0, 1]
      |
      |__[W, 1, 1, 0]
        |
        |__[W, 1, W, 0]
          |
          |__[W, 1, W, 0]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 1, W, 0]*
          |
          |__[W, 0, W, 0]*
      |
      |__[W, 0, 0, 1]*
      |
      |__[W, 0, 0, 0]*
    |
    |__[W, 0, W, 0]*
"""

export
runMOSI : IO ()
runMOSI = do
  assertEq "MOSI" (run_min_sc "MOSI" MOSI 3 10) expected

export
runMOSI8 : IO ()
runMOSI8 = do
  assertEq "MOSI" (run_min_sc8 "MOSI" MOSI 3 10) expected
  -- putStrLn (run_min_sc8 "MOSI" MOSI 3 10)


