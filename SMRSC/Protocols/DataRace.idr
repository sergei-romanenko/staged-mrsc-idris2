module SMRSC.Protocols.DataRace

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

DataRace : CountersWorld
DataRace =
  let
    k = 3

    start : Conf 3
    start = [ω, ^0, ^0]

    rules : (c : Conf 3) -> List ((Bool, Lazy (Conf 3)))
    rules [out, cs, scs] = [
        -- 1
        (out >=^ 1 && cs =^ 0 && scs =^ 0,
            [out - ^1, ^1, ^0]),
        -- 2
        (out >=^ 1 && cs =^ 0,
            [out - ^1, ^0, scs + ^1]),
        -- 3
        (cs >=^ 1,
            [out + ^1, cs - ^1, scs]),
        -- 4
        (scs >=^ 1,
            [out + ^1, cs, scs - ^1])]

    unsafe : (c : Conf 3) -> Bool
    unsafe [out, cs, scs] =
        cs >=^ 1 && scs >=^ 1

  in MkCountersWorld 3 start rules unsafe

expected : String
expected = """
DataRace (16, 237)
|__[W, 0, 0]
  |
  |__[W, 0, W]
    |
    |__[W, 1, 0]
      |
      |__[W, 0, 0]*
    |
    |__[W, 0, W]*
    |
    |__[W, 0, W]*
"""

export
runDataRace : IO ()
runDataRace = do
  assertEq "DataRace" (run_min_sc "DataRace" DataRace 3 10) expected

export
runDataRace8 : IO ()
runDataRace8 = do
  assertEq "DataRace" (run_min_sc8 "DataRace" DataRace 3 10) expected
