module SMRSC.Protocols.MSI

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

MSI : CountersWorld
MSI =
  let
    k = 3

    start : Conf 3
    start = [ω, ^0, ^0]

    rules : (c : Conf 3) -> List ((Bool, Lazy (Conf 3)))
    rules [i, m, s] = [
        (i >=^ 1, [i + m + s - ^1, ^1, ^0]),
        (s >=^ 1, [i + m + s - ^1, ^1, ^0]),
        (i >=^ 1, [i - ^1, ^0, m + s + ^1])]

    unsafe : (c : Conf 3) -> Bool
    unsafe [i, m, s] =
        (m >=^ 1 && s >=^ 1) || (m >=^ 2)

  in MkCountersWorld 3 start rules unsafe

expected : String
expected = """
MSI (3, 58)
|__[W, 0, 0]
  |
  |__[W, 0, W]
    |
    |__[W, 1, 0]
      |
      |__[W, 1, 0]*
      |
      |__[W, 0, 2]*
    |
    |__[W, 1, 0]
      |
      |__[W, 1, 0]*
      |
      |__[W, 0, 2]*
    |
    |__[W, 0, W]*
"""

export
runMSI : IO ()
runMSI = do
  assertEq "MSI" (run_min_sc "MSI" MSI 3 10) expected

export
runMSI8 : IO ()
runMSI8 = do
  assertEq "MSI" (run_min_sc8 "MSI" MSI 3 10) expected
