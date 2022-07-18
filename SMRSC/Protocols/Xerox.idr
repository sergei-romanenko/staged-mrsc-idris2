module SMRSC.Protocols.Xerox

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

Xerox : CountersWorld
Xerox =
  let
    k = 5

    start : Conf 5
    start = [ω, ^0, ^0, ^0, ^0]

    rules : (c : Conf 5) -> List ((Bool, Lazy (Conf 5)))
    rules [i, sc, sd, d, e] = [
        -- (1) rm1
        (i >=^ 1 && d =^ 0 && sc =^ 0 && sd =^ 0 && e =^ 0,
            [i - ^1, ^0, ^0, ^0, ^1]),
        -- (2) rm2
        (i >=^ 1 && d + sc + e + sd >=^ 1,
            [i - ^1, sc + e + ^1, sd + d, ^0, ^0]),
        -- (3) wm1
        (i >=^ 1 && d =^ 0 && sc =^ 0 && sd =^ 0 && e =^ 0,
            [i - ^1, ^0, ^0, ^1, ^0]),
        -- (4) wm2
        (i >=^ 1 && d + sc + e + sd >=^ 1,
            [i - ^1, sc + e + ^1 + (sd + d), sd, ^0, ^0]),
        -- (5) wh1
        (d >=^ 1,
            [i + ^1, sc, sd, d - ^1, e]),
        -- (6) wh2
        (sc >=^ 1,
            [i + ^1, sc - ^1, sd, d, e]),
        -- (7) wh3
        (sd >=^ 1,
            [i + ^1, sc, sd - ^1, d, e]),
        -- (8) wh4
        (e >=^ 1,
            [i + ^1, sc, sd, d, e - ^1])]

    unsafe : (c : Conf 5) -> Bool
    unsafe [i, sc, sd, d, e] =
        (e >=^ 1 && (sc + sd) >=^ 1) ||
        (d >=^ 2) ||
        (e >=^ 2)

  in MkCountersWorld 5 start rules unsafe

expected : String
expected = """
Xerox (10305306, 1278733438)
|__[W, 0, 0, 0, 0]
  |
  |__[W, W, W, 0, 0]
    |
    |__[W, 0, 0, 0, 1]
      |
      |__[W, 2, 0, 0, 0]*
      |
      |__[W, 2, 0, 0, 0]*
      |
      |__[W, 0, 0, 0, 0]*
    |
    |__[W, W, W, 0, 0]*
    |
    |__[W, 0, 0, 1, 0]
      |
      |__[W, 1, 1, 0, 0]*
      |
      |__[W, 2, 0, 0, 0]*
      |
      |__[W, 0, 0, 0, 0]*
    |
    |__[W, W, W, 0, 0]*
    |
    |__[W, W, W, 0, 0]*
    |
    |__[W, W, W, 0, 0]*
"""

export
runXerox : IO ()
runXerox = do
  assertEq "Xerox" (run_min_sc "Xerox" Xerox 3 10) expected

export
runXerox8 : IO ()
runXerox8 = do
  assertEq "Xerox" (run_min_sc8 "Xerox" Xerox 3 10) expected
