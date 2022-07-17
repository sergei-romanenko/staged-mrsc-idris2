module SMRSC.Protocols.Firefly

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

Firefly : CountersWorld
Firefly =
  let
    k = 4

    start : Conf 4
    start = [ω, ^0, ^0, ^0]

    rules : (c : Conf 4) -> List ((Bool, Lazy (Conf 4)))
    rules [i, e, s, d] = [
        -- rm1
        (i >=^ 1 && d =^ 0 && s =^ 0 && e =^ 0,
            [i - ^1, ^1, ^0, ^0]),
        -- rm2
        (i >=^ 1 && d >=^ 1,
            [i - ^1, e, s + ^2, d - ^1]),
        -- rm3
        (i >=^ 1 && s + e >=^ 1,
            [i - ^1, ^0, s + e + ^1, d]),
        -- wh2
        (e >=^ 1,
            [i, e - ^1, s, d + ^1]),
        -- wh3
        (s =^ 1,
            [i, e + ^1, ^0, d]),
        -- wm
        (i >=^ 1,
            [i + e + d + s - ^1, ^0, ^0, ^1])]

    unsafe : (c : Conf 4) -> Bool
    unsafe [i, e, s, d] =
        (d >=^ 1 && s + e >=^ 1) || (e >=^ 2) || (d >=^ 2)


  in MkCountersWorld 4 start rules unsafe

expected : String
expected = """
Firefly (2, 62)
|__[W, 0, 0, 0]
  |
  |__[W, 0, W, 0]
    |
    |__[W, 1, 0, 0]
      |
      |__[W, 0, 2, 0]*
      |
      |__[W, 0, 0, 1]
        |
        |__[W, 0, 2, 0]*
        |
        |__[W, 0, 0, 1]*
      |
      |__[W, 0, 0, 1]
        |
        |__[W, 0, 2, 0]*
        |
        |__[W, 0, 0, 1]*
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
        |__[W, 0, 0, 1]*
      |
      |__[W, 0, 0, 1]
        |
        |__[W, 0, 2, 0]*
        |
        |__[W, 0, 0, 1]*
    |
    |__[W, 0, 0, 1]
      |
      |__[W, 0, 2, 0]*
      |
      |__[W, 0, 0, 1]*
"""

export
runFirefly : IO ()
runFirefly = do
  assertEq "Firefly" (run_min_sc "Firefly" Firefly 3 10) expected

export
runFirefly8 : IO ()
runFirefly8 = do
  assertEq "Firefly" (run_min_sc8 "Firefly" Firefly 3 10) expected
