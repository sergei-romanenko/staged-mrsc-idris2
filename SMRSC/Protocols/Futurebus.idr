module SMRSC.Protocols.Futurebus

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

Futurebus : CountersWorld
Futurebus =
  let
    k = 9

    start : Conf 9
    start = [ω, ^0, ^0, ^0, ^0, ^0, ^0, ^0, ^0]

    rules : (c : Conf 9) -> List ((Bool, Lazy (Conf 9)))
    rules [i, sU, eU, eM, pR, pW, pEMR, pEMW, pSU] = [
        -- r2
        (i >=^ 1 && pW =^ 0,
            [i - ^1, ^0, ^0, ^0, pR + ^1, pW, pEMR + eM, pEMW, pSU + sU + eU]),
        -- r3
        (pEMR >=^ 1,
            [i, sU + pR + ^1, eU, eM, ^0, pW, pEMR - ^1, pEMW, pSU]),
        -- r4
        (pSU >=^ 1,
            [i, sU + pR + pSU, eU, eM, ^0, pW, pEMR, pEMW, ^0]),
        -- r5
        (pR >=^ 2 && pSU =^ 0 && pEMR =^ 0,
            [i, sU + pR, eU, eM, ^0, pW, ^0, pEMW, ^0]),
        -- r6
        (pR =^ 1 && pSU =^ 0 && pEMR =^ 0,
            [i, sU, eU + ^1, eM, ^0, pW, ^0, pEMW, ^0]),
        -- wm1
        (i >=^ 1 && pW =^ 0,
            [i + eU + sU + pSU + pR + pEMR - ^1, ^0, ^0, ^0, ^0, ^1, ^0, pEMW + eM, ^0]),
        -- wm2
        (pEMW >=^ 1,
            [i + ^1, sU, eU, eM + pW, pR, ^0, pEMR, pEMW - ^1, pSU]),
        -- wm3
        (pEMW =^ 0,
            [i, sU, eU, eM + pW, pR, ^0, pEMR, ^0, pSU]),
        -- wh2
        (eU >=^ 1,
            [i, sU, eU - ^1, eM + ^1, pR, pW, pEMR, pEMW, pSU]),
        -- wh2
        (sU >=^ 1,
            [i + sU - ^1, ^0, eU, eM + ^1, pR, pW, pEMR, pEMW, pSU])]

    unsafe : (c : Conf 9) -> Bool
    unsafe [i, sU, eU, eM, pR, pW, pEMR, pEMW, pSU] =
        (sU >=^ 1 && eU + eM >=^ 1) ||
        (eU + eM >=^ 2) ||
        (pR >=^ 1 && pW >=^ 1) ||
        (pW >=^ 2)

  in MkCountersWorld 9 start rules unsafe

expected : String
expected = """
Futurebus (71919064, 20136186996)
|__[W, 0, 0, 0, 0, 0, 0, 0, 0]
  |
  |__[W, W, 0, 0, 0, 0, 0, 0, 0]
    |
    |__[W, 0, 0, 0, 1, 0, 0, 0, W]
      |
      |__[W, 0, 0, 0, W, 0, 0, 0, W]
        |
        |__[W, 0, 0, 0, W, 0, 0, 0, W]*
        |
        |__[W, W, 0, 0, 0, 0, 0, 0, 0]*
        |
        |__[W, W, 0, 0, 0, 0, 0, 0, 0]*
        |
        |__[W, 0, 1, 0, 0, 0, 0, 0, 0]
          |
          |__[W, 0, 0, 0, 1, 0, 0, 0, 1]*
          |
          |__[W, 0, 0, 0, 0, 1, 0, 0, 0]
            |
            |__[W, 0, 0, 1, 0, 0, 0, 0, 0]
              |
              |__[W, 0, 0, 0, 1, 0, 1, 0, 0]
                |
                |__[W, 0, 0, 0, W, 0, 1, 0, 0]
                  |
                  |__[W, 0, 0, 0, W, 0, 1, 0, 0]*
                  |
                  |__[W, W, 0, 0, 0, 0, 0, 0, 0]*
                  |
                  |__[W, 0, 0, 0, 0, 1, 0, 0, 0]*
                  |
                  |__[W, 0, 0, 0, W, 0, 1, 0, 0]*
              |
              |__[W, 0, 0, 0, 0, 1, 0, 1, 0]
                |
                |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
              |
              |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
          |
          |__[W, 0, 1, 0, 0, 0, 0, 0, 0]*
          |
          |__[W, 0, 0, 1, 0, 0, 0, 0, 0]
            |
            |__[W, 0, 0, 0, 1, 0, 1, 0, 0]
              |
              |__[W, 0, 0, 0, W, 0, 1, 0, 0]
                |
                |__[W, 0, 0, 0, W, 0, 1, 0, 0]*
                |
                |__[W, W, 0, 0, 0, 0, 0, 0, 0]*
                |
                |__[W, 0, 0, 0, 0, 1, 0, 0, 0]
                  |
                  |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
                |
                |__[W, 0, 0, 0, W, 0, 1, 0, 0]*
            |
            |__[W, 0, 0, 0, 0, 1, 0, 1, 0]
              |
              |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
            |
            |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
        |
        |__[W, 0, 0, 0, 0, 1, 0, 0, 0]
          |
          |__[W, 0, 0, 1, 0, 0, 0, 0, 0]
            |
            |__[W, 0, 0, 0, 1, 0, 1, 0, 0]
              |
              |__[W, 0, 0, 0, W, 0, 1, 0, 0]
                |
                |__[W, 0, 0, 0, W, 0, 1, 0, 0]*
                |
                |__[W, W, 0, 0, 0, 0, 0, 0, 0]*
                |
                |__[W, 0, 0, 0, 0, 1, 0, 0, 0]*
                |
                |__[W, 0, 0, 0, W, 0, 1, 0, 0]*
            |
            |__[W, 0, 0, 0, 0, 1, 0, 1, 0]
              |
              |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
            |
            |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
        |
        |__[W, 0, 0, 0, W, 0, 0, 0, W]*
    |
    |__[W, 0, 0, 0, 0, 1, 0, 0, 0]
      |
      |__[W, 0, 0, 1, 0, 0, 0, 0, 0]
        |
        |__[W, 0, 0, 0, 1, 0, 1, 0, 0]
          |
          |__[W, 0, 0, 0, W, 0, 1, 0, 0]
            |
            |__[W, 0, 0, 0, W, 0, 1, 0, 0]*
            |
            |__[W, W, 0, 0, 0, 0, 0, 0, 0]*
            |
            |__[W, 0, 0, 0, 0, 1, 0, 0, 0]*
            |
            |__[W, 0, 0, 0, W, 0, 1, 0, 0]*
        |
        |__[W, 0, 0, 0, 0, 1, 0, 1, 0]
          |
          |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
        |
        |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
    |
    |__[W, W, 0, 0, 0, 0, 0, 0, 0]*
    |
    |__[W, 0, 0, 1, 0, 0, 0, 0, 0]
      |
      |__[W, 0, 0, 0, 1, 0, 1, 0, 0]
        |
        |__[W, 0, 0, 0, W, 0, 1, 0, 0]
          |
          |__[W, 0, 0, 0, W, 0, 1, 0, 0]*
          |
          |__[W, W, 0, 0, 0, 0, 0, 0, 0]*
          |
          |__[W, 0, 0, 0, 0, 1, 0, 0, 0]
            |
            |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
          |
          |__[W, 0, 0, 0, W, 0, 1, 0, 0]*
      |
      |__[W, 0, 0, 0, 0, 1, 0, 1, 0]
        |
        |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
      |
      |__[W, 0, 0, 1, 0, 0, 0, 0, 0]*
"""

export
runFuturebus : IO ()
runFuturebus = do
  assertEq "Futurebus" (run_min_sc "Futurebus" Futurebus 3 10) expected

export
runFuturebus8 : IO ()
runFuturebus8 = do
  assertEq "Futurebus" (run_min_sc8 "Futurebus" Futurebus 3 10) expected
