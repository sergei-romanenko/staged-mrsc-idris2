module SMRSC.Protocols.ReaderWriter

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

ReaderWriter : CountersWorld
ReaderWriter =
  let
    k = 6

    start : Conf 6
    start = [^1, ^0, ^0, ω, ^0, ^0]

    rules : (c : Conf 6) -> List ((Bool, Lazy (Conf 6)))
    rules [x2, x3, x4, x5, x6, x7] = [
        -- r1
        (x2 >=^ 1 && x4 =^ 0 && x7 >=^ 1,
            [x2 - ^1, x3 + ^1, ^0, x5, x6, x7]),
        -- r2
        (x2 >=^ 1 && x6 >=^ 1,
            [x2, x3, x4 + ^1, x5, x6 - ^1, x7]),
        -- r3
        (x3 >=^ 1,
            [x2 + ^1, x3 - ^1, x4, x5 + ^1, x6, x7]),
        -- r4
        (x4 >=^ 1,
            [x2, x3, x4 - ^1, x5 + ^1, x6, x7]),
        -- r5
        (x5 >=^ 1,
            [x2, x3, x4, x5 - ^1, x6 + ^1, x7]),
        -- r6
        (x5 >=^ 1,
            [x2, x3, x4, x5 - ^1, x6, x7 + ^1])]

    unsafe : (c : Conf 6) -> Bool
    unsafe [x2, x3, x4, x5, x6, x7] =
        x3 >=^ 1 && x4 >=^ 1

  in MkCountersWorld 6 start rules unsafe

{-
start(::ReaderWriter) = NW[1, 0, 0, w, 0, 0]

rules(x2, x3, x4, x5, x6, x7) = [
    -- r1
    (x2 >= 1 && x4 == 0 && x7 >= 1,
        [x2 - 1, x3 + 1, 0, x5, x6, x7]),
    -- r2
    (x2 >= 1 && x6 >= 1,
        [x2, x3, x4 + 1, x5, x6 - 1, x7]),
    -- r3
    (x3 >= 1,
        [x2 + 1, x3 - 1, x4, x5 + 1, x6, x7]),
    -- r4
    (x4 >= 1,
        [x2, x3, x4 - 1, x5 + 1, x6, x7]),
    -- r5
    (x5 >= 1,
        [x2, x3, x4, x5 - 1, x6 + 1, x7]),
    -- r6
    (x5 >= 1,
        [x2, x3, x4, x5 - 1, x6, x7 + 1])]

is_unsafe(::ReaderWriter, x2::NW, x3::NW, x4::NW, x5::NW, x6::NW, x7::NW) =
    x3 >= 1 && x4 >= 1
-}

expected : String
expected = """
ReaderWriter (17162103740292532125222854955793322242073110442773745557234656218557, 18687629337590216387521010926592513416567502580093009196654012828085572)
|__[1, 0, 0, W, 0, 0]
  |
  |__[1, 0, W, W, W, W]
    |
    |__[0, 1, 0, W, W, W]
      |
      |__[1, 0, 0, W, W, W]*
      |
      |__[0, 1, 0, W, W, W]*
      |
      |__[0, 1, 0, W, W, W]*
    |
    |__[1, 0, W, W, W, W]*
    |
    |__[1, 0, W, W, W, W]*
    |
    |__[1, 0, W, W, W, W]*
    |
    |__[1, 0, W, W, W, W]*
"""

export
runReaderWriter : IO ()
runReaderWriter = do
  assertEq "ReaderWriter" (run_min_sc "ReaderWriter" ReaderWriter 3 10) expected

export
runReaderWriter8 : IO ()
runReaderWriter8 = do
  assertEq "ReaderWriter" (run_min_sc8 "ReaderWriter" ReaderWriter 3 10) expected
