module SMRSC.Protocols.Synapse

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

Synapse : CountersWorld
Synapse =
  let
    k = 3

    start : Conf 3
    start = [ω, ^ 0, ^ 0]

    rules : (c : Conf 3) -> List ((Bool, Lazy (Conf 3)))
    rules [i, d, v] = [
      (i >=^ 1, [i + d - ^1, ^0, v + ^1]),
      (v >=^ 1, [i + d + v - ^1, ^1, ^0]),
      (i >=^ 1, [i + d + v - ^1, ^1, ^0])]

    unsafe : (c : Conf 3) -> Bool
    unsafe [i, d, v] =
      (d >=^ 1) && (v >=^ 1) ||
      (d >=^ 2)

  in MkCountersWorld 3 start rules unsafe

-- bw : BarWhistle (Conf 3)
-- bw = cntWhistle 3 3 10 

-- sw : ScWorld (Conf 3)
-- sw = cntSc synapse

-- graph : LazyGraph (Conf 3)
-- graph = lazy_mrsc sw bw (synapse.start)

-- lu_graph : length_unroll Synapse.graph = 112020
-- lu_graph = Refl

-- su_graph : size_unroll Synapse.graph = (112020 , 4024002)
-- su_graph = Refl

-- graph_cl_unsafe : LazyGraph (Conf 3)
-- graph_cl_unsafe = cl_empty $ cl_unsafe synapse graph

-- Cographs

-- cograph : LazyGraph8 (Conf 3)
-- cograph = build_graph8 sw (synapse.start)

-- cograph_safe : LazyGraph8 (Conf 3)
-- cograph_safe = cl8_empty $ cl8_unsafe synapse cograph

-- cograph_pruned : LazyGraph (Conf 3)
-- cograph_pruned = cl_empty $ prune_graph8 bw cograph_safe

-- graph_cl_unsafe_eq_cograph_pruned : Synapse.graph_cl_unsafe = Synapse.cograph_pruned
-- graph_cl_unsafe_eq_cograph_pruned = Refl


-- Removing empty subtrees while pruning.

-- lgraph : LazyGraph (Conf 3)
-- lgraph = prune0_graph8 sw bw cograph_safe

-- graph_cl_unsafe_eq_lgraph :
--   Synapse.graph_cl_unsafe = Synapse.lgraph
-- graph_cl_unsafe_eq_lgraph = Refl

-- lu_lgraph : length_unroll lgraph = 5
-- lu_lgraph = Refl

-- su_lgraph : size_unroll Synapse.lgraph = (5 , 97)
-- su_lgraph = Refl

-- lgraph_min_size = cl_min_size lgraph

-- su_lgraph_min_size : size_unroll (snd Synapse.lgraph_min_size) = (1 , 9)
-- su_lgraph_min_size = Refl

-- graph_min_size : List (Graph (Conf 3))
-- graph_min_size = unroll (snd lgraph_min_size)

expected : String
expected = """
Synapse (5, 97)
|__[W, 0, 0]
  |
  |__[W, 0, W]
    |
    |__[W, 0, W]*
    |
    |__[W, 1, 0]
      |
      |__[W, 0, 1]*
      |
      |__[W, 1, 0]*
    |
    |__[W, 1, 0]
      |
      |__[W, 0, 1]*
      |
      |__[W, 1, 0]*
"""

export
runSynapse : IO ()
runSynapse = do
  assertEq "Synapse" (run_min_sc "Synapse" Synapse 3 10) expected

export
runSynapse8 : IO ()
runSynapse8 = do
  assertEq "Synapse" (run_min_sc8 "Synapse" Synapse 3 10) expected


