module SMRSC.Statistics

import SMRSC.Util
import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc

%default total

--
-- Counting without generation
--

-- The main idea of staged supercompilation consists in
-- replacing the analysis of residual graphs with the analysis
-- of the program that generates the graphs.
--
-- Gathering statistics about graphs is just a special case of
-- such analysis. For example, it is possible to count the number of
-- residual graphs that would be produced without actually generating
-- the graphs.
--
-- Technically, we can define a function `length_unroll` that analyses
-- lazy graphs such that
--   length_unroll(l) == length(unroll(l))

-- length_unroll

mutual

  public export
  length_unroll : (l : LazyGraph a) -> Nat
  length_unroll Empty = 0
  length_unroll (Stop c) = 1
  length_unroll (Build c lss) = length_unroll_lss lss

  public export
  length_unroll_lss : (lss : List (List (LazyGraph a))) -> Nat
  length_unroll_lss [] = 0
  length_unroll_lss (ls :: lss) =
    length_unroll_ls ls + length_unroll_lss lss

  public export
  length_unroll_ls : (ls : List (LazyGraph a)) -> Nat
  length_unroll_ls [] = 1
  length_unroll_ls (l :: ls) = length_unroll l * length_unroll_ls ls

--
-- Counting nodes in collections of graphs
--
-- Let us find a function `size_unroll`, such that
--   size_unroll(l) == (length(unroll(l)) , sum (map (graph_size) (unroll(l))))
--

-- size_unroll

mutual

  public export
  size_unroll : (l : LazyGraph a) -> (Nat, Nat)
  size_unroll Empty = (0 , 0)
  size_unroll (Stop c) = (1, 1)
  size_unroll (Build c lss) = size_unroll_lss lss

  public export
  size_unroll_lss : (lss : List (List (LazyGraph a))) -> (Nat, Nat)
  size_unroll_lss [] = (0, 0)
  size_unroll_lss (ls :: lss) with (size_unroll_ls ls, size_unroll_lss lss)
    _ | ((k', n'), (k, n)) = (k' + k , k' + n' + n)

  public export
  size_unroll_ls : (ls : List (LazyGraph a)) -> (Nat, Nat)
  size_unroll_ls [] = ?size_unroll_ls_rhs_0
  size_unroll_ls (l:: ls) with (size_unroll l, size_unroll_ls ls)
    _ | ((k', n'), (k, n)) = (k' * k , k' * n + k * n')
