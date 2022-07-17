module SMRSC.Tests.Graphs

import SMRSC.Tests.UnitTest
import SMRSC.Util
import SMRSC.Graphs

ibad : (c:Nat) -> Bool
ibad c = c >= 100

g_back : Graph Nat
g_back = Back 1

g_forth : Graph Nat
g_forth = Forth 1 [Back 1]

g1 : Graph Nat
g1 =
  Forth 1 [
    Back 1,
    Forth 2 [
      Back 1,
      Back 2]]

g_bad_forth : Graph Nat
g_bad_forth =
  Forth 1 [
    Back 1,
    Forth 102 [
      Back 3,
      Back 4]]

g_bad_back : Graph Nat
g_bad_back =
  Forth 1 [
    Back 1,
    Forth 2 [
      Back 3,
      Back 104]]

l2 : LazyGraph Nat
l2 =
  Build 1 [
    [Build 2 [[Stop 1, Stop 2]] ],
    [Build 3 [[Stop 3, Stop 1]] ]]

gs2 : List (Graph Nat)
gs2 = [
  Forth 1 [Forth 2 [Back 1, Back 2]],
  Forth 1 [Forth 3 [Back 3, Back 1]]]

l_empty : LazyGraph Nat
l_empty =
  Build 1 [
    [Stop(2)],
    [Build 3 [
      [Stop 4, Empty]]]]

l_bad_build : LazyGraph Nat
l_bad_build =
  Build 1 [[
    Stop 1,
    Build 102 [[
      Stop(3), Stop(4)]]]]

l_bad_stop : LazyGraph Nat
l_bad_stop =
  Build 1 [[
    Stop 1,
    Build 2 [[
      Stop 3,
      Stop 104]]]]

l3 : LazyGraph Nat
l3 =
  Build 1 [
    [Build 2 [[
      Stop 1, Stop 2]]],
    [Build 3 [[
      Stop 4]]]]

test_graph_show : IO ()
test_graph_show = do
  assertEq "graph_show: g_back" (show g_back)
    "Back 1"
  assertEq "graph_show: g_forth" (show g_forth)
    "Forth 1 [Back 1]"
  assertEq "graph_show: g_back" (show g1)
    "Forth 1 [Back 1, Forth 2 [Back 1, Back 2]]"

test_graph_eq : IO ()
test_graph_eq = do
  assertEq    "graph_eq 1" (Back 1) (Back 1)
  assertNotEq "graph_eq 2" (Back 1) (Back 2)
  assertEq    "graph_eq 3" (Forth 1 [Back 1]) (Forth 1 [Back 1])
  assertNotEq "graph_eq 4" (Forth 1 [Back 1]) (Forth 2 [Back 1])
  assertNotEq "graph_eq 5" (Forth 1 [Back 1]) (Forth 1 [Back 2])

test_lgraph_eq : IO ()
test_lgraph_eq = do
  assertEq    "lgraph_eq 1" Empty (Empty {a = Nat})
  assertEq    "lgraph_eq 2" (Stop 1) (Stop 1)
  assertNotEq "lgraph_eq 3" (Stop 1) (Stop 2)
  assertEq    "lgraph_eq 4" (Build 1 [[Stop 1]]) (Build 1 [[Stop 1]])
  assertNotEq "lgraph_eq 5" (Build 1 [[Stop 1]]) (Build 2 [[Stop 1]])
  assertNotEq "lgraph_eq 6" (Build 1 [[Stop 1]]) (Build 1 [[Stop 2]])

test_unroll : IO ()
test_unroll = do
  assertEq "unroll 1" (unroll (Empty {a = Nat})) []
  assertEq "unroll 2" (unroll (Stop 100)) [Back 100]
  assertEq "unroll 3" (unroll l2) gs2

test_bad_graph : IO ()
test_bad_graph = do
  assertFalse "bad_graph 1" (bad_graph ibad g1)
  assertTrue  "bad_graph 2" (bad_graph ibad g_bad_forth)
  assertTrue  "bad_graph 3" (bad_graph ibad g_bad_back)

test_cl_empty : IO ()
test_cl_empty = do
  assertEq  "cl_empty 1" (cl_empty l_empty) (Build 1 [[Stop 2]])

test_cl_bad_conf : IO ()
test_cl_bad_conf = do
  assertEq  "cl_bad_conf 1" (cl_bad_conf ibad l_bad_build)
    (Build 1 [[Stop 1, Empty]])
  assertEq  "cl_bad_conf 2" (cl_bad_conf ibad l_bad_stop)
    (Build 1 [[Stop 1, Build 2 [[Stop 3, Empty]]]])

test_cl_empty_and_bad : IO ()
test_cl_empty_and_bad = do
  assertEq  "cl_empty_and_bad 1" (cl_empty_and_bad ibad l_bad_build) Empty
  assertEq  "cl_empty_and_bad 2" (cl_empty_and_bad ibad l_bad_stop) Empty

test_graph_size : IO ()
test_graph_size = do
  assertEq  "graph_size 1" (graph_size g1) 5

test_cl_min_size : IO ()
test_cl_min_size = do
  assertEq  "cl_min_size 1" (cl_min_size l3)
    (5, Build 1 [[Build 3 [[Stop 4]]]])

test_cl_min_size_unroll : IO ()
test_cl_min_size_unroll = do
  let min_l = snd (cl_min_size l3)
  let min_g = unroll min_l
  assertEq "cl_min_size_unroll 1" min_g [Forth 1 [Forth 3 [Back 4]]]

test_graph_cartesian : IO ()
test_graph_cartesian = do
  assertEq  "graph_cartesian 1" (cartesian {a = Graph Nat} []) [[]]
  assertEq  "graph_cartesian 2" (cartesian {a = Graph Nat} [[]]) []
  assertEq  "graph_cartesian 3" (cartesian [[Back 1, Back 2]])
    [[Back 1], [Back 2]]
  assertEq  "graph_cartesian 4" (cartesian [[Back 1], []]) []
  assertEq  "graph_cartesian 5"
    (cartesian [[Back 1, Back 2], [Back 10, Back 20]])
    [
      [Back 1, Back 10], [Back 1, Back 20],
      [Back 2, Back 10], [Back 2, Back 20]
    ]

pp_graph : Graph Nat
pp_graph =
  Forth 100 [
    Forth 101 [Back 100],
    Forth 102 [Forth 101 [Back 100]]]

pp_string : String
pp_string = """
|__100
  |
  |__101
    |
    |__100*
  |
  |__102
    |
    |__101
      |
      |__100*
"""

test_pp : IO ()
test_pp =
  assertEq "graph_pp 1" (graph_pp pp_graph) pp_string

export
runGraphs : IO ()
runGraphs = do
  test_graph_show
  test_graph_eq
  test_lgraph_eq
  test_unroll
  test_bad_graph
  test_cl_empty
  test_cl_bad_conf
  test_cl_empty_and_bad
  test_graph_size
  test_cl_min_size
  test_cl_min_size_unroll
  test_graph_cartesian
  test_pp
