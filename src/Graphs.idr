--
-- Graphs of configurations
--

module Graphs

import Util

%default total

%access public export

--
-- Graphs of configurations
--

-- A `Graph a` is supposed to represent a residual program.
-- Technically, a `Graph a` is a tree, with `back` nodes being
-- references to parent nodes.
--
-- A graph's nodes contain configurations. Here we abstract away
-- from the concrete structure of configurations.
-- In this model the arrows in the graph carry no information,
-- because this information can be kept in nodes.
-- (Hence, this information is supposed to be encoded inside
-- "configurations".)
--
-- To simplify the machinery, back-nodes in this model of
-- supercompilation do not contain explicit references
-- to parent nodes. Hence, `Back c` means that `c` is foldable
-- to a parent configuration (perhaps, to several ones).
--
-- * Back-nodes are produced by folding a configuration to another
--   configuration in the history.
-- * Forth-nodes are produced by
--     + decomposing a configuration into a number of other configurations
--       (e.g. by driving or taking apart a let-expression), or
--     + by rewriting a configuration by another one (e.g. by generalization,
--       introducing a let-expression or applying a lemma during
--       two-level supercompilation).

-- Graph

data Graph : (a : Type) -> Type where
  Back  : (c : a) -> Graph a
  Forth : (c : a) -> (gs : List (Graph a)) -> Graph a

%name Graph g,g1,g2,g3,g4 -- Name hints for interactive editing

--
-- Lazy graphs of configuration
--

-- A `LazyGraph a` represents a finite set of graphs
-- of configurations (whose type is `Graph a`).
--
-- "Lazy" graphs of configurations will be produced
-- by the "lazy" (staged) version of multi-result
-- supercompilation.

-- LazyGraph

data LazyGraph : (a : Type) -> Type where
  Empty : LazyGraph a
  Stop  : (c : a) -> LazyGraph a
  Build : (c : a) -> (lss : List (List (LazyGraph a))) -> LazyGraph a

%name LazyGraph l,l1,l2,l3,l4 -- Name hints for interactive editing

-- decEmpty

implementation Uninhabited (Empty = Stop c) where
  uninhabited Refl impossible

implementation Uninhabited (Empty = Build c lss) where
  uninhabited Refl impossible

decEmpty : (l : LazyGraph c) -> Dec (Empty = l)
decEmpty Empty = Yes Refl
decEmpty (Stop c) = No absurd
decEmpty (Build c lss) = No absurd

-- The semantics of a `LazyGraph a` is formally defined by
-- the interpreter `unroll` that generates a list of `Graph a` from
-- the `LazyGraph a` by executing commands recorded in the `LazyGraph a`.

mutual

  unroll : (l : LazyGraph a) -> List (Graph a)
  unroll Empty = []
  unroll (Stop c) = [ Back c ]
  unroll (Build c lss) =
    map (Forth c) (concatMap (cartesian . (map (assert_total unroll))) lss)

--
-- Usually, we are not interested in the whole bag `unroll l`.
-- The goal is to find "the best" or "most interesting" graphs.
-- Hence, there should be developed some techniques of extracting
-- useful information from a `LazyGraph C` without evaluating
-- `unroll l` directly.

-- This can be formulated in the following form.
-- Suppose that a function `select` filters bags of graphs,
-- removing "bad" graphs, so that
--
--     select (unroll l)
--
-- generates the bag of "good" graphs.
-- Let us find a function `extract` such that
--
--     extract l = select (unroll l)
--
-- In many cases, `extract` may be more efficient (by several orders
-- of magnitude) than the composition `select . unroll`.

-- Sometimes, `extract` can be formulated in terms of "cleaners" of
-- lazy graphs. Let `clean` be a function that transforms lazy graphs,
-- such that
--
--     unroll (clean l) ⊆ unroll l
--
-- Then `extract` can be constructed in the following way:
--
--     extract l = unroll (clean l)
--
-- Theoretically speaking, `clean` is the result of "promoting" `select`:
--
--     select . unroll ≗ unroll . clean
--
-- The nice property of cleaners is that they are composable:
-- given `clean₁` and `clean₂`, `clean₂ . clean₁` is also a cleaner.
--

--
-- Some filters
--

-- Removing graphs that contain "bad" configurations.
-- Configurations represent states of a computation process.
-- Some of these states may be "bad" with respect to the problem
-- that is to be solved by means of supercompilation.

mutual

  bad_graph : (bad : a -> Bool) -> (g : Graph a) -> Bool
  bad_graph bad (Back c) = bad c
  bad_graph bad (Forth c gs) =
    bad c || bad_graphs bad gs

  bad_graphs : (bad : a -> Bool) -> (gs : List (Graph a)) -> Bool
  bad_graphs bad [] = False
  bad_graphs bad (g :: gs) =
    bad_graph bad g || bad_graphs bad gs

-- This filter removes the graphs containing "bad" configurations.

fl_bad_conf : (bad : a -> Bool) -> (gs : List (Graph a)) -> List (Graph a)
fl_bad_conf bad gs = filter (not . bad_graph bad) gs

--
-- Some cleaners
--

-- `cl_empty` removes subtrees that represent empty sets of graphs.

cl_empty_build : (c : a) -> List (List (LazyGraph a)) -> LazyGraph a
cl_empty_build c [] = Empty
cl_empty_build c (ls :: lss) = Build c (ls :: lss)

mutual

  cl_empty : (l : LazyGraph a) -> LazyGraph a
  cl_empty Empty = Empty
  cl_empty (Stop c) = Stop c
  cl_empty (Build c lss) = cl_empty_build c (cl_empty2 lss)

  cl_empty2 : (lss : List (List (LazyGraph a))) ->  List (List (LazyGraph a))
  cl_empty2 [] = []
  cl_empty2 (ls :: lss) with (cl_empty1 ls)
    | Nothing = cl_empty2 lss
    | (Just ls') = ls' :: cl_empty2 lss

  cl_empty1 : (ls : List (LazyGraph a)) -> Maybe (List (LazyGraph a))
  cl_empty1 [] = Just []
  cl_empty1 (l :: ls) with (cl_empty l)
    | l' with (decEmpty l')
      | Yes _ = Nothing
      | No _ with (cl_empty1 ls)
        | Nothing = Nothing
        | Just ls' = Just (l' :: ls')

--
-- Removing graphs that contain "bad" configurations.
-- The cleaner `cl_bad_conf` corresponds to the filter `fl_bad_conf`.
-- `cl_bad_conf` exploits the fact that "badness" to be monotonic,
-- in the sense that a single "bad" configuration spoils the whole
-- graph.

mutual

  cl_bad_conf : (bad : a -> Bool) -> (l : LazyGraph a) -> LazyGraph a
  cl_bad_conf bad Empty = Empty
  cl_bad_conf bad (Stop c) =
    if bad c then Empty else (Stop c)
  cl_bad_conf bad (Build c lss) =
    if bad c then Empty else (Build c (cl_bad_conf2 bad lss))

  cl_bad_conf2 : (bad : a -> Bool) ->
    (lss : List (List (LazyGraph a))) -> List (List (LazyGraph a))
  cl_bad_conf2 bad [] = []
  cl_bad_conf2 bad (ls :: lss) =
    map_cl_bad_conf bad ls :: (cl_bad_conf2 bad lss)

  map_cl_bad_conf : (bad : a -> Bool) ->
    (ls : List (LazyGraph a)) -> List (LazyGraph a)
  map_cl_bad_conf bad [] = []
  map_cl_bad_conf bad (l :: ls) =
    cl_bad_conf bad l :: map_cl_bad_conf bad ls

--
-- The graph returned by `cl_bad_conf` may be cleaned by `cl_empty`.
--

cl_empty_and_bad : (bad : a -> Bool) -> (l : LazyGraph a) -> LazyGraph a
cl_empty_and_bad bad = cl_empty . cl_bad_conf bad

--
-- Extracting a graph of minimal size (if any).
--

mutual

  graph_size  : (g : Graph a) -> Nat
  graph_size (Back c) = S Z
  graph_size (Forth c gs) = S (graph_size1 gs)

  graph_size1 : (gs : List (Graph a)) -> Nat
  graph_size1 [] = Z
  graph_size1 (g :: gs) = graph_size g + graph_size1 gs

-- Now we define a cleaner that produces a lazy graph
-- representing the smallest graph (or the empty set of graphs).

-- We use a trick: ∞ is represented by 0 in (0 , Empty).

select_min2 : (kx1, kx2 : (Nat, a)) -> (Nat, a)
select_min2 (Z, _) (k2, x2) = (k2, x2)
select_min2 (k1, x1) (Z, _) = (k1, x1)
select_min2 (k1, x1) (k2, x2) =
  if k1 <= k2 then (k1, x1) else (k2, x2)

select_min : (c : a) -> (kxs : List (Nat, a)) -> (Nat, a)
select_min c [] = (Z , c)
select_min c (kgs :: kgss) = foldl select_min2 kgs kgss

mutual

  cl_min_size : (l : LazyGraph a) -> (Nat, LazyGraph a)
  cl_min_size Empty =
    (Z , Empty)
  cl_min_size (Stop c) =
    (S Z , Stop c)
  cl_min_size (Build c lss) with (cl_min_size2 lss)
    | (Z , _) = (Z , Empty)
    | (k , ls) = (S k , Build c [ ls ])

  cl_min_size2 : (lss : List (List (LazyGraph a))) ->
    (Nat, List (LazyGraph a))
  cl_min_size2 [] = (Z , [])
  cl_min_size2 (ls :: lss) with (cl_min_size_and ls, cl_min_size2 lss)
    | (kls1, kls2) = select_min2 kls1 kls2

  cl_min_size_and : (ls : List (LazyGraph a)) ->
    (Nat, List (LazyGraph a))

  cl_min_size_and [] = (S Z , [])
  cl_min_size_and (l :: ls) with (cl_min_size l, cl_min_size_and ls)
   | ((Z, l'), (_, ls')) = (Z , l' :: ls')
   | ((_, l'), (Z, ls')) = (Z , l' :: ls')
   | ((i, l'), (j, ls')) = (i + j , l' :: ls')

--
-- `cl_min_size` is sound:
--
--  Let cl_min_size l = (k , l'). Then
--     unroll l' ⊆ unroll l
--     k = graph_size (hd (unroll l'))
--
-- TODO: prove this formally
