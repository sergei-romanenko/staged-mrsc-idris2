--
-- Graphs of configurations
--

module SMRSC.Graphs

import SMRSC.Util

%default total

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

public export
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

public export
data LazyGraph : (a : Type) -> Type where
  Empty : LazyGraph a
  Stop  : (c : a) -> LazyGraph a
  Build : (c : a) -> (lss : List (List (LazyGraph a))) -> LazyGraph a

%name LazyGraph l,l1,l2,l3,l4 -- Name hints for interactive editing

-- decEmpty

public export
implementation Uninhabited (Empty = Stop c) where
  uninhabited Refl impossible

public export
implementation Uninhabited (Empty = Build c lss) where
  uninhabited Refl impossible

public export
decEmpty : (l : LazyGraph c) -> Dec (Empty = l)
decEmpty Empty = Yes Refl
decEmpty (Stop c) = No absurd
decEmpty (Build c lss) = No absurd

-- The semantics of a `LazyGraph a` is formally defined by
-- the interpreter `unroll` that generates a list of `Graph a` from
-- the `LazyGraph a` by executing commands recorded in the `LazyGraph a`.

mutual

  public export
  unroll : (l : LazyGraph a) -> List (Graph a)
  unroll Empty = []
  unroll (Stop c) = [ Back c ]
  unroll (Build c lss) =
    -- map (Forth c) (concatMap (cartesian . (map (assert_total unroll))) lss)
    map (Forth c) (unroll_lss lss)

  public export
  unroll_lss : (lss : List (List (LazyGraph a))) -> List (List (Graph a))
  unroll_lss [] = []
  unroll_lss (ls :: lss) = cartesian (unroll_ls ls) ++ unroll_lss lss

  -- `unroll_ls` has only been introduced to make the termination
  -- checker happy. Actually, it is equivalent to `map unroll`.

  public export
  unroll_ls : (ls : List (LazyGraph a)) -> List (List (Graph a))
  unroll_ls [] = []
  unroll_ls (l :: ls) = unroll l :: unroll_ls ls

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

  public export
  bad_graph : (bad : a -> Bool) -> (g : Graph a) -> Bool
  bad_graph bad (Back c) = bad c
  bad_graph bad (Forth c gs) =
    bad c || bad_graph_gs bad gs

  public export
  bad_graph_gs : (bad : a -> Bool) -> (gs : List (Graph a)) -> Bool
  bad_graph_gs bad [] = False
  bad_graph_gs bad (g :: gs) =
    bad_graph bad g || bad_graph_gs bad gs

-- This filter removes the graphs containing "bad" configurations.

fl_bad_conf : (bad : a -> Bool) -> (gs : List (Graph a)) -> List (Graph a)
fl_bad_conf bad gs = filter (not . bad_graph bad) gs

--
-- Some cleaners
--

-- `cl_empty` removes subtrees that represent empty sets of graphs.

public export
cl_empty_build : (c : a) -> List (List (LazyGraph a)) -> LazyGraph a
cl_empty_build c [] = Empty
cl_empty_build c (ls :: lss) = Build c (ls :: lss)

mutual

  public export
  cl_empty : (l : LazyGraph a) -> LazyGraph a
  cl_empty Empty = Empty
  cl_empty (Stop c) = Stop c
  cl_empty (Build c lss) = cl_empty_build c (cl_empty_lss lss)
  
  public export
  cl_empty_lss : (lss : List (List (LazyGraph a))) ->  List (List (LazyGraph a))
  cl_empty_lss [] = []
  cl_empty_lss (ls :: lss) with (cl_empty_ls ls)
    _ | Nothing = cl_empty_lss lss
    _ | Just ls' = ls' :: cl_empty_lss lss


  public export
  cl_empty_ls : (ls : List (LazyGraph a)) -> Maybe (List (LazyGraph a))
  cl_empty_ls [] = Just []
  cl_empty_ls (l :: ls) =
    let l' = cl_empty l in
    cl_empty_ls_case_l' l' ls (decEmpty l')

  public export
  cl_empty_ls_case_l' : (l' : LazyGraph a) ->
    (ls : List (LazyGraph a)) -> Dec (Empty = l') ->
    Maybe (List (LazyGraph a))
  cl_empty_ls_case_l' l' ls (Yes _) = Nothing
  cl_empty_ls_case_l' l' ls (No _) =
    cl_empty_ls_case_ls l' ls (cl_empty_ls ls)

  public export
  cl_empty_ls_case_ls : (l' : LazyGraph a) -> (ls : List (LazyGraph a)) ->
    Maybe (List (LazyGraph a)) -> Maybe (List (LazyGraph a))
  cl_empty_ls_case_ls l' ls Nothing = Nothing
  cl_empty_ls_case_ls l' ls (Just ls') = Just (l' :: ls')

--
-- Removing graphs that contain "bad" configurations.
-- The cleaner `cl_bad_conf` corresponds to the filter `fl_bad_conf`.
-- `cl_bad_conf` exploits the fact that "badness" to be monotonic,
-- in the sense that a single "bad" configuration spoils the whole
-- graph.

mutual

  public export
  cl_bad_conf : (bad : a -> Bool) -> (l : LazyGraph a) -> LazyGraph a
  cl_bad_conf bad Empty = Empty
  cl_bad_conf bad (Stop c) =
    if bad c then Empty else (Stop c)
  cl_bad_conf bad (Build c lss) =
    if bad c then Empty else (Build c (cl_bad_conf_lss bad lss))

  public export
  cl_bad_conf_lss : (bad : a -> Bool) ->
    (lss : List (List (LazyGraph a))) -> List (List (LazyGraph a))
  cl_bad_conf_lss bad [] = []
  cl_bad_conf_lss bad (ls :: lss) =
    cl_bad_conf_ls bad ls :: (cl_bad_conf_lss bad lss)

  public export
  cl_bad_conf_ls : (bad : a -> Bool) ->
    (ls : List (LazyGraph a)) -> List (LazyGraph a)
  cl_bad_conf_ls bad [] = []
  cl_bad_conf_ls bad (l :: ls) =
    cl_bad_conf bad l :: cl_bad_conf_ls bad ls

--
-- The graph returned by `cl_bad_conf` may be cleaned by `cl_empty`.
--

public export
cl_empty_and_bad : (bad : a -> Bool) -> (l : LazyGraph a) -> LazyGraph a
cl_empty_and_bad bad = cl_empty . cl_bad_conf bad

--
-- Extracting a graph of minimal size (if any).
--

mutual

  public export
  graph_size  : (g : Graph a) -> Nat
  graph_size (Back c) = S Z
  graph_size (Forth c gs) = S (graph_size_gs gs)

  public export
  graph_size_gs : (gs : List (Graph a)) -> Nat
  graph_size_gs [] = Z
  graph_size_gs (g :: gs) = graph_size g + graph_size_gs gs

-- Now we define a cleaner that produces a lazy graph
-- representing the smallest graph (or the empty set of graphs).

-- We use a trick: ∞ is represented by 0 in (0 , Empty).

public export
select_min2 : (kx1, kx2 : (Nat, a)) -> (Nat, a)
select_min2 (Z, _) (k2, x2) = (k2, x2)
select_min2 (k1, x1) (Z, _) = (k1, x1)
select_min2 (k1, x1) (k2, x2) =
  if k1 <= k2 then (k1, x1) else (k2, x2)

public export
select_min : (c : a) -> (kxs : List (Nat, a)) -> (Nat, a)
select_min c [] = (Z , c)
select_min c (kgs :: kgss) = foldl select_min2 kgs kgss

mutual

  public export
  cl_min_size : (l : LazyGraph a) -> (Nat, LazyGraph a)
  cl_min_size Empty =
    (Z , Empty)
  cl_min_size (Stop c) =
    (S Z , Stop c)
  cl_min_size (Build c lss) with (cl_min_size2 lss)
    _ | (Z , _) = (Z , Empty)
    _ | (k , ls) = (S k , Build c [ ls ])

  public export
  cl_min_size2 : (lss : List (List (LazyGraph a))) ->
    (Nat, List (LazyGraph a))
  cl_min_size2 [] = (Z , [])
  cl_min_size2 (ls :: lss) with (cl_min_size_and ls, cl_min_size2 lss)
    _ | (kls1, kls2) = select_min2 kls1 kls2

  public export
  cl_min_size_and : (ls : List (LazyGraph a)) ->
    (Nat, List (LazyGraph a))
  cl_min_size_and [] = (S Z , [])
  cl_min_size_and (l :: ls) with (cl_min_size l, cl_min_size_and ls)
   _ | ((Z, l'), (_, ls')) = (Z , l' :: ls')
   _ | ((_, l'), (Z, ls')) = (Z , l' :: ls')
   _ | ((i, l'), (j, ls')) = (i + j , l' :: ls')

--
-- `cl_min_size` is sound:
--
--  Let cl_min_size l = (k , l'). Then
--     unroll l' ⊆ unroll l
--     k = graph_size (hd (unroll l'))
--
-- TODO: prove this formally

--
-- Eq (Graph a)
--

mutual
  eq_g : Eq a => (g1, g2 : Graph a) -> Bool
  eq_g (Back c1) (Back c2) = c1 == c2
  eq_g (Forth c1 gs1) (Forth c2 gs2) = c1 == c2 && eq_gs gs1 gs2
  eq_g _ _ = False

  eq_gs : Eq a => (g1, g2 : List(Graph a)) -> Bool
  eq_gs [] [] = True
  eq_gs (g1 :: gs1) (g2 :: gs2) = eq_g g1 g2 && eq_gs gs1 gs2
  eq_gs _ _ = False

public export
Eq a => Eq (Graph a) where
  (==) = eq_g

--
-- Eq (LazyGraph a)
--

public export
Eq a => Eq (LazyGraph a) where
  Empty == Empty = True
  Empty == Stop c = False
  Empty == Build c lss = False
  Stop c1 == Empty = False
  Stop c1 == Stop c2 = c1 == c2
  Stop c1 == Build c2 lss2 = False
  Build c1 lss1 == Empty = False
  Build c1 lss1 == Stop c2 = False
  Build c1 lss1 == Build c2 lss2 =
    c1 == c2 && eq_lss lss1 lss2
      where
        eq_lss : (lss1, lss2 : List (List (LazyGraph a))) -> Bool
        eq_lss [] [] = True
        eq_lss [] (ls2 :: lss2) = False
        eq_lss (ls1 :: lss1) [] = False
        eq_lss (ls1 :: lss1) (ls2 :: lss2) =
          eq_ls ls1 ls2 && eq_lss lss1 lss2
            where
              eq_ls : (ls1, ls2 : List (LazyGraph a)) -> Bool
              eq_ls [] [] = True
              eq_ls [] (l2 :: ls2) = False
              eq_ls (l1 :: ls1) [] = False
              eq_ls (l1 :: ls1) (l2 :: ls2) =
                l1 == l2 && eq_ls ls1 ls2

--
-- Show
--

export
Show a => Show (Graph a) where
  show (Back c) = "Back " ++ show c
  show (Forth c gs) =
    "Forth " ++ show c ++ " [" ++ show' "" gs ++ "]"
    where
      show' : String -> List (Graph a) -> String
      show' acc [] = acc
      show' acc (g :: gs) with (acc ++ show g)
        show' acc (g :: []) | acc' = acc'
        show' acc (g :: gs) | acc' = show' (acc' ++ ", ") gs

mutual

  show_l : Show a => LazyGraph a -> String
  show_l Empty = "Empty"
  show_l (Stop c) = "Stop " ++ show c
  show_l (Build c lss) =
    "Build " ++ show c ++ " [" ++ show_lss "" lss ++ "]"

  show_lss : Show a => String -> List (List (LazyGraph a)) -> String
  show_lss acc [] = acc
  show_lss acc (ls :: lss) with (acc ++ "[" ++ show_ls "" ls ++ "]")
    show_lss acc (ls :: []) | acc' = acc'
    show_lss acc (ls :: lss) | acc' = show_lss (acc' ++ ", ") lss

  show_ls : Show a => String -> List (LazyGraph a) -> String
  show_ls acc [] = acc
  show_ls acc (l :: ls) with (acc ++ show_l l)
    show_ls acc (l :: []) | acc' = acc'
    show_ls acc (l :: ls) | acc' = show_ls (acc' ++ ", ") ls

export
Show a => Show (LazyGraph a) where
  show = show_l

--
-- Pretty-printing
--

-- Graph pretty-printer

graph_pp_g : Show a => (g : Graph a) -> (indent : String) -> String
graph_pp_g (Back c) indent =
  indent ++ "|__" ++ show c ++ "*"
graph_pp_g (Forth c gs) indent =
  graph_pp_gs (indent ++ "|__" ++ show c) gs indent
  where
    graph_pp_gs : (acc : String) ->
      (gs : List (Graph a)) -> (indent : String) -> String
    graph_pp_gs acc [] indent = acc
    graph_pp_gs acc (g :: gs) indent =
      graph_pp_gs
        (acc ++ "\n  " ++ indent ++ "|\n" ++ graph_pp_g g (indent ++ "  "))
        gs indent

export
graph_pp : Show a => (g : Graph a) -> String
graph_pp g = graph_pp_g g ""
