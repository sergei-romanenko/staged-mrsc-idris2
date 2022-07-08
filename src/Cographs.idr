--
-- Infinite trees/graphs
--
module Cographs

import Data.List.Quantifiers

import Util
import BarWhistles
import Graphs
import BigStepSc

--
-- Lazy cographs of configurations
--

-- A `LazyGraph8 C` represents a (potentially) infinite set of graphs
-- of configurations (whose type is `Graph C`).
--
-- "Lazy" cographs of configurations will be produced
-- by the "lazy" (staged) version of multi-result
-- supercompilation.

-- LazyCoraph

public export
data LazyGraph8 : (a : Type) -> Type where
  Empty8 : LazyGraph8 a
  Stop8  : (c : a) -> LazyGraph8 a
  Build8 : (c : a) -> (lss : Inf(List (List (LazyGraph8 a)))) -> LazyGraph8 a

%name LazyGraph8 l,l1,l2,l3,l4 -- Name hints for interactive editing

-- decEmpty8

implementation Uninhabited (Empty8 = Stop8 c) where
  uninhabited Refl impossible

implementation Uninhabited (Empty8 = Build8 c lss) where
  uninhabited Refl impossible

decEmpty8 : (l : LazyGraph8 c) -> Dec (Empty8 = l)
decEmpty8 Empty8 = Yes Refl
decEmpty8 (Stop8 x) = No absurd
decEmpty8 (Build8 x lss) = No absurd

-- BigStepMRSC8

-- build_graph8

mutual

  build_graph8_c : ScWorld a => (h : List a) -> (c : a) -> LazyGraph8 a
  build_graph8_c h c with (c <<*? h)
    _ | Yes f = Stop8 c
    _ | No nf =
      Build8 c (build_graph8_css h c (develop c))

  build_graph8_css : ScWorld a => (h : List a) -> (c : a) ->
    (css : List (List a)) -> List (List (LazyGraph8 a))
  build_graph8_css h c [] = []
  build_graph8_css h c (cs :: css) =
    build_graph8_cs (c :: h) cs :: build_graph8_css h c css

  build_graph8_cs : ScWorld a => (h : List a) -> (cs : List a) ->
    List (LazyGraph8 a)
  build_graph8_cs h [] = []
  build_graph8_cs h (c :: cs) =
    build_graph8_c h c :: build_graph8_cs h cs

build_graph8 : ScWorld a => (c : a) -> LazyGraph8 a
build_graph8 c = build_graph8_c [] c

-- prune_graph8

mutual

  prune_graph8_l : ScWorld a => (w : BarWhistle a) ->
    (h : List a) -> (b : Bar w.dangerous h) -> (l : LazyGraph8 a) ->
    LazyGraph a
  prune_graph8_l w h b Empty8 = Empty
  prune_graph8_l w h b (Stop8 c) = Stop c
  prune_graph8_l w h b (Build8 c lss) with (w.decDangerous h)
    _ | Yes d = Empty
    _ | No nd with (b)
      _ | Now d = void (nd d)
      _ | Later bs =
        Build c (map (prune_graph8_ls w (c :: h) (bs c)) lss)

  prune_graph8_ls : ScWorld a => (w : BarWhistle a) ->
    (h : List a) -> (b : Bar w.dangerous h) -> (ls : List (LazyGraph8 a)) ->
    List (LazyGraph a)
  prune_graph8_ls w h b [] = []
  prune_graph8_ls w h b (l :: ls) =
    prune_graph8_l w h b l :: prune_graph8_ls w h b ls

prune_graph8 : ScWorld a => (w : BarWhistle a) -> (l : LazyGraph8 a) ->
  LazyGraph a
prune_graph8 w l = prune_graph8_l w [] w.barNil l

--
-- Now that we have docomposed `lazy-mrsc`
--     lazy-mrsc ≗ prune-cograph ∘ build-cograph
-- we can push some cleaners into prune-cograph.
--
-- Suppose `clean∞` is a cograph cleaner such that
--     clean ∘ prune-cograph ≗ prune-cograph ∘ clean∞
-- then
--     clean ∘ lazy-mrsc ≗
--       clean ∘ (prune-cograph ∘ build-cograph) ≗
--       (prune-cograph ∘ clean∞) ∘ build-cograph
--       prune-cograph ∘ (clean∞ ∘ build-cograph)
--
-- The good thing is that `build-cograph` and `clean∞` work in a lazy way,
-- generating subtrees by demand. Hence, evaluating
--     ⟪ prune-cograph ∘ (clean∞ (build-cograph c))  ⟫
-- may be less time and space consuming than evaluating
--     ⟪ clean (lazy-mrsc c) ⟫
--

-- cl8_bad_conf

mutual

  cl8_bad_conf : (bad : a -> Bool) -> (l : LazyGraph8 a) -> LazyGraph8 a
  cl8_bad_conf bad Empty8 =
    Empty8
  cl8_bad_conf bad (Stop8 c) =
    if bad c then Empty8 else Stop8 c
  cl8_bad_conf bad (Build8 c lss) with (bad c)
    _ | False = Build8 c (cl8_bad_conf_lss bad lss)
    _ | True = Empty8

  cl8_bad_conf_lss : (bad : a -> Bool) -> (lss : List (List (LazyGraph8 a))) ->
    List (List (LazyGraph8 a))
  cl8_bad_conf_lss bad [] = []
  cl8_bad_conf_lss bad (ls :: lss) =
    cl8_bad_conf_ls bad ls :: cl8_bad_conf_lss bad lss

  cl8_bad_conf_ls : (bad : a -> Bool) -> (ls : List (LazyGraph8 a)) ->
    List (LazyGraph8 a)
  cl8_bad_conf_ls bad [] = []
  cl8_bad_conf_ls bad (l :: ls) =
    cl8_bad_conf bad l :: cl8_bad_conf_ls bad ls

--
-- A cograph can be cleaned to remove some empty alternatives.
--
-- Note that the cleaning is not perfect, because `cl8_empty` has to pass
-- the productivity check.
-- So, `build c []` is not (recursively) replaced with `Ø`. as is done
-- by `cl-empty`.
--

-- cl8_empty

mutual

  cl8_empty : (l : LazyGraph8 a) -> LazyGraph8 a
  cl8_empty Empty8 = Empty8
  cl8_empty (Stop8 c) = Stop8 c
  cl8_empty (Build8 c lss) =
    Build8 c (cl8_empty_lss lss)

  cl8_empty_lss : (lss : List (List (LazyGraph8 a))) ->  List (List (LazyGraph8 a))
  cl8_empty_lss [] = []
  cl8_empty_lss (ls :: lss) with (any decEmpty8 ls)
      _ | Yes _ = cl8_empty_lss lss
      _ | No  _ = cl8_empty_ls ls :: cl8_empty_lss lss

  cl8_empty_ls : (ls : List (LazyGraph8 a)) -> List (LazyGraph8 a)
  cl8_empty_ls [] = []
  cl8_empty_ls (l :: ls) = cl8_empty l :: cl8_empty_ls ls


-- An optimized version of `prune-cograph`.
-- The difference is that empty subtrees are removed
-- "on the fly".

-- prune0_graph8

mutual

  prune0_graph8_l : ScWorld a => (w : BarWhistle a) ->
    (h : List a) -> (b : Bar w.dangerous h) -> (l : LazyGraph8 a) ->
    LazyGraph a
  prune0_graph8_l w h b Empty8 = Empty
  prune0_graph8_l w h b (Stop8 c) = Stop c
  prune0_graph8_l w h b (Build8 c lss) with (w.decDangerous h)
      _ | Yes d = Empty
      _ | No nd with (b)
        _ | Now d = void (nd d)
        _ | Later bs =
          cl_empty_build c (prune0_graph8_lss w (c :: h) (bs c) lss)

  prune0_graph8_lss :  ScWorld a => (w : BarWhistle a) ->
    (h : List a) -> (b : Bar w.dangerous h) ->
    (lss : List (List (LazyGraph8 a))) -> List (List (LazyGraph a))
  prune0_graph8_lss w h b [] = []
  prune0_graph8_lss w h b (ls :: lss) with (prune0_graph8_ls w h b ls)
    prune0_graph8_lss w h b (ls :: lss) | Nothing =
      prune0_graph8_lss w h b lss
    prune0_graph8_lss w h b (ls :: lss) | Just ls' =
      ls' :: prune0_graph8_lss w h b lss

  prune0_graph8_ls : ScWorld a => (w : BarWhistle a) ->
    (h : List a) -> (b : Bar w.dangerous h) ->
    (ls : List (LazyGraph8 a)) -> Maybe (List (LazyGraph a))
  prune0_graph8_ls w h b [] = Just []
  prune0_graph8_ls w h b (l :: ls) with (prune0_graph8_l w h b l)
    _ | l' with (decEmpty l')
      _ | Yes _ = Nothing
      _ | No  _ with (prune0_graph8_ls w h b ls)
        _ | Nothing = Nothing
        _ | Just ls' = Just (l' :: ls')

prune0_graph8 : ScWorld a => (w : BarWhistle a) ->
  (l : LazyGraph8 a) -> LazyGraph a
prune0_graph8 w l = prune0_graph8_l w [] w.barNil l