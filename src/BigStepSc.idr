module BigStepSc

{- ### Schemes of different types of big-step supercompilation ### -}

{-
A variation of the scheme presented in the paper

Ilya G. Klyuchnikov, Sergei A. Romanenko. Formalizing and Implementing
Multi-Result Supercompilation.
In Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on
Metacomputation. Pereslavl-Zalessky, Russia, July 5-9, 2012).
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan
University of Pereslavl, 2012, 260 p. ISBN 978-5-901795-28-6, pages
142-164.
-}

import Data.List
import Data.List.Quantifiers
import Data.List.Elem
-- import Data.Fun.Extra

import Util
import BarWhistles
import Graphs

%default total

-- Now we formulate an idealized model of big-step multi-result
-- supercompilation.

-- The knowledge about the input language a supercompiler deals with
-- is represented by a "world of supercompilation", which is a record
-- that specifies the following.
--
-- * `Conf` is the type of "configurations". Note that configurations are
--   not required to be just expressions with free variables! In general,
--   they may represent sets of states in any form/language and as well may
--   contain any _additional_ information.
--
-- * `_<<_` is a "foldability relation". c << c' means that c is foldable to c'.
--   (In such cases c' is usually said to be " more general than c".)
--
-- * `_<<?_` is a decision procedure for `_<<_`. This procedure is necessary
--   for implementing supercompilation in functional form.
--
-- * `develop` is a function that gives a number of possible decompositions of
--   a configuration. Let `c` be a configuration and `cs` a list of
--   configurations such that `cs ∈ c`. Then `c` can be "reduced to"
--   (or "decomposed into") configurations in `cs`.
--
--   Suppose that driving is determinstic and, given a configuration `c`,
--   produces a list of configurations `drive c`. Suppose that rebuilding
--   (generalization, application of lemmas) is non-deterministic and
--   `rebuildings c` is the list of configurations that can be produced by
--   rebuilding. Then (in this special case) `develop` is implemented
--   as follows:
--
--       develop c = [ drive c ] ++ map (:: []) (rebuildings c)
--
-- * `whistle` is a "bar whistle" that is used to ensure termination of
--   functional supercompilation (see the module `BarWhistles`).
--
-- * `History` is a list of configuration that have been produced
--   in order to reach the current configuration.
--
-- * `c <<* h` means that `c` is foldable to a configuration in
--   the history `h`.
--
-- * `c <<*? h` decides whether `c <<* h`.

-- ScWorld

infixl 7 <<, <<?, <<*, <<*?

public export
interface ScWorld a where

  (<<) : (c, c' : a) -> Type
  (<<?) : (c, c' : a) -> Dec (c << c')
  develop : (c : a) -> List (List a)

  (<<*) : (c : a) -> (h : List a) -> Type
  c <<* h = Any (c <<) h

  --(<<*?) : (c : a) -> (h : List a) -> Dec (c <<* h)
  (<<*?) : (c : a) -> (h : List a) -> Dec (Any (c <<) h)
  c <<*? h = any (c <<?) h


{-
namespace ScWorldWithLabels

  -- If we need labeled edges in the graph of configurations,
  -- the labels can be hidden inside configurations.
  -- ("Configurations" do not have to be just symbolic expressions, as
  -- they can contain any additional information.)

  interface BarWhistle a => ScWorldWithLabels b a where

    (<<) : (c, c' : a) -> Type
    (<<?) : (c, c' : a) -> Dec (c << c')
    develop : (c : a) -> List (List (b, a))
-}

-- injectLabelsInScWorld

{-
implementation BarWhistle a => BarWhistle (b, a) where
  dangerous h = dangerous (map snd h)
  monoDangerous (l, c) h d = monoDangerous c (map snd h) d
  decDangerous h = decDangerous (map snd h)
  barNil = barNil {a=(b, a)}
-}
{-
injectLabelsInScWorld : ScWorldWithLabels -> ScWorld

injectLabelsInScWorld w = record
  { Conf = Label × Conf
  ; _<<_ = _<<'_
  ; _<<?_ = _<<?'_
  ; _⇉ = _⇉ ∘ proj₂
  ; whistle = inverseImageWhistle proj₂ whistle
  }
  where
  open ScWorldWithLabels w

  _<<'_ : Label × Conf -> Label × Conf -> Type
  (l , c) <<' (l' , c') = c << c'

  _<<?'_ : (c c' : Label × Conf) -> Dec (proj₂ c << proj₂ c')
  (l , c) <<?' (l' , c') = c <<? c'
-}

--
-- Big-step non-deterministic supercompilation
--

public export
data NDSC : ScWorld a => (h : List a) -> (c : a) -> (g : Graph a) -> Type where
  NDSC_Fold  : {s : ScWorld a} -> {h : List a} -> {c : a} ->
    (f : c <<* h) ->
      NDSC h c (Back c)
  NDSC_Build : ScWorld a => {h : List a} -> {c : a} ->
    {cs : List a} -> {gs : List (Graph a)} ->
    (nf : Not (c <<* h)) ->
    (i : Elem cs (develop c)) ->
    (s : Pointwise (NDSC (c :: h)) cs gs) ->
      NDSC h c (Forth c gs)

--
-- Big-step multi-result supercompilation
--

-- Relational big-step multi-result supercompilation.

public export
data MRSC : ScWorld a => (w : BarWhistle a) ->
    (h : List a) -> (c : a) -> (g : Graph a) -> Type where
  MRSC_Fold  : ScWorld a => (w : BarWhistle a) ->
    {h : List a} -> {c : a} ->
    (f : c <<* h) ->
      MRSC w h c (Back c)
  MRSC_Build : ScWorld a => (w : BarWhistle a) ->
    {h : List a} -> {c : a} ->
    {cs : List a} -> {gs : List (Graph a)} ->
    (nf : Not (c <<* h)) ->
    (nw : Not (w.dangerous h)) ->
    (i : Elem cs (develop c)) ->
    (p : Pointwise (MRSC w (c :: h)) cs gs) ->
      MRSC w h c (Forth c gs)

--
-- Functional big-step multi-result supercompilation.
-- (The naive version builds Cartesian products immediately.)
--

public export
naive_mrsc' : ScWorld a => (w : BarWhistle a) ->
  (h : List a) -> (b : Bar w.dangerous h) -> (c : a) -> List (Graph a)
naive_mrsc' w h b c with (c <<*? h)
  _ | Yes f = [ Back c ]
  _ | No nf with (w.decDangerous h)
    _ | Yes w' = []
    _ | No nw' with (b)
      _ | Now w' = void (nw' w')
      _ | Later bs =
        map (Forth c)
          (concatMap (cartesian . map (naive_mrsc' w (c :: h) (bs c)))
                     (develop c))

public export
naive_mrsc : ScWorld a => (w : BarWhistle a) -> (c : a) -> List (Graph a)
naive_mrsc w c = naive_mrsc' w [] w.barNil c

-- "Lazy" multi-result supercompilation.
-- (Cartesian products are not immediately built.)

-- lazy_mrsc is essentially a "staged" version of naive-mrsc
-- with get-graphs being an "interpreter" that evaluates the "program"
-- returned by lazy_mrsc.

public export
lazy_mrsc' : ScWorld a => (w : BarWhistle a) ->
  (h : List a) -> (b : Bar w.dangerous h) -> (c : a) -> LazyGraph a
lazy_mrsc' w h b c with (c <<*? h)
  _ | Yes f = Stop c
  _ | No nf with (w.decDangerous h)
    _ | Yes w' = Empty
    _ | No nw' with (b)
      _ | Now w' = void (nw' w')
      _ | Later bs =
        Build c (map (map (lazy_mrsc' w (c :: h) (bs c))) (develop c))

-- lazy_mrsc

public export
lazy_mrsc : ScWorld a => (w : BarWhistle a) -> (c : a) -> LazyGraph a
lazy_mrsc w c = lazy_mrsc' w [] w.barNil c
