module AbstractSc

{- ### Schemes of different types of supercompilation ### -}

{-
As presented in the paper

Ilya G. Klyuchnikov, Sergei A. Romanenko. Formalizing and Implementing
Multi-Result Supercompilation.
In Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on
Metacomputation. Pereslavl-Zalessky, Russia, July 5-9, 2012).
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan
University of Pereslavl, 2012, 260 p. ISBN 978-5-901795-28-6, pages
142-164.
-}

%default total

{-
### Notation: ###

  g – a current graph of configurations
  β – a current node in a graph of configurations
  c – a configuration in a current node β
-}

interface ScStruct where
  Graph : Type
  Configuration : Type
  Node : Type
  DriveInfo : Type

  conf : Node -> Configuration

  Foldable : (g : Graph) -> (b, a : Node) -> Type
  foldable : (g : Graph) -> (b : Node) -> Maybe Node
  fold : (g : Graph) -> (b, a : Node) -> Graph

  driveStep : Configuration -> DriveInfo
  addChildren : (g : Graph) -> (b : Node) -> (cs : DriveInfo) -> Graph

  rebuilding : (c : Configuration) -> Configuration
  inRebuildings : (c', c : Configuration) -> Type
  rebuild : (g : Graph) -> (b : Node) -> (c' : Configuration) -> Graph

  dangerous : (g : Graph) -> (b : Node) -> Bool

  foldable_correct : forall g, a, b.
    foldable g b = Just a -> Foldable g b a
  rebuilding_correct : forall c, c'.
    rebuilding c = c' -> c' `inRebuildings` c

{-
### (a) SC: Deterministic (traditional) supercompilation ###

  (Fold)

  ∃α : foldable(g, β, α)
  ----------------------
  g → fold(g, β, α)

  (Drive)

  ∄α : foldable(g, β, α)
  ¬dangerous(g, β)
  cs = driveStep(c)
  --------------------------
  g → addChildren(g, β, cs)

  (Rebuild)

  ∄α : foldable(g, β, α)
  dangerous(g, β)
  c′ = rebuilding(g, c)
  ----------------------
  g → rebuild(g, β, c′)
-}

data SC : ScStruct => (g, g' : Graph) -> Type where
  SC_Fold : ScStruct => forall g, a, b.
    (f : foldable g b = Just a) ->
      g `SC` fold g b a
  SC_Drive : ScStruct => forall g, b, cs.
    (not_f : foldable g b = Nothing) ->
    (not_w : dangerous g b = False) ->
    (d  : driveStep (conf b) = cs) ->
      g `SC` addChildren g b cs
  SC_Rebuild : ScStruct => forall g, b, cs, c, c'.
    (not_f : foldable g b = Nothing) ->
    (w  : dangerous g b = True) ->
    (r  : rebuilding c = c') ->
      g `SC` rebuild g b c'

{-
### (b) NDSC: Non-deterministic supercompilation (transformation relation) ###

  (Fold)

  ∃α : foldable(g, β, α)
  ----------------------
  g → fold(g, β, α)

  (Drive)

  ∄α : foldable(g, β, α)
  cs = driveStep(c)
  --------------------------
  g → addChildren(g, β, cs)

  (Rebuild)

  ∄α : foldable(g, β, α)
  c′ ∈ rebuildings(c)
  ----------------------
  g → rebuild(g, β, c′)

-}

data NDSC : ScStruct => (g, g' : Graph) -> Type where
  NDSC_Fold : ScStruct => forall g, b, a.
    (f : foldable g b = Just a) ->
      g `NDSC` fold g b a
  NDSC_Drive : ScStruct => forall g, b, cs.
    (not_f : foldable g b = Nothing) ->
    (d  : driveStep (conf b) = cs) ->
      g `NDSC` addChildren g b cs
  NDSC_Rebuild : ScStruct => forall g, b, c, c'.
    (not_f : foldable g b = Nothing) ->
    (rs : c' `inRebuildings` c) ->
      g `NDSC` rebuild g b c'

{-
### (c) MRSC: Multi-result supercompilation ###

  (Fold)

  ∃α : foldable(g, β, α)
  ----------------------
  g → fold(g, β, α)

  (Drive)

  ∄α : foldable(g, β, α)
  ¬dangerous(g, β)
  cs = driveStep(c)
  --------------------------
  g → addChildren(g, β, cs)

  (Rebuild)

  ∄α : foldable(g, β, α)
  c′ ∈ rebuildings(c)
  -----------------------------------------
  g → rebuild(g, β, c′)

-}

data MRSC : ScStruct => (g, g' : Graph) -> Type where
  MRSC_Fold : ScStruct =>
    (f : foldable g b = Just a) ->
      g `MRSC` fold g b a
  MRSC_Drive : ScStruct =>
    (not_f : foldable g b = Nothing) ->
    (not_w : dangerous g b = False) ->
    (d  : driveStep (conf b) = cs) ->
      g `MRSC` addChildren g b cs
  MRSC_Rebuild : ScStruct =>
    (not_f : foldable g b = Nothing) ->
    (rs : c' `inRebuildings` c) ->
      g `MRSC` rebuild g b c'

-- Now let us prove some "natural" theorems.
-- A formal verification is useful
-- just to ensure that "the ends meet".

-- This model of supercompilation is extremely abstract.
-- So there is not much to prove.

SC_MRSC : ScStruct => g `SC` g' -> g `MRSC` g'
SC_MRSC (SC_Fold f) =
  MRSC_Fold f
SC_MRSC (SC_Drive not_f not_w d) =
  MRSC_Drive not_f not_w d
SC_MRSC (SC_Rebuild not_f w r) =
  MRSC_Rebuild not_f (rebuilding_correct r)

MRSC_NDSC : ScStruct => g `MRSC` g' -> g `NDSC` g'
MRSC_NDSC (MRSC_Fold f) =
  NDSC_Fold f
MRSC_NDSC (MRSC_Drive not_f not_w d) =
  NDSC_Drive not_f d
MRSC_NDSC (MRSC_Rebuild not_f rs) =
  NDSC_Rebuild not_f rs

SC_NDSC : ScStruct => g `SC` g' -> g `NDSC` g'
SC_NDSC h = ?SC_NDSC_rhs

-- Transitive closures

data Star : (a -> a -> Type) -> a -> a -> Type where
  Nil : Star r x x
  (::) : r x y -> Star r y z -> Star r x z

(++) : Star r x y -> Star r y z -> Star r x z
[] ++ s2 = s2
(h :: s1) ++ s2 = h :: (s1 ++ s2)

StarSC : ScStruct => Graph -> Graph -> Type
StarSC = Star SC

StarNDSC : ScStruct => Graph -> Graph -> Type
StarNDSC = Star NDSC

StarMRSC : ScStruct => Graph -> Graph -> Type
StarMRSC = Star MRSC

-- Theorems

StarSC_StarMRSC : ScStruct => g `StarSC` g' -> g `StarMRSC` g'
StarSC_StarMRSC [] = []
StarSC_StarMRSC (h :: s) = SC_MRSC h :: StarSC_StarMRSC s

StarMRSC_StarNDSC : ScStruct => g `StarMRSC` g' -> g `StarNDSC` g'
StarMRSC_StarNDSC [] = []
StarMRSC_StarNDSC (h :: s) = MRSC_NDSC h :: StarMRSC_StarNDSC s

StarSC_StarNDSC : ScStruct =>  g `StarSC` g' -> g `StarNDSC` g'
StarSC_StarNDSC = StarMRSC_StarNDSC . StarSC_StarMRSC
