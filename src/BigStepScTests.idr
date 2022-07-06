module BigStepScTests

import Data.List.Quantifiers
import Data.List.Elem

import Util
import Graphs
import BarWhistles
import BigStepSc
import Decidable.Equality

-- ScWorld Conf3

-- This is a silly world with 3 possible configurations.
-- (Just for testing.)

data Conf3 : Type where
  C0 : Conf3
  C1 : Conf3
  C2 : Conf3

C0notC1 : C0 = C1 -> Void
C0notC1 Refl impossible

C0notC2 : C0 = C2 -> Void
C0notC2 Refl impossible

C1notC0 : C1 = C0 -> Void
C1notC0 Refl impossible

C1notC2 : C1 = C2 -> Void
C1notC2 Refl impossible

C2notC0 : C2 = C0 -> Void
C2notC0 Refl impossible

C2notC1 : C2 = C1 -> Void
C2notC1 Refl impossible

DecEq Conf3 where
  decEq C0 C0 = Yes Refl
  decEq C0 C1 = No C0notC1
  decEq C0 C2 = No C0notC2
  decEq C1 C0 = No C1notC0
  decEq C1 C1 = Yes Refl
  decEq C1 C2 = No C1notC2
  decEq C2 C0 = No C2notC0
  decEq C2 C1 = No C2notC1
  decEq C2 C2 = Yes Refl

conf3_drive : Conf3 -> List Conf3
conf3_drive C0 = [C1, C2]
conf3_drive C1 = [C0]
conf3_drive C2 = [C1 ]

conf3_rebuildings : Conf3 -> List Conf3
conf3_rebuildings C0 = [C1]
conf3_rebuildings _  = []

ScWorld Conf3 where
  c << c' = (c = c')
  c <<? c' = decEq c c'
  develop c = [ conf3_drive c ] ++ map (:: []) (conf3_rebuildings c)

-- NDSC

%hint
not_f1 : Any (Equal C0) [] -> Void
not_f1 (Here x) impossible
not_f1 (There x) impossible

%hint
not_f2 : Any (Equal C1) [C0] -> Void
not_f2 (Here Refl) impossible
not_f2 (There (Here x)) impossible
not_f2 (There (There x)) impossible

not_f3 : Any (Equal C2) [C0] -> Void
not_f3 (Here Refl) impossible
not_f3 (There (Here x)) impossible
not_f3 (There (There x)) impossible

not_f4 : Any (Equal C1) [C2, C0] -> Void
not_f4 (Here Refl) impossible
not_f4 (There (Here Refl)) impossible
not_f4 (There (There (Here x))) impossible
not_f4 (There (There (There x))) impossible

w3graph1 : NDSC [] C0 $
  Forth C0 [
    Forth C1 [ Back C0 ],
    Forth C2 [ Forth C1 [ Back C0 ] ]]
w3graph1 =
  NDSC_Build not_f1 Here [
    NDSC_Build not_f2 Here [
      NDSC_Fold (There (Here Refl)) ],
    NDSC_Build not_f3 Here [
      NDSC_Build not_f4 Here [
        NDSC_Fold (There (There (Here Refl)))]]]

w3graph2 : NDSC [] C0 $
  Forth C0 [ Forth C1 [ Back C0 ]]
w3graph2 =
  NDSC_Build not_f1 (There Here) [
    NDSC_Build not_f2 Here [
      NDSC_Fold (There (Here Refl))]]


plw4 : BarWhistle Conf3
plw4 = pathLengthWhistle Conf3 4

test_naive_mrsc : naive_mrsc BigStepScTests.plw4 C0 = [
  Forth C0 [
    Forth C1 [Back C0],
    Forth C2 [Forth C1 [Back C0]]],
    Forth C0 [Forth C1 [Back C0]]]
test_naive_mrsc = Refl

test_lazy_mrsc : lazy_mrsc BigStepScTests.plw4 C0 =
  Build C0 [
    [
      Build C1 [[Stop C0]],
      Build C2 [[Build C1 [[Stop C0]]]]],
    [
      Build C1 [[Stop C0]]]]
test_lazy_mrsc = Refl


--
-- This stuff might be useful just for testing purposes...
--

-- Eq Conf3

Eq Conf3 where
  C0 == C0 = True
  C1 == C1 = True
  C2 == C2 = True
  c  == c' = False

mutual
  eqGraph : Eq a => (g1, g2 : Graph a) -> Bool
  eqGraph (Back c1) (Back c2) = c1 == c2
  eqGraph (Forth c1 gs1) (Forth c2 gs2) = c1 == c2 && eqGraphList gs1 gs2
  eqGraph _ _ = False

  eqGraphList : Eq a => (g1, g2 : List(Graph a)) -> Bool
  eqGraphList [] [] = True
  eqGraphList (g1 :: gs1) (g2 :: gs2) = eqGraph g1 g2 && eqGraphList gs1 gs2
  eqGraphList _ _ = False

-- Eq (Graph a)

Eq a => Eq (Graph a) where
  (==) = eqGraph
