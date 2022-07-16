module SMRSC.Tests.BigStepSc

import Data.List.Quantifiers
import Data.List.Elem
import Decidable.Equality

import SMRSC.Util
import SMRSC.Graphs
import SMRSC.BarWhistles
import SMRSC.BigStepSc

%default total

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

%hint
Sc3 : ScWorld Conf3
Sc3 =
  let
    IsFoldableTo : (c, c' : Conf3) -> Type
    IsFoldableTo c c' = (c = c')

    decIsFoldableTo : (c, c' : Conf3) -> Dec (IsFoldableTo c c')
    decIsFoldableTo c c' = decEq c c'

    develop : (c : Conf3) -> List (List Conf3)
    develop c = [ conf3_drive c ] ++ map (:: []) (conf3_rebuildings c)
  in
  MkScWorld IsFoldableTo decIsFoldableTo develop

-- NDSC

%hint
not_f1 : Any (IsFoldableTo Sc3 C0) [] -> Void
not_f1 (Here _) impossible
not_f1 (There _) impossible

%hint
not_f2 : Any (IsFoldableTo Sc3 C1) [C0] -> Void
not_f2 (Here Refl) impossible
not_f2 (There (Here x)) impossible
not_f2 (There (There x)) impossible

%hint
not_f3 : Any (IsFoldableTo Sc3 C2) [C0] -> Void
not_f3 (Here Refl) impossible
not_f3 (There (Here _)) impossible
not_f3 (There (There _)) impossible

%hint
not_f4 : Any (IsFoldableTo Sc3 C1) [C2, C0] -> Void
not_f4 (Here Refl) impossible
not_f4 (There (Here Refl)) impossible
not_f4 (There (There (Here _))) impossible
not_f4 (There (There (There _))) impossible

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


Plw4 : BarWhistle Conf3
Plw4 = pathLengthWhistle Conf3 4

test_naive_mrsc : naive_mrsc Sc3 Plw4 C0 = [
  Forth C0 [
    Forth C1 [Back C0],
    Forth C2 [Forth C1 [Back C0]]],
    Forth C0 [Forth C1 [Back C0]]]
test_naive_mrsc = Refl

test_lazy_mrsc : lazy_mrsc Sc3 Plw4 C0 =
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

Show Conf3 where
  show C0 = "C0"
  show C1 = "C1"
  show C2 = "C2"
