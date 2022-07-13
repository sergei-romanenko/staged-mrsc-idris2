module Counters

import Data.Nat
import Data.Vect
import Decidable.Equality
import Data.List.Quantifiers
import Data.Nat.Order.Strict
import Syntax.PreorderReasoning

import Util
import BarWhistles
import Graphs
import BigStepSc
import Cographs

%default total

-- NW

prefix 10 ^

public export
data NW : Type where
  ω   : NW
  (^) : (i : Nat) -> NW

-- (+)

(+) : (m, n : NW) -> NW
ω + n = ω
m + ω = ω
(^ i) + (^ j) = ^(plus i j)

-- (-)

(-) : (m, n : NW) -> NW
ω - n = ω
m - ω = ω
(^ i) - (^ j) = ^(minus i j)

infix 4 >=^, >=^?, =^, =^?

-- (>=^)

data (>=^) : (m : NW) -> (j : Nat) -> Type where
  GTE_WN : ω >=^ j
  GTE_NN : (i `GTE` j) -> ^ i >=^ j

-- (>=^?)

(>=^?) : (m : NW) -> (j : Nat) -> Dec (m >=^ j)
(>=^?) ω j = Yes GTE_WN
(>=^?) (^ i) j with (decLTE j i)
  _ | Yes lte_j_i = Yes $ GTE_NN lte_j_i
  _ | No n_lte_j_i =
    No $ n_lte_j_i . (\case GTE_NN lte_j_i => lte_j_i)

-- (=^)

data (=^) : (m : NW) -> (j : Nat) -> Type where
  EQ_WN : ω =^ j
  EQ_NN : ^ i =^ i

-- (=^?)

(=^?) : (m : NW) -> (j : Nat) -> Dec (m =^ j)
(=^?) ω j = Yes EQ_WN
(=^?) (^ i) j with (decEq i j)
  _ | Yes eq_i_j = rewrite eq_i_j in Yes EQ_NN
  _ | No neq_i_j =
    No $ neq_i_j . (\case EQ_NN => Refl)


-- m `IsIn` n means that n is more general than m.

infix 4 `IsIn`, `decIsIn`

-- IsIn

data IsIn : (m, n : NW) -> Type where
  NIsInW : m `IsIn` ω
  NIsInN : ^ i `IsIn` ^ i

-- decIsIn

decIsIn : (m, n : NW) -> Dec (m `IsIn` n)
m `decIsIn` ω = Yes NIsInW
ω `decIsIn` (^ j) = No $ \case NIsInW impossible
(^ i) `decIsIn` (^ j) with (decEq i j)
  _ | Yes eq_i_j = rewrite eq_i_j in Yes NIsInN
  _ | No neq_i_j = No $ neq_i_j . \case NIsInN => Refl

Eq NW where
  ω == ω = True
  ω == (^ i) = False
  (^ i) == ω = False
  (^ i) == (^ j) = i == j

DecEq NW where
  decEq ω ω = Yes Refl
  -- decEq ω (^ j) = No neq_WN
  decEq ω (^ j) = No $ \case Refl impossible
  decEq (^ i) ω = No $ \case Refl impossible
  decEq (^ i) (^ j) with (decEq i j)
    _ | Yes eq_i_j = rewrite eq_i_j in Yes Refl
    _ | No neq_i_j = No $ neq_i_j . \case Refl => Refl

--
-- "Worlds of counters"
-- (To be converted to worlds of supercompilation.)
--

public export
Conf : Type
Conf = List NW

public export
record CountersWorld where
  constructor MkCountersWorld

  -- Initial configuration
  start : Conf

  -- Driving rules
  rules : (c : Conf) -> List ((Bool, Lazy Conf))

  -- Which configurations are (semantically) unsafe?
  unsafe : (c : Conf) -> Bool

--
-- Converting a world of counters to a world of supercompilation.
--

CntIsFoldableTo : (c, c' : Conf) -> Type
CntIsFoldableTo c c' = Pointwise IsIn c c'

cntDecIsFoldableTo : (c, c' : Conf) -> Dec (CntIsFoldableTo c c')
cntDecIsFoldableTo [] [] = Yes []
cntDecIsFoldableTo [] (n :: ns) = No absurd
cntDecIsFoldableTo (m :: ms) [] = No absurd
cntDecIsFoldableTo (m :: ms) (n :: ns) with (decIsIn m n)
  _ | Yes in_mn with (cntDecIsFoldableTo ms ns)
    _ | Yes pw = Yes $ in_mn :: pw
    _ | No npw = No $ \(_ :: pw) => npw pw
  _ | No nin_mn = No $ \(in_mn :: _) => nin_mn in_mn

  -- Rebuildings

cntRebuild1 : (nw : NW) -> List NW
cntRebuild1 ω = [ ω ]
cntRebuild1 (^ i) = [ ^ i, ω]

cntRebuild : (c : Conf) -> List Conf
cntRebuild c = filter (/= c) (cartesian (map cntRebuild1 c))

cntSc : (cw : CountersWorld) -> ScWorld Conf
cntSc cw =
  let
    drive : (c : Conf) -> List Conf
    drive c = [r | (p, r) <- cw.rules c, p]

    develop : (c : Conf) -> List (List Conf)
    develop c =
      [ drive c] ++ [[ c' ] | c' <- cntRebuild c ]
  in
  MkScWorld CntIsFoldableTo cntDecIsFoldableTo develop

public export
cntWhistle : (maxNat : Nat) -> (maxDepth : Nat) -> BarWhistle Conf
cntWhistle maxNat maxDepth =
  let
    TooBig1 : (m : NW) -> Type
    TooBig1 ω = Void
    TooBig1 (^ i) = maxNat `LTE` i

    decTooBig1 : (m : NW) -> Dec (TooBig1 m)

    TooBig : (c : Conf) -> Type
    TooBig c = Any TooBig1 c

    decTooBig : (c : Conf) -> Dec (TooBig c)
    decTooBig c = any decTooBig1 c

    Dangerous : (h : List Conf) -> Type
    Dangerous h = Either (maxDepth `LTE` length h) (Any TooBig h)

    monoDangerous : (c : Conf) -> (h :List Conf) -> Dangerous h -> Dangerous (c :: h)
    monoDangerous c h (Left dhl) = Left $ lteSuccRight dhl
    monoDangerous c h (Right dhr) = Right $ There dhr

    decDangerous : (h : List Conf) -> Dec (Dangerous h)
    decDangerous h with (maxDepth `decLTE` length h)
      _ | Yes d = Yes (Left d)
      _ | No nd with (any decTooBig h)
        _ | Yes b = Yes $ Right b
        _ | No nb = No $ \case
          Left d => nd d
          Right b => nb b

    bar : (m : _) -> (h : List Conf) -> (d : m + length h = maxDepth) ->
      Bar Dangerous h
    bar Z h d =
      Now $ rewrite d in Left reflexive
    bar (S m) h d =
      Later $ \c => bar m (c :: h) $ Calc $
        |~ m + S (length h)
        ~~ S (m + length h)  ...( sym $ plusSuccRightSucc m (length h) )
        ~~ maxDepth          ...( d )

    -- The whistle is based on the combination of `pathLengthWhistle` and
    -- `Any TooBig h`.

    -- TODO: It is possible to construct a whistle based on the fact that
    -- the set of configurations such that `Not(TooBig c)` is finite.

    barNil : Bar Dangerous []
    barNil = bar maxDepth []
      (the (maxDepth + 0 = maxDepth) $ plusZeroRightNeutral maxDepth)
  in
  MkBarWhistle Dangerous monoDangerous decDangerous barNil

cl_unsafe : (cw : CountersWorld) -> (l : LazyGraph Conf) -> LazyGraph Conf
cl_unsafe cw = cl_bad_conf cw.unsafe

cl8_unsafe : (cw : CountersWorld) -> (l : LazyGraph8 Conf) -> LazyGraph8 Conf
cl8_unsafe cw = cl8_bad_conf cw.unsafe

--
-- A "DSL" for encoding counter systems in a user-friendly form.
--

-- Not necessary?