module SMRSC.Counters

import Data.Nat
import Data.Vect
import Decidable.Equality
import Data.List.Quantifiers
import Syntax.PreorderReasoning
import Decidable.Decidable

-- import Util
import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Cographs

%default total

-- NW

prefix 10 ^

public export
data NW : Type where
  ω   : NW
  (^) : (i : Nat) -> NW

public export
Show NW where
  show ω = "W"
  show (^ i) = show i

-- (+)

public export
(+) : (m, n : NW) -> NW
ω + n = ω
m + ω = ω
(^ i) + (^ j) = ^(plus i j)

-- (-)

public export
(-) : (m, n : NW) -> NW
ω - n = ω
m - ω = ω
(^ i) - (^ j) = ^(minus i j)

-- GTE_CN

data GTE_CN : (m : NW) -> (j : Nat) -> Type where
  GTE_WN : ω `GTE_CN` j
  GTE_NN : (i `GTE` j) -> ^ i `GTE_CN` j

-- decGTE_CN

decGTE_CN : (m : NW) -> (j : Nat) -> Dec (m `GTE_CN` j)
decGTE_CN ω j = Yes GTE_WN
decGTE_CN (^ i) j with (decLTE j i)
  _ | Yes lte_j_i = Yes $ GTE_NN lte_j_i
  _ | No n_lte_j_i =
    No $ n_lte_j_i . (\case GTE_NN lte_j_i => lte_j_i)

-- EQ_CN

data EQ_CN : (m : NW) -> (j : Nat) -> Type where
  EQ_WN : ω `EQ_CN` j
  EQ_NN : ^ i `EQ_CN` i

-- decEQ_CN

decEQ_CN : (m : NW) -> (j : Nat) -> Dec (m `EQ_CN` j)
decEQ_CN ω j = Yes EQ_WN
decEQ_CN (^ i) j with (decEq i j)
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
Conf : Nat -> Type
Conf k = Vect k NW

public export
record CountersWorld where
  constructor MkCountersWorld

  0 k : Nat

  -- Initial configuration
  start : Conf k

  -- Driving rules
  rules : (c : Conf k) -> List ((Bool, Lazy (Conf k)))

  -- Which configurations are (semantically) unsafe?
  unsafe : (c : Conf k) -> Bool

--
-- Converting a world of counters to a world of supercompilation.
--

data IsFoldableTo : {0 k : Nat} -> (ms : Conf k) -> (ns : Conf k) -> Type where
  Nil  : IsFoldableTo [] []
  (::) : m `IsIn` n -> IsFoldableTo ms ns -> IsFoldableTo (m :: ms) (n::ns)

cntDecIsFoldableTo : {0 k : Nat} -> (c, c' : Conf k) -> Dec (IsFoldableTo c c')
cntDecIsFoldableTo [] [] = Yes []
cntDecIsFoldableTo (m :: ms) (n :: ns) with (decIsIn m n)
  _ | No nin_mn = No $ \(in_mn :: _) => nin_mn in_mn
  _ | Yes in_mn with (cntDecIsFoldableTo ms ns)
    _ | Yes pw = Yes $ in_mn :: pw
    _ | No npw = No $ \(_ :: pw) => npw pw

  -- Rebuildings

cntRebuild1 : (nw : NW) -> List NW
cntRebuild1 ω = [ ω ]
cntRebuild1 (^ i) = [ ^ i, ω]

-- vect_cartesian

vect_cartesian2 : {0 k : Nat} -> List a -> List (Vect k a) -> List (Vect (S k) a)
vect_cartesian2 [] yss = []
vect_cartesian2 (x :: xs) yss = map (x ::) yss ++ vect_cartesian2 xs yss

vect_cartesian : {0 k : Nat} -> Vect k (List a) -> List (Vect k a)
vect_cartesian [] = [ [] ]
vect_cartesian (xs :: xss) = vect_cartesian2 xs (vect_cartesian xss)

public export
cntSc : (cw : CountersWorld) -> ScWorld (Conf cw.k)
cntSc cw =
  let
    drive : (c : Conf cw.k) -> List (Conf cw.k)
    drive c = [r | (p, r) <- cw.rules c, p]

    rebuild : (c : Conf cw.k) -> List (Conf cw.k)
    rebuild c = filter (/= c) (vect_cartesian (map cntRebuild1 c))

    develop : (c : Conf cw.k) -> List (List (Conf cw.k))
    develop c =
      [ drive c] ++ [[ c' ] | c' <- rebuild c ]
  in
  MkScWorld
    (IsFoldableTo {k = cw.k}) (cntDecIsFoldableTo {k = cw.k}) develop

public export
cntWhistle : (k : Nat) -> (maxNat : Nat) -> (maxDepth : Nat) -> BarWhistle (Conf k)
cntWhistle k maxNat maxDepth =
  let
    TooBig1 : (m : NW) -> Type
    TooBig1 ω = Void
    TooBig1 (^ i) = maxNat `LTE` i

    decTooBig1 : (m : NW) -> Dec (TooBig1 m)
    decTooBig1 ω = No id
    decTooBig1 (^ i) = decLTE maxNat i

    TooBig : (c : Conf k) -> Type
    TooBig c = Any TooBig1 (toList c)

    decTooBig : (c : Conf k) -> Dec (TooBig c)
    decTooBig c = any decTooBig1 (toList c)

    Dangerous : (h : List (Conf k)) -> Type
    Dangerous h = Either (maxDepth `LTE` length h) (Any TooBig h)

    monoDangerous : (c : Conf k) -> (h :List (Conf k)) -> Dangerous h -> Dangerous (c :: h)
    monoDangerous c h (Left dhl) = Left $ lteSuccRight dhl
    monoDangerous c h (Right dhr) = Right $ There dhr

    decDangerous : (h : List (Conf k)) -> Dec (Dangerous h)
    decDangerous h with (maxDepth `decLTE` length h)
      _ | Yes d = Yes (Left d)
      _ | No nd with (any decTooBig h)
        _ | Yes b = Yes $ Right b
        _ | No nb = No $ \case
          Left d => nd d
          Right b => nb b

    bar : (m : _) -> (h : List (Conf k)) -> (d : m + length h = maxDepth) ->
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

public export
cl_unsafe : (cw : CountersWorld) -> (l : LazyGraph (Conf cw.k)) -> LazyGraph (Conf cw.k)
cl_unsafe cw = cl_bad_conf cw.unsafe

public export
cl8_unsafe : (cw : CountersWorld) -> (l : LazyGraph8 (Conf cw.k)) -> LazyGraph8 (Conf cw.k)
cl8_unsafe cw = cl8_bad_conf cw.unsafe

--
-- A "DSL" for encoding counter systems in a user-friendly form.
--

-- Not necessary?

infix 6 >=^, =^

public export
(>=^) : (m : NW) -> (j : Nat) -> Bool
m >=^ j = isYes (m `decGTE_CN` j)

public export
(=^) : (m : NW) -> (j : Nat) -> Bool
m =^ j = isYes (m `decEQ_CN` j)
