{-
In our model of big-step supercompilation whistles are assumed to be
"inductive bars". See:

Thierry Coquand. About Brouwer's fan theorem. September 23, 2003.
Revue internationale de philosophie, 2004/4 n° 230, p. 483-489.

http://www.cairn.info/revue-internationale-de-philosophie-2004-4-page-483.htm
http://www.cairn.info/load_pdf.php?ID_ARTICLE=RIP_230_0483
-}

module BarWhistles

{-
open import Level
  using ()
open import Data.Nat
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>; ≤-step)
open import Data.List as List
open import Data.List.Any as Any
  using (Any)
open import Data.List.Any.Properties
  using (::↔)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _::_; here; there; lookup)
open import Data.Product as Prod
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty

open import Function
open import Function.Equivalence
  using (_⇔_; equivalence)
open import Function.Related as Related
  using ()
  renaming (module EquationalReasoning to ∼-Reasoning)

open import Relation.Binary.Sum
  using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise
  using (_×-cong_)

open import Relation.Nullary
open import Relation.Unary
  using (_∈_; _∪_; _⊆_)
  renaming (Decidable to Decidable₁)

open import Relation.Binary
  using (Rel; _⇒_)
  renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
  renaming ([_] to P[_])

open import Induction.WellFounded
-}

-- import Data.Morphisms
import Data.Nat
import Data.Nat.Order.Strict
import Syntax.PreorderReasoning

import Util
import AlmostFullRel

%default total

-- Bar

-- The set of finite paths such that either
-- (1) D h is valid right now; or
-- (2) for all possible a1 :: h either
--     (1) D (a1 :: h) is valid right now; or
--     (2) for all possible a2 :: a1 :: h either ...

public export
data Bar : (d : List a -> Type) -> (h : List a) -> Type where
  Now   : d h -> Bar d h
  Later : ((c : a) -> Bar d (c :: h)) -> Bar d h

{-
data Bar {A : Type} (D : List A -> Type) :
         (h : List A) -> Type where
  now   : {h : List A} (w : D h) -> Bar D h
  later : {h : List A} (bs : ∀ c -> Bar D (c :: h)) -> Bar D h
-}

public export
record BarWhistle a where
  constructor MkBarWhistle
  -- Bar whistles deal with sequences of some entities
  -- (which in our model of supercompilations are configurations).

  -- Dangerous histories
  dangerous : (h : List a) -> Type
  monoDangerous : (c : a) -> (h : List a) -> dangerous h -> dangerous (c :: h)
  decDangerous : (h : List a) -> Dec (dangerous h)

  -- Bar-induction
  -- (In Coquand's terms, `Bar dangerous` is required to be "an inductive bar".)
  barNil : Bar dangerous []

{- 
public export
interface BarWhistle a where

  -- Bar whistles deal with sequences of some entities
  -- (which in our model of supercompilations are configurations).

  -- Dangerous histories
  dangerous : (h : List a) -> Type
  monoDangerous : (c : a) -> (h : List a) -> dangerous h -> dangerous (c :: h)
  decDangerous : (h : List a) -> Dec (dangerous h)

  -- Bar-induction
  -- (In Coquand's terms, `Bar dangerous` is required to be "an inductive bar".)
  barNil : Bar dangerous []
-}

{-
record BarWhistle (A : Type) : Type₁ where

  -- Bar whistles deal with sequences of some entities
  -- (which in our model of supercompilations are configurations).

  constructor
    ⟨_,_,_,_⟩
  field

    -- Dangerous histories
    dangerous : (h : List A) -> Type
    monoDangerous : (c : A) (h : List A) -> dangerous h -> dangerous (c :: h)
    decDangerous : (h : List A) -> Dec (dangerous h)

    -- Bar-induction
    -- (In Coquand's terms, `Bar dangerous` is required to be "an inductive bar".)
    barNil : Bar dangerous []
-}

-- BarGen

-- This module shows the generation of finite sequences
-- by means of a bar whistle.

{-
module BarGen {A : Type} (g : List A -> A) (w : BarWhistle A) where

  open BarWhistle w

  barGen′ : ∀ (h : List A) (b : Bar dangerous h) ->
              ∃ λ (h′ : List A) -> dangerous h′
  barGen′ h (now w) = h , w
  barGen′ h (later bs) with g h
  ... | c = barGen′ (c :: h) (bs c)

  barGen : ∃ λ (h : List A) -> dangerous h
  barGen = barGen′ [] barNil
-}

-- A fan, or an finitely branching tree, is a tree
-- each node of which has a finite number of immediate successor nodes.

{-
data Fan (A : Type) : Type where
  fan : List (A × Fan A) -> Fan A
-}

-- BarFanGen

-- This module shows the generation of finitely branching trees
-- by means of a bar whistle.

{-
module BarFanGen
  {A : Type} (_⇉ : List A -> List A) (w : BarWhistle A)
  where
  open BarWhistle w

  fanGen′ : (h : List A) (b : Bar dangerous h) -> Fan A
  fanGen′ h (now w) =
    fan []
  fanGen′ h (later bs) =
    fan (map (λ c -> c , fanGen′ (c :: h) (bs c)) (h ⇉))

  fanGen : Fan A
  fanGen = fanGen′ [] barNil
-}

--
-- Bar D h is "monotonic" with respect to D.
--

-- bar_mono

{-
bar-mono : ∀ {A : Type}
  {D D′ : ∀ (h : List A) -> Type} ->
  D  ⊆ D′ ->
  (h : List A) (b : Bar D h) -> Bar D′ h
bar-mono D->D′ h (now w) =
  now (D->D′ w)
bar-mono D->D′ h (later bs) =
  later (λ c -> bar-mono D->D′ (c :: h) (bs c))
-}

-- bar_mono

bar_mono :
  {d, d' : List a -> Type} ->
  (mono : (h : List a) -> d h -> d' h) ->
  (h : List a) -> (b : Bar d h) -> Bar d' h
bar_mono mono h (Now d_h) =
  Now $ mono h d_h
bar_mono mono h (Later bs) =
  Later (\c => bar_mono mono (c :: h) (bs c))

-- bar-⊎

{-
bar-⊎ : {A : Type}
  {D P : ∀ (h : List A) -> Type} ->
  (h : List A) ->
  Bar D h -> Bar (D ∪ P) h
bar-⊎ h b = bar-mono inj₁ h b
-}

export
bar_either :
  {d, p : List a -> Type} ->
  (h : List a) ->
  Bar d h -> Bar (\h => Either (d h) (p h)) h
bar_either h b = bar_mono (\h', dh' => Left dh') h b


--
-- Bar whistles based on the length of the sequence
--

-- pathLengthWhistle

{-
pathLengthWhistle : (A : Type) (l : ℕ) -> BarWhistle A

pathLengthWhistle A l = ⟨ dangerous , monoDangerous , decDangerous , barNil ⟩
  where

  dangerous : (h : List A) -> Type
  dangerous h = l ≤ length h

  monoDangerous : (c : A) (h : List A) -> dangerous h -> dangerous (c :: h)
  monoDangerous c h dh = ≤-step dh

  decDangerous : (h : List A) -> Dec (dangerous h)
  decDangerous h = l ≤? length h

  bar : ∀ m (h : List A) (d : m + length h ≡ l) -> Bar dangerous h
  bar zero h d =
    now (subst (_≤_ l) (P.sym d) (≤′⇒≤ ≤′-refl))
  bar (suc m) h d =
    later (λ c -> bar m (c :: h) m+1+n≡l)
    where
    open ≡-Reasoning
    m+1+n≡l = begin
      m + suc (length h) ≡⟨ m+1+n≡1+m+n m (length h) ⟩
      suc (m + length h) ≡⟨ d ⟩
      l ∎

  barNil : Bar dangerous []
  barNil = bar l [] (l + zero ≡ l ∋ proj₂ *+.+-identity l)
-}

public export
decLTE : (m , n : _) -> Dec (m `LTE` n)
decLTE Z n = Yes LTEZero
decLTE (S m') Z = No $ \m_LTE_Z => succNotLTEzero m_LTE_Z
decLTE (S m') (S n') with (decLTE m' n')
  _ | Yes m'_LTE_n' = Yes $ LTESucc m'_LTE_n'
  _ | No not_m'_LTE_n' =
    No $ \m_LTE_n => not_m'_LTE_n' (fromLteSucc m_LTE_n)

public export
pathLengthWhistle : (a : Type) -> (l : Nat) -> BarWhistle a
pathLengthWhistle a l =
  let
    dangerous : (h : List a) -> Type
    dangerous h = l `LTE` length h

    monoDangerous : (c : a) -> (h : List a) -> dangerous h -> dangerous (c :: h)
    monoDangerous c h dh = lteSuccRight dh

    decDangerous : (h : List a) -> Dec (dangerous h)
    decDangerous h = l `decLTE` length h

    bar : (m : _) -> (h : List a) -> (d : m + length h = l) ->
      Bar dangerous h
    bar Z h d =
      Now $ rewrite d in reflexive
    bar (S m) h d =
      Later $ \c => bar m (c :: h) $ Calc $
        |~ m + S (length h)
        ~~ S (m + length h)  ...( sym $ plusSuccRightSucc m (length h) )
        ~~ l                 ...( d )

    barNil : Bar dangerous []
    barNil = bar l [] (the (l + 0 = l) $ plusZeroRightNeutral l)
  in
  MkBarWhistle dangerous monoDangerous decDangerous barNil


--
-- Bar whistles based on inverse image
--

-- inverseImageWhistle

{-
inverseImageWhistle : {A B : Type} (f : A -> B)
  (w : BarWhistle B) -> BarWhistle A

inverseImageWhistle {A} {B} f ⟨ d , d:: , d? , bd[] ⟩ =
  ⟨ d ∘ map f , monoDangerous , d? ∘ map f , bar [] bd[] ⟩
  where

  monoDangerous : (c : A) (h : List A) ->
    d (map f h) -> d (f c :: map f h)
  monoDangerous c h dh = d:: (f c) (map f h) dh

  bar : (h : List A) (b : Bar d (map f h)) -> Bar (d ∘ map f) h
  bar h (now w) = now w
  bar h (later bs) = later (λ c -> bar (c :: h) (bs (f c)))
-}

--
-- Bar whistles based on well-founded relations
--

-- wfWhistle

{-
wfWhistle : ∀ {A : Type} (_<_ : Rel A Level.zero) -> Decidable₂ _<_ ->
              (wf : Well-founded _<_) -> BarWhistle A
wfWhistle {A} _<_ _<?_ wf = ⟨ dangerous , monoDangerous , decDangerous , barNil ⟩
  where

  dangerous : (h : List A) -> Type
  dangerous [] = ⊥
  dangerous (c :: []) = ⊥
  dangerous (c′ :: c :: h) = ¬ c′ < c ⊎ dangerous (c :: h)

  monoDangerous : (c : A) (h : List A) -> dangerous h -> dangerous (c :: h)
  monoDangerous c [] dh = dh
  monoDangerous c (c′ :: h) dh = inj₂ dh

  decDangerous : (h : List A) -> Dec (dangerous h)
  decDangerous [] = no id
  decDangerous (c :: []) = no id
  decDangerous (c′ :: c :: h) = helper (decDangerous (c :: h))
    where
    helper : Dec (dangerous (c :: h)) -> Dec (¬ (c′ < c) ⊎ dangerous (c :: h))
    helper (yes dch) = yes (inj₂ dch)
    helper (no ¬dch) with c′ <? c
    ... | yes c′<c = no [ (λ c′≮c -> c′≮c c′<c) , ¬dch ]′
    ... | no  c′≮c = yes (inj₁ c′≮c)

  bar : ∀ c (h : List A) -> Acc _<_ c -> Bar dangerous (c :: h)
  bar c h (acc rs) with decDangerous (c :: h)
  ... | yes dch = now dch
  ... | no ¬dch = later helper
    where helper : ∀ c′ -> Bar dangerous (c′ :: c :: h)
          helper c′ with c′ <? c
          ... | yes c′<c = bar c′ (c :: h) (rs c′ c′<c)
          ... | no  c′≮c = now (inj₁ c′≮c)

  barNil : Bar dangerous []
  barNil = later (λ c -> bar c [] (wf c))
-}

--
-- Whistles based on the idea that some elements of the sequence
-- "cover" other elements.
-- c′ ⋑ c means that c′ "covers" c.
--

{-
record ⋑-World (A : Type) : Type₁ where

  infix 4 _⋑_ _⋑?_ _⋑⋑_  _⋑⋑?_

  field
    _⋑_ : A -> A -> Type
    _⋑?_ : Decidable₂ _⋑_

  -- _⋑⋑_

  _⋑⋑_ : (h : List A) (c : A) -> Type
  h ⋑⋑ c = Any (flip _⋑_ c) h

  -- ⋑dangerous

  ⋑dangerous : (h : List A) -> Type
  ⋑dangerous [] = ⊥
  ⋑dangerous (c :: h) = h ⋑⋑ c ⊎ ⋑dangerous h

  -- _⋑⋑?_

  _⋑⋑?_ : (h : List A) (c : A) -> Dec (h ⋑⋑ c)
  h ⋑⋑? c = Any.any (flip _⋑?_ c) h

  -- ⋑decDangerous

  ⋑decDangerous : (h : List A) -> Dec (⋑dangerous h)
  ⋑decDangerous [] = no id
  ⋑decDangerous (c :: h) with h ⋑⋑? c
  ... | yes ⋑c = yes (inj₁ ⋑c)
  ... | no ¬⋑c with ⋑decDangerous h
  ... | yes dh = yes (inj₂ dh)
  ... | no ¬dh = no [ ¬⋑c , ¬dh ]′

-- ⋑-whistle

⋑-whistle : {A : Type} (⋑-world : ⋑-World A)
            (⋑-barNil : Bar (⋑-World.⋑dangerous ⋑-world) []) -> BarWhistle A
⋑-whistle ⋑-world ⋑-barNil =
  ⟨ ⋑dangerous , (λ c h -> inj₂) , ⋑decDangerous , ⋑-barNil ⟩
  where open ⋑-World ⋑-world
-}

--
-- Almost-full relations
--

{-
module bar⋑dangerous⇔af⋑≫ {A : Type} (⋑-world : ⋑-World A) where

  open ⋑-World ⋑-world

  ⋑≫ : (h : List A) (x y : A) -> Type
  ⋑≫ h x y = ⋑dangerous (x :: h) ⊎ (x ⋑ y)

  -- bar⋑dangerous->af⋑≫

  bar⋑dangerous->af⋑≫ : (h : List A) ->
                  Bar ⋑dangerous h -> Almost-full (⋑≫ h)
  bar⋑dangerous->af⋑≫ h (now w) =
    now (λ x y -> inj₁ (inj₂ w))
  bar⋑dangerous->af⋑≫ h (later bs) =
    later {_≫_ = ⋑≫ h} (λ c -> af-⇒ (step c) (afch c))
    where
    open ∼-Reasoning
    afch : ∀ c -> Almost-full (⋑≫ (c :: h))
    afch c = bar⋑dangerous->af⋑≫ (c :: h) (bs c)
    step : ∀ c {x} {y} -> ⋑≫ (c :: h) x y -> ⋑≫ h x y ⊎ ⋑≫ h c x
    step c {x} {y} =
      ⋑≫ (c :: h) x y
        ↔⟨ _ ∎ ⟩
      (⋑dangerous (x :: c :: h) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      ((c :: h ⋑⋑ x ⊎ ⋑dangerous (c :: h)) ⊎ x ⋑ y)
        ↔⟨ ((sym $ ::↔ (flip _⋑_ x)) ⊎-cong ((h ⋑⋑ c ⊎ ⋑dangerous h) ∎)) ⊎-cong
                            ((x ⋑ y) ∎) ⟩
      (((c ⋑ x ⊎ h ⋑⋑ x) ⊎ (h ⋑⋑ c ⊎ ⋑dangerous h)) ⊎ x ⋑ y)
        ∼⟨ [ [ [ inj₂ ∘ inj₂ , inj₁ ∘ inj₁ ∘ inj₁ ]′ ,
             [ inj₂ ∘ inj₁ ∘ inj₁ , inj₁ ∘ inj₁ ∘ inj₂ ]′ ]′
             , inj₁ ∘ inj₂ ]′ ⟩
      (((h ⋑⋑ x ⊎ ⋑dangerous h) ⊎ x ⋑ y) ⊎ ((h ⋑⋑ c ⊎ ⋑dangerous h) ⊎ c ⋑ x))
        ↔⟨ _ ∎ ⟩
      ((⋑dangerous (x :: h) ⊎ x ⋑ y) ⊎ (⋑dangerous (c :: h) ⊎ c ⋑ x))
        ↔⟨ _ ∎ ⟩
      (⋑≫ h x y ⊎ ⋑≫ h c x)
      ∎

  -- af⟱⋑≫->bar⋑dangerous

  af⟱⋑≫->bar⋑dangerous : (h : List A)
    (t : WFT A) -> ⋑≫ h ⟱ t -> Bar ⋑dangerous h

  af⟱⋑≫->bar⋑dangerous h now R⟱ =
    later (λ c -> later (λ c′ -> now (helper c′ c (R⟱ c c′))))
    where
    open ∼-Reasoning
    helper : ∀ c′ c -> ⋑dangerous (c :: h) ⊎ c ⋑ c′ -> ⋑dangerous (c′ :: c :: h)
    helper c′ c =
      (⋑dangerous (c :: h) ⊎ c ⋑ c′)
        ∼⟨ [ inj₂ , inj₁ ∘ inj₁ ]′ ⟩
      ((c ⋑ c′ ⊎ (h ⋑⋑ c′)) ⊎ ⋑dangerous (c :: h))
        ↔⟨ ::↔ (flip _⋑_ c′) ⊎-cong (⋑dangerous (c :: h) ∎) ⟩
      (c :: h ⋑⋑ c′ ⊎ ⋑dangerous (c :: h))
        ↔⟨ _ ∎ ⟩
      ⋑dangerous (c′ :: c :: h) ∎

  af⟱⋑≫->bar⋑dangerous h (later s) R⟱ = later (λ c -> helper c)
    where
    open ∼-Reasoning
    step : ∀ c {x y} -> ⋑≫ h x y ⊎ ⋑≫ h c x -> ⋑≫ (c :: h) x y
    step c {x} {y} =
      (⋑≫ h x y ⊎ ⋑≫ h c x)
        ↔⟨ _ ∎ ⟩
      ((⋑dangerous (x :: h) ⊎ x ⋑ y) ⊎ ⋑dangerous (c :: h) ⊎ c ⋑ x)
        ↔⟨ _ ∎ ⟩
      (((h ⋑⋑ x ⊎ ⋑dangerous h) ⊎ x ⋑ y) ⊎ (h ⋑⋑ c ⊎ ⋑dangerous h) ⊎ c ⋑ x)
        ∼⟨ [ [ [ inj₁ ∘ inj₁ ∘ inj₂ , inj₁ ∘ inj₂ ∘ inj₂ ]′ , inj₂ ]′ ,
             [ [ inj₁ ∘ inj₂ ∘ inj₁ , inj₁ ∘ inj₂ ∘ inj₂ ]′ ,
                 inj₁ ∘ inj₁ ∘ inj₁ ]′ ]′ ⟩
      (((c ⋑ x ⊎ h ⋑⋑ x) ⊎ h ⋑⋑ c ⊎ ⋑dangerous h) ⊎ x ⋑ y)
        ↔⟨ ((::↔ (flip _⋑_ x)) ⊎-cong ((h ⋑⋑ c ⊎ ⋑dangerous h) ∎)) ⊎-cong
                (x ⋑ y ∎) ⟩
      ((c :: h ⋑⋑ x ⊎ ⋑dangerous (c :: h)) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      (⋑dangerous (x :: c :: h) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      ⋑≫ (c :: h) x y
      ∎

    helper : ∀ c -> Bar ⋑dangerous (c :: h)
    helper c =
      af⟱⋑≫->bar⋑dangerous (c :: h) (s c) (⟱-⇒ (step c) (s c) (R⟱ c))

  -- af⋑≫->bar⋑dangerous

  af⋑≫->bar⋑dangerous : (h : List A) -> Almost-full (⋑≫ h) -> Bar ⋑dangerous h

  af⋑≫->bar⋑dangerous h af with af->af⟱ af
  ... | t , R⟱ = af⟱⋑≫->bar⋑dangerous h t R⟱

  --
  -- bar⋑dangerous⇔af⋑≫
  --

  bar⋑dangerous⇔af⋑≫ : (h : List A) ->
    Bar ⋑dangerous h ⇔ Almost-full (⋑≫ h)

  bar⋑dangerous⇔af⋑≫ h = equivalence (bar⋑dangerous->af⋑≫ h) (af⋑≫->bar⋑dangerous h)
-}
