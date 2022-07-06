module AlmostFullRel

{-
open import Level
  using ()

open import Data.Product as Prod
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)

open import Function
open import Function.Equivalence
  using (_⇔_; equivalence)

open import Relation.Binary
  using (Rel; _⇒_) renaming (Decidable to Decidable₂)
open import Function.Inverse as Inv
  using (_↔_; module Inverse)
open import Function.Related as Related
  using ()
  renaming (module EquationalReasoning to ∼-Reasoning)
import Relation.Binary.Sigma.Pointwise as Σ

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to P[_])
-}

%default total

--
-- Almost-full relations
--

data Almost_full : (r : a -> a -> Type) -> Type where
  Now   : ((x, y : a) -> r x y) ->
    Almost_full r
  Later : ((z : a) -> Almost_full (\x, y => Either (r x y) (r z x))) ->
    Almost_full r
{-
data Almost_full {ℓ} {A : Set ℓ} : Rel A ℓ -> Set (Level.suc ℓ) where
  now   : ∀ {_≫_} -> (z : ∀ x y -> x ≫ y) ->
               Almost_full _≫_
  later : ∀ {_≫_} -> (s : ∀ c -> Almost_full (λ x y -> x ≫ y ⊎ c ≫ x)) ->
               Almost_full _≫_
-}

-- af_mono

af_mono : (pq : {x , y : a} -> p x y -> q x y) ->
  Almost_full p -> Almost_full q
af_mono pq (Now z) =
  Now (\x, y => pq (z x y))
af_mono pq (Later s) =
  Later (\z => af_mono (either (Left . pq) (Right . pq)) (s z))

--
-- Well-founded trees
--

data WFT : (a  :  Type) -> Type where
  WFTNow   : WFT a
  WFTLater : (s : a -> WFT a) -> WFT a

{-
data WFT {ℓ} (A  :  Set ℓ) : Set ℓ where
  now   : WFT A
  later : (s : A -> WFT A) -> WFT A
-}

--
-- _⟱_ (secure by)
-- The tree can be separated from the relation.
--
-- (This is a form of "staging", a wft being a "program" that
-- transforms a relation.)
--

{-
infix 4 _⟱_

-- _⟱_

_⟱_ : ∀ {ℓ} {A : Set ℓ} (_≫_ : Rel A ℓ) (t :  WFT A) -> Set ℓ
_≫_ ⟱ now = ∀ x y -> x ≫ y
_≫_ ⟱ later g = ∀ c -> (λ x y -> x ≫ y ⊎ c ≫ x) ⟱ g c
-}

-- Almost_full⟱

{-
Almost_full⟱ : ∀ {ℓ} {A : Set ℓ} (R : Rel A ℓ) -> Set ℓ
Almost_full⟱ {A = A} R = ∃ λ t -> R ⟱ t
-}

-- af⟱->af

{-
af⟱->af : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} -> Almost_full⟱ R -> Almost_full R

af⟱->af (now , R⟱) =
  now R⟱
af⟱->af (later s , R⟱) =
  later (λ c -> af⟱->af (s c , R⟱ c))
-}

-- af->af⟱

{-
af->af⟱ : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} -> Almost_full R -> Almost_full⟱ R

af->af⟱ (now z) =
  now , z
af->af⟱ {R = R} (later s) =
  later (λ c -> proj₁ (af->af⟱ (s c))) , (λ c -> proj₂ (af->af⟱ (s c)))
-}

-- af⟱⇔af

{-
af⟱⇔af : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} -> Almost_full⟱ R ⇔ Almost_full R

af⟱⇔af = equivalence af⟱->af af->af⟱
-}

-- Given `Almost_full R`, we can extract the corresponding wft tree.

-- af⇒wft

{-
wft : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} -> Almost_full R -> WFT A

wft (now z) = now
wft (later s) = later (λ c -> wft (s c))
-}

-- af⇒wft is sound.

-- af⇒⟱

{-
af⇒⟱ : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} -> (af : Almost_full R) ->
           R ⟱ (wft af)

af⇒⟱ (now z) = z
af⇒⟱ (later s) = λ c -> af⇒⟱ (s c)
-}

--
-- In some proofs there appear expressons of the form
--     f (af_mono p⇒q (s c))
-- so that the termination checker cannot see that the argument of f
-- is smaller than `(later s)` . But the function f is total, because
-- `wft (s c)` is smaller than `wft (s c)` and
--      wft (af_mono p⇒q (s c)) ≡ wft (s c)
-- This is made explicit in the signature of ⟱-⇒ ,
-- so that we can use induction on t, rather than on `Almost_full R` .

-- ⟱-⇒

{-
⟱-⇒ :
  ∀ {ℓ} {A : Set ℓ} {P : Rel A ℓ} {Q : Rel A ℓ}
    (p⇒q : P ⇒ Q) (t : WFT A) -> P ⟱ t -> Q ⟱ t

⟱-⇒ p⇒q now P⟱t =
  λ x y -> p⇒q (P⟱t x y)

⟱-⇒ p⇒q (later s) P⟱t =
  λ c -> ⟱-⇒ (Sum.map p⇒q p⇒q) (s c) (P⟱t c)
-}
