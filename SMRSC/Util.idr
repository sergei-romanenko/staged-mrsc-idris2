module SMRSC.Util

{-
open import Level
  using (Lift; lift; lower)

open import Data.Bool
  using (Bool; true; false; _∧_)
open import Data.Nat
  hiding(_⊔_)
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>)
open import Data.List
open import Data.List.Properties
  using (::-injective; foldr-universal; foldr-fusion)
open import Data.List.Any
  using (Any; here; there; module Membership-=)
open import Data.List.Any.Properties
  using (Any-cong; ⊥↔Any[]; Any↔; ++↔; ::↔; return↔; map↔; concat↔; ⊎↔)
open import Data.List.Any.Membership as MB
  using (map-∈↔)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _::_; lookup)
open import Data.Product as Prod
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; <_,_>; uncurry)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Unit
  using(⊤; tt)
open import Data.Empty

open import Function
open import Function.Equality
  using (_⟨$⟩_)
open import Function.Equivalence as Eq
  using (_⇔_; module Equivalence)
open import Function.Inverse as Inv
  using (_↔_; module Inverse)

open import Function.Related as Related
  using ()
  renaming (module EquationalReasoning to ∼-Reasoning)

import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.Sum
  using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise
  using (_×-cong_)

open import Relation.Binary.List.Pointwise as Pointwise
  using ([]; _::_)

open import Relation.Nullary
open import Relation.Unary
  using () renaming (Decidable to Decidable₁)
open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
  renaming ([_] to P[_])

open import Algebra
  using (module CommutativeSemiring)

module *+ = CommutativeSemiring Data.Nat.Properties.commutativeSemiring

open import Function.Related.TypeIsomorphisms
  using(×⊎-CommutativeSemiring)

module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)

open Membership-=
-}

import Data.List
import Data.Vect
import Control.Function
import Data.List.Elem
import Data.List.Quantifiers

%default total

--
-- Implication reasoning
--

prefix 1  |~~
infixl 0  ~~>
infix  1  ...
infixr 0 |>

-- Implication is a preorder relation...

public export
(|~~) : (0 a : Type) -> (a -> a)
(|~~) a = id

public export
(~~>) : (p : a -> b) -> (q : b -> c) -> (a -> c)
(~~>) p q = q . p

public export
(...) : (0 b : Type) -> (a -> b) -> (a -> b)
(...) b xy = xy

public export
(|>) : forall a, b. (x : a) -> (f : a -> b) -> b
(|>) x f = f x


{-
-- m+1+n≡1+m+n

m+1+n≡1+m+n : ∀ m n -> m + suc n = suc (m + n)
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

-- m∸n+n≡m

m∸n+n≡m : (m n : ℕ) -> n ≤ m -> m ∸ n + n = m
m∸n+n≡m m .0 z≤n = begin
  m ∸ 0 + 0
    ≡⟨⟩
  m + 0
    ≡⟨ proj₂ *+.+-identity m ⟩
  m
  ∎
  where open =-Reasoning
m∸n+n≡m .(suc n) .(suc m) (s≤s {m} {n} n≤m) = begin
  suc n ∸ suc m + suc m
    ≡⟨⟩
  n ∸ m + suc m
    ≡⟨ m+1+n≡1+m+n (n ∸ m) m ⟩
  suc (n ∸ m + m)
    ≡⟨ cong suc (m∸n+n≡m n m n≤m) ⟩
  suc n
  ∎
  where open =-Reasoning


-- foldr∘map

foldr∘map : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A -> B) (g : B -> C -> C) (n : C) ->
  foldr g n ∘ map f ≗ foldr (g ∘ f) n
foldr∘map f g n =
  foldr-universal (foldr g n ∘ map f) (g ∘ f) n refl (λ x xs -> refl)

-- gfilter-++-commute

gfilter-++-commute :
  ∀ {a b} {A : Set a} {B : Set b} (f : A -> Maybe B) xs ys ->
    gfilter f (xs ++ ys) = gfilter f xs ++ gfilter f ys

gfilter-++-commute f [] ys = refl
gfilter-++-commute f (x :: xs) ys with f x
... | just y = cong (_::_ y) (gfilter-++-commute f xs ys)
... | nothing = gfilter-++-commute f xs ys

-- filter-++-commute

filter-++-commute :
  ∀ {a} {A : Set a} (p : A -> Bool) xs ys ->
    filter p (xs ++ ys) = filter p xs ++ filter p ys

filter-++-commute f xs ys =
  gfilter-++-commute (λ z -> Data.Bool.if f z then just z else nothing) xs ys

-- filter∘map

filter∘map :
  ∀ {a b} {A : Set a} {B : Set b} (p : B -> Bool) (f : A -> B) xs ->
  filter p (map f xs) = map f (filter (p ∘ f) xs)

filter∘map p f [] = refl
filter∘map p f (x :: xs) with p (f x)
... | true = cong (_::_ (f x)) (filter∘map p f xs)
... | false = filter∘map p f xs

-- filter-false

filter-false :
  ∀ {a} {A : Set a} (xs : List A) ->
    filter (const false) xs = []

filter-false [] = refl
filter-false (x :: xs) = filter-false xs

-- filter-cong

filter-cong :
  ∀ {a} {A : Set a} {p q : A -> Bool} ->
    p ≗ q -> filter p ≗ filter q

filter-cong p≗q [] = refl
filter-cong {p = p} {q = q} p≗q (x :: xs)
  rewrite p≗q x with q x
... | true = cong (_::_ x) (filter-cong p≗q xs)
... | false = filter-cong p≗q xs
-}

--
-- `Pointwise r xs ys` means that `r x y` for all respective
-- `Elem x xs` and `Elem y ys`.
--

public export
data Pointwise : (r : a -> b -> Type) -> List a -> List b -> Type where
  Nil  : Pointwise r [] []
  (::) : {x, y, r : _} ->
    r x y -> Pointwise r xs ys -> Pointwise r (x :: xs) (y :: ys)

public export
Uninhabited (Pointwise r [] (y :: ys)) where
  uninhabited [] impossible
  uninhabited (x :: z) impossible

public export
Uninhabited (Pointwise r (x :: xs) []) where
  uninhabited [] impossible
  uninhabited (x :: xs) impossible

decPointwise : {r : a -> b -> Type} -> (dec : (x : a) -> (y : b) -> Dec(r x y)) ->
  (xs : List a) -> (ys :List b) -> Dec (Pointwise r xs ys)
decPointwise dec [] [] = Yes []
decPointwise dec [] (y :: ys) = No absurd
decPointwise dec (x :: xs) [] = No absurd
decPointwise dec (x :: xs) (y :: ys) with (dec x y)
  _ | Yes r_x_y with (decPointwise dec xs ys)
    _ | Yes pw = Yes (r_x_y :: pw)
    _ | No npw = No $ \(_ :: pw) => npw pw
  _ | No nr_x_y = No $ \(r_x_y :: _) => nr_x_y r_x_y

{-
map : R ⇒ S → Pointwise R ⇒ Pointwise S
map R⇒S []            = []
map R⇒S (Rxy ∷ Rxsys) = R⇒S Rxy ∷ map R⇒S Rxsys
-}

%hint
export
map_pw : {r, s : a -> b -> Type} ->
  ({x, y : _} -> r x y -> s x y) ->
  Pointwise r xs ys -> Pointwise s xs ys
map_pw f [] = []
map_pw f (rxy :: rxsys) = f rxy :: map_pw f rxsys


{-

public export
Pointwise : (r : a -> b -> Type) -> List a -> List b -> Type
Pointwise r xs ys = All (uncurry r) (zip xs ys)
-}

{-
pw_corr12 : Pointwise r xs ys -> Pointwise' r xs ys
pw_corr12 [] = []
pw_corr12 (rxy :: pw) = rxy :: pw_corr12 pw
-}

{-
decPointwise : {r : a -> b -> Type} -> (dec : (x : a) -> (y : b) -> Dec(r x y)) ->
  (xs : List a) -> (ys :List b) -> Dec (Pointwise r xs ys)
decPointwise dec xs ys =
  all (\(x, y) => dec x y) (zip xs ys)
-}


--
-- Some "technical" theorems about `Any`
--

-- ⊥⊎

{-
⊥⊎ : ∀ {A : Set} -> A ↔ (⊥ ⊎ A)

⊥⊎ {A} = record
  { to = ->-to-⟶ inj₂
  ; from = ->-to-⟶ to
  ; inverse-of = record
    { left-inverse-of = λ x -> refl
    ; right-inverse-of = from∘to
    }
  }
  where
  to : (⊥ ⊎ A) -> A
  to = [ ⊥-elim , id ]′
  from∘to : (x : ⊥ ⊎ A) -> inj₂ (to x) = x
  from∘to (inj₁ ())
  from∘to (inj₂ x) = refl

-- ⊥×

⊥× : ∀ {A : Set} -> ⊥ ↔ (⊥ × A)

⊥× {A} = record
  { to = ->-to-⟶ (λ ())
  ; from = ->-to-⟶ (uncurry (λ a⊥ x -> a⊥))
  ; inverse-of = record
    { left-inverse-of = λ a⊥ -> ⊥-elim a⊥
    ; right-inverse-of = uncurry (λ a⊥ x -> ⊥-elim a⊥)
    }
  }

-- ⊥↔[]∈map::

⊥↔[]∈map:: : ∀ {A : Set} (x : A) (yss : List (List A)) ->
  ⊥ ↔ (List A ∋ []) ∈ map (_::_ x) yss

⊥↔[]∈map:: {A} x yss = record
  { to = ->-to-⟶ (to x yss)
  ; from = ->-to-⟶ (from x yss)
  ; inverse-of = record
    { left-inverse-of = λ a⊥ -> ⊥-elim a⊥
    ; right-inverse-of = to∘from x yss
    }
  }
  where
  to : ∀ (x : A) (yss : List (List A)) -> ⊥ -> [] ∈ map (_::_ x) yss
  to x [] a⊥ = ⊥-elim a⊥
  to x (ys :: yss) a⊥ = there (to x yss a⊥)

  from : ∀ (x : A) (yss : List (List A)) -> [] ∈ map (_::_ x) yss -> ⊥
  from x [] ()
  from x (ys :: yss) (here ())
  from x (ys :: yss) (there []∈map::) = from x yss []∈map::

  to∘from : ∀ (x′ : A) (yss′ : List (List A)) ->
    (p : [] ∈ map (_::_ x′) yss′) -> to x′ yss′ (from x′ yss′ p) = p
  to∘from x [] ()
  to∘from x (ys :: yss) (here ())
  to∘from x (ys :: yss) (there p) = cong there (to∘from x yss p)

-- concat↔∘Any↔

concat↔∘Any↔ : {A B : Set}
  (z : B) (g : B -> B) (f : A -> List B) (xs : List A) ->
  ∃ (λ x -> x ∈ xs × ∃ (λ y -> y ∈ f x × z = g y)) ↔
  z ∈ map g (concat (map f xs))
concat↔∘Any↔ z g f xs =
  ∃ (λ x -> x ∈ xs × ∃ (λ y -> y ∈ f x × z = g y))
    ∼⟨ Σ.cong Inv.id (Inv.id ×-cong Any↔) ⟩
  ∃ (λ x -> x ∈ xs × (Any (λ y -> z = g y) (f x)))
    ∼⟨ _ ∎ ⟩
  ∃ (λ x -> x ∈ xs × (Any (λ y -> z = g y) ∘ f) x)
    ∼⟨ _ ∎ ⟩
  ∃ (λ x -> x ∈ xs × (Any (_≡_ z ∘ g) ∘ f) x)
    ∼⟨ Any↔ ⟩
  Any (Any (_≡_ z ∘ g) ∘ f) xs
    ∼⟨ map↔ ⟩
  Any (Any (_≡_ z ∘ g)) (map f xs)
    ∼⟨ concat↔ ⟩
  Any (_≡_ z ∘ g) (concat (map f xs))
    ∼⟨ map↔ ⟩
  Any (_≡_ z) (map g (concat (map f xs)))
    ∼⟨ _ ∎ ⟩
  z ∈ map g (concat (map f xs))
  ∎
  where open ∼-Reasoning
-}

{-
-- ∈*∘map

∈*∘map-> :
  ∀ {A B : Set} (f : A -> List B) (xs : List A) {ys : List B} ->
  Pointwise.Rel _∈_ ys (map f xs) -> Pointwise.Rel (λ x y -> y ∈ f x) xs ys

∈*∘map-> f [] {[]} _ = []
∈*∘map-> f [] {_ :: _} ()
∈*∘map-> f (x :: xs) (y∈fx :: ys∈*) =
  y∈fx :: ∈*∘map-> f xs ys∈*
-}

%hint
export
pw_elem_map : (f : a -> List b) -> (xs : List a) -> {ys : List b} ->
  Pointwise Elem ys (map f xs) -> Pointwise (\x, y => Elem y (f x)) xs ys

{-
-- ∈*∘map←

∈*∘map← :
  ∀ {A B : Set} (f : A -> List B) (xs : List A) {ys : List B} ->
  Pointwise.Rel (λ x y -> y ∈ f x) xs ys -> Pointwise.Rel _∈_ ys (map f xs)

∈*∘map← f [] [] = []
∈*∘map← f (x :: xs) (y∈fx :: xs∈*) = y∈fx :: ∈*∘map← f xs xs∈*
-}

{-
∈-map⁻ : ∀ {y xs} -> y ∈ map f xs -> ∃ λ x -> x ∈ xs × y = f x

map-∈↔ : ∀ {y xs} -> (∃ λ x -> x ∈ xs × y = f x) ↔ y ∈ map f xs
-}

export
map_elem : (y : b) -> (xs : List a) -> Elem y (map f xs) -> (x ** (Elem x xs, y = f x))
map_elem _ [] Here impossible
map_elem _ [] (There x) impossible
map_elem _ (x' :: xs) Here = (x' ** (Here, Refl))
map_elem y (x' :: xs) (There elem_y) with (map_elem y xs elem_y)
  _ | (x ** (elem_x, y__fx)) = (x ** (There elem_x, y__fx))

  -- map_elem y xs elem_y

{-
elem_map : (y : a) -> (xs : List a) ->
  (x ** (Elem x xs, y = f x)) -> Elem y (map f xs)
elem_map y [] ((x ** (elem_x_nil, y__fx))) = absurd elem_x_nil
elem_map y (x' :: xs) (x ** (elem_x, y__fx)) = ?op_rhs
-}


--
-- Cartesian product
--

-- cartesian

public export
cartesian2 : List a -> List (List a) -> List (List a)
cartesian2 [] yss = []
cartesian2 (x :: xs) yss = map (x ::) yss ++ cartesian2 xs yss

public export
cartesian : List (List a) -> List (List a)
cartesian [] = [ [] ]
cartesian (xs :: xss) = cartesian2 xs (cartesian xss)

--
-- Some "technical" theorems about cartesian products
--

{-
-- cartesian-is-foldr

cartesian-is-foldr : ∀  {A : Set} (xss : List (List A)) ->
  cartesian xss = foldr cartesian2 [ [] ] xss

cartesian-is-foldr [] = refl
cartesian-is-foldr (xs :: xss) = cong (cartesian2 xs) (cartesian-is-foldr xss)

-- cartesian∘map

cartesian∘map : ∀ {A B : Set} (f : A -> List B) (xs : List A) ->
  cartesian (map f xs) = foldr (cartesian2 ∘ f) [ [] ]  xs
cartesian∘map f xs = begin
  cartesian (map f xs)
    ≡⟨ cartesian-is-foldr (map f xs) ⟩
  foldr cartesian2 [ [] ] (map f xs)
    ≡⟨ foldr∘map f cartesian2 [ [] ] xs ⟩
  foldr (cartesian2 ∘ f) [ [] ] xs
  ∎
  where open =-Reasoning
-}

{-
-- cartesian2[]

cartesian2[] : ∀ {A : Set} (xs : List A) ->
  cartesian2 xs [] = []

cartesian2[] [] = refl
cartesian2[] (x :: xs) = cartesian2[] xs
-}

-- cartesian2_nil

%hint
public export
cartesian2_nil : (xs : List a) ->
  cartesian2 xs [] = []
cartesian2_nil [] = Refl
cartesian2_nil (x :: xs) = cartesian2_nil xs

{-
-- ⊥↔[]∈cartesian2

⊥↔[]∈cartesian2 : ∀ {A : Set} (xs : List A) (yss : List (List A)) ->
  ⊥ ↔ [] ∈ cartesian2 xs yss

⊥↔[]∈cartesian2 [] yss =
  ⊥↔Any[]

⊥↔[]∈cartesian2 {A} (x :: xs) yss =
  ⊥
    ↔⟨ ⊥⊎ ⟩
  (⊥ ⊎ ⊥)
    ↔⟨ ⊥↔[]∈map:: x yss ⊎-cong ⊥↔[]∈cartesian2 xs yss ⟩
  ([] ∈ map (_::_ x) yss ⊎ [] ∈ cartesian2 xs yss)
    ↔⟨ ++↔ ⟩
  [] ∈ (map (_::_ x) yss ++ cartesian2 xs yss)
  ∎
  where open ∼-Reasoning
-}

%hint
elem_concat : (z, xs, ys : _) ->
  Elem z (xs ++ ys) -> Either (Elem z xs) (Elem z ys)
elem_concat z [] ys elem = Right elem
elem_concat z (z :: xs) ys Here = Left Here
elem_concat z (x :: xs) ys (There elem) with (elem_concat z xs ys elem)
  _ | Left h = Left (There h)
  _ | Right h = Right h

%hint
not_elem_nil_map : (x : a) -> (yss : List (List a)) ->
  Not (Elem [] (map (x ::) yss))
not_elem_nil_map x [] elem = absurd elem
not_elem_nil_map x (ys :: yss) (There elem) =
  not_elem_nil_map x yss elem

%hint
not_elem_nil_cartesian2 : (xs, yss : _) -> Not (Elem [] (cartesian2 xs yss))
not_elem_nil_cartesian2 [] yss = absurd
-- not_elem_nil_cartesian2 (x :: xs) yss elem = ?not_elem_nil_cartesian2_rhs_1
not_elem_nil_cartesian2 (x :: xs) yss =
  |~~ Elem [] (cartesian2 (x :: xs) yss)
  ~~> Elem [] (map (x ::) yss ++ cartesian2 xs yss)
    ... id
  ~~> Either (Elem [] (map (x ::) yss)) (Elem [] (cartesian2 xs yss))
    ... (elem_concat [] (map (x ::) yss) (cartesian2 xs yss))
  ~~> Void
    ... (either (not_elem_nil_map x yss) (not_elem_nil_cartesian2 xs yss))


-- Some important properties of `cartesian`

{-
-- ≡×∈->map::

≡×∈->map:: : ∀ {A : Set} {x : A} {xs : List A} {y : A} {yss : List (List A)} ->
  (x = y × xs ∈ yss) -> x :: xs ∈ map {B = List A} (_::_ y) yss

≡×∈->map:: (refl , here refl) = here refl
≡×∈->map:: (refl , there xs∈yss) = there (≡×∈->map:: (refl , xs∈yss))

-- map::->≡×∈

map::->≡×∈ : ∀ {A : Set} {x : A} {xs : List A} {y : A} {yss : List (List A)} ->
  x :: xs ∈ map {B = List A} (_::_ y) yss -> (x = y × xs ∈ yss)

map::->≡×∈ {yss = []} ()
map::->≡×∈ {yss = ys :: yss} (here x::xs≡y::ys) =
  helper (::-injective x::xs≡y::ys)
  where helper : _ -> _
        helper (x≡y , xs≡ys) = x≡y , here xs≡ys
map::->≡×∈ {yss = ys :: yss} (there x::xs∈) =
  helper (map::->≡×∈ x::xs∈)
  where helper : _ -> _
        helper (x≡y , xs∈yss) = x≡y , there xs∈yss

-- ≡×∈↔map::

≡×∈↔map:: : ∀ {A : Set} (x : A) (xs : List A) (y : A) (yss : List (List A)) ->
  (x = y × xs ∈ yss) ↔ x :: xs ∈ map {B = List A} (_::_ y) yss

≡×∈↔map:: {A} x xs y yss = record
  { to = ->-to-⟶ ≡×∈->map::
  ; from = ->-to-⟶ map::->≡×∈
  ; inverse-of = record
    { left-inverse-of = to∘from
    ; right-inverse-of = from∘to
    }
  }
  where
  open ∼-Reasoning

  to∘from : ∀ {A : Set} {x : A} {xs : List A} {y : A} {yss : List (List A)} ->
    (p : x = y × xs ∈ yss) -> map::->≡×∈ (≡×∈->map:: p) = p
  to∘from (refl , here refl) = refl
  to∘from {y = y} {yss = ys :: yss} (refl , there xs∈yss)
    rewrite to∘from {y = y} (refl {x = y} , xs∈yss)
    = refl

  from∘to : ∀ {A : Set} {x : A} {xs : List A} {y : A} {yss : List (List A)} ->
    (p : x :: xs ∈ map (_::_ y) yss) -> ≡×∈->map:: (map::->≡×∈ p) = p
  from∘to {yss = []} ()
  from∘to {yss = ys :: yss} (here refl) = refl
  from∘to {yss = ys :: yss} (there x::xs∈) with map::->≡×∈ x::xs∈ | from∘to x::xs∈
  ... | refl , xs∈yss | ft rewrite ft = refl
-}

%hint
eq_elem_map : (x : a) -> (xs : List a) -> (y : a) -> (yss : List (List a)) ->
  Elem (x :: xs) (map (y ::) yss) -> (x = y, Elem xs yss)
eq_elem_map x xs y [] elem = absurd elem
eq_elem_map x xs x (xs :: yss) Here = (Refl, Here)
eq_elem_map x xs y (ys :: yss) (There elem) with (eq_elem_map x xs y yss elem)
  _ | (x__y, elem_xs_yss) = (x__y, There elem_xs_yss)

%hint
elem_cartesian2 : (x : a) -> (xs, ys : List a) -> (yss : List (List a)) ->
  Elem (x :: xs) (cartesian2 ys yss) -> (Elem x ys, Elem xs yss)
elem_cartesian2 x xs [] yss = absurd
elem_cartesian2 x xs (y :: ys) yss =
  |~~ Elem (x :: xs) (cartesian2 (y :: ys) yss)
  ~~> Elem (x :: xs) (map (y ::) yss ++ cartesian2 ys yss)
    ... id
  ~~> Either (Elem (x :: xs) (map (y ::) yss)) (Elem (x :: xs) (cartesian2 ys yss))
    ... (elem_concat (x :: xs) (map (\arg => y :: arg) yss) (cartesian2 ys yss))
  ~~> Either (x = y, Elem xs yss) (Elem x ys, Elem xs yss)
    ... (bimap (eq_elem_map x xs y yss) (elem_cartesian2 x xs ys yss))
  ~~> (Either (x = y) (Elem x ys), Elem xs yss)
    ... (either (bimap Left id) (bimap Right id))
  ~~> (Elem x (y :: ys), Elem xs yss)
    ... (bimap (either (\x__y => replace {p = Elem x . (:: ys)} x__y Here) There) id)

%hint
either_eq_elem : Either (x = y) (Elem x ys) -> Elem x (y :: ys)
either_eq_elem (Left Refl) = Here
either_eq_elem (Right elem) = There elem

%hint
cartesian2_elem :
  (x : a) -> (xs, ys : List a) -> (yss : List (List a)) ->
  Elem (x :: xs) (cartesian2 ys yss) -> (Elem x ys, Elem xs yss)
cartesian2_elem x xs [] yss = \elem => absurd elem
cartesian2_elem x xs (y :: ys) yss =
  |~~ Elem (x :: xs) (cartesian2 (y :: ys) yss)
  ~~> Elem (x :: xs) (map (y ::) yss ++ cartesian2 ys yss)
    ... id
  ~~> Either (Elem (x :: xs) (map (y ::) yss)) (Elem (x :: xs) (cartesian2 ys yss))
    ... (elem_concat (x :: xs) (map (y ::) yss) (cartesian2 ys yss))
  ~~> Either (x = y, Elem xs yss) (Elem x ys, Elem xs yss)
    ... (bimap (eq_elem_map x xs y yss) (elem_cartesian2 x xs ys yss))
  ~~> (Either (x = y) (Elem x ys),  Elem xs yss)
    ... (either (bimap Left id) (bimap Right id))
  ~~> (Elem x (y :: ys), Elem xs yss)
    -- ... (bimap either_eq_elem id)
    ... (bimap (either (\x__y => replace {p = Elem x . (:: ys)} x__y Here) There) id)

{-
-- ∈∈↔::cartesian

∈∈↔::cartesian2 :
  ∀ {A : Set} (x : A) (xs ys : List A) (yss : List (List A)) ->
    (x ∈ ys × xs ∈ yss) ↔ x :: xs ∈ cartesian2 ys yss

∈∈↔::cartesian2 x xs [] yss =
  (x ∈ [] × xs ∈ yss)
    ↔⟨ (sym $ ⊥↔Any[]) ×-cong (_ ∎) ⟩
  (⊥ × xs ∈ yss)
    ↔⟨ sym $ ⊥× ⟩
  ⊥
    ↔⟨ ⊥↔Any[] ⟩
  x :: xs ∈ []
  ∎
  where open ∼-Reasoning

∈∈↔::cartesian2 x xs (y :: ys) yss =
  (x ∈ y :: ys × xs ∈ yss)
    ↔⟨ sym (::↔ (_≡_ x)) ×-cong (_ ∎) ⟩
  ((x = y ⊎ x ∈ ys) × xs ∈ yss)
    ↔⟨ proj₂ ×⊎.distrib (xs ∈ yss) (x = y) (x ∈ ys) ⟩
  (x = y × xs ∈ yss ⊎ x ∈ ys × xs ∈ yss)
    ↔⟨ ≡×∈↔map:: x xs y yss ⊎-cong ∈∈↔::cartesian2 x xs ys yss ⟩
  (x :: xs ∈ map (_::_ y) yss ⊎ x :: xs ∈ cartesian2 ys yss)
    ↔⟨ ++↔ ⟩
  x :: xs ∈ (map (_::_ y) yss ++ cartesian2 ys yss)
    ≡⟨ refl ⟩
  x :: xs ∈ cartesian2 (y :: ys) yss
  ∎
  where open ∼-Reasoning

-- ⊥↔[]∈*

⊥↔[]∈* : ∀ {A : Set} (ys : List A) yss ->
  ⊥ ↔ Pointwise.Rel _∈_ [] (ys :: yss)
⊥↔[]∈* {A} ys yss = record
  { to = ->-to-⟶ (λ a⊥ -> ⊥-elim a⊥)
  ; from = ->-to-⟶ (from ys yss)
  ; inverse-of = record
    { left-inverse-of = (λ ())
    ; right-inverse-of = (from∘to ys yss)
    }
  }
  where
  from : ∀ (ys : List A) (yss : List (List A)) ->
    Pointwise.Rel _∈_ [] (ys :: yss) -> ⊥
  from y yss ()
  from∘to : ∀ (ys : List A) (yss : List (List A)) ->
    (p : Pointwise.Rel _∈_ [] (ys :: yss)) -> ⊥-elim (from ys yss p) = p
  from∘to ys yss ()



×∈*↔∈* : ∀ {A : Set} (x : A) xs ys yss ->
  (x ∈ ys × Pointwise.Rel _∈_ xs yss) ↔ Pointwise.Rel _∈_ (x :: xs) (ys :: yss)

×∈*↔∈* x xs ys yss = record
  { to = ->-to-⟶ to
  ; from = ->-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = to∘from
    ; right-inverse-of = from∘to
    }
  }
  where
  to : x ∈ ys × Pointwise.Rel _∈_ xs yss ->
          Pointwise.Rel _∈_ (x :: xs) (ys :: yss)
  to (x∈ys , xs∈*yss) = x∈ys :: xs∈*yss
  from : Pointwise.Rel _∈_ (x :: xs) (ys :: yss) ->
           x ∈ ys × Pointwise.Rel _∈_ xs yss
  from (x∈ys :: xs∈*yss) = x∈ys , xs∈*yss
  to∘from : (p : x ∈ ys × Pointwise.Rel _∈_ xs yss) -> from (to p) = p
  to∘from (x∈ys , xs∈*yss) = refl
  from∘to : (p : Pointwise.Rel _∈_ (x :: xs) (ys :: yss)) -> to (from p) = p
  from∘to (x∈ys :: xs∈*yss) = refl
-}

--
-- A proof of correctness of `cartesian`
-- with respect to `Pointwise.Rel _∈_`

-- cartesian_pw_elem

%hint
export
cartesian_pw_elem :
  (xs : List a) -> (yss : List (List a)) ->
    Elem xs (cartesian yss) -> Pointwise Elem xs yss
cartesian_pw_elem [] [] elem = []
cartesian_pw_elem [] (ys :: yss) elem =
  void $ (not_elem_nil_cartesian2 ys (cartesian yss)) elem
cartesian_pw_elem (x :: xs) [] (There there) = absurd there
cartesian_pw_elem (x :: xs) (ys :: yss) elem = elem |>
  |~~ Elem (x :: xs) (cartesian (ys :: yss))
  ~~> Elem (x :: xs) (cartesian2 ys (cartesian yss))
    ... id
  ~~> (Elem x ys, Elem xs (cartesian yss))
    ... (elem_cartesian2 x xs ys (cartesian yss))
  ~~> (Elem x ys, Pointwise Elem xs yss)
    ... (bimap id (cartesian_pw_elem xs yss))
  ~~> Pointwise Elem (x :: xs) (ys :: yss)
    ... uncurry (::)

{-
-- ∈*↔∈cartesian

∈*↔∈cartesian :
  ∀ {A : Set} {xs : List A} {yss : List (List A)} ->
    Pointwise.Rel _∈_ xs yss ↔ xs ∈ cartesian yss

∈*↔∈cartesian {A} {[]} {[]} = record
  { to = ->-to-⟶ from
  ; from = ->-to-⟶ to
  ; inverse-of = record
    { left-inverse-of = to∘from
    ; right-inverse-of = from∘to
    }
  }
  where
  from : _ -> _
  from p = here refl
  to : _ -> _
  to p = []
  to∘from : (p : Pointwise.Rel _∈_ [] []) -> [] = p
  to∘from [] = refl
  from∘to : (p : [] ∈ [] :: []) -> here refl = p
  from∘to (here refl) = refl
  from∘to (there ())

∈*↔∈cartesian {A} {[]} {ys :: yss} =
  Pointwise.Rel _∈_ [] (ys :: yss)
    ↔⟨ sym $ ⊥↔[]∈* ys yss ⟩
  ⊥
    ↔⟨ ⊥↔[]∈cartesian2 ys (cartesian yss) ⟩
  [] ∈ cartesian2 ys (cartesian yss)
    ≡⟨ refl ⟩
  [] ∈ cartesian (ys :: yss)
  ∎
  where open ∼-Reasoning

∈*↔∈cartesian {A} {x :: xs} {[]} = record
  { to = ->-to-⟶ from
  ; from = ->-to-⟶ to
  ; inverse-of = record
    { left-inverse-of = to∘from
    ; right-inverse-of = from∘to
    }
  }
  where
  from : (p : Pointwise.Rel _∈_ (x :: xs) []) -> x :: xs ∈ [] :: []
  from ()
  to : (p : x :: xs ∈ [] :: []) -> Pointwise.Rel _∈_ (x :: xs) []
  to (here ())
  to (there ())
  to∘from : (p : Pointwise.Rel _∈_ (x :: xs) []) -> to (from p) = p
  to∘from ()
  from∘to : (p : x :: xs ∈ [] :: []) -> from (to p) = p
  from∘to (here ())
  from∘to (there ())

∈*↔∈cartesian {A} {x :: xs} {ys :: yss} =
  Pointwise.Rel _∈_ (x :: xs) (ys :: yss)
    ↔⟨ sym $ ×∈*↔∈* x xs ys yss ⟩
  (x ∈ ys × Pointwise.Rel _∈_ xs yss)
    ↔⟨ (_ ∎) ×-cong ∈*↔∈cartesian ⟩
  (x ∈ ys × xs ∈ cartesian yss)
    ↔⟨ ∈∈↔::cartesian2 x xs ys (cartesian yss) ⟩
  x :: xs ∈ cartesian2 ys (cartesian yss)
    ≡⟨ refl ⟩
  x :: xs ∈ cartesian (ys :: yss)
  ∎
  where open ∼-Reasoning

--
-- Monotonicity of `Pointwise.Rel _∈_` and `cartesian`.
--

-- ∈*-mono

∈*-mono : {A : Set} {xs : List A} {yss₁ yss₂ : List (List A)} ->
  Pointwise.Rel _⊆_ yss₁ yss₂ ->
  Pointwise.Rel _∈_ xs yss₁ -> Pointwise.Rel _∈_ xs yss₂

∈*-mono [] [] = []
∈*-mono (ys₁⊆ys₂ :: yss₁⊆*yss₂) (x∈ys₁ :: xs∈*yss₁) =
  (ys₁⊆ys₂ x∈ys₁) :: ∈*-mono yss₁⊆*yss₂ xs∈*yss₁

-- cartesian-mono

cartesian-mono : ∀ {A : Set} (xss₁ xss₂ : List (List A)) ->
  Pointwise.Rel _⊆_ xss₁ xss₂ ->
  cartesian xss₁ ⊆ cartesian xss₂

cartesian-mono xss₁ xss₂ xss₁⊆xss₂ {zs} =
  zs ∈ cartesian xss₁
    ↔⟨ sym $ ∈*↔∈cartesian ⟩
  Pointwise.Rel _∈_ zs xss₁
    ∼⟨ ∈*-mono xss₁⊆xss₂ ⟩
  Pointwise.Rel _∈_ zs xss₂
    ↔⟨ ∈*↔∈cartesian ⟩
  zs ∈ cartesian xss₂
  ∎
  where open ∼-Reasoning

-- ∈*∘map-mono

∈*∘map-mono : {A B : Set} {⟪_⟫ : A -> List B} (clean : A -> A) ->
  (mono : ∀ x -> ⟪ clean x ⟫ ⊆ ⟪ x ⟫) (xs : List A) ->
  Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ clean) xs) (map ⟪_⟫ xs)

∈*∘map-mono clean mono [] = []
∈*∘map-mono clean mono (x :: xs) =
  (mono x) :: ∈*∘map-mono clean mono xs

--
-- filter∘cartesian
--

-- all∘::

all∘:: : {A : Set} (p : A -> Bool) {x : A} {b : Bool} -> p x = b ->
  all p ∘ (_::_ x) = _∧_ b ∘ all p

all∘:: p {x} {b} px≡b = begin
  all p ∘ (_::_ x)
    ≡⟨⟩
  _∧_ (p x) ∘ all p
    ≡⟨ cong (λ px -> _∧_ px ∘ all p) px≡b ⟩
  _∧_ b ∘ all p
  ∎
  where open =-Reasoning

-- filter∘cartesian2

filter∘cartesian2 :
  ∀ {A : Set} (p : A -> Bool) (xs : List A) (xss : List (List A)) ->
    filter (all p) (cartesian2 xs xss) =
      cartesian2 (filter p xs) (filter (all p) xss)

filter∘cartesian2 p [] xss = refl

filter∘cartesian2 p (x :: xs) xss with p x | inspect p x

... | true | P[ ≡true ] = begin
  filter (all p) (cartesian2 (x :: xs) xss)
    ≡⟨⟩
  filter (all p) (map (_::_ x) xss ++ cartesian2 xs xss)
    ≡⟨ filter-++-commute (all p) (map (_::_ x) xss) (cartesian2 xs xss) ⟩
  filter (all p) (map (_::_ x) xss) ++ filter (all p) (cartesian2 xs xss)
    ≡⟨ cong₂ _++_ helper (filter∘cartesian2 p xs xss) ⟩
  map (_::_ x) (filter (all p) xss) ++
  cartesian2 (filter p xs) (filter (all p) xss)
  ∎
  where
  open =-Reasoning

  helper : filter (all p) (map (_::_ x) xss) = map (_::_ x) (filter (all p) xss)
  helper = begin
    filter (all p) (map (_::_ x) xss)
      ≡⟨ filter∘map (all p) (_::_ x) xss ⟩
    map (_::_ x) (filter (all p ∘ _::_ x) xss)
      ≡⟨ cong (map (_::_ x)) (cong (flip filter xss) (all∘:: p ≡true)) ⟩
    map (_::_ x) (filter (all p) xss)
    ∎

... | false | P[ ≡false ] = begin
  filter (all p) (cartesian2 (x :: xs) xss)
    ≡⟨⟩
  filter (all p) (map (_::_ x) xss ++ cartesian2 xs xss)
    ≡⟨ filter-++-commute (all p) (map (_::_ x) xss) (cartesian2 xs xss) ⟩
  filter (all p) (map (_::_ x) xss) ++ filter (all p) (cartesian2 xs xss)
    ≡⟨ cong₂ _++_ helper (filter∘cartesian2 p xs xss) ⟩
  [] ++ cartesian2 (filter p xs) (filter (all p) xss)
    ≡⟨⟩
  cartesian2 (filter p xs) (filter (all p) xss)
  ∎
  where
  open =-Reasoning

  helper : filter (all p) (map (_::_ x) xss) = []
  helper = begin
    filter (all p) (map (_::_ x) xss)
      ≡⟨ filter∘map (all p) (_::_ x) xss ⟩
    map (_::_ x) (filter (all p ∘ _::_ x) xss)
      ≡⟨ cong (map (_::_ x)) (cong (flip filter xss) (all∘:: p ≡false)) ⟩
    map (_::_ x) (filter (const false) xss)
      ≡⟨ cong (map (_::_ x)) (filter-false xss) ⟩
    map (_::_ x) []
      ≡⟨⟩
    []
    ∎

-- filter∘cartesian

filter∘cartesian :
  ∀ {A : Set} (p : A -> Bool) (xss : List (List A)) ->
    filter (all p) (cartesian xss) = cartesian (map (filter p) xss)

filter∘cartesian p [] = refl
filter∘cartesian p (xs :: xss) = begin
  filter (all p) (cartesian (xs :: xss))
    ≡⟨⟩
  filter (all p) (cartesian2 xs (cartesian xss))
    ≡⟨ filter∘cartesian2 p xs (cartesian xss) ⟩
  cartesian2 (filter p xs) (filter (all p) (cartesian xss))
    ≡⟨ cong (cartesian2 (filter p xs)) (filter∘cartesian p xss) ⟩
  cartesian2 (filter p xs) (cartesian (map (filter p) xss))
    ≡⟨⟩
  cartesian (filter p xs :: map (filter p) xss)
    ≡⟨⟩
  cartesian (map (filter p) (xs :: xss))
  ∎
  where open =-Reasoning

--
-- Cartesian product for vectors
--

-- vec-cartesian2

vec-cartesian2 : ∀ {k} {A : Set} -> List A -> List (Vec A k) ->
  List (Vec A (suc k))

vec-cartesian2 [] yss = []
vec-cartesian2 (x :: xs) yss = map (_::_ x) yss ++ vec-cartesian2 xs yss

-- vec-cartesian

vec-cartesian : ∀ {k} {A : Set} (xss : Vec (List A) k) -> List (Vec A k)
vec-cartesian [] = [ [] ]
vec-cartesian (xs :: xss) = vec-cartesian2 xs (vec-cartesian xss)

--
-- Fusing `cartesian` and `map`
--

-- cartesianMap

cartesianMap : {A B : Set} (f : A -> List B) (xs : List A) -> List (List B)

cartesianMap f [] = [ [] ]
cartesianMap f (x :: xs) with f x
... | [] = []
... | y :: ys = cartesian2 (y :: ys) (cartesianMap f xs)

-- cartesianMap-correct

cartesianMap-correct : {A B : Set} (f : A -> List B) (xs : List A) ->
  cartesianMap f xs = cartesian (map f xs)

cartesianMap-correct f [] = refl
cartesianMap-correct f (x :: xs) with f x
... | [] = refl
... | y :: ys = begin
  cartesian2 (y :: ys) (cartesianMap f xs)
    ≡⟨ cong (cartesian2 (y :: ys)) (cartesianMap-correct f xs) ⟩
  cartesian2 (y :: ys) (cartesian (map f xs))
  ∎
  where open =-Reasoning
-}
