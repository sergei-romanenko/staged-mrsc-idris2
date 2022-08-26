module SMRSC.BigStepScTheorems

{-
open import Level
  using (Level)
open import Data.Nat
open import Data.List as List
open import Data.List.Properties
  using (map-compose; map-cong; foldr-fusion; map-++-commute)
open import Data.List.Any
  using (Any; here; there)
open import Data.List.Any.Membership.Propositional
  using (_∈_; _⊆_)
open import Data.List.Any.Properties
  using (Any↔; Any-cong; ++↔; return↔; map↔; concat↔; ⊎↔)
open import Data.List.Any.Membership.Propositional.Properties
  using (map-∈↔; concat-∈↔)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty

open import Function
open import Function.Equality
  using (_⟨$⟩_)
open import Function.Equivalence as Eq
  using (_⇔_; equivalence; module Equivalence)
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
  using ([]; _∷_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
  renaming ([_] to P[_])

-}

{-
open import Util
open import BarWhistles
open import Graphs
open import BigStepSc

open ScWorld scWorld
-}

import Data.List.Elem
import Data.List.Quantifiers

import SMRSC.Util
import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc

%default total

--
-- Extracting the residual graph from a proof
--
-- (Just for fun, currently this is not used anywhere.)

namespace GraphExtraction

  -- extractGraph

  extractGraph : {auto s : ScWorld a} ->
    {h : List a} -> {c : a} -> {g : Graph a} ->
    (p : NDSC h c g) -> Graph a
  extractGraph p = g

  -- extractGraph-sound

  extractGraph_sound : {auto s : ScWorld a} ->
    {h : List a} -> {c : a} -> {g : Graph a} ->
    (p : NDSC h c g) -> extractGraph p = g
  extractGraph_sound p = Refl

--
-- MRSC is sound with respect to NDSC
--

namespace MRSC_imp_NDSC'

  MRSC_imp_NDSC : {auto s : ScWorld a} -> {auto w : BarWhistle a} ->
    {h : List a} -> {c, g : _} ->
    MRSC h c g -> NDSC h c g
  MRSC_imp_NDSC (MRSC_Fold f) = NDSC_Fold f
  MRSC_imp_NDSC (MRSC_Build nf nw i p) =
    NDSC_Build nf i (pw_map p)
    where
    pw_map :
      {cs : List a} -> {gs : List (Graph a)} ->
      (qs : Pointwise (MRSC (c :: h)) cs gs) ->
      Pointwise (NDSC (c :: h)) cs gs
    pw_map [] = []
    pw_map (q :: qs) = MRSC_imp_NDSC q :: pw_map qs

--
-- `naive-mrsc` is correct with respect to `_⊢MRSC_↪_`
--

{-
module MRSC-correctness where

  open BigStepMRSC scWorld
-}

namespace MRSC_correctness


  -- naive_mrsc_sound'

{-
  naive_mrsc_sound' :
    (h : History) (b : Bar ↯ h) {c : Conf} {g : Graph Conf} ->
    g ∈ naive_mrsc' h b c -> MRSC h c g

  naive_mrsc_sound' h b {c} q with foldable? h c
  naive_mrsc_sound' h b (here g≡) | yes f rewrite g≡ =
    mrsc-fold f
  naive_mrsc_sound' h b (there ()) | yes f
  ... | no ¬f with ↯? h
  naive_mrsc_sound' h b () | no ¬f | yes w
  naive_mrsc_sound' h (now w) q | no ¬f | no ¬w =
    ⊥-elim (¬w w)
  naive_mrsc_sound' h (later bs) {c} {g} q | no ¬f | no ¬w =
    helper q
    where
    open ∼-Reasoning

    step : ∀ c' -> List (Graph Conf)
    step = naive_mrsc' (c :: h) (bs c)

    gss : List (List (Graph Conf))
    gss = concat (map (cartesian ∘ map step) (c ⇉))

    helper₄ : ∀ cs gs ->
      gs ∈ cartesian (map step cs) ->
         (c :: h) MRSC_cs cs ↪ gs
    helper₄ cs gs =
      gs ∈ cartesian (map step cs)
        ↔⟨ sym $ ∈*↔∈cartesian ⟩
      Pointwise.Rel _∈_ gs (map step cs)
        ∼⟨ ∈*∘map→ step cs ⟩
      Pointwise.Rel (λ c' gs' -> gs' ∈ step c') cs gs
        ∼⟨ Pointwise.map (naive_mrsc_sound' (c :: h) (bs c)) ⟩
      (c :: h) MRSC_cs cs ↪ gs
      ∎

    helper₃ : ∀ gss' css -> gss' ∈ map (cartesian ∘ map step) css -> _
    helper₃ gss' css =
      gss' ∈ map (cartesian ∘ map step) css
        ↔⟨ sym $ map-∈↔ ⟩
      ∃ (λ cs -> (cs ∈ css) × gss' = (cartesian ∘ map step) cs)
      ∎

    helper₂ : ∀ gs' -> gs' ∈ gss -> _
    helper₂ gs' =
      gs' ∈ gss
        ↔⟨ sym $ concat-∈↔ ⟩
      ∃ (λ gss' -> gs' ∈ gss' × gss' ∈ map (cartesian ∘ map step) (c ⇉))
      ∎

    helper₁ : ∃ (λ gs' -> gs' ∈ gss × g = forth c gs') -> MRSC h c g
    helper₁ (gs' , gs'∈gss , g≡) =
      let
        gss' , gs'∈gss' , gss'∈ = helper₂ gs' gs'∈gss
        cs , cs∈css , gss'=   = helper₃ gss' (c ⇉) gss'∈
      in
        gs' ∈ gss'
          ∼⟨ subst (_∈_ gs') gss'= ⟩
        gs' ∈ cartesian (map step cs)
          ∼⟨ helper₄ cs gs' ⟩
        c :: h MRSC_cs cs ↪ gs'
          ∼⟨ mrsc-build ¬f ¬w cs∈css ⟩
        h ⊢MRSC c ↪ forth c gs'
          ∼⟨ subst (_⊢MRSC_↪_ h c) (P.sym g≡) ⟩
        MRSC h c g
        ∎ $ gs'∈gss'

    helper : g ∈ map (forth c) gss  -> MRSC h c g
    helper =
      g ∈ map (forth c) gss
        ↔⟨ sym $ map-∈↔ ⟩
      ∃ (λ gs' -> gs' ∈ gss × g = forth c gs')
        ∼⟨ helper₁ ⟩
      MRSC h c g
      ∎
-}

  naive_mrsc_sound' : (s : ScWorld a) -> (w : BarWhistle a) ->
    (h : List a) -> (b : Bar (dangerous w) h) -> (c : a) -> (g : Graph a) ->
    (elem_g : Elem g (naive_mrsc' s w h b c)) -> MRSC @{s} @{w} h c g
  naive_mrsc_sound' s w h b c g elem_g with (decIsFoldableToHistory s c h)
    naive_mrsc_sound' s w h b c (Back c) Here | Yes f =
      MRSC_Fold f
    naive_mrsc_sound' s w h b c g (There elem_g_nil) | Yes f =
      absurd elem_g_nil
    naive_mrsc_sound' s w h b c g elem_g | No nf with (decDangerous w h)
      _ | Yes d = absurd elem_g
      _ | No nd with (b)
        _ | Now d = void (nd d)
        _ | Later bs = helper elem_g
          where
            Step : (c' : a) -> List (Graph a)
            Step = naive_mrsc' s w (c :: h) (bs c)

            Gss : List (List (Graph a))
            Gss = concatMap' (cartesian . map Step) (develop s c)

            Gs : List (Graph a)
            Gs = map (Forth c) Gss

            helper1 : (gs' ** (Elem gs' Gss, g = Forth c gs')) -> MRSC h c g

            helper : Elem g (map (Forth c) Gss) -> MRSC h c g
            helper =
              |~~ Elem g (map (Forth c) Gss)
              ~~> (gs' ** (Elem gs' Gss, g = Forth c gs'))
                ... (map_elem g Gss)
              ~~> MRSC h c g
                ... ( helper1 )

  --
  -- naive-mrsc-sound
  --

{-
  naive-mrsc-sound :
    {c : Conf} {g : Graph Conf} ->
      g ∈ naive-mrsc c -> [] ⊢MRSC c ↪ g

  naive-mrsc-sound =
    naive_mrsc_sound' [] bar[]

  -- naive-mrsc-complete'

  naive-mrsc-complete' :
    (h : History) (b : Bar ↯ h) {c : Conf} {g : Graph Conf} ->
      MRSC h c g -> g ∈ naive_mrsc' h b c

  naive-mrsc-complete' h b {c} q with foldable? h c
  naive-mrsc-complete' h b (mrsc-fold f) | yes f' =
    here refl
  naive-mrsc-complete' h b (mrsc-build ¬f ¬w i s) | yes f =
    ⊥-elim (¬f f)
  naive-mrsc-complete' h b q | no ¬f with ↯? h
  naive-mrsc-complete' h b (mrsc-fold f) | no ¬f | yes w =
    ⊥-elim (¬f f)
  naive-mrsc-complete' h b (mrsc-build _ ¬w i s) | no ¬f | yes w =
    ⊥-elim (¬w w)
  naive-mrsc-complete' h b (mrsc-fold f) | no ¬f | no ¬w =
    ⊥-elim (¬f f)

  naive-mrsc-complete' h (now w) (mrsc-build _ _ i s) | no ¬f | no ¬w =
    ⊥-elim (¬w w)
  naive-mrsc-complete' h (later bs) {c} (mrsc-build {cs = cs} {gs = gs} _ _ cs∈c⇉ s)
    | no ¬f | no ¬w =
    helper (gs , gs∈gss , refl)
    where
    open ∼-Reasoning

    step = naive_mrsc' (c :: h) (bs c)
    gsss = map (cartesian ∘ map step) (c ⇉)
    gss = concat gsss

    pw→cart : ∀ cs gs ->
      (c :: h) MRSC_cs cs ↪ gs ->
        gs ∈ cartesian (map step cs)
    pw→cart cs gs =
      (c :: h) MRSC_cs cs ↪ gs
        ∼⟨ Pointwise.map (naive-mrsc-complete' (c :: h) (bs c)) ⟩
      Pointwise.Rel (λ c' gs' -> gs' ∈ step c') cs gs
        ∼⟨ ∈*∘map← step cs ⟩
      Pointwise.Rel _∈_ gs (map step cs)
        ↔⟨ ∈*↔∈cartesian ⟩
      gs ∈ cartesian (map step cs)
      ∎

    →gss'∈gsss : ∀ gss' -> _ -> gss' ∈ gsss
    →gss'∈gsss gss' =
        ∃ (λ cs' -> cs' ∈ c ⇉ × gss' = cartesian (map step cs'))
        ↔⟨ map-∈↔ ⟩
      gss' ∈ map (cartesian ∘ map step) (c ⇉)
        ≡⟨ refl ⟩
      gss' ∈ gsss
      ∎

    →gs∈gss : _ -> gs ∈ gss
    →gs∈gss =
      ∃ (λ gss' -> gs ∈ gss' × gss' ∈ gsss)
        ↔⟨ concat-∈↔ ⟩
      gs ∈ concat (map (cartesian ∘ map step) (c ⇉))
        ↔⟨ _ ∎ ⟩
      gs ∈ gss
      ∎

    gs∈cart : gs ∈ cartesian (map step cs)
    gs∈cart = pw→cart cs gs s

    cart∈gsss : cartesian (map step cs) ∈ gsss
    cart∈gsss = →gss'∈gsss (cartesian (map step cs)) (cs , cs∈c⇉ , refl)

    gs∈gss : gs ∈ gss
    gs∈gss = →gs∈gss (cartesian (map step cs) , gs∈cart , cart∈gsss)

    helper : _ -> _
    helper =
      ∃ (λ gs' -> gs' ∈ gss × forth c gs = forth c gs')
        ↔⟨ map-∈↔ ⟩
      (forth c gs) ∈ map (forth c) gss
      ∎
-}

  -- naive-mrsc-complete

{-
  naive-mrsc-complete :
    {c : Conf} {g : Graph Conf} ->
     [] ⊢MRSC c ↪ g -> g ∈ naive-mrsc c

  naive-mrsc-complete r =
    naive-mrsc-complete' [] bar[] r
-}

  --
  -- ⊢MRSC↪⇔naive-mrsc
  --

{-
  ⊢MRSC↪⇔naive-mrsc :
    {c : Conf} {g : Graph Conf} ->
     [] ⊢MRSC c ↪ g ⇔ g ∈ naive-mrsc c

  ⊢MRSC↪⇔naive-mrsc =
    equivalence naive-mrsc-complete naive-mrsc-sound
-}


--
-- The main theorem:
-- `naive-mrsc` and `lazy-mrsc` produce the same bag of graphs!
--

{-
module MRSC-naive≡lazy where

  open BigStepMRSC scWorld

  mutual

    -- naive≡lazy'

    naive≡lazy' : (h : History) (b : Bar ↯ h) (c : Conf) ->
      naive_mrsc' h b c = ⟪ lazy-mrsc' h b c ⟫

    naive≡lazy' h b c with foldable? h c
    ... | yes f = refl
    ... | no ¬f with ↯? h
    ... | yes w = refl
    naive≡lazy' h (now w) c | no ¬f | no ¬w =
      ⊥-elim (¬w w)
    naive≡lazy' h (later bs) c | no ¬f | no ¬w =
      cong (map (forth c)) (helper (c ⇉))
      where
      open =-Reasoning

      naive-step = naive_mrsc' (c :: h) (bs c)
      lazy-step = lazy-mrsc' (c :: h) (bs c)

      helper : ∀ css ->
        concat (map (cartesian ∘ map naive-step) css) =
          ⟪ map (map lazy-step) css ⟫⇉

      helper [] = refl
      helper (cs :: css) = begin
        concat (map (cartesian ∘ map naive-step) (cs :: css))
          ≡⟨⟩
        cartesian (map naive-step cs) ++
          concat (map (cartesian ∘ map naive-step) css)
          ≡⟨ cong₂ _++_ (cong cartesian (map∘naive-mrsc' (c :: h) (bs c) cs))
                        (helper css) ⟩
        cartesian ⟪ map lazy-step cs ⟫* ++ ⟪ map (map lazy-step) css ⟫⇉
          ≡⟨⟩
        ⟪ map (map lazy-step) (cs :: css) ⟫⇉
        ∎

    -- map∘naive-mrsc'

    map∘naive-mrsc' : (h : History ) (b : Bar ↯ h) (cs : List Conf) ->
      map (naive_mrsc' h b) cs = ⟪ map (lazy-mrsc' h b) cs ⟫*

    map∘naive-mrsc' h b cs = begin
      map (naive_mrsc' h b) cs
        ≡⟨ map-cong (naive≡lazy' h b) cs ⟩
      map (⟪_⟫ ∘ lazy-mrsc' h b) cs
        ≡⟨ map-compose cs ⟩
      map ⟪_⟫ (map (lazy-mrsc' h b) cs)
        ≡⟨ P.sym $ ⟪⟫*-is-map (map (lazy-mrsc' h b) cs) ⟩
      ⟪ map (lazy-mrsc' h b) cs ⟫*
      ∎
      where open =-Reasoning
-}


  --
  -- naive≡lazy
  --

{-
  naive≡lazy : (c : Conf) ->
    naive-mrsc c = ⟪ lazy-mrsc c ⟫

  naive≡lazy c = naive≡lazy' [] bar[] c
-}
