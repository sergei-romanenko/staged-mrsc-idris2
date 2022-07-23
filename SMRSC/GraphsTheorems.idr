module SMRSC.GraphsTheorems

--
-- Graphs of configurations
--

{- 
open import Algebra
  using (module Monoid)
open import Data.Bool
  using (Bool; true; false; if_then_else_; not; _∨_)
open import Data.Nat
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.List as List
  using (List; []; _∷_; map; _++_; filter; all)
open import Data.List.Properties
  using (::-injective; map-compose; map-++-commute)
open import Data.List.Any as Any
  using (Any; here; there; any)
open import Data.List.Any.Membership.Propositional
  using (_∈_; _⊆_)
open import Data.List.Any.Properties
  using (Any-cong; Any↔; ++↔; return↔; map↔; concat↔; ⊎↔)
open import Data.List.Any.Membership.Propositional.Properties
  using (map-∈↔)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Maybe
  using (Maybe; nothing; just)
open import Data.Unit
  using (⊤; tt)

open import Function
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

private
  module LM {a} {A : Set a} = Monoid (List.monoid A)
-}

import Syntax.PreorderReasoning
import Syntax.WithProof
import Data.DPair

import SMRSC.Util
import SMRSC.Graphs

%hint
unroll_cl_empty : (c: a) ->(lss : List (List (LazyGraph a))) ->
  unroll (Build c lss) = unroll (cl_empty_build c lss)
unroll_cl_empty c [] = Refl
unroll_cl_empty c (ls' :: lss') = Refl

--
-- `cl_empty` is correct
--

mutual

  cl_empty_correct : (l : LazyGraph a) ->
    unroll(cl_empty l) = unroll l
  cl_empty_correct Empty = Refl
  cl_empty_correct (Stop c) = Refl
  cl_empty_correct (Build c lss) =
    rewrite sym $ unroll_cl_empty c (cl_empty_lss lss) in
    rewrite cl_empty_lss_correct lss in
    Refl

  cl_empty_lss_correct : (lss : List (List (LazyGraph a))) ->
    unroll_lss(cl_empty_lss lss) = unroll_lss lss
  cl_empty_lss_correct [] = Refl
  cl_empty_lss_correct (ls :: lss) with (cl_empty_ls_correct ls)
    _ | Left (cl_ls_Nothing, u_ls_nil) =
        rewrite cl_ls_Nothing in
        rewrite u_ls_nil in
        cl_empty_lss_correct lss
    _ | Right (ls' ** (cl_ls_Just, u_ls)) =
      rewrite cl_ls_Just in
      rewrite u_ls in
      rewrite cl_empty_lss_correct lss in
       Refl

  cl_empty_ls_correct : (ls : List (LazyGraph a)) -> Either
    (cl_empty_ls ls = Nothing , cartesian (unroll_ls ls) = [])
    (ls' ** (cl_empty_ls ls = Just ls', unroll_ls ls = unroll_ls ls'))
  cl_empty_ls_correct [] = Right $ ([] ** (Refl, Refl))
  cl_empty_ls_correct (l :: ls) with (@@ cl_empty l)
    _ | (Empty ** eq_l') =
      rewrite sym $ cl_empty_correct l in
      rewrite eq_l' in
      Left (Refl, Refl)
    _ | (l' ** eq_l') with (@@ decEmpty l')
      _ | (Yes eq_Empty_l' ** eq_decEmpty) =
        rewrite sym $ cl_empty_correct l in
        rewrite eq_l' in
        rewrite sym $ eq_Empty_l' in
        Left ((Refl, Refl))
      _ | (No neq_Empty_l' ** eq_decEmpty) with (cl_empty_ls_correct ls)
        _ | Left (cl_ls_Nothing, u_ls_nil) =
          rewrite u_ls_nil in
          rewrite eq_l' in
          rewrite eq_decEmpty in
          rewrite cl_ls_Nothing in
          Left $ (Refl, cartesian2_nil (unroll l))
        _ | Right (ls' ** (cl_ls_Just, u_ls)) =
          rewrite sym $ cl_empty_correct l in
          rewrite eq_l' in
          rewrite u_ls in
          rewrite eq_decEmpty in
          rewrite cl_ls_Just in
          Right $ (l' :: ls' ** (Refl, Refl))

--
-- `cl_ex_empty` - `cl_empty` and `cl_empty_correct` "in one vial".
--

mutual

  public export
  cl_ex_empty : (l : LazyGraph a) ->
    Subset (LazyGraph a) (\l' => unroll l = unroll l')
  cl_ex_empty Empty = Element Empty Refl
  cl_ex_empty (Stop c) = Element (Stop c) Refl
  cl_ex_empty (Build c lss) with (cl_ex_empty_lss lss)
    _ | Element lss' u_lss =
      rewrite u_lss in
      Element (cl_empty_build c lss') (unroll_cl_empty c lss')

  public export
  cl_ex_empty_lss : (lss : List (List (LazyGraph a))) ->
    Subset(List (List (LazyGraph a))) (\lss' => unroll_lss lss = unroll_lss lss')
  cl_ex_empty_lss [] = Element [] Refl
  cl_ex_empty_lss (ls :: lss) with (cl_ex_empty_ls ls)
    _ | Left u_ls_nil with (cl_ex_empty_lss lss)
      _ | Element lss' u_lss =
        rewrite u_ls_nil in
        rewrite u_lss in
        Element lss' Refl
    _ | Right (Element ls' u_ls) with (cl_ex_empty_lss lss)
      _ | (Element lss' u_lss) =
        rewrite u_ls in
        rewrite u_lss in
        Element (ls' :: lss') Refl

  public export
  cl_ex_empty_ls : (ls : List (LazyGraph a)) -> Either
    (cartesian (unroll_ls ls) = [])
    (Subset(List (LazyGraph a)) (\ls' => unroll_ls ls = unroll_ls ls'))
  cl_ex_empty_ls [] = Right $ Element [] Refl
  cl_ex_empty_ls (l :: ls) with (cl_ex_empty l)
    _ | Element Empty u_l =
      rewrite u_l in
      Left Refl
    _ | Element l' u_l with (cl_ex_empty_ls ls)
      _ | Left u_ls_nil =
        rewrite u_ls_nil in
        Left $ cartesian2_nil (unroll l)
      _ | Right (Element ls' u_ls) =
        rewrite u_l in
        rewrite u_ls in
        Right $ Element (l' :: ls') Refl

--
-- `cl_bad_conf` is sound
--

-- cl_bad_conf*-is-map

parameters (bad : a -> Bool)

  cl_bad_conf_ls_is_map : (ls : List (LazyGraph a)) ->
    cl_bad_conf_ls bad ls = map (cl_bad_conf bad) ls
  cl_bad_conf_ls_is_map [] = Refl
  cl_bad_conf_ls_is_map (l :: ls) =
    cong (cl_bad_conf bad l ::) (cl_bad_conf_ls_is_map ls)


{-
mutual

    cl_bad_conf_sound :
      (l : LazyGraph C) ->
        ⟪ cl_bad_conf bad l ⟫ ⊆ ⟪ l ⟫

    cl_bad_conf_sound Ø =
      id
    cl_bad_conf_sound (stop c) with bad c
    ... | true = λ ()
    ... | false = id
    cl_bad_conf_sound (build c lss) {g} with bad c
    ... | true = λ ()
    ... | false =
      g ∈ map (forth c) ⟪ cl_bad_conf⇉ bad lss ⟫⇉
        ↔⟨ sym $ map-∈↔ ⟩
      ∃ (λ g′ -> g′ ∈ ⟪ cl_bad_conf⇉ bad lss ⟫⇉ × g ≡ forth c g′)
        ∼⟨ Σ.cong Inv.id (cl_bad_conf⇉_sound lss ×-cong id) ⟩
      ∃ (λ g′ -> g′ ∈ ⟪ lss ⟫⇉ × g ≡ forth c g′)
        ↔⟨ map-∈↔ ⟩
      g ∈ map (forth c) ⟪ lss ⟫⇉
      ∎ where open ∼-Reasoning

    cl_bad_conf⇉_sound :
      (lss : List (List (LazyGraph C))) ->
        ⟪ cl_bad_conf⇉ bad lss ⟫⇉ ⊆ ⟪ lss ⟫⇉

    cl_bad_conf⇉_sound [] =
      id
    cl_bad_conf⇉_sound (ls :: lss) {g} =
      g ∈ cartesian ⟪ cl_bad_conf* bad ls ⟫* ++ ⟪ cl_bad_conf⇉ bad lss ⟫⇉
       ↔⟨ sym $ ++↔ ⟩
      (g ∈ cartesian ⟪ cl_bad_conf* bad ls ⟫* ⊎
        g ∈ ⟪ cl_bad_conf⇉ bad lss ⟫⇉)
       ∼⟨ cl_bad_conf_cartesian ls ⊎-cong cl_bad_conf⇉_sound lss ⟩
      (g ∈ cartesian ⟪ ls ⟫* ⊎ g ∈ ⟪ lss ⟫⇉)
        ↔⟨ ++↔ ⟩
      g ∈ cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉
      ∎ where open ∼-Reasoning

    -- cl_bad_conf_cartesian

    cl_bad_conf_cartesian :
      (ls : List (LazyGraph C)) ->
        cartesian ⟪ cl_bad_conf* bad ls ⟫* ⊆ cartesian ⟪ ls ⟫*

    cl_bad_conf_cartesian ls {gs} =
      cartesian-mono ⟪ cl_bad_conf* bad ls ⟫* ⟪ ls ⟫* (helper tt)
      where
      open ∼-Reasoning

      ∈*∘map : ∀ ls ->
        Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ cl_bad_conf bad) ls) (map ⟪_⟫ ls)
      ∈*∘map [] = []
      ∈*∘map (l :: ls) = cl_bad_conf_sound l :: ∈*∘map ls

      helper : ⊤ -> Pointwise.Rel _⊆_ ⟪ cl_bad_conf* bad ls ⟫* ⟪ ls ⟫*
      helper =
        ⊤
          ∼⟨ const (∈*∘map ls) ⟩
        Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ cl_bad_conf bad) ls) (map ⟪_⟫ ls)
          ∼⟨ subst (λ u -> Pointwise.Rel _⊆_ u (map ⟪_⟫ ls))
                   (map-compose ls) ⟩
        Pointwise.Rel _⊆_ (map ⟪_⟫ (map (cl_bad_conf bad) ls)) (map ⟪_⟫ ls)
          ∼⟨ subst₂ (λ u v -> Pointwise.Rel _⊆_ u v)
                    (P.sym $ ⟪⟫*-is-map (map (cl_bad_conf bad) ls))
                    (P.sym $ ⟪⟫*-is-map ls) ⟩
        Pointwise.Rel _⊆_ ⟪ map (cl_bad_conf bad) ls ⟫* ⟪ ls ⟫*
          ∼⟨ subst (λ u -> Pointwise.Rel _⊆_ ⟪ u ⟫* ⟪ ls ⟫*)
                   (P.sym $ cl_bad_conf*-is-map ls) ⟩
        Pointwise.Rel _⊆_ ⟪ cl_bad_conf* bad ls ⟫* ⟪ ls ⟫*
        ∎
-}

--
-- `cl_bad_conf` is correct with respect to `fl-bad-conf`.
--

{- 
module ClBadConf~FlBadConf (C : Set) (bad : C -> Bool) where

  not∘bad_graph* :
    not ∘ bad-graph* bad ≗ all (not ∘ bad-graph bad)

  not∘bad_graph* [] = refl
  not∘bad_graph* (g :: gs) with bad-graph bad g
  ... | true = refl
  ... | false = not∘bad_graph* gs

  not∘bad_graph : {c : C} {b : Bool} -> bad c ≡ b ->
    not ∘ _∨_ b ∘ bad-graph* bad ≡ not ∘ bad-graph bad ∘ forth c
  not∘bad_graph {c} {b} bad-c≡b = begin
    not ∘ _∨_ b ∘ bad-graph* bad
      ≡⟨ cong (λ bad-c -> not ∘ _∨_ bad-c ∘ bad-graph* bad) (P.sym $ bad-c≡b) ⟩
    not ∘ _∨_ (bad c) ∘ bad-graph* bad
      ≡⟨⟩
    not ∘ bad-graph bad ∘ forth c
    ∎ where open ≡-Reasoning
-}

{- 
  mutual

    cl_bad_conf_correct :
      ⟪_⟫ ∘ cl_bad_conf bad ≗ fl-bad-conf bad ∘ ⟪_⟫

    cl_bad_conf_correct Ø =
      refl
    cl_bad_conf_correct (stop c) with bad c
    ... | true = refl
    ... | false = refl
    cl_bad_conf_correct (build c lss) with bad c | inspect bad c

    ... | true | P[ ≡true ] = begin
      []
        ≡⟨⟩
      map (forth c) []
        ≡⟨ cong (map (forth c)) (P.sym $ filter-false ⟪ lss ⟫⇉) ⟩
      map (forth c) (filter (const false) ⟪ lss ⟫⇉)
        ≡⟨ cong (map (forth c))
                (cong (flip filter ⟪ lss ⟫⇉) (not∘bad_graph ≡true)) ⟩
      map (forth c) (filter ((not ∘ bad-graph bad) ∘ forth c) ⟪ lss ⟫⇉)
        ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad)
                              (forth c) ⟪ lss ⟫⇉ ⟩
      filter (not ∘ bad-graph bad) (map (forth c) ⟪ lss ⟫⇉)
        ≡⟨⟩
      fl-bad-conf bad (map (forth c) ⟪ lss ⟫⇉)
      ∎ where open ≡-Reasoning

    ... | false | P[ ≡false ] = begin
      map (forth c) ⟪ cl_bad_conf⇉ bad lss ⟫⇉
        ≡⟨ cong (map (forth c)) (cl_bad_conf⇉_correct lss) ⟩
      map (forth c) (filter (not ∘ bad-graph* bad) ⟪ lss ⟫⇉)
        ≡⟨ cong (map (forth c))
                (cong (flip filter ⟪ lss ⟫⇉) (not∘bad_graph ≡false)) ⟩
      map (forth c) (filter ((not ∘ bad-graph bad) ∘ forth c) ⟪ lss ⟫⇉)
        ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad)
                              (forth c) ⟪ lss ⟫⇉ ⟩
      filter (not ∘ bad-graph bad) (map (forth c) ⟪ lss ⟫⇉)
        ≡⟨⟩
      fl-bad-conf bad (map (forth c) ⟪ lss ⟫⇉)
      ∎ where open ≡-Reasoning

    -- cl_bad_conf⇉_correct

    cl_bad_conf⇉_correct :
      ∀ lss -> ⟪ cl_bad_conf⇉ bad lss ⟫⇉ ≡
                 filter (not ∘ bad-graph* bad) ⟪ lss ⟫⇉

    cl_bad_conf⇉_correct [] = refl
    cl_bad_conf⇉_correct (ls :: lss) = begin
      ⟪ cl_bad_conf⇉ bad (ls :: lss) ⟫⇉
        ≡⟨ refl ⟩
      cartesian ⟪ cl_bad_conf* bad ls ⟫* ++ ⟪ cl_bad_conf⇉ bad lss ⟫⇉
        ≡⟨ cong₂ _++_ (cartesian∘cl_bad* ls)
                      (cl_bad_conf⇉_correct lss) ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫*) ++
      filter (not ∘ bad-graph* bad) ⟪ lss ⟫⇉
        ≡⟨ P.sym $ filter-++-commute (not ∘ bad-graph* bad)
                                     (cartesian ⟪ ls ⟫*) ⟪ lss ⟫⇉ ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉)
        ≡⟨⟩
      filter (not ∘ bad-graph* bad) ⟪ ls :: lss ⟫⇉
      ∎ where open ≡-Reasoning

    -- cartesian∘cl_bad*

    cartesian∘cl_bad* :
      ∀ (ls : List (LazyGraph C)) ->
      cartesian ⟪ cl_bad_conf* bad ls ⟫* ≡
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫*)

    cartesian∘cl_bad* ls = begin
      cartesian ⟪ cl_bad_conf* bad ls ⟫*
        ≡⟨ cong cartesian (cl_bad_conf*_correct ls) ⟩
      cartesian (map (fl-bad-conf bad) ⟪ ls ⟫*)
        ≡⟨⟩
      cartesian (map (filter (not ∘ bad-graph bad)) ⟪ ls ⟫*)
        ≡⟨ P.sym $ filter∘cartesian (not ∘ bad-graph bad) ⟪ ls ⟫* ⟩
      filter (all (not ∘ bad-graph bad)) (cartesian ⟪ ls ⟫*)
        ≡⟨ P.sym $ filter-cong not∘bad_graph* (cartesian ⟪ ls ⟫*) ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫*)
      ∎ where open ≡-Reasoning


    cl_bad_conf*_correct :
      ∀ ls -> ⟪ cl_bad_conf* bad ls ⟫* ≡ map (fl-bad-conf bad) ⟪ ls ⟫*

    cl_bad_conf*_correct [] = refl
    cl_bad_conf*_correct (l :: ls) = begin
      ⟪ cl_bad_conf* bad (l :: ls) ⟫*
        ≡⟨⟩
      ⟪ cl_bad_conf bad l ⟫ :: ⟪ cl_bad_conf* bad ls ⟫*
        ≡⟨ cong₂ _∷_ (cl_bad_conf_correct l)
                     (cl_bad_conf*_correct ls) ⟩
      fl-bad-conf bad ⟪ l ⟫ :: map (fl-bad-conf bad) ⟪ ls ⟫*
        ≡⟨⟩
      map (fl-bad-conf bad) (⟪ l ⟫ :: ⟪ ls ⟫*)
        ≡⟨⟩
      map (fl-bad-conf bad) ⟪ l :: ls ⟫*
      ∎ where open ≡-Reasoning
-}

--
-- `cl_min_size` is sound:
--
--  Let cl_min_size l ≡ (k , l′). Then
--     ⟪ l′ ⟫ ⊆ ⟪ l ⟫
--     k ≡ graph-size (hd ⟪ l′ ⟫)
--
-- TODO: prove this formally
