/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Counting / polynomial-agreement / hypercube bricks (WHIR #113, Fiat-Shamir #116, sumcheck #13/#114)

* `card_filter_forall_pi` — the count of length-`s` tuples whose every coordinate satisfies a
  predicate `Q` is `(#Q)^s` (WHIR out-of-domain / FS union-bound counting, #113/#116).
* `card_filter_exists_not_pi` — the complementary exact count of tuples with at least one bad
  coordinate, `|β|^s - (#Q)^s`.
* `Polynomial.card_eval_agreement_le_of_natDegree_lt` — two distinct polynomials of degree `< N`
  agree on at most `N-1` field points (the counting/Schwartz–Zippel dual used in collision-count
  arguments, #113/#116).
* `Polynomial.card_eval_disagreement_ge_of_natDegree_lt` — the complementary lower bound on
  disagreement points.
* `Polynomial.card_filter_forall_isRoot_le` — for a nonzero polynomial of degree `< N`, at most
  `(N-1)^s` length-`s` tuples are all roots.
* `Polynomial.card_filter_forall_eval_eq_le_of_natDegree_lt` — two distinct degree-`< N`
  polynomials agree on every coordinate of at most `(N-1)^s` length-`s` tuples.
* `Finset.sum_boolCube_prod_factor_eq_prod_sum` — the boolean-hypercube identity
  `∑_{x∈{0,1}^σ} ∏ᵢ (xᵢ=0 ? aᵢ : bᵢ) = ∏ᵢ (aᵢ + bᵢ)` underlying multilinear-extension sumcheck
  folding (#13/#114).
-/

open Finset Polynomial

/-- Count of length-`s` tuples whose every coordinate satisfies `Q` equals `(#Q)^s`. -/
theorem card_filter_forall_pi {β : Type*} [Fintype β] [DecidableEq β] (s : ℕ)
    (Q : β → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun r : Fin s → β => ∀ i, Q (r i))).card
      = (Finset.univ.filter Q).card ^ s := by
  have h : (Finset.univ.filter (fun r : Fin s → β => ∀ i, Q (r i)))
      = Fintype.piFinset (fun _ : Fin s => Finset.univ.filter Q) := by
    ext r; simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]; simp

/-- Count of length-`s` tuples with at least one coordinate outside `Q`. -/
theorem card_filter_exists_not_pi {β : Type*} [Fintype β] [DecidableEq β] (s : ℕ)
    (Q : β → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun r : Fin s → β => ∃ i, ¬ Q (r i))).card
      = Fintype.card β ^ s - (Finset.univ.filter Q).card ^ s := by
  have hgood := card_filter_forall_pi (β := β) s Q
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin s → β))) (p := fun r => ∀ i, Q (r i))
  have hbad_filter :
      (Finset.univ.filter (fun r : Fin s → β => ¬ ∀ i, Q (r i)))
        = Finset.univ.filter (fun r : Fin s → β => ∃ i, ¬ Q (r i)) := by
    ext r
    simp
  have hcard_fun : Fintype.card (Fin s → β) = Fintype.card β ^ s := by
    simp
  have hcard_univ : (Finset.univ : Finset (Fin s → β)).card = Fintype.card β ^ s := by
    rw [Finset.card_univ, hcard_fun]
  rw [hbad_filter] at hsplit
  rw [hgood, hcard_univ] at hsplit
  omega

namespace Polynomial

/-- Two distinct polynomials of degree `< N` agree on at most `N-1` field points. -/
theorem card_eval_agreement_le_of_natDegree_lt {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {N : ℕ} {p q : F[X]} (hpq : p ≠ q) (hp : p.natDegree < N) (hq : q.natDegree < N) :
    (Finset.univ.filter (fun x : F => p.eval x = q.eval x)).card ≤ N - 1 := by
  have hr : p - q ≠ 0 := sub_ne_zero_of_ne hpq
  have hdeg : (p - q).natDegree < N := (natDegree_sub_le p q).trans_lt (max_lt hp hq)
  have hsub : (Finset.univ.filter (fun x : F => p.eval x = q.eval x)) ⊆ (p - q).roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hr, Polynomial.IsRoot.def,
      Polynomial.eval_sub, sub_eq_zero]
    exact hx
  calc (Finset.univ.filter (fun x : F => p.eval x = q.eval x)).card
      ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := Polynomial.card_roots' _
    _ ≤ N - 1 := by omega

/-- Two distinct polynomials of degree `< N` disagree on at least `|F| - (N-1)` field points. -/
theorem card_eval_disagreement_ge_of_natDegree_lt {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {N : ℕ} {p q : F[X]} (hpq : p ≠ q) (hp : p.natDegree < N)
    (hq : q.natDegree < N) :
    Fintype.card F - (N - 1) ≤
      (Finset.univ.filter (fun x : F => p.eval x ≠ q.eval x)).card := by
  have hagree :=
    Polynomial.card_eval_agreement_le_of_natDegree_lt (F := F) (N := N) (p := p) (q := q)
      hpq hp hq
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset F)) (p := fun x : F => p.eval x = q.eval x)
  have hdisagree_filter :
      (Finset.univ.filter (fun x : F => ¬ p.eval x = q.eval x))
        = Finset.univ.filter (fun x : F => p.eval x ≠ q.eval x) := by
    ext x
    simp
  have hcard : (Finset.univ : Finset F).card = Fintype.card F := by
    simp
  rw [hdisagree_filter, hcard] at hsplit
  omega

/-- If `p` is nonzero of degree `< N`, then at most `(N-1)^s` length-`s` tuples
are made entirely of roots of `p`. -/
theorem card_filter_forall_isRoot_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {N s : ℕ} {p : F[X]} (hp0 : p ≠ 0) (hp : p.natDegree < N) :
    (Finset.univ.filter (fun r : Fin s → F => ∀ i, p.IsRoot (r i))).card ≤
      (N - 1) ^ s := by
  classical
  have hroot_card :
      (Finset.univ.filter (fun x : F => p.IsRoot x)).card ≤ N - 1 := by
    have hsub : (Finset.univ.filter (fun x : F => p.IsRoot x)) ⊆ p.roots.toFinset := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
      exact hx
    calc (Finset.univ.filter (fun x : F => p.IsRoot x)).card
        ≤ p.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' _
      _ ≤ N - 1 := by omega
  rw [card_filter_forall_pi (β := F) s (fun x : F => p.IsRoot x)]
  exact Nat.pow_le_pow_left hroot_card s

/-- Two distinct polynomials of degree `< N` agree on every coordinate of at most `(N-1)^s`
length-`s` tuples. -/
theorem card_filter_forall_eval_eq_le_of_natDegree_lt {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {N s : ℕ} {p q : F[X]} (hpq : p ≠ q) (hp : p.natDegree < N)
    (hq : q.natDegree < N) :
    (Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = q.eval (r i))).card ≤
      (N - 1) ^ s := by
  have hagree :=
    Polynomial.card_eval_agreement_le_of_natDegree_lt (F := F) (N := N) (p := p) (q := q)
      hpq hp hq
  rw [card_filter_forall_pi (β := F) s (fun x : F => p.eval x = q.eval x)]
  exact Nat.pow_le_pow_left hagree s

end Polynomial

namespace Finset

/-- Boolean-hypercube sum of per-coordinate two-way products factors as the product of sums. -/
theorem sum_boolCube_prod_factor_eq_prod_sum {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]
    (a b : σ → R) :
    ∑ x : σ → Fin 2, ∏ i : σ, (if x i = 0 then a i else b i) = ∏ i : σ, (a i + b i) := by
  have key : (∏ i : σ, ∑ j : Fin 2, (if j = 0 then a i else b i))
      = ∑ x : σ → Fin 2, ∏ i : σ, (if x i = 0 then a i else b i) := by
    rw [Finset.prod_univ_sum, ← Fintype.piFinset_univ]
  rw [← key]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]; simp

end Finset

#print axioms card_filter_forall_pi
#print axioms card_filter_exists_not_pi
#print axioms Polynomial.card_eval_agreement_le_of_natDegree_lt
#print axioms Polynomial.card_eval_disagreement_ge_of_natDegree_lt
#print axioms Polynomial.card_filter_forall_isRoot_le
#print axioms Polynomial.card_filter_forall_eval_eq_le_of_natDegree_lt
#print axioms Finset.sum_boolCube_prod_factor_eq_prod_sum
