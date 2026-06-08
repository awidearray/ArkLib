/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift

/-!
## Binary Basefold Soundness Fold Distance

Distance and disagreement transfer lemmas from fiber views to folded codewords.
This file packages:
1. helper lemmas turning fiber agreement into fold agreement
2. disagreement propagation from noncompliant fibers to folded evaluations
3. the folded-distance lower bounds used in the later bad-block analysis

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering follows the archived revision of [DP24].
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

open Classical in
omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡]
  [SampleableType L] in
/-- Pair-closeness to a concrete BBF codeword implies UDR-closeness to the BBF code. -/
lemma UDRClose_of_pair_UDRClose_to_BBF_Codeword (i : Fin r) (h_i : i ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (hg : g ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_pair : pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) h_i (f := f) (g := g)) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (h_i := h_i) (f := f) := by
  unfold UDRClose pair_UDRClose at *
  calc
    2 * Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≤
        2 * Δ₀(f, g) := by
      rw [ENat.mul_le_mul_left_iff
        (ha := by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
        (h_top := by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true])]
      exact Code.distFromCode_le_dist_to_mem
        (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
        (u := f) (v := g) hg
    _ < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul] using (ENat.coe_lt_coe.mpr h_pair)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [SampleableType L] in
/-- Helper: global agreement of two source words is preserved by iterated folding. -/
lemma fold_agreement_of_fiber_agreement (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    (∀ x, f x = g x) →
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f (r_challenges := r_challenges) y =
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le g (r_challenges := r_challenges) y)) := by
  intro h_agree
  have hfg : f = g := funext h_agree
  rw [hfg]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [SampleableType L] in
/-- Helper: The disagreement set of the folded functions is a subset of the fiberwise disagreement set. -/
lemma disagreement_fold_subset_fiberwiseDisagreement (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) :
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f (r_challenges := r_challenges)
    let folded_g := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le g (r_challenges := r_challenges)
    disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl) (f := folded_f) (g := folded_g) ⊆
    fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f g := by
  classical
  dsimp only
  intro y hy
  have h_steps_ne : steps ≠ 0 := NeZero.ne steps
  have h_exists : ∃ x, f x ≠ g x := by
    by_contra hnone
    have hfg : f = g := by
      funext x
      exact not_not.mp (by
        intro hx
        exact hnone ⟨x, hx⟩)
    rw [hfg] at hy
    simp [disagreementSet] at hy
  simp [fiberwiseDisagreementSet, h_steps_ne, h_exists]

omit [CharP L 2] [SampleableType L] in
/-- **Lemma 4.25, far branch.**
If the source word is fiberwise far, no bad folding event occurred, and the next word is
UDR-close, then the folded source is not pair-UDR-close to the decoded next codeword. The
close branch needs the full fiberwise-distance/cardinality bridge. -/
lemma lemma_4_24_dist_folded_ge_of_last_noncompliant (i_star : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i_star.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_star : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩)
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (r_challenges : Fin steps → L)
    -- 1. f_next is the actual folded function
    -- 2. i* is non-compliant
    (_h_not_compliant : ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le
       f_star f_next (challenges := r_challenges))
    -- 3. No bad event occurred at i*
    (h_no_bad_event : ¬ foldingBadEvent 𝔽q β (i := ⟨i_star, by omega⟩) steps h_destIdx h_destIdx_le f_star r_challenges)
    -- 4. The next function `f_next` IS close enough to have a unique codeword `f_bar_next`
    (h_next_close : UDRClose 𝔽q β destIdx h_destIdx_le f_next) :
      ¬ fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i_star, by omega⟩) (steps := steps) (destIdx := destIdx)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_star) →
      let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star
        (r_challenges := r_challenges)
      let f_bar_next := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        destIdx h_destIdx_le (f := f_next) (h_within_radius := h_next_close)
      ¬ pair_UDRClose 𝔽q β destIdx h_destIdx_le folded_f f_bar_next := by
  intro h_far
  dsimp only
  intro h_pair
  let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star
    (r_challenges := r_challenges)
  let f_bar_next := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    destIdx h_destIdx_le (f := f_next) (h_within_radius := h_next_close)
  have h_bar_mem : f_bar_next ∈
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
    UDRCodeword_mem_BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := h_destIdx_le) (f := f_next)
      (h_within_radius := h_next_close)
  have h_folded_close : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := h_destIdx_le) (f := folded_f) :=
    UDRClose_of_pair_UDRClose_to_BBF_Codeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
      (h_i := h_destIdx_le) (f := folded_f) (g := f_bar_next)
      h_bar_mem h_pair
  have h_far' : ¬ fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i_star, by omega⟩) (steps := steps) (destIdx := destIdx)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (f := f_star) := by
    simpa using h_far
  apply h_no_bad_event
  simp [foldingBadEvent, h_far', folded_f, h_folded_close]

end

end Binius.BinaryBasefold
