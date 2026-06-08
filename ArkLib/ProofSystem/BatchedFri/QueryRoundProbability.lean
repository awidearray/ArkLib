/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.BatchedFri.Security
import ArkLib.ToMathlib.FriQueryRoundProb

/-!
# Batched FRI query-round probability adapters

This module connects the Mathlib-only probability-space query-round theorem from
`ArkLib.ToMathlib.FriQueryRoundProb` to the Batched FRI Claim 8.2 frontier in
`ArkLib.ProofSystem.BatchedFri.Security`.

The remaining hard Claim 8.2/8.3 pieces stay explicit: the correlated-agreement bridge,
virtual-oracle soundness preservation, sequential composition, and total-error consumption are not
proved here.
-/

namespace Fri
section ProbabilityAdapter

open scoped ENNReal NNReal BigOperators
open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function ProbabilityTheory

namespace QueryRound

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- Probability-space query-round acceptance frontier: under independent uniform queries, all
queries land in the good set with probability at most `(1 - δ) ^ t` when the good-set density is
at most `1 - δ`. -/
def probabilityAcceptanceBound (G : Finset ι) (δ : ℝ≥0∞) (t : ℕ) : Prop :=
  (G.card : ℝ≥0∞) / Fintype.card ι ≤ 1 - δ →
    (PMF.uniformOfFintype (Fin t → ι)).toOuterMeasure
        {q : Fin t → ι | ∀ j, q j ∈ G}
      ≤ (1 - δ) ^ t

/-- The probability-space query-round acceptance frontier is discharged by the Mathlib-only
query-round probability theorem. -/
theorem probabilityAcceptanceBound_holds (G : Finset ι) (δ : ℝ≥0∞) (t : ℕ) :
    probabilityAcceptanceBound G δ t := by
  intro h_density
  exact ArkLib.Fri.QueryRoundProb.prob_allQueriesIn_le G δ t h_density

/-- Probability-space query-round detection frontier: under independent uniform queries, at least
one query lands outside the good set with probability at least `1 - (1 - δ) ^ t`. -/
def probabilityDetectionBound (G : Finset ι) (δ : ℝ≥0∞) (t : ℕ) : Prop :=
  (G.card : ℝ≥0∞) / Fintype.card ι ≤ 1 - δ →
    1 - (1 - δ) ^ t
      ≤ (PMF.uniformOfFintype (Fin t → ι)).toOuterMeasure
          {q : Fin t → ι | ¬ (∀ j, q j ∈ G)}

/-- The probability-space query-round detection frontier is discharged by the Mathlib-only
complementary detection theorem. -/
theorem probabilityDetectionBound_holds (G : Finset ι) (δ : ℝ≥0∞) (t : ℕ) :
    probabilityDetectionBound G δ t := by
  intro h_density
  exact ArkLib.Fri.QueryRoundProb.prob_someQueryOut_ge G δ t h_density

end QueryRound

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
variable {n : ℕ} {k : ℕ}
variable {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n 𝔽}

/-- Instantiate the Claim 8.2 frontier with the proved probability-space query-round bound. -/
def FriQuerySoundnessParts.of_queryRoundProbabilityBound
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    (lensReduction agreementBridge : Prop)
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      lensReduction →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω) (f := f)
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3)) :
    FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) where
  query_round_acceptance_bound := QueryRound.probabilityAcceptanceBound G δ queries
  batching_oracle_lens_reduction := lensReduction
  correlated_agreement_to_jointAgreement := agreementBridge
  pieces_imply_claim := pieces_imply_claim

/-- Reassemble Claim 8.2 after discharging the query-round frontier with the probability-space
query-round theorem. -/
theorem fri_query_soundness_of_queryRoundProbabilityBound
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    {lensReduction agreementBridge : Prop}
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      lensReduction →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω) (f := f)
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (h_lens : lensReduction)
    (h_agreementBridge : agreementBridge) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  let parts :=
    FriQuerySoundnessParts.of_queryRoundProbabilityBound
      (n := n) (ω := ω) (f := f) (h_agreement := h_agreement)
      (m_ge_3 := m_ge_3) G δ queries lensReduction agreementBridge pieces_imply_claim
  exact fri_query_soundness_of_parts (n := n) (ω := ω) f h_agreement m_ge_3 parts
    (QueryRound.probabilityAcceptanceBound_holds G δ queries) h_lens h_agreementBridge

/-- Instantiate the Claim 8.2 frontier with the proved probability-space query-round bound and
the structural Batched FRI oracle-lens package. -/
def FriQuerySoundnessParts.of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (agreementBridge : Prop)
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω) (f := f)
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3)) :
    FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) where
  query_round_acceptance_bound := QueryRound.probabilityAcceptanceBound G δ queries
  batching_oracle_lens_reduction :=
    batchedFRIOracleLensReduction
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond) l t
  correlated_agreement_to_jointAgreement := agreementBridge
  pieces_imply_claim := pieces_imply_claim

/-- Reassemble Claim 8.2 after discharging the probability-space query-round bound and the
structural Batched FRI oracle-lens package. -/
theorem fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    {agreementBridge : Prop}
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω) (f := f)
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (h_agreementBridge : agreementBridge) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  let parts :=
    FriQuerySoundnessParts.of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) (h_agreement := h_agreement) (m_ge_3 := m_ge_3)
      G δ queries l domain_size_cond agreementBridge pieces_imply_claim
  exact fri_query_soundness_of_parts (n := n) (ω := ω) f h_agreement m_ge_3 parts
    (QueryRound.probabilityAcceptanceBound_holds G δ queries)
    (batchedFRIOracleLensReduction_holds
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond) l t)
    h_agreementBridge

omit [Nontrivial 𝔽] in
/-- Reassemble Claim 8.2 from the probability-space query-round theorem, the structural Batched
FRI oracle lens, and a concrete `Code.jointProximity` witness.

This removes the arbitrary `agreementBridge : Prop` from this front door: the remaining
coding-theoretic obligation is exactly the proximity predicate equivalent to the
`Code.jointAgreement` conclusion of `fri_query_soundness`. -/
theorem fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_proximity :
      Code.jointProximity
        (C := (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
        (u := f) (δ := 1 - α)) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  exact
    fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
      (n := n) (s := s) (d := d) (ω := ω)
      f h_agreement m_ge_3 G δ queries l domain_size_cond
      (agreementBridge :=
        Code.jointProximity
          (C := (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
          (u := f) (δ := 1 - α))
      (fun _h_query _h_lens h_joint =>
        fri_query_soundness_of_jointProximity
          (n := n) (ω := ω) f h_agreement m_ge_3 h_joint)
      h_proximity

/-! ### Axiom audit (issue #14 probability adapter) -/

#print axioms Fri.QueryRound.probabilityAcceptanceBound
#print axioms Fri.QueryRound.probabilityAcceptanceBound_holds
#print axioms Fri.QueryRound.probabilityDetectionBound
#print axioms Fri.QueryRound.probabilityDetectionBound_holds
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundProbabilityBound
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBound
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity

end ProbabilityAdapter
end Fri
