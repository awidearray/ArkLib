/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.BatchedFri.QueryRoundProbability

/-!
# Batched FRI soundness adapters from query-round probability

`QueryRoundProbability.lean` discharges the Claim 8.2 query-round frontier from the
Mathlib-only probability theorem. This file routes that probability-space front door into the
Claim 8.3 full-domain query-lift and sequential-composition packaging from `Security.lean`.
-/

namespace Fri
section ProbabilitySoundnessAdapter

open scoped ENNReal NNReal BigOperators
open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
variable {n : ℕ} {k : ℕ}
variable {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n 𝔽}
variable (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)

omit [Nontrivial 𝔽] in
/-- The proved probability-space query-round frontier supplies the Claim 8.3 full-domain
query-lift field, keeping the correlated-agreement bridge explicit. -/
theorem friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {agreementBridge : Prop}
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (h_agreementBridge : agreementBridge) :
    friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 := by
  unfold friSoundnessQueryLift
  exact
    fri_query_soundness_lift_subdomainZero_to_domain
      (n := n) (ω := ω) (f := f) h_agreement m_ge_3
    (fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
        (n := n) (s := s) (d := d) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        h_agreement m_ge_3 G δ queries l domain_size_cond
        pieces_imply_claim h_agreementBridge)

omit [Nontrivial 𝔽] in
/-- The proved probability-space query-round frontier supplies the Claim 8.3 full-domain
query-lift field from a concrete subdomain `Code.jointProximity` witness.

This is the probability-route analogue of the density query-lift joint-proximity adapter in
`Security.lean`: callers provide the actual proximity witness equivalent to the Claim 8.2
`Code.jointAgreement` conclusion rather than an arbitrary `agreementBridge : Prop`. -/
theorem friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (h_proximity :
      Code.jointProximity
        (C := (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
        (u := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (δ :=
          1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (2 ^ n)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))) :
    friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 := by
  unfold friSoundnessQueryLift
  exact
    fri_query_soundness_lift_subdomainZero_to_domain
      (n := n) (ω := ω) (f := f) h_agreement m_ge_3
      (fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
        (n := n) (s := s) (d := d) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        h_agreement m_ge_3 G δ queries l domain_size_cond h_proximity)

omit [Nontrivial 𝔽] in
/-- Probability-route Claim 8.3 residual from the concrete subdomain proximity witness.

This composes the probability query-lift joint-proximity adapter with `fri_soundness_of_queryLift`.
It mirrors the density-route theorem in `Security.lean`; the proximity witness remains the explicit
coding-theoretic target. -/
theorem fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (h_proximity :
      Code.jointProximity
        (C := (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
        (u := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (δ :=
          1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (2 ^ n)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ queries l domain_size_cond h_agreement h_proximity)

omit [Nontrivial 𝔽] in
/-- Raw full-domain Claim 8.2 conclusion from the proved probability-space query-round theorem
and the Batched FRI oracle-lens piece.

This is the probability-route analogue of
`fri_jointAgreement_of_queryRoundDensityBoundAndBatchedFRIOracleLens`, returning the underlying
`Code.jointAgreement` target rather than the packaged Claim 8.3 query-lift field. -/
theorem fri_jointAgreement_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {agreementBridge : Prop}
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (h_agreementBridge : agreementBridge) :
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin t.succ)
      (ι := ω)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (2 ^ n)).carrier)
      (δ :=
        let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (2 ^ n)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
        let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
        1 - α)
      (W := f) := by
  exact
    fri_query_soundness_lift_subdomainZero_to_domain
      (n := n) (ω := ω) (f := f) h_agreement m_ge_3
      (fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
        (n := n) (s := s) (d := d) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        h_agreement m_ge_3 G δ queries l domain_size_cond
        pieces_imply_claim h_agreementBridge)

omit [Nontrivial 𝔽] in
/-- Reassemble Claim 8.3 after discharging the query-lift field by the proved probability-space
query-round theorem and the concrete Batched FRI sequential-composition field. The remaining
frontiers are the correlated-agreement bridge and total-error accounting. -/
theorem fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialComposition
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₂ : Set (((Fin t → 𝔽) × Spec.Statement 𝔽 (0 : Fin (k + 1))) ×
      (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_batch : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₁ lang₂
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t).verifier
      batchError)
    (h_fri : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₂ lang₃
      (BatchedFri.Spec.liftedFRI
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l t).verifier
      friError)
    (h_residual : OracleVerifier.appendSoundnessResidual
      (init := init) (impl := impl)
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t).verifier
      (BatchedFri.Spec.liftedFRI
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l t).verifier
      h_batch h_fri)
    {agreementBridge totalErrorAccounting : Prop}
    (query_pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (soundness_pieces_imply_claim :
      friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 →
      friSoundnessSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError →
      totalErrorAccounting →
      fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond) f m_ge_3)
    (h_agreementBridge : agreementBridge)
    (h_total : totalErrorAccounting) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  let parts :=
    FriSoundnessParts.of_queryRoundDensityBoundAndBatchedFRIOracleLens
      (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError)
      totalErrorAccounting soundness_pieces_imply_claim
  exact fri_soundness_of_parts
    (n := n) (s := s) (d := d) (ω := ω) (l := l)
    (domain_size_cond := domain_size_cond) f m_ge_3 parts
    (friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond)
      f m_ge_3 G δ queries l h_agreement query_pieces_imply_claim h_agreementBridge)
    (friSoundnessSequentialComposition_of_append
      (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond)
      init impl lang₁ lang₂ lang₃ h_batch h_fri h_residual)
    h_total

omit [Nontrivial 𝔽] in
/-- Reassemble Claim 8.3 after discharging the probability-route query-lift and supplying the
already-named concrete sequential-composition and total-error-accounting fields directly.

This is the field-level probability-route front door: callers that already have
`friSoundnessSequentialComposition` and `friSoundnessTotalErrorAccounting` do not need to repack
the append residual or per-phase error bounds in the same theorem. -/
theorem fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSoundnessFields
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_seq :
      friSoundnessSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError)
    (h_total :
      friSoundnessTotalErrorAccounting
        (n := n) (s := s) (ω := ω) (l := l) m_ge_3 batchError friError)
    {agreementBridge : Prop}
    (query_pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (soundness_pieces_imply_claim :
      friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 →
      friSoundnessSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError →
      friSoundnessTotalErrorAccounting
        (n := n) (s := s) (ω := ω) (l := l) m_ge_3 batchError friError →
      fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond) f m_ge_3)
    (h_agreementBridge : agreementBridge) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  let parts :=
    FriSoundnessParts.of_queryRoundDensityBoundAndBatchedFRIOracleLensAndSequentialComposition
      (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond)
      f m_ge_3 init impl lang₁ lang₃ batchError friError
      (friSoundnessTotalErrorAccounting
        (n := n) (s := s) (ω := ω) (l := l) m_ge_3 batchError friError)
      soundness_pieces_imply_claim
  exact fri_soundness_of_parts
    (n := n) (s := s) (d := d) (ω := ω) (l := l)
    (domain_size_cond := domain_size_cond) f m_ge_3 parts
    (friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond)
      f m_ge_3 G δ queries l h_agreement query_pieces_imply_claim h_agreementBridge)
    h_seq h_total

omit [Nontrivial 𝔽] in
/-- Reassemble Claim 8.3 through the probability-route query-lift, an already-named concrete
sequential-composition field, and the named per-phase error-bound targets.

This keeps the append/virtual-oracle preservation work explicit as the source of `h_seq`, and keeps
the phase analyses explicit as `friBatchPhaseErrorBound` and `friTailPhaseErrorBound`. -/
theorem
    fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSoundnessFieldAndNamedPhaseBounds
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_seq :
      friSoundnessSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError)
    (h_batch_error :
      friBatchPhaseErrorBound
        (n := n) (s := s) (ω := ω) m_ge_3 batchError)
    (h_fri_error :
      friTailPhaseErrorBound
        (n := n) (ω := ω) (l := l) m_ge_3 friError)
    {agreementBridge : Prop}
    (query_pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (soundness_pieces_imply_claim :
      friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 →
      friSoundnessSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError →
      friSoundnessTotalErrorAccounting
        (n := n) (s := s) (ω := ω) (l := l) m_ge_3 batchError friError →
      fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond) f m_ge_3)
    (h_agreementBridge : agreementBridge) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSoundnessFields
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3 G δ queries h_agreement init impl lang₁ lang₃ h_seq
      (friSoundnessTotalErrorAccounting_of_named_phase_bounds
        (n := n) (s := s) (ω := ω) (l := l) m_ge_3 h_batch_error h_fri_error)
      query_pieces_imply_claim soundness_pieces_imply_claim h_agreementBridge

open ENNReal in
omit [Nontrivial 𝔽] in
/-- Reassemble Claim 8.3 after discharging the probability-route query-lift, concrete
sequential-composition, and concrete total-error-accounting fields.  The remaining explicit inputs
are the Claim 8.2 bridge and the phase soundness/append-residual data needed to supply the concrete
sequential field. -/
theorem
    fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndTotalError
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₂ : Set (((Fin t → 𝔽) × Spec.Statement 𝔽 (0 : Fin (k + 1))) ×
      (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_batch_soundness : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₁ lang₂
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t).verifier
      batchError)
    (h_fri_soundness : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₂ lang₃
      (BatchedFri.Spec.liftedFRI
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l t).verifier
      friError)
    (h_residual : OracleVerifier.appendSoundnessResidual
      (init := init) (impl := impl)
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t).verifier
      (BatchedFri.Spec.liftedFRI
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l t).verifier
      h_batch_soundness h_fri_soundness)
    (h_batch_error :
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽);
       (batchError : ℝ≥0∞) ≤ εC 𝔽 n s m ρ_sqrt))
    (h_fri_error :
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽);
       let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))));
       (friError : ℝ≥0∞) ≤ α ^ l))
    {agreementBridge : Prop}
    (query_pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (soundness_pieces_imply_claim :
      friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 →
      friSoundnessSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError →
      friSoundnessTotalErrorAccounting
        (n := n) (s := s) (ω := ω) (l := l) m_ge_3 batchError friError →
      fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond) f m_ge_3)
    (h_agreementBridge : agreementBridge) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialComposition
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3 G δ queries h_agreement init impl lang₁ lang₂ lang₃
      h_batch_soundness h_fri_soundness h_residual query_pieces_imply_claim
      soundness_pieces_imply_claim h_agreementBridge
      (friSoundnessTotalErrorAccounting_of_phase_bounds
        (n := n) (s := s) (ω := ω) (l := l) m_ge_3 h_batch_error h_fri_error)

open ENNReal in
omit [Nontrivial 𝔽] in
/-- Probability-route Claim 8.3 reassembly from named phase error-bound targets. -/
theorem
    fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndPhaseErrorBounds
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₂ : Set (((Fin t → 𝔽) × Spec.Statement 𝔽 (0 : Fin (k + 1))) ×
      (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_batch_soundness : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₁ lang₂
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t).verifier
      batchError)
    (h_fri_soundness : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₂ lang₃
      (BatchedFri.Spec.liftedFRI
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l t).verifier
      friError)
    (h_residual : OracleVerifier.appendSoundnessResidual
      (init := init) (impl := impl)
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t).verifier
      (BatchedFri.Spec.liftedFRI
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l t).verifier
      h_batch_soundness h_fri_soundness)
    (h_batch_error :
      friBatchPhaseErrorBound (𝔽 := 𝔽) n (s := s) (ω := ω) m_ge_3 batchError)
    (h_fri_error :
      friTailPhaseErrorBound (𝔽 := 𝔽) n (ω := ω) (l := l) m_ge_3 friError)
    {agreementBridge : Prop}
    (query_pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (soundness_pieces_imply_claim :
      friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 →
      friSoundnessSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError →
      friSoundnessTotalErrorAccounting
        (n := n) (s := s) (ω := ω) (l := l) m_ge_3 batchError friError →
      fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond) f m_ge_3)
    (h_agreementBridge : agreementBridge) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 :=
  fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndTotalError
    (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
    f m_ge_3 G δ queries h_agreement init impl lang₁ lang₂ lang₃
    h_batch_soundness h_fri_soundness h_residual h_batch_error h_fri_error
    query_pieces_imply_claim soundness_pieces_imply_claim h_agreementBridge

set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
set_option linter.style.longLine false in
#print axioms Fri.fri_jointAgreement_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialComposition
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSoundnessFields
set_option linter.style.longLine false in
#print axioms
  Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSoundnessFieldAndNamedPhaseBounds
set_option linter.style.longLine false in
#print axioms
  Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndTotalError
set_option linter.style.longLine false in
#print axioms
  Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndPhaseErrorBounds

end ProbabilitySoundnessAdapter
end Fri
