/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.ToMathlib.FriComplete
import ArkLib.ToMathlib.FriCompleteCompose

/-!
# FRI: Composed Folding Reduction Perfect Completeness (issue #117)

This module integrates the perfect completeness of the composed FRI reduction
(`Fri.Spec.reduction`), completing the proof outline from `ArkLib.ToMathlib.FriCompleteCompose`.
It defines the missing residuals and applies the sequential composition keystones.
-/

namespace Fri.Spec.Completeness

open OracleSpec OracleComp ProtocolSpec NNReal Domain

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ}
variable {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- **Brick residual — query round.** -/
def queryRoundPerfectCompletenessResidual
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (l : ℕ)
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    (hInit : NeverFail init) (δ : ℝ≥0) : Prop :=
  OracleReduction.perfectCompleteness init impl
    (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
    (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
    (QueryRound.queryOracleReduction.{0} s d dom_size_cond l)

/-- **Brick — query round** (reduction to its named residual). -/
theorem queryRound_perfectCompleteness
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (l : ℕ)
    (hInit : NeverFail init) (δ : ℝ≥0)
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    (hResidual : queryRoundPerfectCompletenessResidual (k := k)
      (hQueryChallenge := hQueryChallenge) init impl dom_size_cond l hInit δ) :
    OracleReduction.perfectCompleteness init impl
      (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      (QueryRound.queryOracleReduction.{0} s d dom_size_cond l) :=
  hResidual

/-- **Brick D residual — folding phase.** -/
def foldPhasePerfectCompletenessResidual
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
    (hInit : NeverFail init) (δ : ℝ≥0)
    [hFoldChallenge : ∀ i,
      SampleableType ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i)]
    (hRounds : ∀ i : Fin k, foldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit i (round_bound dom_size_cond) δ)
    (hFinal : finalFoldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit (round_bound dom_size_cond) δ) : Prop :=
  OracleReduction.perfectCompleteness init impl
    (inputRelation k s d dom_size_cond δ)
    (FinalFoldPhase.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
    (reductionFold k s d (ω := ω))

/-- **Brick D — folding phase completeness.** -/
theorem foldPhase_perfectCompleteness
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
    (hInit : NeverFail init) (δ : ℝ≥0)
    [∀ i, ∀ j, SampleableType ((FoldPhase.pSpec (ω := ω) s i).Challenge j)]
    [∀ j, SampleableType ((FinalFoldPhase.pSpec F).Challenge j)]
    [hFoldChallenge : ∀ i,
      SampleableType ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i)]
    [OracleVerifier.Append.AppendCoherent (reductionFold k s d (ω := ω)).verifier]
    (hRounds : ∀ i : Fin k, foldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit i (round_bound dom_size_cond) δ)
    (hFinal : finalFoldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit (round_bound dom_size_cond) δ)
    (hResidual : foldPhasePerfectCompletenessResidual
      (hFoldChallenge := hFoldChallenge) init impl dom_size_cond hInit δ hRounds hFinal) :
    OracleReduction.perfectCompleteness init impl
      (inputRelation k s d dom_size_cond δ)
      (FinalFoldPhase.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      (reductionFold k s d (ω := ω)) :=
  hResidual

/-- **Brick D residual — composed FRI reduction.** -/
def reductionPerfectCompletenessResidual
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (l : ℕ)
    (hInit : NeverFail init) (δ : ℝ≥0)
    [hFoldChallenge : ∀ i,
      SampleableType ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i)]
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    (hFold : OracleReduction.perfectCompleteness init impl
      (inputRelation k s d dom_size_cond δ)
      (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      (reductionFold k s d (ω := ω)))
    (hQuery : OracleReduction.perfectCompleteness init impl
      (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      (QueryRound.queryOracleReduction.{0} s d dom_size_cond l)) : Prop :=
  letI : ∀ i, SampleableType
      (((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F) ++ₚ
        QueryRound.pSpec l (ω := ω)).Challenge i) :=
    @ProtocolSpec.instSampleableTypeChallengeAppend _ _ _ _ hFoldChallenge hQueryChallenge
  OracleReduction.perfectCompleteness init impl
    (inputRelation k s d dom_size_cond δ)
    (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
    ((reductionFold k s d (ω := ω)).append
      (QueryRound.queryOracleReduction.{0} s d dom_size_cond l))

/-- **Brick D — composed FRI reduction perfect completeness.**
The honest FRI protocol is perfectly complete, reducing the proximity of the initial oracle
to the proximity of the final polynomial and the passing of the query checks. -/
theorem reduction_perfectCompleteness
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (l : ℕ)
    (hInit : NeverFail init) (δ : ℝ≥0)
    [∀ i, ∀ j, SampleableType ((FoldPhase.pSpec (ω := ω) s i).Challenge j)]
    [∀ j, SampleableType ((FinalFoldPhase.pSpec F).Challenge j)]
    [hFoldChallenge : ∀ i,
      SampleableType ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i)]
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    [OracleVerifier.Append.AppendCoherent (reductionFold k s d (ω := ω)).verifier]
    (hRounds : ∀ i : Fin k, foldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit i (round_bound dom_size_cond) δ)
    (hFinal : finalFoldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit (round_bound dom_size_cond) δ)
    (hFoldRes : foldPhasePerfectCompletenessResidual
      (hFoldChallenge := hFoldChallenge) init impl dom_size_cond hInit δ hRounds hFinal)
    (hQueryRes : queryRoundPerfectCompletenessResidual (k := k)
      (hQueryChallenge := hQueryChallenge) init impl dom_size_cond l hInit δ)
    (hResidual : reductionPerfectCompletenessResidual
      (hFoldChallenge := hFoldChallenge) (hQueryChallenge := hQueryChallenge)
      init impl dom_size_cond l hInit δ
      (foldPhase_perfectCompleteness init impl dom_size_cond hInit δ hRounds hFinal hFoldRes)
      (queryRound_perfectCompleteness init impl dom_size_cond l hInit δ hQueryRes)) :
    letI : ∀ i, SampleableType
        (((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F) ++ₚ
          QueryRound.pSpec l (ω := ω)).Challenge i) :=
      @ProtocolSpec.instSampleableTypeChallengeAppend _ _ _ _ hFoldChallenge hQueryChallenge
    OracleReduction.perfectCompleteness init impl
      (inputRelation k s d dom_size_cond δ)
      (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      ((reductionFold k s d (ω := ω)).append
        (QueryRound.queryOracleReduction.{0} s d dom_size_cond l)) := by
  unfold reductionPerfectCompletenessResidual at hResidual
  exact reduction_perfectCompleteness_of_phases init impl dom_size_cond l
    (foldPhase_perfectCompleteness init impl dom_size_cond hInit δ hRounds hFinal hFoldRes)
    (queryRound_perfectCompleteness init impl dom_size_cond l hInit δ hQueryRes)
    hResidual

end Fri.Spec.Completeness
