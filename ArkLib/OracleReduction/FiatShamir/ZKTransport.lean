/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic

/-!
# Basic Fiat-Shamir ZK Pre-Transport Wrappers (#116)

`FiatShamir/Basic.lean` exposes wrappers that apply a discharged HVZK simulator-transfer
residual on a larger relation and then restrict the Fiat-Shamir conclusion. This companion
module provides the dual consumer shape: first restrict the source `Reduction.isHVZK` proof to
the relation where the transfer residual is stated, then apply that residual.

These declarations are API plumbing over the existing residual surfaces. They do not construct a
Fiat-Shamir simulator or discharge the semantic HVZK transfer residual.
-/

noncomputable section

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ τ : Type}

attribute [local instance 10000] Reduction.fiatShamirZKNoChallengeSampleable

/-- Basic Fiat-Shamir statistical HVZK from a transfer residual stated on a sub-relation, after
first restricting the source HVZK proof to that sub-relation. -/
theorem fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer ε R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTransfer R.fiatShamir ε :=
  fiatShamir_isStatHVZK_of_HVZK init impl fsInit fsImpl relTransfer ε R hTransfer
    (hHVZK.mono_relation hsub)

/-- Basic Fiat-Shamir statistical HVZK from a transfer residual stated on a sub-relation, after
first restricting the source HVZK proof and then relaxing the target error budget. -/
theorem fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation_error
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    {ε₁ ε₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer ε₁ R)
    (hle : ε₁ ≤ ε₂)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTransfer R.fiatShamir ε₂ :=
  (fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation init impl fsInit fsImpl hsub ε₁ R
    hTransfer hHVZK).mono_error hle

/-- Basic Fiat-Shamir perfect HVZK from a perfect transfer residual stated on a sub-relation, after
first restricting the source HVZK proof to that sub-relation. -/
theorem fiatShamir_isHVZK_of_transfer_pre_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl relTransfer R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isHVZK fsInit fsImpl relTransfer R.fiatShamir :=
  fiatShamir_isHVZK_of_transfer init impl fsInit fsImpl relTransfer R hTransfer
    (hHVZK.mono_relation hsub)

/-- Basic Fiat-Shamir statistical HVZK from a perfect transfer residual stated on a sub-relation,
after first restricting the source HVZK proof to that sub-relation. -/
theorem fiatShamir_isStatHVZK_of_transfer_pre_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl relTransfer R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTransfer R.fiatShamir ε :=
  (fiatShamir_isHVZK_of_transfer_pre_mono_relation init impl fsInit fsImpl hsub R
    hTransfer hHVZK).isStatHVZK ε

/-- Basic Fiat-Shamir perfect HVZK from a zero-error statistical transfer residual stated on a
sub-relation, after first restricting the source HVZK proof to that sub-relation. -/
theorem fiatShamir_isHVZK_of_HVZK_zero_pre_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isHVZK fsInit fsImpl relTransfer R.fiatShamir :=
  fiatShamir_isHVZK_of_HVZK_zero init impl fsInit fsImpl relTransfer R hTransfer
    (hHVZK.mono_relation hsub)

/-- Basic Fiat-Shamir statistical HVZK at any error from a zero-error statistical transfer residual
stated on a sub-relation, after first restricting the source HVZK proof to that sub-relation. -/
theorem fiatShamir_isStatHVZK_of_HVZK_zero_pre_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTransfer R.fiatShamir ε :=
  (fiatShamir_isHVZK_of_HVZK_zero_pre_mono_relation init impl fsInit fsImpl hsub R
    hTransfer hHVZK).isStatHVZK ε

#print axioms fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation
#print axioms fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation_error
#print axioms fiatShamir_isHVZK_of_transfer_pre_mono_relation
#print axioms fiatShamir_isStatHVZK_of_transfer_pre_mono_relation
#print axioms fiatShamir_isHVZK_of_HVZK_zero_pre_mono_relation
#print axioms fiatShamir_isStatHVZK_of_HVZK_zero_pre_mono_relation

end Reduction
