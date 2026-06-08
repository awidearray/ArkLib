/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Spec
import ArkLib.ProofSystem.RingSwitching.BatchingPhase
import ArkLib.ProofSystem.RingSwitching.SumcheckPhase
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Full Ring-Switching Protocol

This module contains specifications and security properties for the full
ring-switching protocol. The protocol is a sequential composition of:
1. **Batching Phase** (polynomial packing and batching via tensor algebra operations)
2. **Sumcheck Phase** (ℓ' rounds of sumcheck, and the final sumcheck step)
3. **Large Field Invocation** (invocation to underlying large-field IOPCS)

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
-/

namespace RingSwitching.FullRingSwitching
noncomputable section
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (mlIOPCS : MLIOPCS L ℓ')

def batchingCoreVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:= BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (V₂:=SumcheckPhase.coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (pSpec₂:=pSpecCoreInteraction L ℓ')

/-- The batching-then-core composite verifier is `AppendCoherent` (batching `.append`
core-interaction, both phases coherent), so it can be `.append`ed onto the MLIOPCS sub-protocol. -/
instance instBatchingCoreVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS) :=
  OracleVerifier.Append.AppendCoherent.append
    (c₁ := BatchingPhase.instOracleVerifierAppendCoherent κ L K P ℓ ℓ' h_l
      (aOStmtIn := mlIOPCS.toAbstractOStmtIn))
    (c₂ := RingSwitching.SumcheckPhase.instCoreInteractionOracleVerifierAppendCoherent κ L K P ℓ ℓ' h_l
      (aOStmtIn := mlIOPCS.toAbstractOStmtIn)) _ _

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
def fullOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
    (V₂:=mlIOPCS.oracleReduction.verifier)
    (pSpec₂:=mlIOPCS.pSpec)

def batchingCoreReduction :=
  OracleReduction.append
    (R₁ := BatchingPhase.batchingOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (R₂ := SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
       mlIOPCS.toAbstractOStmtIn)
    (pSpec₂:=pSpecCoreInteraction L ℓ')

/-- The batching-then-core composite reduction's verifier is `AppendCoherent`. -/
instance instBatchingCoreReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).verifier :=
  OracleVerifier.Append.AppendCoherent.oracleReductionAppend
    (R₁ := BatchingPhase.batchingOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (R₂ := RingSwitching.SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
       mlIOPCS.toAbstractOStmtIn)

/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
def fullOracleReduction :
    OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L:=L) (ℓ := ℓ)) (StmtOut := Bool)
    (OStmtIn:= mlIOPCS.OStmtIn)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPspec κ L K P ℓ' mlIOPCS)
    (WitIn := BatchingWitIn (L:=L) (K:=K) (ℓ := ℓ) (ℓ' := ℓ')) (WitOut := Unit)
    :=
  (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).append mlIOPCS.oracleReduction

/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
def fullOracleProof :
    OracleProof []ₒ
    (Statement := BatchingStmtIn (L:=L) (ℓ := ℓ))
    (OStatement := mlIOPCS.OStmtIn)
    (Witness := BatchingWitIn (L:=L) (K:=K) (ℓ := ℓ) (ℓ' := ℓ'))
    (pSpec:= fullPspec κ L K P ℓ' mlIOPCS) :=
    fullOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS

variable [∀ i, SampleableType (mlIOPCS.pSpec.Challenge i)]

/-- Input relation for the full ring-switching protocol -/
abbrev fullInputRelation := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ'
  h_l mlIOPCS.toAbstractOStmtIn
abbrev fullOutputRelation := acceptRejectOracleRel

open scoped NNReal
open Sumcheck.Structured

section SecurityProperties
variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [(i : mlIOPCS.pSpec.ChallengeIdx) → SampleableType (mlIOPCS.pSpec.Challenge i)] in
-- `[IsDomain L] [IsDomain K]` are needed by the core-interaction (final-sumcheck) completeness,
-- which invokes the DP24 capstone `A_MLE_eval_eq_compute_final_eq_value` (an `IsDomain` algebra
-- lemma). They hold in every real instantiation (`binaryTowerProfile` builds from fields `K`, `L`).
lemma batchingCore_perfectCompleteness [IsDomain L] [IsDomain K]
    (hCoreInteractionAppendPerfectCompleteness :
      (SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn).perfectCompleteness
        (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
        (OStmtIn := mlIOPCS.toAbstractOStmtIn.OStmtIn)
        (StmtOut := MLPEvalStatement L ℓ')
        (OStmtOut := mlIOPCS.toAbstractOStmtIn.OStmtIn)
        (WitIn := SumcheckWitness L ℓ' 0)
        (WitOut := WitMLP L ℓ')
        (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0)
        (relOut := mlIOPCS.toAbstractOStmtIn.toRelInput)
        (init := init)
        (impl := impl))
    (hBatchingCoreAppendPerfectCompleteness :
      (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
        (pSpec := pSpecLargeFieldReduction κ L K P ℓ')
        (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l
          mlIOPCS.toAbstractOStmtIn)
        (relOut := mlIOPCS.toRelInput)
        (init := init)
        (impl := impl)) :
  (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
  (pSpec := pSpecLargeFieldReduction κ L K P ℓ')
  (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
  (relOut := mlIOPCS.toRelInput)
  (init:=init) (impl:=impl) := by
  exact OracleReduction.append_perfectCompleteness
    (R₁ := BatchingPhase.batchingOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (R₂ := SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn)
    (h₁ := BatchingPhase.batchingReduction_perfectCompleteness κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn hBatching)
    (h₂ := SumcheckPhase.coreInteraction_perfectCompleteness
      κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn
      (init := init) (impl := impl) hRounds hCoreInteractionAppendPerfectCompleteness)
    (hResidual := hBatchingCoreAppendPerfectCompleteness)
    (hRounds : SumcheckPhase.iteratedSumcheckOracleReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := mlIOPCS.toAbstractOStmtIn) (init := init) (impl := impl))
    (hCoreInteractionAppendPerfectCompleteness :
      (SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn).perfectCompleteness
        (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
        (OStmtIn := mlIOPCS.toAbstractOStmtIn.OStmtIn)
        (StmtOut := MLPEvalStatement L ℓ')
        (OStmtOut := mlIOPCS.toAbstractOStmtIn.OStmtIn)
        (WitIn := SumcheckWitness L ℓ' 0)
        (WitOut := WitMLP L ℓ')
        (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0)
        (relOut := mlIOPCS.toAbstractOStmtIn.toRelInput)
        (init := init)
        (impl := impl))
    (hBatchingCoreAppendPerfectCompleteness :
      (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
        (pSpec := pSpecLargeFieldReduction κ L K P ℓ')
        (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l
          mlIOPCS.toAbstractOStmtIn)
        (relOut := mlIOPCS.toRelInput)
        (init := init)
        (impl := impl))
    (hFullAppendPerfectCompleteness :
      (fullOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
        (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l
          mlIOPCS.toAbstractOStmtIn)
        (relOut := acceptRejectOracleRel)
        (init := init)
        (impl := impl)) :
  (fullOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
    (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl)
     := by
  exact OracleReduction.append_perfectCompleteness
    (R₁ := batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS)
    (R₂ := mlIOPCS.oracleReduction)
    (Oₛ₃ := by exact fun _ ↦ OracleInterface.instDefault)
    (h₁ := batchingCore_perfectCompleteness κ L K P ℓ ℓ' h_l mlIOPCS init hBatching hRounds
      hCoreInteractionAppendPerfectCompleteness hBatchingCoreAppendPerfectCompleteness)
    (h₂ := mlIOPCS.perfectCompleteness)
    (hResidual := hFullAppendPerfectCompleteness)

def batchingCoreRbrKnowledgeError
    (i : (pSpecBatching κ L K P ++ₚ pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  Sum.elim (f:=BatchingPhase.batchingRBRKnowledgeError κ L K P)
    (g:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (ChallengeIdx.sumEquiv.symm i)

def fullRbrKnowledgeError (i : (fullPspec κ L K P ℓ' mlIOPCS).ChallengeIdx) : ℝ≥0
    := Sum.elim (f:=batchingCoreRbrKnowledgeError κ L K P ℓ')
  (g:=mlIOPCS.rbrKnowledgeError)
  (ChallengeIdx.sumEquiv.symm i)

variable [SampleableType L]

omit [(i : mlIOPCS.pSpec.ChallengeIdx) → SampleableType (mlIOPCS.pSpec.Challenge i)] in
/-- Round-by-round knowledge soundness for the full ring-switching oracle verifier.
`IsDomain K` (with the existing `IsDomain L`) is inherited from the batching phase's knowledge
soundness, where it backs the DP24 row-extraction capstone; it holds in every real instantiation
(`binaryTowerProfile` builds from a field `K`).

The generic RingSwitching wrapper no longer carries a free Boolean-domain embedding `𝓑`. The
current local KState repairs use the always-valid unit error bounds in the batching and iterated
sumcheck phases until the separate DP24/Schwartz-Zippel root-count residual is proved. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness [IsDomain L] [IsDomain K]
    (hCoreInteractionAppendRbrKnowledgeSoundness :
      (SumcheckPhase.coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn).rbrKnowledgeSoundness
        (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
        (OStmtIn := mlIOPCS.toAbstractOStmtIn.OStmtIn)
        (StmtOut := MLPEvalStatement L ℓ')
        (OStmtOut := mlIOPCS.toAbstractOStmtIn.OStmtIn)
        (WitIn := SumcheckWitness L ℓ' 0)
        (WitOut := WitMLP L ℓ')
        (init := init)
        (impl := impl)
        (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0)
        (relOut := mlIOPCS.toAbstractOStmtIn.toRelInput)
        (rbrKnowledgeError := SumcheckPhase.coreInteractionRbrKnowledgeError (L:=L) (ℓ':=ℓ')))
    (hBatchingCoreAppendRbrKnowledgeSoundness :
      (batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS).rbrKnowledgeSoundness
        (init := init)
        (impl := impl)
        (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
        (relOut := mlIOPCS.toRelInput)
        (rbrKnowledgeError := batchingCoreRbrKnowledgeError κ L K P ℓ'))
    (hFullAppendRbrKnowledgeSoundness :
      (fullOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS).rbrKnowledgeSoundness
        (init := init)
        (impl := impl)
        (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
        (relOut := fullOutputRelation)
        (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i)) :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := fullOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
    (init := init)
    (impl := impl)
    (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
    (relOut := fullOutputRelation)
    (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i) := by
  unfold fullOracleVerifier fullRbrKnowledgeError
  have batchInteractionRBRKS :=
    OracleVerifier.append_rbrKnowledgeSoundness (init:=init) (impl:=impl)
    (hResidual := hBatchingCoreAppendRbrKnowledgeSoundness)
    (rel₁:=fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
    (rel₂:=sumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0)
    (rel₃:=mlIOPCS.toRelInput)
    (V₁:=BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (V₂:=SumcheckPhase.coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (rbrKnowledgeError₁:=BatchingPhase.batchingRBRKnowledgeError κ L K P)
    (rbrKnowledgeError₂:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (h₁:=BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness κ L K P ℓ
      ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (h₂:=SumcheckPhase.coreInteraction_rbrKnowledgeSoundness κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn hCoreInteractionAppendRbrKnowledgeSoundness)

  have res :=
    OracleVerifier.append_rbrKnowledgeSoundness (init:=init) (impl:=impl)
    (hResidual := hFullAppendRbrKnowledgeSoundness)
    (rel₁:=fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
    (rel₂:=mlIOPCS.toRelInput)
    (rel₃:=fullOutputRelation)
    (V₁:=batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
    (V₂:=mlIOPCS.oracleReduction.verifier)
    (Oₛ₃:=by exact fun i ↦ OracleInterface.instDefault)
    (rbrKnowledgeError₁:=batchingCoreRbrKnowledgeError κ L K P ℓ')
    (rbrKnowledgeError₂:=mlIOPCS.rbrKnowledgeError)
    (h₁:=batchInteractionRBRKS) (h₂:=by
      convert mlIOPCS.rbrKnowledgeSoundness (L:=L) (ℓ' := ℓ') (init:=init) (impl:=impl)
    )
  convert res

end SecurityProperties
end
end RingSwitching.FullRingSwitching
