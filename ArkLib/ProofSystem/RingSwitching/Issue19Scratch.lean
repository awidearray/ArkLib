import ArkLib.ProofSystem.RingSwitching.SumcheckPhase

/-!
# Issue #19 audit frontier

This scratch file used to contain an attempted proof of the iterated sumcheck round
perfect-completeness residual.  The actual source module now exposes that obligation as the named
`Prop` `iteratedSumcheckOracleReduction_perfectCompleteness_residual`, so keeping a duplicate
scratch theorem with executable holes made the root sorry census fail without adding a usable API.

The useful proof-plan context is still worth preserving.  The honest-round algebra is in-tree:
* `getSumcheckRoundPoly_points_sum_eq_cube` for the verifier sum-check;
* `getSumcheckRoundPoly_eval_eq_cube_succ` for the round transition;
* `fixFirstVariablesOfMQP_projectToMid_step` for the witness structural-invariant step.

The remaining work is the monadic `OracleReduction.run` peel, adapted from the verified Binius
sibling `iteratedSumcheckOracleReduction_perfectCompleteness`.  Until that assembly is complete,
this file stays an importable audit anchor and leaves the real proof obligation explicit and
unlaundered in `SumcheckPhase.lean`.
-/

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

namespace RingSwitching.SumcheckPhase
noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Scratch/audit alias for the live iterated-sumcheck completeness frontier. -/
abbrev iteratedSumcheckOracleReduction_perfectCompleteness_residual_frontier : Prop :=
    iteratedSumcheckOracleReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl)

end
end RingSwitching.SumcheckPhase

/-! ### Axiom audit (issue #19 scratch/audit alias) -/

#print axioms RingSwitching.SumcheckPhase.iteratedSumcheckOracleReduction_perfectCompleteness_residual_frontier
