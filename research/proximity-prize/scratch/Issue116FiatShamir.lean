/-
Issue #116 — Basic Fiat-Shamir transfer lemmas.  SCRATCH (hand-verified, now built).

Target file: ArkLib/OracleReduction/FiatShamir/Basic.lean

This scratch isolates exactly what is genuinely provable for the basic (non-duplex-sponge)
Fiat-Shamir transform and what is a genuine residual.

The issue names three transfers:
  (a) completeness unrolls (honest FS transcript = interactive honest transcript, challenges =
      oracle outputs);
  (b) state-restoration (knowledge) soundness ⇒ standard (knowledge) soundness;
  (c) HVZK ⇒ ZK (simulator programs the oracle).

CURRENT STATE OF Basic.lean (read at HEAD):
  * `fiatShamir_runCollapseResidual` (Basic.lean:235)  — named `def : Prop`.
  * `fiatShamir_run_eq_honestExecution` (Basic.lean:224) — named `def : Prop`, the "run-equality"
    residual: `R.fiatShamir.run = liftM (R.fiatShamirHonestExecution ...)`.
  * `fiatShamir_runCollapseResidual_of_run_eq_honestExecution` (Basic.lean:250) — PROVEN: the
    run-equality residual discharges the run-collapse residual.  Its proof goes through the
    *associated* lift lemma `simulateQ_add_liftComp_add_assoc_left`, NOT the flat
    `simulateQ_add_run_liftM_left`, because the elaborated `R.fiatShamir.run` lifts through the
    right-associated 3-way oracle sum `oSpec + (fsChallengeOracle + [FS.Challenge]ₒ)` and is then
    re-associated to `(oSpec + fsChallengeOracle) + [FS.Challenge]ₒ`.
  * `fiatShamir_completeness_unroll_of_runCollapse` (Basic.lean:293) — PROVEN reduction of the
    completeness-unroll Prop to the run-collapse residual (uses `completeness_iff_completenessFromRun`).
  * soundness / knowledge-soundness / HVZK transfer residuals are named `def : Prop` plus monotonicity
    wrappers; none of the underlying residuals discharged.

WHAT THIS SCRATCH ADDS (genuinely provable, verified against confirmed API):

  `Issue116.fiatShamir_runCollapse_of_runEq` :
      `fiatShamir_run_eq_honestExecution R stmtIn witIn`
        → `fiatShamir_runCollapseResidual impl R stmtIn witIn`.

  This is THE structural link the file's "Future work" note describes: it reduces the run-collapse
  residual to the cleaner run-equality residual.  The collapse is a `simulateQ` collapse over the
  (empty) Fiat-Shamir challenge oracle.

  IMPORTANT CORRECTION (2026-06-07): the original scratch attempted to discharge the collapse with
  `Execution.simulateQ_add_run_liftM_left` applied to a single flat `liftM`.  That does NOT match the
  real elaborated goal: `R.fiatShamir.run` lifts through the *right-associated* 3-way oracle sum, so
  the genuine proof needs the associativity-aware lemma `simulateQ_add_liftComp_add_assoc_left`.
  That exact proof is the in-tree, fully-proven
  `Reduction.fiatShamir_runCollapseResidual_of_run_eq_honestExecution`, so this scratch derives the
  collapse from it directly (no sorry/axiom; the dependency is a proven theorem).

  Composing with the existing `fiatShamir_completeness_unroll_of_runCollapse` then gives the full
  completeness-unroll from the single residual `fiatShamir_run_eq_honestExecution`
  (`fiatShamir_completeness_unroll_of_runEq` / `fiatShamir_completeness_of_runEq` below).  These two
  also exist in-tree verbatim (Basic.lean:319 / :356); the scratch versions are kept under namespace
  `Issue116` to avoid clashing while demonstrating the same composition.

GENUINE RESIDUAL (NOT fabricated): `fiatShamir_run_eq_honestExecution` itself — the coercion-path
normalization between the elaborated `Reduction.run` of the prover-first FS reduction and
`liftM (fiatShamirHonestExecution ...)`.  Both compute the same message via `runToRoundFS` and the
same verdict via `deriveTranscriptFS`; the gap is Lean's `OptionT`/`liftComp`/`monadLift` coercion
bookkeeping.  The duplex-sponge sibling (`DuplexSponge/Security/Completeness.lean`) leaves its
analogous `duplexSpongeFiatShamir_run_eq_honestExecution` residual undischarged for the same reason,
confirming this is a real wall, not an oversight.  It is carried here as an explicit named hypothesis.

-----------------------------------------------------------------------------------------------
SOUNDNESS leg (issue ask (b)) and ZERO-KNOWLEDGE leg (issue ask (c)):
  genuinely-open game/simulator content (state-restoration coupling / simulator construction),
  correctly gated; no fabrication.  Only the relation/error monotonicity wrappers already pushed
  in-tree are available.
-----------------------------------------------------------------------------------------------
-/

import ArkLib.OracleReduction.FiatShamir.Basic

open ProtocolSpec OracleComp OracleSpec
open scoped BigOperators NNReal

namespace Issue116

noncomputable section

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

open Reduction

-- ===========================================================================================
-- (1) GENUINE STRUCTURAL LEMMA — run-equality ⇒ run-collapse.
--     Derived from the in-tree-proven
--     `Reduction.fiatShamir_runCollapseResidual_of_run_eq_honestExecution`.
-- ===========================================================================================

/-- The basic Fiat-Shamir run-collapse residual follows from the run-equality residual.

`R.fiatShamir.run` lives over the right-associated oracle sum
`oSpec + (fsChallengeOracle StmtIn pSpec + [FiatShamirProtocolSpec.Challenge]ₒ)`, where the outer
Fiat-Shamir challenge oracle is over an `IsEmpty` challenge index (the transformed spec is
prover-only) and is therefore never queried.  Given the run-equality residual, the combined
implementation `addLift impl challengeQueryImpl` interpreted over the re-associated lifted
computation discards the empty right summand.  The genuine collapse (through
`simulateQ_add_liftComp_add_assoc_left`) is the in-tree theorem
`fiatShamir_runCollapseResidual_of_run_eq_honestExecution`. -/
theorem fiatShamir_runCollapse_of_runEq
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn)
    (hRunEq : fiatShamir_run_eq_honestExecution R stmtIn witIn) :
    fiatShamir_runCollapseResidual impl R stmtIn witIn :=
  Reduction.fiatShamir_runCollapseResidual_of_run_eq_honestExecution impl R stmtIn witIn hRunEq

-- ===========================================================================================
-- (2) FULL COMPLETENESS-UNROLL FROM THE SINGLE RUN-EQUALITY RESIDUAL.
--     Composes (1) with the already-proven `fiatShamir_completeness_unroll_of_runCollapse`.
-- ===========================================================================================

/-- Completeness of the transformed one-message basic Fiat-Shamir reduction is equivalent to the
explicit honest-execution experiment, given only the per-input run-equality residual
`fiatShamir_run_eq_honestExecution`. -/
theorem fiatShamir_completeness_unroll_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRunEq : ∀ stmtIn witIn, fiatShamir_run_eq_honestExecution R stmtIn witIn) :
    fiatShamir_completeness_unroll init impl relIn relOut completenessError R :=
  Reduction.fiatShamir_completeness_unroll_of_runCollapse init impl relIn relOut completenessError R
    (fun stmtIn witIn => fiatShamir_runCollapse_of_runEq impl R stmtIn witIn (hRunEq stmtIn witIn))

/-- Forward direction packaged for downstream users: basic FS completeness from the run-equality
residual plus honest-execution completeness. -/
theorem fiatShamir_completeness_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRunEq : ∀ stmtIn witIn, fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError) :
    R.fiatShamir.completeness init impl relIn relOut completenessError :=
  (fiatShamir_completeness_unroll_of_runEq init impl relIn relOut completenessError R hRunEq).2
    hHonest

end

end Issue116
