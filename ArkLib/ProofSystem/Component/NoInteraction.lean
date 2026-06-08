/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
  # A classification of all (oracle) reductions with no interaction between the prover and verifier

  This file contains the general form of all (oracle) reductions with no interaction between the
  prover and verifier. In this setting, there are many specializations, and we can use these to
  derive simpler conditions for completeness & soundness.
-/

open OracleComp OracleInterface ProtocolSpec Function NNReal ENNReal

namespace NoInteraction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}

section Reduction

variable (mapStmt : StmtIn → OracleComp oSpec StmtOut)
  (mapWit : StmtIn → WitIn → OracleComp oSpec WitOut)

/-- Collect the functions `mapStmt` and `mapWit` into a single function `mapCtx` -/
@[reducible]
def combineMap : StmtIn × WitIn → OracleComp oSpec (StmtOut × WitOut) :=
  fun ⟨stmt, wit⟩ => do return (← mapStmt stmt, ← mapWit stmt wit)

/-- The prover in a no-interaction reduction can be specified by a tuple of functions:
- `mapStmt : StmtIn → OracleComp oSpec StmtOut` maps the input statement to an output statement
- `mapWit : StmtIn → WitIn → OracleComp oSpec WitOut` maps the input witness to an output witness,
  depending on the input statement
-/
@[reducible]
def prover : Prover oSpec StmtIn WitIn StmtOut WitOut !p[] where
  PrvState | 0 => StmtIn × WitIn
  input := id
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := combineMap mapStmt mapWit

/-- The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a
  function `mapStmt : StmtIn → OracleComp oSpec StmtOut` -/
@[reducible]
def verifier : Verifier oSpec StmtIn StmtOut !p[] where
  verify := fun stmt _ => mapStmt stmt

/-- The no-interaction reduction can be specified by a tuple of functions:
- `mapStmt : StmtIn → OracleComp oSpec StmtOut` maps the input statement to an output statement
- `mapWit : StmtIn → WitIn → OracleComp oSpec WitOut` maps the input witness to an output witness,
  depending on the input statement
-/
@[reducible]
def reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut !p[] where
  prover := prover mapStmt mapWit
  verifier := verifier mapStmt

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}

/-- A `some`-valued `ProbComp` under `OptionT.mk` is `OptionT.lift` of the underlying computation:
  the no-interaction run never fails (the prover and verifier only `liftM` total `OracleComp oSpec`
  maps, never `failure`), so its `Reduction.run` distribution is the `OptionT.lift` of a plain
  `ProbComp`. Used to peel the `OptionT` wrapper in `reduction_completeness`. -/
private theorem optionT_mk_some_map_eq_lift {α : Type} (x : ProbComp α) :
    (OptionT.mk (some <$> x) : OptionT ProbComp α) = OptionT.lift x := by
  rw [OptionT.lift, bind_pure_comp]

private lemma simulateQ_addLift_liftM_oracleComp_empty
    {α : Type} (oa : OracleComp oSpec α) :
    simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl (pSpec := (!p[] : ProtocolSpec 0))))
      (liftM oa : OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) =
      (simulateQ impl oa : StateT σ ProbComp α) := by
  rw [show (liftM oa : OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) =
      liftComp oa (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) by
        rw [liftComp_eq_liftM]]
  rw [QueryImpl.simulateQ_add_liftComp_left]

private lemma liftM_optionT_lift_eq_monadLift_liftM_empty
    {α : Type} (mx : OracleComp oSpec α) :
    (liftM (OptionT.lift mx : OptionT (OracleComp oSpec) α) :
      OptionT (OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)) α) =
      (monadLift (liftM mx : OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) :
        OptionT (OracleComp
          (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)) α) := by
  rw [liftM_OptionT_eq]
  change
    simulateQ (fun t => (liftM (OracleSpec.query t) :
        OracleComp
          (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) _))
      (OptionT.lift mx).run =
    (monadLift (liftM mx : OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) :
      OptionT (OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)) α).run
  rw [show OptionT.lift mx = OptionT.mk (some <$> mx) by rfl]
  rw [show (monadLift (liftM mx : OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) :
      OptionT (OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)) α).run =
      some <$> (monadLift (liftM mx : OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) :
        OracleComp
          (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) by
        exact OptionT.run_monadLift
          (m := OracleComp
            (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface))
          (n := OracleComp
            (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface))
          (liftM mx : OracleComp
            (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α)]
  rw [monadLift_eq_self]
  change simulateQ (fun t => (liftM (OracleSpec.query t) :
      OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) _))
    (some <$> mx) =
      some <$> (liftM mx : OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α)
  rw [simulateQ_map]
  rw [show simulateQ (fun t => (liftM (OracleSpec.query t) :
        OracleComp
          (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) _))
      mx =
      liftComp mx
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) by rfl]
  rw [liftComp_eq_liftM]

private lemma liftM_oracleComp_eq_monadLift_liftM_empty
    {α : Type} (mx : OracleComp oSpec α) :
    (liftM mx : OptionT (OracleComp
      (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)) α) =
      (monadLift (liftM mx : OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) :
        OptionT (OracleComp
          (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)) α) := by
  change (liftM ((mx : OptionT (OracleComp oSpec) α)) :
      OptionT (OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)) α) = _
  rw [oracleComp_toOptionT_eq_lift]
  exact liftM_optionT_lift_eq_monadLift_liftM_empty mx

private lemma simulateQ_addLift_liftM_oracleComp_optionT_run_empty
    {α : Type} (oa : OracleComp oSpec α) :
    simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl (pSpec := (!p[] : ProtocolSpec 0))))
      (OptionT.run (liftM oa : OptionT (OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)) α)) =
      (some <$> simulateQ impl oa : StateT σ ProbComp (Option α)) := by
  rw [liftM_oracleComp_eq_monadLift_liftM_empty oa]
  rw [show (monadLift (liftM oa : OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) :
      OptionT (OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)) α).run =
      some <$> (monadLift (liftM oa : OracleComp
        (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) :
        OracleComp
          (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α) by
        exact OptionT.run_monadLift
          (m := OracleComp
            (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface))
          (n := OracleComp
            (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface))
          (liftM oa : OracleComp
            (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface) α)]
  rw [monadLift_eq_self]
  rw [simulateQ_map]
  rw [simulateQ_addLift_liftM_oracleComp_empty (impl := impl) oa]

/-- Completeness of a no-interaction reduction.

  **Faithfulness of the hypothesis `hRel`.** `Reduction.run` (`Execution.lean`) runs the prover
  and the verifier as two *independent* sub-computations: the prover evaluates
  `combineMap mapStmt mapWit` (one call each to `mapStmt` and `mapWit`), while the verifier
  *separately* evaluates `mapStmt` again on the same input statement. The completeness event
  (`Reduction.completeness`, `Security/Basic.lean`) then demands not only
  `(stmtOut, witOut) ∈ relOut` but also that the prover's and the verifier's output statements
  *agree* (`prvStmtOut = stmtOut`).
  When `mapStmt` is randomized (queries `oSpec`), the two independent evaluations may disagree, so a
  hypothesis about a *single* evaluation of `combineMap` is too weak to imply completeness — it
  cannot constrain the verifier's separate `mapStmt` call. Accordingly `hRel` is stated over the
  *genuine* run distribution: the prover's `combineMap`, the verifier's separate `mapStmt`, and the
  success event including the agreement constraint, all threaded through the *same* state via
  `simulateQ impl`. There is no challenge oracle to lift (the protocol `!p[]` has no rounds), so
  this is the faithful image of `Reduction.run` for the no-interaction reduction. -/
theorem reduction_completeness {ε : ℝ≥0} [DecidablePred (· ∈ relOut)]
    [DecidableEq StmtOut]
    (hRel : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn →
      Pr[ fun ⟨⟨pStmtOut, witOut⟩, vStmtOut⟩ =>
          (vStmtOut, witOut) ∈ relOut ∧ pStmtOut = vStmtOut | do
        (simulateQ impl <| do
            let ctxOut ← combineMap mapStmt mapWit ⟨stmtIn, witIn⟩
            let vStmtOut ← mapStmt stmtIn
            pure (ctxOut, vStmtOut)).run' (← init)] ≥ 1 - ε) :
    Reduction.completeness init impl relIn relOut (reduction mapStmt mapWit) ε := by
  simp only [Reduction.completeness, Reduction.run, Verifier.run, prover, Prover.run,
    Prover.runToRound_zero_of_prover_first, Fin.last, Fin.zero_eta, id_eq, QueryImpl.addLift_def]
  intro stmtIn witIn hStmtIn
  refine ge_trans (le_of_eq ?_) (hRel stmtIn witIn hStmtIn)
  simp only [combineMap, OptionT.run_bind,
    OptionT.run_monadLift, monadLift_eq_self,
    simulateQ_bind, simulateQ_map,
    ← liftComp_eq_liftM, OracleComp.liftComp_bind, OracleComp.liftComp_map,
    QueryImpl.simulateQ_add_liftComp_left, QueryImpl.liftTarget_self,
    Option.elimM, Option.elim, Option.getM,
    StateT.run'_eq, StateT.run_bind, StateT.run_map, liftM_map, OptionT.run_map,
    bind_pure_comp, map_bind, bind_assoc, map_pure, pure_bind,
    bind_map_left, Functor.map_map]
  conv_rhs =>
    pattern (OptionT.run (liftM _))
    change OracleComp.liftComp (some <$> mapStmt stmtIn) _
  conv_rhs =>
    pattern (simulateQ _ (OracleComp.liftComp _ _))
    rw [QueryImpl.simulateQ_add_liftComp_left, simulateQ_map]
  conv_rhs =>
    arg 1; arg 1
    simp only [StateT.run_map, map_bind, Functor.map_map, Function.comp, Option.map_some,
      bind_assoc, bind_pure_comp, map_pure]
    -- split the innermost `(some ∘ proj) <$> X` into `some <$> (proj <$> X)`
    enter [2, __do_lift]
    enter [2, a]
    enter [2, a_1]
    rw [← Functor.map_map]
  -- factor `some` outward, innermost bind first
  conv_rhs =>
    arg 1; arg 1
    enter [2, __do_lift]
    enter [2, a]
    rw [← map_bind]
  conv_rhs =>
    arg 1; arg 1
    enter [2, __do_lift]
    rw [← map_bind]
  conv_rhs =>
    arg 1; arg 1
    rw [← map_bind]
  rw [optionT_mk_some_map_eq_lift, OptionT.probEvent_lift]
  simp only [probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]

/-- The honest transcript distribution for a no-interaction reduction is the deterministic empty
transcript. The statement and witness maps may be randomized and oracle-dependent, but their outputs
are not part of the zero-round transcript. -/
theorem honestTranscriptDist_reduction_evalDist
    (stmtIn : StmtIn) (witIn : WitIn) :
    evalDist (Reduction.honestTranscriptDist init impl
        (reduction mapStmt mapWit) stmtIn witIn) =
      evalDist (pure default : OptionT ProbComp (FullTranscript !p[])) := by
  apply evalDist_ext
  intro transcript
  classical
  unfold Reduction.honestTranscriptDist
  simp only [Reduction.run, Verifier.run, reduction, prover, Prover.run, verifier,
    Prover.runToRound_zero_of_prover_first, Fin.last, Fin.zero_eta, id_eq,
    QueryImpl.addLift_def, combineMap, OptionT.run_bind, OptionT.run_monadLift,
    monadLift_eq_self, simulateQ_bind, simulateQ_map, ← liftComp_eq_liftM,
    OracleComp.liftComp_bind, OracleComp.liftComp_map,
    QueryImpl.simulateQ_add_liftComp_left, QueryImpl.liftTarget_self,
    simulateQ_addLift_liftM_oracleComp_optionT_run_empty, Option.elimM, Option.elim,
    Option.getM, StateT.run'_eq, StateT.run_bind, StateT.run_map, liftM_map,
    OptionT.run_map, bind_pure_comp, map_bind, bind_assoc, map_pure, pure_bind,
    bind_map_left, Functor.map_map]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  by_cases htr : transcript = default
  · subst transcript
    rw [show
      Pr[= some default | (pure default : OptionT ProbComp (FullTranscript !p[])).run] = 1 by
        simp [OptionT.run_pure]]
    apply probOutput_eq_one_of_support_subset_singleton
    · exact HasEvalPMF.probFailure_eq_zero _
    · intro y hy
      simp only [OptionT.run_mk, Option.map_some, support_bind, Set.mem_iUnion, exists_prop,
        support_map, Set.mem_image] at hy
      aesop
  · rw [show
      Pr[= some transcript | (pure default : OptionT ProbComp (FullTranscript !p[])).run] = 0 by
        simp [OptionT.run_pure, probOutput_pure, htr]]
    apply probOutput_eq_zero_of_not_mem_support
    intro hy
    simp only [OptionT.run_mk, Option.map_some, support_bind, Set.mem_iUnion, exists_prop,
      support_map, Set.mem_image] at hy
    rcases hy with ⟨_, _, _, _, _, _, _, _, hEq⟩
    exact htr (Option.some.inj hEq).symm

/-- A no-interaction reduction is perfectly HVZK for any input relation: it has no messages or
challenges, so the identity empty-transcript simulator matches every honest transcript
distribution. -/
theorem reduction_perfectHVZK (relIn : Set (StmtIn × WitIn)) :
    Reduction.perfectHVZK init impl relIn
      (reduction mapStmt mapWit) Reduction.idTranscriptSimulator := by
  intro stmtIn witIn _
  exact (honestTranscriptDist_reduction_evalDist (mapStmt := mapStmt)
    (mapWit := mapWit) stmtIn witIn).symm

/-- Perfect HVZK implies statistical HVZK for a no-interaction reduction at every error budget. -/
theorem reduction_statisticalHVZK (relIn : Set (StmtIn × WitIn)) (ε : NNReal) :
    Reduction.statisticalHVZK init impl relIn
      (reduction mapStmt mapWit) Reduction.idTranscriptSimulator ε :=
  (reduction_perfectHVZK (mapStmt := mapStmt) (mapWit := mapWit)
    (init := init) (impl := impl) relIn).statisticalHVZK ε

/-- A no-interaction reduction has an explicit perfect-HVZK simulator for any input relation. -/
theorem reduction_isHVZK (relIn : Set (StmtIn × WitIn)) :
    Reduction.isHVZK init impl relIn (reduction mapStmt mapWit) :=
  ⟨Reduction.idTranscriptSimulator, reduction_perfectHVZK (mapStmt := mapStmt)
    (mapWit := mapWit) (init := init) (impl := impl) relIn⟩

/-- A no-interaction reduction has statistical HVZK for any input relation and error budget. -/
theorem reduction_isStatHVZK (relIn : Set (StmtIn × WitIn)) (ε : NNReal) :
    Reduction.isStatHVZK init impl relIn (reduction mapStmt mapWit) ε :=
  (reduction_isHVZK (mapStmt := mapStmt) (mapWit := mapWit)
    (init := init) (impl := impl) relIn).isStatHVZK ε

#print axioms NoInteraction.honestTranscriptDist_reduction_evalDist
#print axioms NoInteraction.reduction_perfectHVZK
#print axioms NoInteraction.reduction_statisticalHVZK
#print axioms NoInteraction.reduction_isHVZK
#print axioms NoInteraction.reduction_isStatHVZK

end Reduction

section OracleReduction



end OracleReduction

end NoInteraction
