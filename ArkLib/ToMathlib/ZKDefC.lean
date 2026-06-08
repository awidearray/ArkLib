/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
  # Migrated ZK Instance Scratch

  The Brick C zero-round identity HVZK instance has been promoted to
  `ArkLib.OracleReduction.Security.ZeroKnowledge`. This file remains as a compatibility re-export
  for existing scratch imports.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  [∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

/-- The honest transcript distribution of an oracle reduction, interpreted via `toReduction`. -/
def honestTranscriptDist
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn) :
    OptionT ProbComp (FullTranscript pSpec) :=
  Reduction.honestTranscriptDist init impl oracleReduction.toReduction (stmtIn, oStmtIn) witIn

/-- A simulator for an oracle reduction receives the bundled public statement, but not the private
  witness. -/
abbrev TranscriptSimulator :=
  Reduction.TranscriptSimulator oSpec (StmtIn × ∀ i, OStmtIn i) pSpec

/-- Perfect honest-verifier zero-knowledge for oracle reductions. -/
def perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (sim : TranscriptSimulator (oSpec := oSpec) (StmtIn := StmtIn) (OStmtIn := OStmtIn)
      (pSpec := pSpec)) :
    Prop :=
  Reduction.perfectHVZK init impl rel oracleReduction.toReduction sim

/-- Statistical honest-verifier zero-knowledge for oracle reductions with error `ε`. -/
def statisticalHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (sim : TranscriptSimulator (oSpec := oSpec) (StmtIn := StmtIn) (OStmtIn := OStmtIn)
      (pSpec := pSpec))
    (ε : ℝ≥0) : Prop :=
  Reduction.statisticalHVZK init impl rel oracleReduction.toReduction sim ε

/-- An oracle reduction is honest-verifier zero-knowledge if some simulator achieves perfect
  transcript-level HVZK for the bundled public statement. -/
def isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
    Prop :=
  ∃ sim : TranscriptSimulator (oSpec := oSpec) (StmtIn := StmtIn) (OStmtIn := OStmtIn)
      (pSpec := pSpec),
    perfectHVZK init impl rel oracleReduction sim

/-- Alias for the issue-facing terminology. -/
abbrev honestVerifierZeroKnowledge
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
    Prop :=
  isHVZK init impl rel oracleReduction

section Identity

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type}
  [∀ i, OracleInterface (OStatement i)] {Witness : Type}

/-- The simulator for the zero-round identity oracle reduction. -/
abbrev idTranscriptSimulator :
    TranscriptSimulator (oSpec := oSpec) (StmtIn := Statement) (OStmtIn := OStatement)
      (pSpec := !p[]) :=
  Reduction.idTranscriptSimulator

/-- The zero-round identity oracle reduction satisfies perfect honest-verifier zero-knowledge for
  any relation over bundled public statements and witnesses. -/
theorem id_perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((Statement × ∀ i, OStatement i) × Witness)) :
    perfectHVZK init impl rel
      (OracleReduction.id :
        OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[])
      idTranscriptSimulator := by
  unfold perfectHVZK
  simp only [OracleReduction.id_toReduction]
  exact Reduction.id_perfectHVZK init impl rel

/-- The zero-round identity oracle reduction is honest-verifier zero-knowledge for any relation
  over bundled public statements and witnesses. -/
theorem id_isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((Statement × ∀ i, OStatement i) × Witness)) :
    isHVZK init impl rel
      (OracleReduction.id :
        OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[]) :=
  ⟨idTranscriptSimulator, id_perfectHVZK init impl rel⟩

end Identity

end OracleReduction
