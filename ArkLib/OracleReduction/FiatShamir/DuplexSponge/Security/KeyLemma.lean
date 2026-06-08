/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.EvalDist.TVDist

/-!
# Key Lemma for Duplex-Sponge Fiat-Shamir Security (Lemma 5.1)

This module formalizes the core statistical indistinguishability result (Lemma 5.1 in
Chiesa-Orrù [CO25]) bridging the Duplex-Sponge Fiat-Shamir (DSFS) transformation and the basic
Fiat-Shamir transformation.

The key lemma asserts that the security games for basic Fiat-Shamir and duplex-sponge Fiat-Shamir
yield statistically indistinguishable distributions on their output transcripts (up to a small
simulation error $\eta^*$), provided that the malicious prover and query-answer traces are mapped
via the
appropriate trace and prover transformations.

From this result, preservation of both soundness and knowledge soundness under the DSFS
transformation follows directly.

## Formalization shape

The statistical-distance conclusion is stated faithfully via `SPMF.tvDist`:

- `duplexSpongeFiatShamirGameRemapped` runs `duplexSpongeFiatShamirGame` and pushes both query
  logs through the §5.5 `D2STrace` transform (`TraceTransform.d2sTrace`), landing both
  experiments on the same basic-FS output surface.
- `KeyLemmaStatement` is the per-prover conclusion of [CO25, Lemma 5.1]: there is a simulated
  basic-FS prover (CO25's `D2SAlgo`) whose game outputs are `ηStar`-close in total variation to
  the remapped DSFS game outputs, respecting the `θStar` challenge-query budget.
- `KeyLemmaResidual` is the named residual carrying the full quantified lemma. It is a genuine
  distribution bound and is **not** dischargeable by `trivial`; the simulation argument of
  CO25 §5.4–§5.7 is required to prove it.
- `duplexSpongeToFSGameStatDist` consumes the residual to expose the statement under its
  paper-facing name, threading the query bounds `(tₒ, tₕ, tₚ, tₚᵢ)` and the simulation error
  `ηStar` computed from the codec's decoding biases (`Codec.decodingBias`, CO25 Def. 4.1).
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]

section SecurityGames

variable
  -- All messages are serializable to vectors of units
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  -- All challenges are deserializable from vectors of units
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- First game for the key lemma: the basic Fiat-Shamir transform.

We run the malicious prover, then the verifier, then returns:
- the input statement (that the malicious prover chooses)
- the output statement (that the verifier returns)
- the messages / proof sent by the prover
- the query log of the prover
- the query log of the verifier -/
def basicFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (StmtIn × pSpec.Messages)) :
    OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
      (StmtIn × StmtOut × pSpec.Messages × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
        × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let ⟨⟨stmtIn, messages⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  let ⟨stmtOut, verifyQueryLog⟩ ← (simulateQ loggingOracle
    (V.fiatShamir.run stmtIn (fun i => match i with | ⟨0, _⟩ => messages))).run
  return ⟨stmtIn, ← stmtOut.getM, messages, proveQueryLog, verifyQueryLog⟩

/-- Second game for the key lemma: the duplex sponge Fiat-Shamir transform.

We run the malicious prover, then the verifier, then returns:
- the input statement (that the malicious prover chooses)
- the output statement (that the verifier returns)
- the messages / proof sent by the prover
- the query log of the prover
- the query log of the verifier -/
def duplexSpongeFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (StmtIn × StmtOut × pSpec.Messages
        × QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)
        × QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) := do
  let ⟨⟨stmtIn, messages⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle
      (V.duplexSpongeFiatShamir.run
        stmtIn (fun i => match i with | ⟨0, _⟩ => messages))).run
  return ⟨stmtIn, ← stmtOut.getM, messages, proveQueryLog, verifyQueryLog⟩

end SecurityGames

section KeyLemma

open scoped NNReal

variable [DecidableEq ι]

/-- `θStar` in the paper, which is just equal to `tₚ`, the bound for number of forward permutation
  queries made by the malicious prover -/
def θStar (_tₕ tₚ _tₚᵢ : ℕ) : ℕ := tₚ

/-!
`ηStar` in the paper, is the bound on the statistical distance between two experiments in Lemma 5.1
-/
noncomputable def ηStar (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ : ℕ) (L : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) : ℝ≥0 :=
  let tTotal : ℕ := (tₕ + tₚ + tₚᵢ)
  -- First term in Equation (5)
  -- Numerator: `7 * t ^ 2 + (28 * L + 25) * t + (14 * L + 1) * (L + 1)`
  -- Note: we rewrote the numerator to make it clear that the term is nonnegative (no subtraction)
  -- Original: `7 * t ^ 2 + 28 * (L + 1) * t + 14 * (L + 1) ^ 2 - 3 * t - 13 * (L + 1)`
  let firstTermNumerator : ℝ≥0 :=
    7 * tTotal ^2 + (28 * L + 25) * tTotal + (14 * L + 1) * (L + 1)
  let firstTermDenominator : ℝ≥0 := 2 * ((Fintype.card U) ^ (SpongeSize.C + 1))
  -- Second term in Equation (5)
  let secondTerm : ℝ≥0 := θStar tₕ tₚ tₚᵢ * (iSup εcodec)
  -- Third term in Equation (5)
  let thirdTerm : ℝ≥0 := ∑ i, εcodec i
  -- η⋆ = (7 t^2 + (28 L + 25) t + (14 L + 1) (L + 1)) / (2 · |Σ|^c) + θ⋆ · max ε + ∑ ε
  firstTermNumerator / firstTermDenominator + secondTerm + thirdTerm

section Statement

open DSTraceStorage

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U] [∀ i, Fintype (pSpec.Message i)]
  [oSpec.Fintype] [oSpec.Inhabited]

local instance : Inhabited U := ⟨0⟩

/-- The (slow) Fiat-Shamir challenge oracle has finite ranges: each oracle answer is a protocol
challenge, and challenges are `VCVCompatible`. Stated as a local instance because
`fsChallengeOracle` fixes its oracle-interface family explicitly, bypassing the generic
`[v]ₒ.Fintype` instance. -/
local instance : (fsChallengeOracle StmtIn pSpec).Fintype where
  fintype_B q := inferInstanceAs (Fintype (pSpec.Challenge q.1))

/-- The (slow) Fiat-Shamir challenge oracle has inhabited ranges (challenges are
`VCVCompatible`). -/
local instance : (fsChallengeOracle StmtIn pSpec).Inhabited where
  inhabited_B q := inferInstanceAs (Inhabited (pSpec.Challenge q.1))

/-- Flavor of a single query index of the DSFS adversary's oracle
`oSpec + duplexSpongeChallengeOracle StmtIn U`: either the shared ambient oracle `oSpec`, or one
of the three duplex-sponge query flavors `(h, p, p⁻¹)` of CO25 §5.4. Used to phrase the
per-flavor query budgets `(tₕ, tₚ, tₚᵢ)` of [CO25, Lemma 5.1]. -/
inductive DSQueryFlavor where
  /-- A query to the shared ambient oracle `oSpec`. -/
  | shared
  /-- A hash query `h(𝕩)` to the duplex-sponge start oracle. -/
  | hash
  /-- A forward permutation query `p(s_in)`. -/
  | perm
  /-- An inverse permutation query `p⁻¹(s_out)`. -/
  | permInv
  deriving DecidableEq

/-- Classify a query index of `oSpec + duplexSpongeChallengeOracle StmtIn U` by its
`DSQueryFlavor`. -/
def dsQueryFlavor :
    ι ⊕ (StmtIn ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U) → DSQueryFlavor
  | .inl _ => .shared
  | .inr (.inl _) => .hash
  | .inr (.inr (.inl _)) => .perm
  | .inr (.inr (.inr _)) => .permInv

/-- The duplex-sponge Fiat-Shamir game with its query logs remapped onto the basic-FS surface:
run `duplexSpongeFiatShamirGame`, then push both the prover and verifier query logs through the
§5.5 `D2STrace` transform (`TraceTransform.d2sTrace`).

The result lives directly at the `SPMF` level (rather than inside one oracle monad) because the
trace transform consumes auxiliary `𝒰(Σ)` sampling randomness from a separate `Unit →ₒ U` oracle;
composing the evaluation distributions is exactly CO25's "remapped experiment" (§5.5.2). -/
noncomputable def duplexSpongeFiatShamirGameRemapped
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let ⟨stmtIn, stmtOut, messages, proveQueryLog, verifyQueryLog⟩ ←
    𝒟[duplexSpongeFiatShamirGame (U := U) V P]
  let proveQueryLog' ←
    𝒟[TraceTransform.d2sTrace (T_H := T_H) (T_P := T_P) (δ := δ) (pSpec := pSpec)
      proveQueryLog]
  let verifyQueryLog' ←
    𝒟[TraceTransform.d2sTrace (T_H := T_H) (T_P := T_P) (δ := δ) (pSpec := pSpec)
      verifyQueryLog]
  return ⟨stmtIn, stmtOut, messages, proveQueryLog', verifyQueryLog'⟩

/-- The per-prover conclusion of [CO25, Lemma 5.1].

For a malicious DSFS prover `P`, there exists a simulated basic-FS prover (CO25's
`D2SAlgo^f(P)`, §5.4) that:
- respects the shared-oracle budgets `tₒ`,
- makes at most `θStar tₕ tₚ tₚᵢ` challenge queries, and
- induces a basic-FS game output distribution within total-variation distance
  `ηStar U tₕ tₚ tₚᵢ L codec.decodingBias` of the remapped DSFS game outputs.

`L` is the CO25 Eq. (5) bound on the number of absorbed rate-blocks per challenge derivation
(determined by the codec's message/challenge sizes and the sponge rate). -/
def KeyLemmaStatement
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₒ : ι → ℕ) (tₕ tₚ tₚᵢ L : ℕ) : Prop :=
  ∃ P' : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (StmtIn × pSpec.Messages),
    (∀ i : ι, IsQueryBoundP P' (fun j => j.getLeft? = some i) (tₒ i)) ∧
    IsQueryBoundP P' (fun j => j.isRight = true) (θStar tₕ tₚ tₚᵢ) ∧
    SPMF.tvDist 𝒟[basicFiatShamirGame V P']
        (duplexSpongeFiatShamirGameRemapped T_H T_P δ V P)
      ≤ (ηStar U tₕ tₚ tₚᵢ L codec.decodingBias : ℝ)

/-- Named residual carrying the full quantified content of [CO25, Lemma 5.1]: for every verifier
and every query-bounded malicious DSFS prover, the simulated basic-FS prover of
`KeyLemmaStatement` exists.

This is a genuine total-variation bound between the two game distributions; it can **not** be
discharged by `trivial`. Proving it requires the CO25 §5.4–§5.7 simulation argument
(`ProverTransform.d2sAlgo` correctness, the hybrid games `Hyb₁`–`Hyb₄`, and the bad-event
analysis giving `ηStar`). Downstream soundness/knowledge-soundness preservation should consume
this residual explicitly. -/
def KeyLemmaResidual
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (tₒ : ι → ℕ) (tₕ tₚ tₚᵢ L : ℕ) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)),
    (∀ i : ι, IsQueryBoundP P (fun j => j.getLeft? = some i) (tₒ i)) →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
    IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
    KeyLemmaStatement T_H T_P δ V P tₒ tₕ tₚ tₚᵢ L

/-- [CO25, Lemma 5.1]
The statistical distance between the outputs of the basic Fiat-Shamir game (with the simulated
prover) and the (trace-remapped) duplex-sponge Fiat-Shamir game is bounded by the simulation
error `ηStar`, assuming query bounds `(tₒ, tₕ, tₚ, tₚᵢ)` on the malicious prover.

The conclusion is the real statistical-distance statement `KeyLemmaStatement`; the simulation
argument itself is the named residual `KeyLemmaResidual`, so this lemma cannot be used to
discharge security trivially. -/
lemma duplexSpongeToFSGameStatDist
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₒ : ι → ℕ) (tₕ tₚ tₚᵢ L : ℕ)
    (hKeyLemma : KeyLemmaResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ tₒ tₕ tₚ tₚᵢ L)
    (hShared : ∀ i : ι,
      IsQueryBoundP maliciousProver (fun j => j.getLeft? = some i) (tₒ i))
    (hHash : IsQueryBoundP maliciousProver (fun j => dsQueryFlavor j = .hash) tₕ)
    (hPerm : IsQueryBoundP maliciousProver (fun j => dsQueryFlavor j = .perm) tₚ)
    (hPermInv : IsQueryBoundP maliciousProver (fun j => dsQueryFlavor j = .permInv) tₚᵢ) :
    KeyLemmaStatement T_H T_P δ V maliciousProver tₒ tₕ tₚ tₚᵢ L :=
  hKeyLemma V maliciousProver hShared hHash hPerm hPermInv

end Statement

end KeyLemma

end DuplexSpongeFS
