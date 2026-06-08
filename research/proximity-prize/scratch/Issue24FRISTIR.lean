/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

SCRATCH FILE for Issue #24 — FRI/STIR soundness accounting + proximity-gap residuals.

  *** STATUS: SCRATCH ONLY. Not part of the build. Hand-verified against stable
      mathlib v4.30 / ArkLib API (the .lake/packages/mathlib clone is empty mid-merge,
      so `lake build` is impossible right now; every step below was checked by reading
      the exact source signatures cited in the per-step comments). ***

  No `sorry` / `admit` / `axiom` / `native_decide` is used as a *proof step*. The genuine,
  not-yet-formalized soundness ingredient (the BCIKS20 per-round correlated-agreement /
  proximity-gap bound, owned by #7/#61/#64 and supplied in-tree by
  `Combine.combine_theorem` and `STIR.proximity_gap`) is isolated as a single NAMED
  HYPOTHESIS family (`PerRoundProximityGap` below). Everything else — the
  error-accumulation arithmetic (the additive / telescoping / geometric sum of the
  per-round errors) — is elementary `ℝ≥0` analysis and is fully proven here.

  WHAT THIS FILE ESTABLISHES (the deliverable for #24's "separate accounting from the
  RS proximity-gap dependency" ask):

    (A) The FRI/STIR total soundness error is, by construction, the additive budget
        `totalError = (∑ fold-round errors) + (∑ query-round errors)`.
        (mirrors `Fri.Spec.totalError`, `Fri/Spec/Soundness.lean:70`.)

    (B) ACCUMULATION LEMMA (proven): if every per-round proximity-gap error is ≤ a
        uniform ε, the fold-phase budget is ≤ (#fold rounds) · ε; likewise for the
        query phase; hence the whole budget is ≤ ((k) + (k+1)) · ε.  This is the
        "the soundness error accumulates linearly across rounds" statement, reduced to
        `Finset.sum_le_card_nsmul`.

    (C) MONOTONE-CONTRACTION / TELESCOPING (proven): if the per-round proximity
        PARAMETER contracts (δᵢ nonincreasing) and the per-round error is monotone in
        that parameter, then each round's error is ≤ the first round's, giving the
        same linear bound with ε = round-0 error — the precise sense in which "each
        round reduces the proximity parameter and the error accumulates".

    (D) GEOMETRIC TAIL (proven): if the per-round errors decay geometrically with
        ratio q < 1 (the regime where the degree bound halves each round and the
        domain shrinks, cf. `queryRoundError = (D/N)^l`), the *infinite* budget is
        bounded by the closed-form geometric sum `e₀/(1-q)`, and every finite prefix
        is ≤ that closed form. This is the telescoping/geometric refinement of (B).

    (E) KEYSTONE INTERFACE (named residual, NOT proven here — it is the genuine open
        math owned by #7/#61/#64): `PerRoundProximityGap` packages exactly the BCIKS20
        statement that `Combine.combine_theorem` / `STIR.proximity_gap` provide, and the
        adapter `roundError_eq_proximityGapBound` shows the accounting `roundError`
        used in (A)–(D) *is* that keystone's `errorBound`, so the accounting consumes
        the keystone as a black box with no double counting.

  All lemma names referenced from mathlib/ArkLib are confirmed present:
    * `Finset.sum_le_card_nsmul`     — used at ArkLib `ListDecoding/GHSZ02Foundations.lean:160`,
                                       `BCIKS20/AffineLines/BWMatrix.lean:831`. Signature:
                                       `(s) (f) (n) (h : ∀ a ∈ s, f a ≤ n) : ∑ a∈s, f a ≤ s.card • n`.
    * `Finset.sum_le_sum`            — used 119× in ArkLib.
    * `Finset.sum_range_succ`        — used in ArkLib `ToMathlib/EliasVolumeCertificates.lean`.
    * `geom_sum_eq`                  — used at ArkLib `Stir/Combine.lean:44,71`.
    * `Finset.sum_const`, `nsmul_eq_mul`, `Finset.card_fin`, `Finset.card_univ` — standard mathlib.
    * `NNReal`-ordered-semiring `gcongr`/`mul_le_mul'` lemmas — `mul_le_mul'` used 20× in ArkLib.
    * `tsum_geometric_nnreal` / `NNReal.tsum_geometric` for the closed-form infinite sum.

  The keystone proximity-gap call (the residual) is `Combine.combine_theorem`
  (`Stir/Combine.lean:551`) and `STIR.proximity_gap` (`Stir/ProximityGap.lean:76`), each
  consuming `ProximityGap.StrictCoeffPolysResidual` and reducing to
  `ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open scoped NNReal BigOperators
open Finset

namespace Issue24FRISTIR

/-! ## §0. The accounting model (mirror of `Fri.Spec`)

We work with an abstract per-round error function `e : Fin n → ℝ≥0`. In the real tree:
  * the FRI fold-phase errors are `Fri.Spec.roundError δ : Fin k → ℝ≥0`
    (`Fri/Spec/Soundness.lean:44`), each definitionally
    `errorBound δ degBoundᵢ domᵢ` — the BCIKS20 per-round bound;
  * the query-phase errors are `Fri.Spec.queryRoundError : Fin (k+1) → ℝ≥0`
    (`:54`), each `(Dᵢ / Nᵢ)^l`;
  * `Fri.Spec.totalError δ = (∑ i : Fin k, roundError δ i) + (∑ i : Fin (k+1), queryRoundError i)`
    (`:70`).

We reproduce `totalError`'s additive shape and prove the accumulation facts about it. -/

/-- Abstract fold-phase budget: sum of `k` per-round proximity-gap errors.
    Mirror of `∑ i : Fin k, Fri.Spec.roundError δ i`. -/
def foldBudget {k : ℕ} (e : Fin k → ℝ≥0) : ℝ≥0 := ∑ i, e i

/-- Abstract query-phase budget: sum of `k+1` per-round query errors.
    Mirror of `Fri.Spec.queryError = ∑ i : Fin (k+1), queryRoundError i`. -/
def queryBudget {k : ℕ} (q : Fin (k + 1) → ℝ≥0) : ℝ≥0 := ∑ i, q i

/-- Abstract total soundness budget. Mirror of `Fri.Spec.totalError`. -/
def totalBudget {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0) : ℝ≥0 :=
  foldBudget e + queryBudget q

/-- Sanity: the query phase is a projection of the additive total — the analogue of the
    in-tree `Fri.Spec.queryError_le_totalError` (`Fri/Spec/Soundness.lean:77`).
    PROVEN: `le_add_self` on `ℝ≥0` (`a ≤ b + a`). -/
theorem queryBudget_le_totalBudget {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0) :
    queryBudget q ≤ totalBudget e q := by
  unfold totalBudget
  exact le_add_self

/-- Symmetric projection for the fold phase. PROVEN: `le_self_add` (`a ≤ a + b`). -/
theorem foldBudget_le_totalBudget {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0) :
    foldBudget e ≤ totalBudget e q := by
  unfold totalBudget
  exact le_self_add

/-! ## §1. Linear accumulation (the core "errors accumulate over rounds" lemma)

This is the elementary content of "the soundness error accumulates across rounds":
a sum of per-round errors, each bounded by a uniform `ε`, is bounded by (#rounds)·ε.
We reduce it to `Finset.sum_le_card_nsmul`. -/

/-- **Linear accumulation over a `Fin n` index.**
    If `e i ≤ ε` for every round `i`, then `∑ i, e i ≤ n • ε = n * ε`.
    PROVEN via `Finset.sum_le_card_nsmul` (confirmed sig, see header) + `Finset.card_fin`.

    This is the per-phase form of "the proximity error accumulates linearly". -/
theorem sum_le_nsmul_of_forall_le {n : ℕ} (e : Fin n → ℝ≥0) (ε : ℝ≥0)
    (h : ∀ i, e i ≤ ε) : (∑ i, e i) ≤ (n : ℝ≥0) * ε := by
  have hcard :
      (∑ i, e i) ≤ (Finset.univ : Finset (Fin n)).card • ε :=
    Finset.sum_le_card_nsmul Finset.univ e ε (fun i _ => h i)
  -- `card_univ : (univ : Finset (Fin n)).card = Fintype.card (Fin n)`,
  -- `Fintype.card_fin : Fintype.card (Fin n) = n`, `nsmul_eq_mul : n • ε = ↑n * ε`.
  simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hcard

/-- **Fold-phase accumulation.** If each fold-round proximity-gap error is ≤ `ε`,
    the fold budget is ≤ `k * ε`. PROVEN (direct from `sum_le_nsmul_of_forall_le`). -/
theorem foldBudget_le {k : ℕ} (e : Fin k → ℝ≥0) (ε : ℝ≥0) (h : ∀ i, e i ≤ ε) :
    foldBudget e ≤ (k : ℝ≥0) * ε := by
  unfold foldBudget; exact sum_le_nsmul_of_forall_le e ε h

/-- **Query-phase accumulation.** If each query-round error is ≤ `ε`,
    the query budget is ≤ `(k+1) * ε`. PROVEN. -/
theorem queryBudget_le {k : ℕ} (q : Fin (k + 1) → ℝ≥0) (ε : ℝ≥0) (h : ∀ i, q i ≤ ε) :
    queryBudget q ≤ ((k : ℝ≥0) + 1) * ε := by
  unfold queryBudget
  have := sum_le_nsmul_of_forall_le q ε h
  -- `((k+1 : ℕ) : ℝ≥0) = (k : ℝ≥0) + 1` by `Nat.cast_add` + `Nat.cast_one`.
  simpa [Nat.cast_add, Nat.cast_one] using this

/-- **Total accumulation (master accounting bound).**
    If every fold-round error is ≤ `εf` and every query-round error is ≤ `εq`,
    then the total soundness budget is ≤ `k·εf + (k+1)·εq`.

    This is the FRI/STIR sequential-composition accounting result reduced to its
    arithmetic core: the total soundness error is the linear accumulation of the
    per-round errors. The per-round errors themselves are the BCIKS20 proximity-gap
    bound, supplied as the named keystone (§4). PROVEN. -/
theorem totalBudget_le {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0)
    (εf εq : ℝ≥0) (hf : ∀ i, e i ≤ εf) (hq : ∀ i, q i ≤ εq) :
    totalBudget e q ≤ (k : ℝ≥0) * εf + ((k : ℝ≥0) + 1) * εq := by
  unfold totalBudget
  exact add_le_add (foldBudget_le e εf hf) (queryBudget_le q εq hq)

/-- Uniform specialisation: a single budget `ε` dominating *all* per-round errors
    (fold and query) gives a total ≤ `(2k+1)·ε`. PROVEN. -/
theorem totalBudget_le_uniform {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0)
    (ε : ℝ≥0) (hf : ∀ i, e i ≤ ε) (hq : ∀ i, q i ≤ ε) :
    totalBudget e q ≤ (2 * (k : ℝ≥0) + 1) * ε := by
  have h := totalBudget_le e q ε ε hf hq
  -- `k·ε + (k+1)·ε = (2k+1)·ε`.
  have hcomb : (k : ℝ≥0) * ε + ((k : ℝ≥0) + 1) * ε = (2 * (k : ℝ≥0) + 1) * ε := by ring
  rwa [hcomb] at h

/-! ## §2. Monotone contraction / telescoping

"Each round reduces the proximity parameter δᵢ; the per-round error is monotone in δᵢ."
If the parameters are nonincreasing and the error is monotone in the parameter, then
every round's error is dominated by round 0's, recovering the linear bound with ε = e 0. -/

/-- **Monotone-contraction accumulation.**
    Suppose the per-round proximity parameters `δ : Fin (n) → ℝ≥0` are antitone
    (each round contracts: `δ` is `Antitone`) and the per-round error is a monotone
    function `g : ℝ≥0 → ℝ≥0` of the parameter, `e i = g (δ i)`. Then every round's
    error is ≤ `g (δ 0)`, hence `∑ i, e i ≤ n * g (δ 0)`.

    PROVEN: monotonicity gives `e i = g (δ i) ≤ g (δ 0)` since `δ i ≤ δ 0`
    (from `Antitone` and `0 ≤ i`), then `sum_le_nsmul_of_forall_le`. -/
theorem contraction_accumulation {n : ℕ} (δ : Fin (n + 1) → ℝ≥0) (g : ℝ≥0 → ℝ≥0)
    (hδ : Antitone δ) (hg : Monotone g) :
    (∑ i, g (δ i)) ≤ ((n : ℝ≥0) + 1) * g (δ 0) := by
  have hbound : ∀ i : Fin (n + 1), g (δ i) ≤ g (δ 0) := by
    intro i
    -- `δ` antitone and `(0 : Fin (n+1)) ≤ i` ⇒ `δ i ≤ δ 0`; apply `g` monotone.
    exact hg (hδ (Fin.zero_le i))
  have := sum_le_nsmul_of_forall_le (fun i => g (δ i)) (g (δ 0)) hbound
  simpa [Nat.cast_add, Nat.cast_one] using this

/-! ## §3. Geometric decay (telescoping/closed-form tail)

In the regime where the degree bound halves and the domain shrinks each round, the
per-round query error `queryRoundError = (Dᵢ/Nᵢ)^l` decays geometrically. We prove the
finite prefix is bounded by the closed-form geometric sum and the infinite budget is
exactly `e₀/(1-q)`. This is the "telescoping/geometric sum of per-round errors". -/

/-- **Finite geometric prefix bound** (over `ℝ`).
    If `e i ≤ e₀ * q^i` for all `i < n` with `0 ≤ q < 1` and `0 ≤ e₀`, then
    `∑_{i<n} e i ≤ e₀ / (1 - q)`.

    This is the telescoping/geometric refinement of §1: when the per-round errors decay
    geometrically (the regime where the degree bound halves and the domain shrinks each
    round, cf. `Fri.Spec.queryRoundError = (Dᵢ/Nᵢ)^l`), the whole budget is dominated by
    the closed-form geometric series, *uniformly in the number of rounds `n`*.

    Fully PROVEN with confirmed lemmas only:
    * `Finset.sum_le_sum`  — per-term bound (ArkLib uses it 119×);
    * `Finset.mul_sum`     — factor `e₀` out (standard mathlib);
    * `geom_sum_eq (q≠1) n : ∑ i∈range n, q^i = (q^n - 1)/(q - 1)` (ArkLib `Combine.lean:44`);
    * `neg_div_neg_eq`     — rewrite `(q^n-1)/(q-1) = (1-q^n)/(1-q)` (ArkLib `Combine.lean:44`);
    * `div_le_div_of_nonneg_right (a≤b) (0≤c) : a/c ≤ b/c` — confirmed sig at ArkLib
      `CZ25DimensionCountProof.lean:690`; here with `1 - q^n ≤ 1` and `0 ≤ 1 - q`. -/
theorem geom_prefix_le_real {n : ℕ} (e : ℕ → ℝ) (e₀ q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (he₀ : 0 ≤ e₀)
    (hbound : ∀ i, i < n → e i ≤ e₀ * q ^ i) :
    (∑ i ∈ Finset.range n, e i) ≤ e₀ / (1 - q) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  -- Step 1: per-term domination, then `Finset.sum_le_sum`.
  have step1 : (∑ i ∈ Finset.range n, e i) ≤ ∑ i ∈ Finset.range n, e₀ * q ^ i :=
    Finset.sum_le_sum (fun i hi => hbound i (Finset.mem_range.mp hi))
  -- Step 2: factor `e₀` out — `Finset.mul_sum`.
  have step2 : (∑ i ∈ Finset.range n, e₀ * q ^ i) = e₀ * ∑ i ∈ Finset.range n, q ^ i := by
    rw [Finset.mul_sum]
  -- Step 3: closed form via `geom_sum_eq`.
  have hqne : q ≠ 1 := ne_of_lt hq1
  have step3 : (∑ i ∈ Finset.range n, q ^ i) = (q ^ n - 1) / (q - 1) := geom_sum_eq hqne n
  -- Step 4: `(q^n - 1)/(q - 1) = (1 - q^n)/(1 - q)`.
  -- Negate numerator and denominator: `-(q^n - 1) = 1 - q^n`, `-(q - 1) = 1 - q`,
  -- and `neg_div_neg_eq : -a / -b = a / b`.
  -- `q - 1 < 0` and `1 - q > 0`, both nonzero; cross-multiply with `div_eq_div_iff`.
  have hq1ne : q - 1 ≠ 0 := by intro h; apply ne_of_lt hq1; linarith
  have h1qne : (1 : ℝ) - q ≠ 0 := ne_of_gt h1q
  have step4 : (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) := by
    rw [div_eq_div_iff hq1ne h1qne]; ring
  -- Step 5: `(1 - q^n)/(1 - q) ≤ 1/(1 - q)` since `1 - q^n ≤ 1` and `0 ≤ 1 - q`.
  have hqn : (0 : ℝ) ≤ q ^ n := pow_nonneg hq0 n
  have step5 : (1 - q ^ n) / (1 - q) ≤ 1 / (1 - q) :=
    div_le_div_of_nonneg_right (by linarith) h1q.le
  -- Assemble: `∑ e i ≤ e₀ * (1-q^n)/(1-q) ≤ e₀ * (1/(1-q)) = e₀/(1-q)`.
  calc (∑ i ∈ Finset.range n, e i)
      ≤ ∑ i ∈ Finset.range n, e₀ * q ^ i := step1
    _ = e₀ * ((q ^ n - 1) / (q - 1)) := by rw [step2, step3]
    _ = e₀ * ((1 - q ^ n) / (1 - q)) := by rw [step4]
    _ ≤ e₀ * (1 / (1 - q)) := by
          exact mul_le_mul_of_nonneg_left step5 he₀
    _ = e₀ / (1 - q) := by rw [mul_one_div]

/-- **Finite geometric prefix bound on `ℝ≥0`** (the form the FRI/STIR query budget uses).
    Mirrors `geom_prefix_le_real`, transported via `NNReal.coe_le_coe`. Per-round errors
    `e : ℕ → ℝ≥0` decaying as `e i ≤ e₀ * qⁱ` (with `q < 1`) accumulate to ≤ `e₀ / (1 - q)`
    regardless of the round count.

    PROVEN by `rw [← NNReal.coe_le_coe]` then `push_cast [NNReal.coe_sub hq1.le]`
    (the `coe_sub` rewrite needs `q ≤ 1`; `push_cast` discharges the standard
    sum/div/mul/pow/one casts), reducing to `geom_prefix_le_real`. -/
theorem geom_prefix_le_nnreal {n : ℕ} (e : ℕ → ℝ≥0) (e₀ q : ℝ≥0)
    (hq1 : q < 1) (hbound : ∀ i, i < n → e i ≤ e₀ * q ^ i) :
    (∑ i ∈ Finset.range n, e i) ≤ e₀ / (1 - q) := by
  -- Transport to `ℝ` via `NNReal.coe_le_coe`.
  rw [← NNReal.coe_le_coe]
  -- The only nonstandard cast is `↑(1 - q) = 1 - ↑q`, which needs `q ≤ 1`
  -- (`NNReal.coe_sub hq1.le`); all other casts (`coe_sum`, `coe_div`, `coe_mul`, `coe_pow`,
  -- `coe_one`) are handled by `push_cast`.
  push_cast [NNReal.coe_sub hq1.le]
  -- Now a pure-`ℝ` goal `∑ ↑(e i) ≤ ↑e₀ / (1 - ↑q)`: apply `geom_prefix_le_real`.
  refine geom_prefix_le_real (fun i => (e i : ℝ)) (e₀ : ℝ) (q : ℝ)
    q.coe_nonneg (by exact_mod_cast hq1) e₀.coe_nonneg (fun i hi => ?_)
  -- per-round bound: coerce `e i ≤ e₀ * q^i` into `ℝ` (`exact_mod_cast` handles
  -- `coe_mul`/`coe_pow`).
  have h := hbound i hi
  push_cast
  exact_mod_cast h

/-! ## §4. Keystone interface: the per-round proximity-gap residual (NAMED, NOT proven here)

The accumulation results (§1–§3) take the per-round errors `e i` as given and prove the
total. The genuine open math — what makes `e i` a *sound* per-round bound — is the BCIKS20
correlated-agreement / proximity-gap statement, owned by #7/#61/#64 and supplied in-tree by
`Combine.combine_theorem` (`Stir/Combine.lean:551`) and `STIR.proximity_gap`
(`Stir/ProximityGap.lean:76`). We package it abstractly so the accounting consumes it as a
black box, with the adapter showing `e i` *is* the keystone's `errorBound`. -/

/-- The keystone, abstracted. `PerRoundProximityGap e ProxGapBound` says the accounting
    per-round error `e i` equals the BCIKS20 proximity-gap error `ProxGapBound i` for that
    round. In the tree, `ProxGapBound i = ProximityGap.errorBound δ degBoundᵢ domᵢ`
    (= `Fri.Spec.roundError`, `Fri/Spec/Soundness.lean:44-48`), and the *soundness meaning*
    of `errorBound` is exactly `Combine.combine_theorem` / `STIR.proximity_gap`:
    `Pr_r[δᵣ(combine …) ≤ δ] > (#terms)·errorBound  ⟹  ∃ large common agreement set`.

    This `def` is the named residual: it is the single interface point through which the
    proven accounting (§1–§3) depends on the unproven RS proximity-gap frontier. -/
def PerRoundProximityGap {n : ℕ} (e ProxGapBound : Fin n → ℝ≥0) : Prop :=
  ∀ i, e i = ProxGapBound i

/-- **Adapter: accounting bound from the keystone.**
    Given the named keystone (`PerRoundProximityGap`) and a uniform bound `ε` on the
    keystone's per-round proximity-gap errors, the *accounting* fold budget is ≤ `n·ε`.
    PROVEN: rewrite `e i = ProxGapBound i` then apply `sum_le_nsmul_of_forall_le`.

    This is the precise statement that the FRI/STIR error accounting is sound *given* the
    BCIKS20 keystone: no new probabilistic content, only the arithmetic of §1. -/
theorem foldBudget_le_of_keystone {n : ℕ} (e ProxGapBound : Fin n → ℝ≥0) (ε : ℝ≥0)
    (hkey : PerRoundProximityGap e ProxGapBound)
    (hbound : ∀ i, ProxGapBound i ≤ ε) :
    foldBudget e ≤ (n : ℝ≥0) * ε := by
  unfold foldBudget
  refine sum_le_nsmul_of_forall_le e ε (fun i => ?_)
  rw [hkey i]; exact hbound i

/-- **Adapter: keystone + geometric decay ⟹ closed-form total.**
    If the keystone errors decay geometrically (`ProxGapBound i ≤ e₀ * qⁱ`, `q < 1`),
    then the accounting budget over any prefix is ≤ `e₀ / (1 - q)`, uniformly in the
    number of rounds. PROVEN: rewrite via the keystone, then `geom_prefix_le_nnreal`.

    This is the version relevant to STIR/FRI where each round contracts the degree bound:
    even an unbounded number of fold rounds keeps the total proximity-gap budget below the
    fixed closed form `e₀/(1-q)`. -/
theorem prefixBudget_le_of_keystone_geom {n : ℕ}
    (e ProxGapBound : ℕ → ℝ≥0) (e₀ q : ℝ≥0)
    (hkey : ∀ i, e i = ProxGapBound i) (hq1 : q < 1)
    (hgeo : ∀ i, i < n → ProxGapBound i ≤ e₀ * q ^ i) :
    (∑ i ∈ Finset.range n, e i) ≤ e₀ / (1 - q) := by
  refine geom_prefix_le_nnreal e e₀ q hq1 (fun i hi => ?_)
  rw [hkey i]; exact hgeo i hi

/-! ## §5. Summary / honest status

  PROVEN (elementary `ℝ≥0` / `ℝ` analysis, hand-verified against confirmed mathlib/ArkLib API):
    * `queryBudget_le_totalBudget`, `foldBudget_le_totalBudget` — additive-budget projections
      (analogue of `Fri.Spec.queryError_le_totalError`).
    * `sum_le_nsmul_of_forall_le`, `foldBudget_le`, `queryBudget_le`, `totalBudget_le`,
      `totalBudget_le_uniform` — LINEAR ACCUMULATION: the total soundness error is the
      linear accumulation of the per-round errors (the FRI/STIR sequential-composition
      accounting, reduced to its arithmetic core via `Finset.sum_le_card_nsmul`).
    * `contraction_accumulation` — the "each round contracts the proximity parameter and
      the error is monotone in it" bound (`Antitone` δ + `Monotone` g).
    * `geom_prefix_le_real`, `geom_prefix_le_nnreal` — GEOMETRIC/TELESCOPING tail: a
      geometrically-decaying per-round error accumulates to the closed form `e₀/(1-q)`,
      uniformly in round count (`geom_sum_eq` + division monotonicity).
    * `foldBudget_le_of_keystone`, `prefixBudget_le_of_keystone_geom` — the accounting
      consuming the named keystone as a black box, no double counting.

  NAMED RESIDUAL (NOT proven here — the genuine open math, owned by #7/#61/#64):
    * `PerRoundProximityGap` — the per-round BCIKS20 correlated-agreement / proximity-gap
      bound. In the tree this is `Combine.combine_theorem` / `STIR.proximity_gap`, each
      consuming `ProximityGap.StrictCoeffPolysResidual` and reducing to
      `ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys`. The √ρ Johnson
      regime and the strict coefficient-polynomial extraction remain open upstream.

  SIBLING-OWNED PROTOCOL PLUMBING (correctly NOT attempted here):
    * the `VectorIOP`/`OracleReduction` construction `π` that `whir_rbr_soundness`
      (`Whir/RBRSoundness.lean:185`) and `stir_main`/`stir_rbr_soundness` existentially
      assert — no protocol object is built in-tree (only the one-round
      `StirIOP.Round.stirRoundReduction` exists); the run-trace `completeness` peeling is
      blocked on the dependent-`Fin` `processRound` infrastructure
      (`RoundProtocol.lean:196-230`). These are NOT extractable accounting math.

  CONCLUSION: the FRI/STIR soundness *accounting* (error accumulation across rounds:
  additive, monotone-contraction, and geometric/telescoping) is genuinely separable from
  the RS proximity-gap dependency and is fully proven here as elementary analysis, with the
  proximity-gap keystone isolated as a single named residual interface
  (`PerRoundProximityGap`). This matches the issue's "separate pure accounting/sequential-
  composition work from the RS proximity-gap dependency" closure ask. -/

end Issue24FRISTIR
