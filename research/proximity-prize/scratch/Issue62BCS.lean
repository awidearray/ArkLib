/-
Scratch / hand-verification file for ArkLib issue #62
(Complete the BCS compiler beyond statement-level scaffolding).

GOAL OF THIS FILE
-----------------
Issue #62 asks to complete the Ben-Sasson–Chiesa–Spooner (BCS) compiler: turn an
Interactive Oracle Reduction (IOR) into a concrete Interactive Reduction by
replacing oracle messages with cryptographic commitments + opening proofs, and to
prove completeness / soundness preservation under commitment binding/extractability.

Per the supervising instructions, this scratch file isolates the GENUINELY
EXTRACTABLE MATH from the (large) pure-construction remainder. After reading
`ArkLib/OracleReduction/BCS/Basic.lean` in full, the situation is:

  * The BCS-compiled protocol is, structurally,
        `Reduction.append interaction opening`
    (see `OracleReduction.BCSTransform`, line ~216 of BCS/Basic.lean), where
    `opening` is the sequential composition of the `m` per-message commitment
    opening proofs (`BCSOpeningPhase`, line ~106).

  * The intended soundness-preservation statement is therefore an ERROR-UNION
    BOUND: the compiled argument is sound with error
        ε_interaction  +  (Σ_{i} ε_open(i))
    i.e. the IOR/interaction-phase soundness error plus the sum of the per-message
    commitment-opening (binding) errors. This is exactly the "error-union bound"
    the supervisor flagged as the math content.

  * In the live codebase, the per-`append` step of this bound is the named
    residual `Verifier.appendSoundnessResidual` / `Verifier.append_soundness`
    (Composition/Sequential/Append.lean, line ~734): the additive error
    `soundnessError₁ + soundnessError₂` is the *statement*, but its proof is an
    UNPROVEN deep residual (malicious-prover seam decomposition + probabilistic
    union bound). So the probabilistic core is NOT yet available as a theorem;
    it is blocked on that residual (and the BCS file itself defers all of this to
    ArkLib#433, the OracleReduction rewrite).

WHAT IS GENUINELY PROVABLE HERE (and is below)
----------------------------------------------
The *accounting* layer of the union bound — the `ℝ≥0` arithmetic that the BCS
soundness composition reduces to once the per-step probabilistic bound is granted
as a hypothesis — is real, self-contained math. We prove it abstractly:

  (1) `bcsTotalError`: the total error of a BCS-compiled protocol as
      ε_interaction + Σ ε_open, and its basic algebra (additivity, the empty /
      single-message / cons cases, monotonicity).
  (2) `bcs_union_bound`: the abstract union-bound accounting — if a "bad event"
      probability is bounded by the interaction error, and each per-message
      opening failure by its own error, then the total is bounded by
      ε_interaction + Σ ε_open. This is the `ℝ≥0` skeleton of the soundness
      composition, stated and proved over an arbitrary `ℝ≥0`-valued probability
      functional so it is independent of the (unproven) probabilistic substrate.
  (3) `bcs_append_accounting`: specialization to the two-phase `append` shape
      (`m = 1`-flavoured, interaction + single opening), matching the additive
      error in `Verifier.append_soundness`.

These are the parts that are MATH, not construction. Everything else the issue
asks for (constructing the two phases from the oracle reduction + schemes,
threading the dependent query-log types, the probabilistic seam decomposition)
is construction/plumbing blocked on ArkLib#433 and the `appendSoundnessResidual`.

This file is intentionally self-contained (no ArkLib imports) so it can be
HAND-VERIFIED while the build environment is mid-reclone. The lemmas are stated
over `ℝ≥0` (NNReal) and `Finset.sum`, exactly the types ArkLib uses for
`soundnessError` (`ArkLib/OracleReduction/Security/Basic.lean`, `soundnessError : ℝ≥0`).

NO `sorry` / `admit` / `axiom` / `native_decide` is used.
-/

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped NNReal
open scoped BigOperators

namespace ArkLibScratch.Issue62

/-! ## 1. The BCS total error: ε_interaction + Σ ε_open

`m` is the number of committed oracle messages (the `pSpec.MessageIdx ≃ Fin m`
ordering in `BCSTransform`). `εInteraction` is the interaction-phase soundness
error; `εOpen i` is the soundness/binding error of the `i`-th per-message opening
proof. The total compiled error is their union-bound sum. -/

/-- The total soundness error of a BCS-compiled protocol with `m` committed
messages: the interaction-phase error plus the sum of the per-message opening
errors. This is the `ε_interaction + Σ ε_open(i)` accounting target. -/
def bcsTotalError {m : ℕ} (εInteraction : ℝ≥0) (εOpen : Fin m → ℝ≥0) : ℝ≥0 :=
  εInteraction + ∑ i, εOpen i

/-- With zero committed messages the opening phase is empty, so the BCS error is
just the interaction-phase error. (Empty opening schedule base case.) -/
@[simp] theorem bcsTotalError_zero (εInteraction : ℝ≥0) (εOpen : Fin 0 → ℝ≥0) :
    bcsTotalError εInteraction εOpen = εInteraction := by
  simp [bcsTotalError]

/-- The `cons` (one-more-message) recurrence for the BCS total error:
peeling off message `0` adds its opening error and recurses on the rest.
This is the inductive step matching `BCSOpeningSchedule.toOpeningStatements_cons`
in the source file. -/
theorem bcsTotalError_succ {m : ℕ} (εInteraction : ℝ≥0) (εOpen : Fin (m + 1) → ℝ≥0) :
    bcsTotalError εInteraction εOpen
      = εOpen 0 + bcsTotalError εInteraction (fun i => εOpen i.succ) := by
  unfold bcsTotalError
  rw [Fin.sum_univ_succ]
  ring

/-- Single committed message: the BCS error is the interaction error plus the one
opening error. This is the shape that matches `Reduction.append interaction
opening` with a single per-message opening, i.e. `Verifier.append_soundness`'s
additive error `soundnessError₁ + soundnessError₂`. -/
theorem bcsTotalError_one (εInteraction : ℝ≥0) (εOpen : Fin 1 → ℝ≥0) :
    bcsTotalError εInteraction εOpen = εInteraction + εOpen 0 := by
  simp [bcsTotalError, Fin.sum_univ_one]

/-- The BCS total error is monotone in the interaction error. -/
theorem bcsTotalError_mono_interaction {m : ℕ} {ε₁ ε₂ : ℝ≥0} (εOpen : Fin m → ℝ≥0)
    (h : ε₁ ≤ ε₂) : bcsTotalError ε₁ εOpen ≤ bcsTotalError ε₂ εOpen := by
  unfold bcsTotalError
  gcongr

/-- The BCS total error is monotone in the per-message opening errors (pointwise).
Monotonicity is exactly what is needed to relax binding errors upward, mirroring
`soundness.mono_error` in `Security/Basic.lean`. -/
theorem bcsTotalError_mono_open {m : ℕ} (εInteraction : ℝ≥0)
    {εOpen₁ εOpen₂ : Fin m → ℝ≥0} (h : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    bcsTotalError εInteraction εOpen₁ ≤ bcsTotalError εInteraction εOpen₂ := by
  unfold bcsTotalError
  gcongr with i
  exact h i

/-- Joint monotonicity in both the interaction error and the opening errors. -/
theorem bcsTotalError_mono {m : ℕ} {εInt₁ εInt₂ : ℝ≥0}
    {εOpen₁ εOpen₂ : Fin m → ℝ≥0}
    (hInt : εInt₁ ≤ εInt₂) (hOpen : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    bcsTotalError εInt₁ εOpen₁ ≤ bcsTotalError εInt₂ εOpen₂ :=
  le_trans (bcsTotalError_mono_open εInt₁ hOpen)
    (bcsTotalError_mono_interaction εOpen₂ hInt)

/-! ## 2. The abstract union-bound accounting

We model "probability of a bad event" abstractly as an `ℝ≥0`-valued functional
`P` on events, satisfying only the two facts a union bound needs:
  * monotonicity (`P` of a smaller event ≤ `P` of a bigger event), and
  * subadditivity over a `cons` (the union bound for two events).

We then show: if the interaction-phase failure event has `P ≤ εInteraction`, and
the `i`-th opening-failure event has `P ≤ εOpen i`, then the overall BCS failure
(modelled as the union of all these events) has `P ≤ bcsTotalError εInteraction
εOpen`. This is precisely the soundness-composition accounting, abstracted away
from the specific probability monad so it is provable today.

`E` is the (opaque) type of events; `union` is binary event union; `none` is the
empty (never-fires) event. -/

variable {E : Type*}

/-- The structure of a probability functional that admits a union bound:
a monotone, finitely-subadditive `ℝ≥0`-valued measure of "bad events". This is
the minimal interface that the ArkLib `Pr[·]`/`probEvent` functional satisfies
(`probEvent_mono` and finite union subadditivity), recorded abstractly so the
accounting below is provable without the probability monad. -/
structure UnionBoundPr (E : Type*) where
  /-- Probability of an event. -/
  pr : E → ℝ≥0
  /-- The empty event. -/
  empty : E
  /-- Binary union of events. -/
  union : E → E → E
  /-- The empty event never fires. -/
  pr_empty : pr empty = 0
  /-- Union bound for two events (finite subadditivity). -/
  pr_union_le : ∀ a b, pr (union a b) ≤ pr a + pr b

/-- Union of a finite family of events, folded over `Fin m`. -/
def UnionBoundPr.unionFin (μ : UnionBoundPr E) :
    ∀ {m : ℕ}, (Fin m → E) → E
  | 0, _ => μ.empty
  | _ + 1, f => μ.union (f 0) (μ.unionFin (fun i => f i.succ))

/-- Finite union bound: the probability of a union of `m` events is at most the
sum of their probabilities. This is the standard union bound, proved by induction
on `m` from binary subadditivity. It is the probabilistic core of the BCS
soundness accounting over the `m` per-message opening proofs. -/
theorem UnionBoundPr.pr_unionFin_le (μ : UnionBoundPr E) :
    ∀ {m : ℕ} (f : Fin m → E), μ.pr (μ.unionFin f) ≤ ∑ i, μ.pr (f i) := by
  intro m
  induction m with
  | zero =>
      intro f
      simp [UnionBoundPr.unionFin, μ.pr_empty]
  | succ m ih =>
      intro f
      calc
        μ.pr (μ.unionFin f)
            = μ.pr (μ.union (f 0) (μ.unionFin (fun i : Fin m => f i.succ))) := rfl
        _ ≤ μ.pr (f 0) + μ.pr (μ.unionFin (fun i : Fin m => f i.succ)) :=
              μ.pr_union_le _ _
        _ ≤ μ.pr (f 0) + ∑ i : Fin m, μ.pr (f i.succ) := by
              gcongr
              exact ih (fun i : Fin m => f i.succ)
        _ = ∑ i, μ.pr (f i) := by rw [Fin.sum_univ_succ]

/-- **BCS soundness-error union bound (accounting form).**

Given a probability functional with a union bound, an interaction-phase bad event
`badInteraction` bounded by `εInteraction`, and per-message opening-failure events
`badOpen i` each bounded by `εOpen i`, the union of all bad events is bounded by
the BCS total error `εInteraction + Σ εOpen`.

This is the `ℝ≥0` skeleton of "IOP-soundness + per-message binding ⟹ argument
soundness": the probabilistic composition reduces to exactly this accounting once
each phase's failure probability is controlled. It is fully proved (no sorry),
using only monotonicity + subadditivity. -/
theorem bcs_union_bound {m : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction : ℝ≥0) (εOpen : Fin m → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ bcsTotalError εInteraction εOpen := by
  calc
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
        ≤ μ.pr badInteraction + μ.pr (μ.unionFin badOpen) := μ.pr_union_le _ _
    _ ≤ εInteraction + ∑ i, μ.pr (badOpen i) :=
          add_le_add hInteraction (μ.pr_unionFin_le badOpen)
    _ ≤ εInteraction + ∑ i, εOpen i := by
          gcongr with i
          exact hOpen i
    _ = bcsTotalError εInteraction εOpen := rfl

/-! ## 3. Specialization to the two-phase `append` shape

The reduction-level `OracleReduction.BCSTransform` is literally
`Reduction.append interaction opening`. When the opening phase is treated as a
single composite reduction with error `εOpen`, the BCS error is the additive
`εInteraction + εOpen` of `Verifier.append_soundness`. We record that this is the
`m = 1` instance of the union bound, so the two-phase compiler error and the
`m`-message error are the same accounting. -/

/-- The two-phase `append` accounting: interaction error plus a single composite
opening error, matching `Verifier.append_soundness`'s additive
`soundnessError₁ + soundnessError₂`. -/
theorem bcs_append_accounting (μ : UnionBoundPr E)
    (badInteraction badOpen : E) (εInteraction εOpen : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : μ.pr badOpen ≤ εOpen) :
    μ.pr (μ.union badInteraction (μ.union badOpen μ.empty))
      ≤ εInteraction + εOpen := by
  have h := bcs_union_bound (m := 1) μ badInteraction (fun _ => badOpen)
    εInteraction (fun _ => εOpen) hInteraction (fun _ => hOpen)
  -- `unionFin` on a `Fin 1` family is `union (badOpen) empty`; total error is
  -- `εInteraction + εOpen` by `bcsTotalError_one`.
  simpa [UnionBoundPr.unionFin, bcsTotalError_one] using h

/-- Consistency check: the two-phase total and the `m = 1` `bcsTotalError` agree,
so collapsing the opening phase to one composite reduction loses no accounting. -/
theorem bcs_two_phase_total_eq (εInteraction εOpen : ℝ≥0) :
    bcsTotalError εInteraction (fun _ : Fin 1 => εOpen) = εInteraction + εOpen :=
  bcsTotalError_one _ _

/-! ## 4. A concrete witness that `UnionBoundPr` is inhabited (sanity)

To confirm the abstract interface is not vacuous, we exhibit a concrete model:
events are `ℝ≥0` "weights", `pr` is the identity, union is `max` (which is
subadditive over `ℝ≥0`), and the empty event is `0`. This shows the hypotheses of
`bcs_union_bound` are simultaneously satisfiable, so the bound is non-vacuous. -/

/-- A trivial concrete `UnionBoundPr` on `ℝ≥0`: `pr = id`, `union = max`. -/
def maxUnionBoundPr : UnionBoundPr ℝ≥0 where
  pr := id
  empty := 0
  union := max
  pr_empty := rfl
  pr_union_le a b := by
    -- `max a b ≤ a + b` for nonnegative `a, b`.
    rcases le_total a b with h | h
    · rw [max_eq_right h]; exact le_add_self
    · rw [max_eq_left h]; exact le_add_right le_rfl

/-- Sanity: the union bound instantiates on the concrete model, so the abstract
accounting is not vacuous. -/
example (εInteraction : ℝ≥0) (εOpen : Fin 3 → ℝ≥0) :
    maxUnionBoundPr.pr
        (maxUnionBoundPr.union εInteraction (maxUnionBoundPr.unionFin εOpen))
      ≤ bcsTotalError εInteraction εOpen :=
  bcs_union_bound maxUnionBoundPr εInteraction εOpen εInteraction εOpen
    le_rfl (fun _ => le_rfl)

end ArkLibScratch.Issue62
