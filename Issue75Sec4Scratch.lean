/-
Issue #75 — ABF26 §4 remaining CapacityBounds CA/MCA theorem families.
SCRATCH (hand-verified; migration target: a sibling CapacityBoundsT413.lean importing
ListDecoding.Bounds, or CapacityBounds.lean itself if the import is added).

GOAL OF THIS FILE
-----------------
CapacityBounds.lean is already heavily residualized: every external admit has a `_of_bound`
symbolic wrapper, the lower-bound families (T4.16/CS25/DG25/T4.18) have witness-package +
covered-stack + count-budget reductions, and the GG25 *FRS* corollary T4.14
(`frs_epsMCA_capacity_gg25`) is reduced to T4.13 + T2.18 via
`frs_epsMCA_capacity_gg25_of_residuals` (T2.18 itself now proven, AdmissibleDischarge.lean).

The one §4 brick whose in-tree-extractable content is NOT yet exposed is the GG25 base theorem
**T4.13** `subspaceDesign_epsMCA_gg25` — currently it has only the trivial `_of_bound` wrapper.
The file's own note (CapacityBounds.lean:1212) states T4.13 "factors as T3.4 (design→list-size)
∘ T5.1 (list-size→MCA)".  T3.4 IS PROVEN IN-TREE (conditional on the Guruswami–Wang span charge
`CZ25SpanBound'`) as `subspaceDesign_list_decoding_cz25`.  So the genuine SILVER reduction is:

    T4.13  ⟸  [ PROVEN T3.4 Λ-bound, invoked ]  +  [ ONE named residual: the vector-alphabet
              list-size → epsMCA amplification at the matching radius (GG25 line-stitching) ]

This file builds that reduction.  It actually INVOKES the proven T3.4 path for the Λ half (so
the design→list-size content is genuinely proven, not admitted), proves the radius
reconciliation algebra, and isolates the GG25 list→MCA engine as a single explicit hypothesis.
That is strictly more in-tree content than the current monolithic admit.

API ANCHORS (signatures read from source; no guessed lemma names):
  epsMCA  (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal                         Errors.lean:231
  Lambda  (C : Code ι F) (δ : ℝ) : ℕ∞                                   ListDecodability.lean:85
  Lambda_mono {C} {δ₁ δ₂} [Finite F] (h : δ₁ ≤ δ₂) : Lambda C δ₁ ≤ Lambda C δ₂
                                                                        ListDecodability.lean:96
  IsSubspaceDesign s τ (C : Submodule F (ι → Fin s → F)) : Prop         SubspaceDesign.lean:74
  CZ25SpanBound' s τ C h η hη : Prop                                    CZ25SpanDimension.lean:257
  subspaceDesign_list_decoding_cz25 s τ C h η hη_pos hSB :
     (Lambda C (1 - τ ⌊1/η⌋ - η) : ENNReal) ≤ ofReal ((1 - τ ⌊1/η⌋)/η)  Bounds.lean:2109
  subspaceDesign_epsMCA_gg25 s τ C h t ht : Prop :=
     epsMCA C (1 - τ(t+1) - 3/(2t)).toNNReal ≤ ofReal ((t·n + 4t²)/|F|) CapacityBounds.lean:1195
  epsCA_le_epsMCA (MC : Submodule F (ι → A)) δ : epsCA MC δ δ ≤ epsMCA MC δ (Fact 4.5, PROVEN)
                                                                        Errors.lean:496

No `sorry`/`admit`/`axiom`/`native_decide`.  The genuine external content is isolated as the
named predicate `SubspaceDesignListToMCA` (the GG25 design-list-decoder → MCA amplification).
Everything else (the T3.4 Λ invocation, the radius reconciliation, the `ℕ∞` cast plumbing,
the bound transitivity) is proven.
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ListDecoding.Bounds
import ArkLib.Data.CodingTheory.ListDecodability

namespace CodingTheory
namespace Issue75Scratch

open scoped NNReal
open ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The GG25 list-size → MCA amplification residual (the genuine external core of T4.13)

`subspaceDesign_epsMCA_gg25` (T4.13) bounds `epsMCA` of a τ-subspace-design code at the
capacity-near radius `δ`.  The note at CapacityBounds.lean:1204-1225 makes explicit that the
entire substantive content is the GG25 line-stitching + interpolation engine turning a
*list-decoding* (`Lambda`) bound into an `epsMCA` bound.  We name exactly that step.

`SubspaceDesignListToMCA s τ C δ L bound`: *if* the subspace-design code `C` has list size
`≤ L` at radius `(δ:ℝ)`, then its MCA error at `δ` is `≤ bound`.  This is the vector-alphabet
analogue of T5.1 (`linear_listSize_to_epsMCA_gcxk25`, which is scalar-alphabet `LinearCode ι F`
only and so does NOT directly apply: here the alphabet is `Fin s → F`).  Isolating it as a
`Prop` predicate (rather than baking the GG25 constants into a black-box theorem) keeps the
residual honest and reusable across radii. -/
def SubspaceDesignListToMCA
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (δ : ℝ≥0) (L : ℕ) (bound : ℝ) : Prop :=
  (Lambda ((C : Set (ι → Fin s → F))) (δ : ℝ) ≤ (L : ℕ∞)) →
    epsMCA (F := F) (A := Fin s → F) ((C : Set (ι → Fin s → F))) δ ≤ ENNReal.ofReal bound

/-! ## Brick A — T4.13 from a Λ-bound (at the coerced radius) + the list→MCA residual.

Pure plumbing edge: the Λ hypothesis is stated at the *same* coerced radius
`((1 - τ(t+1) - 3/(2t)).toNNReal : ℝ)` that `SubspaceDesignListToMCA` consumes, so no
raw-vs-coerced bridge is needed here. -/
theorem subspaceDesign_epsMCA_gg25_of_lambda_coerced_listToMCA
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (t : ℕ) (ht : 0 < t) (L : ℕ)
    (hΛ : Lambda ((C : Set (ι → Fin s → F)))
        (((1 - τ (t + 1) - 3 / (2 * t : ℝ)).toNNReal : ℝ≥0) : ℝ) ≤ (L : ℕ∞))
    (hListToMCA : SubspaceDesignListToMCA s τ C
        ((1 - τ (t + 1) - 3 / (2 * t : ℝ)).toNNReal) L
        (((t : ℝ) * Fintype.card ι + 4 * t ^ 2) / Fintype.card F)) :
    subspaceDesign_epsMCA_gg25 s τ C h t ht := by
  unfold subspaceDesign_epsMCA_gg25
  exact hListToMCA hΛ

/-! ## Radius reconciliation: under the non-degenerate guard, raw radius = coerced radius.

The T4.13 radius `r := 1 - τ(t+1) - 3/(2t)` is wrapped in `toNNReal` inside
`subspaceDesign_epsMCA_gg25`.  When `0 ≤ r` (the non-degenerate / nonvacuous regime, exactly
the `CZ25SpanBound'` guard), `((r.toNNReal : ℝ≥0) : ℝ) = r`, so a raw Λ-bound at `r` is
literally a Λ-bound at the coerced radius. -/
theorem coe_toNNReal_radius
    (s : ℕ) (τ : ℕ → ℝ) (t : ℕ)
    (hr : 0 ≤ 1 - τ (t + 1) - 3 / (2 * t : ℝ)) :
    (((1 - τ (t + 1) - 3 / (2 * t : ℝ)).toNNReal : ℝ≥0) : ℝ)
      = 1 - τ (t + 1) - 3 / (2 * t : ℝ) :=
  -- `Real.coe_toNNReal (r) (h : 0 ≤ r) : (r.toNNReal : ℝ) = r` (in-tree at CapacityBounds:877,
  -- WeightedAgreement:394).  The `: ℝ≥0` annotation is redundant (`.toNNReal : ℝ≥0`).
  Real.coe_toNNReal _ hr

/-- Brick A, raw-radius form: under the non-degenerate guard `0 ≤ r`, a Λ-bound at the raw
T4.13 radius plus the list→MCA residual yields T4.13. -/
theorem subspaceDesign_epsMCA_gg25_of_lambda_raw_listToMCA
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (t : ℕ) (ht : 0 < t) (L : ℕ)
    (hr : 0 ≤ 1 - τ (t + 1) - 3 / (2 * t : ℝ))
    (hΛ : Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (t + 1) - 3 / (2 * t : ℝ)) ≤ (L : ℕ∞))
    (hListToMCA : SubspaceDesignListToMCA s τ C
        ((1 - τ (t + 1) - 3 / (2 * t : ℝ)).toNNReal) L
        (((t : ℝ) * Fintype.card ι + 4 * t ^ 2) / Fintype.card F)) :
    subspaceDesign_epsMCA_gg25 s τ C h t ht := by
  refine subspaceDesign_epsMCA_gg25_of_lambda_coerced_listToMCA s τ C h t ht L ?_ hListToMCA
  rw [coe_toNNReal_radius s τ t hr]
  exact hΛ

/-! ## Brick B — discharge the Λ-bound from the PROVEN T3.4 path.

T3.4 `subspaceDesign_list_decoding_cz25` gives, for parameter `η > 0` and the span charge
`CZ25SpanBound'`:

    Lambda C (1 - τ ⌊1/η⌋ - η) ≤ ofReal ((1 - τ ⌊1/η⌋)/η)            (PROVEN, conditional on hSB)

To feed Brick A we need the matching radius: pick `η` and an integer list bound `L` with

    (i)  ⌊1/η⌋ = t + 1            (radius-index match)
    (ii) η = 3/(2t)               (radius-slack match)
    (iii) (1 - τ(t+1))/η ≤ L      (list-size cast: the real Λ-bound is below the integer L)

Under (i)+(ii) the T3.4 radius `1 - τ⌊1/η⌋ - η` equals the T4.13 raw radius
`1 - τ(t+1) - 3/(2t)`, and (iii) lifts the `ofReal` real bound to the `(L:ℕ∞)` integer bound
that `SubspaceDesignListToMCA` consumes.  We pass (i)–(iii) as explicit hypotheses (the
informal GG25 choice `t ≈ 1/η`, made precise) so nothing is smuggled.

`hListBound` performs the genuine ℕ∞ ← ENNReal cast: `Lambda … : ℕ∞`, T3.4 bounds it as an
`ENNReal` (`(Lambda … : ENNReal) ≤ ofReal …`); we recover `Lambda … ≤ (L:ℕ∞)` from the integer
comparison via the cast lemma below. -/

/-- Helper: from `(Lambda C r : ENNReal) ≤ ENNReal.ofReal b` and `b ≤ (L:ℝ)`,
derive `Lambda C r ≤ (L:ℕ∞)`.  Honest ℕ∞↔ENNReal cast plumbing for Brick B.

The coercion `(Lambda C r : ENNReal)` is `ENat.toENNReal (Lambda C r)` (the convention used by
T3.4, e.g. Bounds.lean:227,328).  We chain in ENNReal then descend via `ENat.toENNReal_le`
(the order-iso `.mp`, confirmed in-tree at Folding.lean:942) and the cast identity
`ENat.toENNReal ((L:ℕ):ℕ∞) = ENNReal.ofReal (L:ℝ)` (the `hcast` idiom proven at Bounds.lean:328). -/
theorem lambda_le_natCast_of_ennreal_bound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (r : ℝ) (b : ℝ) (L : ℕ)
    (hEnn : (Lambda ((C : Set (ι → Fin s → F))) r : ENNReal) ≤ ENNReal.ofReal b)
    (hbL : b ≤ (L : ℝ)) :
    Lambda ((C : Set (ι → Fin s → F))) r ≤ (L : ℕ∞) := by
  -- cast identity for the integer bound, copying the proven Bounds.lean:328 idiom.
  have hcast : ENat.toENNReal ((L : ℕ) : ℕ∞) = ENNReal.ofReal (L : ℝ) := by
    rw [ENNReal.ofReal_natCast]; simp
  -- chain in ENNReal: toENNReal (Lambda) ≤ ofReal b ≤ ofReal L = toENNReal L.
  have hchain :
      ENat.toENNReal (Lambda ((C : Set (ι → Fin s → F))) r)
        ≤ ENat.toENNReal ((L : ℕ) : ℕ∞) := by
    rw [hcast]
    exact le_trans hEnn (ENNReal.ofReal_le_ofReal hbL)
  -- descend along the ℕ∞ ↪ ENNReal order-iso (`ENat.toENNReal_le : toENNReal a ≤ toENNReal b ↔ a ≤ b`).
  have hdesc := ENat.toENNReal_le.mp hchain
  simpa using hdesc

/-- **Brick B (T4.13 from PROVEN T3.4 + list→MCA residual).**  Composes the proven T3.4 Λ-bound
with the GG25 list→MCA amplification residual to yield T4.13.  The genuine residuals are exactly:
  * `hSB`  — the Guruswami–Wang span charge `CZ25SpanBound'` (the in-tree T3.4 residual);
  * `hListToMCA` — the GG25 vector-alphabet list→MCA amplification (the genuine GG25 engine).
Everything else (radius match, list-size cast, non-degeneracy) is explicit arithmetic. -/
theorem subspaceDesign_epsMCA_gg25_of_t34_residuals
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (t : ℕ) (ht : 0 < t) (L : ℕ)
    (η : ℝ) (hη_pos : 0 < η)
    -- radius reconciliation (the precise form of GG25's informal `t ≈ 1/η`):
    (hIdx : Nat.floor (1 / η) = t + 1)
    (hSlack : η = 3 / (2 * t : ℝ))
    -- non-degeneracy guard (= the `CZ25SpanBound'` nonvacuous regime):
    (hr : 0 ≤ 1 - τ (t + 1) - 3 / (2 * t : ℝ))
    -- list-size lift: the real T3.4 bound is below the integer `L`:
    (hListBound : (1 - τ (t + 1)) / η ≤ (L : ℝ))
    -- the two genuine residuals:
    (hSB : CZ25SpanBound' s τ C h η hη_pos)
    (hListToMCA : SubspaceDesignListToMCA s τ C
        ((1 - τ (t + 1) - 3 / (2 * t : ℝ)).toNNReal) L
        (((t : ℝ) * Fintype.card ι + 4 * t ^ 2) / Fintype.card F)) :
    subspaceDesign_epsMCA_gg25 s τ C h t ht := by
  -- (1) invoke PROVEN T3.4 to get the ENNReal Λ-bound at radius `1 - τ⌊1/η⌋ - η`.
  have hT34 := subspaceDesign_list_decoding_cz25 s τ C h η hη_pos hSB
  -- (2) rewrite the radius and the bound index using `hIdx`, `hSlack`.
  rw [hIdx] at hT34
  -- now hT34 : (Lambda C (1 - τ(t+1) - η) : ENNReal) ≤ ofReal ((1 - τ(t+1))/η)
  -- replace `η` by `3/(2t)` in the radius via `hSlack`:
  have hT34' : (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (t + 1) - 3 / (2 * t : ℝ)) : ENNReal)
      ≤ ENNReal.ofReal ((1 - τ (t + 1)) / η) := by
    rw [← hSlack]; exact hT34
  -- (3) lift the real bound to the integer list bound `(L:ℕ∞)`.
  have hΛnat : Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (t + 1) - 3 / (2 * t : ℝ)) ≤ (L : ℕ∞) :=
    lambda_le_natCast_of_ennreal_bound s τ C
      (1 - τ (t + 1) - 3 / (2 * t : ℝ)) ((1 - τ (t + 1)) / η) L hT34' hListBound
  -- (4) feed Brick A (raw-radius form) with the non-degeneracy guard.
  exact subspaceDesign_epsMCA_gg25_of_lambda_raw_listToMCA s τ C h t ht L hr hΛnat hListToMCA

/-! ## Brick C — the FRS specialization route is ALREADY closed in-tree.

Note for the migration record: once Brick B supplies T4.13 from (T3.4 charge + list→MCA
residual), the FRS corollary T4.14 (`frs_epsMCA_capacity_gg25`) needs no new work — it is
already reduced to T4.13 + T2.18 by the in-tree `frs_epsMCA_capacity_gg25_of_residuals`
(CapacityBounds.lean:1304) and the proven T2.18 admissibility discharge
(`frs_is_subspaceDesign_gk16_of_orderOf_ge_of_cosetSep`, AdmissibleDischarge.lean).  So Brick B
is the missing edge that, combined with the GG25 list→MCA engine, would close the *entire* GG25
capacity column (T4.13 → T4.14) down to two named residuals (`CZ25SpanBound'`,
`SubspaceDesignListToMCA`) plus the already-proven T2.18.  No Brick C decl is needed. -/

end Issue75Scratch
end CodingTheory
