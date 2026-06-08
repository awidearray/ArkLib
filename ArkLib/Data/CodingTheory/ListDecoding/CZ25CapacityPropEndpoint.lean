/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.Bounds

/-!
# ABF26 C3.5 — named-`Prop` endpoint from the single coordinate-fiber-cap residual

This file closes the **named** external statement `frs_list_decoding_capacity_cz25`
(ABF26 Corollary 3.5 [CZ25 Cor 2.21], the unfolded inequality `Prop` admitted in
`ListDecoding/Bounds.lean`) reduced to exactly:

* `hT218` — ABF26 T2.18 [GK16] (FRS is a `τ`-subspace-design), and
* `hCap`  — the single named bridge residual `CZ25CoordFiberCap` for **every**
  `τ`-subspace-design code (the irreducible Guruswami–Wang affine-flat
  coordinate-fiber cap; documented in `CZ25SpanDimension.lean` as having no
  in-tree shortcut), plus
* `hηnat` — the documented floor/real reconciliation `1/η = ⌊1/η⌋`.

The inequality-body version of this composition is
`CZ25CapacityReduction.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218`.
Here we land the variant whose **conclusion is the named `Prop`**
`frs_list_decoding_capacity_cz25 …`, so downstream assembly code that targets the
named statement (not its unfolded inequality body) routes through one named
residual `CZ25CoordFiberCap` (+ T2.18) rather than re-discharging the
`hT34` general `Λ`-bound hypothesis.

The reduction is a pure composition of two already-landed, axiom-clean in-tree
bricks:

* `subspaceDesign_list_decoding_cz25_of_coordFiberCap` (T3.4 from the fiber cap,
  the #93 bridge), and
* `frs_list_decoding_capacity_cz25_of_residuals_prop` (the C3.5 corollary's own
  τ-substitution + bound algebra + floor/real reconciliation, concluding the
  named `Prop`).

No `sorry`, no new axioms. It does **not** attempt `CZ25CoordFiberCap` itself.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ListDecodable

/-- **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — named-`Prop` endpoint from the
coordinate-fiber cap.**

Concludes the named external statement `frs_list_decoding_capacity_cz25` from the
FRS subspace-design instance `hT218` and the single named residual
`CZ25CoordFiberCap` (quantified over every `τ`-subspace-design code), plus the
floor/real reconciliation `hηnat`.

This threads `CZ25CoordFiberCap` to the named C3.5 `Prop` by composing the #93
bridge `subspaceDesign_list_decoding_cz25_of_coordFiberCap` (which discharges the
general `hT34` `Λ`-bound) with `frs_list_decoding_capacity_cz25_of_residuals_prop`
(which discharges the corollary's own τ-substitution + bound algebra). -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη')
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s := by
  refine frs_list_decoding_capacity_cz25_of_residuals_prop
    domain k s ω hs_pos η hη_pos hη_lt_s hT218 ?_ hηnat
  intro τ' C' h' η' hη'_pos
  exact subspaceDesign_list_decoding_cz25_of_coordFiberCap s τ' C' h' η' hη'_pos
    (hCap τ' C' h' η' hη'_pos)

end CodingTheory

#print axioms CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop
