/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveringCount

/-!
# CS25 covered-stack existence from the few-far-words budget (toward T4.17, #82)

Composes the proven pigeonhole `exists_line_covered_stack_of_sum_far_lt` with the covering
double-count `sum_far_card_eq` to obtain a single clean reduction: a fully line-covered stack
exists once `|F| · #{w far from C} < |ι → A|`. This is the crisp remaining target for the CS25
complete-CA-breakdown lower bound — the genuine open content is now exactly the "few far words"
budget `#{w far} < |A|^n / |F|`, which the qEntropy/RS-ball-count argument must supply.
-/

open scoped NNReal
open Finset

set_option linter.unusedSectionVars false

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Covered bad-line stack from the "few far words" budget.** If `|F| · #{w far from C} < |ι → A|`
then some stack `u` has its whole affine line `u 0 + γ • u 1` within distance `δ` of `C`. -/
theorem exists_line_covered_stack_of_far_lt (C : Set (ι → A)) (δ : ℝ≥0)
    (hbudget : Fintype.card F * (univ.filter (fun w : ι → A => ¬ δᵣ(w, C) ≤ δ)).card
        < Fintype.card (ι → A)) :
    ∃ u : Matrix (Fin 2) ι A, ∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ := by
  classical
  have hpos : 0 < Fintype.card (ι → A) :=
    Fintype.card_pos_iff.mpr (⟨fun _ => 0⟩ : Nonempty (ι → A))
  have hcard : Fintype.card (Matrix (Fin 2) ι A)
      = Fintype.card (ι → A) * Fintype.card (ι → A) :=
    (Fintype.card_congr (finTwoArrowEquiv (ι → A))).trans (Fintype.card_prod _ _)
  have hsum : (∑ u : Matrix (Fin 2) ι A,
      (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card)
      < Fintype.card (Matrix (Fin 2) ι A) := by
    rw [sum_far_card_eq, hcard]
    calc Fintype.card F * Fintype.card (ι → A)
            * (univ.filter (fun w : ι → A => ¬ δᵣ(w, C) ≤ δ)).card
        = (Fintype.card F * (univ.filter (fun w : ι → A => ¬ δᵣ(w, C) ≤ δ)).card)
            * Fintype.card (ι → A) := by ring
      _ < Fintype.card (ι → A) * Fintype.card (ι → A) :=
          mul_lt_mul_of_pos_right hbudget hpos
  exact exists_line_covered_stack_of_sum_far_lt C δ hsum

end ProximityGap
