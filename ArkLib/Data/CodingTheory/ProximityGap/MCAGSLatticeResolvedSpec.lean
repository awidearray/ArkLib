/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCAGSLatticePrizeSpec

/-!
# Exact GS MCA prize resolutions with specifications

`MCAGSLatticePrizeSpec.lean` exposes adjacent-upper-witness front doors that resolve the
four-rate faithful MCA prize at the concrete lower-frontier lattice indices. This file packages
those exact resolutions with the satisfy/maximality specification supplied by
`mcaPrizeLatticeResolved_iff`.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal ENNReal

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GrandChallengesLattice

open GrandChallenges

section GSResolvedSpec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Faithful GS mass frontiers plus adjacent explicit upper witnesses resolve the four-rate MCA
prize at the lower-frontier lattice indices and expose satisfy/maximality specs for those exact
indices. -/
theorem mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
        (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar
              (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i →
              i ≤ latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ := by
    simpa [τ] using
      mcaPrizeLatticeResolved_of_GSMassFrontiers_and_adjacent_upperWitnesses
        domain δ hδ_le_one frontier whi hδhi hadj
  exact ⟨by simpa [τ] using hτ, by simpa [τ] using (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Faithful GS pivot/list-size frontiers plus adjacent explicit upper witnesses resolve the
four-rate MCA prize at the lower-frontier lattice indices and expose satisfy/maximality specs for
those exact indices. -/
theorem mcaPrizeLatticeResolved_with_spec_of_GSPivotFrontiers_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSPivotLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
        (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar
              (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i →
              i ≤ latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ := by
    simpa [τ] using
      mcaPrizeLatticeResolved_of_GSPivotFrontiers_and_adjacent_upperWitnesses
        domain δ hδ_le_one frontier whi hδhi hadj
  exact ⟨by simpa [τ] using hτ, by simpa [τ] using (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

end GSResolvedSpec

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_GSPivotFrontiers_and_adjacent_upperWitnesses

end GrandChallengesLattice

end ProximityGap
