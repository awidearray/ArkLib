/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Match

/-!
# Scratch: BCIKS20 A.4 P2 — `RestrictedFaaDiBrunoMatch` re-keying bricks (issue #90)

Scratch-first workspace for issue #90.  Works ONLY against the built oleans of
`P2Match` / `P2Close` / `HenselNumerator`.  Everything here is axiom-clean and proven;
integrated upstream once green.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

set_option maxHeartbeats 1600000

/-- **Probe: the carved core is equivalent to `βHenselAssembled = gammaGenuine`.**
The forward direction is the proven uniqueness identification; the backward direction
transports the unconditional genuine-root `gammaGenuine_root` along the equality. -/
theorem restrictedMatch_iff_assembled_eq_gammaGenuine (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp
      ↔ βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp := by
  constructor
  · intro hmatch
    exact βHenselAssembled_eq_gammaGenuine H x₀ R hHyp
      (assembledSeries_isRoot_of_match H x₀ R hHyp hmatch)
  · intro heq
    refine restrictedFaaDiBrunoMatch_of_fullVanishes H x₀ R hHyp ?_
    intro t
    rw [faaDiBrunoFullSum_eq_coeff, heq, gammaGenuine_root hHyp, map_zero]

/-! **Axiom audit for the carved-core re-keying brick.** -/
section AxiomAudit
#print axioms restrictedMatch_iff_assembled_eq_gammaGenuine
end AxiomAudit

end BCIKS20.HenselNumerator
