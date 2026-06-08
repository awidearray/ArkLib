/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.UnclearedEmbedding

/-!
# Quantitative extraction / base-case API for the carved P2 core (BCIKS20 A.4, issue #139)

Infrastructure around `RestrictedFaaDiBrunoMatch` — the #139 analogue of #138's clearing-product
divisibility/quotient API. Every consequence lemma takes the (unproven) combinatorial core
`RestrictedFaaDiBrunoMatchAt` only as an explicit hypothesis (using just the proven `ζ ≠ 0`),
exactly as the in-tree P2 consequence theorems do — none assumes the STEP-8 core.

* `coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt` / `restrictedMatchAt_of_…` /
  `restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq` — the carved core at order `t` is *exactly*
  the normalized-quotient coefficient equation `coeff (t+1) βHenselAssembled = −rFdBSum t / ζ`.
* `coeff_succ_βHenselAssembled_eq_of_restrictedMatch` — the all-orders consumer.
* `restrictedFaaDiBrunoSum_zero_eq_powerSum` — the `t = 0` base case of the raw STEP-1 defect sum.
* `neg_ζ_mul_coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree` /
  `coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree_div_ζ` — the order-zero
  recursion side alone gives a closed form for the first successor coefficient.
* `RestrictedMatchAtZeroTaylorWDivTarget` — the fixed order-zero core as the exact equality of the
  root-side Taylor sum and the un-cleared Taylor sum divided by `W ^ R.natDegree`.
* `RestrictedMatchAtZeroEval₂WDivTarget` — the same fixed order-zero target in compact `eval₂`
  form, before expanding either side into Taylor sums.
* `restrictedMatchAtZeroEval₂WDivTarget_iff_taylorWDivTarget` — direct bridge between the compact
  `eval₂` target and the expanded Taylor-sum target.
* `RestrictedMatchAtZero{Taylor,Eval₂}WDivTarget.of_…` / `RestrictedFaaDiBrunoPartitionMatchAt`
  target constructors — endpoint adapters between the order-zero targets and the full carved /
  normalized partition residual surfaces.
* `embeddingCleared_eq_Wpow_mul_uncleared_of_target` — makes the cleared/un-cleared `eval₂` mismatch
  *quantitative*: under the STEP-8 target, the two `𝒪`-reps differ by exactly `W^{natDegreeY p}`.
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

/-- **Quantitative coefficient extraction from the carved P2 core (consequence, axiom-clean).**
Given `RestrictedFaaDiBrunoMatchAt t` and the genuine separability non-vanishing `ζ ≠ 0`, the
`(t+1)` coefficient of `βHenselAssembled` is `−restrictedFaaDiBrunoSum t / ζ`.
#139 analogue of #138's `divWeight_quotient_unique`: the unproven combinatorial core is taken
only as a hypothesis. -/
theorem coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H := by
  unfold RestrictedFaaDiBrunoMatchAt at hmatch
  rw [hmatch, neg_neg, mul_comm, mul_div_assoc, div_self (ζ_ne_zero H x₀ R hHyp), mul_one]

/-- **Converse of the quantitative extraction (axiom-clean).** The explicit coefficient equation
implies the carved single-order core `RestrictedFaaDiBrunoMatchAt t` (again only using `ζ ≠ 0`). -/
theorem restrictedMatchAt_of_coeff_succ_βHenselAssembled_eq (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hcoeff : PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t := by
  unfold RestrictedFaaDiBrunoMatchAt
  rw [hcoeff, mul_div_assoc', mul_comm (ClaimA2.ζ R x₀ H),
    mul_div_assoc, div_self (ζ_ne_zero H x₀ R hHyp), mul_one, neg_neg]

/-- **The carved core at order `t` is exactly the normalized-quotient coefficient equation.** -/
theorem restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t ↔
      PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H :=
  ⟨coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt H x₀ R hHyp t,
    restrictedMatchAt_of_coeff_succ_βHenselAssembled_eq H x₀ R hHyp t⟩

/-- **All-orders quantitative coefficient extraction (axiom-clean).** From the full carved core
`RestrictedFaaDiBrunoMatch`, every successor coefficient of the assembled numerator series is the
normalized quotient `−restrictedFaaDiBrunoSum t / ζ`. -/
theorem coeff_succ_βHenselAssembled_eq_of_restrictedMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) (t : ℕ) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H :=
  coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt H x₀ R hHyp t (hmatch t)

/-- **Order-zero base case of the raw restricted Faà-di-Bruno sum (axiom-clean).** The un-normalized
STEP-1 defect sum collapses at `t = 0` to the single surviving Taylor power-sum over the `Y`-degree
of `Q` — the raw sibling of `restrictedFaaDiBrunoPartitionForm_zero_eq_powerSum`. -/
theorem restrictedFaaDiBrunoSum_zero_eq_powerSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedFaaDiBrunoSum H x₀ R hHyp 0 =
      ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        (liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i))
        * (PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ i := by
  rw [restrictedFaaDiBrunoSum_eq_restrictedPartitionForm H x₀ R hHyp 0,
    restrictedFaaDiBrunoPartitionForm_zero_eq_powerSum H x₀ R hHyp]

/-- **Order-zero raw sum after reabsorbing the surviving power-sum (axiom-clean).** The raw
restricted Faà-di-Bruno sum at `t = 0` is exactly the cleared root evaluation
`hasseEvalAtRoot ... 1 0`. -/
theorem restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedFaaDiBrunoSum H x₀ R hHyp 0 = hasseEvalAtRoot H x₀ R 1 0 := by
  rw [restrictedFaaDiBrunoSum_zero_eq_powerSum H x₀ R hHyp,
    ← restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot H x₀ R hHyp]
  rfl

/-- **Order-zero quantitative coefficient extraction (axiom-clean).** The carved P2 core at
order zero gives the base successor coefficient equation directly in terms of `hasseEvalAtRoot`. -/
theorem coeff_one_βHenselAssembled_eq_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
      = -hasseEvalAtRoot H x₀ R 1 0 / ClaimA2.ζ R x₀ H := by
  simpa [restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot H x₀ R hHyp] using
    coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt H x₀ R hHyp 0 hmatch

/-- **Converse order-zero quantitative extraction (axiom-clean).** The base coefficient equation
with the reabsorbed LHS `hasseEvalAtRoot` implies the carved order-zero core. -/
theorem restrictedMatchAt_zero_of_coeff_one_βHenselAssembled_eq
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hcoeff :
      PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
        = -hasseEvalAtRoot H x₀ R 1 0 / ClaimA2.ζ R x₀ H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  apply restrictedMatchAt_of_coeff_succ_βHenselAssembled_eq H x₀ R hHyp 0
  simpa [restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot H x₀ R hHyp] using hcoeff

/-- **Order-zero carved core iff the reabsorbed base coefficient equation.** -/
theorem restrictedMatchAt_zero_iff_coeff_one_βHenselAssembled_eq
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
        = -hasseEvalAtRoot H x₀ R 1 0 / ClaimA2.ζ R x₀ H :=
  ⟨coeff_one_βHenselAssembled_eq_of_restrictedMatchAt_zero H x₀ R hHyp,
    restrictedMatchAt_zero_of_coeff_one_βHenselAssembled_eq H x₀ R hHyp⟩

/-- **Order-zero recursion-side closed form, unsolved coefficient form.**  The `βHensel`
recursion itself makes the normalized RHS `-ζ * coeff 1 βHenselAssembled` equal to the un-cleared
Hasse numerator divided by `W ^ R.natDegree`, under the same degree hypothesis used by the
order-zero RHS cancellation. This is recursion-side normalization only; it does not compare with
the LHS `hasseEvalAtRoot`. -/
theorem neg_ζ_mul_coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    - (ClaimA2.ζ R x₀ H * PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp))
      = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree := by
  calc
    - (ClaimA2.ζ R x₀ H * PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp))
        = restrictedMatchRecursionPartitionForm H x₀ R hHyp 0 := by
      simpa using restrictedMatch_rhs_eq_restrictedRecursionPartitionForm H x₀ R hHyp 0
    _ = restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp := by
      exact restrictedMatchRecursionPartitionForm_zero_eq_single_B_coeff H x₀ R hHyp
    _ = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree := by
      exact
        restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_W_natDegree
          H x₀ R hHyp hd (ζ_ne_zero H x₀ R hHyp)

/-- **Order-zero recursion-side closed form, solved coefficient form.**  Dividing the previous
closed form by the nonzero separability factor `ζ` gives the first successor coefficient of
`βHenselAssembled` explicitly in terms of the un-cleared Hasse numerator. -/
theorem coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree_div_ζ
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
      = - (embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree)
          / ClaimA2.ζ R x₀ H := by
  have hneg :=
    neg_ζ_mul_coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree H x₀ R hHyp hd
  have hζ : ClaimA2.ζ R x₀ H ≠ 0 := ζ_ne_zero H x₀ R hHyp
  rw [← hneg]
  field_simp [hζ]

/-- **Order-zero Taylor/W-divisor target.** The fixed order-zero P2 obstruction after all proven
normalizations: the root-side shifted Hasse-Taylor sum with powers `(T/W)^i` equals the un-cleared
shifted Hasse-Taylor sum with powers `T^i`, divided by the global factor `W ^ R.natDegree`. -/
def RestrictedMatchAtZeroTaylorWDivTarget (x₀ : F) (R : F[X][X][Y]) : Prop :=
  (∑ i ∈ Finset.range ((Bivariate.evalX (Polynomial.C x₀)
          (hasseDerivX 1 (hasseDerivY 0 R))).natDegree + 1),
      (i + 0).choose 0
        • (liftToFunctionField (H := H)
              ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff (i + 0))
            * (functionFieldT (H := H)
                / liftToFunctionField (H := H) H.leadingCoeff) ^ i))
    =
    (∑ i ∈ Finset.range ((Bivariate.evalX (Polynomial.C x₀)
          (hasseDerivX 1 (hasseDerivY 0 R))).natDegree + 1),
      (i + 0).choose 0
        • (liftToFunctionField (H := H)
              ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff (i + 0))
            * (functionFieldT (H := H)) ^ i))
      / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree

/-- The carved order-zero P2 core is exactly the named Taylor/W-divisor target under the same
degree hypothesis as the order-zero RHS cancellation. -/
theorem restrictedMatchAt_zero_iff_taylorWDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      RestrictedMatchAtZeroTaylorWDivTarget H x₀ R := by
  unfold RestrictedMatchAtZeroTaylorWDivTarget
  rw [restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree
    H x₀ R hHyp hd (ζ_ne_zero H x₀ R hHyp)]
  rw [hasseEvalAtRoot_eq_taylorSum,
    embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared_eq_taylorSum]

/-- Project the Taylor/W-divisor target from the carved order-zero P2 core. -/
theorem RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    RestrictedMatchAtZeroTaylorWDivTarget H x₀ R :=
  (restrictedMatchAt_zero_iff_taylorWDivTarget H x₀ R hHyp hd).1 hmatch

/-- Build the carved order-zero P2 core from the Taylor/W-divisor target. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_taylorWDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : RestrictedMatchAtZeroTaylorWDivTarget H x₀ R) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_taylorWDivTarget H x₀ R hHyp hd).2 htarget

/-- **Order-zero `eval₂`/W-divisor target.** The same fixed order-zero P2 obstruction as
`RestrictedMatchAtZeroTaylorWDivTarget`, but before expanding the two sides into shifted Taylor
sums: `Y ↦ T/W` equals `Y ↦ T` divided by `W ^ R.natDegree` on
`(Δ_X Δ_Y^0 R)|x₀`. -/
def RestrictedMatchAtZeroEval₂WDivTarget (x₀ : F) (R : F[X][X][Y]) : Prop :=
  Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R)))
    =
    Polynomial.eval₂ (liftToFunctionField (H := H)) (functionFieldT (H := H))
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R)))
      / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree

/-- The carved order-zero P2 core is exactly the compact `eval₂`/W-divisor target under the
same degree hypothesis as the order-zero RHS cancellation. -/
theorem restrictedMatchAt_zero_iff_eval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      RestrictedMatchAtZeroEval₂WDivTarget H x₀ R := by
  unfold RestrictedMatchAtZeroEval₂WDivTarget
  rw [restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree
    H x₀ R hHyp hd (ζ_ne_zero H x₀ R hHyp)]
  unfold hasseEvalAtRoot
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared]

/-- Project the compact `eval₂`/W-divisor target from the carved order-zero P2 core. -/
theorem RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  (restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd).1 hmatch

/-- Build the carved order-zero P2 core from the compact `eval₂`/W-divisor target. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_eval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : RestrictedMatchAtZeroEval₂WDivTarget H x₀ R) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd).2 htarget

/-- The compact `eval₂`/W-divisor order-zero target is exactly the expanded shifted Taylor-sum
order-zero target. This bridge has no `ClaimA2` or degree hypotheses; it only changes presentation
of the same equality. -/
theorem restrictedMatchAtZeroEval₂WDivTarget_iff_taylorWDivTarget
    (x₀ : F) (R : F[X][X][Y]) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R ↔
      RestrictedMatchAtZeroTaylorWDivTarget H x₀ R := by
  unfold RestrictedMatchAtZeroEval₂WDivTarget RestrictedMatchAtZeroTaylorWDivTarget
  rw [← hasseEvalAtRoot_eq_taylorSum H x₀ R 1 0,
    ← embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared_eq_taylorSum H x₀ R 1 0]
  unfold hasseEvalAtRoot
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared]

/-- Expand the compact `eval₂`/W-divisor target into the Taylor-sum target. -/
theorem RestrictedMatchAtZeroTaylorWDivTarget.of_eval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y])
    (htarget : RestrictedMatchAtZeroEval₂WDivTarget H x₀ R) :
    RestrictedMatchAtZeroTaylorWDivTarget H x₀ R :=
  (restrictedMatchAtZeroEval₂WDivTarget_iff_taylorWDivTarget H x₀ R).1 htarget

/-- Compress the Taylor-sum target back into the compact `eval₂`/W-divisor target. -/
theorem RestrictedMatchAtZeroEval₂WDivTarget.of_taylorWDivTarget
    (x₀ : F) (R : F[X][X][Y])
    (htarget : RestrictedMatchAtZeroTaylorWDivTarget H x₀ R) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  (restrictedMatchAtZeroEval₂WDivTarget_iff_taylorWDivTarget H x₀ R).2 htarget

/-- Project the expanded Taylor/W-divisor target from the full carved P2 core. -/
theorem RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    RestrictedMatchAtZeroTaylorWDivTarget H x₀ R :=
  RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd (hmatch 0)

/-- Project the compact `eval₂`/W-divisor target from the full carved P2 core. -/
theorem RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd (hmatch 0)

/-- Project the expanded Taylor/W-divisor target from the fixed order-zero partition residual. -/
theorem RestrictedMatchAtZeroTaylorWDivTarget.of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    RestrictedMatchAtZeroTaylorWDivTarget H x₀ R :=
  RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt H x₀ R hHyp 0 hpart)

/-- Project the compact `eval₂`/W-divisor target from the fixed order-zero partition residual. -/
theorem RestrictedMatchAtZeroEval₂WDivTarget.of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt H x₀ R hHyp 0 hpart)

/-- Build the fixed order-zero partition residual from the expanded Taylor/W-divisor target. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_taylorWDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : RestrictedMatchAtZeroTaylorWDivTarget H x₀ R) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  RestrictedFaaDiBrunoPartitionMatchAt.of_restrictedMatchAt H x₀ R hHyp 0
    (RestrictedFaaDiBrunoMatchAt.zero_of_taylorWDivTarget H x₀ R hHyp hd htarget)

/-- Build the fixed order-zero partition residual from the compact `eval₂`/W-divisor target. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_eval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : RestrictedMatchAtZeroEval₂WDivTarget H x₀ R) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  RestrictedFaaDiBrunoPartitionMatchAt.of_restrictedMatchAt H x₀ R hHyp 0
    (RestrictedFaaDiBrunoMatchAt.zero_of_eval₂WDivTarget H x₀ R hHyp hd htarget)

/-- Project the expanded Taylor/W-divisor target from the all-orders partition residual. -/
theorem RestrictedMatchAtZeroTaylorWDivTarget.of_partitionMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    RestrictedMatchAtZeroTaylorWDivTarget H x₀ R :=
  RestrictedMatchAtZeroTaylorWDivTarget.of_partitionMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoPartitionMatch.at H x₀ R hHyp hpart 0)

/-- Project the compact `eval₂`/W-divisor target from the all-orders partition residual. -/
theorem RestrictedMatchAtZeroEval₂WDivTarget.of_partitionMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  RestrictedMatchAtZeroEval₂WDivTarget.of_partitionMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoPartitionMatch.at H x₀ R hHyp hpart 0)

/-- **The cleared `𝒪`-rep embedding is `W^{natDegreeY p}` times the un-cleared rep embedding, GIVEN
the STEP-8 target (axiom-clean).** Makes the cleared/un-cleared `eval₂` mismatch *quantitative*:
under the carved STEP-8 match `HasseCoeffRepr𝒪UnclearedEval₂Target`, the two `𝒪`-reps are related by
exactly the `m = |λ|`-dependent factor `W^{natDegreeY p}` named in the #139 obstruction analysis. -/
theorem embeddingCleared_eq_Wpow_mul_uncleared_of_target (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ)
    (htarget : HasseCoeffRepr𝒪UnclearedEval₂Target H x₀ R i1 m) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (hasseCoeffRepr𝒪_cleared H x₀ R i1 m) : 𝒪 H)
      = liftToFunctionField (H := H) H.leadingCoeff
            ^ Bivariate.natDegreeY
                (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))
          * embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m) := by
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared,
    (HasseCoeffRepr𝒪UnclearedMatchesRoot.of_eval₂Target H x₀ R i1 m htarget)]

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoSum_zero_eq_powerSum
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot
#print axioms BCIKS20.HenselNumerator.coeff_one_βHenselAssembled_eq_of_restrictedMatchAt_zero
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_coeff_one_βHenselAssembled_eq
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.neg_ζ_mul_coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree_div_ζ
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_taylorWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.zero_of_taylorWDivTarget
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_eval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.zero_of_eval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAtZeroEval₂WDivTarget_iff_taylorWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget.of_eval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget.of_taylorWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget.of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget.of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_taylorWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_eval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget.of_partitionMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget.of_partitionMatch
#print axioms BCIKS20.HenselNumerator.embeddingCleared_eq_Wpow_mul_uncleared_of_target
