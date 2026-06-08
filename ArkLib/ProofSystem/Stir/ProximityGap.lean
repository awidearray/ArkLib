/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Stir.ProximityBound

/-!
# STIR proximity gap for Reed-Solomon codes

This file states the proximity-gap theorem for Reed-Solomon codes used by STIR (Theorem 4.1),
relating the probability that a random linear combination of words is close to the code to the
existence of a common large agreement set for the individual words.

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

open NNReal ProbabilityTheory ReedSolomon

namespace STIR

/-- Theorem 4.1[BCIKS20] from [ACFY24stir]
  Let `C = RS[F, ι, degree]` be a ReedSolomon code with rate `degree / |ι|`
  and let Bstar(ρ) = √ρ. For all `δ ∈ (0, 1 - Bstar(ρ))`, `f₁,...,fₘ : ι → F`, if
  `Pr_{r ← F} [ δᵣ(rⱼ * fⱼ, C) ≤ δ] > err'(degree, ρ, δ, m)`
  then ∃ S ⊆ ι, |S| ≥ (1 - δ) * |ι| and
  ∀ i : m, ∃ u : C, u(S) = fᵢ(S)

  STATUS (audit refreshed 2026-06-06, #122). This is still an inert STIR
  front-door `Prop`, but the old "flat sorry keystone" provenance is stale:
  the downstream BCIKS20/Combine surface is now expressed through named,
  explicit residual hypotheses rather than hidden proof holes.

  Two independent blockers remain:

  1. STATEMENT DEFECT (free `GenFun`). As written, `GenFun : F → Fin m → F` is universally
     quantified with no constraint, so the statement is FALSE: instantiate `GenFun r j = 0`,
     then the combination `∑ⱼ GenFun r j * f j x ≡ 0 ∈ C`, so the hypothesis `Pr[… ≤ δ] = 1 >
     err'` holds for every `f`, yet arbitrary `fᵢ` need not agree with any codeword on a large
     set. The intended instance is the monomial / Vandermonde generator `GenFun r j = r^j`
     (cf. `RSGenerator.genRSC`, ProofSystem/Whir/ProximityGen.lean: `Gen = {r ↦ (j ↦ r^(exp j))}`,
     and `Generator.ProximityGenerator.proximity`, which is this exact statement specialised to
     that generator — itself still open). A faithful repair fixes `GenFun r j = r^j` (or adds
     a `ProximityGenerator`-style hypothesis on `GenFun`). This file has no consumers
     (`grep STIR.proximity_gap` ⇒ only its own definition), so the statement is currently inert.

  2. SOURCE residuals (Johnson/√ρ regime). Even the monomial instance reduces to BCIKS20
     Thm 1.5, `ProximityGap.correlatedAgreement_affine_curves`
     (Data/.../BCIKS20/Curves.lean), via
     `proximityError F degree ρ δ m = (m-1) * errorBound δ degree domain` and the
     degree-`(m-1)` curve `∑ᵢ rⁱ • fᵢ`. The current curve theorem is no longer a raw
     `sorry`: it is proved from the explicit residuals `StrictCoeffPolysResidual`
     (strict Johnson coefficient-polynomial extraction; owned by #7/#61) and
     `BoundaryProbabilityResidual` / older `BoundaryCardResidual` compatibility
     (closed square-root boundary; owned by #64/#7). `Combine.combine_theorem` likewise
     takes `StrictCoeffPolysResidual` as an explicit argument and routes through
     `correlatedAgreement_affine_curves_of_strict_coeff_polys`.

  Honest residual: repair this front door by specializing to the monomial generator and
  thread the current residual arguments (`StrictCoeffPolysResidual` plus the boundary
  branch when needed) through the BCIKS20 curve theorem / STIR combine layer. The
  statement-level STIR ownership remains #24; the correlated-agreement residual owners
  are #7/#61/#64. -/
def proximity_gap
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type} [Fintype ι] [Nonempty ι] {φ : ι ↪ F}
  {degree m : ℕ} {δ : ℝ≥0} {f : Fin m → ι → F} {GenFun : F → Fin m → F}
  -- Statement repair (verified defect): for an *arbitrary* `GenFun` the statement is FALSE —
  -- `GenFun r j = 0` makes the combined word `0 ∈ code` (a Submodule), so the probability
  -- hypothesis holds with probability 1 while the agreement conclusion fails for `f` far
  -- from the code. BCIKS20 Theorem 4.1 is about the power generator; pin `GenFun r j = r^j`.
  (_hGen : ∀ r j, GenFun r j = r ^ (j : ℕ))
  (_hδPos : 0 < δ)
  (_hδLt : δ < 1 - Bstar (LinearCode.rate (code φ degree)))
  (_hProb :
    Pr_{ let r ← $ᵖ F}[δᵣ((fun x => ∑ j : Fin m, (GenFun r j) * f j x), code φ degree) ≤ δ] >
      ENNReal.ofReal (proximityError F degree (LinearCode.rate (code φ degree)) δ m)) : Prop :=
  ∃ S : Finset ι,
    S.card ≥ (1 - δ) * (Fintype.card ι) ∧
    ∀ i : Fin m, ∃ u : ι → F, u ∈ (code φ degree) ∧ ∀ x ∈ S, f i x = u x

end STIR

/- Axiom audit for the STIR proximity-gap residual front door (#24). -/
#print axioms STIR.proximity_gap
