STATUS: COMPLETE — targets 1, 2, 3 PROVEN + stretch (4) uniqueness PROVEN; compile exit 0; in-file axiom audit clean (no sorryAx)

# P2 instantiation: the genuine Hensel-lifted root γ in the BCIKS20 setting

File: `upstream/lean-research/ArkLib/ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean`
(`lalalune/main`, upstream ArkLib source-of-truth checkout)
Namespace: `ProximityPrize.BCIKS20.GammaGenuine`

## What this is

This is the mathematical content of `βHensel_lift_identity`'s frontier: the genuine
power-series root `γ : (𝕃 H)⟦X⟧` of [BCIKS20] App. A.4, produced directly via the
application-shaped Hensel theorem of `HenselSeriesCoeff.lean`, replacing the degenerate
`ClaimA2.γ` (which is built on the vacuous `β = 0` numerator and fails `HasSubst` for `x₀ ≠ 0`,
per the honesty notes at `β_regular` and in `GammaSubstObstruction.lean`).

## The construction (target 1) — the X-recentered Y-polynomial of R

`R : F[X][X][Y] = Polynomial (Polynomial (Polynomial F))`; outer→inner layers are
Y (algebraic variable solved for), X (lift/local variable specialized at x₀), Z (function-field
variable lifted into `𝕃 H`). Per-Y-coefficient ring hom (each factor is a genuine `RingHom`, so
the composite and `R.map` of it are honest):

  `coeffHom x₀ H : F[X][Y] →+* (𝕃 H)⟦X⟧`
     := coeToPowerSeries.ringHom ∘ mapRingHom liftToFunctionField ∘ (taylorAlgHom (C x₀))

  `Q x₀ R H : Polynomial ((𝕃 H)⟦X⟧) := R.map (coeffHom x₀ H)`

The X-layer is recentered by `Polynomial.taylor (C x₀)` (the faithful, HasSubst-free fix from
`GammaSubstObstruction.lean`); X is read as the power-series variable via
`Polynomial.coeToPowerSeries.ringHom`; Z-coefficients are lifted by `liftToFunctionField`.
Coefficient lemmas: `coeff_coeffHom`, `constantCoeff_coeffHom`.

## The order-0 data (target 2)

`α₀ H := functionFieldT / liftToFunctionField H.leadingCoeff : 𝕃 H` (the base root T/W).

`Q₀_eq`: `HenselSeriesCoeff.Q₀ (Q x₀ R H) = (Bivariate.evalX (C x₀) R).map liftToFunctionField`
  — because `constantCoeff` reads the X = x₀ Taylor constant term (`taylor_coeff_zero`:
  coeff 0 = eval at x₀), and that is exactly the X-specialization R(x₀,Y,Z) lifted.

`eval_α₀_derivative_Q₀`: `eval α₀ (derivative Q₀) = ζ R x₀ H` (derivative commutes with map;
  matches the in-tree definition of ζ exactly).

- `eval_α₀_Q₀_eq_zero` (ROOT): from `Hypotheses.dvd_evalX` (H ∣ evalX (C x₀) R) write
  evalX (C x₀) R = H·g; then `eval₂ α₀ (H·g) = (eval₂ α₀ H)·(eval₂ α₀ g) = 0·… = 0` using the
  base-root lemma `eval₂_liftToFunctionField_div_leadingCoeff_H_eq_zero` (RationalFunctions ~1772).
- `isUnit_eval_α₀_derivative_Q₀` (SIMPLICITY): in the field 𝕃 H, `IsUnit x ↔ x ≠ 0`
  (`isUnit_iff_ne_zero`); nonvanishing of `eval α₀ (derivative Q₀) = ζ` is
  `Separable.eval₂_derivative_ne_zero` applied to `Hypotheses.separable_evalX` at the root α₀.

## MAIN (target 3) + stretch (target 4)

- `gammaGenuine x₀ R H hHyp : (𝕃 H)⟦X⟧` :=
    `(HenselSeriesCoeff.exists_powerSeries_root_seriesCoeff
        (eval_α₀_Q₀_eq_zero hHyp) (isUnit_eval_α₀_derivative_Q₀ hHyp)).choose`
- `gammaGenuine_constantCoeff`: `constantCoeff (gammaGenuine …) = α₀ H`  (lifts the base root)
- `gammaGenuine_root`: `Polynomial.eval (gammaGenuine …) (Q x₀ R H) = 0`
    — THE genuine relation R(X, γ, Z) = 0 in (𝕃 H)⟦X⟧ (X the recentered local variable).
- `gammaGenuine_unique` (stretch): any root γ' of Q with `constantCoeff γ' = α₀` equals
    `gammaGenuine`, via `HenselSeriesCoeff.root_unique_seriesCoeff` at the simple root α₀.

## Verification

- Compile ONLY this file: `cd /home/shaw/ethereumroadmap/upstream/lean-research/ArkLib && export PATH=$HOME/.elan/bin:$PATH &&
  timeout 1800 lake env lean ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean`
  → exit 0, no errors, no warnings.
- In-file axiom audit (run on a temp copy with `#print axioms` for all 15 decls, then removed):
  every declaration depends only on `[propext, Classical.choice, Quot.sound]`. No `sorryAx`,
  no `native_decide` / `Lean.ofReduceBool`, no `admit`/`bv_decide`. The committed file contains
  no axiom statements.
- Both upstream assets imported directly (oleans prebuilt in this worktree):
  `HenselSeriesCoeff` (Hensel existence/uniqueness) and `RationalFunctions`
  (`𝕃`, `liftToFunctionField`, `functionFieldT`, base-root lemma, `ζ`, `ClaimA2.Hypotheses`).
  No dedupe/restate needed.

## Residual / honest scope

NONE for the stated P2 instantiation: the genuine γ, its order-0 lift to α₀, the genuine root
relation R(X,γ,Z)=0, and uniqueness are all proven and kernel-checked.

Out of scope (not part of this task; pre-existing frontier elsewhere on the P2 chain): connecting
`gammaGenuine` BACK to the existing `ClaimA2.α`/`ClaimA2.γ` (which are anchored to the vacuous
`β_regular = 0` stub). Those defs would have to be re-anchored to genuine recursive Hensel data —
or downstream callers re-pointed at `gammaGenuine` — to make the §5 weight/numerator chain
(Claims 5.8/5.8'/5.9, `embeddingOf𝒪Into𝕃 (β t) = α_t·W^{t+1}·ξ^{e_t}`) reference a non-vacuous
object. This file supplies the genuine root that such a re-anchoring would target; the
re-anchoring itself is owner-integration, not a formalizable gap.

## Declarations (15)

α₀, eval₂_H_α₀, coeffHom, Q, coeff_coeffHom, constantCoeff_coeffHom, Q₀_eq, eval_α₀_Q₀,
eval_α₀_derivative_Q₀, eval_α₀_Q₀_eq_zero, isUnit_eval_α₀_derivative_Q₀, gammaGenuine,
gammaGenuine_constantCoeff, gammaGenuine_root, gammaGenuine_unique.
Axioms (all): [propext, Classical.choice, Quot.sound].
