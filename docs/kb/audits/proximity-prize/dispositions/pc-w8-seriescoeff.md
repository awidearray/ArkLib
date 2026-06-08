STATUS: COMPLETE — both theorems proven (existence + uniqueness), compile exit 0, in-file axiom audit clean

# PC-W8 — Application-shaped Hensel: series-coefficient polynomials (BCIKS20 App. A.4)

## Goal

Generalize the proven abstract Hensel of `HenselExistence.lean` (polynomial `P : R[X]` with
*constant* coefficients in `R`) to the **BCIKS20-application shape**: the polynomial whose root we
lift already has **power-series coefficients**,

  `Q : Polynomial R⟦X⟧`,

with root data prescribed only at **order 0** via the reduction `Q₀ := Q.map constantCoeff : R[X]`.

## Result

New file (mathlib-only imports), compiles `lake env lean` exit 0, no warnings:

  `/home/shaw/ethereumroadmap/upstream/lean-research/ArkLib/ArkLib/Data/Polynomial/HenselSeriesCoeff.lean`
  namespace `ProximityPrize.HenselSeriesCoeff`

Both target theorems proven:

* **EXISTENCE** — `exists_powerSeries_root_seriesCoeff`:
  for `Q : Polynomial R⟦X⟧`, if `eval c Q₀ = 0` and `IsUnit (eval c (derivative Q₀))` then
  `∃ γ : R⟦X⟧, constantCoeff γ = c ∧ Polynomial.eval γ Q = 0`.

* **UNIQUENESS** — `root_unique_seriesCoeff`:
  two roots `γ₁ γ₂` of `Q` with `constantCoeff γ₁ = constantCoeff γ₂` and
  `IsUnit (eval (constantCoeff γ₁) (derivative Q₀))` are equal.

The evaluation primitive is plain `Polynomial.eval γ Q` (NOT `aeval`/`eval₂`): `Q`'s coefficients
already live in `R⟦X⟧`, the same ring as `γ`, so `eval` is the right and cleanest map. Confirmed
mathlib names used: `PowerSeries.constantCoeff` (a `RingHom`), `Polynomial.map`,
`Polynomial.coeff_map`, `Polynomial.natDegree_map_le`, `Polynomial.eval_eq_sum_range[']`,
`Polynomial.derivative_eval`, `Polynomial.sum_over_range'`, `PowerSeries.coeff_mul`.

## Method — the new ingredient is the generalized linearization (convolution)

The order-`t` coefficient of `eval γ Q` is a CONVOLUTION over each coefficient series:

  `coeff t (eval γ Q) = ∑ᵢ ∑_{a+b=t} coeff a (Q.coeff i) · coeff b (γ^i)`   (`coeff_eval_eq_sum_range`).

(i) **Truncation propagation** (`coeff_pow_sub_below`, LEMMA A — transfers verbatim from the asset;
it is purely about powers of one series).

(ii) **Order-`t` linearization** (`coeff_eval_sub_at`): comparing `γ₁,γ₂` agreeing below order `t`
(`0 < t`), LEMMA A kills every antidiagonal pair with `b < t`, so ONLY the corner `(a,b)=(0,t)`
survives each convolution difference. The surviving `a=0` factor is
`coeff 0 (Q.coeff i) = constantCoeff (Q.coeff i) = Q₀.coeff i`, a *constant*. The convolution thus
collapses to exactly the constant-coefficient linearization of `HenselExistence`, but against `Q₀`:

  `coeff t (eval γ₁ Q) − coeff t (eval γ₂ Q) = eval c (derivative Q₀) · (coeff t γ₁ − coeff t γ₂)`.

The power difference is `coeff_pow_sub_at` (LEMMA B, transfers verbatim), and the reindexing
`∑ᵢ Q₀.coeff i · i · c^{i-1} = eval c (derivative Q₀)` is the same `derivative_eval` +
`sum_over_range'` finish as the asset, applied to `Q₀`.

Watch (handled): degree mismatch `natDegree Q₀ ≤ natDegree Q` — both `coeff_eval_sub_at` and
`constantCoeff_eval` index over the COMMON range `range (Q.natDegree+1)` (padded for `Q₀` via
`eval_eq_sum_range'`, since the extra `Q₀` coefficients are zero). The derivative-vs-`Q₀` interplay
is via `coeff_Q₀ : (Q₀ Q).coeff i = constantCoeff (Q.coeff i)` (i.e. `Polynomial.coeff_map`);
`Polynomial.derivative_map` was available as a fallback but the direct `derivative_eval` route on
`Q₀` sufficed without commuting `derivative` through `map`.

(iii) **Newton recursion + vanishing** (`S`, `coeff_S_*`, `γ`, `coeff_zero_eval_γ`,
`coeff_succ_eval_γ`, `eval_γ_eq_zero`): VERBATIM the `HenselExistence` construction with `aeval … P`
replaced by `eval … Q` and `eval c P'` replaced by `eval c (derivative Q₀)`. Order-0 vanishing uses
`constantCoeff_eval : constantCoeff (eval γ Q) = eval (constantCoeff γ) Q₀`.

## Declarations (all proven, sorry-free)

LEMMA A/B (local restatements): `coeff_pow_sub_below`, `coeff_pow_sub_at`.
Reduction: `Q₀`, `coeff_Q₀`, `natDegree_Q₀_le`.
Convolution + linearization: `coeff_eval_eq_sum_range`, `coeff_eval_sub_at`, `constantCoeff_eval`.
Newton machinery: `S`, `coeff_S_succ_of_le`, `coeff_S_eq_zero_of_lt`, `coeff_S_stable`, `γ`,
`coeff_γ`, `constantCoeff_γ`, `coeff_γ_eq_S`.
Vanishing: `coeff_zero_eval_γ`, `coeff_succ_eval_γ`, `eval_γ_eq_zero`.
Main: `exists_powerSeries_root_seriesCoeff` (existence), `root_unique_seriesCoeff` (uniqueness).

## Axiom audit (in-file, run on a temp copy then removed)

`#print axioms` on `exists_powerSeries_root_seriesCoeff`, `root_unique_seriesCoeff`,
`coeff_eval_sub_at`, `constantCoeff_eval`, `eval_γ_eq_zero`, `coeff_eval_eq_sum_range`:
each depends ONLY on `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `native_decide`,
no `Lean.ofReduceBool`. (`Classical.choice` enters via `Ring.inverse`/`Nat.find`/`PowerSeries.ext`;
expected and benign.)

## Residual

NONE for this task. Both theorems are proven outright (acceptance level (a)). The lemmas
`coeff_pow_sub_below` / `coeff_pow_sub_at` are local restatements of on-branch assets
(`NewtonLinearization.lean`) reproven line-for-line because their `olean`s are not prebuilt in this
worktree and they are stated for `R[X]`, not `R⟦X⟧[X]` — flagged as dedupe targets if/when the
worktree olean graph is rebuilt and a shared `R⟦X⟧[X]` namespace is consolidated. This file feeds
the BCIKS20 App. A.4 quotienting argument (P2 path), where the polynomial-in-Z whose simple order-0
root must be lifted to `R⟦X⟧` genuinely has power-series coefficients.
