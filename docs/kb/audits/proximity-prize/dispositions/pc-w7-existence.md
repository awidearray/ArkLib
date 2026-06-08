STATUS: PROVEN — Hensel-root EXISTENCE for power series, by explicit Newton construction (mathlib-only, axiom-clean)

# Hensel-root existence for `R⟦X⟧` (existence half of abstract Hensel)

File: `upstream/lean-research/ArkLib/ArkLib/Data/Polynomial/HenselExistence.lean`
(`lalalune/main` at ArkLib commit `c8a6a6d56`). Compiles
`lake env lean … HenselExistence.lean` → exit 0,
sorry-free, axiom audit `[propext, Classical.choice, Quot.sound]` only.

## Result

```
theorem exists_powerSeries_root {R} [CommRing R] {P : Polynomial R} {c : R}
    (hc0 : Polynomial.eval c P = 0)
    (hu  : IsUnit (Polynomial.eval c (Polynomial.derivative P))) :
    ∃ γ : R⟦X⟧, constantCoeff γ = c ∧ Polynomial.aeval γ P = 0
```

This is the EXISTENCE companion to the in-tree UNIQUENESS lemma
`NewtonLinearization.aeval_root_unique`. Together they give the full abstract Hensel
statement for `R⟦X⟧`: a *simple* root `c` of `P` over `R` (`eval c P = 0`,
`IsUnit (eval c P')`) lifts **uniquely** to a root of `P` over `R⟦X⟧`. The statement is the
strong/general one requested: arbitrary `CommRing R`, no locality, `P` not assumed monic,
exact root (not just residue-field).

## STEP 0 (scout): is it already in mathlib? — NO usable instance.

- `Mathlib/RingTheory/Henselian.lean` is the ONLY file referencing `HenselianLocalRing` /
  `HenselianRing`. There is **no** `instance … HenselianLocalRing R⟦X⟧` and **no**
  `instance … IsAdicComplete (Ideal.span {X}) R⟦X⟧` anywhere in mathlib (greps below).
  So both abstract routes (`HenselianLocalRing` and `IsAdicComplete.henselianRing`) are
  dead — no instance fires.
- Even if an instance existed, `HenselianLocalRing.is_henselian` requires `[IsLocalRing R]`,
  `f.Monic`, and only `f.eval a₀ ∈ maximalIdeal` (a residue-field/approximate root) — a
  strictly weaker and different setting than the exact `eval c P = 0` over an arbitrary
  `CommRing`. Not derivable cheaply from the mathlib API for our hypotheses.
- `WeierstrassPreparation.lean` exists but is the wrong tool (factorization, not Hensel lift).

Greps: `grep -rln HenselianLocalRing Mathlib/` → only `Henselian.lean`;
`grep -rln "IsAdicComplete.*PowerSeries|PowerSeries.*IsAdicComplete" Mathlib/` → empty.

## STEP 1 (route used): explicit Newton construction.

Let `A := eval c P'`, `u := Ring.inverse A` (`A * u = 1` via `Ring.mul_inverse_cancel`).

Partial-sum sequence by ORDINARY structural recursion (no strong recursion / WF gymnastics —
the cleaner design):
```
S 0      := PowerSeries.C c
S (t+1)  := S t + PowerSeries.monomial (t+1) (-u * coeff (t+1) (aeval (S t) P))
```
- `coeff_S_succ_of_le` : adding the order-(t+1) monomial leaves coeffs ≤ t fixed.
- `coeff_S_eq_zero_of_lt` : `S t` is supported on `[0,t]` (coeff j (S t) = 0 for t < j).
- `coeff_S_stable` : `coeff j (S t) = coeff j (S j)` for `j ≤ t` (diagonal is reached and
  frozen).

Diagonalise: `γ := mk (fun t => coeff t (S t))`. Then `coeff j γ = coeff j (S t)` for all
`j ≤ t` (`coeff_γ_eq_S`), so γ agrees with `S t` below order `t+1`, and
`constantCoeff γ = c` (`constantCoeff_γ`).

Order-by-order vanishing of `aeval γ P`:
- order 0 (`coeff_zero_aeval_γ`): `constantCoeff (aeval γ P) = eval (constantCoeff γ) P
  = eval c P = 0`, via the local `constantCoeff_aeval_powerSeries`.
- order t+1 (`coeff_succ_aeval_γ`): the Newton linearization `coeff_aeval_sub_at`
  (P'(c)-linear response) applied to (γ, S t), which agree below t+1, gives
  `coeff(t+1)(aeval γ P) − w = A·(coeff(t+1) γ − 0)` where `w := coeff(t+1)(aeval (S t) P)`.
  By construction `coeff(t+1) γ = coeff(t+1)(S(t+1)) = -u·w`, so the RHS `= A·(-u·w) = -w`,
  forcing `coeff(t+1)(aeval γ P) = w + (-w) = 0`. (Uses `A·u = 1`, i.e. the simple-root unit.)
- `aeval_γ_eq_zero` : `PowerSeries.ext` + the two cases ⇒ `aeval γ P = 0`.

## Self-containment

The asset oleans (`NewtonLinearization`, `GammaSubstObstruction`) are NOT prebuilt in this
worktree (`import` resolves the module but the decls are absent — stale/unbuilt olean), so
the four facts consumed are restated and reproven locally (namespace `HenselExistence`),
line-for-line the asset proofs: `coeff_aeval_eq_sum_range`, `coeff_pow_sub_below`,
`coeff_pow_sub_at`, `coeff_aeval_sub_at`, `constantCoeff_aeval_powerSeries`. The file imports
only mathlib. When the asset oleans are rebuilt, these locals can be replaced by `import` +
the originals with zero proof change.

## Declarations (all axiom-clean: [propext, Classical.choice, Quot.sound])

Assets (local restatements): `coeff_aeval_eq_sum_range`, `coeff_pow_sub_below`,
`coeff_pow_sub_at`, `coeff_aeval_sub_at`, `constantCoeff_aeval_powerSeries`.
Construction: `S`, `coeff_S_succ_of_le`, `coeff_S_eq_zero_of_lt`, `coeff_S_stable`, `γ`,
`coeff_γ`, `constantCoeff_γ`, `coeff_γ_eq_S`.
Vanishing + flagship: `coeff_zero_aeval_γ`, `coeff_succ_aeval_γ`, `aeval_γ_eq_zero`,
`exists_powerSeries_root`.

## Residual

NONE for the stated theorem — existence is fully proven (outcome (a)). Only cosmetic
follow-up: once the asset oleans are rebuilt, dedupe the 5 locally-restated lemmas against
their originals (mechanical, no math residual).
