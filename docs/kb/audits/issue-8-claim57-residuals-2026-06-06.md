# Issue #8: Claim 5.7 residual surface

This note audits the current `Claim57Residuals` surface in the BCIKS20
list-decoding agreement stack. The legacy bundle lives in
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean`;
the newer discharge layers live in `ArkLib/ToMathlib/Claim57Supply.lean`,
`ArkLib/ToMathlib/Section5ConcreteJohnson.lean`, and
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Claim57FieldDischarge.lean`.
The descended-set replacement for the legacy factor surface lives in
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/DescendedRset.lean`.
The mathlib-only discriminant/separability bridge for the good-specialization side condition lives
in `ArkLib/ToMathlib/DiscriminantSeparable.lean`.

## Legacy Front Door

The legacy class still packages eight fields:

```lean
class Claim57Residuals (k : ℕ) (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) where
  hx0 : ∀ R ∈ pg_Rset h_gs, Bivariate.evalX (Polynomial.C x₀) R ≠ 0
  hsep : ∀ R ∈ pg_Rset h_gs, (Bivariate.evalX (Polynomial.C x₀) R).Separable
  hS_nonempty : (coeffs_of_close_proximity k ωs δ u₀ u₁).Nonempty
  A : coeffs_of_close_proximity k ωs δ u₀ u₁ → Finset (Fin n)
  hA : ∀ z i, i ∈ A z → (u₀ + z.1 • u₁) i = (Pz z.2).eval (ωs i)
  hcount : ∀ z, natWeightedDegree (eval_on_Z Q z.1) 1 k < m * (A z).card
  hlarge : #(coeffs_of_close_proximity k ωs δ u₀ u₁) / natDegreeY Q > ...
  hfactor : ∀ R ∈ pg_Rset h_gs,
    R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose
```

That class shape is still used by many downstream lemmas in `Agreement.lean`, but it is no longer
the minimal mathematical frontier.

## Discharge Layers

`Agreement.lean` exposes the first API reduction:

```lean
GraphExtractionHypotheses
Claim57Residuals.ofGraphExtractionHypotheses
exists_factors_with_large_common_root_set_of_graphExtraction
```

This moves `hx0`, `hsep`, `hS_nonempty`, `A`, `hA`, `hcount`, and `hlarge` into a proved
graph-extraction side-condition package. The only extra hypothesis at that front door is the
legacy factor-list bridge `hfactor`.

`Claim57Supply.lean` then makes the graph package non-circular by using the canonical
`matching_coords_for_z` agreement set:

```lean
graphExtractionHypotheses_of_johnson
graphExtractionHypotheses_of_natCeil_johnson
claim57Residuals_of_johnson
claim57Residuals_of_natCeil_johnson
```

At this layer, `A`/`hA` are canonical, `hS_nonempty` follows from `hlarge`, and `hcount` is narrowed
to the Johnson matching-coordinate or `⌈δ * n⌉` budget.

`Section5ConcreteJohnson.lean` narrows the Johnson side further:

```lean
hcount_natCeil_of_johnson_budget
claim57Residuals_of_gsInterpolant
```

It proves that `Z`-specialization does not raise the `(1, k)` weighted degree, so the per-`z`
`hcount` follows from one `z`-independent budget:

```lean
Bivariate.natWeightedDegree Q 1 k < m * (n - ⌈δ * (n : ℚ)⌉₊)
```

`Claim57FieldDischarge.lean` is the latest field-level brick:

```lean
claim57_hfactor_irreducible_of_pg_Rset
exists_good_x₀_evalX_discr_y_ne
exists_good_x₀_X_shape_ne
exists_good_x₀_X_shape
Claim57Residuals.ofInTree
Claim57Residuals.ofInTree2
```

It proves the honest irreducibility fragment of legacy `hfactor`, proves both the original
`Z`-shape and repaired `X`-shape avoidance producers for the specialization point, and assembles
the legacy bundle from the minimal current inputs.

`DescendedRset.lean` is now the preferred Claim 5.7 factor-set route:

```lean
pg_RsetDescended
pg_RsetDescended_hfactor
pg_RsetDescended_irreducible
pg_RsetDescended_separable_FF
pg_RsetDescended_natDegree_pos
pg_RsetDescended_discr_y_ne_zero
pg_RsetDescended_comp_dvd_Q
Claim57ResidualsDescended
Claim57ResidualsDescended.ofInTree
Claim57Residuals.ofDescended
exists_factors_with_large_common_root_set_of_descended
R_descended
H_descended
R_descended_mem_factorization
irreducible_H_descended
natDegree_H_descended_pos
fact_irreducible_H_descended
fact_natDegree_H_descended_pos
H_descended_dvd_evalX_R_descended
evalX_R_descended_separable
claimA2_hypotheses_descended
```

The descended bundle removes `hfactor` by construction: membership in `pg_RsetDescended` is
membership in the descended primitive-separable factor list. Legacy consumers can still recover
`Claim57Residuals` through `Claim57Residuals.ofDescended`, but only under the explicit coincidence
hypothesis `pg_RsetDescended = pg_Rset`. The new front door and projections then expose the
Claim-5.7 factors and Claim-A.2 hypotheses from that descended bundle. The `Fact` helpers package
`Irreducible H_descended` and `0 < H_descended.natDegree` for downstream Appendix-A / beta-rec
consumers that expect typeclass facts around the extracted `H`.

`DiscriminantSeparable.lean` supplies the mathlib-level payoff bridge for the `hx0` / `hsep`
side condition:

```lean
Polynomial.discr_map_of_natDegree_preserved
Polynomial.separable_of_discr_ne_zero
Polynomial.ne_zero_and_separable_of_specialized_discr_ne_zero
Polynomial.ne_zero_and_separable_of_specialized_base_discr_ne_zero
```

This proves that nonvanishing specialized discriminant data gives both nonzero specialized factors
and separability, provided the specialization preserves `natDegree`. It deliberately stays out of
the `CompPoly` `discr_y` / `evalX` stack while that layer is under repair.

## Current Minimal Surface

After the current discharge layers, the recommended descended-set path has this remaining
Claim 5.7 proof surface:

| Field | Current status |
| --- | --- |
| `hx0` / `hsep` | `hx0` is produced on both the legacy and descended routes by the `X`-shape avoidance lemmas (`exists_good_x₀_X_shape_ne`, `exists_good_x₀_X_shape_ne_descended`). The remaining separability input is the honest per-point residual `hsepPt` used by `Claim57ResidualsDescended.ofInTree`. |
| `hJohnson` | The single Johnson weighted-degree budget feeding `hcount_natCeil_of_johnson_budget`; not a class field, but still an explicit input to `claim57Residuals_of_gsInterpolant` and `Claim57Residuals.ofInTree`. |
| `hlarge` | The close-set largeness / field-size budget input. It also derives `hS_nonempty`. |
| `hfactor` | Removed on the `Claim57ResidualsDescended` path. The legacy `pg_Rset` field remains unprovable in full generality because `pg_Rset` is built from `normalizedFactors Q`, while the Eq. 5.12 list contains descended primitive-separable factors. Use `Claim57Residuals.ofDescended` only under the explicit coincidence hypothesis. |

The fields `A`, `hA`, `hcount`, and `hS_nonempty` are not the active residual surface anymore:
they are discharged through `Claim57Supply.lean` and `Section5ConcreteJohnson.lean` once the
minimal inputs above are provided.

## Remaining Downstream Surface

Most later Claim 5.7 / Claim 5.8 lemmas in `Agreement.lean` still carry the legacy class:

```lean
[Claim57Residuals (F := F) k δ x₀ h_gs]
```

The useful downstream cleanup is to route new consumers through
`Claim57ResidualsDescended.ofInTree`, the descended projections, and the local `Fact` helpers, then
use `Claim57Residuals.ofDescended` only at legacy boundaries that still need the old class under an
explicit coincidence hypothesis.

## Verification Status

This audit was checked against the current anchors:

- `Claim57Residuals`
- `GraphExtractionHypotheses`
- `Claim57Residuals.ofGraphExtractionHypotheses`
- `exists_factors_with_large_common_root_set_of_graphExtraction`
- `graphExtractionHypotheses_of_johnson`
- `claim57Residuals_of_gsInterpolant`
- `hcount_natCeil_of_johnson_budget`
- `claim57_hfactor_irreducible_of_pg_Rset`
- `exists_good_x₀_evalX_discr_y_ne`
- `exists_good_x₀_X_shape_ne`
- `exists_good_x₀_X_shape`
- `Claim57Residuals.ofInTree`
- `Claim57Residuals.ofInTree2`
- `pg_RsetDescended`
- `pg_RsetDescended_hfactor`
- `Claim57ResidualsDescended`
- `Claim57ResidualsDescended.ofInTree`
- `Claim57Residuals.ofDescended`
- `exists_factors_with_large_common_root_set_of_descended`
- `R_descended`
- `H_descended`
- `R_descended_mem_factorization`
- `irreducible_H_descended`
- `natDegree_H_descended_pos`
- `fact_irreducible_H_descended`
- `fact_natDegree_H_descended_pos`
- `H_descended_dvd_evalX_R_descended`
- `evalX_R_descended_separable`
- `claimA2_hypotheses_descended`
- `Polynomial.discr_map_of_natDegree_preserved`
- `Polynomial.separable_of_discr_ne_zero`
- `Polynomial.ne_zero_and_separable_of_specialized_discr_ne_zero`
- `Polynomial.ne_zero_and_separable_of_specialized_base_discr_ne_zero`

This refresh was docs-only and anchor-checked against current `fork/main`; no broad Lean build was
run for this audit update.

## Resolution (2026-06-07) — issue #8 closed

The Claim 5.7 residual bundle is closed to its **minimal honest surface**. The whole Section 5
chain is `sorry`-free, `admit`-free, and `axiom`-free; the per-declaration `#print axioms`
directives at the foot of `Claim57FieldDischarge.lean` and `DescendedRset.lean` enforce that every
anchor rests only on `[propext, Classical.choice, Quot.sound]`. The four acceptance criteria of
issue #8 map to discharging anchors as follows:

| Acceptance criterion | Status | Discharging anchor(s) |
| --- | --- | --- |
| 1. Prove the graph/count data (per-`z` graph vanishing/count for `hcount`) from `ModifiedGuruswami` | **Met** | `A`/`hA`/`hcount`/`hS_nonempty` are proved upstream from the single Johnson budget via `graphExtractionHypotheses_of_johnson`, `claim57Residuals_of_gsInterpolant`, and `hcount_natCeil_of_johnson_budget` (the `Z`-specialization never raises the `(1,k)` weighted degree). |
| 2. Put `hlarge` in the correct hypothesis position (not a false off-regime conclusion) | **Met** | `hlarge` is a *hypothesis* (the BCIKS20 "many close codewords" regime antecedent); `coeffs_of_close_proximity_nonempty_of_large_natdiv` derives `hS_nonempty` from it. |
| 3. Prove `hfactor`, or remove the legacy factorization-list dependency | **Met (removed)** | `pg_RsetDescended_hfactor` makes the factor-list membership a *theorem* by construction (`Finset.mem_toFinset`); the descended route carries no `hfactor` hypothesis. The honestly-provable legacy fragment is `claim57_hfactor_irreducible_of_pg_Rset`. |
| 4. Replace the `[Claim57Residuals]` typeclass in downstream consumers with proved data or smaller residuals | **Met** | The hfactor-free `Claim57ResidualsDescended` bundle plus a complete parallel output interface — `R_descended`, `H_descended`, `irreducible_H_descended` (+`fact_`), `natDegree_H_descended_pos` (+`fact_`), `H_descended_dvd_evalX_R_descended`, `evalX_R_descended_separable`, `commonRootSet_descended_card_ge`, `claim57_largeness_descended`, `claimA2_hypotheses_descended` — gives every downstream consumer a smaller-residual route. End-to-end in-tree packages: `exists_factors_with_large_common_root_set_of_descended_inTree`, `claimA2_hypotheses_descended_inTree`, `claim57_descended_inTree_package`. Legacy `pg_Rset` consumers (Claims 5.8–5.11) are reachable from the descended bundle via `Claim57Residuals.ofDescended` under the explicit coincidence hypothesis. |

### Irreducible residuals (genuine antecedents, not proof gaps)

What remains as named hypotheses is **mathematically irreducible** — these are the antecedents of
BCIKS20 Claim 5.7 itself (or facts that are false in positive characteristic), and cannot be
discharged without weakening a statement or laundering a `sorry`:

- `hJohnson` (`natWeightedDegree Q 1 k < m·(n − ⌈δ·n⌉)`) — the Johnson-radius parameter regime;
  provably independent of `ModifiedGuruswami`, an input to the claim, not a consequence.
- `hlarge` (close-set cardinality) — the "many close codewords" regime; the second conjunct of
  Claim 5.7, `R,H`-independent.
- `hsepPt` — domain-level separability over `F[Z]`, strictly stronger than discriminant
  nonvanishing (it needs a unit derivative-resultant, exposed by
  `separable_evalX_of_resultant_isUnit`); the honest residual matching the F8/F10 precedents.
- the coincidence `pg_RsetDescended = pg_Rset` — the legacy-only bridge that is structurally false
  in characteristic `p` (normalized factors vs descended primitive-separable factors); required
  only when re-entering the legacy `pg_Rset` chain.

Discharging `hlarge`/`hJohnson` for a concrete deployment is the §6 curve→close-set probability
bridge tracked separately (issues #22/#24); the Appendix-A Hensel inputs feeding Claims 5.8–5.9 are
issue #9. Neither is part of the Claim 5.7 residual bundle, so issue #8 is closed.
