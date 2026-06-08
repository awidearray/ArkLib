# Issue #64 - exact lattice boundary frontier

**Status:** Open. The non-square endpoint, square endpoint API, lattice-data adapters, and
degenerate `k = 0` front doors have been packaged in source. The remaining work is still the
nonzero exact square-lattice combinatorics behind `BoundaryCardLatticeData` /
`BoundaryCardLatticeResidual`.

## Current Source Frontier

The exact boundary split lives in
`ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean`.

- `BoundaryCardStrictInteriorResidual`: strict-subradius producer for the non-lattice levels.
- `BoundaryCardLatticeResidual`: the genuine exact `1/n` lattice endpoint obligation.
- `BoundaryCardLatticeData`: the smaller concrete square-branch surface, asking for the two
  good-set cardinality bounds plus coefficient-polynomial extraction.
- `boundary_lattice_iff_isSquare_deg_mul_card`: arithmetic characterization of the endpoint:
  boundary-lattice iff `IsSquare (deg * Fintype.card iota)`.
- `boundaryCardResidual_of_not_isSquare_deg_mul_card` and
  `boundaryProbabilityResidual_of_not_isSquare_deg_mul_card`: non-square endpoints reduce to the
  strict-interior producer.
- `boundaryCardResidual_of_isSquare_deg_mul_card` and
  `boundaryProbabilityResidual_of_isSquare_deg_mul_card`: square endpoints consume only the
  isolated lattice residual.
- `boundaryCardLatticeResidual_zero` and `boundaryCardLatticeData_zero`: the exact-lattice branch is
  vacuous at `k = 0`.

The downstream adapters live in `ArkLib/ToMathlib/BoundaryDischarge.lean`.

- `boundaryCardLatticeResidual_of_lattice_data`: lowers the concrete data surface into the exact
  lattice residual.
- `BoundaryCardQuantizationData`: packages the strict-interior producer with concrete lattice data.
- `boundaryCardResidual_of_lattice_data_isSquare`,
  `boundaryProbabilityResidual_of_lattice_data_isSquare`, and
  `correlatedAgreement_affine_curves_of_lattice_data_isSquare`: square endpoint front doors from
  concrete lattice data.
- `boundaryCardResidual_zero`, `boundaryProbabilityResidual_zero`, and
  `correlatedAgreement_affine_curves_zero`: degenerate `k = 0` boundary calls are closed.

Affine-line callers that need the smaller data surface are already wired through
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean`.

## Exact Remaining Obligation

For `0 < k`, at the exact Johnson boundary

```lean
delta = 1 - ReedSolomon.sqrtRate deg domain
(Nat.floor (delta * Fintype.card iota) : NNReal) = delta * Fintype.card iota
```

and in the square endpoint case `IsSquare (deg * Fintype.card iota)`, prove the concrete data
needed by

```lean
BoundaryCardResidual.BoundaryCardLatticeData
```

or directly prove

```lean
BoundaryCardResidual.BoundaryCardLatticeResidual
```

The data route is the smaller target: for every nonempty `RS_goodCoeffsCurve`, prove the two
cardinality lower bounds and the coefficient-polynomial extraction that
`BoundaryDischarge.boundaryCardLatticeResidual_of_lattice_data` consumes. This is the genuine
BCIKS20 boundary Johnson-list combinatorics; it is not discharged by the arithmetic square/non-square
split alone.

## Focused Audit Commands

```sh
rg -n 'BoundaryCardLatticeData|BoundaryCardLatticeResidual|boundary_lattice_iff_isSquare_deg_mul_card|boundaryCardResidual_of_isSquare_deg_mul_card|boundaryCardResidual_of_not_isSquare_deg_mul_card' ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean
rg -n 'boundaryCardLatticeResidual_of_lattice_data|BoundaryCardQuantizationData|lattice_data_isSquare|correlatedAgreement_affine_curves_zero' ArkLib/ToMathlib/BoundaryDischarge.lean
rg -n 'lattice_data|BoundaryCardLatticeData|BoundaryCardLatticeResidual' ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean
lake build ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardResidual:olean ArkLib.ToMathlib.BoundaryDischarge:olean
```

## Good Next Bricks

- Prove source lemmas that turn square-endpoint nonemptiness of `RS_goodCoeffsCurve` into the two
  cardinality bounds required by `BoundaryCardLatticeData`.
- Prove the coefficient-polynomial extraction component of `BoundaryCardLatticeData` in the exact
  square endpoint, reusing the strict branch where the hypotheses genuinely match and avoiding any
  appeal to the already-goal-shaped `jointAgreement`.
- If the full data proof is still too large, split `BoundaryCardLatticeData` into named card-bound
  and coefficient-extraction subpredicates before proving either side.

## Shortcut To Avoid

Do not try to prove a blanket `BoundaryCardQuantizationData_zero` theorem as a k-zero vacuity
wrapper. `BoundaryCardQuantizationData` contains `BoundaryCardStrictInteriorResidual`, and that
strict-interior residual is not guarded by a `0 < k` hypothesis. The existing k-zero facts close the
cardinality, probability, curve-facing, lattice-residual, and lattice-data surfaces individually;
they do not make the full strict-plus-lattice quantization data package automatic at `k = 0`.
