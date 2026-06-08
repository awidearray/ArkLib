# Issue #7 BCIKS20 Correlated-Agreement Residual Narrowing

Date: 2026-06-06

Scope:

- `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean`

## Current narrowed surface

Remote main now narrows the issue #7 front door in
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean`.

The strict Johnson branch previously exposed only the broad residual
`StrictCoeffPolysResidual`, which asks for coefficient-polynomial witnesses for
every decoded selector `P` on `RS_goodCoeffsCurve`.

The current source adds the smaller named obligation
`StrictCanonicalCoeffPolysResidual`. It asks for:

1. one canonical decoded family `P₀`,
2. coefficient-polynomial witnesses for that canonical family, and
3. uniqueness of decoded families on the good-coefficient set.

The bridge theorem
`strictCoeffPolysResidual_of_strictCanonicalCoeffPolysResidual` proves that this
canonical obligation implies the existing broad residual by reusing the in-tree
`coeff_polys_for_all_decoded_of_canonical_agreement` lemma.

The boundary branch is also narrowed by `BoundaryProbabilityResidual`, which
retains the probability and Johnson-side hypotheses available at the branch
point. The compatibility theorem
`boundaryProbabilityResidual_of_boundaryCardResidual` shows the older
`BoundaryCardResidual` implies this sharper boundary residual.

The front-door wrapper
`correlatedAgreement_affine_curves_of_strictCanonicalCoeffPolysResidual` proves
the curve correlated-agreement theorem from:

- `StrictCanonicalCoeffPolysResidual`, and
- `BoundaryProbabilityResidual`.

## Why this narrows the work

The remaining strict-branch proof can now target the canonical decoded-family
data produced by the Section 5 / Berlekamp-Welch / Polishchuk-Spielman pipeline,
instead of proving coefficient-polynomial extraction separately for every
decoded selector. The universal selector form remains available for downstream
compatibility, but it is no longer the only public residual interface.

## Remaining residuals

1. Prove `StrictCanonicalCoeffPolysResidual` from the in-tree Section 5
   extraction material.
2. Prove `BoundaryProbabilityResidual` directly, or continue using
   `BoundaryCardResidual` through the compatibility theorem while a direct
   boundary proof is developed.
3. Once those two are closed, remove the conditional residual arguments from
   `correlatedAgreement_affine_curves`.

This does not complete BCIKS20 Theorem 1.5. It reduces the strict-branch API to
the canonical mathematical data already present in the surrounding assembly
theorems and leaves a smaller, named proof target.
