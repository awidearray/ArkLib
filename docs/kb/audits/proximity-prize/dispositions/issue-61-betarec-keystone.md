# Issue #61: betaRec-to-hcoeffPoly keystone assembly

This issue owns the final non-vacuous Proximity Prize integration gate:

```text
betaRec + Section 5 extraction data
  -> CurveCoeffPolys
  -> bundled hcoeffPoly
  -> BCIKS20 curve correlated agreement front door
```

## Current in-tree state

The current front-door assembly route is
`ArkLib.ToMathlib.CorrelatedAgreementListDecodingClosed`.

The key non-vacuous step is:

```lean
ArkLib.CorrelatedAgreementListDecodingClosed.curveCoeffPolys_of_section5Data
```

That theorem calls:

```lean
ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec
```

so the proof route consumes the real `betaRec` machinery, including the matching-set large-root
path through `tail_zero_of_betaRec_embedding_zero` and
`betaRec_embedding_eq_zero_of_matchingSet_large`. It does not assume a packaged conclusion
equivalent to the front-door `hcoeffPoly` witness.

There is now also an off-centre keystone route in:

```lean
ArkLib.ToMathlib.BetaToCurveCoeffPolysOffcentre
```

with the main declaration:

```lean
ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec_offcentre
```

This route replaces the centred-only `PowerSeries.subst (shiftSeries x0 H)` / `HasSubst` pair with
the local-variable series:

```lean
ArkLib.BetaToCurveCoeffPolys.gammaLocal
```

and proves the same `CurveCoeffPolys` conclusion from a representative identity against
`gammaLocal`. The proof is still load-bearing on `betaRec`: the truncation step is
`gammaLocal_eq_trunc_of_betaRec`, which routes through the same matching-set large-root path.

The bundling step is:

```lean
ArkLib.CorrelatedAgreementListDecodingClosed.hcoeffPoly_witness_of_section5Data
```

which turns the derived `CurveCoeffPolys` data into the `∃ B : ℕ -> Polynomial F` shape consumed by
the curve front door.

The off-centre route is also exposed at the `KeystoneStrictResidual` boundary:

```lean
ArkLib.KeystoneStrictResidual.hcoeffPoly_of_betaRec_offcentre
ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
ArkLib.KeystoneStrictResidual.hcoeffPoly_of_betaRecOffcentre
ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentre
ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_offcentre
ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_offcentre_strict
```

These declarations are API packaging over the same `gammaLocal` /
`curveCoeffPolys_of_betaRec_offcentre` proof route. They make the off-centre data surface reusable
at the coefficient-polynomial residual and correlated-agreement front doors, but they do not
construct the primitive Section 5 inputs.

## Remaining gate

The remaining work is not to prove another wrapper from an `hcoeffPoly`-shaped assumption. The live
gap is to wire the live Section 5 context into the genuine betaRec route:

- matching-point data and matching-set cardinality/weight bounds;
- either the existing centred `Section5StrictData` inputs at `x0 = 0`, or the off-centre
  `gammaLocal` representative input expected by `curveCoeffPolys_of_betaRec_offcentre`;
- the degree-X bound and decoded-family specialization bridge, stated against the truncated local
  representative in the off-centre route;
- the child #91 `hPz` supplier: `HPzBridge` already provides the abstract
  `HenselDatum -> hPz` and direct-identity landing pads, and `HenselDatumProducer` reduces the
  supplier surface to `SepHenselInput -> HenselDatum -> hPz`, with the matching-divisibility
  route now packaged as `MatchingDvdInput -> HenselDatum -> hPz`; the live Section 5 context still
  has to construct the per-`z` `SepHenselInput` or matching-divisibility witness, prove the degree
  bounds, and thread those witnesses through
  `GSFactorData.toSection5StrictData` / `BetaCurveInput` / `BetaCurveInputOffcentre`;
- the GS-factor divisibility input `Hlift H ∣ R`;
- the L13 betaRec drop-in for the legacy `β_regular` path.

The old `hsubst`/`hγ` fields are no longer the right off-centre target: the landed
`gammaLocal` route is the non-vacuous replacement for that F1 caveat. The per-coefficient polynomial
conclusion is still derived only after these Section 5 inputs exist.

## Anti-vacuity check

Do not replace the remaining gate with `Section55Output`, `hcoeffPoly`, or any structure that already
contains:

```lean
∀ P, ... -> ∃ B, ...
```

as a field. That reintroduces the F4 trap documented in `GRIND-LEDGER.md`.

The proof-gap index now points to #61 for this apex integration surface so the issue is not hidden
under local residual tickets.
