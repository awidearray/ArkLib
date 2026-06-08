STATUS: CLOSED — stale `GrandChallengeMCAAttainment.lean` pointer repaired in place (no new module added). Regression check below returns zero hits.

# issue-55 — missing MCA-attainment counterpart: reference repaired, no module added

File: `ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeLDAttainment.lean`
Tracking issue: lalalune/ArkLib#55

## Finding

`GrandChallengeLDAttainment.lean` pointed readers to a module
`GrandChallengeMCAAttainment.lean` that never existed in the tree. The MCA-side
attainment/collapse argument was never a single file; it is the collapse/decision
file family.

## Disposition: repair the reference (chosen over adding a thin module)

A re-export module named `GrandChallengeMCAAttainment.lean` would duplicate an
already well-factored family and create a second naming scheme for the same
content. The docstring now points at the real locations:

* `GrandChallengeCollapse.lean` — MCA step-function collapse
  (`epsMCA_eq_of_floor_eq`) and degeneration to radius one
  (`grandMCAChallenge_iff_epsMCA_one`, `mcaPrize_iff_forall_epsMCA_one`) —
  the direct MCA analogue of `grandListDecodingChallenge_iff_Lambda_one_le`.
* `GrandChallengeRadiusOne.lean` / `GrandChallengeRadiusOneExact.lean` — the
  radius-one value `ε_mca(RS, 1)`, bracketed then pinned to `C(n, k+1)/|F|`.
* `GrandChallengeDecision.lean` — decision of the formal MCA prize predicate
  outside the explicit middle band of field sizes.
* `GrandChallengeResolutionWitness.lean` — witness-carrying `GrandMCAResolution`
  data objects in the large-field regime.

All lemma names cited in the repaired docstring were verified present in the
named files at close time.

## Regression check

The phantom module name must not reappear (as a reference or as a file):

```sh
rg -n 'GrandChallengeMCAAttainment' ArkLib docs            # expect: no hits
rg --files ArkLib/Data/CodingTheory/ProximityGap | rg 'MCAAttainment'   # expect: no hits
```

If a real MCA-attainment module is ever added, delete this note and update
`GrandChallengeLDAttainment.lean` to point at it.
