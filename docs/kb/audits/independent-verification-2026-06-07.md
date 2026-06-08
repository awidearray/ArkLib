# Independent Verification Dossier — ArkLib

- **Commit audited:** `35cc5177`
- **Toolchain:** `leanprover/lean4:v4.30.0-rc2`
- **Date:** 2026-06-07
- **By:** NubsCarson (clean-room rebuild: fresh `elan`, `lake exe cache get`, full `lake build`)

## TL;DR

On a from-scratch checkout, every headline result is **machine-checked clean**:

| Check | Result |
|---|---|
| Flagship `#print axioms` (17 theorems) | **17/17 reduce to only `{propext, Classical.choice, Quot.sound}`** (one to **none**); 0 residual-backed |
| Sorry / proof-hole census (whole tree) | **`holes: 0`** (368 `sorry` tokens are all documentation mentions in comments) |
| Forbidden-token scan | **clean** — no `native_decide` / `bv_decide` / undocumented axioms |
| Custom axioms | **10, every one explicitly declared + documented**, isolated in 2 leaf files (`CapacityBoundsProofs.lean`, `Leaderboard.lean`) that **no flagship imports** |

## Reproduce it yourself

```bash
git checkout 35cc5177
lake exe cache get
python3 scripts/axiom_audit.py        # -> "axiom audit: all 17 flagship declarations clean"
python3 scripts/sorry_census.py --root .   # -> holes: 0
python3 scripts/forbidden_tokens.py        # -> clean (10 allowlisted residual axioms)
```

## Flagship axiom results

All of the following print only `{propext, Classical.choice, Quot.sound}` (or fewer):

- `ProximityGap.proximity_gap_RSCodes`
- `ProximityGap.correlatedAgreement_affine_curves`
- `ProximityGap.RS_correlatedAgreement_affineLines`
- `ProximityGap.not_listDecodingPrize`, `ProximityGap.grandMCAChallenge_iff_epsMCA_one`
- `ProximityGap.GrandChallengesLattice.mcaThreshold_spec`
- `KZG.CommitmentScheme.correctness`, `KZG.CommitmentScheme.map_binding_to_t_sdh_of_two_valid_openings`
- `InductiveMerkleTree.opening_binding` (**zero axioms — fully constructive**), `InductiveMerkleTree.extracted_leaf_unique`
- `BerlekampWelch.decoder_eq_some`
- `JohnsonBound.johnson_condition_weak_implies_strong`
- `ProximityPrize.HenselExistence.exists_powerSeries_root`
- `GSListSizeBound.gs_list_size_bound`, `BKR06.subspacePoly_natDegree`, `BKR06.bkr06_tight_family_hfamily_unconditional`
- `CodingTheory.large_alphabet_barrier_bdg24_agl23`

## Honest scope — what this DOES and does NOT claim

**DOES:** certify that the 17 headline proofs are *valid Lean*, kernel-reducible to the three standard axioms, with **no `sorry`** and **no dependence on any placeholder/residual axiom**. This is the kernel itself certifying the proofs are real — not a self-report.

**DOES NOT** claim the Proximity Prize is *closed*. Several flagships (e.g. `proximity_gap_RSCodes`) are **conditional** on an explicit residual hypothesis (`StrictCoeffPolysResidual`) — proven honestly as "if `H` then conclusion," where `H` is the deep BCIKS20 §5 coefficient-polynomial extraction still being formalized. A conditional theorem is axiom-clean regardless of whether its hypothesis is yet discharged; that hard kernel is the genuine remaining work.

The **10 residual axioms** (`gkl24_cubeRoot_mca_bound`, `bgks20_etaMargin_ca_bound`, `bchks25_*`, `cs25_*`, `gg25_*`, `fenziSanso_upperBound_attack_concrete_residual`) are honest external-paper obligations, each named with a tracking issue — declared scaffolding, not concealed gaps.

## Verdict

Real, machine-verified proof infrastructure with **honestly-declared** open residuals. Not slop, not confabulation. The remaining work is the deep correlated-agreement kernel — genuine mathematics, being ground out, not faked.
