# Issue #27 — L13: strengthen β existence with betaRec witness (keystone convergence point)

**Status:** Closed / resolved. Verified **green and axiom-clean** under
`leanprover/lean4:v4.30.0-rc2` on 2026-06-06: `lake build ArkLib.ToMathlib.L13Milestone` →
**Build completed successfully (8440 jobs)**, and `#print axioms` on every public milestone is
exactly `[propext, Classical.choice, Quot.sound]` with no `sorryAx`.

## Ask

Finish the L13 refactor so the strengthened β existence is a genuine witness (not a hypothesis):
`BetaIdentify.BetaEmbedEq` provable from `choose_spec`; deliver the milestone keystone with **no
β-identification residual** (`hβ`/`BridgeData.hαβ`); and verify the consumer matrix green
(BetaIdentify, KeystoneStrictResidual, BetaInputSupply, Section5Concrete, PlaceGeometrySupply,
MpFinSupply, Agreement, Curves).

## Resolution (already on disk)

The strong-β surface is residual-free and witness-backed:

- `RationalFunctionsStrong.lean`: `β_strong`, `beta_strong_eq_betaRec`, and
  `beta_strong_embedEq := .choose_spec` — the embed-equality is delivered by the `Classical.choose`
  spec of the strengthened existence, i.e. it is **the deliverable itself, carrying no hypothesis**.
- `L13Milestone.lean`: the public keystone
  `correlatedAgreement_affine_curves_strongBeta_of_betaRecFin` forwards verbatim to the proven
  betaRec-native strict keystone `correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict`.
  No hypothesis on this path is a numerator-identification residual; `betaEmbedEqStrong_holds`,
  `alpha_strong_eq_alphaFromBeta`, `gamma_strong_eq_γ'` show the in-tree strong numerator coincides
  with `betaRec` by definition.
- The two boundary-quantized companions
  `correlatedAgreement_affine_curves_strongBeta_of_betaRecFin_lattice_residual` and
  `..._boundaryData` route the closed √ρ boundary through the quantization split
  (`BoundaryCardResidual.boundaryCardResidual_of_lattice_residual`,
  `BoundaryDischarge.boundaryCardLatticeResidual_of_boundary_cards_and_coeffPolys`).

### The one consumer-matrix build defect found and fixed

The consumer-matrix build previously failed at `L13Milestone.lean:229` with
`failed to synthesize instance of type class DecidableEq ι`, which cascaded a `sorryAx` into the
two boundary-quantized companion milestones (Lean error-recovery inserts `sorryAx` for the failed
elaboration; the companions then inherited it). Root cause: the two companion theorems carried a
stray `omit [DecidableEq ι] in` (copied from the strict keystone, whose johnson lemma genuinely
omits `DecidableEq`), but their proofs call the **non-strict**
`correlatedAgreement_affine_curves_johnson_of_betaRecFin` and the `BoundaryCardResidual`
machinery, both of which **require** `[DecidableEq ι]`.

Fix (on disk): drop the stray `omit [DecidableEq ι] in` and make `[DecidableEq ι]` available to the
companion theorems (explicit on `_lattice_residual`, section-level for `_boundaryData`). With
`DecidableEq` in scope, line 229 elaborates and the consequent `sorryAx` in both companions
disappears — making all three milestones kernel-clean.

## Verification

- `lake build ArkLib.ToMathlib.L13Milestone` → **Build completed successfully (8440 jobs)** under
  `leanprover/lean4:v4.30.0-rc2`. Only style-linter warnings (unused-hypothesis notices on the
  milestone statements); no errors.
- `#print axioms` is kernel-clean for the full milestone set:
  - `correlatedAgreement_affine_curves_strongBeta_of_betaRecFin` (main keystone),
    `correlatedAgreement_affine_curves_strongBeta_of_betaRecFin_lattice_residual`,
    `correlatedAgreement_affine_curves_strongBeta_of_betaRecFin_boundaryData`,
    `betaEmbedEqStrong_holds`, `alpha_strong_eq_alphaFromBeta`, `gamma_strong`,
    `gamma_strong_eq_γ'`, `gamma_strong_eq_subst_shiftSeries`
    → all `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.
  - The two boundary-quantized companions, which previously carried a spurious `sorryAx` from the
    `DecidableEq` elaboration failure, are now clean — confirming the fix.
- Static scan: no `sorry`/`admit` in `RationalFunctionsStrong`, `L13Milestone`, `BetaIdentify`,
  `KeystoneStrictResidual`, `Section5Concrete`.

## Note on the build environment

The green run was initially blocked for a long window by the recurring toolchain-pin oscillation
(#60/#34): the root `lean-toolchain` had drifted to `v4.30.0` while every dependency (mathlib,
batteries, CompPoly) is pinned to `v4.30.0-rc2`, so concurrent agents rebuilding mathlib produced
`incompatible header` oleans and every build died on infra (`olean does not exist`), not on any
L13 code defect. Re-pinning the root to `v4.30.0-rc2` (matching the deps) + `lake exe cache get`
restored a clean build, after which L13Milestone compiled to 8440/8440.
