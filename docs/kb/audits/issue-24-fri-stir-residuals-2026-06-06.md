# Issue #24 FRI/STIR Soundness Residual Audit

Date: 2026-06-06

Scope:

- `ArkLib/ProofSystem/Fri/Spec/Soundness.lean`
- `ArkLib/ProofSystem/BatchedFri/Security.lean`
- `ArkLib/ProofSystem/Stir/ProximityGap.lean`
- `ArkLib/ProofSystem/Stir/Combine.lean`
- `ArkLib/ProofSystem/Stir/RoundProtocol.lean`
- `ArkLib/ProofSystem/Stir/MainThm.lean`

## Branch-harvest note

The stale STIR/proximity branches are not merge candidates:

- `origin/codingtheory-refactor`
- `origin/Katy/ProximityRefactor`
- `origin/Katy/ProximityWIP`
- `origin/Katy/mathlibDefs`
- `origin/quangvdao/Julek/ElijahVlasov/fri-implementation-rebase`

Raw branch scans show live `sorry` bodies and/or `opaque` placeholders across the old
coding-theory, BCIKS20, polynomial, STIR folding, out-of-domain sampling, and combine files.
Do not replay these branches wholesale.

The useful content from `origin/codingtheory-refactor` is already represented on current `main`
under the newer `ArkLib/ProofSystem/Stir/**` layout:

- `ArkLib/ProofSystem/Stir/ProximityBound.lean` carries `Bstar` and `proximityError`.
- `ArkLib/ProofSystem/Stir/Combine.lean` carries the STIR combine and degree-correction surface.
- `ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean` carries the out-of-domain sampling surface.
- `ArkLib/ProofSystem/Stir/RoundProtocol.lean` carries the real one-round STIR oracle reduction.

The old `Data/CodingTheory/Folding/Stir.lean` and `Operations/Combine.lean` proof sketches should
be treated as historical references only. Current work should target the live `ProofSystem/Stir`
files and the residuals below.

The old FRI implementation rebase is also reference-only. Its FRI files were useful during the
initial coset-domain / even-odd / single-round protocol design, but current `main` now has the
newer `ArkLib/ProofSystem/Fri/**`, `ArkLib/ProofSystem/BatchedFri/**`, and
`ArkLib/ProofSystem/Stir/RoundProtocol.lean` surfaces. A direct merge of the old branch would
delete the current Batched FRI security modules and the current STIR round protocol file while
replacing them with a smaller pre-current FRI model.

## Current residual surfaces

### FRI soundness accounting

`ArkLib/ProofSystem/Fri/Spec/Soundness.lean` currently contains candidate
accounting definitions:

- `roundError`
- `queryRoundError`
- `queryError`
- `totalError`

The module documentation explicitly marks these as accounting placeholders
pending sequential-composition infrastructure.  The local projection lemmas
`roundError_sum_le_totalError`, `roundError_le_totalError`, and
`queryError_le_totalError` record that the fold-round and query contributions
are included in `totalError`.  The missing work is still a soundness theorem
tying the per-round BCIKS20 proximity-gap and query-consistency quantities to
the actual FRI verifier failure probability.

The Batched FRI query surface in
`ArkLib/ProofSystem/BatchedFri/Security.lean` is tracked separately in #14. The
old finite-range diagnostic scratch block after `fri_query_soundness` has been
removed; the declaration itself remains the faithful non-`True` Claim 8.2
residual, namely the query-round route to `Code.jointAgreement`.

Current source also exposes the #14 split frontier:

- `FriQuerySoundnessParts` separates the Claim 8.2 proof boundary into the
  query-round acceptance bound, the batching/oracle-lens reduction, and the
  correlated-agreement-to-joint-agreement coding step.
- `fri_query_soundness_of_parts` reassembles the faithful
  `fri_query_soundness` residual from those three named ingredients.
- `queryRoundAcceptanceBound` / `queryRoundAcceptanceBound_holds` and
  `queryRoundDensityBound` / `queryRoundDensityBound_holds` now prove the pure
  independent-query counting core: if the good set has density at most
  `1 - δ`, then `t` independent uniform queries all land in it with probability
  at most `(1 - δ) ^ t`.
- `FriQuerySoundnessParts.of_queryRoundAcceptanceBound` and
  `fri_query_soundness_of_queryRoundAcceptanceBound` plug the proved card-form
  query-round proposition into the Claim 8.2 frontier while leaving the
  batching/oracle-lens and correlated-agreement bridge fields explicit.
- `FriQuerySoundnessParts.of_queryRoundDensityBound` and
  `fri_query_soundness_of_queryRoundDensityBound` provide the same adapter from
  the normalized-density hypothesis that proximity arguments usually produce.
- `FriSoundnessParts` separates the Claim 8.3 proof boundary into the
  Claim 8.2 lift to the full-domain statement, sequential-composition
  soundness, and the `totalError` accounting step.
- `Fri.batchedFRIreduction_verifier_eq_append` and
  `Fri.batchedFRISequentialCompositionSoundness_of_append` specialize the
  existing append soundness API to the concrete Batched FRI verifier seam,
  reducing the sequential-composition field to the per-phase soundness inputs
  plus the generic `OracleVerifier.appendSoundnessResidual`.
- `Fri.friSoundnessSequentialComposition` names the resulting concrete
  end-to-end verifier soundness proposition, and
  `Fri.friSoundnessSequentialComposition_of_append` supplies it from the append
  theorem whenever the per-phase soundness inputs and generic append residual
  are available.
- `Fri.friSoundnessTotalErrorAccounting` names the concrete `εC + α^l`
  arithmetic budget in the Claim 8.3 threshold, and
  `Fri.friSoundnessTotalErrorAccounting_of_phase_bounds` supplies it from
  separate batching and FRI-tail error bounds.
- `Fri.friBatchPhaseErrorBound` and `Fri.friTailPhaseErrorBound` name those
  remaining per-phase error-bound targets, and
  `Fri.friSoundnessTotalErrorAccounting_of_named_phase_bounds` feeds them into
  total-error accounting.
- `Fri.fri_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndPhaseErrorBounds`
  and
  `Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndPhaseErrorBounds`
  are the density/probability Claim 8.3 front doors that consume those named
  phase-bound targets directly.
- `Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndTotalError`
  routes the proved probability-space query-round front door through the
  concrete sequential-composition and total-accounting fields.
- `Fri.fri_query_soundness_of_forall_mem`,
  `Fri.friSoundnessQueryLift_of_forall_mem`, and
  `Fri.fri_soundness_of_forall_mem` cover the all-rows-already-codewords
  extreme of the correlated-agreement bridge, including the end-to-end Claim 8.3
  implication; the general bridge remains open.
- `fri_soundness_of_parts` reassembles the faithful `fri_soundness` residual
  from those three named ingredients.

The query-round acceptance field now has a proved combinatorial core and two
adapters into the split frontier. This is still not a proof of Claims 8.2 or
8.3: the batching/oracle-lens reduction, the coding-theoretic bridge into
`Code.jointAgreement`, the generic append residual / virtual-oracle soundness
preservation, and the per-phase error bounds `Fri.friBatchPhaseErrorBound` /
`Fri.friTailPhaseErrorBound` feeding the `totalError` accounting step remain
open proof work.

### STIR proximity gap

`ArkLib/ProofSystem/Stir/ProximityGap.lean` is intentionally inert today. Its
audit comments record two separate blockers:

1. The original unconstrained-generator statement is false. A zero generator
   makes the combined word identically zero, so the probability hypothesis can
   hold for arbitrary inputs without yielding the claimed common agreement set.
   The file therefore includes the `_hGen` repair requiring the monomial /
   Vandermonde generator shape.
2. The repaired monomial statement still depends on the BCIKS20 correlated
   agreement chain in the square-root-rate list-decoding regime. The blocking
   base case is `RS_correlatedAgreement_affineLines` in
   `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean`.

The clean unique-decoding-regime result does not cover the STIR hypothesis
`δ < 1 - Bstar ρ`, so closing this surface requires the list-decoding branch,
not just a local restatement.

### STIR combine theorem

`ArkLib/ProofSystem/Stir/Combine.lean` exposes `combine_theorem`, but the theorem
requires `ProximityGap.StrictCoeffPolysResidual`. That residual is the strict
coefficient-polynomial bridge needed to feed the repaired BCIKS20 proximity gap.
As a result, `combine_theorem` remains downstream of the same affine-lines /
spaces / curves correlated-agreement proof chain.

### STIR main theorem and RBR soundness

`ArkLib/ProofSystem/Stir/RoundProtocol.lean` now defines a real single STIR
fold-round oracle reduction, `StirIOP.stirRoundReduction`, using the genuine
`Combine.combine` operation. That removes the older "no protocol object exists"
obstruction for the one-round fold-and-combine object. The proof obligations on
that object are still open: `stirRoundReduction_completeness` is a named
statement whose proof is owed.

`ArkLib/ProofSystem/Stir/MainThm.lean` still has two documented residual
surfaces:

- `stir_main`, the full STIR IOPP construction theorem.
- `stir_rbr_soundness`, the round-by-round soundness theorem.

Both require assembling the full `VectorIOP` protocol object from the round
building blocks and proving the round-by-round security bounds. The directory
now contains a genuine single-round object, but not the full multi-round
construction and sequential soundness assembly needed by these theorem
statements. Their proximity-gap inputs also flow through `Combine.combine_theorem`,
so they remain gated on the BCIKS20 list-decoding-regime correlated-agreement
work.

## Audit command

```sh
rg -n 'accounting placeholders|sorryAx-tainted|Honest residual|Open proof|residual|placeholder' \
  ArkLib/ProofSystem/Fri ArkLib/ProofSystem/Stir
```

Observed hits on 2026-06-06:

> Superseded raw-line note: the `AffineLines/Main.lean:40` references in this
> preserved command output are historical breadcrumbs. Current proximity-gap
> ownership is by the named `StrictCoeffPolysResidual`, `BoundaryCardResidual`,
> and `BoundaryCardLatticeResidual` interfaces plus their focused issues.

```text
ArkLib/ProofSystem/Fri/Spec/Soundness.lean:19:soundness theorem — they are accounting placeholders pending the sequential
ArkLib/ProofSystem/Stir/MainThm.lean:150:  -- full chain). Honest residual: this is a major protocol-formalisation effort gated on (1) the
ArkLib/ProofSystem/Stir/MainThm.lean:242:  -- construction scaffolding exists yet. Honest residual: gated on AffineLines/Main.lean:40
ArkLib/ProofSystem/Stir/ProximityGap.lean:41:  STATUS (audit 2026-06-04, branch arklib-sorry-fixes). Open proof. Two independent,
ArkLib/ProofSystem/Stir/ProximityGap.lean:68:  Honest residual: close `AffineLines/Main.lean:40` (Thm 5.1, list-decoding regime), which
ArkLib/ProofSystem/Stir/RoundProtocol.lean:132: The STIR fold-round oracle reduction
ArkLib/ProofSystem/Stir/RoundProtocol.lean:187: Completeness of the real STIR fold-round object
ArkLib/ProofSystem/BatchedFri/Security.lean:420:def queryRoundAcceptanceBound
ArkLib/ProofSystem/BatchedFri/Security.lean:431:theorem queryRoundAcceptanceBound_holds
ArkLib/ProofSystem/BatchedFri/Security.lean:454:def queryRoundDensityBound
ArkLib/ProofSystem/BatchedFri/Security.lean:463:theorem queryRoundDensityBound_holds
ArkLib/ProofSystem/BatchedFri/Security.lean:837:def fri_query_soundness
ArkLib/ProofSystem/BatchedFri/Security.lean:868:structure FriQuerySoundnessParts
ArkLib/ProofSystem/BatchedFri/Security.lean:892:theorem fri_query_soundness_of_parts
ArkLib/ProofSystem/BatchedFri/Security.lean:918:def FriQuerySoundnessParts.of_queryRoundAcceptanceBound
ArkLib/ProofSystem/BatchedFri/Security.lean:950:theorem fri_query_soundness_of_queryRoundAcceptanceBound
ArkLib/ProofSystem/BatchedFri/Security.lean:982:def FriQuerySoundnessParts.of_queryRoundDensityBound
ArkLib/ProofSystem/BatchedFri/Security.lean:1011:theorem fri_query_soundness_of_queryRoundDensityBound
ArkLib/ProofSystem/BatchedFri/Security.lean:1061:def fri_soundness
ArkLib/ProofSystem/BatchedFri/Security.lean:1099:structure FriSoundnessParts
ArkLib/ProofSystem/BatchedFri/Security.lean:1115:theorem fri_soundness_of_parts
```

## Remaining proof tracks

1. FRI: add sequential-composition soundness infrastructure, prove the
   batching/oracle-lens and coding ingredients still exposed by
   `FriQuerySoundnessParts`, connect the proved query-round acceptance package
   to the actual oracle-reduction run, discharge the Claim 8.3
   lift/composition/accounting ingredients exposed by `FriSoundnessParts`, then
   prove that `totalError` bounds the verifier failure probability.
2. BCIKS20/STIR proximity gap: close the affine-lines correlated-agreement
   theorem in the list-decoding regime, then lift through affine spaces and
   curves to the repaired monomial proximity-gap statement.
3. STIR combine: discharge `StrictCoeffPolysResidual` and reconnect
   `combine_theorem` to the repaired proximity gap.
4. STIR main theorem: lift the existing single-round object into the full
   concrete `VectorIOP` object and prove the round-by-round security assembly
   using the closed combine/proximity-gap inputs.

This audit does not close the mathematical residuals. It makes the remaining
surfaces explicit and separates the work into dependency tracks so the issue is
not mistaken for a collection of local `sorry` cleanups.
