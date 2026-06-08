# Issue #14 Batched FRI Query-Soundness Residual Audit

Date: 2026-06-06

Scope:

- `ArkLib/ProofSystem/BatchedFri/Security.lean`
- `ArkLib/ProofSystem/BatchedFri/Spec/General.lean`
- `ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean`
- `ArkLib/ProofSystem/Fri/Spec/Soundness.lean`
- `ArkLib/Data/CodingTheory/InterleavedCode.lean`

## Current residual surface

`ArkLib/ProofSystem/BatchedFri/Security.lean` records BCIKS20 Claim 8.2 as
`Fri.Soundness.fri_query_soundness`. The declaration is already repaired away
from the old degenerate `True` conclusion: it is now a named `Prop` whose
conclusion is the intended `Code.jointAgreement` statement for the batched
input functions at `δ := 1 - α`.

The remaining proof is not a local simplification of the declaration. The
missing bridge is the probabilistic query-round analysis:

1. Express the Batched FRI query verifier's acceptance event through
   `OracleReduction.run` for the composed batching + FRI reduction.
2. Prove the per-query consistency bound from the query samples.
3. Convert the consistency bound into `Code.jointAgreement` for
   `Fₛ f : Fin t.succ → (ω.subdomain 0 → 𝔽)`.
4. Feed Claim 8.2 into `fri_soundness` / Claim 8.3, whose conclusion uses the
   same `Code.jointAgreement` predicate on the full domain.

Current source exposes both sides of that frontier as named parts:

- `FriQuerySoundnessParts` splits Claim 8.2 into query-round acceptance,
  batching/oracle-lens, and correlated-agreement-to-joint-agreement ingredients.
- `queryRoundDensityBound_holds` and `batchedFRIOracleLensReduction_holds`
  discharge the local query-round counting and structural Batched FRI
  oracle-lens pieces.  The adapter
  `fri_query_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLens`
  reassembles Claim 8.2 from those two proved pieces plus the still-open
  correlated-agreement bridge.
- `Fri.fri_query_soundness_of_jointProximity` exposes that bridge through the
  existing `Code.jointAgreement_iff_jointProximity` theorem.  The density-route
  `Fri.fri_query_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndJointProximity`
  and probability-route
  `Fri.fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity`
  adapters reassemble the query-round/lens route with a concrete
  `Code.jointProximity` witness rather than an arbitrary `agreementBridge :
  Prop`.
- `FriSoundnessParts` splits Claim 8.3 into the Claim 8.2 lift, the
  sequential-composition soundness step, and the `totalError` accounting step.
- `Fri.batchedFRIreduction_verifier_eq_append` and
  `Fri.batchedFRISequentialCompositionSoundness_of_append` expose the concrete
  Batched FRI append seam: if the batching-round verifier, lifted-FRI verifier,
  and generic `OracleVerifier.appendSoundnessResidual` are available, the
  appended verifier has additive soundness error.
- `Fri.friSoundnessSequentialComposition` names that additive soundness
  proposition for the actual `BatchedFri.Spec.batchedFRIreduction` verifier, and
  `fri_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndSequentialComposition`
  reassembles Claim 8.3 with the query-lift and concrete sequential fields
  supplied while leaving the append residual and `totalError` consumption
  explicit.
- `Fri.friSoundnessTotalErrorAccounting` names the exact `εC 𝔽 n s m ρ_sqrt +
  α ^ l` arithmetic budget used by `fri_soundness`, and
  `Fri.friSoundnessTotalErrorAccounting_of_phase_bounds` proves it from
  separate batching and FRI-tail error bounds.
- `Fri.friBatchPhaseErrorBound` and `Fri.friTailPhaseErrorBound` name those two
  per-phase error-bound targets directly; `Fri.friSoundnessTotalErrorAccounting_of_named_phase_bounds`
  packages them into the existing total-error accounting field.
- `Fri.fri_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndPhaseErrorBounds`
  and
  `Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndPhaseErrorBounds`
  are the density/probability Claim 8.3 front doors that consume those named
  phase-bound targets directly.
- `Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndTotalError`
  gives the same Claim 8.3 reassembly along the probability-space query-round
  route, with query lift, concrete sequential composition, and arithmetic
  total-error accounting supplied.
- `Fri.fri_query_soundness_of_forall_mem`,
  `Fri.friSoundnessQueryLift_of_forall_mem`, and
  `Fri.fri_soundness_of_forall_mem` prove the complete-codeword extreme of the
  correlated-agreement bridge: if every row is already in the corresponding
  Reed-Solomon code, the `Code.jointAgreement` conclusion holds on the full
  coordinate set, including the end-to-end Claim 8.3 implication.
- `Code.jointAgreement_equiv_of_codeword_transport` proves the finite-domain
  transport part of that lift across an equivalence of coordinate domains, once
  the corresponding codeword transport hypothesis is supplied.
- `ReedSolomon.codeword_equiv_of_eval_eq`,
  `CosetFftDomainClass.subdomainZeroEquiv`, and
  the Batched FRI-facing `Fri.jointAgreement_subdomainZero_to_domain` /
  `Fri.fri_query_soundness_lift_subdomainZero_to_domain` instantiate that
  transport for the `ω.subdomain 0` to `ω` Reed-Solomon domain change used
  between Claim 8.2 and Claim 8.3.
- `fri_query_soundness_of_parts` and `fri_soundness_of_parts` are small
  reassembly theorems. They do not prove the missing probabilistic bounds; they
  make the remaining obligations independently targetable.

## Existing in-tree pieces

- `BatchedFri.Spec.BatchingRound.batchSpec` sends the random batching
  coefficients.
- `BatchedFri.Spec.batchedFRIOracleLens` defines the virtual oracle routing
  from the batched outer oracles to the inner FRI round-0 oracle.
- `Fri.batchedFRIOracleLensReduction_holds` proves the structural fact that
  the lifted Batched FRI reduction uses that oracle lens and the corresponding
  value-level `liftingLens.stmt`.
- `BatchedFri.Spec.batchedFRIreduction` composes the batching round with the
  FRI fold/final/query phases.
- `Fri.batchedFRIreduction_verifier_eq_append` identifies its verifier with the
  append of `BatchingRound.batchOracleReduction.verifier` and
  `BatchedFri.Spec.liftedFRI.verifier`; the companion theorem
  `Fri.batchedFRISequentialCompositionSoundness_of_append` specializes the
  generic append soundness theorem to that concrete Batched FRI seam.
- `Fri.friSoundnessSequentialComposition_of_append` packages that theorem as
  the concrete `FriSoundnessParts.sequential_composition_soundness` field for
  the actual Batched FRI reduction verifier.
- `Code.jointAgreement` and `jointAgreement_iff_jointProximity` are available
  in `ArkLib/Data/CodingTheory/InterleavedCode.lean`.
- `Code.jointAgreement_equiv_of_codeword_transport` transports a
  `jointAgreement` witness along an equivalence of coordinate domains, isolating
  the finite-coordinate bookkeeping from code-specific transport.
- `ReedSolomon.codeword_equiv_of_eval_eq` transports RS codeword membership
  across equivalent evaluation domains whose embeddings select the same field
  points.
- `CosetFftDomainClass.subdomainZeroEquiv` identifies the zeroth subdomain's
  finite field-point type with the ambient domain.  The Batched FRI security
  file also exposes `Fri.subdomainZeroEquiv`,
  `Fri.reedSolomon_code_subdomainZero_transport`,
  `Fri.jointAgreement_subdomainZero_to_domain`, and
  `Fri.fri_query_soundness_lift_subdomainZero_to_domain` as Claim 8.3 lift
  front doors.
- `Fri.Spec.Soundness.queryRoundError`, `queryError`, and `totalError` are
  accounting definitions.  The projection lemmas
  `Fri.Spec.roundError_sum_le_totalError`,
  `Fri.Spec.roundError_le_totalError`, and
  `Fri.Spec.queryError_le_totalError` show the fold-round and query
  contributions are included in `totalError`; the FRI soundness theorem
  consuming the full budget is still deferred to sequential-composition/query
  infrastructure.

## Audit commands

```sh
rg -n 'fri_query_soundness|fri_soundness|jointAgreement|queryRoundError|batchedFRIOracleLens|batchedFRIreduction' \
  ArkLib/ProofSystem/BatchedFri ArkLib/ProofSystem/Fri ArkLib/Data/CodingTheory/InterleavedCode.lean
```

```sh
rg -n 'Batched FRI|fri_query_soundness|query soundness|Claim 8.2|named residual|degenerate|True' \
  ArkLib/ProofSystem/BatchedFri/Security.lean docs/kb/audits docs/kb/papers
```

Observed core anchors on 2026-06-06:

```text
ArkLib/ProofSystem/BatchedFri/Security.lean:670: Corresponds to Claim 8.2 of [BCIKS20]
ArkLib/ProofSystem/BatchedFri/Security.lean:695:def fri_query_soundness
ArkLib/ProofSystem/BatchedFri/Security.lean:726:structure FriQuerySoundnessParts
ArkLib/ProofSystem/BatchedFri/Security.lean:749:theorem fri_query_soundness_of_parts
ArkLib/ProofSystem/BatchedFri/Security.lean:775:def fri_soundness
ArkLib/ProofSystem/BatchedFri/Security.lean:813:structure FriSoundnessParts
ArkLib/ProofSystem/BatchedFri/Security.lean:829:theorem fri_soundness_of_parts
ArkLib/ProofSystem/BatchedFri/Spec/General.lean:128:def batchedFRIOracleLens
ArkLib/ProofSystem/BatchedFri/Spec/General.lean:257:def batchedFRIreduction
ArkLib/ProofSystem/Fri/Spec/Soundness.lean:54:noncomputable def queryRoundError
ArkLib/Data/CodingTheory/InterleavedCode.lean:697:def jointAgreement
ArkLib/Data/CodingTheory/InterleavedCode.lean:708:theorem jointAgreement_equiv_of_codeword_transport
ArkLib/Data/CodingTheory/InterleavedCode.lean:738:theorem jointAgreement_iff_jointProximity
```

## Remaining proof tasks

1. Connect the structural Batched FRI oracle-lens package to the still
   residualized virtual-oracle soundness-preservation theorem.
2. Derive the general Claim 8.2 `Code.jointProximity`/`Code.jointAgreement`
   conclusion for the batched input stack from the BCIKS20
   correlated-agreement/proximity-gap analysis.  The conversion from
   `Code.jointProximity` to the `fri_query_soundness` residual is now proved by
   `Fri.fri_query_soundness_of_jointProximity`; both density and probability
   query-round/lens front doors now consume that concrete proximity witness. The
   all-rows-already-codewords extreme is proved by
   `Fri.fri_query_soundness_of_forall_mem` and
   `Fri.fri_soundness_of_forall_mem`, but the real proximity-gap bridge remains
   open.
3. Connect the Claim 8.2 output through
   `Fri.fri_query_soundness_lift_subdomainZero_to_domain`, then prove the
   remaining generic append residual / virtual-oracle soundness preservation
   and `totalError` accounting steps for Claim 8.3 (`fri_soundness`) /
   end-to-end Batched FRI soundness.  The concrete sequential-composition field
   itself is now named by `Fri.friSoundnessSequentialComposition` and supplied
   by `Fri.friSoundnessSequentialComposition_of_append` once the generic append
   residual is available; the arithmetic `εC + α^l` budget is named by
   `Fri.friSoundnessTotalErrorAccounting` and supplied from per-phase error
   bounds by `Fri.friSoundnessTotalErrorAccounting_of_phase_bounds`.  The
   remaining per-phase targets are now named as
   `Fri.friBatchPhaseErrorBound` and `Fri.friTailPhaseErrorBound`, with
   density/probability wrappers that consume those names directly.  The
   probability-route wrapper
   `Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialCompositionAndTotalError`
   combines the proved query-round probability front door with these Claim 8.3
   fields.

This audit does not close the mathematical residual. It confirms that the
current source no longer hides Claim 8.2 behind a vacuous `True` theorem and
records the exact theorem infrastructure still needed to replace the named
residual with a proof body.
