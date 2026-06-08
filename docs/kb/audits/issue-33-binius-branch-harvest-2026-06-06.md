# Issue #33 Binius Branch-Harvest Note

Date: 2026-06-06

Scope:

- `origin/CompBinius`
- `origin/completeness-of-binius`
- `origin/soundness-binarybasefold`
- `origin/binarybasefold-proofs`
- `origin/tensor-algebra`
- `ArkLib/ProofSystem/Binius/**`
- `ArkLib/Data/FieldTheory/AdditiveNTT/**`
- `ArkLib/Data/FieldTheory/BinaryField/Tower/TensorAlgebra.lean`

## Result

Do not merge these stale Binius branches wholesale into current `main`.

Current `main` has already absorbed or reworked many of the useful surfaces from this cluster:

- split BinaryBasefold step modules;
- perfect-completeness front doors for the individual BBF steps;
- `iterated_fold_last`;
- `iterated_fold_eq_matrix_form`;
- the explicit `FoldPreservesBBFCodeMembershipResidual` frontier and audited wrappers.

The remaining useful branch content is proof-reference material for porting the Lemma 4.13
code-membership route, not a safe direct cherry-pick.

## Branch Findings

`origin/CompBinius` is not mergeable. It contains the AdditiveNTT `Domain` / `compSDomain`
renaming and a large alternate Binius refactor, but a raw branch scan finds many live `sorry`
bodies across `BinaryBasefold/{Basic,Code,CoreInteractionPhase,General,Prelude,QueryPhase}` and
related files.

`origin/soundness-binarybasefold` and `origin/binarybasefold-proofs` are also not mergeable. They
still contain live `sorry` bodies and `stop` commands in AdditiveNTT, BinaryBasefold, Steps,
Spec, QueryPhase, and RingSwitching files. They should be treated as old proof sketches only.

`origin/tensor-algebra` has useful historical tensor-product and binary-tower material, but the
salvage already happened in the dependency layer. Current `main` keeps
`ArkLib/Data/FieldTheory/BinaryField/Tower/TensorAlgebra.lean` as a compatibility re-export of
`CompPoly.Fields.Binary.Tower.TensorAlgebra`, and the current CompPoly file contains the branch's
key standalone declarations:

- `comm_map_smul_tmul`;
- `commSEquiv`;
- `Basis.baseChangeRight`;
- `Basis.baseChangeRight_repr_tmul`;
- `Basis.baseChangeRight_apply`.

Do not duplicate that code back into ArkLib unless the dependency strategy changes.

`origin/completeness-of-binius` is the highest-value reference branch. It has proof bodies for:

- `fold_preserves_BBF_Code_membership`;
- `iterated_fold_preserves_BBF_Code_membership`;
- many BBF / FRI-Binius / RingSwitching perfect-completeness wrappers;
- scalar knowledge-soundness wrappers via the RBR-to-KS lemmas.

However, that branch is pre-current architecture. Its `fold_preserves_BBF_Code_membership` route
depends on the old general-`i` reconstruction stack:

- `getINovelCoeffs`;
- `degree_intermediateEvaluationPoly_lt`;
- `intermediateEvaluationPoly_from_inovel_coeffs_eq_self`;
- `fold_advances_evaluation_poly`.

Current `main` already preserves that old Lemma 4.13 route as a disabled legacy proof block in
`ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean`, immediately before
`FoldPreservesBBFCodeMembershipResidual`. The live theorem wrappers deliberately expose the
residual until that reconstruction stack is ported to the current AdditiveNTT / CompPoly surface.

## Remaining #33 Work

The next real #33 proof brick is to port the old general-`i` reconstruction stack to current
`AdditiveNTT` / `intermediateEvaluationPoly` APIs, then replace
`FoldPreservesBBFCodeMembershipResidual` with the revived proof of
`fold_preserves_BBF_Code_membership` and its iterated wrapper.

The stale branches should remain reference material. Merging them directly would overwrite the
newer residualized mainline Binius structure and reintroduce old proof holes.
