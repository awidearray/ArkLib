# Issue #62 BCS/Merkle Branch-Harvest Note

Date: 2026-06-06

Scope:

- `origin/merkle-tree-soundness`
- `ArkLib/CommitmentScheme/MerkleTree/**`
- `ArkLib/OracleReduction/BCS/Basic.lean`

## Result

Do not merge `origin/merkle-tree-soundness` wholesale into current `main`.

The branch adds a parallel Merkle tree surface under:

- `ArkLib/CommitmentScheme/MerkleTree/Inductive/Defs.lean`
- `ArkLib/CommitmentScheme/MerkleTree/Inductive/Completeness.lean`
- `ArkLib/CommitmentScheme/MerkleTree/Inductive/Collision.lean`
- `ArkLib/CommitmentScheme/MerkleTree/Inductive/Extractability.lean`
- `ArkLib/CommitmentScheme/MerkleTree/Vector/MerkleTree.lean`

Current `main` already has the ArkLib-side Merkle commitment support that is more relevant to the
BCS frontier:

- `ArkLib/CommitmentScheme/MerkleTree/Batch.lean`
- `ArkLib/CommitmentScheme/MerkleTree/Extraction.lean`
- `ArkLib/CommitmentScheme/MerkleTree/Hiding.lean`

Those current files build on the VCVio inductive Merkle tree API and align with the typed
opening-log / commitment frontier in `ArkLib/OracleReduction/BCS/Basic.lean`.

## Branch Risk

The old branch still contains live proof holes and TODO-heavy proof scaffolding in the added
parallel files. A raw scan of the branch finds live `sorry` bodies in the inductive collision and
extractability files, plus TODO markers in the definitions/vector layers. The useful content should
therefore be treated as design/proof-reference material only.

## Remaining #62 Work

The BCS compiler still needs the generic compiler construction and the preservation theorems for
completeness, soundness, and knowledge soundness. Merkle-specific follow-up should target the
current `Batch` / `Extraction` / `Hiding` modules or the VCVio dependency surface, not the stale
parallel branch files.
