# Issue #75 Johnson-Bound Branch-Harvest Note

Date: 2026-06-06

Scope:

- `origin/dtumad/finalize-4-26`
- `ArkLib/Data/CodingTheory/JohnsonBound/**`
- `ArkLib/Data/CodingTheory/ProximityGap/{BCIKS20,DG25}.lean`

## Result

Do not merge `origin/dtumad/finalize-4-26` wholesale into current `main`.

The branch has a small Johnson-bound proof-fix delta. The relevant commit is:

- `47b52f077 fixes in Johnson bound lemmas`

The useful signal is proof intent around the Johnson-bound arithmetic side conditions, especially
the transition lemmas in:

- `ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean`
- `ArkLib/Data/CodingTheory/JohnsonBound/Choose2.lean`
- `ArkLib/Data/CodingTheory/JohnsonBound/Lemmas.lean`

Those edits are worth revisiting when closing the current Johnson-bound inequality frontier, but
they are not directly importable.

## Branch Risk

The old branch still contains live unfinished commands and proof holes in the touched proof files.
A raw diff against `fork/main` shows `stop` commands in the Johnson-bound theorem path and DG25 row
distance/cardinality proof areas, plus live `sorry` bodies in Johnson-bound arithmetic lemmas.

The branch also carries a stale monolithic `BCIKS20.lean` edit from an older layout. Current `main`
has split and reorganized the BCIKS/DG25 proximity-gap surface, so that hunk should not be replayed
without first translating it to the current files.

## Remaining #75 Work

For issue #75, the salvage path is to extract individual Johnson-bound arithmetic lemmas from the
old branch by hand, remove the `stop` / `sorry` scaffolding, and port only proofs that compile
against the current split codebase. The branch should be treated as a proof-reference artifact, not
as a merge candidate.
