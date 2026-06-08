# Issue 44 upstream PR handoff

Issue: <https://github.com/lalalune/ArkLib/issues/44>

## Current upstream state

Open PRs against `Verified-zkEVM/ArkLib` already cover several adjacent lanes:

* #505 `feat/abf26-plan` - ABF26 planning material already in upstream review.
* #489 `Katy/MCAgens` - MCA generator lemmas.
* #279 `codingtheory-refactor` - broad coding-theory refactor.
* #497 `rational-functions-positive-degree` - rational-function lemmas near the BCIKS/L13 lane.
* #538 `cg/comppoly-bump-v430` - Lean/mathlib/CompPoly toolchain reconciliation.
* #532, #433, #491, #449 - oracle/interaction infrastructure that overlaps later security
  reduction PRs.

This means the local harvest should not be pushed as one monolithic branch. It should be split into
small branches that either build on, or explicitly avoid, those open upstream PRs.

## Proposed upstream batches

1. `abf26-gk16-frs-closure`
   * GK16 T2.18 FRS closure chain.
   * Vandermonde/Gaussian-elimination Lemma 12 hard direction.
   * Claim 16 column-divisibility and structural transport.
   * Base against the current state of upstream #505/#279, not raw upstream `main`.

2. `cs25-epsca-lambda-closure`
   * `rs_epsCA_implies_lambda_extended_cs25_complete`.
   * CS25 combiner-sign statement correction notes.
   * Keep this separate from the broader BCIKS agreement residual work.

3. `proximity-lattice-threshold-brackets`
   * Lattice Grand Challenge encodings.
   * Threshold bracket certificates and judge-grade statement-bug findings.
   * This can be a docs + theorem-surface PR if the proof payload is too entangled with #505.

4. `subspace-poly-linearized-support`
   * Linearized-support theorem.
   * `IsQLinearized` algebra.
   * Likely mathlib-adjacent; should be reviewed separately from proximity-prize material.

5. `ingredient-bricks-keystone-assembly`
   * The 28 ingredient-D bricks.
   * Keystone assembly surface.
   * This should wait until the smaller theorem batches above are reviewed, because it is likely to
     depend on their naming and import layout.

## Non-PR feedback packet

The following are best sent as maintainer/judge feedback before or alongside PRs, not hidden inside
large proof branches:

* F-series statement issues: s-factor in T2.18, F5/F6, BKR06 `Submodule F F`.
* CS25 combiner sign.
* `needsHInitNeverFail`.
* `[Module F K]` insufficiency.
* `fri_query_soundness` old `True` placeholder surface.

## Next concrete action

Create the first upstream branch from the appropriate upstream base, cherry-pick only the GK16/FRS
closure files and their direct dependencies, run the focused Lake build, and open a draft PR that
references #44 and the already-open upstream PRs it depends on.
