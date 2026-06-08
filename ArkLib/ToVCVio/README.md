# Additions to VCVio not yet in the pinned dependency

This is a collection of `simulateQ` / `OracleComp` lemmas that ArkLib needs but
that the currently-pinned VCVio commit predates (ArkLib pins VCVio ~41 commits
behind upstream `master`, and bumping is parked alongside the Lean-toolchain
bump).

Each lemma here is staged so it can be **deleted wholesale** once the VCVio
dependency is bumped: prefer landing the general statements upstream in
`~/VCV-io/` under the same names, then remove the corresponding declaration
here and let references resolve to the upstream version.

- `SimulateQ.lean` — `simulateQ`-distributivity simp lemmas (`forIn`, …) used by
  the toy-problem / IOR completeness proofs. `simulateQ_list_forIn` is already
  upstreamed to VCVio under the same name.
