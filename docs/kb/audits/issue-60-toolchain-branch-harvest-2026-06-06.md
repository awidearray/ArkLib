# Issue #60 Toolchain Branch-Harvest Note

Date: 2026-06-06

Scope:

- `origin/428_compatibility`
- `origin/quang/bump-v4.29.0`
- `origin/quang/update-deps-backup-120326`
- `lean-toolchain`
- `lakefile.toml`
- `lake-manifest.json`

## Result

Do not merge these stale toolchain/dependency branches into current `main`.

Current `fork/main` is pinned to:

- `leanprover/lean4:v4.30.0-rc2`

The inspected branches are older transition artifacts:

- `origin/428_compatibility` ports a compatibility branch to Lean `v4.28.0`.
- `origin/quang/bump-v4.29.0` moves an older branch to Lean `v4.29.0` and adapts component proofs
  such as `RandomQuery` / `SendClaim` to that era's simp behavior.
- `origin/quang/update-deps-backup-120326` is a backup of an older CompPoly / VCVio migration state.

Their dependency pins are behind the current rc2 mainline and would overwrite the active VCVio /
CompPoly coordination tracked in #60.

## Branch Risk

The branches mix source edits with old `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`
pins. Replaying them would downgrade or fork the current dependency graph rather than repair the
current root build.

Some source edits may still be useful as historical patterns for future API drift, but they should
be re-derived against the current `v4.30.0-rc2` pins. They should not be cherry-picked together with
their old dependency manifests.

## Remaining #60 Work

Root-build repair should stay on the current pinned dependency graph. If a future build failure
resembles one of these branch-era changes, port only the minimal source proof adjustment and keep
the current toolchain / package pins unchanged unless #60 explicitly decides to move the whole
project to a new dependency revision.
