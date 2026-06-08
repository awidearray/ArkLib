# Quickstart

This page is the recommended agent playbook for commands and validation.
Use it as the main guide for routine local checks.

## Recommended Validation

For a convenient routine check, run:

```bash
./scripts/validate.sh
```

On a cold clone, fetch precompiled dependencies first:

```bash
lake exe cache get
./scripts/validate.sh
```

Do not use bare `lake update` as a routine cache-repair command. It re-resolves
`lake-manifest.json` and may delete/re-clone package directories while other checks are running.
Use `lake exe cache get` after syncing instead. Run `lake update` only when intentionally changing
dependency pins, and commit the resulting manifest together with the matching `lean-toolchain`.

### Recovering a corrupted or re-cloning `mathlib` package

Symptoms (tree-wide build failures, OOM, or stalls that are not your change):

- `.lake/packages/mathlib` is large on disk but has no checked-out source
  (e.g. `Mathlib/Algebra/Field/Basic.lean` is missing) or `git -C .lake/packages/mathlib rev-parse HEAD` fails.
- Many concurrent `git-remote-https ... mathlib4` clone processes are racing into that one
  directory, so it never converges and every session's build fails on missing `mathlib` oleans.

Root cause: a per-session package fetch checked out mathlib's default branch instead of the
manifest-pinned revision, and parallel sessions racing the same directory prevent convergence.

Non-destructive recovery (one actor at a time; do **not** `rm -rf` the shared package — the pinned
revision is usually already fetched inside it):

```bash
# 1. Pause (do not kill) the racing clones so the directory stops being overwritten.
pkill -STOP -f 'git-remote-https.*mathlib4'

# 2. Check out the revision pinned in lake-manifest.json (NOT the default branch).
#    Find the pin with: python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])"
git -C .lake/packages/mathlib checkout -f <manifest-pinned-rev>

# 3. Decompress the matching precompiled oleans for that revision.
lake exe cache get

# 4. Verify a real build completes.
lake build ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeCollapse
```

Prevention: never run `lake update` for cache repair (see above); let a single coordinator do
package recovery; the only source of truth for the mathlib revision is the `mathlib` entry in
`lake-manifest.json`.

## Validation By Change Type

### Existing Lean files only

```bash
./scripts/validate.sh
```

### Added, renamed, or deleted files under `ArkLib/`

```bash
git add path/to/newfile.lean
./scripts/validate.sh
```

`./scripts/update-lib.sh` only considers tracked files, and now fails fast if untracked
`ArkLib/**/*.lean` files are present.

### Lean-heavy refactors or cleanup

```bash
./scripts/validate.sh --lint
```

This adds `./scripts/lint-style.sh` to the convenience wrapper. The main CI build currently runs
with lint disabled, so treat this as opt-in for now.
If the task is specifically Lean warning cleanup, follow
[`../skills/fix-lean-warnings.md`](../skills/fix-lean-warnings.md).

### Docstrings, blueprint, or website changes

```bash
./scripts/validate.sh --docs
```

For website or blueprint output, run:

```bash
./scripts/validate.sh --site
```

`./scripts/build-web.sh` is still what assembles the site, and it skips blueprint generation if
`leanblueprint` is not installed. If blueprint output matters, install it first:

```bash
python3 -m pip install leanblueprint
```

## Important Notes

- `./scripts/validate.sh` is the recommended convenience wrapper for routine local validation.
- By default it runs the forbidden-token precheck, `lake build`, the `ArkLib/Data/**` warning
  budget, the zero-hole sorry census, the flagship axiom audit, umbrella-import checks, docs
  integrity checks, and knowledge-base checks, so a clean local `validate.sh` matches the CI gate set
  (issue #111 parity).
- The lower-level scripts remain valid when you only want one specific check.
- `scripts/build-project.sh` is now just a compile-only helper, not the convenience wrapper.
- `scripts/README.md` is still useful as an inventory of helper scripts.
- Only run docs and site builds when those surfaces are relevant; they are slower and more
  tool-dependent than normal Lean builds.

## Optional Direct Commands

You can still run the underlying pieces directly when debugging a specific issue:

```bash
lake build
python3 ./scripts/forbidden_tokens.py
python3 ./scripts/sorry_census.py --fail-on-holes
python3 ./scripts/axiom_audit.py
./scripts/check-imports.sh
python3 ./scripts/check-docs-integrity.py
python3 ./scripts/kb/check_generated.py
python3 ./scripts/kb/lint.py --strict-cited-pages
```

If you specifically need to regenerate `ArkLib.lean`, use:

```bash
./scripts/update-lib.sh
```

If blueprint output matters and `leanblueprint` is missing:

```bash
python3 -m pip install leanblueprint
```

## CI Mapping

- [`../../.github/workflows/ci.yml`](../../.github/workflows/ci.yml)
  runs the timing-enabled main build on PRs and pushes to `main`, measures a
  clean build, a warm rebuild, and the `./scripts/validate.sh` path, then
  uploads timing artifacts and posts a comparison report on same-repo PRs.
  It also enforces the issue #47 verification gates: a fast precheck rejecting
  `native_decide`/`bv_decide`/custom `axiom` declarations in live source
  (`scripts/forbidden_tokens.py`), a comment-stripped sorry census requiring
  zero live holes (`scripts/sorry_census.py --fail-on-holes`), and a
  `#print axioms` sweep over the pinned flagship list
  (`scripts/axiom_audit.py` reading `scripts/flagship_axioms.txt`) that must
  stay within `propext`, `Classical.choice`, `Quot.sound`. Renaming or
  deleting a pinned flagship theorem without updating the list is a hard CI
  failure. As of issue #111 these same three gates also run from
  `./scripts/validate.sh`, so local validation matches CI.
- The forbidden-token precheck rejects every custom `axiom` *except* the
  documented, tracked residuals listed in
  [`../../scripts/residual_axioms.txt`](../../scripts/residual_axioms.txt) (route (a)
  of #111). Each allowlist entry names one residual axiom and the issue that owns its
  eventual discharge; an undocumented or newly added `axiom` still fails the gate, and a
  stale allowlist entry (matching no live axiom) prints a warning to prompt cleanup.
  `scripts/forbidden_tokens.py` also accepts explicit Lean files or directories for
  focused checks; stale allowlist warnings are only meaningful on the default full-tree scan.
- [`../../.github/workflows/check-imports.yml`](../../.github/workflows/check-imports.yml)
  checks that `ArkLib.lean` matches the tracked source tree.
- [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml)
  checks local markdown links and the `CLAUDE.md` symlink.

## Manual Timing Helper

If you need to reproduce the timing workflow locally, the same helper script can
capture a measurement and render a report:

```bash
bash scripts/build_timing_report.sh run clean_build /tmp/build-timing.jsonl -- \
  bash -eo pipefail -c 'rm -rf .lake/build && lake build'
bash scripts/build_timing_report.sh render /tmp/build-timing.jsonl
```
