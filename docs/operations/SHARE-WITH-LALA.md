# ArkLib audit — links for review

Hi Lala — production-readiness / LARP audit work lives on **awidearray's public fork** only (not on `Verified-zkEVM/ArkLib`).

**Repo:** https://github.com/awidearray/ArkLib

---

## Pull requests (open)

| PR | Title | Link |
|----|--------|------|
| **#1** | fix(audit): honest axiom naming and sorry-tracker fetch behavior | https://github.com/awidearray/ArkLib/pull/1 |
| **#2** | refactor(#110): split GrandChallengesLattice into focused submodules | https://github.com/awidearray/ArkLib/pull/2 |
| **#3** | chore: production-readiness infrastructure and security scanning | https://github.com/awidearray/ArkLib/pull/3 |

---

## Audit issues (open)

| Issue | Title | Link |
|-------|--------|------|
| **#4** | Infrastructure: `lake exe cache get` fails with HTTP 403 in restricted networks | https://github.com/awidearray/ArkLib/issues/4 |
| **#5** | Audit: Grand Challenge prize resolution formalizes collapsed predicates, not external conjectures | https://github.com/awidearray/ArkLib/issues/5 |
| **#6** | Audit: 10 allowlisted residual axioms remain paper imports in flagship paths | https://github.com/awidearray/ArkLib/issues/6 |
| **#7** | Audit: Proximity prize open surfaces blocked on research mathematics | https://github.com/awidearray/ArkLib/issues/7 |

---

## Branches

| Branch | Link |
|--------|------|
| `fix/larp-audit-honesty-labeling` | https://github.com/awidearray/ArkLib/tree/fix/larp-audit-honesty-labeling |
| `refactor/issue-110-grand-challenges-lattice-split` | https://github.com/awidearray/ArkLib/tree/refactor/issue-110-grand-challenges-lattice-split |
| `chore/production-readiness-infrastructure` | https://github.com/awidearray/ArkLib/tree/chore/production-readiness-infrastructure |

---

## What each PR fixes

### PR #1 — LARP / honesty labeling
- Renames `CapacityBoundsProofs` `*_proven` → `*_from_paper_axiom` (44 axiom wrappers)
- Clarifies Grand Challenge prize docs (F6 collapse vs external conjecture)
- `sorry-tracker.py`: real URL fetch, fails loud (no simulated content)
- `ci-axiom-audit.sh` → `axiom_audit.py`
- Related issues: **#5**, **#6**

### PR #2 — GrandChallengesLattice split (#110)
- Splits ~3.8k-line monolith into 7 submodules under `GrandChallengesLattice/`
- Updates `ArkLib.lean` imports (+7)
- Related issue: **#5**

### PR #3 — Production readiness
- `production-readiness-check.sh`, `security-scan.sh`, CI security workflow
- `docs/operations/PRODUCTION-READINESS.md` (rollback + monitoring)
- `validate.sh` gates (cleanroom audit + security scan)
- Related issue: **#4** (cache 403 blocks full `validate.sh` locally)

---

## Issue ↔ PR map

| Issue | Tracks | PR |
|-------|--------|-----|
| [#4](https://github.com/awidearray/ArkLib/issues/4) | Mathlib cache 403 — blocks full validate | [#3](https://github.com/awidearray/ArkLib/pull/3) |
| [#5](https://github.com/awidearray/ArkLib/issues/5) | Prize “resolution” = collapsed predicates | [#1](https://github.com/awidearray/ArkLib/pull/1), [#2](https://github.com/awidearray/ArkLib/pull/2) |
| [#6](https://github.com/awidearray/ArkLib/issues/6) | 10 allowlisted paper axioms | [#1](https://github.com/awidearray/ArkLib/pull/1) |
| [#7](https://github.com/awidearray/ArkLib/issues/7) | Open research math (#138–#141 class) | (informational) |

---

## Quick copy-paste list

```
Repo:     https://github.com/awidearray/ArkLib
PR #1:    https://github.com/awidearray/ArkLib/pull/1
PR #2:    https://github.com/awidearray/ArkLib/pull/2
PR #3:    https://github.com/awidearray/ArkLib/pull/3
Issue #4: https://github.com/awidearray/ArkLib/issues/4
Issue #5: https://github.com/awidearray/ArkLib/issues/5
Issue #6: https://github.com/awidearray/ArkLib/issues/6
Issue #7: https://github.com/awidearray/ArkLib/issues/7
```
