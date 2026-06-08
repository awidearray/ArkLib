# ArkLib audit — issues & pull requests (2026-06-07)

**Repository:** [awidearray/ArkLib](https://github.com/awidearray/ArkLib) (public, open source)

All audit tracking and fix PRs live on this fork only — not on `Verified-zkEVM/ArkLib`.

---

## Fork branches

| Branch | Link |
|--------|------|
| `fix/larp-audit-honesty-labeling` | https://github.com/awidearray/ArkLib/tree/fix/larp-audit-honesty-labeling |
| `refactor/issue-110-grand-challenges-lattice-split` | https://github.com/awidearray/ArkLib/tree/refactor/issue-110-grand-challenges-lattice-split |
| `chore/production-readiness-infrastructure` | https://github.com/awidearray/ArkLib/tree/chore/production-readiness-infrastructure |

---

## Audit findings (issues)

| # | Title | Link |
|---|--------|------|
| 4 | Infrastructure: `lake exe cache get` fails with HTTP 403 in restricted networks | https://github.com/awidearray/ArkLib/issues/4 |
| 5 | Audit: Grand Challenge prize resolution formalizes collapsed predicates, not external conjectures | https://github.com/awidearray/ArkLib/issues/5 |
| 6 | Audit: 10 allowlisted residual axioms remain paper imports in flagship paths | https://github.com/awidearray/ArkLib/issues/6 |
| 7 | Audit: Proximity prize open surfaces blocked on research mathematics | https://github.com/awidearray/ArkLib/issues/7 |

---

## Fix pull requests

| PR | Title | Related issues | Link |
|----|--------|----------------|------|
| 1 | fix(audit): honest axiom naming and sorry-tracker fetch behavior | #5, #6 | https://github.com/awidearray/ArkLib/pull/1 |
| 2 | refactor(#110): split GrandChallengesLattice into focused submodules | #5 | https://github.com/awidearray/ArkLib/pull/2 |
| 3 | chore: production-readiness infrastructure and security scanning | #4 | https://github.com/awidearray/ArkLib/pull/3 |

---

## Issue ↔ PR map

| Issue | What it tracks | Addressed by |
|-------|----------------|--------------|
| [#4](https://github.com/awidearray/ArkLib/issues/4) | Mathlib cache HTTP 403 — blocks full `validate.sh` | Open; noted on [#3](https://github.com/awidearray/ArkLib/pull/3) |
| [#5](https://github.com/awidearray/ArkLib/issues/5) | Prize “resolution” = collapsed predicates, not external conjectures | Partial: [#1](https://github.com/awidearray/ArkLib/pull/1), [#2](https://github.com/awidearray/ArkLib/pull/2) |
| [#6](https://github.com/awidearray/ArkLib/issues/6) | 10 allowlisted residual paper axioms | Naming fix: [#1](https://github.com/awidearray/ArkLib/pull/1); proofs still open |
| [#7](https://github.com/awidearray/ArkLib/issues/7) | Proximity prize surfaces blocked on research math | Informational; no close PR |

---

## Docs

- [Production readiness checklist](https://github.com/awidearray/ArkLib/blob/chore/production-readiness-infrastructure/docs/operations/PRODUCTION-READINESS.md) (in PR #3)
