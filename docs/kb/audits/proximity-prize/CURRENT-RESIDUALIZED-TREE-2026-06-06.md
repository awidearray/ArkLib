# ArkLib residualized tree audit snapshot (2026-06-06)

This is a source-map snapshot for the proximity-prize audit notes in this ArkLib checkout, not a
live GitHub issue-status ledger. Older notes in this directory preserve campaign history and may
mention old raw-hole line numbers such as `Curves.lean:1819`; treat those as historical
breadcrumbs, not current locations.

## Current shape

The live ArkLib tree mostly exposes unfinished work as named residual APIs, explicit hypothesis
bundles, documentation-only roadmap notes, or opaque stand-ins. The old "single raw sorry at a line"
framing is no longer accurate for the BCIKS20/FRI/STIR/WHIR proximity-gap campaign.

## Historical tracking issue map

Use focused GitHub issues as the active work index. The tables below preserve the campaign issue
map from the first and second audit passes; their `State` cells are historical and may be stale
after later issue splits such as #64-#87. For live ownership, run:

```sh
gh issue list -R lalalune/ArkLib --state open --limit 100
gh issue list -R lalalune/ArkLib --state all --limit 200 --json number,title,state
```

### Proximity-prize residual buckets (#6-#23, first pass)

| Area | Issue | State |
|---|---|---|
| Umbrella proof-gap audit | #6 | closed |
| BCIKS20 correlated agreement residuals | #7 | open |
| BCIKS20 Claim 5.7 residuals | #8 | open |
| BCIKS20 Appendix-A Hensel residuals | #9 | open |
| Hab25 Johnson-range MCA residuals | #10 | open |
| ABF26 Lemma 4.6 hard direction | #11 | open |
| GG25 line-decodability multi-gamma coverage | #12 | open |
| LogUp Protocol 2 residuals | #13 | open |
| Batched FRI query soundness | #14 | open |
| Duplex-sponge Fiat-Shamir placeholder | #15 | open |
| ToyProblem KoalaBear placeholder | #16 | open |
| SendWitness knowledge-soundness placeholders | #17 | open |
| ToyProblem protocol and leaderboard residual anchors | #18 | open |
| RingSwitching/Binius completeness plumbing | #19 | open |
| WHIR MCA conjecture placeholders | #20 | closed |
| External coding-theory theorem residual APIs | #21 | closed |
| CS25/BCHKS/BGKS bridge residuals | #22 | open |
| Stale proximity-prize docs cleanup | #23 | closed |

### Protocol, keystone, and infrastructure follow-ups (#24-#38)

| Area | Issue | State |
|---|---|---|
| FRI/STIR soundness accounting and proximity-gap residuals | #24 | open |
| OracleReduction sequential-composition and Fiat-Shamir run-equality | #25 | open |
| Placeholder commitment/folding module disposition | #26 | closed |
| L13 keystone: betaRec witness for β existence | #27 | open |
| ToyProblem rewinding-extractor wiring | #28 | closed |
| RingSwitching coordinated KState weakening | #29 | open |
| Leaderboard Phase-5: concrete KoalaBear code + numeric anchors | #30 | open |
| L6.12 Step-4 ToyStep4 injection into SoundnessBounds | #31 | closed |
| Binius: CompBinius new-API Prelude port | #32 | open |
| Binius Steps: 9 named residuals after Prelude port | #33 | open |
| Environment: toolchain churn + Mathlib rebuild | #34 | open |
| Verification debt: axiom audits pending rebuild | #35 | open |
| Final global verification: green root build + census | #36 | open |
| Relations.getMidCodewords_succ legacy iterated_fold migration | #37 | closed |
| BKR06 final arithmetic side conditions | #38 | open |

### External theorem formalization buckets (#48-#54)

| Area | Issue | State |
|---|---|---|
| ABF26 §4 CapacityBounds external CA/MCA theorem family | #48 | open |
| Johnson-family bounds: Joh62 Jqℓ + MDS Johnson corollary | #49 | open |
| GGR11 interleaved list-size recursion + erase-decode tree | #50 | open |
| Multiplicative rigidity: product-coset + in-band cluster bounds | #51 | open |
| MCAGS beyond-UDR GS-list mass bound | #52 | open |
| GK16/CZ25 folded-RS subspace-design and capacity inputs | #53 | closed |
| ABF26 §3 list-decoding theorem family in ListDecoding/Bounds | #54 | open |

### Process, debt tracking, and external actions (#40-#47)

| Area | Issue | State |
|---|---|---|
| Grand LD value question after RIM/AGL24 refutation | #40 | closed |
| RIM/AGL24 derandomization counterexample formalization | #41 | closed |
| External-irreducible literature admits (honest debt) | #42 | closed |
| Permanently blocked items (disproven mathematics) | #43 | closed |
| Upstream PRs to Verified-zkEVM/ArkLib | #44 | open |
| Send ABF26 errata to Proximity Prize judges | #45 | open |
| Write-ups: three publishable notes | #46 | closed |
| CI: lake build + axiom audit + sorry census | #47 | closed |

## Grand Challenges

The prize Grand Challenges remain open research, tracked separately from the residual buckets
above. Distinguish four kinds of grand-challenge work when claiming or filing issues:

* **Collapsed real-threshold predicates** — the formal Grand MCA / Grand LD statements whose
  real-number thresholds were collapsed to predicate form during residualization; see #55 for the
  missing MCA-attainment counterpart / stale-reference repair.
* **Faithful lattice threshold values** — replacing collapsed predicates with faithful
  lattice-encoded threshold values: canonical bridges between singular and plural lattice
  encodings (#58), and discharging the numeric Johnson/Elias certificates at the faithful
  thresholds (#56).
* **Radius-one middle-band extremal count** — the exact bad-scalar extremal count in the
  remaining middle band for radius one (#39); the boundary `mu_8` list-of-three witness already
  landed.
* **Concrete four-rate MCA/LD lattice instantiation** — instantiating faithful lattice-threshold
  brackets at the four prize rates for Grand MCA (#57) and the matching Grand LD certificates
  (#56).

The post-refutation value state (after the RIM/AGL24 derandomization counterexample, #40/#41) is
documented in the repo alongside the counterexample formalization; the dead derandomization route
is formalized so it cannot regress.

## Historical notes

The following notes are retained for provenance but are not current inventories. Where an old
note says "issues #6-#23", read it as "the issue map in this index", which now extends through
the grand-challenge second pass (#39-#59):

* `GRIND-LEDGER.md` records the June 5 bottom-up campaign and still contains old
  `Curves.lean:1819` breadcrumbs.
* `integration-2026-06-05/NOTES.md` records an isolated integration attempt and explicitly says the
  old keystone did not close against that base.
* `dispositions/*.md` files are campaign-specific dispositions; prefer the issue list above for
  current ownership and open work.

## Audit commands

Raw proof-hole and placeholder census:

```sh
rg -n --glob '*.lean' '^\s*(sorry|admit)\b|:=\s*(by\s+)?(sorry|admit)\b|by\s+(sorry|admit)\b|\baxiom\s+[A-Za-z_]|opaque\s+[A-Za-z_]' ArkLib
rg -n --glob '*.lean' '^(noncomputable\s+)?(def|structure|class|theorem|lemma)\s+\w*Residual\w*|\b\w*Residual\w*\s*:' ArkLib
rg -n --glob '*.lean' 'opaque\s+\w+|placeholder|stub|TODO|FIXME|named residual|explicit hypothesis|remaining unproven|only remaining|sole residual|single remaining' ArkLib
```

Live issue map refresh:

```sh
gh issue list -R lalalune/ArkLib --state all --limit 200 --json number,title,state
```

Historical proximity-prize note scan:

```sh
rg -n --glob '*.md' 'Curves\.lean:1819|Agreement\.lean.*11|raw pass|sorry@|admit@|Current ArkLib.*ac6dc78a|arklib-sorry-fixes|Curves\.lean:1288' docs/kb/audits/proximity-prize
```
