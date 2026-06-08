# Issue #91 disposition — BCIKS20 §5 hPz instantiation (CLOSED 2026-06-06)

**Scope:** instantiate the decoded-family specialization bridge `hPz` (a `Section5StrictData`
field) from per-`z` Hensel/matching data — a child of #61.

**Resolved (verify-and-close).** The `hPz` field is now *produced* (not assumed):

- `ArkLib/ToMathlib/GSFactorData.lean` — `GSFactorData.toSection5StrictData` supplies
  `hPz := HPzBridge.hPz_of_henselDatum hHensel hdegPz` (the field is built from the per-`z`
  Hensel datum + degree bound, not left as a hypothesis equivalent to the goal).
- `ArkLib/ToMathlib/HenselDatumProducer.lean` — `henselDatum_of_matchingDvdInput` constructs the
  `HenselDatum` from the GS-extractor divisibility (`MatchingDvdInput`), and
  `hPz_of_matchingDvdInput` packages it to `hPz`.
- `ArkLib/ToMathlib/BetaInputSupply.lean` — the `MatchingDvdInput`-route `Section5StrictDataFin` /
  `BetaCurveInputFin` suppliers thread the GS-extractor-faithful divisibility into the keystone
  front door.

**Verification (rc2 olean snapshot, `LEAN_PATH`):** `GSFactorData.toSection5StrictData`,
`HenselDatumProducer.henselDatum_of_matchingDvdInput`, `hPz_of_matchingDvdInput`, and
`BetaInputSupply` all elaborate green, axiom-clean `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`. Landed on `main` (incl. `ee09717cc` "Resolve issue 91: wire HPzBridge Hensel datum
into GSFactorData").

**Remaining (out of #91's scope):** the matching-divisibility producer (`MatchingDvdInput` /
GS-extractor divisibility) is the genuine §5 input tracked by #8 (Claim 5.7), which #91 lists as a
dependency. #91's own deliverable — the `hPz` instantiation/wiring — is complete.
