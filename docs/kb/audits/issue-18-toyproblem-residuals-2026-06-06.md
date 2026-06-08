# Issue #18 ToyProblem Residual Audit

Date: 2026-06-06

Scope:

- `ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean`
- `ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean`
- `ArkLib/ProofSystem/ToyProblem/Spec/General.lean`
- `ArkLib/ProofSystem/ToyProblem/Leaderboard.lean`
- `ArkLib/ToMathlib/ToyStep4.lean`

## Result

The issue text is still live, but several anchors have already been narrowed from
old theorem-shaped placeholders into explicit residual propositions. The current
tree should not be treated as containing hidden ToyProblem `sorry`/`axiom`
closures for these surfaces:

- `simplified_iop_soundness_listDecoding_lb_residual` is now the genuine ABF26
  Section 6.4.1 Step-4 attack-data construction: relative-distance regime,
  linear encoder data, and an injective family of passing challenges.
- `simplified_iop_soundness_listDecoding_lb` derives the winning-set cardinality
  bound from that data through `ToyProblem.simplified_iop_listDecoding_lb_of_winningChallenges`.
  The cardinality inequality itself is no longer assumed as the residual.
- The useful fixed-encoding repair from old branch `origin/feat/abf26-plan` is
  already present on current `main`: `relationFor`, `relaxedRelationFor`,
  `winningSetFor`, `relaxedRelationFor_imp`, and `winningSetFor_subset` in
  `Definitions.lean`, together with witness-bearing fixed-encoding output
  relations in the ToyProblem specs. Do not merge that stale branch wholesale;
  its remaining ToyProblem hunks are superseded by current split files and
  include old proof/doc scaffolding.
- `protocol62_knowledgeSound_residual`, `protocol62_rbrKnowledgeSound_residual`,
  and `simplifiedIOR_knowledgeSound_residual` are all reducible aliases for the
  single straightline-from-rewinding bridge
  `Bridge.StraightlineOfRewinding`.
- `winningSetSoundness_le_toySoundnessError_residual` remains the ABF26 Lemma
  6.10 upper-bound obligation, exposed as an explicit `Prop`.
- The KoalaBear leaderboard carrier now uses `KoalaBear.rsCodeSet`; the old
  opaque carrier path is not the live blocker. The concrete attack-side anchor
  reduces to `fenziSanso_upperBound_attack_concrete_residual`, a winning-set
  cardinality witness of size at least `2^70`.  The bridge theorem
  `fenziSanso_upperBound_attack_residual_of_concrete` now feeds that concrete
  residual back into the canonical `fenziSanso_upperBound_attack_residual`, so
  downstream code can keep the original 116-bit attack anchor name while proving
  only the concrete Phase-5 cardinality statement.

## Audit command

```sh
rg -n 'residual|Residual|opaque koalaCode|StraightlineOfRewinding|winningSetSoundness|simplified_iop_soundness|protocol62_knowledgeSound|protocol62_rbrKnowledgeSound|arklib_lowerBound|fenziSanso' \
  ArkLib/ProofSystem/ToyProblem
```

## Remaining proof tracks

1. Construct the ABF26 Section 6.4.1 distinct-challenge family from the
   list-decoding data, discharging `simplified_iop_soundness_listDecoding_lb_residual`.
2. Prove the framework bridge from the already-proven rewinding extractor
   predicate to the straightline and round-by-round knowledge-soundness APIs,
   discharging the three `Bridge.StraightlineOfRewinding` consumers.
3. Prove ABF26 Lemma 6.10 for the simplified IOR, or replace it with a repaired
   Johnson-radius / MCA-safe theorem matching the current code comments,
   discharging `winningSetSoundness_le_toySoundnessError_residual`.
4. Prove the concrete KoalaBear winning-set cardinality witness behind
   `fenziSanso_upperBound_attack_concrete_residual`.  The field-cardinality,
   explicit-power arithmetic, and canonical-attack-anchor bridge around the
   `2^(-116)` target are already separated from this coding-theory obligation.

This audit does not close issue #18. It records the live residual surface so the
next repair can target the remaining mathematical and framework obligations
rather than reworking already-narrowed placeholders.
