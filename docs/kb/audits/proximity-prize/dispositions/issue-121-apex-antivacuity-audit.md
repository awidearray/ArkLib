# Issue #121 — anti-vacuity audit of the apex prize theorems

**Standing audit.** `scripts/proximity_prize_cleanroom_audit.py` +
`scripts/proximity_prize_cleanroom_targets.txt` enforce, for each apex declaration, the
two *syntactic* clean-room conditions: (a) no residual `Prop` hypotheses, and (b) the
conclusion token does not appear among the hypotheses (the goal-equivalent-assumption /
F4 trap). This note records the *semantic* third condition the token scanner cannot
see — whether the conclusion's **content** is non-degenerate — for the two apex theorems
in `ArkLib/Data/CodingTheory/ProximityGap/GrandChallengePrizeResolution.lean`.

## `prizeResolution_ld` (list-decoding side) — genuinely non-vacuous ✓

Signature: `(domain) (hm : 0 < m) (hι : 2 ≤ n)` — only concrete positivity side
conditions, no `Prop` math residual. Conclusion:

```
¬ listDecodingPrize domain m
  ∧ (∀ k ≤ n, grandListDecodingChallengeRS domain k m ε* ↔ q^(k·m) ≤ ε*·q)
  ∧ IsEmpty (GrandListResolution (RS[F,domain,⌊n/2⌋]) m ε*)
```

A conjunction of a **negation**, a **closed-form characterisation**, and an **`IsEmpty`**.
None of these can be vacuously inflated: the negation and `IsEmpty` carry strictly
positive content (they *refute* the prize predicate and *empty* the resolution type), and
the closed form `q^{k·m} ≤ ε*·q` pins the exact arithmetic reason the prize fails
(LHS `≥ q²`, RHS `< q`). This is the honest negative deliverable. No caveat.

## `prizeResolution_mca_M521` (MCA side) — correct, but content = radius-one bound only ⚠

Signature: **zero hypotheses** (fully closed at `ι = Fin 16`, `F = ZMod M₅₂₁`). Conclusion:
`mcaPrize prizeDomain ∧ ∀ j, Nonempty (GrandMCAResolution (RS[…ρⱼ…]) ε*)`.

**Caveat (the F6 collapse, made explicit).** The witnessing `GrandMCAResolution`
(`grandMCAResolution_of_large_field`, `GrandChallengeResolutionWitness.lean`) sets

```
δStar := 1
```

The `GrandMCAResolution` structure's `maximal` field is
`∀ δ, δStar < δ → δ ≤ 1 → ε_mca(C, δ) > ε*`. At `δStar = 1` its premise `1 < δ ∧ δ ≤ 1`
is **unsatisfiable**, so `maximal` is discharged by
`absurd (lt_of_lt_of_le h1δ hδ1) (lt_irrefl 1)` — i.e. it is **vacuously true and carries
no content**. The *entire* genuine content of the MCA resolution is therefore the single
`bound` field:

```
ε_mca(C, 1) ≤ ε*        (epsMCA_one_eq_choose_div: = C(n, k+1)/|F| ≤ ε*)
```

i.e. the **radius-one** MCA bound. This is exactly the documented collapse
`GrandChallengeCollapse.mcaPrize_iff_forall_epsMCA_one` /
`grandMCAChallenge_iff_epsMCA_one`: the *formal* `mcaPrize` predicate is satisfied by the
trivial maximal threshold `δStar = 1` whenever the radius-one bound holds.

**Verdict.** `prizeResolution_mca_M521` is **honest and correct** as a resolution of the
*formal/collapsed* `mcaPrize` encoding. It does **not** determine the genuine ABF26 MCA
decoding threshold (the actual prize question), because the `maximal` clause asserts
nothing at `δStar = 1`. Any downstream reading of this theorem as a *genuine-threshold
determination* would be the F6 over-claim, and is incorrect.

## Outstanding

- `#print axioms` transitive check (axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`},
  no `sorryAx`) is **pending a green build** — blocked by the #110 toolchain migration. The
  source is free of `sorry`/`axiom`/`admit`; the only `native_decide` mentions are docstrings
  stating that Mersenne-521 primality uses kernel `decide` (Lucas–Lehmer), not `native_decide`.
  Re-run `lake env lean` + `#print axioms` on the new mathlib baseline to confirm.

*Filed by the #121 anti-vacuity audit, 2026-06-07. Cross-refs: F4 trap and F6 collapse in
`docs/kb/audits/proximity-prize/GRIND-LEDGER.md`; `GrandChallengeCollapse.lean`.*
