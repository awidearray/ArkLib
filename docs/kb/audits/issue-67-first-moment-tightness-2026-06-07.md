# Issue #67 — GCXK25 first-moment: per-codeword bound tightness analysis

Date: 2026-06-07. Independent mathematical verification (no code change).

## Result

The in-tree per-codeword bound `|mcaBadWitness w| ≤ max(1, 2δn)`
(`mcaBadWitness_card_le_two_delta_mul_card`, `GKL24FirstMoment.lean`) is **worst-case
tight**, and GCXK25's sharp `|Bad¹| ≤ δn` is provably **not** achievable by any per-codeword
argument. The remaining work is necessarily the global / codeword-pair first moment.

## Definitions (recall)

For a stack `(u₀, u₁)`, code `MC`, radius `δ`, and a fixed codeword `w ∈ MC`:
- `mcaBadWitness w = { γ : ∃ S, |S| ≥ (1−δ)n, w = u₀ + γ·u₁ on S, ¬pairJointAgreesOn S }`.
- `secondSupport u₁ = { i : u₁ i ≠ 0 }`,  `secondZeros u₁ = { i : u₁ i = 0 }`,
  `|secondSupport| + |secondZeros| = n`.
- Full agreement set `A_γ := { i : w i = u₀ i + γ·u₁ i } ⊇ S` (so `|A_γ| ≥ (1−δ)n`).

## Pairwise obstruction (the source of the factor 2)

For two **distinct** bad scalars `γ ≠ γ'` witnessed by the same `w`: on `A_γ ∩ A_{γ'}`,
`u₀ + γ·u₁ = w = u₀ + γ'·u₁` ⟹ `(γ − γ')·u₁ = 0` ⟹ `u₁ = 0`. Hence
`A_γ ∩ A_{γ'} ⊆ secondZeros u₁`, so

    (1 − 2δ)·n  ≤  |A_γ| + |A_{γ'}| − n  ≤  |A_γ ∩ A_{γ'}|  ≤  |secondZeros u₁|.

**Two distinct bad γ exist only when `|supp u₁| = n − |secondZeros| ≤ 2δn`.**

## Sharp case split (proves the `max` and its tightness)

- `|supp u₁| > 2δn`  ⟹  at most **one** bad γ  ⟹  `|mcaBadWitness w| ≤ 1`.
- `|supp u₁| ≤ 2δn`  ⟹  `|mcaBadWitness w| ≤ |supp u₁| ≤ 2δn`
  (each bad γ = `combiningPoint w u₀ u₁ i` for some `i ∈ supp u₁`;
  `mcaBadWitness_subset_image_combiningPoint`).

The pointwise supremum over `|supp u₁|` is attained at `|supp u₁| = 2δn`, giving exactly `2δn`.
So **no per-codeword refinement beats `2δn`.** The factor 2 is intrinsic to the two-witness
symmetric-difference step: a single witness certifies only `(1−δ)n` agreement, never the
`u₁`-vanishing that a `δn` charge would require.

## Consequence for #67 / ABF26 T5.1

GCXK25's `|Bad¹| ≤ δn` is the **global / codeword-pair** first moment, not the per-codeword
sum. It charges over the maximal agreement domain across the list `𝓛`; the `L²` factor is the
codeword-PAIR index (consistent with the `Bad(π₁,π₂,δ)` framing). The clean in-tree assembly
`|mcaBad| ≤ Σ_{w∈𝓛} |mcaBadWitness w| ≤ |𝓛|·2δn` (via `mcaBad_subset_biUnion_mcaBadWitness`
+ `card_biUnion_le`) yields `ε_mca ≤ 2L·δ` — the first-moment half, a factor 2 from the sharp
global `δn`. Remaining work is therefore the global/pair charging (the maximal-domain argument
the witness-cover interface bricks are targeting), **not** any per-codeword sharpening.
