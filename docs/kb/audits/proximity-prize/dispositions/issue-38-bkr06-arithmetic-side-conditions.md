# Issue #38 — BKR06: final arithmetic side conditions (hparam + nonneg)

**Status:** Closed / resolved. Verified green and axiom-clean under `leanprover/lean4:v4.30.0-rc2`
on 2026-06-06.

## Ask

The tight chain `BKR06.bkr06_tight_family_hfamily_unconditional` was proven *modulo* pure
parameter algebra:

- the `hparam` exponent identity `(m·u − v²) = (α − β²)·log q` (under `v ≈ β·m`, `k = q^u`),
- the `v² ≤ m·u` nonnegativity / cutoff side condition,
- the ordering `u ≤ v ≤ m`,
- the `hclose` agreement→δ final wiring connecting the tight family to a close-codeword count.

## Resolution (already on disk, this issue only verified + recorded it)

All side conditions are discharged in-tree; nothing is left as a hypothesis bundle, residual
`Prop`, or `sorry`. The discharge ladder lives in
`ArkLib/ToMathlib/SubspacePolyLinearized.lean` and `ArkLib/ToMathlib/BKR06EndToEnd.lean`:

- `bkr06CutoffIndex m v := ⌈v²/m⌉` (`(v² + m − 1) / m`) — the explicit `k = q^u` cutoff window.
  - `le_mul_bkr06CutoffIndex` proves `v² ≤ m · bkr06CutoffIndex m v` (the **nonneg** side condition).
  - `bkr06CutoffIndex_le` proves `bkr06CutoffIndex m v ≤ v` from `v ≤ m` (the **ordering** side condition).
- `bkr06_tight_family_hfamily_param_free` — **`hparam` eliminated**: instantiates
  `α := (m·u − v²)/log q`, `β := 0` (using `log q ≠ 0` from `2 ≤ q`), so the conclusion is stated
  at the concrete tight exponent `q^{m·u − v²}` with no `α`/`β` hypothesis.
- `bkr06_tight_family_hfamily_alpha_of_beta` — the α/β-form connector: for *any* `β`, the explicit
  `α := β² + (m·u − v²)/log q` satisfies the parameter identity, reproducing BKR06's bare
  `q^{(α−β²)·log q}` exponent bookkeeping under the `v ≈ β·m`, `k = q^u` convention.
- `bkr06_tight_family_explicit` — **all side conditions discharged at once**: at the explicit
  cutoff the only remaining inputs are `2 ≤ q`, `#F = q`, and `v ≤ m`.
- `bkr06_close_codewords_card_ge_tight` (`BKR06EndToEnd.lean`) — the end-to-end capstone wiring
  `hclose` (`mem_closeCodewordsRel_of_subspace`), `hsmall` (degree window), `hdistinct`
  (pigeonhole injectivity) and the final count (`bkr06_family_close_codewords_card_ge`) into a
  close-codeword lower bound `q^{m·u − v²}` at relative radius `δ = 1 − (#K)^{β−1}` in
  `RS[K, K, q^u + 1]`.

The "infinitely-many-prime-powers witness sequence" is the universal quantification over the
field pair `(F, K)` with `Fintype.card F = q` for arbitrary `q ≥ 2` carried by every theorem above;
each prime power instantiates `F`.

## Verification

- `lake build ArkLib.ToMathlib.BKR06EndToEnd` → **Build completed successfully (8345 jobs)**;
  only style linter warnings (`unusedDecidableInType`, `unnecessarySimpa`), no errors, no `sorry`.
- `#print axioms` on the full keystone set is kernel-clean:
  - `bkr06_close_codewords_card_ge_tight`, `bkr06_tight_family_hfamily_unconditional`,
    `bkr06_tight_family_hfamily_param_free`, `bkr06_tight_family_hfamily_alpha_of_beta`,
    `bkr06_tight_family_explicit` → `[propext, Classical.choice, Quot.sound]`.
  - `bkr06CutoffIndex` → `[propext]`; `le_mul_bkr06CutoffIndex`, `bkr06CutoffIndex_le` →
    `[propext, Quot.sound]`.
- `rg --pcre2 '(?<![\`\w])(sorry|admit)\b'` over the chain
  (`SubspacePolyLinearized`, `BKR06EndToEnd`, `BKR06Close`, `BKR06Injection`, `LinearizedSupport`,
  `BKR06SubspacePoly`) → 0 hits.

No `sorryAx`, no custom axioms, no residual `Prop`. Issue closed.
