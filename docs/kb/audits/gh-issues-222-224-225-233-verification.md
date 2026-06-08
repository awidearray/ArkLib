# Issue Audit: GitHub Issues #222, #224, #225, #233 (Guruswami-Sudan / Interleaved-code sorries)

This page is a verification audit of four "proof wanted" GitHub issues against the current
upstream (`origin/main`-equivalent) state of the worktree. Each issue was a `sorry` to fill.
The goal is to determine, with file/line evidence, whether the issue is genuinely discharged
by the current code, subsumed by a renamed/relocated result, made moot by an API change, or
still open.

All work was read-only against branch `gh-issues`. The relevant module was compiled and the
target theorems passed an axiom probe (acceptable axioms only).

## Status Legend

- `RESOLVED-UPSTREAM`: the issue's theorem now exists, sorry-free, with an equivalent
  (or only inessentially modified) statement.
- `SUBSUMED`: the issue's mathematical content is carried out, sorry-free, under a different
  name / location; the original named declaration no longer needs to exist.
- `MOOT`: the API the issue referred to was removed/replaced; the lemma is no longer meaningful
  or needed.
- `STILL-OPEN`: the obligation is not discharged.

## Summary Table

| Issue | Subject | Verdict | Primary evidence |
| --- | --- | --- | --- |
| #233 | `decoder_mem_impl_dist` (soundness) | RESOLVED-UPSTREAM | `dist_le_of_mem_decoder`, GuruswamiSudan.lean:106-118 |
| #222 | `decoder_dist_impl_mem` (completeness) | RESOLVED-UPSTREAM (statement strengthened) | `mem_decoder_of_dist`, GuruswamiSudan.lean:122-260 |
| #224 | `guruswami_sudan_for_proximity_gap_property` (divisibility) | SUBSUMED (+ named lemma retained) | `dvd_property`, Basic.lean:884-950; `guruswami_sudan_for_proximity_gap_property`, GuruswamiSudan.lean:928-942 |
| #225 | `minDist_eq_minDist` (interleaved code) | MOOT | InterleavedCode.lean rewritten; no such symbol; 0 sorries |

## Axiom probe

Module `ArkLib.Data.CodingTheory.GuruswamiSudan.GuruswamiSudan` was built (olean produced
after the source mtime) and `#print axioms` was run via `lake env lean /tmp/gs_axiom_probe.lean`:

```
'GuruswamiSudan.dist_le_of_mem_decoder' depends on axioms: [propext, Classical.choice, Quot.sound]
'GuruswamiSudan.mem_decoder_of_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'GuruswamiSudan.guruswami_sudan_for_proximity_gap_property' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard Lean/Mathlib axioms appear. No `sorryAx`, no custom `axiom`, no
`opaque`. `grep` confirms the file
[`ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean`](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean)
contains zero `sorry` and zero `axiom`/`opaque` declarations.

## Per-issue findings

### #233 — `decoder_mem_impl_dist` (soundness) — RESOLVED-UPSTREAM

**Old (blueprint, v4.22.0) statement** with `opaque decoder ... := sorry`:

```lean
theorem decoder_mem_impl_dist
  {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))   -- e ≤ n - √(k·n)
  {ωs : Fin n ↪ F} {f : Fin n → F} {p : F[X]}
  (h_in : p ∈ decoder k r D e ωs f) :
  Δ₀(f, p.eval ∘ ωs) ≤ e := by sorry
```

**Current statement** (GuruswamiSudan.lean:106-118), sorry-free, against a real
`noncomputable def decoder` (GuruswamiSudan.lean:98-103):

```lean
theorem dist_le_of_mem_decoder
    {k r D e : ℕ}
    (_he : (e : ℝ) < ↑n - Real.sqrt ((↑k + 1) * ↑n))
    {ωs : Fin n ↪ F} {f : Fin n → F} {p : F[X]}
    (hin : p ∈ decoder k r D e ωs f) :
    Δ₀(f, p.eval ∘ ωs) ≤ e
```

- **Error-radius hypothesis.** The radius hypothesis is *unused* in the soundness proof
  (named `_he`), so any change to it is immaterial for #233. For the record, the new
  bound is `e < n − √((k+1)·n)` vs the old `e ≤ n − √(k·n)`. This is the rate-`(k+1)/n`
  Johnson radius matching `proximity_gap_johnson k n m = 1 − √ρ − √ρ/(2m)` with
  `ρ = (k+1)/n` (Basic.lean:34-36). It is *conservatively stronger* (smaller radius) than
  the old `√(k·n)` form, which is the safe direction for a soundness statement (a smaller
  admissible `e` only weakens the hypothesis pool; soundness holds for all `e` anyway).
- **Decoder is non-trivial.** `decoder` (GuruswamiSudan.lean:98-103) is *not* a constant.
  In the `if h : ∃ m, 0 < m ∧ e/n < proximity_gap_johnson k n m` branch it builds the real
  GS interpolation polynomial `Q := polySol k n h.choose ωs f` (Basic.lean:405) and returns
  `Q.roots.toList.filter (fun p ↦ hammingDist f (p.eval ∘ ωs) ≤ e)`. The else-branch returns
  `[]`. So the output is genuinely the distance-filtered root set, not `∅`/everything.
- **Not vacuous.** Soundness is proved by `simp [decoder]; split`: in the `then` branch it
  extracts `hin.2` directly from the `List.mem_filter` distance predicate; in the `else`
  branch `p ∈ []` is impossible (`simp at hin`). The conclusion follows from the filter, so it
  is true even when the output happens to be `[]` (trivially), and substantively when non-empty.
  This is exactly the intended soundness guarantee.

The theorem name changed (`decoder_mem_impl_dist` → `dist_le_of_mem_decoder`) but the
statement is equivalent (modulo the immaterial, strictly-safe radius change). Verdict:
**RESOLVED-UPSTREAM**.

### #222 — `decoder_dist_impl_mem` (completeness) — RESOLVED-UPSTREAM (statement strengthened)

**Old statement** (v4.22.0), with `sorry`:

```lean
theorem decoder_dist_impl_mem
  {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F} {f : Fin n → F} {p : F[X]}
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e) :
  p ∈ decoder k r D e ωs f := by sorry
```

**Current statement** (GuruswamiSudan.lean:122-260), sorry-free:

```lean
theorem mem_decoder_of_dist
    {k r D e : ℕ}
    (he : (e : ℝ) < ↑n - Real.sqrt ((↑k + 1) * ↑n))
    {ωs : Fin n ↪ F} {f : Fin n → F} {p : F[X]}
    (hdeg : p.natDegree < k)               -- NEW hypothesis
    (hdist : Δ₀(f, p.eval ∘ ωs) ≤ e) :
    p ∈ decoder k r D e ωs f
```

Hypothesis-by-hypothesis comparison:
- Radius: `e ≤ n − √(k·n)` → `e < n − √((k+1)·n)` (rate `(k+1)/n` Johnson radius; see #233).
- **`hdeg : p.natDegree < k` is a genuinely added hypothesis.** The old completeness claim had
  *no* degree restriction, which is in fact false/unprovable: a `p` of degree `≥ k` can be
  `e`-close to `f` yet need not be a `Y`-root of the degree-bounded GS witness `Q`. The decoder
  returns roots of `Q`, and only degree-`< k` (RS-codeword) candidates are guaranteed to divide
  `Q`. So the added hypothesis is the *correct* statement of GS completeness; the original issue
  statement was slightly under-specified. This is a meaningful (but mathematically necessary)
  strengthening of the hypothesis — flagged here so the maintainer can decide if it satisfies #222.
- **Proof is substantive, not vacuous.** The proof (1) discharges the `∃ m` existence inside
  `decoder` via the Archimedean property (GuruswamiSudan.lean:153-210), relating the ℚ-based
  `√ρ` in `proximity_gap_johnson` to the ℝ-based `√((k+1)·n)` in `he`
  (`hsqrtRel`, L173-180); then (2) enters the `dif_pos` branch and must show `p ∈ Q.roots`
  with `Δ₀ ≤ e`. The root membership is obtained from divisibility
  `X − C p ∣ polySol k n mDec ωs f` via `dvd_property` (L240-255) and
  `dvd_iff_isRoot`/`mem_roots polySol_ne_zero` (L257-260). `polySol_ne_zero` (Basic.lean:443)
  guarantees `Q ≠ 0`, so `Q.roots` is the real (finite) root multiset — the membership is not
  vacuous. The completeness direction therefore genuinely lands `p` in the decoder output.

Verdict: **RESOLVED-UPSTREAM**, with the caveat that the statement now carries the extra
(mathematically required) `p.natDegree < k` hypothesis.

### #224 — `guruswami_sudan_for_proximity_gap_property` (divisibility) — SUBSUMED

**Old statement** (v4.22.0), with `sorry`: for any GS-system solution `Q` and RS codeword
`p` with `Δ₀(w, P) ≤ δ₀(ρ, m)`, conclude `(Y − P(X)) ∣ Q` i.e. `(X − C (codewordToPoly p)) ∣ Q`
in `F[X][Y]`.

The mathematical core — "Condition (degree bound + multiplicity ≥ m) + closeness ⟹
`X − C P ∣ Q`" — is now carried out, sorry-free, by **`dvd_property`** in
[`ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean`](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean):884-950:

```lean
theorem dvd_property [DecidableEq F] (hk : k + 1 ≤ n) (hm : 1 ≤ m) (p : code ωs k)
    {Q : F[X][Y]}
    (hQ_deg : weightedDegree Q 1 (k - 1) ≤ proximity_gap_degree_bound k n m)
    (hQ_mult : ∀ i, m ≤ rootMultiplicity Q (ωs i) (f i))
    (h_dist : (hammingDist f (fun i ↦ (codewordToPoly p).eval (ωs i)) : ℝ) / n
                < proximity_gap_johnson k n m) :
    X - C (codewordToPoly p) ∣ Q
```

The proof (Basic.lean:891-950) is the genuine GS counting argument: by contraposition, if
`X − C P ∤ Q` then `R := Q.eval (codewordToPoly p) ≠ 0`; the agreement positions force
`rootMultiplicity ≥ m` at each, giving `deg R ≥ m·(n − dist)` (L895-936), while the weighted
degree bound gives `deg R ≤ proximity_gap_degree_bound` (L937-944), and
`sufficient_multiplicity_bound` (L945-950) closes the contradiction with the Johnson radius.
A rate-`k/n` variant `gs_dvd_property`/`gs_divisibility` (Basic.lean:1020+, GuruswamiSudan.lean:1041)
and a packaged `proximity_gap_divisibility` (GuruswamiSudan.lean:982-988) wrap the same result
against the `Conditions` structure.

In addition, the **named lemma `guruswami_sudan_for_proximity_gap_property` still exists** at
[GuruswamiSudan.lean:928-942](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean),
now sorry-free, but recast in the *constructive* (CompPoly witness / `isQRootRaw` / Hasse-derivative)
form, asserting Q-root extraction at every interpolation point for a `witnessCandidateSet`
member. This is a related-but-different statement from the classical `(Y − P) ∣ Q`; the classical
divisibility lives in `dvd_property`. The divisibility step the issue asked for is concretely
used inside `mem_decoder_of_dist` at GuruswamiSudan.lean:240-258.

Verdict: **SUBSUMED** — the classical `(Y − P(X)) ∣ Q` content is fully proved as
`dvd_property` (Basic.lean:884), and the original named lemma survives sorry-free in
constructive form (GuruswamiSudan.lean:928).

### #225 — `minDist_eq_minDist` (interleaved code) — MOOT

Maintainer comment on the issue: "The interleaved code APIs have been changed so this is not
needed anymore ... That file is deleted [content replaced]. Fundamental APIs for interleaved
codes are already done."

Code evidence on this branch:
- `grep -n "minDist_eq_minDist\|sorry\|axiom\|opaque"` over
  [`ArkLib/Data/CodingTheory/InterleavedCode.lean`](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean)
  returns **nothing** — there is no `minDist_eq_minDist` declaration and no sorry/axiom/opaque
  anywhere in the file.
- The file (806 lines, authors Hristova/Silváši/Nguyen) has been rewritten around a unified
  matrix-based API: `interleavedCodeSet`, `codewordStackSet`, `InterleavedWord`, `WordStack`,
  `CodewordStack` (InterleavedCode.lean:160-360), with distance handled via the relative-distance
  machinery `δᵣ`/`Δ₀` from
  [`ArkLib/Data/CodingTheory/Basic/Distance.lean`](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean)
  and `Basic/RelativeDistance.lean` (e.g. `relDistFromCode_eq_distFromCode_div`,
  `relDistFromCode_le_relDist_to_mem`). The substantive interleaved-code results are now
  `jointProximityNat_iff_closeToInterleavedCodeword` (L641) and
  `jointAgreement_iff_jointProximity` (L681), both proved.

The lemma the issue referenced no longer exists and the distance interface it depended on was
replaced; the obligation is no longer meaningful. Verdict: **MOOT** (consistent with the
maintainer's comment).

## Notes / caveats for the maintainer

- #233 and #233's twin #222 changed the Johnson-radius hypothesis from `√(k·n)` to
  `√((k+1)·n)`. This matches `proximity_gap_johnson`'s `ρ = (k+1)/n` and is the conservative
  (safe) direction; the file header (GuruswamiSudan.lean:89-93) documents this deviation
  explicitly.
- #222's `mem_decoder_of_dist` adds `p.natDegree < k`. This is mathematically required for a
  GS decoder that returns roots of a degree-bounded witness, but it is a strengthening of the
  literal issue statement. If #222 is meant to be the *literal* old statement (no degree bound),
  it would be **unprovable as written**; the upstream theorem is the corrected form.
- The named lemma `guruswami_sudan_for_proximity_gap_property` (#224) was kept but its statement
  was repurposed to a constructive form; the classical divisibility lives in `dvd_property`.
