# F-series statement-defect catalogue

## Purpose

This note records statement-level defects found while formalizing the proximity-prize material. The
common lesson is that a failed Lean proof can reveal a paper-interface mismatch rather than a missing
tactic.

## Catalogue

### F1: Power-series substitution at off-center points

Mathlib's `PowerSeries.HasSubst` requires the substituted series to have nilpotent constant
coefficient. Over a field this means constant coefficient zero. For the BCIKS shift `X -> X - x0`,
that condition holds only at `x0 = 0`. Off-center substitution therefore needs an explicit
hypothesis or a different formal interface.

Formal anchor: `ArkLib/ToMathlib/SubstFieldCaveat.lean`.

### F2: Claim 5.11 dependency DAG

The Claim 5.11 route is not a single isolated counting lemma. It depends on a structured chain of
section data, matching-set hypotheses, numerator bounds, and boundary cardinality inputs. The
residualized API should keep that DAG visible instead of hiding it behind one opaque admit.

### F3: Telescope-style equalities

Several prose arguments use telescoping equalities across dependent transports. In Lean these become
separate transport lemmas, not rewriting trivia. Treating them as named bridge lemmas keeps the proof
surface honest.

### F4: Nominal bundling

Some statements quantify over data that is only nominally bundled in the paper. The formal version
must distinguish inputs, derived witnesses, side conditions, and residual hypotheses so downstream
theorems do not silently assume conclusions.

### F5: Universal t blowup

Arguments that move from fixed `t` to all `t` can introduce a hidden quantifier blowup. The formal
interface should state whether the witness data is uniform in `t` or reconstructed separately for
each `t`.

### F6: Real-delta challenge encoding collapse

Challenge encodings that are clean over discrete parameters can collapse when phrased with a real
`delta` before rounding. Formal statements should make the integer parameter and its real
interpretation separate objects with explicit comparison lemmas.

### F7: GK16 Lemma 12 bare statement is false

The bare statement `LinearIndependent F P -> foldedWronskian P omega != 0` is false without an
order hypothesis on `omega`: over a finite field the folded Wronskian can vanish when the
substituted point collides with a degree (deg 0 vs `orderOf omega`).

- False statement: linear independence alone forces the folded Wronskian nonzero.
- Witness/refutation: `not_lemma12_bare` (rationals, `s = 2`, `P = ![X, 1]`, `omega = 1`).
- Corrected form: the order hypothesis is genuinely necessary; the general hard direction holds
  *with* it. Proven as `foldedWronskian_ne_zero_of_linearIndependent` (via the monomial closed
  form `foldedWronskian_monomial = Vandermonde`, the top-coefficient identity
  `coeff_foldedWronskian_sum_natDegree`, and degree-echelon recombination
  `exists_distinctDegree_recombination`).
- Lives in `ArkLib/Data/CodingTheory/ProximityGap/GK16Lemma12.lean` (with the recombination helper
  in `ArkLib/ToMathlib/GK16Finish.lean`).

### F8: GK16 / ABF26 T2.18 admissibility — three coupled statement bugs

Formalizing the FRS half of ABF26 Theorem 2.18 exposed three distinct defects in the surrounding
injectivity / separation statements, each kernel-refuted and repaired.

- F8a — global `hEinj`. The statement "`frsEvalOnPoints` is injective on all of `F[X]`" is
  **unconditionally false** (an infinite-dimensional source maps to a finite-dimensional target).
  Witness/refutation: `frsEvalOnPoints_not_injective`. Corrected form: `InjOn` of the evaluation on
  `Polynomial.degreeLT F k`, which holds under `k <= s * |iota|`.
- F8b — `Admissible` docstring over-claim. The conjuncts of `Admissible L s omega` do **not** by
  themselves give fold-point injectivity: with `omega = 0` and `s >= 2` the folds collapse
  (witness `L = {1, 2}` over `GF(5)`). Corrected form: the minimal repair is the explicit side
  condition `omega != 0` (proven).
- F8c — unbounded `homega_sep`. The unbounded degree-separation statement is **false in any finite
  field** (degree `0` and `orderOf omega` collide). Corrected form: separation restricted to
  degrees `< orderOf omega`, which the recombination respects since it keeps degrees
  `< k <= orderOf omega` (proven).
- Lives in `ArkLib/Data/CodingTheory/ProximityGap/GK16Admissible.lean` and
  `ArkLib/Data/CodingTheory/SubspaceDesign.lean`. With the repairs, T2.18's FRS half is proven
  unconditionally from `Admissible` data alone (`frs_is_subspaceDesign_gk16_of_admissible`).

### F9: CZ25 span-bound at negative effective radius; naive per-coordinate charge

The CZ25/Guruswami-Wang span residual was first stated as `CZ25SpanBound` without guarding the
effective radius, and a tempting elementary "per-coordinate charge" simplification of it is false.

- False statement: `CZ25SpanBound` as written holds in the reachable regime. It is false when the
  effective radius `delta_eff = 1 - tau(floor(1/eta)) - eta < 0` (here `m * eta` is forced
  negative and the inequality is unsatisfiable); admissible FRS profiles with `eta < 1/s` actually
  reach that regime.
- Witness/refutation: `cz25SpanBound_false_of_neg_radius` (kernel-clean). Corrected form: the
  delta-guarded `CZ25SpanBound'`, with faithfulness `cz25SpanBound'_of_dimensionCount` and the
  re-established T3.4 chain `subspaceDesign_list_decoding_cz25_of_spanBound'`.
- Separately, the naive per-coordinate charge `#{c : c_i = f_i} - 1 <= dim(A inter ker eval_i)` is
  **false past the Johnson radius** (agreeing elements fill affine flats of `q^dim` points, not
  `dim + 1`). Sweep evidence: 28669/32635 failures in the numerical audit accompanying
  `CZ25SpanDimension.lean`; the span-dimension witness `m = dim span` likewise fails `|L| <= m + 1`
  (RS at `delta = 0.6`: `|L| = 10` vs `3`). Corrected form: the irreducible truth is
  `CZ25DimensionCount` (the full GW/Johnson iterative argument); the chain is pinned exactly there.
- Lives in `ArkLib/Data/CodingTheory/ListDecoding/CZ25SpanDimension.lean` (with the T3.4 packaging
  in `CZ25DesignToLambda.lean`).

### F10: Claim 5.7 `hfactor` is structurally unprovable as stated

The BCIKS20 Claim 5.7 side condition `hfactor` equates two factor lists that only coincide in the
separable case. As stated it cannot be proven; the divergence is a genuine characteristic-`p`
phenomenon, not a missing tactic.

- False statement: `pg_Rset := normalizedFactors Q` (`Extraction.lean:724`) equals the descended
  primitive-separable factor list (`Extraction.lean:340`). These agree only in the
  separable / `nn = 1` case; in characteristic `p` an inseparable normalized factor is a proper
  `p`-power image of its descended root, so the lists genuinely differ.
- Witness/refutation: the char-`p` divergence argument recorded in
  `Claim57FieldDischarge.lean`; the honestly-provable fragment is
  `claim57_hfactor_irreducible_of_pg_Rset` (every `pg_Rset` member is irreducible — the true part).
- Corrected form: either redefine `pg_Rset` over the descended list, or accept `hfactor` as a
  permanent characteristic-`p` side condition (design decision, not a gap). The associated good-`x0`
  avoidance is proven (`exists_good_x₀_evalX_discr_y_ne`).
- Lives in
  `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Claim57FieldDischarge.lean`.

### F11: Middle-band radius-one threshold law is refuted; q* is not a function of C alone

The radius-one extremal count is a two-regime step (`P = q` for `q < C(n, k+1)`,
`P = C(n, k+1)` for `q >= q*`), but the conjectured transition threshold law is false.

- False statement: `q* = smallest prime >= C(n, k+1)` (i.e. `q*` depends only on `C := C(n, k+1)`).
- Witness/refutation: at `(n, k) = (6, 3)`, `C = 15`, the law predicts `q* = 17`, but an
  unconditional exhaustive `q^6` sweep gives `P(6, 3, 17) = P(6, 3, 19) = 14`, so `q* = 23`.
  Decisive: `(6, 1)` and `(6, 3)` share `C = 15` yet have `q* = 17` vs `23`, so `q*` is **not** a
  function of `C` alone. Obstruction: one forced collision among subset functionals from high
  pairwise overlap when `k` is near `n`. Sweep module: `scripts/pp_exp_middle_band.py`
  (with `tests/test_pp_exp_middle_band.py`).
- Corrected form: only the cardinality direction survives in closed form,
  `q* >= smallest prime >= C(n, k+1)`; the exact `q*` closed form is open. Companion: deep-hole
  `u1` is **not** extremal in the band (a general `u1` strictly wins below its covering threshold).
- Lives in the writeup `docs/kb/audits/proximity-prize/writeups/MIDDLE_BAND_RESOLUTION.md`; the Lean
  port (`MCAMiddleBand.lean`) is specified there and queued.

### F12: discriminant / evalX X-vs-Z variable mismatch

The sketched specialization-commutation identity for the Claim 5.7 discriminant type-checks but is
false, because the two sides specialize *different* variables of a trivariate object.

- False statement: `discr(evalX (C x0) R) = evalX x0 (discr_y R)`. The left side specializes the
  middle `X` variable; the right side specializes the inner `Z` variable. It type-checks (both are
  the right type) but is false — caught before any proof attempt succeeded.
- Witness/refutation: documented in `DiscriminantSeparable.lean`; the corrected same-variable form
  is `discr_map_of_natDegree_preserved` (the discriminant commutes with any ring map into a domain
  that preserves `natDegree`, via `resultant_deriv` + `resultant_map_map`).
- Corrected form: alongside the commutation fix, the missing mathlib converse
  `separable_of_discr_ne_zero` (`disc != 0 ⟹ Separable` over a field, via Bezout/resultant ⟹
  `IsCoprime` ⟹ `separable_def`) and the packaged payload
  `ne_zero_and_separable_of_specialized_discr_ne_zero` are proven. Consumer caveat: the
  `Z`-shaped good-`x0` producer (`exists_good_x₀_evalX_discr_y_ne`) must be reconciled with the
  `X`-shaped consumer — the F12 mismatch is precisely between those two; the reconciliation is
  `exists_good_x₀_X_shape_ne` (the same avoidance argument rerun against the `X`-specialization).
- Lives in `ArkLib/ToMathlib/DiscriminantSeparable.lean` (with the consumer reconciliation in
  `Claim57FieldDischarge.lean`).

## Experiment-side refutations (toy lattice Grand-MCA campaign)

The same defect discipline applies to conjectured *closed-form laws* surfaced by the toy-scale
lattice experiment campaign. Each refutation below is an exact (exhaustive or full-transversal,
not searched-only) counterexample, not an asymptotic heuristic. These sharpen, rather than close,
the mathematical prize.

### E1: interior law `q*eps_mca = 2*C(k+j-1, j-1)` refuted at (7,7,3)

The fine-structure conjecture that the window-interior weight equals twice the dimension of the
space of `k`-variate polynomials of degree `< j` is false.

- False statement: `q*eps_mca(j/n) = 2*C(k+j-1, j-1)` in the window interior.
- Witness/refutation: the `(7, 7, 3)` exhaustive run (5.76M transversal pairs) gives interior value
  `6` at `j = 2`, where the formula predicts `8` (raw) / `7` (capped). Module
  `scripts/pp_exp_fine_structure.py`. Nine rival closed forms were each refuted with exact
  counterexamples in the same module.
- Corrected form: `P[0] = 1` and `P[1] = 2` are universal (and now theorems — see below); the wide
  interior is governed by minor-variety root counting, not a single binomial formula. The proven
  wide-regime law is `P[j] = j + 1` for `n - k >= 2j + 1`
  (`scripts/pp_exp_jgeneral_theorem.py`, `JGENERAL-WIDE-LAW-2026-06-06.md`).

### E2: unified candidate `2*min(k+1, n-k-1)` refuted at (31,8,4)

The single closed-form candidate proposed to unify the `j = 2` interior value across regimes is
false.

- False statement: `P[2] = 2*min(k+1, n-k-1)`.
- Witness/refutation: `(31, 8, 4)` admits **7** distinct bad scalars (> 6), triple-verified (fast
  counter + exhaustive enumeration + direct `mcaEvent`); the explicit witness set
  `{4, 9, 10, 13, 21, 24, 29}` was independently re-derived by a second agent. Module
  `scripts/pp_exp_j2_theorem.py` (`J2-VALUE-2026-06-06.md`). The candidate is wrong in *both*
  directions (under at `n - k = 4` / large `k`, over in the wide regime).
- Corrected form: `P[2] = 3` is proven `<=` in the wide regime `n - k >= 5` (3x3-minor root
  counting) and construction-attained; the narrow regime `n - k = 4` is irregular with no closed
  form (`P[2] = (4, 6, 6, 7, 7)` for `k = 1..5` at `q = 31`, exhaustive).

### E3: deep-hole non-extremality in both the window and the band

The natural conjecture that the `X^k` deep hole is the extremal `u1` is false in both the
window-interior and the radius-one band.

- False statement: the deep-hole construction (`u1` = evaluations of `X^k`) attains the extremal
  bad-scalar count.
- Witness/refutation: in the window interior the deep hole **undershoots** the true optimum by
  roughly 2x on exact cases — sparse low-weight overlapping pairs reach the true value and beat the
  deep hole by 15-40% at scale (`(251, 12, 6)`, `j = 4`: `14` vs `12`; `(251, 16, 8)`, `j = 6`:
  `22` vs `17`), from the full-transversal ground truth in
  `scripts/pp_exp_window_breaker.py`. In the radius-one band a general `u1` strictly wins below its
  covering threshold (e.g. `(5, 2)` reaches `10/10` at true `q* = 11`, vs deep-hole `q* = 17`),
  from `scripts/pp_exp_middle_band.py`.
- Corrected form: the extremal `u1` is not the deep hole; the radius-one attainment threshold is a
  covering / hyperplane-avoidance problem (see F11 / the middle-band writeup). The kernel-proven
  *upper* bound `eps_mca(RS, 1) <= C(n, k+1)/q` (`epsMCA_one_le_choose_div`) and its exact-value
  attainment for large `q` (`epsMCA_one_eq_choose_div`) are unaffected — they are statements about
  the maximum over all `(u0, u1)`, which these refutations populate but do not contradict.

## Methodological takeaway

The right response to these defects is not to weaken the final theorem silently. Keep the original
mathematical intent visible, isolate the exact missing bridge as a named residual, and prove the
remaining reductions against that residual.
