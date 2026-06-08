# Middle-band resolution: the radius-one bad-scalar extremal count

Resolution writeup for `lalalune/ArkLib` issue #39 — *"Grand MCA: determine the
exact radius-one bad-scalar extremal count in the remaining middle band."*

## 0. Scope and honesty contract

This note resolves, as completely as toy scale allows, the one finite extremal
quantity that the radius-one Grand MCA layer reduces to. Every number is computed
by an exact closed-form functional (no asymptotics, no sampling where labelled
"exact"). The certification regime of each number is kept explicit:

- **exact:exhaustive** — full pair sweep, no search gap;
- **exact:construction** — a witness attaining a *proven* upper bound (so the
  value is exact, not merely a lower bound);
- **searched-only** — a lower bound from random search, flagged as such and never
  treated as exact.

The threshold law below stays a **conjecture except where per-case verified**,
and its one genuine **failure** is established rigorously (exhaustively), not by
search. The Lean port is **queued** (toolchain migration in progress); the port
plan is in §7.

Executable companion (every number here is traceable to a function in it):
`scripts/pp_exp_middle_band.py`, tests in `tests/test_pp_exp_middle_band.py`.
Both build read-only on `scripts/pp_exp_collision_structure.py` (prior wave) and
`scripts/proximity_prize_rs_experiments.py` (base harness). In-tree anchors that
already formalize the surrounding objects (read-only here):
`ArkLib/Data/CodingTheory/ProximityGap/MCABadCount.lean` and `MCASecondMoment.lean`.

## 1. The extremal quantity and the two kernel-proven framing bounds

Fix a Reed–Solomon code `RS[F, L, k]` with `n = |L|` distinct evaluation points
over a prime field `F = F_q`. At radius `δ = 1` the mutual-correlated-agreement
error is *exactly* a normalised bad-scalar count (this is the content of
`MCABadCount.lean`):

> `eps_mca(C, 1) = (sup over word pairs (u₀,u₁) of mcaBadCount C 1 u₀ u₁) / q`,
> where `mcaBadCount C 1 u₀ u₁ = #{ γ ∈ F : mcaEvent C 1 u₀ u₁ γ }`.

Write the extremal count

> **P(n,k,q) := max over (u₀,u₁) of mcaBadCount(RS[F,L,k], 1, u₀, u₁).**

The radius-one characterization (kernel-proven, `GrandChallengeRadiusOne(Exact)`,
recalled in the prior wave) makes `P` computable from a single linear functional.
For a `(k+1)`-subset `T`, the restriction `u|T` is codeword-extendable iff
`c_T(u) = 0`, where `c_T(u)` is the `Xᵏ` coefficient of the Lagrange interpolant
of `u` on `T` (`pp_exp_collision_structure.c_functional`). A scalar `γ` is bad for
`(u₀,u₁)` iff some `T` has `c_T(u₁) ≠ 0` while `c_T(u₀) + γ·c_T(u₁) = 0`; each such
`T` pins the **unique** bad scalar `γ_T = −c_T(u₀)/c_T(u₁)`. Hence

> `mcaBadCount(u₀,u₁) = #{ γ_T : T with c_T(u₁) ≠ 0 }`.

This frames `P` between two **kernel-proven** bounds (both already in tree):

- **(UB) the `(k+1)`-subset cap:** `P(n,k,q) ≤ C(n, k+1)`
  (`epsMCA_one_le_choose_div` ⇒ at most one `γ_T` per `(k+1)`-subset).
- **(CARD) the cardinality cap:** `P(n,k,q) ≤ q` (only `q` scalars exist).
- **(ATTAIN) the union-bound attainment:** `P(n,k,q) = C(n,k+1)` once
  `q > C(C(n,k+1), 2)` (`epsMCA_one_eq_choose_div`, the deep-hole + hyperplane
  union bound).

Together: **`P(n,k,q) ≤ min(C(n,k+1), q)` always**, with equality for large `q`.
The **middle band** `C(n,k+1) ≤ q ≤ C(C(n,k+1), 2)` is the regime (ATTAIN) left
undecided. `MCASecondMoment.lean` narrows the lower side by a second-moment
average but leaves the exact knife-edge count. Issue #39 asks for that count.

Module map: `choose`, `union_bound_threshold`, `exhaustive_extremal_count`,
`construction_extremal_count`, `band_entry`.

## 2. The exact band map (per `(n,k)`, regime-labelled)

`band_map(n,k)` tabulates `q ↦ P(n,k,q)` over the lower (interesting) part of the
band. The structure is identical across cases: the count rises `q → min(C,q)`,
crosses `C(n,k+1)` at the threshold `q*`, and is pinned at `C` thereafter.

### 2.1 Representative full map — `(5,2)`, `C(5,3) = 10`, union bound `45`

| `q` | `P` | `min(C,q)` | regime | certification |
|----:|----:|-----------:|--------|---------------|
| 5  | 5  | 5  | sub-`C` (capped by `q`) | exact:exhaustive |
| 7  | 7  | 7  | sub-`C` (capped by `q`) | exact:exhaustive |
| 11 | 10 | 10 | **tight (`q* = 11`)** | exact:exhaustive |
| 13 | 10 | 10 | tight | exact:exhaustive |
| 17 | 10 | 10 | tight | exact:construction |
| 19 | 10 | 10 | tight | exact:construction |
| 23 | 10 | 10 | tight | exact:construction |
| 29 | 10 | 10 | tight | exact:construction |

Two phenomena, both mapped:

- **Sub-`C(n,k+1)` regime (`q < C`):** the cardinality cap `q` binds and is
  **attained** — `P = q`, i.e. **all `q` scalars can be simultaneously bad**
  (e.g. `(5,2)` at `q ∈ {5,7}`, `(6,3)` at `q = 13`). Verified exhaustively.
  (`test_sub_choose_regime_all_q_scalars_bad`.)
- **Tight regime (`q ≥ q*`):** `P = C(n,k+1)`, pinned. Below the pair-exhaustive
  ceiling this is `exact:exhaustive`; above it, a construction attaining the
  proven cap `C` certifies the value exactly (`exact:construction`).

Module map: `band_map`, `BandEntry`.

## 3. The threshold law `q*(n,k)` and the refutation of the prior conjecture

Define `q*(n,k) :=` least prime with `P(n,k,q) = C(n,k+1)`. The prior wave
(`pp_exp_collision_structure`) conjectured

> **(C0)** `q*(n,k) = smallest prime ≥ C(n,k+1)`

and verified it exhaustively only for `(4,1)` and `(5,2)`. Result of this wave:

| `(n,k)` | `C(n,k+1)` | smallest prime ≥ `C` | `q*` (observed) | **(C0)** holds | `q*` certification |
|---------|-----------:|---------------------:|----------------:|:--------------:|--------------------|
| (4,1) | 6  | 7  | 7  | yes | exact:exhaustive |
| (5,1) | 10 | 11 | 11 | yes | exact:construction |
| (5,2) | 10 | 11 | 11 | yes | exact:exhaustive |
| (6,2) | 20 | 23 | 23 | yes | exact:construction |
| (6,1) | 15 | 17 | 17 | yes | exact:construction |
| **(6,3)** | **15** | **17** | **23** | **NO** | exact:construction |

### 3.1 The conjecture is REFUTED — `(6,3)` (rigorous, exhaustive)

`C(6,4) = 15`; the smallest prime `≥ 15` is `17`. But:

> **`P(6,3,17) = 14`  and  `P(6,3,19) = 14`** — both equal to `C − 1`, established
> by an **unconditional exhaustive sweep over all `q⁶` transversal pairs** (no
> search gap; `q⁶ ≈ 24M` at `q = 17`, `≈ 47M` at `q = 19`).

There is no prime in `(19, 23)`, and a construction attains `15` at `q = 23`, so
`q*(6,3) = 23 ≠ 17`. The conjecture (C0)'s *sufficiency* direction is false.

This is not undersampling: the `14` is exact. Module map:
`exhaustive_refutation(6,3,17)` returns `extremal_count = 14, deficit = 1,
status = "exact:exhaustive"`; the test `test_conjecture_fails_for_6_3_rigorously`
re-runs the full sweep (~30 s, the single heavy test).

### 3.2 `q*` is not a function of `C(n,k+1)` alone

`(6,1)` and `(6,3)` have the **same** `C(n,k+1) = 15`, yet `q*(6,1) = 17` while
`q*(6,3) = 23`. So any law for `q*` must read the geometry of the functional
family, not just its cardinality. (`test_conjecture_holds_for_6_1_same_choose_
different_qstar`.)

### 3.3 The corrected statement (evidence status explicit)

- **PROVEN (cardinality necessity):** `q*(n,k) ≥ smallest prime ≥ C(n,k+1)` —
  you cannot place `C` distinct values in `F_q` with `q < C`. This is the only
  part of (C0) that survives.
- **PER-CASE VERIFIED:** equality holds for `(4,1),(5,1),(5,2),(6,2),(6,1)`.
- **REFUTED:** equality fails for `(6,3)` (`q* = 23 > 17`).
- **OPEN:** no closed form for `q*(n,k)` is established. `q*` is governed by the
  incidence/overlap geometry of the `(k+1)`-subset functionals (see §4), and the
  high-overlap (`k` near `n`) cases can push `q*` strictly above the cardinality
  threshold.

Module map: `threshold_qstar`, `threshold_law_table` (verdict string:
`"REFUTED as a universal law: holds for 5/6 cases…"`).

## 4. The obstruction and the extremal construction

### 4.1 What blocks `(6,3)` at `q ∈ {17,19}`

At the best transversal pair for `(6,3), q = 17`, all 15 `(k+1)`-subsets qualify
(a deep-hole-like configuration) but **exactly one pair of functionals is forced
to collide** — e.g. `T = {0,1,3,4}` and `T' = {1,2,3,5}` both map to the same
`γ`. The deficit `C − P = 1` is unavoidable over the entire pair space (this is
exactly what the exhaustive `P = 14` says). The colliding pairs concentrate on
subsets with large overlap.

Why `(6,3)` and not `(6,1)`, both `C = 15`: the `(k+1) = 4`-subsets of `{0..5}`
pairwise share `2` or `3` of their `4` coordinates (overlap histogram
`{2: 45, 3: 60}`); the high-overlap subsets create near-parallel functionals that
need more field room to separate. The `2`-subsets of `(6,1)` share at most `1`
coordinate (histogram `{0: 45, 1: 60}`) and separate already at `q = 17`. This is
the prior wave's covering/hyperplane picture, now seen to be *case-dependent*:

- deep-hole covering threshold `(6,1)` = `17`  =  `q*(6,1)`;
- deep-hole covering threshold `(6,3)` = `29` (general `u₁` improves it to `23`).

Module map: `obstruction_at`, and the prior wave's `forced_collision_analysis` /
`covering_threshold` (read-only).

### 4.2 Which family is extremal in the band

The prior wave's finding that the `Xᵏ` **deep hole is not optimal** is confirmed
and made part of the band picture:

- Above its own covering threshold the deep hole alone attains `C` (it is the
  cleanest extremal object there).
- **Below** the deep-hole covering threshold but at/above `q*`, the extremal
  family is a **general `u₁`** (so `c_T(u₁)` varies across `T`), which strictly
  beats every monic deep hole. Concretely at `(5,2), q = 13`: the deep hole is
  stuck at `9 = C − 1`, but a general-`u₁` pair attains `10 = C` (witness verified
  to realise 10 distinct bad scalars). Module map:
  `extremal_construction(5,2,13)` → `deep_hole_count = 9`,
  `general_u1_needed = True`, `witness_verified_count = 10`.

So the extremal construction in the band is: *take any `u₁` with all (or enough)
`c_T(u₁) ≠ 0`, then choose `u₀` so the affine values `γ_T = −c_T(u₀)/c_T(u₁)`
avoid every pairwise-collision condition.* Existence of such a `u₀` is exactly the
hyperplane-avoidance/covering condition, which becomes solvable at `q*`.

## 5. Exact band tables — summary across cases

| `(n,k)` | `C(n,k+1)` | union bound `C(C,2)` | sub-`C` behaviour | `q*` | `P` for `q ≥ q*` |
|---------|-----------:|---------------------:|-------------------|-----:|------------------|
| (4,1) | 6  | 15  | `P = q` (`q<6`) | 7  | 6  |
| (5,1) | 10 | 45  | `P = q` (`q<10`) | 11 | 10 |
| (5,2) | 10 | 45  | `P = q` (`q<10`) | 11 | 10 |
| (6,2) | 20 | 190 | `P = q` (`q<20`) | 23 | 20 |
| (6,3) | 15 | 105 | `P = q` (`q<15`) | **23** | 15 |
| (6,1) | 15 | 105 | `P = q` (`q<15`) | 17 | 15 |

Reading: in **every** mapped case the entire band collapses to a two-regime step
— `P = q` while `q < C(n,k+1)`, then `P = C(n,k+1)` from `q*` onward, with a thin
transition window `[smallest prime ≥ C, q*)` where `P = C − (small deficit)`
(nonempty only for `(6,3)`: `q ∈ {17,19}`, `P = 14`). The union bound `C(C,2)`
is shown to be enormously loose: `q*` is one or two primes above `C`, never near
the quadratic threshold.

## 6. What remains genuinely open

1. **A closed form / clean predictor for `q*(n,k)`.** Open. `q*` depends on the
   functional incidence geometry; the cardinality bound `q* ≥ smallest prime ≥ C`
   is the only proven handle, and it is not tight (`(6,3)`).
2. **A proof of the per-case threshold law.** Each `q*` above is verified
   (exhaustively or by construction-against-proven-UB) but not *proven* by a
   general argument. A proof would characterize exactly when the pairwise
   collision hyperplanes/conics fail to cover the free space.
3. **The general high-overlap obstruction.** The `(6,3)` extra collision is the
   smallest instance of a family-overlap phenomenon for `k` near `n`; quantifying
   the deficit `C − P` as a function of the overlap structure is open.

Negative findings, stated plainly: the prior single-formula conjecture (C0) is
**false**; the deep hole is **not** the extremal object throughout the band; and
no toy-scale-validated closed form for `q*` was found.

## 7. Queued Lean-port plan

Lean is currently **blocked by a toolchain migration**; the port is queued, not
attempted here. When unblocked:

- **Target file:** a new `MCAMiddleBand.lean` beside `MCABadCount.lean` and
  `MCASecondMoment.lean` in
  `ArkLib/Data/CodingTheory/ProximityGap/`.
- **Lemma to port first (the only fully proven content):** the cardinality
  necessity
  `mcaBadCount_le_card_field : mcaBadCount C 1 u₀ u₁ ≤ Fintype.card F`,
  giving `P(n,k,q) ≤ q` and hence `q* ≥ smallest prime ≥ C(n,k+1)`. This composes
  with the in-tree `epsMCA_one_le_choose_div` to state the combined bracket
  `mcaBadCount ≤ min(C(n,k+1), q)` as a named theorem `mcaBadCount_le_min`.
- **Statement-defect record (port as a `def`/docstring, not a theorem):** the
  conjecture `q* = smallest prime ≥ C(n,k+1)` is **refuted**; the in-tree note
  should record `(6,3)` as the counterexample (`P(6,3,17) = 14 < 15`), mirroring
  the F-series statement-defect catalogue convention — *do not silently formalize
  the false sufficiency direction*.
- **Decidability bridge (optional, larger):** a `Decidable`/`decide`-style
  reflection of `exhaustive_extremal_count` for fixed small `(n,k,q)` would let
  the `(6,3)` refutation be a machine-checked `by decide`-class fact rather than
  an external Python artifact; this is the natural follow-up once the toolchain is
  back.

## 8. Traceability index (number → module function)

| Claim | Function in `scripts/pp_exp_middle_band.py` | Test |
|-------|---------------------------------------------|------|
| `P ≤ min(C,q)` bracket | `exhaustive_extremal_count`, `choose` | `test_proven_bracket_holds_on_band_spot_checks` |
| sub-`C` regime `P = q` | `exhaustive_extremal_count` | `test_sub_choose_regime_all_q_scalars_bad` |
| band map / regimes | `band_map`, `band_entry`, `BandEntry` | `test_band_map_first_tight_and_status_partition`, `test_band_entry_regime_labels` |
| `q*` extraction + scoring | `threshold_qstar`, `threshold_law_table` | `test_threshold_qstar_extraction_small_cases`, `test_threshold_law_table_verdict` |
| **`(6,3)` refutation (exact)** | `exhaustive_refutation` | `test_conjecture_fails_for_6_3_rigorously`, `test_threshold_qstar_6_3_is_23_not_17` |
| `q*` not a function of `C` | `cs.deep_hole_max_distinct_gammas` (read-only) | `test_conjecture_holds_for_6_1_same_choose_different_qstar` |
| extremal construction / deep hole not optimal | `extremal_construction`, `construction_extremal_count` | `test_extremal_construction_general_u1_needed_below_deep_hole_threshold` |
| obstruction deficit | `obstruction_at` | `test_obstruction_deficit_at_qstar_minus_one` |
| engine ↔ base harness cross-check | `exhaustive_extremal_count` vs `base.radius_one_mca_profile` | `test_engine_matches_base_radius_one_profile` |

All tests run under the repo-root `pytest` in well under 120 s
(`tests/test_pp_exp_middle_band.py`, 14 tests, ≈ 35 s wall).
