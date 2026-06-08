STATUS: ADVANCED — (P2) `βHensel_lift_identity` statement REPAIRED + PROVEN modulo one localized root residual; base case + uniqueness reduction fully proven (axiom-clean). Compile exit 0.

# pc-w10-connect — connecting βHensel (A.1) to the genuine root gammaGenuine

File: `upstream/lean-research/ArkLib/ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean`
Source: `lalalune/main`, upstream ArkLib source-of-truth checkout
Compile: `lake env lean ArkLib/.../HenselNumerator.lean` → exit 0 (only the two expected `sorry`s).

## The problem with the old statement (documented statement repair)

The old `βHensel_lift_identity` equated `embedding(βHensel … t)` with
`ClaimA2.α x₀ R H hHyp t · W^{t+1} · ξ^{2t−1}`. This was **false-as-stated, not merely deep**:
`ClaimA2.α t = embedding(ClaimA2.β R t) / (W^{t+1}·ξ^{2t−1})`, and `ClaimA2.β R t =
(β_regular …).choose` whose witness is the **vacuous `β = 0` stub** (`β_regular := fun _ => ⟨0, by simp⟩`).
So `ClaimA2.α t = 0` for every `t`, while the LHS at `t=0` is `embedding(βHensel … 0) = T ≠ 0`
(`embeddingOf𝒪Into𝕃_βHensel_zero`). The in-tree lemma `βHensel_lift_identity_iff_β_eq` already
showed the old statement was equivalent to `embedding(βHensel … t) = embedding(β R t)` — provably
false at `t=0`.

## Repair (TASK 1) — done, documented in §4f docstring

New genuine coefficient: `αGenuine t := PowerSeries.coeff t (gammaGenuine x₀ R H hHyp)`, the `t`-th
coefficient of the genuine Hensel-lift root `gammaGenuine` of `GammaGenuine.lean`
(`constantCoeff = α₀ = T/W`, `eval gammaGenuine Q = 0`). Repaired statement:
`embedding(βHensel … t) = αGenuine t · W^{t+1} · ξ^{2t−1}`.

Normalization verified against BCIKS20 fulltext lines ~3950–3965 (Claim A.2):
`α_t = β_t/(W^{t+1}·ξ^{e_t})` with `e_t = max(0, 2t−1)` (`e_0=0`, `e_t=2t−1` for `t≥1`). In ℕ-truncated
subtraction `2*t−1` realises `e_t` exactly (`2*0−1=0`), so the clearing powers `W^{t+1}`, `ξ^{2t−1}`
are unchanged from the old statement; only the coefficient is repaired (vacuous `ClaimA2.α` →
genuine `αGenuine`). Import of `GammaGenuine` added (no cycle: GammaGenuine depends only on
HenselSeriesCoeff + RationalFunctions, not HenselNumerator).

## What is PROVEN (axiom-clean: `[propext, Classical.choice, Quot.sound]`, no sorryAx — in-file audited)

- `αGenuine_zero` : `αGenuine 0 = α₀ = T/W`.
- `ζ_ne_zero` : `ζ R x₀ H ≠ 0`, from `IsUnit(eval α₀ (derivative Q₀)) = IsUnit ζ`
  (`isUnit_eval_α₀_derivative_Q₀` + `eval_α₀_derivative_Q₀`, the in-tree simple-root datum).
- `embeddingOf𝒪Into𝕃_ξ_ne_zero` : `embedding ξ = W^{d−2}·ζ ≠ 0`.
- `den_ne_zero` : the A.4 denominator `W^{t+1}·ξ^{2t−1} ≠ 0`.
- `βHenselAssembled` : the assembled numerator series `mk (fun t => embedding(βHensel t)/(W^{t+1}ξ^{e_t}))`.
- `βHenselAssembled_constantCoeff` / `βHensel_lift_identity_zero` (TASK 2, the BASE CASE):
  `constantCoeff(βHenselAssembled) = α₀`, i.e. `embedding(βHensel … 0) = αGenuine 0 · W · ξ^0 = (T/W)·W = T`.
  Fully discharged via `embeddingOf𝒪Into𝕃_βHensel_zero` + `e_0=0` + `div_mul_cancel₀`.
- `βHenselAssembled_eq_gammaGenuine` (TASK 3, the UNIQUENESS REDUCTION): GIVEN the assembled series is
  a root of `Q`, it equals `gammaGenuine` — by `gammaGenuine_unique` fed the PROVEN base case (constant
  coeff = α₀) + the root hypothesis.
- `βHensel_lift_identity_of_assembledSeries_isRoot` : GIVEN the root, the full identity holds for ALL `t`
  (coeff t βHenselAssembled = αGenuine t, then clear `den_ne_zero`).
- `βHensel_lift_identity` : the repaired theorem, **PROVEN** (no sorry on it) by feeding the single
  residual into the reduction. (Its axiom set carries `sorryAx` solely via that one residual.)

## The single residual (THE deep step, carved minimal)

`assembledSeries_isRoot : eval (βHenselAssembled …) Q = 0` — the genuine BCIKS20 A.4 statement that
the (A.1)-assembled series is a root of the X-recentered Y-polynomial `Q`. This is the **only** open
piece of (P2): base case, denominator nonvanishing, uniqueness reduction, and per-`t` clearing are all
proven. The residual is the Faà-di-Bruno bridge: `HenselSeriesCoeff.coeff_eval_eq_sum_range` expands
order-`n` of `eval γ Q` into a sum over Y-degrees and X-partitions of `n`, and
`PowerSeriesComposition.coeff_pow_eq_partitionSum` turns each `γ^j` into the partition sum whose shape
is exactly `B_coeff · partitionProd` (the objects were built to those shapes). It carries NO false
content: `gammaGenuine` genuinely IS a root (`gammaGenuine_root`); the missing piece is only the formal
expansion match for the assembled series.

## Net effect

- Removed one false-as-stated frontier sorry (`βHensel_lift_identity` against vacuous `ClaimA2.α`).
- Added one true, minimal, precisely-localized residual (`assembledSeries_isRoot`, a single root equality).
- Added 8 axiom-clean proven lemmas (base case + uniqueness machinery + nonvanishing).
- P1 sorry `βHensel_succ_term_weight_le` unchanged (separate, gated-on-P2 wall — untouched).
- No external breakage: only consumer is `β_embedding_eq_of_βHensel_lift_identity` (wrapper, signature
  unchanged) used by `ListDecoding/Agreement.lean`, which passes its lift hypothesis locally.

File now ends at 1956 lines; `linter.style.longFile` bumped 1900→2100.
