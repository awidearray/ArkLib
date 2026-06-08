# PC Wave-3 SCOUT — coeff_subst → order-by-order vanishing of R(X,γ,Z)

Read-only map. NO file built yet. Source: BCIKS20 App A.4
(`research/proximity-prize/artifacts/2020-654-fulltext.txt`). All line refs against
worktree `/home/shaw/arklib-prize` (branch `proximity-prize-l217`).

## 0. What P2 is and where the bricks sit

P2 (the §5 keystone) = `R(X, γ(X), Z) = 0` as a power series in `(X − x₀)`, where
`γ = Σ_t α^t (X − x₀)^t`. In-tree this is the documented `sorry`
`βHensel_lift_identity` (HenselNumerator.lean:1502, the (P1) gate at ~1492-1502, and
the §4e frontier ~1541). The whole edifice (P1 weight bound) is gated on the
"structured IH", which is gated on P2 (HenselNumerator.lean:76, 1245-1246).

Already-built bricks (HenselNumerator.lean, all axiom-clean) that the order-t coeff
must reproduce:
- `mvHasseCoeff k p` (:155) — multivariate Hasse coeff, the `Δ_X^{i1} Δ_Y^{m}` engine.
- `hasseDerivX`/`hasseDerivY` (:432,:437) — iterated Hasse derivs of `R : F[X][X][Y]`.
- `partitionProd lam b = ∏_l (b l)^{λ_l}` (:341) with `partitionProd_eq_prod_count`
  (:347), `_indiscrete` (:371), `_mul` (:377).
- `sigmaLambda lam = lam.parts.card = Σλ` (:326).
- `prefactor i i1 lam = lam.parts.countPerms` (`prefactor_eq_countPerms`); the explicit scalar is
  the positive-part multinomial/countPerms only. Hasse binomials are emitted by the Hasse
  derivative coefficient lemmas, not stored in `prefactor`.
- `B_coeff i1 lam = prefactor • hasseCoeffRepr𝒪` (:549) — the genuine `B_{i1,λ} ∈ 𝒪 H`.
- `βHensel` (:1103) is itself the (A.1) recursion whose RHS already IS a
  `Σ_{i1} Σ_{λ, (k+1)∉λ.parts} W^{…} ξ^{…} B_coeff · partitionProd lam β`. So the
  TARGET algebraic shape (partition sum of `B·∏β^λ`) is already the in-tree object.

## 1. EXACT statement of `coeff_subst` (TASK 1)

Univariate, the form we use (`PowerSeries.coeff_subst'`, Substitution.lean:232):

    coeff e (PowerSeries.subst b f)
      = finsum (fun d : ℕ => coeff d f • PowerSeries.coeff e (b ^ d))

i.e. `coeff_e(subst b f) = Σ_d (coeff_d f) · coeff_e(b^d)` as a `finsum` over `d : ℕ`.
General target form (Substitution.lean:222, `MvPowerSeries.coeff` indexed by `e : τ →₀ ℕ`):

    MvPowerSeries.coeff e (subst a f)
      = finsum (fun d : ℕ => coeff d f • MvPowerSeries.coeff e (a ^ d)).

Finiteness of the finsum support: `coeff_subst_finite` / `coeff_subst_finite'`
(Substitution.lean:207,218) — so `finsum` = a genuine finite `Finset.sum` once we
exhibit the support. Substitution legality is `PowerSeries.HasSubst b`, which (via
`MvPowerSeries.HasSubst`, :77) needs `IsNilpotent (constantCoeff b)` + cofinite
support. For our `γ` shift `b = mk (t ↦ -x₀,1,0,0,…)` the constant coeff is `-x₀`
which is NOT nilpotent in a field — see WALL note in §4.

The `b^d` coefficient itself is mathlib `PowerSeries.coeff_pow` (Basic.lean:629):

    coeff n (φ^k) = Σ_{l ∈ finsuppAntidiag (range k) n} ∏_{i ∈ range k} coeff (l i) φ

and the `Finset`-product generalization `coeff_prod` (Basic.lean:607). This is the
COMBINATORIAL HEART: `coeff_t(γ^d)` becomes a sum over weak-compositions
`l : range d →₀ ℕ` with `Σ l_i = t` of `∏_i (coeff of γ at l_i)`.

## 2. The composition → partition bridge (TASK 2 — multivariate Faà di Bruno)

`R(X,·,Z)` is a polynomial in the middle variable `Y` (the `F[X][X][Y]` middle layer).
"Evaluate R at the power series γ" = `Polynomial.aeval`/`eval₂` of that Y-polynomial at
`γ ∈ (𝕃)⟦X−x₀⟧`. Because `subst`/`aeval` is an `AlgHom`, `subst_pow`/`subst_mul`/
`subst_add` (Substitution.lean:194,198,186) push the coeff through the polynomial
structure of R term by term. So coeff_t reduces to, per Y-monomial `Y^i` of R:

    coeff_t( (coeff_i R as a series) · γ^i )  →  uses coeff_pow on γ^i.

Then the chain is:

(a) `coeff_pow`/`coeff_prod` ⇒ `coeff_t(γ^i) = Σ_{compositions l, Σl=t} ∏ coeff_{l_j}(γ)`.
(b) γ's own coeffs: `coeff_{l_j}(γ) = α^{l_j}` (the α-family) UP TO the inner `subst`
    by the `(X−x₀)`-shift — note γ is itself a `subst` (RationalFunctions.lean:3049),
    so `coeff_{l_j}(γ)` first needs `coeff_subst'` again to peel the shift; with the
    shift being `t↦(-x₀,1,0,…)` the cleanest route is to prove a γ-coeff lemma
    `coeff_n γ = (something explicit in α)` once and reuse.
(c) GROUP compositions by multiplicity → partitions: a composition `l : range i →₀ ℕ`
    with `Σ l = t` collapses, after grouping equal parts, to a `Nat.Partition` of `t`
    with multiplicities `λ_l`; the number of compositions mapping to a given partition
    is exactly the `multinomial`. The product `∏_j α^{l_j}` becomes `∏_l (α_l)^{λ_l} =
    partitionProd lam α`, and the multinomial count is `prefactor`'s `multinomial`
    factor. The `C(j,Σλ)` binomial is supplied separately by `hasseDerivY_coeff` after the
    zero-peeling reindex (`countPerms_replicate_zero_add_choose_sl`). NET: order-t coeff of
    R(X,γ,Z) =
    `Σ_{i1} Σ_{λ ⊢ (t-i1)} prefactor · (Hasse coeff of R) · partitionProd lam α`
    = the `Σ B_{i1,λ} · ∏ α^{λ_l}` structure of (A.1). The (A.1) recursion defining
    α (RationalFunctions.lean:3029-3033 / βHensel:1103) is precisely the choice making
    every order-t coeff (t≥1) vanish — that is P2.

The single missing MATH OBJECT in mathlib: there is NO `Nat.Partition ↔ finsuppAntidiag`
(composition) reindexing lemma (`grep` for `Partition.*antidiagonal` in
`Combinatorics/Enumerative/*` returns NOTHING; `Bell.lean` exists but is set-partition
Stirling-number flavor, not integer-composition→integer-partition multinomial grouping).
This grouping lemma — "sum over weak compositions = sum over partitions weighted by
multinomial(multiplicities)" — IS the multivariate Faà di Bruno combinatorial core and
must be built. It is the load-bearing bridge between mathlib's `coeff_pow` finsuppAntidiag
sum and the in-tree `partitionProd`/`prefactor`/`sigmaLambda` triple.

## 3. The precise reusable-lemma sequence to build in ONE fresh file (TASK 3)

Direct from mathlib (thin wrappers, no new math — confidence high, compile-cheap):
  L1. `coeff_subst_as_finsum`: restate `coeff_subst'` specialized to our ring `𝕃 H` and
      package the finite support as a `Finset.sum` (uses `coeff_subst_finite'`).
  L2. `coeff_pow_as_antidiag`: alias of `PowerSeries.coeff_pow` (Basic.lean:629) at `𝕃 H`.
  L3. `coeff_subst_poly`: a Y-polynomial `aeval`'d at a power series has coeff_t equal to
      `Σ_i (coeff i R) · coeff_t(g^i)` — assembled from `subst_add/_mul/_pow/_coe`
      (Substitution.lean:186-300) i.e. AlgHom term-by-term. Direct, no new math.

Needs the new partition bridge (the genuine reusable math — the wave-3 deliverable):
  L4 (**FOUNDATIONAL**). `compositionSum_eq_partitionSum`:
      `Σ_{l ∈ finsuppAntidiag (range k) t} ∏_j (b (l j))
        = Σ_{λ ⊢ t, parts.card = k... } multinomial(λ) · partitionProd lam b`
      — the grouping-by-multiplicity identity. Pure combinatorics over a comm-monoid `b`,
      independent of 𝕃/R/H. This is what makes the `coeff_pow` antidiagonal sum land on
      `partitionProd`+`prefactor`. EVERYTHING downstream reuses it.
  L5. `coeff_t_gammaPow_eq_partitionProd_alpha`: combine L2+L4 (+ a γ-coeff peel lemma
      `coeff_n_gamma`) to get `coeff_t(γ^i) = Σ_{λ} multinomial · partitionProd lam α`.
  L6. `coeff_t_R_at_gamma_eq_Bsum`: combine L3+L5+the in-tree `B_coeff`/`prefactor` to
      land EXACTLY on the `Σ_{i1,λ} B_{i1,λ}·∏α^{λ_l}` shape — i.e. the order-t coeff of
      R(X,γ,Z) in the (A.1) sum form. (No vanishing yet — just the structural identity.)
  [Future, NOT wave 3] L7. order-t coeff = 0 via the (A.1) defn of α (this IS P2).

## 4. HONEST verdict — waves, walls, first brick (TASK 4)

WALL (must be surfaced honestly, do not paper over): `PowerSeries.HasSubst b` for the
γ-shift `b = mk(t↦ -x₀, 1, 0,…)` requires `IsNilpotent (constantCoeff b) = IsNilpotent(-x₀)`,
which FAILS over a field for `x₀ ≠ 0`. The in-tree `γ` (RationalFunctions.lean:3049)
uses `PowerSeries.subst` regardless; whether its `coeff` is governed by `coeff_subst`
(which needs `HasSubst`) is the FIRST thing wave-3's file must pin down. Two honest
options: (i) work formally in the `(X−x₀)`-adic completion where the shift is a genuine
substitution after recentering `X' = X − x₀` (constant coeff 0, nilpotent-trivially), or
(ii) prove the γ-coeff lemma directly from the in-tree `subst`/`mk` definition without
routing through `HasSubst`. This is a real research decision, not a stub; flag it as the
wave-3 OPENING question. The β/(A.1) side does NOT have this problem (it lives in `𝒪 H`,
not a power-series substitution), which is why the in-tree keystone was built there.

NEW INFRASTRUCTURE to reach R(X,γ,Z)=0: at least 3 more waves beyond this foundation:
  - Wave 3 (THIS one): L1-L6 — composition-coefficient lemmas + the partition bridge L4.
    The structural identity "coeff_t(R(X,γ,Z)) = (A.1)-shaped partition sum". ~1 file.
  - Wave 4: resolve the HasSubst/recentering wall (the formal home of γ) and prove the
    γ-coeff peel `coeff_n γ = α_n` rigorously. This may itself be a multi-file sub-project.
  - Wave 5: identify the (A.1) recursion as the unique annihilator — i.e. that the α-defn
    forces each order-t (t≥1) partition sum to telescope to 0. This is the genuine P2.
  - Wave 6: thread the resulting `Λ(α_t)=1`/structured-IH back into (P1)
    (`βHensel_succ_term_weight_le`, HenselNumerator.lean ~1492-1502).
  Realistically MONTHS-scale, consistent with the task framing; wave 3 is ONE brick.

SINGLE MOST FOUNDATIONAL LEMMA TO BUILD FIRST (L4):
  `compositionSum_eq_partitionSum` — the multiplicity-grouping identity turning mathlib's
  `coeff_pow` `finsuppAntidiag (range k) t` weak-composition sum into the in-tree
  `partitionProd`+`multinomial` partition sum. It is pure comm-monoid combinatorics
  (testable on `ℕ`/a free monoid, zero dependence on 𝕃/R/H so it compiles fast and
  cannot be vacuous), and it is the ONLY piece with no mathlib precedent. Build and
  axiom-audit it standalone before touching γ.

## Compile/honesty constraints honored
New file only; `lake env lean <newfile>`; no `lake build`; no git; in-file `#print axioms`
then remove; no `sorry`/`admit`/`native_decide`/`bv_decide`. L4 must be proven non-vacuously
(exhibit a concrete `k,t` instance where both sides are a nonzero explicit value) to avoid a
gamed/empty-sum lemma.
