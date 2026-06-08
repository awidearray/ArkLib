STATUS: PROVEN (3 target decls + 1 helper, axiom-clean, compile exit 0)

# pc-w6-newton — Newton-step linearization for power-series powers (BCIKS20 App. A.4 / P2 path)

File: `ArkLib/Data/Polynomial/NewtonLinearization.lean`
Worktree: `/home/shaw/arklib-prize` (branch `proximity-prize-l217`). Imports: mathlib only
(`PowerSeries.Basic`, `Polynomial.Derivative`, `Polynomial.Eval.Degree`).
Compile: `lake env lean ArkLib/Data/Polynomial/NewtonLinearization.lean` → exit 0.

## What was proven (all kernel-checked, no sorry)

Setting: `[CommRing R]`, `γ₁ γ₂ : R⟦X⟧` agreeing below order `t` (`∀ j < t, coeff j γ₁ = coeff j γ₂`,
which includes `j = 0`, so `constantCoeff γ₁ = constantCoeff γ₂`).

1. **LEMMA A — `coeff_pow_sub_below`** (truncation propagation)
   `∀ i, ∀ j < t, coeff j (γ₁^i) = coeff j (γ₂^i)`.
   Induction on `i`; `coeff_mul` antidiagonal pairs `(a,b)` have `a+b=j<t` ⇒ `a,b<t` ⇒ both
   factors agree (hyp / IH).

2. **LEMMA B — `coeff_pow_sub_at`** (order-`t` linearization), `0 < t`, `c := constantCoeff γ₁`:
   `coeff t (γ₁^(i+1)) − coeff t (γ₂^(i+1)) = (i+1) • (c^i * (coeff t γ₁ − coeff t γ₂))`.
   Stated in the subtraction-free `(i+1)` shape to dodge the `i−1`-in-ℕ pitfall.
   Induction on `i`; expand `γ^(i+1)=γ^i·γ` via `coeff_mul` over `Finset.antidiagonal t`,
   split the end terms `(t,0)`/`(0,t)` with `Finset.sum_eq_add_of_mem`; every interior pair
   has `a<t ∧ b<t` ⇒ cancels (LEMMA A + hyp). End-terms `(t,0): (Δpow)·c` (rewritten by IH) and
   `(0,t): c^{i+1}·δ`; closed by `nsmul_eq_mul` + `ring`.

3. **`coeff_aeval_eq_sum_range`** (helper, local restatement of
   `GammaSubstObstruction.coeff_aeval_powerSeries` — restated to keep mathlib-only imports):
   `coeff n (aeval γ P) = ∑_{i ≤ natDegree P} P.coeff i * coeff n (γ^i)`.

4. **COROLLARY — `coeff_aeval_sub_at`** (the P2-facing `P′(c)`-linear form), `0 < t`:
   `coeff t (aeval γ₁ P) − coeff t (aeval γ₂ P) = eval c (derivative P) * (coeff t γ₁ − coeff t γ₂)`.
   Expand both via the helper, subtract termwise; the `i`-th term is
   `P.coeff i · i · c^{i−1} · δ` (LEMMA B; `i=0` term vanishes since `coeff t 1 = 0` for `t>0`).
   Pull out `δ` (`Finset.sum_mul`); the residual sum `∑ P.coeff i · i · c^{i−1}` is
   `eval c (derivative P)` via `Polynomial.derivative_eval` + `Polynomial.sum_over_range'`.

## Axiom audit (in-file `#print axioms`, run on temp copy then removed)

All four decls depend only on `[propext, Classical.choice, Quot.sound]`.
No `sorryAx`, no `native_decide`/`Lean.ofReduceBool`. Forbidden-tactic scan: clean
(only the audit comment mentions the words).

## Residual / next step on the P2 chain

- The corollary is the genuine Newton/Hensel linearization driving the order-by-order
  `R(X,γ,Z)=0` induction: order-`t` coefficient of the composed series is `P′(c)`-linear in the
  order-`t` input. Combined with the in-tree base fact `R(x₀,α₀)=0` and
  `constantCoeff_aeval_powerSeries` (GammaSubstObstruction), the inductive step now has its
  linear-response engine.
- NOT yet done here (downstream): (i) the actual order-by-order vanishing recursion that
  *uses* this linearization to solve for `coeff t γ` order by order (needs `P′(c)` invertible,
  i.e. the Hensel `simple-root` hypothesis); (ii) the `X`-recentering / Taylor-shift bridge
  (already available as `aeval_taylor_powerSeries` in GammaSubstObstruction); (iii) tying `γ`
  to the genuine recursive Hensel data (the `β`/`α`/`γ` re-anchoring obstruction recorded in
  GammaSubstObstruction and the w2/w3 scouts). These remain owner-hot / later-wave.

## Note on concurrent convergence

The shared harness at one point reduced the file to LEMMA A only (and renamed the
antidiagonal-membership lemma to the correct `Finset.mem_antidiagonal`). LEMMA B + COROLLARY
were re-added on top of that converged base; final on-disk file carries all four decls and
compiles exit 0.
