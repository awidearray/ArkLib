STATUS: SUCCESS (L4 foundation proven + axiom-clean; 1 staged sorry; converged with concurrent harness)

# PC Wave-3 BUILD — power-series composition-coefficient foundation

File: `/home/shaw/arklib-prize/ArkLib/Data/Polynomial/PowerSeriesComposition.lean`
Worktree: `/home/shaw/arklib-prize` (branch `proximity-prize-l217`).
Compile: `cd /home/shaw/arklib-prize && export PATH=$HOME/.elan/bin:$PATH && lake env lean ArkLib/Data/Polynomial/PowerSeriesComposition.lean` → exit 0 (only one expected `sorry` warning).
Imports: mathlib-only (`RingTheory.PowerSeries.Substitution`, `Combinatorics.Enumerative.Partition.Basic`, `Data.Nat.Choose.Multinomial`, `Algebra.Polynomial.Basic`). No dependence on `RationalFunctions`/`HenselNumerator`/`𝕃`/`R`/`H`.

## Decls PROVEN (all axiom-clean: [propext, Classical.choice, Quot.sound]; no sorryAx, no native/ofReduceBool)

- `valueMultiset s l` (def) — the bag `s.val.map l : Multiset ℕ` of a weak composition's values.
- `valueMultiset_card` — `(valueMultiset s l).card = s.card`.
- `valueMultiset_sum` — `(valueMultiset s l).sum = ∑ i ∈ s, l i`.
- `prod_eq_multiset_value_prod` — `∏ i ∈ s, b (l i) = ((valueMultiset s l).map b).prod` (index-keyed → value-keyed product; the prerequisite for grouping).
- `compositionSum_eq_valueMultisetSum` (**L4 — THE FOUNDATIONAL BRICK**) — the multiplicity-grouping identity:
  `∑_{l ∈ finsuppAntidiag s t} ∏_{i∈s} b (l i) = ∑_{m ∈ image valueMultiset} (#fiber m) • ((m.map b).prod)`.
  Pure CommSemiring combinatorics; proven via `prod_eq_multiset_value_prod` + mathlib `Finset.sum_comp` (fiber-cardinality grouping). This is the multivariate-Faà-di-Bruno core: it regroups mathlib's `coeff_pow` antidiagonal/weak-composition sum by the multiset of part-values; fiber-card = the multinomial weight, `(m.map b).prod = ∏_l (b l)^{count l m} = ∏ β^λ`.
- `compositionSum_example` + two `example`s — NON-VACUITY witness at `s=range 2, t=2, b n=2^n`: both sides equal the nonzero `12`, the grouping genuinely splits into the two distinct value-multisets `{2,0}` (fiber 2 → `2•4=8`) and `{1,1}` (fiber 1 → `1•4=4`). Kernel `decide` (NOT native_decide; confirmed axiom-clean). Rules out an empty-sum / `0=0` gamed lemma.
- `coeff_subst_eq_finset_sum` (**L1**) — packages mathlib `PowerSeries.coeff_subst'` (a `finsum`) as a genuine `Finset.sum` over the support from `coeff_subst_finite'`. Pure repackaging, reusable.
- `coeff_pow_eq_compositionSum` (**L2**) — restatement of `PowerSeries.coeff_pow` (the antidiagonal form the keystone consumes).
- `coeff_pow_eq_valueMultisetSum` (**L5-precursor**) — L2∘L4: `coeff n (φ^k)` directly in multiplicity-grouped form. This is the structural shape the keystone's order-`t` coefficient must reproduce (with `φ=γ`, `k=i` the Y-degree).

## Staged residual (documented `sorry`, NOT faked)

- `fiberCard_eq_countPerms_staged {k t} (m) (hcard hsum)` — `#{l ∈ finsuppAntidiag (range k) t | valueMultiset (range k) l = m} = Multiset.countPerms m`. STATED with `sorry`. This is the load-bearing identity that turns L4's fiber-card weight into the `prefactor`/`Nat.multinomial` of BCIKS20 (A.1). NOT proven here: it needs a `Finset.finsuppAntidiagEquiv : finsuppAntidiag s n ≃ Sym s n` argument + `Multiset.countPerms_filter_ne` zero-part bookkeeping — a self-contained but non-trivial later-wave brick.
- The full in-tree `compositionSum_eq_partitionSum` (landing on `Nat.Partition`/`partitionProd`/`prefactor`/`sigmaLambda` from `HenselNumerator.lean`) is NOT stated as a decl; the gap vs L5 is the zero-part/value-multiset split plus `fiberCard_eq_countPerms_staged`. Current `prefactor` is only the positive-part `countPerms`; the Y-Hasse binomial is supplied separately by Hasse-derivative coefficient extraction. The scout's HasSubst/recentering WALL (γ's coeff peel `coeff_n γ = α_n`) is untouched — that is Wave 4, as the scout flagged.

## Honest scope / what this is NOT

This is ONE BRICK of P2 (the §5 keystone `R(X,γ,Z)=0`), exactly as the scout framed it. Proven: the pure-combinatorics grouping foundation (L4) + power-series wrappers (L1/L2/L5-precursor) that put `coeff_pow` into the (A.1) value-multiset shape. NOT done (later waves, MONTHS-scale): the `countPerms` fiber identity, the `Nat.Partition` reconciliation, the γ-coeff HasSubst wall, the (A.1)-recursion vanishing (the actual P2), and threading back into (P1).

## Contention note (no git mutation by me)

A concurrent harness committed a byte-identical version of this exact file at HEAD (commits `276f0f3d6`/`a27fabc39`/`9d9b29968`) — benign convergence on the same foundation, per the converge-don't-edit-war stance. I ran only read-only git (status/show/diff/log); no commit/add/push/checkout/merge. Working tree == HEAD for this file. Temp axiom-audit file created and removed; in-file `#print axioms` run then removed, leaving only a recorded audit note in the source.
