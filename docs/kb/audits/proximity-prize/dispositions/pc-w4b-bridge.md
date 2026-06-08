STATUS: CLOSED (fiber-card sorry proven; full partition regrouping landed; file fully sorry-free; axiom-clean)

# PC-W4b — fiberCard_eq_countPerms + compositionSum_eq_partitionSum

File: `upstream/lean-research/ArkLib/ArkLib/Data/Polynomial/PowerSeriesComposition.lean`
(`lalalune/main` at ArkLib commit `0e76930a`).

## What was closed

1. The staged `sorry` at the former line ~189 (`fiberCard_eq_countPerms_staged`) is **proven**.
2. The full regrouping promised by the staged residual is now **stated and proven**:
   `compositionSum_eq_partitionSum`, plus its `coeff_pow` corollary `coeff_pow_eq_partitionSum`.

The whole file compiles `lake env lean` exit 0 and is now fully `sorry`-free.

## The exact identity (worked out, not the paper's cosmetic form)

`valueMultiset (range k) l = (range k).val.map (l ·)` is the multiset of the `k` slot-VALUES of a
weak composition, **including zero values** (one entry per index `i ∈ range k`, even where `l i = 0`).
So the fiber `#{l ∈ finsuppAntidiag (range k) t | valueMultiset (range k) l = m}` is the number of
ordered `k`-tuples of naturals whose value-bag is `m` — i.e. the number of distinct ARRANGEMENTS of
the bag `m` (card `k`, sum `t`) over `k` ordered slots. That is exactly `Multiset.countPerms m`
(= `Nat.multinomial m.toFinset (count · m)` = `k! / ∏ (mult)!`, with the zero-value slots already
folded into one of `m`'s multiplicities). No separate `Nat.choose i i₁` zero-part split is needed:
the zeros are honest entries of `m`, counted by `count 0 m`.

NOTE on the original WALL plan: the staged comment proposed routing through
`Finset.finsuppAntidiagEquiv : finsuppAntidiag s n ≃ Sym s n`. That equiv is the WRONG handle — its
`Sym` is the multiset of INDICES (each index `a` appearing `l a` times), not the value-multiset. It
does not connect to `valueMultiset`. The actual proof avoids it entirely.

## Proof architecture (all in a new `FiberCard` section)

countPerms side (pure Multiset combinatorics):
- `countPerms_eq_multinomial` / `countPerms_erase_eq_multinomial` — `countPerms m` and
  `countPerms (m.erase v)` as `Nat.multinomial` over the COMMON finset `m.toFinset`
  (`Finsupp.multinomial_of_support_subset` + `Nat.multinomial_congr_of_sdiff`).
- `count_mul_countPerms` (★): `count v m * countPerms m = card m * countPerms (m.erase v)`, by
  clearing both `Nat.multinomial_spec` denominators over `m.toFinset` (they differ at `v` by one
  factorial step: `Finset.mul_prod_erase`, `Nat.mul_factorial_pred`, `Nat.factorial_succ`).
- `countPerms_eq_sum_erase`: for `m ≠ 0`, `countPerms m = ∑_{v∈m.toFinset} countPerms (m.erase v)`,
  by summing (★) and cancelling `card m > 0`.

fiber side:
- `fiberCard_eq_countPerms_gen` (over an ARBITRARY index finset `s`, target `m.sum`), by
  `Finset.induction` on `s`. Empty ⇒ `m = 0`, `countPerms 0 = 1`. `insert a s`: partition the fiber
  by the value `l a = v` (`Finset.card_eq_sum_card_fiberwise` into `m.toFinset`); each block bijects
  (`Finset.card_bij'` via `Finsupp.erase a` ⇄ `Finsupp.update · a v`) with the `m.erase v` fiber over
  `s`, matched against `countPerms_eq_sum_erase` term-by-term. Index-peel recursion
  `valueMultiset (insert a s) l = (l a) ::ₘ valueMultiset s l` (`valueMultiset_insert`).
- `fiberCard_eq_countPerms {k t} (m) (hcard hsum)` — specialization to `s = range k`
  (`Finset.card_range`). This is the originally-staged statement.
- `fiberCard_eq_countPerms_staged` retained as a proven compatibility alias (same statement).

regrouping:
- `compositionSum_eq_partitionSum (s t b)`: feeds the fiber identity into the existing (axiom-clean)
  `compositionSum_eq_valueMultisetSum` (L4), replacing the opaque fiber weight `#{…}` by
  `countPerms m`. `∑_l ∏ b(l i) = ∑_{m∈image} countPerms m • (m.map b).prod`.
- `coeff_pow_eq_partitionSum (k n φ)`: the `coeff_pow` corollary (`b j := coeff j φ`).

## Declarations added (all axiom-audited in-file)

valueMultiset_insert, valueMultiset_erase_notMem, countPerms_eq_multinomial,
countPerms_erase_eq_multinomial, sum_count_self, sum_count_erase, count_mul_countPerms,
countPerms_eq_sum_erase, fiberCard_eq_countPerms_gen, fiberCard_eq_countPerms,
fiberCard_eq_countPerms_staged (alias), compositionSum_eq_partitionSum, coeff_pow_eq_partitionSum.

In-file `#print axioms` (on a copy, removed after) for every new decl plus the existing ones:
`[propext, Classical.choice, Quot.sound]` only — NO `sorryAx`, NO `Lean.ofReduceBool`/native_decide,
NO admit/axiom. `valueMultiset_insert` even narrower (`[propext, Quot.sound]`).

## Residual

None for this file. Downstream (NOT in scope here): the keystone in `HenselNumerator.lean` still
needs the `Nat.Partition` zero-part split and the `γ`-coefficient HasSubst/recentering peel
(`coeff_n γ = α_n`) — the scout's Wave-4 WALL, untouched here. `compositionSum_eq_partitionSum`
lands on `countPerms`/`Nat.multinomial`, which is the multiplicity weight consumed by the current
positive-part `prefactor`; the Y-Hasse binomial is a separate coefficient-extraction factor.
