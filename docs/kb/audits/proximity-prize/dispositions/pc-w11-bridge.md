STATUS: PARTIAL — `assembledSeries_isRoot` is now sorry-free (proven by `PowerSeries.ext` from a PROVEN order-0 base + one carved per-successor-order residual); the irreducible Faà-di-Bruno frontier is sharpened to the single minimal lemma `coeff_succ_eval_βHenselAssembled` (documented `sorry`). Strategy: per-order carving (order-0 closed; alternative `=gammaGenuine` strategy shown equivalent to the same residual, no shorter).

# PC-W11 — the (A.1)-assembled numerator series is a root of `Q`

File: `upstream/lean-research/ArkLib/ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean`
(worktree `/home/shaw/ethereumroadmap/upstream/lean-research/ArkLib`; content materialized from /
matching `lalalune/main`). Edited ONLY that file for the PC-W11 bridge pass. Compiled it alone with
`lake env lean ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean` → **exit 0**.
Axiom-audited in-file (`#print axioms`, then removed). Later upstream validation rebuilt the
aggregate import with `lake build ArkLib` successfully.

## What changed

The previous state was a SINGLE opaque residual:
```
theorem assembledSeries_isRoot … : Polynomial.eval (βHenselAssembled …) (Q …) = 0 := by sorry
```
That single `sorry` hid BOTH the (provable) order-0 root content AND the (deep) order-≥1
Faà-di-Bruno content behind one statement. It is now decomposed into three declarations:

1. `coeff_zero_eval_βHenselAssembled` — **PROVEN, axiom-clean**
   `[propext, Classical.choice, Quot.sound]` (verified by in-file `#print axioms`, no `sorryAx`):
   ```
   coeff 0 (eval (βHenselAssembled …) Q) = 0
   ```
   Proof: `coeff 0 (eval γ Q) = eval (constantCoeff γ) Q₀` (`HenselSeriesCoeff.constantCoeff_eval`)
   ⟶ `constantCoeff (βHenselAssembled …) = α₀` (`βHenselAssembled_constantCoeff`)
   ⟶ `eval α₀ Q₀ = 0` (`GammaGenuine.eval_α₀_Q₀_eq_zero`, from `H ∣ evalX (C x₀) R` and `H(α₀)=0`).
   This is the genuine order-0 root vanishing, discharged unconditionally.

2. `coeff_succ_eval_βHenselAssembled` — **the carved residual (documented `sorry`)**:
   ```
   coeff (t+1) (eval (βHenselAssembled …) Q) = 0
   ```
   The single irreducible per-successor-order Faà-di-Bruno content.

3. `assembledSeries_isRoot` — **now sorry-free** (its own body uses no `sorry`):
   ```
   eval (βHenselAssembled …) Q = 0
   ```
   by `PowerSeries.ext`, `rcases t`: order-0 ⟵ (1), order-(t+1) ⟵ (2).
   (Its transitive axiom set is `[propext, sorryAx, Classical.choice, Quot.sound]` only because of
   the carved residual (2); the assembly + base case carry NO `sorryAx` of their own.)

The header item-9 doc-comment and the `βHensel_lift_identity` PROOF-STATUS note were updated to
point at `coeff_succ_eval_βHenselAssembled` as the single residual.

## Net `sorry` ledger for the file (unchanged count, sharper content)

- line ~1548 `βHensel_succ_term_weight_le` — the pre-existing **(P1)** per-term WALL (NOT this
  task; gated on the structured `α_t`-weight invariant which is itself gated on (P2), per wave 5).
- line ~1933 `coeff_succ_eval_βHenselAssembled` — **this task's** carved residual.

`assembledSeries_isRoot` itself moved from sorry-bearing to sorry-free. Two file-level `sorry`
warnings remain (same count as before), but the (P2) root residual is now the minimal per-order
lemma rather than the whole-series statement, and the order-0 half is genuinely closed.

## Why the residual cannot be closed honestly in this session

Closing `coeff_succ_eval_βHenselAssembled` is the genuine BCIKS20 A.4 Faà-di-Bruno / multivariate
chain-rule expansion for the *normalized* assembled series:
`coeff_eval_eq_sum_range` (convolution) ↦ `coeff_pow_eq_partitionSum` (per-`γ^j` partition sums)
↦ match against `B_coeff · partitionProd` with the `W`/`ξ` clearing powers telescoping. The
partition-sum machinery (`PowerSeriesComposition.lean`) IS fully sorry-free, and the local
zero-peel/Y-Hasse weight identity is now proven in `P2Vanish.lean`. The final match is gated on
the term-level residual `RestrictedFaaDiBrunoMatch`: aligning the restricted Faà-di-Bruno index set
with the `(A.1)` `B_coeff · partitionProd` sum, including `ζ` sign and denominator clearing. That
reconciliation is substantial and cannot be faked.

## Alternative strategy evaluated (`βHenselAssembled = gammaGenuine` first), and why it is NOT shorter

The brief's ALTERNATIVE: prove `βHenselAssembled = gammaGenuine` directly (non-circular), then
`assembledSeries_isRoot` ⟵ `gammaGenuine_root` by rewrite. I evaluated this against the actual
Newton machinery (`HenselSeriesCoeff.coeff_eval_sub_at`, `root_unique_seriesCoeff`, `S`/`γ`):

- `βHenselAssembled = gammaGenuine` reduces (by `PowerSeries.ext` + strong induction) to a
  per-coefficient match `coeff (t+1) βHenselAssembled = coeff (t+1) gammaGenuine`.
- The Newton linearization gives, with the proven unit `A = eval α₀ (derivative Q₀) = ζ ≠ 0`
  (`isUnit_eval_α₀_derivative_Q₀`) and inductive agreement below `t+1`:
  `coeff(t+1)(eval βHA Q) − coeff(t+1)(eval γG Q) = A·(coeff(t+1) βHA − coeff(t+1) γG)`,
  and `coeff(t+1)(eval γG Q) = 0` (`gammaGenuine_root`). So **the coefficient match at `t+1` is
  equivalent to `coeff(t+1)(eval βHA Q) = 0`** — i.e. to the very residual carved here.

Conclusion: both strategies bottom out at the SAME per-order content (the (A.1) recursion ↔ Newton
correction match). The `=gammaGenuine` route adds extra induction plumbing but does not reduce the
mathematical residual, and risks looking circular (it must NOT route through `assembledSeries_isRoot`,
whereas the existing `βHenselAssembled_eq_gammaGenuine` deliberately takes `hroot` as a hypothesis).
The per-order eval-vanishing carving chosen here is the cleaner, smaller, self-contained core. This
equivalence is documented inside the residual's doc-comment so the next attempt can pick either frame.

## Verification

- `cd /home/shaw/ethereumroadmap/upstream/lean-research/ArkLib && lake env lean ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean` → exit 0.
- `cd /home/shaw/ethereumroadmap/upstream/lean-research/ArkLib && lake build ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.CurvesBridge && lake env lean ArkLib.lean` → exit 0.
- `cd /home/shaw/ethereumroadmap/upstream/lean-research/ArkLib && lake build ArkLib` → exit 0.
- In-file `#print axioms` (temp, removed):
  - `coeff_zero_eval_βHenselAssembled` → `[propext, Classical.choice, Quot.sound]` (clean).
  - `assembledSeries_isRoot` → `[propext, sorryAx, Classical.choice, Quot.sound]` (`sorryAx`
    enters only via the carved residual `coeff_succ_eval_βHenselAssembled`).
- No `native_decide` / `bv_decide` / `admit` / `axiom` introduced.

## Decls touched
- `coeff_zero_eval_βHenselAssembled` (NEW, proven, axiom-clean)
- `coeff_succ_eval_βHenselAssembled` (NEW, the carved `sorry` residual)
- `assembledSeries_isRoot` (REWRITTEN, now sorry-free body; transitively `sorryAx` via the residual)
- doc-comments: header item 9; `βHensel_lift_identity` PROOF STATUS note.
