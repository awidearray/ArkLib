STATUS: P2 NOT fully closed — disposition (b): target `faaDiBruno_succ_sum_eq_zero` PROVEN (no sorry), reduced to ONE smaller named residual `trunc_defect_cancel_assembled`; one genuinely-new connective lemma `trunc_defect_eq_faaDiBruno_assembled_restricted` PROVEN axiom-clean.

# pc-w14 — last P2 lemma: `faaDiBruno_succ_sum_eq_zero`

File: `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean`
Worktree: `/home/shaw/arklib-prize` (HEAD detached @ lalalune/proximity-prize-l217; harness HARD-RESETS — see wipe note below)
Compile: `cd /home/shaw/arklib-prize && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>` → **EXIT 0**

## Outcome summary

- TARGET `faaDiBruno_succ_sum_eq_zero` is now **PROVEN (no bare `sorry`)** — it follows from the
  PROVEN content-free expansion `coeff_eval_Q_faaDiBruno` (run backwards) + the PROVEN Newton
  defect reduction `coeff_succ_eval_of_trunc_defect_cancel`, applied to ONE smaller named residual.
- The genuine open content of (P2) is RE-CARVED into the strictly-smaller, more honest residual
  `trunc_defect_cancel_assembled` (the cleared truncated-defect cancellation — the actual identity
  the `(A.1)` recursion `βHensel_succ` was DEFINED to satisfy). This is the only new bare `sorry`.
- A genuinely-new connective lemma `trunc_defect_eq_faaDiBruno_assembled_restricted` was PROVEN
  **axiom-clean** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**):
  the truncated defect equals the surviving-partition (`(t+1) ∉ m`) restriction of the assembled
  Faà-di-Bruno sum. This formalizes the truncation→survival-guard step of BCIKS20 A.4.

## Bare-sorry count in file: 2
- line 1589 `βHensel_succ_term_weight_le` — the **P1** residual (gated on the structured IH; NOT this task's target; documented honest WALL, unchanged).
- line 2425 `trunc_defect_cancel_assembled` — the carved **P2** residual (this task; smaller than the original `faaDiBruno_succ_sum_eq_zero` sorry).

NOTE re task's "should be 1": that target presumed a FULL P2 close. P2 is NOT fully closed. The
2026-06-06 correction is that current `prefactor` is already normalized to the positive-part
`countPerms`, so the frontier is not a separate `prefactor_eq_paper` definition. The irreducible
frontier is the term-level `RestrictedFaaDiBrunoMatch` equality of sums, with the local
zero-peel/Y-Hasse weight identity already proven.

## End-to-end audit (run in-file via `#print axioms`, then prints removed — verbatim)
```
'BCIKS20.HenselNumerator.βHensel_lift_identity' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'BCIKS20.HenselNumerator.faaDiBruno_succ_sum_eq_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'BCIKS20.HenselNumerator.trunc_defect_eq_faaDiBruno_assembled_restricted' depends on axioms: [propext, Classical.choice, Quot.sound]
```
HONEST: `βHensel_lift_identity` and `faaDiBruno_succ_sum_eq_zero` still carry `sorryAx` because they
route through the genuine open residual `trunc_defect_cancel_assembled`. The NEW lemma
`trunc_defect_eq_faaDiBruno_assembled_restricted` is `sorryAx`-free.

## WIPE INSURANCE — verbatim proofs (working tree gets hard-reset by harness; orchestrator commits on return)

### NEW PROVEN (axiom-clean) lemma — paste back if wiped:
```lean
theorem trunc_defect_eq_faaDiBruno_assembled_restricted (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          ∑ ab ∈ Finset.antidiagonal (t + 1),
            (liftToFunctionField (H := H)
                ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
            * (∑ m ∈ ((Finset.finsuppAntidiag (Finset.range i) ab.2).image
                      (ArkLib.PowerSeriesComposition.valueMultiset (Finset.range i))).filter
                      (fun m => (t + 1) ∉ m),
                (Multiset.countPerms m) •
                  ((m.map (fun j =>
                    PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)) := by
  classical
  rw [coeff_eval_Q_faaDiBruno H x₀ R (βHenselTrunc H x₀ R hHyp t) (t + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun ab hab => ?_
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hm
  have hpart_le : ∀ j ∈ ArkLib.PowerSeriesComposition.valueMultiset (Finset.range i) l,
      j ≤ ab.2 := by
    intro j hj
    rw [ArkLib.PowerSeriesComposition.valueMultiset, Multiset.mem_map] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    rw [Finset.mem_finsuppAntidiag] at hl
    rw [← hl.1]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simpa using hk)
  by_cases htop : (t + 1) ∈ ArkLib.PowerSeriesComposition.valueMultiset (Finset.range i) l
  · rw [if_neg (by simpa using htop)]
    have hzero : ((ArkLib.PowerSeriesComposition.valueMultiset (Finset.range i) l).map
        (fun j => PowerSeries.coeff j (βHenselTrunc H x₀ R hHyp t))).prod = 0 := by
      refine Multiset.prod_eq_zero ?_
      rw [Multiset.mem_map]
      exact ⟨t + 1, htop, coeff_βHenselTrunc_of_gt H x₀ R hHyp (Nat.lt_succ_self t)⟩
    rw [hzero]; exact smul_zero _
  · rw [if_pos (by simpa using htop)]
    congr 2
    refine Multiset.map_congr rfl fun j hj => ?_
    have hab2 : ab.2 ≤ t + 1 := by
      have := Finset.mem_antidiagonal.mp hab; omega
    have hjt : j ≤ t := by
      have hjle : j ≤ t + 1 := le_trans (hpart_le j hj) hab2
      rcases Nat.lt_or_ge j (t + 1) with h | h
      · exact Nat.lt_succ_iff.mp h
      · exact absurd (Nat.le_antisymm hjle h ▸ hj) htop
    rw [coeff_βHenselTrunc_of_le H x₀ R hHyp hjt]
```

### RE-CARVED residual (the ONLY new bare sorry) — paste back if wiped:
```lean
theorem trunc_defect_cancel_assembled (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = 0 := by
  sorry
```

### TARGET `faaDiBruno_succ_sum_eq_zero` now PROVEN — paste back if wiped:
```lean
theorem faaDiBruno_succ_sum_eq_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    (∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        ∑ ab ∈ Finset.antidiagonal (t + 1),
          (liftToFunctionField (H := H)
              ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
          * (∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) ab.2).image
                    (ArkLib.PowerSeriesComposition.valueMultiset (Finset.range i)),
              (Multiset.countPerms m) •
                ((m.map (fun j =>
                  PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))) = 0 := by
  rw [← coeff_eval_Q_faaDiBruno H x₀ R (βHenselAssembled H x₀ R hHyp) (t + 1)]
  exact coeff_succ_eval_of_trunc_defect_cancel H x₀ R hHyp t
    (trunc_defect_cancel_assembled H x₀ R hHyp t)
```

INSERTION POINT: replace the original `faaDiBruno_succ_sum_eq_zero` decl (its docstring + statement
+ `sorry`) in §4g of HenselNumerator.lean, inserting the two new theorems above it.

## The precise remaining math (for the next wave)

`trunc_defect_cancel_assembled` asks: the cleared truncated defect cancels the `ζ`-linear response.
Concretely, expand both sides and match term-by-term:
- LHS truncated defect = (PROVEN) `trunc_defect_eq_faaDiBruno_assembled_restricted`: sum over
  `Y`-degree `i`, antidiagonal `(a,b)=ab`, and value-multisets `m` with `(t+1) ∉ m`, of
  `lift((Δ_X^a R)|_{x0}.coeff i) · countPerms(m) · ∏_{j∈m} coeff_j(βHenselAssembled)`.
- The `ζ · coeff(t+1)(βHenselAssembled)` term: by `βHensel_succ`, `coeff(t+1)(βHenselAssembled)` is
  (modulo the `W/ξ` clearing `prod_map_coeff_assembled`/`partitionProd_coeff_assembled`) the
  negative of the `(A.1)` sum `−∑_{i1}∑_{λ, (t+1)∉λ.parts} W^{…}ξ^{…}·B_coeff·partitionProd`.
- The collapse now factors as: `prefactor` contributes only `lam.parts.countPerms`, while
  `hasseDerivY_coeff` contributes the Y-Hasse binomial `C(j, Σλ)`. The proven zero-peeling lemma
  `countPerms_replicate_zero_add_choose_sl` packages those as the full value-multiset weight
  `countPerms(m)`. The remaining work is not to change `prefactor`, but to formalize the full
  index/value equality between the restricted Faà-di-Bruno sum and the `(A.1)` sum, including the
  `B_coeff` carrier, the `ζ` sign, and the `W`/`ξ` clearing powers.
  The remaining unformalized work is the bijective index match `m ↔ (i1, λ)` (with the
  `i = i0 + i1`, the `(t+1)∉parts`/`(t+1)∉m` guard alignment, and the zero-slot/`j0` bookkeeping)
  and the resulting term-by-term weight equality. This is the genuine A.4 combinatorial core; it is
  TRUE (gammaGenuine is a genuine root) but a substantial multi-hundred-line formalization.

## Files
- `/home/shaw/arklib-prize/ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean` (edited; the 3 decls in §4g)
- Reused PROVEN connective lemmas (all in same file unless noted): `coeff_eval_Q_faaDiBruno`,
  `coeff_Q_eq_B`, `coeff_succ_eval_of_trunc_defect_cancel`, `coeff_succ_eval_defect_reduction`,
  `coeff_βHenselTrunc_of_gt`, `coeff_βHenselTrunc_of_le`, `partitionProd_coeff_trunc_assembled`,
  `partition_sum_add_one_local`, `prefactor_eq_choose_mul_countPerms`.
- `ArkLib/Data/Polynomial/MultinomialChainRule.lean`: `prefactor_paper_factorization`.
- `ArkLib/Data/Polynomial/PowerSeriesComposition.lean`: `coeff_pow_eq_partitionSum`,
  `countPerms_eq_multinomial`, `valueMultiset`.
- `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean`: `gammaGenuine_root`,
  `gammaGenuine_unique` (genuineness witnesses — the residual is TRUE).
