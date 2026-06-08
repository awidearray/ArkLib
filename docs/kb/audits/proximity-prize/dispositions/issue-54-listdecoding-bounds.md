STATUS: CLOSED — §3 list-bounds family verified resolved in-tree. Canonical per-paper record is the "Disposition ledger (issue #54)" header in `Bounds.lean`; this note is the audit-trail pointer + verification evidence (no duplicate ledger added).

# issue-54 — ABF26 §3 list-decoding theorem family in ListDecoding/Bounds

Tracking issue: lalalune/ArkLib#54
Canonical record: header of `ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean`
(the "Disposition ledger (issue #54)" section, per-paper).

This is the §3 list-bounds workstream, distinct from Johnson (#49), GGR11
interleaving (#50), and GK16/CZ25 subspace-design (#53).

## Finding

`Bounds.lean` is `sorry`-free, builds green, and is axiom-clean. Every actionable
deliverable of #54 is met in-tree; the genuinely-open items are external classical
results recorded as honest `def … : Prop` admits with proven `_of_residuals` reductions.
The issue's flagged optional target (the ST20 puncturing/coset pigeonhole core) is
already proved.

## Per-paper status (verified 2026-06-06)

PROVEN in-tree (`theorem`, `sorry`-free):
* `linear_lambda_ge_elias_volume_eli57` — L3.7 [Eli57] Elias volume lower bound.
* `linear_lambda_ge_entropy_volume` — C3.8 entropy-volume lower bound (MS77 ball
  volume via Robbins–Stirling, all in-tree).
* `linear_C_le_generalized_singleton_st20` — T3.9 [ST20 Thm 1.2]. **The puncturing /
  coset-agreement pigeonhole core #54 flags is complete** —
  `exists_representative_center_sum_hammingDist_le` (plurality averaging) plus helpers
  `st20_kernel_extract` / `st20_dist_bound` / `st20_nat_ineq` / `st20_ncard_eq`, under
  the faithful-lattice (`hlat`) and range (`ha_le`) hypotheses.
* `rs_lambda_high_rate_jh01` — T3.14 [JH01 Thm 2], via the interpolation construction in
  `ListDecoding.JH01`.

EXTERNAL ADMIT, NEEDS_CLASSICAL (`def … : Prop`; genuine paper content, no in-tree route):
* `random_rs_list_decoding` — T3.6 [AGL24 Thm 1.1]. The random-domain probability
  space is in-tree (`Probability.uniformSizeSubsetOfLe`); the AGL24 probability bound
  and parameter instantiation remain external.
* `large_alphabet_barrier_bdg24_agl23` — T3.10 [BDG24, AGL23].
* `random_linear_lambda_lower_glmrsw22` — T3.11 [GLMRSW22 Thm 4.1].

COUNTING DISCHARGED, narrowed to an irreducible geometric/asymptotic core
(`def` + proven `_of_residuals` reduction theorem):
* `rs_lambda_superpoly_extension_bkr06` — T3.12 [BKR06 Cor 2.2]. Arithmetic side proven
  (`rs_lambda_superpoly_extension_bkr06_of_residuals` via
  `BKR06.subspacePoly_natDegree_ge_target`, plus the fiber-count `_of_family`); residual =
  the BKR06 Lemma-3.5 roots→distinct-close-codewords *encoding* at genuine extension
  parameters. The BKR06 arithmetic side conditions also have a dedicated tracker (#38).
* `rs_lambda_large_prime_ghsz02` — T3.13 [GHSZ02 Cor 20]. Reduction proven
  (`rs_lambda_large_prime_ghsz02_of_residuals`, and `hcount_of_largeN` in
  `ToMathlib/GHSZ02Cor20.lean`); residual = the `GHSZ02LargeN` asymptotic input, which
  carries the genuine `for large enough p` threshold quantifier (`a^a ≤ n^{(1−β/2)n^ε}`
  above a threshold + constant absorption) and is not derivable in-tree from the
  unhypothesised statement. It is NOT a character-sum residual (GHSZ02 Cor 20 uses no
  multiplicative characters).

TRACKED UNDER #53 (GK16/CZ25), recorded for completeness:
* `subspaceDesign_list_decoding_cz25` — T3.4 [CZ25 Thm B.5].
* `frs_list_decoding_capacity_cz25` — C3.5 [CZ25 Cor 2.21], with proven
  `frs_list_decoding_capacity_cz25_of_residuals_prop`.

DEFERRED (out of §3 list-bounds scope, recorded in the file header):
* T3.15 [CW07] — algorithmic hardness barrier, out of scope per ABF26_PLAN §7 D2.

## Disposition: verify + record (no new theorems, no duplicate ledger)

The in-tree-provable §3 bounds are proved; the remainder are genuine external classical
inputs that cannot be formalized in-tree without importing whole classical
constructions, and are correctly carried as honest `Prop`-valued admits with proven
reductions to their irreducible cores. The closure work is verification + an audit-trail
pointer; duplicating the in-file ledger here would create a second naming scheme for the
same content (cf. issue-55 disposition), so this note points at the canonical header.

## Regression check

```sh
# file must stay sorry-free (docstring mentions of "sorry" are fine):
rg -n --pcre2 '(?<![`\w])(sorry|admit)\b' ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean
# proven theorems must remain `theorem`, external results must remain `def`:
rg -n '^theorem (linear_C_le_generalized_singleton_st20|rs_lambda_high_rate_jh01)\b' ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean
rg -n '^def (large_alphabet_barrier_bdg24_agl23|rs_lambda_superpoly_extension_bkr06|rs_lambda_large_prime_ghsz02)\b' ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean
# green + axiom-clean:
lake build ArkLib.Data.CodingTheory.ListDecoding.Bounds
```

If any external admit (BDG24/AGL23, GLMRSW22, BKR06 encoding, GHSZ02 asymptotic) is ever
upgraded to a `theorem`, update the `Bounds.lean` ledger and this note.
