# Audit: GitHub issues campaign (2026-06-04) — issues #1–#4, #222–#233, #450, #480

Status: complete. Companion to `gh-issues-222-224-225-233-verification.md` (which carries the
detailed per-theorem evidence for the four Guruswami–Sudan / InterleavedCode issues).

Scope: branch `gh-issues` (base: campaign tip `a36a4ea9`, a strict descendant of upstream
`main` `c1784658`). All verification commands were run in this worktree; axiom probes accept
only `propext`, `Classical.choice`, `Quot.sound`.

## Per-issue outcome

| Issue | Verdict | Evidence |
|---|---|---|
| #233 `decoder_mem_impl_dist` | RESOLVED UPSTREAM | `dist_le_of_mem_decoder`, sorry-free, axiom-clean (companion audit) |
| #222 `decoder_dist_impl_mem` | RESOLVED UPSTREAM (corrected) | `mem_decoder_of_dist` + necessary `p.natDegree < k` hypothesis |
| #224 GS divisibility | SUBSUMED | `dvd_property` (Basic.lean:884) + recast named lemma, sorry-free |
| #225 `minDist_eq_minDist` | MOOT | InterleavedCode API rewritten; maintainer-confirmed |
| #450 splitNth/foldNth eval lemmas | DONE (this branch) | `59a1c9bf`: `foldNth` def + `polyFold_eq_foldNth` + `eval_eq_sum_splitNth` + the 3 issue lemmas, axiom-clean |
| #480 Basic.lean docs | DONE (this branch, per maintainer redirection) | `ef78352f`: `docs/kb/concepts/oracle-reductions.md` (KB page, not docstrings — #433-safe); lint green |
| #2 commitment schemes | DONE | Box 1 (security defs) live upstream in `CommitmentScheme/Basic.lean`; box 2 done here: `76c2c944` states `ProtocolSpec.BCSTransform` (fully general) + `OracleReduction.BCSTransform` (phases-as-inputs; honest deferral notes), zero sorry |
| #3 sumcheck & Spartan | CHECKBOXES PROVEN; lift blocked on #433 | All three boxes sorry-free + axiom-clean as `Simple.*` (SingleRound.lean L898/L1000/L1037). Canonical lifted variants sorryAx-tainted via `OracleVerifier.liftContext` (see design gaps). Spartan defs blocked on the same |
| #1 IOR composition | DEFS DONE; proofs advanced to structural ceiling | `toFun_next` of `StateFunction.append` proven (`d4db5576`); 7 new sorry-free infrastructure lemmas (`dc52d2ea`, `2c1cc5b9`); remainder blocked on documented design gaps below |
| #4 Merkle trees | BATCH COMPLETENESS + BINDING PROVEN; RO layer open | `2ab8b7bf`: Batch/Extraction/Hiding modules (+475 lines, zero sorry); see VCVio findings below |

Sorry deltas vs upstream `main` on issue-relevant files (campaign base + this session):
SingleRound 21→12, Append 19→11, Spartan 8→3, SeqCompose 9→0, Implications 13→10,
Security/Basic 3→0, Rewinding 2→0, Sequential/General 3→0, BCS 2→0, Fold 5→0.

## Statements found FALSE or unprovable-as-stated (do not "prove"; need upstream statement fixes)

1. `Sumcheck...Simple.oracleVerifier_eq_verifier` (SingleRound.lean:594) and consumer
   `oracleReduction_eq_reduction` — the compiled oracle verifier guards on the *oracle
   statement* polynomial's D-sum; the plain verifier guards on the *prover message*
   polynomial. Equal only for honest provers (Finding-13 / eq-510 family; already de-tainted
   out of all real proofs).
2. `Simple.verifier_rbrKnowledgeSoundness` (L1031) and `Security.verifier_rbrKnowledgeSoundness`
   (L1524) — false at error `deg/|R|`: a malicious prover wins with probability 1 because the
   plain verifier never checks the message against the oracle (constructive attack in the
   2026-06-04 analysis; same root cause as item 1).
3. `StateFunction.append.toFun_full` (Append.lean) — unprovable for the conjunction-based
   composite `toFun`: in the S₁-false/S₂-true case, `S₂(last)` may legitimately hold on
   out-of-language input (lucky challenge — rbr soundness bounds this only probabilistically),
   so the demanded `Pr = 0` fails. Composite state function needs a different `toFun`.
4. (VCVio, pinned package) `MerkleTree.Inductive.completeness` is vacuous w.r.t. verification
   success: `NeverFail (….run)` over `OptionT` holds even for wrong-leaf openings, because
   `guard` rejection reifies as the *value* `none`. Adversarially probed. Acceptance-form
   replacements proven in `ArkLib/CommitmentScheme/MerkleTree/Batch.lean`. Worth reporting to
   VCVio upstream.

## Design gaps blocking the remaining sorries (all consistent with the #433 rewrite rationale)

- `OracleVerifier.liftContext` (LiftContext/OracleReduction.lean:48): under-determined — the
  Lens API lacks `simOStmt`/`liftOStmt` oracle-routing fields (commented-out TODOs at
  Lens.lean:63–94, Basic.lean:278–293). The sumcheck lens is a non-invertible virtual
  summation; Spartan's lenses change oracle index types. No restricted equiv-variant serves
  either use-case. Blocks: de-tainting the lifted sumcheck theorems, Spartan's 3 defs, the
  `Simpler` decomposition (4 defs).
- `Implications.lean` lattice: `knowledgeSoundness`/`rbrKnowledgeSoundness` quantify provers
  over the relation's fixed witness types while `soundness`/`rbrSoundness` quantify over
  arbitrary types (KS⇒S, rbrKS⇒rbrS not derivable as stated); SR-vs-plain theorems relate
  unrelated `init`/`impl` pairs; salt theorems have statement holes and Salt.lean itself
  documents an SR-not-preserved counterexample; the OneShot converter needs the upstream
  `IsMonotone` placeholder completed.
- rbr⇒plain telescoping pair (the only legitimately-closable Implications residue): the
  combinatorial backbone is now proven (`exists_flip_of_false_zero_true_last`,
  `exists_challenge_flip_of_false_zero_true_last`, `probEvent_exists_mem_le_sum`,
  `probEvent_exists_le_sum` in RoundByRound.lean; `runToRound_succ`,
  `processRound_challenge`, `fst_map_runToRound_succ_challenge` in Execution.lean — and the
  feared fresh-challenge coupling mismatch was checked and does NOT exist). The remaining gap
  is a probabilistic-monad layer over `OptionT (StateT σ ProbComp)` + `simulateQ`:
  failure-monotone bind, per-round decomposition of full-run marginals, and a
  verifier-run↔full-run bridge. Exact stuck goal recorded in the 2026-06-04 agent ledger.
- `Prover.append_run` + `append_completeness`: blocked on a runToRound split decomposition and
  the upstream-documented commutative-monad obstacle (Append.lean:404–448, "prove after VCVio
  refactor").
- Merkle full extractability (§18.5) + hiding: the deterministic cores are proven
  (`opening_binding`, extraction uniqueness, salted completeness); the missing layer is
  negligible-collision-probability reasoning over the random oracle, absent from VCVio.

## New infrastructure banked (sorry-free, axiom-clean; verified 2026-06-04)

`exists_flip_of_false_zero_true_last`, `exists_challenge_flip_of_false_zero_true_last`,
`probEvent_exists_mem_le_sum`, `probEvent_exists_le_sum` (RoundByRound.lean);
`Prover.runToRound_succ`, `Prover.processRound_challenge`,
`Prover.fst_map_runToRound_succ_challenge` (Execution.lean);
`StateFunction.append.toFun_next` closed (Append.lean);
`ProtocolSpec.BCSOpeningPhase`/`BCSTransform`, `Reduction.bcsMessageOpening`,
`OracleReduction.BCSTransform` (BCS/Basic.lean);
`Polynomial.foldNth` + `polyFold_eq_foldNth` + `eval_eq_sum_splitNth` +
`splitNth_two_eval_add`/`_sub` + `foldNth_two_eval` (SplitFold.lean);
`InductiveMerkleTree` batch/extraction/hiding modules (CommitmentScheme/MerkleTree/).

---

## FINAL LEDGER (2026-06-04, post-convergence proving waves)

Tree: `gh-issues` = consolidated convergence (campaign pin 19a7a93e7 + build fixes + issue
deliverables + consolidated/prize branch merges). All remaining sorries were attacked by
dedicated agents; final state below. Census: ~66 sorry-tokens (from 94 at the pin).

### Closed by the final waves (commits on gh-issues)
`b2a07aee9` Composition/General 7/7 (seqCompose security stack; taint now gated solely on
Append's 7) · `5cd537e60` BBF Steps relay pair regraft · `bb0c9f32f` FRIBinius 12 profile-law
obligations (FRIBinius/General → 0 sorries) · `04f2c6818` DP24 capstone layer ported to
RingSwitching/Prelude (16 lemmas) + **soundness-bug fix** (performCheckOriginalEvaluation
columns→rows) + BatchingPhase L424 · `4fba2a67e` q-ary Plotkin average-distance bound (4
lemmas; also corrected an inverted factor in the docstring) · `5fee4013b` BBF General def pair
· `a144924af` Steps toFun_next bad-event branch + simulateQ toolkit. All axiom-clean
(propext/Classical.choice/Quot.sound only on own proofs).

### MUST-STAY-OPEN (9) — intentional, do not close
- ToyProblem ×7: EF Proximity Prize leaderboard contract (proximityprize.org, ABF26 §6);
  routes partially DISPROVEN (Diamond-Gruen eprint 2025/2046); in-file "do not close" markers.
- mca_johnson_bound_CONJECTURE, mca_capacity_bound_CONJECTURE: ACFY24 Conjecture 4.12;
  capacity variant DISPROVEN.

### Research frontier (each with its named gap)
- **§5 list-decoding extraction** (gates Curves keystone → Agreement ×6, Stir/ProximityGap,
  BatchedFri 8.3): needs `hcoeffPoly` = Claims 5.8'/5.9 in curve coeff-poly form; ingredients
  C (Appendix-A↔§5 bridge) + D (β_regular as Hensel numerator). Active on concurrent
  worktrees (arklib-agree/arklib-bounds) — harvest, don't race.
- **Append ×7** (gates General's taint + Logup ×2): rbr pair needs V₁-determinism hypothesis
  or non-deterministic StateFunction.append; completeness family = commutative-monad reorder
  (direction-independent); verify pair = AppendCoherent with verified 13-protocol-file blast
  radius + unsolved append_toVerifier simulateQ-fusion. Probability toolkit fully in-tree.
- **BaseFold crypto content**: QueryPhase ×3 (proximity bound (1/2+2^-(𝓡+1))^γ, Lemma 4.9
  cast alignment), Steps fold/commit/finalSumcheck residuals (extraction soundness,
  reject-branch reconstruction), BBF General ×2 theorems (gated on QueryPhase).
- **RingSwitching residuals** (~6): eqTilde tensor-expansion dual (L563), SZ κ/|L| bridge,
  KState reconstructions, shared snoc-vs-cons defect (L203, counterexample-backed, needs
  owner fix in Sumcheck.Structured).
- **JohnsonBound ×2**: needs the sharp Johnson–Plotkin sphere/projection argument (in-tree
  second-moment provably lands at reciprocal radius; Plotkin ingredient now banked).
- **Stir/MainThm ×2**: IOPP/VectorIOP construction layer absent. **CoordinateWise ×1**:
  forking/rewinding extractor framework (explicitly future work). **InterleavedCode ×1**:
  [GGR11] external admit. **MCA ×2 open** (mca_linearCode needs CA-soundness field on
  ProximityGenerator — statement gap with falsifying instantiation documented; mca_rsc =
  multi-step ABF26 §4). **Whir Folding ×3 + RBRSoundness ×1**: MCA-chain + IOPP gated.

### Verdict
Every theorem provable with current in-tree mathematics is proven. The remainder is:
intentional prize-contract markers, stated conjectures (one disproven), and the genuine
research frontier with each gap precisely named — the same frontier the source papers leave
open or the upstream authors have deferred (#433-class design decisions).
