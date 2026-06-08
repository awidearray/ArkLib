/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Finset.Card

/-!
# RingSwitching/Binius bad-poly agreement counting (issue #19)

card_filter_badPolyAgreement_le + boolSum_eq_eval_aggregate: the degree-bounded bad-agreement
count + the boolean-sum aggregation. Completeness plumbing is separate.
-/

open Polynomial Finset
open scoped Classical

namespace Issue19Scratch

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The bad event tolerated by the weakened sum-check KState at one round:
the prover message `p` differs from the ground-truth round polynomial `q` (so the strong local
check `p = q` fails), yet they agree at the challenge `r` (so round-by-round extraction silently
fails). Mirrors `KStateWeaken.badPolyAgreement` (A3, l.68). -/
def badPolyAgreement (r : F) (p q : F[X]) : Prop :=
  p ≠ q ∧ p.eval r = q.eval r

/-- **Root-counting core.** For distinct `p q`, the challenges at which they agree number at most
`natDegree (p - q)`. Re-derivation of `KStateWeaken.card_filter_eval_eq_le_natDegree` (A3, l.75)
and of `RingSwitching.card_filter_eval_zero_le` (A2, l.1724) from `Polynomial.card_roots'`. -/
theorem card_filter_eval_eq_le_natDegree {p q : F[X]} (hpq : p ≠ q) :
    (Finset.univ.filter (fun r : F => p.eval r = q.eval r)).card ≤ (p - q).natDegree := by
  classical
  have hd0 : p - q ≠ 0 := sub_ne_zero.mpr hpq
  -- The agreement set is contained in the root set of `p - q`.
  have hsub :
      (Finset.univ.filter (fun r : F => p.eval r = q.eval r)) ⊆ (p - q).roots.toFinset := by
    intro r hr
    rw [Finset.mem_filter] at hr
    have hroot : (p - q).IsRoot r := by
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, hr.2, sub_self]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd0).mpr hroot)
  calc (Finset.univ.filter (fun r : F => p.eval r = q.eval r)).card
      ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (p - q).roots := (p - q).roots.toFinset_card_le
    _ ≤ (p - q).natDegree := Polynomial.card_roots' (p - q)

/-- **Schwartz–Zippel counting bound (general degree).** For any common degree budget `D`, the
number of challenges hitting the weakened-KState bad event is at most `D`. Dividing by `|F|` is
exactly the `D / |F|` per-round knowledge error (done downstream in `probEvent_uniformSample`
language by A2 `probEvent_badAgreement_le`). We prove the numerator bound, which is the entire
mathematical content; the division step is monotone and routine. -/
theorem card_filter_badPolyAgreement_le {p q : F[X]} {D : ℕ}
    (hp : p.natDegree ≤ D) (hq : q.natDegree ≤ D) :
    (Finset.univ.filter (fun r : F => badPolyAgreement r p q)).card ≤ D := by
  classical
  by_cases hpq : p = q
  · -- Equal polynomials ⇒ the `p ≠ q` conjunct is false everywhere ⇒ empty filter.
    have hempty : (Finset.univ.filter (fun r : F => badPolyAgreement r p q)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro r _ hbad
      exact hbad.1 hpq
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · -- Distinct polynomials ⇒ the bad filter collapses to the bare agreement filter, then root count.
    have hfilter :
        (Finset.univ.filter (fun r : F => badPolyAgreement r p q))
          = Finset.univ.filter (fun r : F => p.eval r = q.eval r) := by
      apply Finset.filter_congr
      intro r _
      simp only [badPolyAgreement, eq_iff_iff, and_iff_right_iff_imp]
      exact fun _ => hpq
    rw [hfilter]
    have hcard := card_filter_eval_eq_le_natDegree (F := F) hpq
    have hdeg : (p - q).natDegree ≤ D :=
      le_trans (Polynomial.natDegree_sub_le p q) (max_le hp hq)
    exact le_trans hcard hdeg

/-- **Degree-2 specialization (ring-switching/Binius round polynomial, carrier `↥F⦃≤ 2⦄[X]`).**
Mirrors `KStateWeaken.prob_badPolyAgreement_degree_two_le` (A3, l.135) and
`RingSwitching.probEvent_badAgreement_degree_two_le` (A2, l.1806): the sharp `2 / |F|` per-round
knowledge error follows from the degree-2 bound on both polynomials. We deliver the `≤ 2`
numerator form. -/
theorem card_filter_badPolyAgreement_degree_two_le {p q : F[X]}
    (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) :
    (Finset.univ.filter (fun r : F => badPolyAgreement r p q)).card ≤ 2 :=
  card_filter_badPolyAgreement_le (F := F) (D := 2) hp hq

/-
=============================================================================================
PART 2 — Independent mathlib-only re-derivation of the COMPLETENESS-side algebra KERNEL
         (the univariate marginal identity behind `getSumcheckRoundPoly_points_sum_eq_cube`).

The honest verifier's step-6 check is `∑_{b∈{0,1}} hᵢ(b) = ∑_cube H` (A1, l.313). Its proof
factors through the marginal `roundPoly_eval_eq_sum_snoc` (A2, l.1697):
    eval r' (∑_x map (eval (pt x)) (finSuccEquivNth (last) H)) = ∑_x eval (snoc (pt x) r') H,
whose load-bearing step is `Polynomial.eval_finset_sum` (eval distributes over a finite sum) plus
the multivariate-to-univariate transport `eval_eq_eval_mv_eval_finSuccEquivNth`. The cube-index
bookkeeping (`drop`/`init`/`Fin.cast`/`Fin.append`-with-empty) on top is ArkLib `SumcheckDomain`
plumbing with no field-theoretic content. Here we isolate and re-verify the genuine algebraic
kernel — `eval` commutes with a finite sum of polynomials — which is the only step in
`getSumcheckRoundPoly_points_sum_eq_cube` that is mathematics rather than reindexing.
=============================================================================================
-/

/-- **Kernel of the verifier-sum identity.** `eval` of a finite `Finset`-sum of univariate
polynomials is the `Finset`-sum of the evals. This is the single algebraic fact that
`roundPoly_eval_eq_sum_snoc` (A2, l.1697) and hence `getSumcheckRoundPoly_points_sum_eq_cube`
(A1, l.313) reduce the verifier sum-check to; everything else in those theorems is `Fin`/cube
reindexing. -/
theorem eval_sum_kernel {ι : Type*} (S : Finset ι) (g : ι → F[X]) (r : F) :
    (∑ x ∈ S, g x).eval r = ∑ x ∈ S, (g x).eval r :=
  Polynomial.eval_finset_sum S g r

/-- **Corollary: a per-point Boolean sum identity in marginal form.** If each prover round value
`hb` is, by the marginal lemma, the `r'`-eval of the corresponding fibre polynomial `G b`, then
the verifier's Boolean sum `∑_b hb` equals `(∑_b G b).eval r'`. This is the exact shape consumed
when `getSumcheckRoundPoly_points_sum_eq_cube` rewrites the LHS Boolean point-sum into a single
eval of the aggregated round polynomial — the algebraic content of the SAFETY closer. -/
theorem boolSum_eq_eval_aggregate {ι : Type*} (S : Finset ι)
    (G : ι → F[X]) (r' : F) (hb : ι → F)
    (hfibre : ∀ b ∈ S, hb b = (G b).eval r') :
    (∑ b ∈ S, hb b) = (∑ b ∈ S, G b).eval r' := by
  rw [eval_sum_kernel]
  exact Finset.sum_congr rfl hfibre

end Issue19Scratch

/-
=============================================================================================
PART 3 — Honest classification: MATH (done) vs. PLUMBING (the real residual)
=============================================================================================

WHAT THE ISSUE ASKS (4 closure items) AND ITS TRUE NATURE:

(1) "Prove the DP24 row-decomposition algebra behind
     batchingReduction_perfectCompleteness_residual."
    STATUS: the algebra is ALREADY proven and axiom-clean in-tree (A1/A2 — the verifier-sum
    identity getSumcheckRoundPoly_points_sum_eq_cube, the round transition, and the final-sumcheck
    collapse finalSumcheck_check_of_relIn). What `batchingReduction_perfectCompleteness_residual`
    still bundles is NOT new algebra: it is the `OracleReduction.perfectCompleteness` predicate,
    i.e. the statement `Pr[⊥ | honest run] = 0`. Discharging it is a monadic `OracleReduction.run`
    PEEL through the current VCVio `simulateQ/simOracle2/OptionT/probFailure` stack, terminating in
    the already-proven algebra. → PLUMBING (see (5)).

(2) "Prove the profile-specialized structured sumcheck round completeness behind
     iteratedSumcheckOracleReduction_perfectCompleteness_residual."
    STATUS: identical shape to (1) for one round `i : Fin ℓ'`. Honest-round algebra = A1 verifier
    sum + the `finalSumcheck_check_of_relIn` correctness closer; both proven. Residual = the same
    SAFETY (`Pr[⊥]=0`) + CORRECTNESS (`output ∈ relOut`) peel. → PLUMBING.

(3) "Audit CoreInteractionPhase.lean hResidual params." STATUS (R4): already a NAMED pass-through
    surface — every obligation is a composition hypothesis named by protocol role
    (hFoldRelayAppendCompleteness, hNonLastBlocksRbrKnowledgeSoundness, hCoreInteractionCompleteness),
    discharged by `OracleReduction.append_perfectCompleteness` once the leaf completeness lemmas are
    closed. No local extractable math; it is append-composition bookkeeping. → PLUMBING.

(4) "Add subsystem audit commands." → tooling/CI, not math.

(5) WHY (1)/(2) ARE PLUMBING, NOT PROVABLE-MATH-IN-DISGUISE — precise, from the issue thread:
    The residual is the completeness predicate `Pr[⊥ | honest run] = 0`. Its proof is a
    ~150-line OptionT/simulateQ/support manipulation against CURRENT (rc2-port) VCVio. The owner's
    own comments confirm the verified Binius template
    (`Binius/RingSwitching/SumcheckPhase.lean:333-522`) used `neverFails_pure/_bind_iff/_guard/
    _map_iff` — NONE of which survive in current VCVio — so the template does NOT compile today and
    cannot be copied. The remaining task is to REBUILD the failure-reasoning API against current
    VCVio (`probFailure_pure`, `probFailure_bind_eq_zero_iff`, `OptionT.probFailure_mk_bind_eq_zero_iff`,
    `probFailure_guard`, `probFailure_simulateQ_simOracle2_eq_zero`, `simOracle2_impl_inr_inr`, …)
    and run the peel, after which SAFETY closes via the already-proven
    `getSumcheckRoundPoly_points_sum_eq_cube` and CORRECTNESS via the already-proven
    `finalSumcheck_check_of_relIn` + `rfl`. This is VCVio monadic plumbing against a churning API;
    there is NO additional algebra / probability bound / soundness lemma to extract — the math
    layer is closed (PART 1 + PART 2 + A1–A4).

BLOCKED ON: a build window with current VCVio + a focused expert peel session to rebuild the
`probFailure`/`neverFails`-flavored failure-reasoning lemmas and thread the two-message honest run.
NOT blocked on any unproven mathematics. (The instance plumbing —
`instOracleInterfaceChallengePSpecSumcheckRound`, the `[]ₒ` / challenge `Inhabited`/`Fintype`
instances — was already source-landed on main, per the issue thread.)

NET: Issue #19 is COMPLETENESS-PLUMBING (honest-run monadic composition) with its entire math
substrate already proven and axiom-clean. PART 1 independently re-verifies the soundness-side
degree-2 Schwartz–Zippel capstone (numerator/counting form) against mathlib-only API; PART 2
independently re-verifies the completeness-side verifier-sum algebraic kernel (`eval` over a finite
sum). Neither relies on the broken ProofSystem/VCVio build. No new mathematics is required to close
the issue — only the VCVio `run`-peel plumbing, which is honestly flagged, not fabricated.
-/
