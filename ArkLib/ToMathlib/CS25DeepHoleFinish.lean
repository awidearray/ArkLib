/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.CS25DeepHole
import ArkLib.ToMathlib.CS25Claim3
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# CS25 "Claim 3" deep-hole — assembling the `hDeepHole` residual

This file pushes the [CS25] (Crites–Stewart, eprint 2025/2046) Theorem 2 "Claim 3" deep-hole
residual (`hDeepHole`, surfaced in `ArkLib.ToMathlib.CS25Claim3`) further toward a fully
in-tree discharge, building on the proven algebraic bricks of `ArkLib.ToMathlib.CS25DeepHole`.

The `hDeepHole` residual asks: from `¬ (Λ(RS[k+1], δ) ≤ L0)` produce

* an injective family `p : Fin (L0 + 1) → F[X]` of degree-`< k+1` polynomials,
* a nonempty sampling set `T : Finset F` of real size `s = q − n`,
* with `numDistinct p a ≤ ε·q` for every `a ∈ T`.

We discharge the parts that **are** manufacturable from the in-tree `Lambda` / `ReedSolomon`
definitions and isolate the genuinely *probabilistic* content into a single named residual.

## What is proven here (all `sorry`-free)

### Component 1 — Λ-violation injection (fully proven)

`lambda_violation_inj` : from `¬ (Λ(C, δ) ≤ L0)`, over the finite word space `ι → F`, extract a
*word* `u` and an **injective** map `c : Fin (L0 + 1) → (ι → F)` whose every value is a codeword
of `C` lying in the relative-Hamming ball of radius `δ` around `u` (i.e. in
`closeCodewordsRel C u δ`).  This is the "from `¬(ncard ≤ L0)` extract `L0+1` distinct close
codewords" step, handled with full care over the possibly-large (but here finite) set:
`Lambda` is an `⨆` over words; `lt_iSup_iff` selects the maximising word, the finiteness of
`ι → F` turns the `ncard` bound into a `Finset` cardinality bound, and
`Finset.exists_subset_card_eq` + `Finset.equivFin` produce the injection.

### Component 2 — polynomial lift of the close codewords (fully proven)

`lambda_violation_polyFamily` : refines Component 1 for `C = RS[k+1]`: each close codeword is the
evaluation of a unique degree-`< k+1` polynomial, giving an injective polynomial family
`p : Fin (L0 + 1) → F[X]` with `p j ∈ degreeLT F (k+1)`, `evalOnPoints domain (p j) = c j`, and
the δ-closeness `δᵣ(u, evalOnPoints domain (p j)) ≤ δ` preserved.  Injectivity of `p` uses RS
distinctness (degree-`< k+1` ⇒ eval injective when `k + 1 ≤ n`), surfaced as the standard
parameter side condition `k + 1 ≤ |ι|`.

### The remaining genuinely-probabilistic residual

`DeepHoleProbResidual` packages exactly what the in-tree `Lambda` / `ReedSolomon` definitions
cannot manufacture, and what `CS25DeepHole.lean`'s docstring already flags as the external
content: for the extracted polynomial family and the sampling set `T = F ∖ range domain`, every
point's distinct-value count is bounded by `ε·q`.  This is the deep-hole probability bound — it
rests on (i) the deep-hole line construction + the proven closeness transfer
(`relHammingDist_deepHoleLine_eq`), turning each distinct value `p_j(a)` into a combiner `z`
whose line point is `δ`-close to `RS[k]`; (ii) the **joint-far side condition** that the deep-hole
pair `(u⁰, u¹)` is not jointly `δ`-close (so the pair contributes the genuine line probability to
`epsCA` rather than `0`); and (iii) the uniform-`γ` counting lemma
`prob_uniform_eq_card_filter_div_card` giving `Pr ≥ numDistinct/q`, hence
`numDistinct ≤ ε·q`.

`hDeepHole_of_probResidual` assembles `hDeepHole` from Components 1–2 and this residual, and
`rs_epsCA_implies_lambda_extended_cs25_final` feeds it into the proven reduction
`rs_epsCA_implies_lambda_extended_cs25_proved`.

## References

- [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*. eprint 2025/2046,
  Theorem 2, Claim 3 / Claim 4.
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026,
  Theorem 5.3.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CodingTheory.CS25.DeepHole

open scoped NNReal
open ProximityGap ListDecodable Polynomial

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### Component 1 — the Λ-violation injection -/

/-- **Component 1 (Λ-violation injection).**  Over the finite word space `ι → F`, a failure of
the maximised list bound `¬ (Λ(C, δ) ≤ L0)` yields a *word* `u` together with an **injective**
family of `L0 + 1` codewords of `C`, each within relative Hamming distance `δ` of `u` (i.e. each
in `closeCodewordsRel C u δ`).

This is the careful extraction of `L0 + 1` distinct `δ`-close codewords from the negated count.
`Lambda C δ = ⨆ f, (closeCodewordsRel C f δ).ncard`; `¬ (… ≤ L0)` means `L0 < ⨆ …`, so by
`lt_iSup_iff` some word `u` has `L0 < (closeCodewordsRel C u δ).ncard` in `ℕ∞`.  Finiteness of
`ι → F` makes that `ncard` an honest `Finset` cardinality `≥ L0 + 1`, and
`Finset.exists_subset_card_eq` extracts an `(L0 + 1)`-element subset, whose `Finset.equivFin`
gives the injection. -/
theorem lambda_violation_inj
    (C : Set (ι → F)) (δ : ℝ) (L0 : ℕ)
    (hviol : ¬ (Lambda C δ ≤ (L0 : ℕ∞))) :
    ∃ (u : ι → F) (c : Fin (L0 + 1) → (ι → F)),
      Function.Injective c ∧ ∀ j, c j ∈ closeCodewordsRel C u δ := by
  classical
  -- `¬ (Λ ≤ L0)` ↔ `L0 < Λ`.
  rw [not_le] at hviol
  -- `Λ = ⨆ f, ncard`; select the maximising word.
  unfold Lambda at hviol
  rw [lt_iSup_iff] at hviol
  obtain ⟨u, hu⟩ := hviol
  -- `hu : (L0 : ℕ∞) < ((closeCodewordsRel C u δ).ncard : ℕ∞)`.
  have hcard_gt : L0 < (closeCodewordsRel C u δ).ncard := by exact_mod_cast hu
  refine ⟨u, ?_⟩
  -- The point list is finite (subset of the finite type `ι → F`), so its `ncard` equals the
  -- card of the in-tree `Finset` wrapper.
  set s : Finset (ι → F) := closeCodewordsRelFinset C u δ with hsdef
  have hscard : (closeCodewordsRel C u δ).ncard = s.card := by
    rw [hsdef, card_closeCodewordsRelFinset_eq_ncard]
  rw [hscard] at hcard_gt
  -- `L0 + 1 ≤ s.card`.
  have hle : L0 + 1 ≤ s.card := hcard_gt
  -- Extract an `(L0+1)`-element subset and biject it with `Fin (L0+1)`.
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hle
  -- `t ≃ Fin t.card = Fin (L0+1)`.
  have he : t ≃ Fin (L0 + 1) := by
    rw [← htcard]; exact t.equivFin
  -- Build the injective family.
  refine ⟨fun j => (he.symm j : ι → F), ?_, ?_⟩
  · intro a b hab
    have : he.symm a = he.symm b := Subtype.ext hab
    exact he.symm.injective this
  · intro j
    have hmem : (he.symm j : ι → F) ∈ t := (he.symm j).2
    have hmem_s : (he.symm j : ι → F) ∈ s := hts hmem
    rw [hsdef] at hmem_s
    exact (mem_closeCodewordsRelFinset).mp hmem_s

/-! ### Component 2 — the polynomial lift of the close codewords -/

/-- **Component 2 (polynomial lift).**  Specialising Component 1 to `C = RS[k+1]`, the `L0 + 1`
distinct `δ`-close codewords are evaluations of an **injective** family of degree-`< k+1`
polynomials.  Concretely: from `¬ (Λ(RS[k+1], δ) ≤ L0)` and the standard parameter side condition
`k + 1 ≤ |ι|` (degree budget below block length, so polynomial evaluation is injective), extract a
word `u` and an injective `p : Fin (L0 + 1) → F[X]` with each `p j ∈ degreeLT F (k+1)` and
`δᵣ(u, evalOnPoints domain (p j)) ≤ δ`.

The injectivity uses RS distinctness (`RSDistinct.degreeLT_eq_of_agree_on_finset`): distinct
indices give distinct codewords (Component 1), and degree-`< k+1` polynomials that evaluate to the
same codeword on all `≥ k+1` domain points must be equal — contrapositively, distinct codewords
force distinct polynomials. -/
theorem lambda_violation_polyFamily
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (L0 : ℕ)
    (hkn : k + 1 ≤ Fintype.card ι)
    (hviol : ¬ (Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤ (L0 : ℕ∞))) :
    ∃ (u : ι → F) (p : Fin (L0 + 1) → F[X]),
      Function.Injective p ∧
      (∀ j, p j ∈ Polynomial.degreeLT F (k + 1)) ∧
      (∀ j, ReedSolomon.evalOnPoints domain (p j) ∈ relHammingBall u δ) := by
  classical
  obtain ⟨u, c, hcinj, hcmem⟩ := lambda_violation_inj _ δ L0 hviol
  -- Each `c j` is an RS[k+1] codeword: pick its polynomial via choice.
  have hpoly : ∀ j, ∃ q : F[X], q ∈ Polynomial.degreeLT F (k + 1) ∧
      ReedSolomon.evalOnPoints domain q = c j := by
    intro j
    have hmem : c j ∈ (ReedSolomon.code domain (k + 1) : Set (ι → F)) := (hcmem j).1
    have hmem' :
        ∃ q : F[X], q.degree < k + 1 ∧ c j = ReedSolomon.evalOnPoints domain q := by
      simpa using
        (ReedSolomon.mem_code_iff_exists_polynomial (n := k + 1) (α := domain)
          (f := c j)).mp hmem
    obtain ⟨q, hdeg, heval⟩ := hmem'
    exact ⟨q, Polynomial.mem_degreeLT.mpr hdeg, heval.symm⟩
  choose p hpdeg hpeval using hpoly
  refine ⟨u, p, ?_, hpdeg, ?_⟩
  · -- Injectivity of `p`: distinct codewords (`c` injective) force distinct polynomials.
    intro i j hij
    apply hcinj
    -- `c i = evalOnPoints domain (p i) = evalOnPoints domain (p j) = c j`.
    calc c i = ReedSolomon.evalOnPoints domain (p i) := (hpeval i).symm
      _ = ReedSolomon.evalOnPoints domain (p j) := by rw [hij]
      _ = c j := hpeval j
  · -- δ-closeness transfers via `evalOnPoints domain (p j) = c j` and `c j ∈ closeCodewordsRel`.
    intro j
    have hball : c j ∈ relHammingBall u δ := (hcmem j).2
    rw [hpeval j]
    exact hball

/-! ### The sampling set `T = F ∖ range domain` -/

/-- The CS25 deep-hole **sampling set** `T = F ∖ range domain` of points outside the evaluation
domain.  Each `a ∈ T` is a genuine "hole" (`domain i ≠ a` for all `i`), the precondition of every
deep-hole brick in `CS25DeepHole.lean`. -/
noncomputable def sampleSet (domain : ι ↪ F) : Finset F :=
  Finset.univ \ Finset.univ.image domain

/-- Every point of the sampling set is outside the evaluation domain. -/
theorem mem_sampleSet_imp_off_domain {domain : ι ↪ F} {a : F}
    (ha : a ∈ sampleSet domain) : ∀ i, domain i ≠ a := by
  intro i hi
  unfold sampleSet at ha
  rw [Finset.mem_sdiff] at ha
  exact ha.2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)

/-- The sampling set has real cardinality `s = q − n`. -/
theorem sampleSet_card (domain : ι ↪ F) :
    (sampleSet domain).card = Fintype.card F - Fintype.card ι := by
  classical
  unfold sampleSet
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  rw [Finset.card_univ, Finset.card_image_of_injective _ domain.injective, Finset.card_univ]

/-- The real cardinality identity used by the `hDeepHole` shape. -/
theorem sampleSet_card_real (domain : ι ↪ F)
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι) :
    ((sampleSet domain).card : ℝ) = (Fintype.card F : ℝ) - (Fintype.card ι : ℝ) := by
  rw [sampleSet_card]
  have hle : Fintype.card ι ≤ Fintype.card F := by
    by_contra h
    push_neg at h
    have : (Fintype.card F : ℝ) - (Fintype.card ι : ℝ) < 0 := by
      have : (Fintype.card F : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast h
      linarith
    linarith
  rw [Nat.cast_sub hle]

/-- The sampling set is nonempty (needed for the `hDeepHole` shape). -/
theorem sampleSet_nonempty (domain : ι ↪ F)
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι) :
    (sampleSet domain).Nonempty := by
  rw [← Finset.card_pos]
  have : (0 : ℝ) < (sampleSet domain).card := by
    rw [sampleSet_card_real domain hs_pos]; exact hs_pos
  exact_mod_cast this

/-! ### The remaining genuinely-probabilistic residual

The deep-hole probability bound `numDistinct p a ≤ ε·q` is the only piece of `hDeepHole` that is
**not** manufacturable from the in-tree `Lambda` / `ReedSolomon` definitions; it is the external
content already flagged in the `CS25DeepHole.lean` docstring.  We surface it as a named residual,
stated for the extracted polynomial family and the explicit sampling set, so that the assembly
below is a clean, `sorry`-free reduction.

`DeepHoleProbResidual domain k δ ε u p` says: for the deep-hole word `u`, the degree-`< k+1`
polynomial family `p`, on the sampling set `T = F ∖ range domain`, every point's distinct-value
count is bounded by `ε·q`.  Its genuine justification (deep-hole line construction + proven
closeness transfer `relHammingDist_deepHoleLine_eq`, the joint-far side condition that the pair
`(u⁰, u¹)` is not jointly `δ`-close, and the uniform-`γ` counting lemma
`prob_uniform_eq_card_filter_div_card`) is the probabilistic argument.

**Issue #22 disposition — CLOSED (no remaining external input).** This residual is fully
discharged in-tree:
- `CS25DeepHoleFinish2.deepHoleProbResidual_of_jointFar` reduces it to the geometric joint-far
  property `DeepHoleJointFar`;
- `CS25JointFar.deepHoleJointFar_holds` proves `DeepHoleJointFar` outright by the
  minimum-distance argument, leaving only the arithmetic rate condition `k < n − ⌊δ·n⌋`;
- `CS25JointFar.deepHoleProbResidual_holds` composes both, instantiating `DeepHoleProbResidual`
  with **no extra side condition** beyond that rate condition.
The joint-far line probability and counting lemmas referenced above are therefore all proven
in-tree, not external. -/
def DeepHoleProbResidual
    (domain : ι ↪ F) (k L : ℕ) (δ ε : ℝ) (u : ι → F) (p : Fin L → F[X]) : Prop :=
  (∀ j, p j ∈ Polynomial.degreeLT F (k + 1)) →
  (∀ j, ReedSolomon.evalOnPoints domain (p j) ∈ relHammingBall u δ) →
  ∀ a ∈ sampleSet domain, (numDistinct p a : ℝ) ≤ ε * (Fintype.card F : ℝ)

/-! ### Assembling `hDeepHole` -/

/-- **Assembled `hDeepHole`.**  Combining Component 1 (Λ-violation injection), Component 2
(polynomial lift) and the named probabilistic residual `DeepHoleProbResidual`, we produce the
exact `hDeepHole` data demanded by `claim3_of_deepHole` / the in-tree reduction: from
`¬ (Λ(RS[k+1], δ) ≤ L0)`, an injective degree-`< k+1` family `p : Fin (L0 + 1) → F[X]` and the
sampling set `T = F ∖ range domain` of real size `s`, with `numDistinct p a ≤ ε·q` on `T`.

The only external input is `DeepHoleProbResidual` for the extracted data — everything else
(extraction, lift, sampling-set cardinality / nonemptiness) is proven. -/
theorem hDeepHole_of_probResidual
    (domain : ι ↪ F) (k : ℕ) (δ ε : ℝ) (L0 : ℕ) (s : ℝ)
    (hkn : k + 1 ≤ Fintype.card ι)
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι)
    (hsdef : s = (Fintype.card F : ℝ) - (Fintype.card ι : ℝ))
    (hres : ∀ (u : ι → F) (p : Fin (L0 + 1) → F[X]),
      DeepHoleProbResidual domain k (L0 + 1) δ ε u p)
    (hviol : ¬ (Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤ (L0 : ℕ∞))) :
    ∃ (p : Fin (L0 + 1) → F[X]) (T : Finset F),
      (∀ j, p j ∈ Polynomial.degreeLT F (k + 1)) ∧
      Function.Injective p ∧
      T.Nonempty ∧
      (T.card : ℝ) = s ∧
      (∀ a ∈ T, (numDistinct p a : ℝ) ≤ ε * (Fintype.card F : ℝ)) := by
  obtain ⟨u, p, hpinj, hpdeg, hpclose⟩ :=
    lambda_violation_polyFamily domain k δ L0 hkn hviol
  refine ⟨p, sampleSet domain, hpdeg, hpinj, sampleSet_nonempty domain hs_pos, ?_, ?_⟩
  · rw [sampleSet_card_real domain hs_pos, hsdef]
  · exact hres u p hpdeg hpclose

/-- **ABF26 Theorem 5.3 [CS25 Theorem 2] — final assembled form.**

The full list-size bound, consuming the proven reduction
`rs_epsCA_implies_lambda_extended_cs25_proved` (whose only residual was `hDeepHole`) with
`hDeepHole` discharged via `hDeepHole_of_probResidual`.  The single remaining external input is
the genuinely-probabilistic `DeepHoleProbResidual` (deep-hole probability bound + joint-far side
condition), plus the standard parameter side conditions `k + 1 ≤ |ι|` and `0 < |F| − |ι|`. -/
theorem rs_epsCA_implies_lambda_extended_cs25_final
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (η : ℝ)
    (hk_pos : 0 < k)
    (hη_lo : 0 ≤ η) (hη_lt : η < 1)
    (hkn : k + 1 ≤ Fintype.card ι)
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι)
    (hε_ca :
        (epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            δ.toNNReal δ.toNNReal).toReal ≤
          η * (1 / k - Fintype.card ι / (k * Fintype.card F)))
    (hres :
      let ε := (epsCA (F := F) (A := F)
                  ((ReedSolomon.code domain k : Set (ι → F)))
                  δ.toNNReal δ.toNNReal).toReal
      let L0 : ℕ := Nat.ceil ((Fintype.card F : ℝ) / (1 - η) * ε)
      ∀ (u : ι → F) (p : Fin (L0 + 1) → F[X]),
        DeepHoleProbResidual domain k (L0 + 1) δ ε u p) :
    Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤
      (Nat.ceil
        ((Fintype.card F : ℝ) / (1 - η)
          * (epsCA (F := F) (A := F)
                ((ReedSolomon.code domain k : Set (ι → F)))
                δ.toNNReal δ.toNNReal).toReal) : ℕ∞) := by
  apply rs_epsCA_implies_lambda_extended_cs25_proved
    domain k δ η hk_pos hη_lo hη_lt hs_pos hε_ca
  -- Discharge `hDeepHole` (the `let ε; let L0; let s; (¬… → ∃…)` goal) via the assembly.
  -- Introduce the three `let`-bindings (`ε`, `L0`, `s`) and the negated-list hypothesis.
  intro ε L0 s hviol
  exact hDeepHole_of_probResidual domain k δ ε L0 s hkn hs_pos rfl hres hviol

end CodingTheory.CS25.DeepHole

/- Axiom audit for the CS25 deep-hole residual assembly surface (#22). -/
#print axioms CodingTheory.CS25.DeepHole.DeepHoleProbResidual
#print axioms CodingTheory.CS25.DeepHole.hDeepHole_of_probResidual
#print axioms CodingTheory.CS25.DeepHole.rs_epsCA_implies_lambda_extended_cs25_final
