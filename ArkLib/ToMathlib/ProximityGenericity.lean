import Mathlib

/-! Finite-field genericity counting for BCIKS20 §5 Claim 5.7 (the `hx0`/`hsep`
specialization in `GraphExtractionHypotheses`): a good `x₀` avoiding finitely many nonzero
obstruction polynomials exists when `|F|` exceeds their total degree. -/

open Polynomial Finset

namespace ProximityGap.Genericity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Good evaluation point exists (finite-field counting).** Given a finite family of nonzero
polynomials whose degrees sum to less than `|F|`, some field element is a non-root of all of
them. The bad set `⋃ roots` has at most `∑ natDegree < |F|` elements. -/
theorem exists_eval_ne_zero_of_sum_natDegree_lt
    (ps : Finset F[X]) (hne : ∀ p ∈ ps, p ≠ 0)
    (hcard : ∑ p ∈ ps, p.natDegree < Fintype.card F) :
    ∃ x : F, ∀ p ∈ ps, p.eval x ≠ 0 := by
  classical
  set bad : Finset F := ps.biUnion (fun p => p.roots.toFinset) with hbad
  have hbad_card : bad.card < Fintype.card F := by
    calc bad.card ≤ ∑ p ∈ ps, (p.roots.toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ ps, p.natDegree := by
          apply Finset.sum_le_sum
          intro p _hp
          exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' p)
      _ < Fintype.card F := hcard
  have hne_univ : bad ≠ (Finset.univ : Finset F) := by
    intro h
    rw [h, Finset.card_univ] at hbad_card
    exact lt_irrefl _ hbad_card
  obtain ⟨x, hx⟩ : ∃ x : F, x ∉ bad := by
    by_contra h
    push Not at h
    exact hne_univ (Finset.eq_univ_iff_forall.mpr h)
  refine ⟨x, fun p hp hpx => ?_⟩
  apply hx
  rw [hbad, Finset.mem_biUnion]
  refine ⟨p, hp, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hne p hp)]
  exact hpx

/-- **Good point for an indexed obstruction family.** If per-`R` obstruction polynomials
`obstr R` (`R ∈ Rs`) are nonzero with total degree `< |F|`, a single `x₀` makes all of them
nonvanish. In the #8 application `Rs = pg_Rset` and `obstr R` packages the leading-coefficient
witness (for `hx0`) / the Y-discriminant (for `hsep`), so a good specialization `x₀` exists
once `|F|` exceeds the total obstruction degree. -/
theorem exists_good_point_of_obstructions
    {ι : Type*} (Rs : Finset ι) (obstr : ι → F[X])
    (hne : ∀ R ∈ Rs, obstr R ≠ 0)
    (hcard : ∑ R ∈ Rs, (obstr R).natDegree < Fintype.card F) :
    ∃ x : F, ∀ R ∈ Rs, (obstr R).eval x ≠ 0 := by
  classical
  set bad : Finset F := Rs.biUnion (fun R => (obstr R).roots.toFinset) with hbad
  have hbad_card : bad.card < Fintype.card F := by
    calc bad.card ≤ ∑ R ∈ Rs, ((obstr R).roots.toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ R ∈ Rs, (obstr R).natDegree := by
          apply Finset.sum_le_sum
          intro R _hR
          exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' (obstr R))
      _ < Fintype.card F := hcard
  have hne_univ : bad ≠ (Finset.univ : Finset F) := by
    intro h
    rw [h, Finset.card_univ] at hbad_card
    exact lt_irrefl _ hbad_card
  obtain ⟨x, hx⟩ : ∃ x : F, x ∉ bad := by
    by_contra h
    push Not at h
    exact hne_univ (Finset.eq_univ_iff_forall.mpr h)
  refine ⟨x, fun R hR hRx => ?_⟩
  apply hx
  rw [hbad, Finset.mem_biUnion]
  refine ⟨R, hR, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hne R hR)]
  exact hRx

/-- **Good specialization over a coefficient domain (the form #8 needs).** For a finite family
of nonzero polynomials over an integral domain `T` into which `F` embeds (`φ` injective), and
whose degrees sum to `< |F|`, some `x : F` makes every `p.eval (φ x)` nonzero. In the BCIKS20
application `T = F[Z][Y]`, `φ = C·C` (the constant embedding), and `p = R` viewed as a
polynomial in the `X`-variable over `T`: the bad `x₀` are exactly the `T`-roots of `R`, so the
`hx0` specialization `evalX (C x₀) R ≠ 0` holds for `|F| >` the total `X`-degree, **with no
coefficient extraction** — the obstruction is `R` itself over the domain. -/
theorem exists_eval_ne_zero_over_domain
    {T : Type*} [CommRing T] [IsDomain T] (φ : F →+* T) (hφ : Function.Injective φ)
    (ps : Finset (Polynomial T)) (hne : ∀ p ∈ ps, p ≠ 0)
    (hcard : ∑ p ∈ ps, p.natDegree < Fintype.card F) :
    ∃ x : F, ∀ p ∈ ps, p.eval (φ x) ≠ 0 := by
  classical
  -- bad set: x ∈ F whose image φ x is a root of some p
  set bad : Finset F :=
    ps.biUnion (fun p => (p.roots.toFinset).preimage φ (hφ.injOn)) with hbad
  have hbad_card : bad.card < Fintype.card F := by
    calc bad.card ≤ ∑ p ∈ ps, ((p.roots.toFinset).preimage φ (hφ.injOn)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ p ∈ ps, p.natDegree := by
          apply Finset.sum_le_sum
          intro p _hp
          calc ((p.roots.toFinset).preimage φ (hφ.injOn)).card
              ≤ (p.roots.toFinset).card :=
                Finset.card_le_card_of_injOn φ
                  (fun a ha => Finset.mem_preimage.mp ha) (hφ.injOn)
            _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
            _ ≤ p.natDegree := Polynomial.card_roots' p
      _ < Fintype.card F := hcard
  have hne_univ : bad ≠ (Finset.univ : Finset F) := by
    intro h; rw [h, Finset.card_univ] at hbad_card; exact lt_irrefl _ hbad_card
  obtain ⟨x, hx⟩ : ∃ x : F, x ∉ bad := by
    by_contra h; push Not at h; exact hne_univ (Finset.eq_univ_iff_forall.mpr h)
  refine ⟨x, fun p hp hpx => ?_⟩
  apply hx
  rw [hbad, Finset.mem_biUnion]
  refine ⟨p, hp, ?_⟩
  rw [Finset.mem_preimage, Multiset.mem_toFinset, Polynomial.mem_roots (hne p hp)]
  exact hpx

#print axioms ProximityGap.Genericity.exists_eval_ne_zero_of_sum_natDegree_lt
#print axioms ProximityGap.Genericity.exists_good_point_of_obstructions
#print axioms ProximityGap.Genericity.exists_eval_ne_zero_over_domain

end ProximityGap.Genericity
