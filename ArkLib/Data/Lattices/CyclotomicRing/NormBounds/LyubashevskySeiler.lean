/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.MicciancioYoung
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Lyubashevsky–Seiler: Short Elements Are Invertible

The Lyubashevsky–Seiler invertibility result [LS18, Corollary 1.2]; recalled as Lemma 3 of
the Hachi paper [NOZ26]: over the power-of-two cyclotomic modulus `φ = X^{2^α} + 1`
(`powTwoCyclotomic α`) with a prime `q ≡ 5 (mod 8)`, a nonzero element of
`Rq (powTwoCyclotomic α) = ZMod q[X]/(X^{2^α}+1)` whose centered Euclidean norm is below
`√q` is a unit.

The statement is deliberately pinned to `powTwoCyclotomic α` (`X^{2^α}+1`): LS18 Cor. 1.2
is the `k = 2` splitting case (`q ≡ 2·2+1 ≡ 5 (mod 8)`, Euclidean bound `q^{1/2} = √q`),
and that splitting / minimum-distance analysis is specific to the negacyclic ring. For a
general cyclotomic `Φ_m` of power-of-two *degree* (e.g. `Φ₁₅`, `Φ₁₂`) the `q ≡ 5 (mod 8)`
condition and the `√q` bound are simply wrong, so phrasing the lemma for an arbitrary
`Φ` with `deg φ = 2^α` would be unsound.

This is one of the two key lemmas for the Greyhound [NS24] / Hachi [NOZ26] weak-binding argument.
The proof is a genuine piece of algebraic number theory, carried out here in full:

* For `α ≥ 1` the modulus splits as `X^{2^α}+1 = (X^{2^{α-1}} − r)(X^{2^{α-1}} + r) (mod q)`, where
  `r² = −1` (`exists_sqrt_neg_one`, from `ZMod.exists_sq_eq_neg_one_iff` since `q % 4 = 1`).
* Each conjugate factor is *irreducible* (`irreducible_X_pow_sub_C`): it divides the
  `2^{α+1}`-th cyclotomic polynomial and its degree `2^{α-1}` equals the multiplicative order of
  `q` modulo `2^{α+1}`, which for `q ≡ 5 (mod 8)` is exactly `2^{α-1}` (`orderOf_q_mod_twoPow`,
  via `ZMod.orderOf_one_add_four_mul`), so the finite-field cyclotomic-factor criterion
  (`ZMod.irreducible_of_dvd_cyclotomic_of_natDegree`) applies.
* The minimum-distance bound (`eq_zero_of_dvd_X_pow_sub_C`) is the LS18 statement that a nonzero
  element of the ideal `(X^{2^{α-1}} − s)` has `ℓ₂` norm `≥ √q`: writing `m = 2^{α-1}`, if such a
  factor divides the lift `c̃`, comparing coefficients of `c̃ = (X^m − s)·h` gives
  `cᵢ² + c_{m+i}² ≡ 0` mod `q`, so `q` divides each (nonnegative) summand of `‖c‖₂² < q`, forcing
  every coefficient — hence `c` — to vanish.
* Thus `c̃` is coprime to each irreducible factor (`Irreducible.coprime_iff_not_dvd`), hence to
  `X^{2^α}+1`, hence `c` is a unit (`isUnit_of_isCoprime_toPoly`, through the ring isomorphism
  `Rq Φ ≃+* Polynomial (ZMod q) ⧸ (φ)`, `Rq.equivQuotient`). The `α = 0` case is the field
  `ZMod q[X]/(X+1) ≅ ZMod q`, handled directly.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

open Polynomial

namespace ArkLib.Lattices.CyclotomicModulus

/-! ## The reduced-representative ring is the cyclotomic quotient

`Rq.toQuotientHom` is injective (`toQuotient_injective`); it is also surjective, since every
quotient class has a (canonical, reduced) representative, so it is a ring isomorphism. We package
this and transfer `IsUnit` across it: invertibility in `Rq Φ` is the same as invertibility in the
semantic quotient `Polynomial R ⧸ (φ)`. -/

section Bridge

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [Nontrivial R]
  (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- `Rq.toQuotientHom` is surjective: a quotient class `[p]` is hit by the reduced representative
`Rq.mk Φ (ringEquiv.symm p)`. -/
theorem Rq.toQuotientHom_surjective : Function.Surjective (Rq.toQuotientHom Φ) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨Rq.mk Φ (CompPoly.CPolynomial.ringEquiv.symm p), ?_⟩
  change Rq.toQuotient Φ _ = _
  rw [Rq.toQuotient_mk, Φ.quotientHom_apply]
  congr 1
  exact CompPoly.CPolynomial.ringEquiv.apply_symm_apply p

/-- The ring isomorphism `Rq Φ ≃+* Polynomial R ⧸ (φ)`. -/
noncomputable def Rq.equivQuotient : Rq Φ ≃+* Φ.CyclotomicRing :=
  RingEquiv.ofBijective (Rq.toQuotientHom Φ)
    ⟨Rq.toQuotient_injective Φ, Rq.toQuotientHom_surjective Φ⟩

/-- Invertibility in `Rq Φ` matches invertibility of the image in the semantic quotient. -/
theorem Rq.isUnit_iff_isUnit_toQuotient (c : Rq Φ) :
    IsUnit c ↔ IsUnit (Φ.quotientHom c.1) := by
  have h : (Rq.equivQuotient Φ) c = Φ.quotientHom c.1 := rfl
  rw [← h, MulEquiv.isUnit_map]

/-- If the reduced lift `c̃` is coprime to the modulus `φ̃` in `R[X]`, then `c` is a unit in
`Rq Φ`: coprimality `a·φ̃ + b·c̃ = 1` maps, under `quotientHom` with `quotientHom φ̃ = 0`, to
`(mk b)·(mk c̃) = 1`. -/
theorem isUnit_of_isCoprime_toPoly {c : Rq Φ}
    (h : IsCoprime Φ.φ.toPoly c.1.toPoly) : IsUnit c := by
  rw [Rq.isUnit_iff_isUnit_toQuotient]
  obtain ⟨a, b, hab⟩ := h
  have hmk : (Ideal.Quotient.mk Φ.modIdeal b) * (Ideal.Quotient.mk Φ.modIdeal c.1.toPoly) = 1 := by
    have hcong := congrArg (Ideal.Quotient.mk Φ.modIdeal) hab
    rw [map_add, map_mul, map_mul, map_one] at hcong
    rwa [show (Ideal.Quotient.mk Φ.modIdeal Φ.φ.toPoly) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
      mul_zero, zero_add] at hcong
  rw [Φ.quotientHom_apply]
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hmk)

end Bridge

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

omit [NeZero q] in
/-- The squared `ℓ₂` norm is bounded by the square of the `ℓ₁` norm: `Σ aᵢ² ≤ (Σ aᵢ)²`. -/
theorem Rq.l2NormSq_le_l1Norm_sq (Φ' : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ']
    (c : Rq Φ') : Rq.l2NormSq Φ' c ≤ (Rq.l1Norm Φ' c) ^ 2 :=
  Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => Nat.zero_le _)

variable (α : ℕ)

/-- The power-of-two ("Hachi") cyclotomic modulus `X^{2^α}+1` over `ZMod q`. -/
local notation "Φ" => (powTwoCyclotomic (R := ZMod q) α)

/-! ## Number-theoretic input: the multiplicative order of `q` mod `2^{α+1}`

For `q ≡ 5 (mod 8)` the residue `q` is `1 + 4·(odd)` modulo `2^{α+1}`, so its multiplicative
order in `(ℤ/2^{α+1})ˣ` is exactly `2^{α-1}` (`q` generates the full `⟨5⟩` cyclic part). Combined
with the degree of the irreducible factors of `cyclotomic (2^{α+1})` over the finite field
`ZMod q` (which is that multiplicative order, `natDegree_of_dvd_cyclotomic_of_irreducible`), this
forces the splitting `X^{2^α}+1 = (X^{2^{α-1}} − r)(X^{2^{α-1}} + r)` into two *irreducible*
degree-`2^{α-1}` factors. -/

omit [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- For `q ≡ 5 (mod 8)` and `α ≥ 1`, the multiplicative order of `q` modulo `2^{α+1}` is
`2^{α-1}`. This is the classical fact that an integer `≡ 5 (mod 8)` generates the `⟨5⟩` cyclic
part of `(ℤ/2^{α+1})ˣ`. -/
theorem orderOf_q_mod_twoPow (hq5 : q % 8 = 5) {β : ℕ} :
    orderOf ((q : ZMod (2 ^ (β + 2)))) = 2 ^ β := by
  -- Write `q = 1 + 4·a` with `a` odd, coming from `q ≡ 5 (mod 8)`.
  -- From `q ≡ 5 (mod 8)` get `q = 8·s + 5` over ℤ, so `q - 1 = 4·(2s+1)` with `2s+1` odd.
  obtain ⟨s, hs⟩ : ∃ s : ℕ, q = 8 * s + 5 := ⟨q / 8, by omega⟩
  set a : ℤ := 2 * (s : ℤ) + 1 with ha
  have hq1 : (q : ℤ) - 1 = 4 * a := by rw [ha, hs]; push_cast; ring
  have haodd : Odd a := ⟨(s : ℤ), by rw [ha]⟩
  have hq : ((q : ZMod (2 ^ (β + 2)))) = 1 + 4 * (a : ZMod (2 ^ (β + 2))) := by
    have hzint : (q : ℤ) = 1 + 4 * a := by linarith [hq1]
    have : ((q : ℤ) : ZMod (2 ^ (β + 2))) = ((1 + 4 * a : ℤ) : ZMod (2 ^ (β + 2))) := by
      rw [hzint]
    rw [Int.cast_natCast] at this
    rw [this]; push_cast; ring
  rw [hq, ZMod.orderOf_one_add_four_mul a haodd β]

/-! ## The splitting `X^{2^α}+1 = (X^{2^{α-1}} − r)(X^{2^{α-1}} + r)` into irreducible factors -/

omit [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- For `q ≡ 5 (mod 8)`, `−1` is a square modulo `q` (since `q % 4 = 1 ≠ 3`); pick a square root
`r` with `r² = −1`. -/
theorem exists_sqrt_neg_one (hq5 : q % 8 = 5) : ∃ r : ZMod q, r ^ 2 = -1 := by
  have hp : (q : ℕ) % 4 ≠ 3 := by omega
  obtain ⟨r, hr⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := q)).mpr hp
  exact ⟨r, by rw [sq, ← hr]⟩

/-- `q` does not divide `2^{α+1}` (it is an odd prime). -/
theorem q_not_dvd_twoPow (hq5 : q % 8 = 5) : ¬ q ∣ 2 ^ (α + 1) := by
  intro hdvd
  have hq : q ∣ 2 := (Nat.Prime.dvd_of_dvd_pow (Fact.out (p := Nat.Prime q)) hdvd)
  have hq2 : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq
  omega

/-- The negacyclic modulus splits as a product of the two conjugate binomials:
`X^{2^{β+1}} + 1 = (X^{2^β} − r)(X^{2^β} + r)` when `r² = −1`. -/
theorem X_pow_add_one_eq_mul {r : ZMod q} (hr : r ^ 2 = -1) (β : ℕ) :
    (Polynomial.X : (ZMod q)[X]) ^ (2 ^ (β + 1)) + 1
      = (Polynomial.X ^ (2 ^ β) - Polynomial.C r) * (Polynomial.X ^ (2 ^ β) + Polynomial.C r) := by
  have hpow : (Polynomial.X : (ZMod q)[X]) ^ (2 ^ (β + 1))
      = (Polynomial.X ^ (2 ^ β)) ^ 2 := by
    rw [← pow_mul, pow_succ]
  have hCr : (Polynomial.C r) ^ 2 = Polynomial.C (r ^ 2) := by rw [← Polynomial.C_pow]
  rw [hpow]
  have hfac : (Polynomial.X ^ (2 ^ β) - Polynomial.C r) * (Polynomial.X ^ (2 ^ β) + Polynomial.C r)
      = (Polynomial.X ^ (2 ^ β)) ^ 2 - (Polynomial.C r) ^ 2 := by ring
  rw [hfac, hCr, hr, Polynomial.C_neg, Polynomial.C_1, sub_neg_eq_add]

/-- Each conjugate factor `X^{2^β} − r` (and its sign-flip via `r ↦ −r`) is irreducible over
`ZMod q` for `q ≡ 5 (mod 8)`: it divides `cyclotomic (2^{β+2})` and its degree `2^β` equals the
multiplicative order of `q` modulo `2^{β+2}` (`orderOf_q_mod_twoPow`), so the
finite-field cyclotomic-factor criterion forces irreducibility. -/
theorem irreducible_X_pow_sub_C (hq5 : q % 8 = 5) {r : ZMod q} (hr : r ^ 2 = -1) (β : ℕ) :
    Irreducible ((Polynomial.X : (ZMod q)[X]) ^ (2 ^ β) - Polynomial.C r) := by
  -- The modulus is the `2^{β+2}`-th cyclotomic polynomial.
  have hcyc : (Polynomial.X : (ZMod q)[X]) ^ (2 ^ (β + 1)) + 1
      = Polynomial.cyclotomic (2 ^ (β + 2)) (ZMod q) := by
    have := (powTwoCyclotomic_isCyclotomic (R := ZMod q) (β + 1)).isCyclotomic
    rw [powTwo_toPoly (α := β + 1)] at this
    simpa using this
  -- The factor divides the cyclotomic polynomial.
  have hdvd : ((Polynomial.X : (ZMod q)[X]) ^ (2 ^ β) - Polynomial.C r)
      ∣ Polynomial.cyclotomic (2 ^ (β + 2)) (ZMod q) := by
    rw [← hcyc, X_pow_add_one_eq_mul hr β]
    exact Dvd.intro _ rfl
  -- The factor has degree `2^β`.
  have hdeg : ((Polynomial.X : (ZMod q)[X]) ^ (2 ^ β) - Polynomial.C r).natDegree = 2 ^ β := by
    rw [Polynomial.natDegree_X_pow_sub_C]
  -- That degree equals the multiplicative order of `q` modulo `2^{β+2}`.
  have hqn : ¬ q ∣ 2 ^ (β + 2) := q_not_dvd_twoPow (β + 1) hq5
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree hqn hdvd
  rw [hdeg, show orderOf (ZMod.unitOfCoprime q
      ((Fact.out (p := Nat.Prime q)).coprime_iff_not_dvd.mpr hqn))
      = orderOf ((q : ZMod (2 ^ (β + 2)))) from by
    rw [← ZMod.coe_unitOfCoprime q
      ((Fact.out (p := Nat.Prime q)).coprime_iff_not_dvd.mpr hqn), orderOf_units]]
  rw [orderOf_q_mod_twoPow hq5]

/-! ## The minimum-distance / norm argument

If a conjugate factor `X^m − s` (with `s² = −1`, `m = 2^β`) divides the reduced lift `c̃` of a ring
element `c` of degree `< 2m`, then comparing coefficients of `c̃ = (X^m − s)·h` gives
`c_i = −s·c_{m+i}` for `i < m`, hence `c_i² + c_{m+i}² = 0` in `ZMod q`. Over the centered integer
representatives this says `q ∣ |c_i|² + |c_{m+i}|²`; summing over `i < m` is exactly the squared
`ℓ₂` norm `‖c‖₂² < q`, so every term — being a nonnegative multiple of `q` bounded by a value
`< q` — vanishes. Thus all coefficients of `c̃` are zero, i.e. `c = 0`. This is the concrete
incarnation of the LS18 ideal-lattice minimum-distance bound `√(det) = √q`. -/

/-- Coefficient relation from divisibility by a conjugate factor: if `X^m − C s` divides a
polynomial `f` of degree `< 2m`, then `f.coeff i = − s · f.coeff (m + i)` for every `i < m`. -/
theorem coeff_of_dvd_X_pow_sub_C {S : Type*} [CommRing S] [Nontrivial S] {m : ℕ} (hm : 0 < m)
    {s : S} {f : S[X]} (hf : f.natDegree < 2 * m)
    (hdvd : ((Polynomial.X : S[X]) ^ m - Polynomial.C s) ∣ f) {i : ℕ} (hi : i < m) :
    f.coeff i = - (s * f.coeff (m + i)) := by
  rcases eq_or_ne f 0 with hf0 | hfne
  · subst hf0; simp
  obtain ⟨h, hfh⟩ := hdvd
  -- `deg (X^m - C s) = m`, so `deg h < m` from `deg f < 2m`.
  have hmon : ((Polynomial.X : S[X]) ^ m - Polynomial.C s).Monic := by
    apply Polynomial.monic_X_pow_sub
    exact lt_of_le_of_lt (Polynomial.degree_C_le) (by exact_mod_cast hm)
  have hgnd : ((Polynomial.X : S[X]) ^ m - Polynomial.C s).natDegree = m :=
    Polynomial.natDegree_X_pow_sub_C
  have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hfh; exact hfne hfh
  have hhnd : h.natDegree < m := by
    have hfnd : f.natDegree = m + h.natDegree := by
      rw [hfh, hmon.natDegree_mul' hh0, hgnd]
    omega
  -- `f = X^m * h - C s * h`; read off coefficients.
  have hexp : f = (Polynomial.X : S[X]) ^ m * h - Polynomial.C s * h := by
    rw [hfh]; ring
  -- `f.coeff i = -(s * h.coeff i)` for `i < m`.
  have hci : f.coeff i = - (s * h.coeff i) := by
    rw [hexp, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul', if_neg (by omega),
      Polynomial.coeff_C_mul, zero_sub]
  -- `f.coeff (m+i) = h.coeff i` for `i < m`.
  have hcmi : f.coeff (m + i) = h.coeff i := by
    rw [hexp, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul', if_pos (by omega),
      Polynomial.coeff_C_mul]
    have : h.coeff (m + i) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [show m + i - m = i from by omega, this, mul_zero, sub_zero]
  rw [hci, hcmi]

/-- **Minimum-distance bound.** If a conjugate factor `X^{2^β} − s` (`s² = −1`) divides the reduced
lift of a ring element `c : Rq (powTwoCyclotomic (β+1))` whose squared `ℓ₂` norm is `< q`, then
`c = 0`. This is the LS18 statement that the nonzero elements of the ideal `(X^{2^β} − s)` have
`ℓ₂` norm `≥ √q`. -/
theorem eq_zero_of_dvd_X_pow_sub_C {β : ℕ} {s : ZMod q} (hs : s ^ 2 = -1)
    {c : Rq (powTwoCyclotomic (R := ZMod q) (β + 1))}
    (hnorm : Rq.l2NormSq (powTwoCyclotomic (R := ZMod q) (β + 1)) c < q)
    (hdvd : ((Polynomial.X : (ZMod q)[X]) ^ (2 ^ β) - Polynomial.C s) ∣ c.1.toPoly) :
    c = 0 := by
  have hmpos : 0 < 2 ^ β := by positivity
  have hsplitnat : (2 : ℕ) ^ (β + 1) = 2 ^ β + 2 ^ β := by rw [pow_succ]; ring
  have hdeg2m : c.1.toPoly.natDegree < 2 * 2 ^ β := by
    have := natDegree_toPoly_lt (α := β + 1) c
    rw [show (2 : ℕ) ^ (β + 1) = 2 * 2 ^ β from by rw [pow_succ]; ring] at this
    exact this
  -- Abbreviations for the per-index centered absolute values.
  let A : ℕ → ℕ := fun i => (c.1.coeff i).valMinAbs.natAbs
  let B : ℕ → ℕ := fun i => (c.1.coeff (2 ^ β + i)).valMinAbs.natAbs
  -- `(natAbs (valMinAbs x))² ≡ x² (mod q)`.
  have hsqcast : ∀ x : ZMod q, ((x.valMinAbs.natAbs : ZMod q)) ^ 2 = x ^ 2 := fun x => by
    have h1 : ((x.valMinAbs.natAbs : ZMod q)) ^ 2 = ((x.valMinAbs : ℤ) : ZMod q) ^ 2 := by
      rw [← Int.cast_natCast, ← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]
    rw [h1, ZMod.coe_valMinAbs]
  -- `q ∣ A i ^ 2 + B i ^ 2` for `i < 2^β`.
  have hdvdsum : ∀ i, i < 2 ^ β → q ∣ A i ^ 2 + B i ^ 2 := by
    intro i hi
    have hcoeff := coeff_of_dvd_X_pow_sub_C (s := s) hmpos hdeg2m hdvd hi
    rw [← CompPoly.CPolynomial.coeff_toPoly, ← CompPoly.CPolynomial.coeff_toPoly] at hcoeff
    have hzero : (c.1.coeff i) ^ 2 + (c.1.coeff (2 ^ β + i)) ^ 2 = 0 := by
      rw [hcoeff]
      have : (-(s * c.1.coeff (2 ^ β + i))) ^ 2 = s ^ 2 * (c.1.coeff (2 ^ β + i)) ^ 2 := by ring
      rw [this, hs]; ring
    have hcast : ((A i ^ 2 + B i ^ 2 : ℕ) : ZMod q) = 0 := by
      change (((c.1.coeff i).valMinAbs.natAbs ^ 2
          + (c.1.coeff (2 ^ β + i)).valMinAbs.natAbs ^ 2 : ℕ) : ZMod q) = 0
      push_cast
      rw [show (((c.1.coeff i).valMinAbs.natAbs : ZMod q)) ^ 2 = (c.1.coeff i) ^ 2 from
          hsqcast _,
        show (((c.1.coeff (2 ^ β + i)).valMinAbs.natAbs : ZMod q)) ^ 2
          = (c.1.coeff (2 ^ β + i)) ^ 2 from hsqcast _, hzero]
    rwa [ZMod.natCast_eq_zero_iff] at hcast
  -- The squared `ℓ₂` norm splits as `Σ_{i<2^β} (A i ^ 2 + B i ^ 2)`.
  have hsplit : Rq.l2NormSq (powTwoCyclotomic (R := ZMod q) (β + 1)) c
      = ∑ i ∈ Finset.range (2 ^ β), (A i ^ 2 + B i ^ 2) := by
    rw [Rq.l2NormSq, powTwo_natDegree (α := β + 1), hsplitnat]
    rw [Finset.sum_range_add (fun k => (c.1.coeff k).valMinAbs.natAbs ^ 2) (2 ^ β) (2 ^ β),
      ← Finset.sum_add_distrib]
  -- Each term is `0`, so all coefficients vanish.
  have hterm0 : ∀ i, i < 2 ^ β → A i = 0 ∧ B i = 0 := by
    intro i hi
    have hle : A i ^ 2 + B i ^ 2
        ≤ Rq.l2NormSq (powTwoCyclotomic (R := ZMod q) (β + 1)) c := by
      rw [hsplit]
      exact Finset.single_le_sum (f := fun i => A i ^ 2 + B i ^ 2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
    have hlt : A i ^ 2 + B i ^ 2 < q := lt_of_le_of_lt hle hnorm
    have heq0 : A i ^ 2 + B i ^ 2 = 0 := by
      rcases (hdvdsum i hi) with ⟨t, ht⟩
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · rw [ht, ht0, mul_zero]
      · exfalso; rw [ht] at hlt; nlinarith [htpos]
    exact ⟨by nlinarith [heq0, Nat.zero_le (B i)], by nlinarith [heq0, Nat.zero_le (A i)]⟩
  -- Conclude `c = 0`.
  apply Subtype.ext
  rw [Rq.zero_val]
  apply toPoly_injective
  rw [CompPoly.CPolynomial.toPoly_zero]
  ext k
  rw [Polynomial.coeff_zero, ← CompPoly.CPolynomial.coeff_toPoly]
  rcases lt_or_ge k (2 ^ β) with hk | hk
  · exact (ZMod.valMinAbs_eq_zero _).mp (Int.natAbs_eq_zero.mp (hterm0 k hk).1)
  · rcases lt_or_ge k (2 * 2 ^ β) with hk2 | hk2
    · obtain ⟨i, hi, rfl⟩ : ∃ i, i < 2 ^ β ∧ k = 2 ^ β + i := ⟨k - 2 ^ β, by omega, by omega⟩
      exact (ZMod.valMinAbs_eq_zero _).mp (Int.natAbs_eq_zero.mp (hterm0 i hi).2)
    · have := coeff_toPoly_eq_zero_of_le (α := β + 1) (a := c) (i := k)
        (by rw [show (2 : ℕ) ^ (β + 1) = 2 * 2 ^ β from by rw [pow_succ]; ring]; omega)
      rwa [← CompPoly.CPolynomial.coeff_toPoly] at this

/-- **Lyubashevsky–Seiler: short elements are invertible** (LS18, Cor. 1.2; Hachi, Lemma 3).
Over the power-of-two cyclotomic modulus `powTwoCyclotomic α` (`φ = X^{2^α}+1`) with a prime
`q ≡ 5 (mod 8)`, a nonzero element of `Rq (powTwoCyclotomic α)` with centered `ℓ₁` norm
`≤ κ` and `κ² < q` is a unit (then `‖c‖₂² ≤ ‖c‖₁² ≤ κ² < q`, the LS `k = 2` bound
`‖c‖ < √q`). Proved via the negacyclic splitting into irreducible conjugate factors and the
minimum-distance bound; see the module docstring for the structure. -/
theorem isUnit_of_l1Norm_le (hq5 : q % 8 = 5) {c : Rq Φ} {κ : ℕ}
    (hpos : 0 < Rq.l1Norm Φ c) (hle : Rq.l1Norm Φ c ≤ κ) (hκ : κ ^ 2 < q) :
    IsUnit c := by
  -- Reduce to coprimality of the reduced lift `c̃` with the modulus `φ̃ = X^{2^α}+1`.
  apply isUnit_of_isCoprime_toPoly
  -- The squared `ℓ₂` norm is `< q`.
  have hl2 : Rq.l2NormSq Φ c < q :=
    lt_of_le_of_lt (Rq.l2NormSq_le_l1Norm_sq Φ c)
      (lt_of_le_of_lt (Nat.pow_le_pow_left hle 2) hκ)
  -- `c ≠ 0`, since its `ℓ₁` norm is positive.
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [Rq.l1Norm] at hpos
    simp only [Rq.zero_val, CompPoly.CPolynomial.coeff_zero, ZMod.valMinAbs_zero,
      Int.natAbs_zero, Finset.sum_const_zero, lt_self_iff_false] at hpos
  -- The modulus as a Mathlib polynomial.
  have hφ : (powTwoCyclotomic (R := ZMod q) α).φ.toPoly
      = (Polynomial.X : (ZMod q)[X]) ^ (2 ^ α) + 1 := powTwo_toPoly (α := α)
  rcases Nat.eq_zero_or_pos α with hα0 | hαpos
  · -- `α = 0`: the modulus is `X + 1` (degree 1) and a nonzero `c` is a nonzero constant, a unit.
    subst hα0
    rw [hφ]
    -- `c̃` has degree `< 1`, hence is the constant `C (c̃.coeff 0)`, and it is nonzero.
    have hdeglt : c.1.toPoly.natDegree < 1 := by
      have := natDegree_toPoly_lt (α := 0) c; simpa using this
    have hc0 : c.1.toPoly ≠ 0 := by
      intro h0; apply hcne; apply Subtype.ext; rw [Rq.zero_val]
      exact toPoly_injective (by rw [h0, CompPoly.CPolynomial.toPoly_zero])
    have hcconst : c.1.toPoly = Polynomial.C (c.1.toPoly.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero (by omega)
    have hunit : IsUnit c.1.toPoly := by
      rw [hcconst]
      refine isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h0 => hc0 ?_))
      rw [hcconst, h0, map_zero]
    -- A unit is coprime to everything.
    obtain ⟨u, hu⟩ := hunit
    exact ⟨0, (↑u⁻¹ : (ZMod q)[X]), by rw [zero_mul, zero_add, ← hu]; simp [← Units.val_mul]⟩
  · -- `α = β + 1`: genuine splitting into two irreducible conjugate factors.
    obtain ⟨β, rfl⟩ : ∃ β, α = β + 1 := ⟨α - 1, by omega⟩
    obtain ⟨r, hr⟩ := exists_sqrt_neg_one (q := q) hq5
    have hrneg : (-r) ^ 2 = -1 := by rw [neg_pow]; simpa using hr
    -- Neither conjugate factor divides `c̃` (else `c = 0`).
    have hnd1 : ¬ ((Polynomial.X : (ZMod q)[X]) ^ (2 ^ β) - Polynomial.C r) ∣ c.1.toPoly := by
      intro hdvd; exact hcne (eq_zero_of_dvd_X_pow_sub_C hr hl2 hdvd)
    have hnd2 : ¬ ((Polynomial.X : (ZMod q)[X]) ^ (2 ^ β) - Polynomial.C (-r)) ∣ c.1.toPoly := by
      intro hdvd; exact hcne (eq_zero_of_dvd_X_pow_sub_C hrneg hl2 hdvd)
    -- Each factor is irreducible, hence coprime to `c̃`.
    have hcop1 : IsCoprime ((Polynomial.X : (ZMod q)[X]) ^ (2 ^ β) - Polynomial.C r) c.1.toPoly :=
      (irreducible_X_pow_sub_C hq5 hr β).coprime_iff_not_dvd.mpr hnd1
    have hcop2 :
        IsCoprime ((Polynomial.X : (ZMod q)[X]) ^ (2 ^ β) - Polynomial.C (-r)) c.1.toPoly :=
      (irreducible_X_pow_sub_C hq5 hrneg β).coprime_iff_not_dvd.mpr hnd2
    -- The product `(X^{2^β}−r)(X^{2^β}+r) = X^{2^{β+1}}+1 = φ̃` is coprime to `c̃`.
    rw [hφ, X_pow_add_one_eq_mul hr β]
    have hcop2' :
        IsCoprime ((Polynomial.X : (ZMod q)[X]) ^ (2 ^ β) + Polynomial.C r) c.1.toPoly := by
      rwa [Polynomial.C_neg, sub_neg_eq_add] at hcop2
    exact hcop1.mul_left hcop2'

end ArkLib.Lattices.CyclotomicModulus
