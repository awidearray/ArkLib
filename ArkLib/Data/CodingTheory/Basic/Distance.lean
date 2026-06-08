/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.Fin.Basic
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENat.Lattice
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Qify
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Data.Real.ENatENNReal
import CompPoly.Data.Nat.Bitwise

/-!
  # Basics of Coding Theory

  We define a general code `C` to be a subset of `n → R` for some finite index set `n` and some
  target type `R`.

  We can then specialize this notion to various settings. For `[CommSemiring R]`, we define a linear
  code to be a linear subspace of `n → R`. We also define the notion of generator matrix and
  (parity) check matrix.

  ## Naming conventions
  1. suffix `'`: **computable/instantiation** of the corresponding
  mathematical generic definitions without such suffix (e.g. `Δ₀'(u, C)` vs `Δ₀(u, C)`,
  `δᵣ'(u, C)` vs `δᵣ(u, C)`, ...)
    - **NOTE**: The generic (non-suffixed) definitions (`Δ₀`, `δᵣ`, ...) are recommended
      to be used in generic security statements, and the suffixed definitions
      (`Δ₀'`, `δᵣ'`, ...) are used for proofs or in statements of lemmas that need
      smaller value range.
    - We usually prove the equality as a bridge from the suffixed definitions into the
      non-suffixed definitions (e.g. `distFromCode'_eq_distFromCode`, ...)

  ## Type conventions

  Distance quantities span several numeric types depending on the use case:

  - Hamming distance (absolute, pairwise): `ℕ` — `hammingDist`, `Δ₀(u, v)`.
  - Min distance of a code (absolute): `ℕ` — `Code.minDist`, `‖C‖₀`.
  - Distance to a code (absolute, may be `⊤`): `ℕ∞` — `distFromCode`, `Δ₀(u, C)`.
  - Relative Hamming distance (pairwise): `ℚ≥0` — `relHammingDist`, `δᵣ(u, v)`.
  - Relative distance to a code: `ENNReal` — `relDistFromCode`, `δᵣ(u, C)`.
  - Restricted relative Hamming distance: `ℝ≥0` — `restrictedRelHammingDist`
    (ABF26 `Δ_T(f, g)`).
  - Code rate: `ℚ≥0` — `LinearCode.rate`, `ρ C`.
  - Computable variants: `ℚ≥0` — `δᵣ'`, `Δ₀'`, …

  See `docs/wiki/coding-theory-conventions.md` for the broader set of
  conventions (theorem naming, notation, ε-error types).

  Bridges between these realms are spelled out in the "Switching between different
  distance realms" subsection below (`relDistFromCode_eq_distFromCode_div`,
  `distFromCode_le_iff_relDistFromCode_le`, etc.). Downstream consumers should
  prefer the generic forms (`Δ₀`, `δᵣ`) and only switch to computable forms when
  the proof actually needs evaluation.

  ## Main Definitions
  1. Distance between two words:
    - `hammingDist u v (Δ₀(u, v))`: The Hamming distance between two words `u` and `v`
    - `relHammingDist u v (δᵣ(u, v))`: The relative Hamming distance between two words `u` and `v`
  2. Distance of code:
    - `dist C (‖"C‖₀)`: The Hamming distance of a code `C`, defined as the infimum (in `ℕ∞`) of the
      Hamming distances between any two distinct elements of `C`. This is noncomputable.
      + `minDist C`: another statement of `dist C` using equality, we have `dist_eq_minDist`
    - `dist' C (‖C‖₀')`: A computable version of `dist C`, assuming `C` is a `Fintype`.
  3. Distance from a word to a code:
    - `distFromCode u C (Δ₀(u, C))`: The hamming distance from a word `u` to a code `C`
      + `distFromCode_of_empty`: `Δ₀(u, ∅) = ⊤`
      + `distFromCode_eq_top_iff_empty`: `Δ₀(u, C) = ⊤ ↔ C = ∅`
    - `distFromCode' u C (Δ₀'(u, C))`: A computable version of `distFromCode u C`,
      assuming `C` is a `Fintype`.
      + `distFromCode'_eq_distFromCode`: `Δ₀'(u, C) = Δ₀(u, C)`
    - `relDistFromCode u C (δᵣ(u, C))`: The relative Hamming distance from a word `u` to a code `C`
      + `relDistFromCode' u C (δᵣ'(u, C))`: A computable version of `relDistFromCode u C`,
      assuming `C` is a `Fintype` and `C` is **non-empty**.
      + `relDistFromCode'_eq_relDistFromCode`: `δᵣ'(u, C) = δᵣ(u, C)`
  4. Switching between different distance realms:
    - `relDistFromCode_eq_distFromCode_div`: `δᵣ(u, C) = Δ₀(u, C) / |ι|`
    - `pairDist_eq_distFromCode_iff_eq_relDistFromCode_div`:
      `Δ₀(u, v) = Δ₀(u, C) ↔ δᵣ(u, v) = δᵣ(u, C)`
    - `relDistFromCode_le_relDist_to_mem`: `δᵣ(u, C) ≤ δᵣ(u, v)`
    - `relCloseToCode_iff_relCloseToCodeword_of_minDist`: `δᵣ(u, C) ≤ δ ↔ ∃ v ∈ C, δᵣ(u, v) ≤ δ`
    - `pairRelDist_le_iff_pairDist_le`:
      `(δᵣ(u, v) ≤ δ) ↔ (Δ₀(u, v) ≤ Nat.floor (δ * Fintype.card ι))`
    - `distFromCode_le_iff_relDistFromCode_le`:
      `Δ₀(u, C) ≤ e ↔ δᵣ(u, C) ≤ (e : ℝ≥0) / (Fintype.card ι : ℝ≥0)`
    - `relDistFromCode_le_iff_distFromCode_le`:
      `δᵣ(u, C) ≤ δ ↔ Δ₀(u, C) ≤ Nat.floor (δ * Fintype.card ι)`
    - `relCloseToWord_iff_exists_possibleDisagreeCols`
    - `relCloseToWord_iff_exists_agreementCols`
    - `relDist_floor_bound_iff_complement_bound`
    - `distFromCode_le_dist_to_mem`: `Δ₀(u, C) ≤ Δ₀(u, v), given v ∈ C`
    - `distFromCode_le_card_index_of_Nonempty`: `Δ₀(u, C) ≤ |ι|, given C is non-empty`
  5. Unique decoding radius:
    - `uniqueDecodingRadius C (UDR(C))`: The unique decoding radius of a code `C`
    - `relativeUniqueDecodingRadius C (relUDR(C))`:
      The relative unique decoding radius of a code `C`
    - `UDR_close_iff_exists_unique_close_codeword`:
      `Δ₀(u, C) ≤ UDR(C) ↔ ∃! v ∈ C, Δ₀(u, v) ≤ UDR(C)`
    - `UDRClose_iff_two_mul_proximity_lt_d_UDR`: `e ≤ UDR(C) ↔ 2 * e < ‖C‖₀`
    - `eq_of_le_uniqueDecodingRadius`
    - `UDR_close_iff_relURD_close`: `Δ₀(u, C) ≤ UDR(C) ↔ δᵣ(u, C) ≤ relUDR(C)`
    - `dist_le_UDR_iff_relDist_le_relUDR`:
      `e ≤ UDR(C) ↔ (e : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ relUDR(C)`

  We define the block length, rate, and distance of `C`. We prove simple properties of linear codes
  such as the singleton bound.

## Notes
- Implement `ENNRat (ℚ≥0∞)`, for usage in `relDistFromCode` and `relDistFromCode'`,
  as counterpart of `ENat (ℕ∞)` in `distFromCode` and `distFromCode'`.
-/


variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code
open NNReal

-- Notation for Hamming distance
notation "Δ₀(" u ", " v ")" => hammingDist u v

notation "‖" u "‖₀" => hammingNorm u

/-- The **disagreement set** of two `(ι → R)`-words: the coordinates where they differ.

Returns a `Finset ι` (requires `[Fintype ι]` and `[DecidableEq R]`).
The cardinality is the standard Hamming distance — see
`hammingDist_eq_disagreementCols_card`.

This is the canonical primitive for "coordinates where two words
disagree", used throughout the coding-theory development. Several
protocol-specific files (`Binius/BinaryBasefold/Prelude.lean`,
`Stir/Quotienting.lean`, `Whir/BlockRelDistance.lean`,
`DG25/MainResults.lean`) ship their own paper-shape `disagreementSet`
with additional structure (interleaved pairs, polynomial-evaluation
comparisons, block-fibers, etc.); those are intentional specialisations
on top of this base. Pure pointwise disagreement should use this
primitive directly.

Named `disagreementCols` rather than `disagreementSet` so that paper-
specific subtypes that `open Code` can keep their `disagreementSet`
local name without a resolution clash. -/
def disagreementCols (u v : n → R) : Finset n :=
  Finset.filter (fun i => u i ≠ v i) Finset.univ

@[simp]
lemma mem_disagreementCols {u v : n → R} {i : n} :
    i ∈ disagreementCols u v ↔ u i ≠ v i := by
  simp [disagreementCols]

/-- The Hamming distance is the cardinality of the disagreement set. -/
lemma hammingDist_eq_disagreementCols_card (u v : n → R) :
    hammingDist u v = (disagreementCols u v).card := by
  simp only [hammingDist, disagreementCols, ne_eq]

/-- The Hamming distance of a code `C` is the minimum Hamming distance between any two distinct
  elements of the code.
We formalize this as the infimum `sInf` over all `d : ℕ` such that there exist `u v : n → R` in the
code with `u ≠ v` and `hammingDist u v ≤ d`. If none exists, then we define the distance to be `0`.
-/
noncomputable def dist (C : Set (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ Δ₀( u, v ) ≤ d}

-- Note: rewrite this file using existing `(e)infsep` definitions

instance : EDist (n → R) where
  edist := fun u v => hammingDist u v

instance : Dist (n → R) where
  dist := fun u v => hammingDist u v

noncomputable def eCodeDistNew (C : Set (n → R)) : ENNReal := C.einfsep

noncomputable def codeDistNew (C : Set (n → R)) : ℝ := C.infsep

notation "‖" C "‖₀" => dist C

/-- The distance from a vector `u` to a code `C` is the minimum Hamming distance between `u`
and any element of `C`. -/
noncomputable def distFromCode (u : n → R) (C : Set (n → R)) : ℕ∞ :=
  sInf {d | ∃ v ∈ C, hammingDist u v ≤ d}

notation "Δ₀(" u ", " C ")" => distFromCode u C

/-- The distance to a code is at most the distance to any specific codeword. -/
lemma distFromCode_le_dist_to_mem (u : n → R) {C : Set (n → R)} (v : n → R) (hv : v ∈ C) :
    Δ₀(u, C) ≤ Δ₀(u, v) := by
  apply csInf_le
  · -- Show the set is bounded below
    use 0
    intro d hd
    simp only [Set.mem_setOf_eq] at hd
    rcases hd with ⟨w, _, h_dist⟩
    exact bot_le
  · -- Show hammingDist u v is in the set
    simp only [Set.mem_setOf_eq]
    exact ⟨v, hv, le_refl _⟩

/-- If `u` and `v` are distinct members of a code `C`, their distance is at least `‖C‖₀`. -/
lemma pairDist_ge_code_mindist_of_ne {C : Set (n → R)} {u v : n → R}
    (hu : u ∈ C) (hv : v ∈ C) (h_ne : u ≠ v) :
    Δ₀(u, v) ≥ ‖C‖₀:= by
  unfold Code.dist -- We use the property of sInf: if `k` is in the set `S`, then `sInf S ≤ k`.
  apply Nat.sInf_le
  simp only [Set.mem_setOf_eq]
  exists u
  constructor
  · exact hu
  · exists v

noncomputable def minDist (C : Set (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}

@[simp]
theorem dist_empty : ‖ (∅ : Set (n → R) ) ‖₀ = 0 := by simp [dist]

@[simp]
theorem dist_subsingleton {C : Set (n → R)} [Subsingleton C] : ‖C‖₀ = 0 := by
  simp only [Code.dist]
  have {d : ℕ} : (∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d) = False := by
    have h := @Subsingleton.allEq C _
    simp_all only [Set.subsingleton_coe, Subtype.forall, Subtype.mk.injEq, ne_eq, eq_iff_iff,
      iff_false, not_exists, not_and, not_le]
    intro a ha b hb hab
    have hEq : a = b := h a ha b hb
    simp_all
  have : {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d} = (∅ : Set ℕ) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    simp [this]
  simp [this]

@[simp]
theorem dist_le_card (C : Set (n → R)) : dist C ≤ Fintype.card n := by
  by_cases h : Subsingleton C
  · simp
  · simp only [Set.subsingleton_coe, Set.not_subsingleton_iff] at h
    unfold Set.Nontrivial at h
    obtain ⟨u, hu, v, hv, huv⟩ := h
    refine Nat.sInf_le ?_
    simp only [ne_eq, Set.mem_setOf_eq]
    refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨huv, hammingDist_le_card_fintype⟩⟩⟩

lemma dist_eq_minDist {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F] (C : Set (ι → F)) :
    Code.dist C = Code.minDist C := by
  -- 1. Define the sets
  let S_le : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d}
  let S_eq : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}
  -- Apply antisymmetry
  apply le_antisymm
  · -- 2. Prove dist C ≤ minDist C (i.e., sInf S_le ≤ sInf S_eq)
    -- This relies on finding an element achieving Nat.sInf S_eq
    by_cases hS_eq_nonempty : S_eq.Nonempty
    · -- Case: S_eq is non-empty
      -- Get the minimum element d_min which exists and equals sInf S_eq
      obtain ⟨d_min, hd_min_in_Seq, hd_min_is_min⟩ := Nat.sInf_mem hS_eq_nonempty
      -- hd_min_is_min : ∃ v ∈ C, d_min ≠ v ∧ Δ₀(d_min, v) = sInf S_eq
      rcases hd_min_is_min with ⟨v, hv, hne, hdist_eq_dmin⟩
      dsimp only [S_eq] at hdist_eq_dmin
      dsimp only [Code.minDist, ne_eq]
      rw [←hdist_eq_dmin] -- Replace sInf S_eq with d_min
      -- Show d_min is in S_le
      have hd_min_in_Sle : Δ₀(d_min, v) ∈ S_le := by
        use d_min, hd_min_in_Seq, v, hv, hne
      -- Since d_min is in S_le, sInf S_le must be less than or equal to it
      apply Nat.sInf_le hd_min_in_Sle
    · -- Case: S_eq is empty
      simp only [Set.not_nonempty_iff_eq_empty, S_eq] at hS_eq_nonempty
      simp only [dist, ne_eq, Code.minDist, hS_eq_nonempty]
      rw [Nat.sInf_empty]
      have hS_le_empty : S_le = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro d hd_in_Sle
        rcases hd_in_Sle with ⟨u, hu, v, hv, hne, hdist_le_d⟩
        -- If such u,v,hne existed, then d' = hammingDist u v would be in S_eq.
        have hd'_in_Seq : hammingDist u v ∈ S_eq := ⟨u, hu, v, hv, hne, rfl⟩
        simp_rw [S_eq, hS_eq_nonempty] at hd'_in_Seq
        exact hd'_in_Seq -- mem ∅
      -- sInf of empty set is 0.
      simp_rw [S_le] at hS_le_empty
      rw [hS_le_empty, Nat.sInf_empty]
  · -- 3. Prove minDist C ≤ dist C (i.e., sInf S_eq ≤ sInf S_le)
    -- Show sInf S_le is a lower bound for S_eq
    by_cases hS_le_nonempty : S_le.Nonempty
    · -- Case: S_le is non-empty
      obtain ⟨d_min, hd_min_in_Seq, hd_min_is_min⟩ := Nat.sInf_mem hS_le_nonempty
      -- hd_min_is_min : ∃ v ∈ C, d_min ≠ v ∧ Δ₀(d_min, v) = sInf S_le
      rcases hd_min_is_min with ⟨v, hv, hne, hdist_le_dmin⟩
      dsimp only [S_le] at hdist_le_dmin
      dsimp only [dist]
      have h :  minDist C ≤ Δ₀(d_min, v) := by
        apply Nat.sInf_le
        use d_min, hd_min_in_Seq, v, hv, hne
      omega
    · -- Case: S_le is empty
      -- If S_le is empty, sInf S_le = 0
      -- ⊢ minDist C ≤ ‖C‖₀
      simp only [Set.nonempty_iff_ne_empty, ne_eq, not_not, S_le] at hS_le_nonempty
      rw [dist, hS_le_nonempty, Nat.sInf_empty]
      -- Goal: ⊢ minDist C ≤ 0
      -- Since minDist C is a Nat, this implies minDist C = 0
      rw [Nat.le_zero]
      -- Goal: ⊢ minDist C = 0
      rw [minDist]
      -- Goal: ⊢ sInf S_eq = 0
      have hS_eq_empty : S_eq = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr -- Prove by showing no element d is in S_eq
        intro d hd_in_Seq -- Assume d ∈ S_eq
        -- Unpack the definition of S_eq
        rcases hd_in_Seq with ⟨u, hu, v, hv, hne, hdist_eq_d⟩
        -- If such u, v, hne exist, then d = Δ₀(u, v) must be in S_le
        -- because Δ₀(u, v) ≤ d (as they are equal)
        have hd_in_Sle : d ∈ S_le := by
          use u, hu, v, hv, hne
          exact le_of_eq hdist_eq_d -- Use d' ≤ d where d' = Δ₀(u, v) = d
        -- But we know S_le is empty, so d cannot be in S_le
        simp_rw [S_le, hS_le_nonempty] at hd_in_Sle -- Rewrites the goal to `d ∈ ∅`
        exact hd_in_Sle -- This provides the contradiction (proof of False)
      simp_rw [S_eq] at hS_eq_empty
      rw [hS_eq_empty, Nat.sInf_empty]

/-- A non-trivial code (a code with at least two distinct codewords)
must have a minimum distance greater than 0.
-/
lemma dist_pos_of_Nontrivial {ι : Type*} [Fintype ι] {F : Type*} (C : Set (ι → F))
    [DecidableEq F] (hC : Set.Nontrivial C) : Code.dist C > 0 := by
  rw [Code.dist_eq_minDist]
  unfold Code.minDist
  let S_eq : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}
  -- 2. `hC : Set.Nontrivial C` means `∃ u ∈ C, ∃ v ∈ C, u ≠ v`
  rcases hC with ⟨u, hu, v, hv, hne⟩
  -- 3. This implies S_eq is non-empty, because the distance d' = Δ₀(u, v) is in it
  let d' := hammingDist u v
  have hd'_in_Seq : d' ∈ S_eq := ⟨u, hu, v, hv, hne, rfl⟩
  have hS_eq_nonempty : S_eq.Nonempty := ⟨d', hd'_in_Seq⟩
  -- 4. Get the minimum element d_min = sInf S_eq
  let d_min := sInf S_eq
  -- 5. By `Nat.sInf_mem_of_nonempty`, this minimum d_min is itself an element of S_eq
  have h_d_min_in_Seq : d_min ∈ S_eq := by
    exact Nat.sInf_mem hS_eq_nonempty
  -- 6. Unpack the proof that d_min ∈ S_eq
  --    This gives us a pair (u', v') that *achieves* this minimum distance
  rcases h_d_min_in_Seq with ⟨u', hu', v', hv', hne', hdist_eq_dmin⟩
  -- 7. The goal is to show d_min > 0.
  -- We know d_min = hammingDist u' v' from hdist_eq_dmin
  dsimp only [d_min, S_eq] at hdist_eq_dmin
  rw [←hdist_eq_dmin]
  exact hammingDist_pos.mpr hne'

lemma exists_closest_codeword_of_Nonempty_Code {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) [Nonempty C] (u : ι → F) : ∃ M ∈ C, Δ₀(u, M) = Δ₀(u, C) := by
  set S := (fun (x : C) => Δ₀(u, x)) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  -- Use the fact that we can find a minimum element in S
  let SENat := (fun (g : C) => (Δ₀(u, g) : ENat)) '' Set.univ
    -- let S_nat := (fun (g : C_i) => hammingDist f g) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  have h_coe_sinfS_eq_sinfSENat : ↑(sInf S) = sInf SENat := by
    rw [ENat.coe_sInf (hs := hS_nonempty)]
    simp only [SENat, Set.image_univ, sInf_range]
    simp only [S, Set.image_univ, iInf_range]
  rcases Nat.sInf_mem hS_nonempty with ⟨g_subtype, hg_subtype, hg_min⟩
  rcases g_subtype with ⟨M_closest, hg_mem⟩
  -- The distance `d` is exactly the Hamming distance of `U` to `M_closest` (lifted to `ℕ∞`).
  have h_dist_eq_hamming : Δ₀(u, C) = (hammingDist u M_closest) := by
    -- We found `M_closest` by taking the `sInf` of all distances, and `hg_min`
    -- shows that the distance to `M_closest` achieves this `sInf`.
    have h_distFromCode_eq_sInf : Δ₀(u, C) = sInf SENat := by
      apply le_antisymm
      · -- Part 1 : `d ≤ sInf ...`
        simp only [distFromCode]
        apply sInf_le_sInf
        intro a ha
        -- `a` is in `SENat`, so `a = ↑Δ₀(f, g)` for some codeword `g`.
        rcases (Set.mem_image _ _ _).mp ha with ⟨g, _, rfl⟩
        -- We must show `a` is in the set for `d`, which is `{d' | ∃ v, ↑Δ₀(f, v) ≤ d'}`.
        -- We can use `g` itself as the witness `v`, since `↑Δ₀(f, g) ≤ ↑Δ₀(f, g)`.
        use g; simp only [Subtype.coe_prop, le_refl, and_self]
      · -- Part 2 : `sInf ... ≤ d`
        simp only [distFromCode]
        apply le_sInf
        -- Let `d'` be any element in the set that `d` is the infimum of.
        intro d' h_d'
        -- Unpack `h_d'` : there exists some `v` in the code such that
        -- `↑(hammingDist f v) ≤ d'`.
        rcases h_d' with ⟨v, hv_mem, h_dist_v_le_d'⟩
        -- By definition, `sInf SENat` is a lower bound for all elements in `SENat`.
        -- The element `↑(hammingDist f v)` is in `SENat`.
        have h_sInf_le_dist_v : sInf SENat ≤ ↑(hammingDist u v) := by
          apply sInf_le -- ⊢ ↑Δ₀(f, v) ∈ SENat
          rw [Set.mem_image]
          -- ⊢ ∃ x ∈ Set.univ, ↑Δ₀(f, ↑x) = ↑Δ₀(f, v)
          simp only [Set.mem_univ, Nat.cast_inj, true_and, Subtype.exists, exists_prop]
          -- ⊢ ∃ a ∈ C_i, Δ₀(f, a) = Δ₀(f, v)
          use v -- exact And.symm ⟨rfl, hv_mem⟩
        -- Now, chain the inequalities : `sInf SENat ≤ ↑(dist_to_any_v) ≤ d'`.
        exact h_sInf_le_dist_v.trans h_dist_v_le_d'
    rw [h_distFromCode_eq_sInf, ←h_coe_sinfS_eq_sinfSENat, ←hg_min]
  use M_closest, hg_mem, h_dist_eq_hamming.symm

noncomputable def pickClosestCodeword_of_Nonempty_Code {ι : Type*} [Fintype ι] {F : Type*}
    [DecidableEq F] (C : Set (ι → F)) [Nonempty C] (u : ι → F) : C := by
  have h_exists := exists_closest_codeword_of_Nonempty_Code C u
  let M_val := Classical.choose h_exists
  have h_M_spec := Classical.choose_spec h_exists
  exact ⟨M_val, h_M_spec.1⟩

lemma distFromPickClosestCodeword_of_Nonempty_Code {ι : Type*} [Fintype ι] {F : Type*}
    [DecidableEq F] (C : Set (ι → F)) [Nonempty C] (u : ι → F) :
    Δ₀(u, C) = Δ₀(u, pickClosestCodeword_of_Nonempty_Code C u) := by
  have h_exists := exists_closest_codeword_of_Nonempty_Code C u
  have h_M_spec := Classical.choose_spec h_exists
  -- reapply the choose spec for definitional equality
  exact h_M_spec.2.symm

theorem closeToWord_iff_exists_possibleDisagreeCols
    {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F] (u v : ι → F) (e : ℕ) :
    Δ₀(u, v) ≤ e ↔ ∃ (D : Finset ι),
      D.card ≤ e ∧ (∀ (colIdx : ι), colIdx ∉ D → u colIdx = v colIdx) := by
  constructor
  · -- Direction 1: Δ₀(u, v) ≤ e → ∃ D, ...
    intro h_dist_le_e
    -- Define D as the set of disagreeing columns
    let D : Finset ι := disagreementCols u v
    use D
    constructor
    · -- Prove D.card ≤ e
      have hD_card_eq_dist : D.card = hammingDist u v :=
        (hammingDist_eq_disagreementCols_card u v).symm
      rw [hD_card_eq_dist]
      -- Assume Δ₀(word, codeword) = hammingDist word codeword (perhaps needs coercion)
      -- Let's assume Δ₀ returns ℕ∞ and hammingDist returns ℕ for now
      apply ENat.coe_le_coe.mp -- Convert goal to ℕ ≤ ℕ
      -- Goal: ↑(hammingDist u ↑v) ≤ ↑e
      rw [Nat.cast_le (α := ENat)]
      exact h_dist_le_e
    · -- Prove agreement outside D
      intro colIdx h_colIdx_notin_D
      -- h_colIdx_notin_D means colIdx is not in the filter
      simp only [D, mem_disagreementCols, ne_eq, not_not] at h_colIdx_notin_D
      -- Therefore, u colIdx = v.val colIdx
      exact h_colIdx_notin_D
  · -- Direction 2: (∃ D, ...) → Δ₀(u, v) ≤ e
    intro h_exists_D
    rcases h_exists_D with ⟨D, hD_card_le_e, h_agree_outside_D⟩
    -- Goal: Δ₀(u, v) ≤ e

    -- Consider the set where u and v differ
    let Diff_set := disagreementCols u v
    -- Show that Diff_set is a subset of D
    have h_subset : Diff_set ⊆ D := by
      intro colIdx h_diff -- Assume colIdx is in Diff_set, i.e., u colIdx ≠ v.val colIdx
      simp only [Diff_set, mem_disagreementCols] at h_diff
      -- We need to show colIdx ∈ D
      -- Suppose colIdx ∉ D for contradiction
      by_contra h_notin_D
      -- Then by h_agree_outside_D, u colIdx = v.val colIdx
      have h_eq := h_agree_outside_D colIdx h_notin_D
      -- This contradicts h_diff
      exact h_diff h_eq
    -- Use card_le_card and the properties
    have h_card_diff_le_card_D : Diff_set.card ≤ D.card := Finset.card_le_card h_subset
    have h_dist_eq_card_diff : hammingDist u v = Diff_set.card :=
      hammingDist_eq_disagreementCols_card u v
    -- Combine the inequalities
    -- Assuming Δ₀(w, c) = ↑(hammingDist w c)
    rw [← ENat.coe_le_coe] -- Convert goal to ℕ∞ ≤ ℕ∞
    -- Goal: ↑(hammingDist u ↑v) ≤ ↑e
    apply le_trans (ENat.coe_le_coe.mpr (by rw [h_dist_eq_card_diff]))
    apply ENat.coe_le_coe.mpr
    exact Nat.le_trans h_card_diff_le_card_D hD_card_le_e

theorem closeToWord_iff_exists_agreementCols
    {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F] (u v : ι → F) (e : ℕ) :
    Δ₀(u, v) ≤ e ↔ ∃ (S : Finset ι),
      Fintype.card ι - e ≤ S.card ∧ (∀ (colIdx : ι), (colIdx ∈ S → u colIdx = v colIdx)
        ∧ (u colIdx ≠ v colIdx → colIdx ∉ S)) := by
  classical
  rw [closeToWord_iff_exists_possibleDisagreeCols]
  constructor
  · -- Direction 1: (∃ D, D.card ≤ e ∧ ∀ colIdx ∉ D, u colIdx = v colIdx) → ∃ S, ...
    intro h_exists_D
    rcases h_exists_D with ⟨D, hD_card_le_e, h_agree_outside_D⟩
    -- Define S as the complement of D (the agreeing columns)
    let S : Finset ι := Finset.filter (fun colIdx => colIdx ∉ D) Finset.univ
    use S
    constructor
    · -- Prove Fintype.card ι - e ≤ S.card
      -- S is the complement of D, so S.card = Fintype.card ι - D.card
      have hS_card_eq : S.card = Fintype.card ι - D.card := by
        -- S is the complement of D in univ
        -- Use the fact that S = univ.filter (· ∉ D) and card of complement
        have h_compl : S = Finset.univ \ D := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
          constructor
          · intro hx_S
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hx_S
            exact hx_S
          · intro hx_sdiff
            exact (Finset.mem_filter_univ x).mpr hx_sdiff
        rw [h_compl, Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
      rw [hS_card_eq]
      omega
    · -- Prove agreement inside S
      intro colIdx
      constructor
      · intro h_colIdx_in_S
        have h_colIdx_notin_D : colIdx ∉ D := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at h_colIdx_in_S
          exact h_colIdx_in_S
        exact h_agree_outside_D colIdx h_colIdx_notin_D
      · intro h_colIdx_neq_v_colIdx
        by_contra h_colIdx_in_S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at h_colIdx_in_S
        have h_eq := h_agree_outside_D colIdx h_colIdx_in_S
        exact h_colIdx_neq_v_colIdx (h_agree_outside_D colIdx h_colIdx_in_S)
  · -- Direction 2: (∃ S, ...) → (∃ D, D.card ≤ e ∧ ∀ colIdx ∉ D, u colIdx = v colIdx)
    intro h_exists_S
    rcases h_exists_S with ⟨S, hS_card_ge, h_agree_inside_S⟩
    -- Define D as the complement of S (the disagreeing columns)
    let D : Finset ι := Finset.filter (fun colIdx => colIdx ∉ S) Finset.univ
    use D
    constructor
    · -- Prove D.card ≤ e
      -- D is the complement of S, so D.card = Fintype.card ι - S.card
      have hD_card_eq : D.card = Fintype.card ι - S.card := by
        -- D is the complement of S in univ
        have h_compl : D = Finset.univ \ S := by
          ext x
          simp only [Finset.mem_univ, true_and, Finset.mem_sdiff]
          constructor
          · intro hx_D
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, D] at hx_D
            exact hx_D
          · intro hx_sdiff
            exact (Finset.mem_filter_univ x).mpr hx_sdiff
        rw [h_compl, Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
      rw [hD_card_eq]
      -- We are given: Fintype.card ι - e ≤ S.card
      -- This is equivalent to: Fintype.card ι - S.card ≤ e
      omega
    · -- Prove agreement outside D
      intro colIdx h_colIdx_notin_D
      -- colIdx ∉ D means colIdx is not in filter (fun colIdx => colIdx ∉ S) univ
      -- This means either colIdx ∉ univ (impossible) or colIdx ∈ S
      -- So colIdx ∈ S
      have h_colIdx_in_S : colIdx ∈ S := by
        by_contra h_notin_S
        have h_in_D : colIdx ∈ D := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Decidable.not_not,
            D] at h_colIdx_notin_D
          exact False.elim (h_notin_S h_colIdx_notin_D)
        exact h_colIdx_notin_D h_in_D
      -- By h_agree_inside_S, if colIdx ∈ S, then u colIdx = v colIdx
      exact (h_agree_inside_S colIdx).1 h_colIdx_in_S

/-- If `u` and `v` are two codewords of `C` with distance less than `dist C`,
then they are the same. -/
theorem eq_of_lt_dist {C : Set (n → R)} {u v : n → R} (hu : u ∈ C) (hv : v ∈ C)
    (huv : Δ₀(u, v) < ‖C‖₀) : u = v := by
  simp only [dist] at huv
  by_contra hNe
  push Not at hNe
  revert huv
  simp only [ne_eq, imp_false, not_lt]
  refine Nat.sInf_le ?_
  simp only [Set.mem_setOf_eq]
  refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨hNe, le_rfl⟩⟩⟩

@[simp]
theorem distFromCode_of_empty (u : n → R) : Δ₀(u, (∅ : Set (n → R))) = ⊤ := by
  simp [distFromCode]

theorem distFromCode_eq_top_iff_empty (u : n → R) (C : Set (n → R)) : Δ₀(u, C) = ⊤ ↔ C = ∅ := by
  apply Iff.intro
  · simp only [distFromCode]
    intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    apply sInf_eq_top.mp at h
    revert h
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp, imp_false, not_forall]
    refine ⟨Fintype.card n, v, hv, ?_, ?_⟩
    · norm_num; exact hammingDist_le_card_fintype
    · norm_num
  · intro h; subst h; simp

lemma distFromCode_le_card_index_of_Nonempty (u : n → R) {C : Set (n → R)} [Nonempty C] :
    Δ₀(u, C) ≤ Fintype.card n := by
  -- exact an element from C since C is nonempty
  letI h_nonempty : Set.Nonempty C := by (expose_names; exact Set.nonempty_coe_sort.mp inst_2)
  let v : n → R := Classical.choose h_nonempty
  have hv : v ∈ C := Classical.choose_spec h_nonempty
  have h_dist_u_C_le_dist_u_v : Δ₀(u, C) ≤ Δ₀(u, v) := by
    apply distFromCode_le_dist_to_mem u v hv
  have h_dist_u_v_le_card_index : Δ₀(u, v) ≤ Fintype.card n := by
    exact hammingDist_le_card_fintype
  have h_dist_u_C_ne_top : Δ₀(u, C) ≠ ⊤ := by
    by_contra h_dist_u_C_eq_top
    rw [distFromCode_eq_top_iff_empty (n := n) (u := u) (C := C)] at h_dist_u_C_eq_top
    have h_C_ne_empty: C ≠ ∅ := by (expose_names; exact Set.nonempty_iff_ne_empty'.mp inst_2)
    exact h_C_ne_empty h_dist_u_C_eq_top
  lift Δ₀(u, C) to ℕ using h_dist_u_C_ne_top with d
  norm_cast at ⊢ h_dist_u_C_le_dist_u_v
  exact Nat.le_trans h_dist_u_C_le_dist_u_v h_dist_u_v_le_card_index

@[simp]
theorem distFromCode_of_mem (C : Set (n → R)) {u : n → R} (h : u ∈ C) : Δ₀(u, C) = 0 := by
  simp only [distFromCode]
  apply ENat.sInf_eq_zero.mpr
  simp [h]

theorem distFromCode_eq_zero_iff_mem (C : Set (n → R)) (u : n → R) : Δ₀(u, C) = 0 ↔ u ∈ C := by
  apply Iff.intro
  · simp only [distFromCode]
    intro h
    apply ENat.sInf_eq_zero.mp at h
    revert h
    simp
  · intro h; exact distFromCode_of_mem C h

theorem distFromCode_eq_of_lt_half_dist (C : Set (n → R)) (u : n → R) {v w : n → R}
    (hv : v ∈ C) (hw : w ∈ C) (huv : Δ₀(u, v) < ‖C‖₀ / 2) (hvw : Δ₀(u, w) < ‖C‖₀ / 2) : v = w := by
  apply eq_of_lt_dist hv hw
  calc
    Δ₀(v, w) ≤ Δ₀(v, u) + Δ₀(u, w) := by exact hammingDist_triangle v u w
    _ = Δ₀(u, v) + Δ₀(u, w) := by simp only [hammingDist_comm]
    _ < ‖C‖₀ / 2 + ‖C‖₀ / 2 := by omega
    _ ≤ ‖C‖₀ := by omega

lemma closeToCode_iff_closeToCodeword_of_minDist {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    {C : Set (ι → F)} (u : ι → F) (e : ℕ) : Δ₀(u, C) ≤ e ↔ ∃ v ∈ C, Δ₀(u, v) ≤ e := by
  constructor
  · -- Direction 1: (→)
    -- Assume: Δ₀(u, C) ≤ ↑e
    -- Goal: ∃ v ∈ C, Δ₀(u, v) ≤ e
    intro h_dist_le_e
    -- We need to handle two cases: the code C being empty or non-empty.
    by_cases hC_empty : C = ∅
    · -- Case 1: C is empty
      -- The goal is `∃ v ∈ ∅, ...`, which is `False`.
      -- We must show the assumption `h_dist_le_e` is also `False`.
      rw [hC_empty] at h_dist_le_e
      rw [distFromCode_of_empty] at h_dist_le_e
      -- h_dist_le_e is now `⊤ ≤ ↑e`.
      -- Since `e : ℕ`, `↑e` is finite (i.e., `↑e ≠ ⊤`).
      have h_e_ne_top : (e : ℕ∞) ≠ ⊤ := ENat.coe_ne_top e
      -- `⊤ ≤ ↑e` is only true if `↑e = ⊤`, so this is a contradiction.
      simp only [top_le_iff, ENat.coe_ne_top] at h_dist_le_e
    · -- Case 2: C is non-empty
      have hC_nonempty : Set.Nonempty C := Set.nonempty_iff_ne_empty.mpr hC_empty
      have hC_nonempty_instance : Nonempty C := Set.Nonempty.to_subtype hC_nonempty
      let v := pickClosestCodeword_of_Nonempty_Code C u
      use v; constructor
      · simp only [Subtype.coe_prop]
      · rw [distFromPickClosestCodeword_of_Nonempty_Code] at h_dist_le_e
        rw [ENat.coe_le_coe] at h_dist_le_e
        exact h_dist_le_e
  · -- Direction 2: (←)
    -- Assume: `∃ v ∈ C, Δ₀(u, v) ≤ e`
    -- Goal: `Δ₀(u, C) ≤ ↑e`
    intro h_exists
    -- Unpack the assumption
    rcases h_exists with ⟨v, hv_mem, h_dist_le_e⟩
    -- Goal is `sInf {d | ∃ w ∈ C, ↑(Δ₀(u, w)) ≤ d} ≤ ↑e`
    -- We can use the lemma `ENat.sInf_le` (or `sInf_le` for complete linear orders)
    -- which says `sInf S ≤ x` if `x ∈ S`.
    have h_sInf_le: Δ₀(u, C) ≤ Δ₀(u, v) := by
      apply sInf_le
      simp only [Set.mem_setOf_eq, Nat.cast_le]
      use v
    calc Δ₀(u, C) ≤ Δ₀(u, v) := h_sInf_le
    _ ≤ e := by exact ENat.coe_le_coe.mpr h_dist_le_e

section Computable

/-- Computable version of the Hamming distance of a code `C`, assuming `C` is a `Fintype`.

The return type is `ℕ∞` since we use `Finset.min`. -/
def dist' (C : Set (n → R)) [Fintype C] : ℕ∞ :=
  Finset.min <| ((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2)).image
    (fun ⟨u, v⟩ => hammingDist u.1 v.1)

notation "‖" C "‖₀'" => dist' C

variable {C : Set (n → R)} [Fintype C]

@[simp]
theorem dist'_empty : ‖(∅ : Set (n → R))‖₀' = ⊤ := rfl

@[simp]
theorem codeDist'_subsingleton [Subsingleton C] : ‖C‖₀' = ⊤ := by
  simp only [dist', ne_eq]
  apply Finset.min_eq_top.mpr
  simp only [Finset.image_eq_empty, Finset.filter_eq_empty_iff, Finset.mem_univ,
    Decidable.not_not, forall_const, Prod.forall, Subtype.forall, Subtype.mk.injEq]
  have h := @Subsingleton.elim C _
  simp_all only [Set.subsingleton_coe, Subtype.forall, Subtype.mk.injEq]
  exact h

theorem dist'_eq_dist : ‖C‖₀'.toNat = ‖C‖₀ := by
  by_cases h : Subsingleton C
  · simp
  · -- Extract two distinct codewords u,v ∈ C
    simp only [Set.subsingleton_coe, Set.not_subsingleton_iff] at h
    unfold Set.Nontrivial at h
    obtain ⟨u, hu, v, hv, huv⟩ := h
    -- The filtered pair set is nonempty
    have hPairs_nonempty :
        (((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2))).Nonempty := by
      refine ⟨(⟨u, hu⟩, ⟨v, hv⟩), ?_⟩
      simp [huv]
    set pairs : Finset (C × C) :=
      ((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2)) with hpairs
    set vals : Finset ℕ :=
      pairs.image (fun ⟨u, v⟩ => hammingDist u.1 v.1) with hvals
    have hVals_nonempty : vals.Nonempty := by
      rcases hPairs_nonempty with ⟨p, hp⟩
      rcases p with ⟨u', v'⟩
      exact ⟨hammingDist u'.1 v'.1, Finset.mem_image.mpr ⟨(u', v'), hp, rfl⟩⟩
    -- Let d* be the minimum realized distance among distinct pairs
    set dStar : ℕ := vals.min' (by simpa [hvals] using hVals_nonempty) with hdstar
    -- Show the computable distance's toNat equals this minimum
    have h_toNat_eq_min' : ‖C‖₀'.toNat = dStar := by
      -- First, rewrite ‖C‖₀' as the minimum of `vals` in `ℕ∞`.
      have hmin_coe : ‖C‖₀' = (vals.min : ℕ∞) := by
        simp only [dist', hvals, hpairs]
      -- Next, show `(vals.min : ℕ∞) = dStar` by sandwiching with ≤.
      have hmem_min' : dStar ∈ vals := by
        simpa [hdstar] using
          (Finset.min'_mem (s := vals)
            (by simpa [hvals] using hVals_nonempty))
      -- `vals.min ≤ dStar` since `dStar ∈ vals`.
      have h_le : vals.min ≤ (dStar : ℕ∞) := by
        simpa using (Finset.min_le hmem_min')
      -- `dStar ≤ a` for all `a ∈ vals`, hence `dStar ≤ vals.min`.
      have h_ge : (dStar : ℕ∞) ≤ vals.min := by
        -- Use the universal lower-bound property of `min'`.
        refine Finset.le_min (s := vals) (m := (dStar : ℕ∞)) ?_;
        intro a ha; exact
          (show (dStar : ℕ∞) ≤ (a : ℕ∞) from by
              -- `dStar ≤ a` in `ℕ`, then coerce.
              have h' : dStar ≤ a := by
                -- `min' ≤ any element`.
                have hleast := (Finset.isLeast_min' (s := vals)
                                  (H := by simpa [hvals] using hVals_nonempty))
                exact hleast.2 ha
              simpa using h')
      -- Conclude equality in `ℕ∞` and take `toNat`.
      have : (vals.min : ℕ∞) = dStar := le_antisymm h_le h_ge
      simpa only [hmin_coe, this, hdstar]
    -- Now prove that the abstract distance equals the same minimum
    -- Define the set used in sInf
    let S : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d}
    -- First inequality: dist C ≤ dStar using a minimizing pair
    have h_le_dStar : dist C ≤ dStar := by
      -- obtain a pair (u,v) attaining the minimum distance dStar
      have hmem_min : dStar ∈ vals := by
        simpa [hdstar] using
          (Finset.min'_mem (s := vals)
            (by simpa [hvals] using hVals_nonempty))
      rcases Finset.mem_image.mp hmem_min with ⟨p, hpairs_mem, hp_eq⟩
      rcases p with ⟨u', v'⟩
      have hneq_sub : u' ≠ v' := (Finset.mem_filter.mp hpairs_mem).2
      -- Lift inequality on subtypes to inequality on values
      have hneq : (↑u' : n → R) ≠ ↑v' := by
        intro h
        apply hneq_sub
        exact Subtype.ext (by simpa using h)
      -- Show dStar ∈ S using the minimizing pair
      have hdist_le_dstar : hammingDist u'.1 v'.1 ≤ dStar := by
        simp only [hp_eq, le_refl]
      have hmemS : dStar ∈ S := by
        change ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ dStar
        exact ⟨u'.1, u'.2, v'.1, v'.2, hneq, hdist_le_dstar⟩
      -- Therefore sInf S ≤ dStar
      have := Nat.sInf_le (s := S) hmemS
      simpa [Code.dist, S] using this
    -- Second inequality: dStar ≤ dist C using lower-bound argument
    have h_dStar_le : dStar ≤ dist C := by
      -- Show dStar is a lower bound of S
      have hLB : ∀ d ∈ S, dStar ≤ d := by
        intro d hd
        rcases hd with ⟨u, hu, v, hv, hne, hle⟩
        -- The realized distance appears in vals, hence ≥ dStar
        have hmem : hammingDist u v ∈ vals := by
          -- show (⟨u,hu⟩,⟨v,hv⟩) ∈ pairs
          have hp : (⟨⟨u, hu⟩, ⟨v, hv⟩⟩ : C × C) ∈ pairs := by
            simp [hpairs, hne]
          -- then its image is in vals
          exact Finset.mem_image.mpr ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, hp, rfl⟩
        -- min' ≤ any member of vals
        have : dStar ≤ hammingDist u v := by
          -- Using the `IsLeast` property of `min'`.
          have hleast := (Finset.isLeast_min' (s := vals)
                            (H := by simpa [hvals] using hVals_nonempty))
          have := hleast.2 hmem
          simpa [hdstar] using this
        exact le_trans this hle
      -- The set S is nonempty since C is non-subsingleton
      have hS_nonempty : S.Nonempty := by
        refine ⟨hammingDist u v, ?_⟩
        exact ⟨u, hu, v, hv, huv, le_rfl⟩
      -- Greatest lower bound property on ℕ
      have := sInf.le_sInf_of_LB (S := S) hS_nonempty hLB
      simpa [Code.dist, S] using this
    -- Assemble inequalities and replace toNat of ‖C‖₀' by dStar
    have : ‖C‖₀ = dStar := le_antisymm h_le_dStar h_dStar_le
    simp [this, h_toNat_eq_min']

section

/-
- Note: We currently do not use `(E)Dist` as it forces the distance(s) into `ℝ`.
        Instead, we take some explicit notion of distance `δf`.
        Let us give this some thought.
-/

variable {α : Type*}
         {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- The set of possible distances `δf` from a vector `w` to a code `C`.
-/
def possibleDistsToCode (w : ι → F) (C : Set (ι → F)) (δf : (ι → F) → (ι → F) → α) : Set α :=
  {d : α | ∃ c ∈ C, c ≠ w ∧ δf w c = d}

lemma possibleDistsToCode_nonempty_iff
    {α : Type*} {F : Type*} {ι : Type*}
    {w : ι → F} {C : Set (ι → F)} {δf : (ι → F) → (ι → F) → α} :
    (possibleDistsToCode w C δf).Nonempty ↔ (C \ {w}).Nonempty := by
  -- 1. Unfold definitions
  unfold possibleDistsToCode
  simp only [Set.nonempty_def, Set.mem_setOf_eq]
  -- Goal: (∃ d, ∃ c ∈ C, c ≠ w ∧ δf w c = d) ↔ (∃ c, c ∈ C \ {w})

  -- 2. Unfold set difference on RHS
  simp only [Set.mem_diff, Set.mem_singleton_iff]
  -- Goal: (∃ d, ∃ c ∈ C, c ≠ w ∧ δf w c = d) ↔ (∃ c, c ∈ C ∧ c ≠ w)

  -- 3. Prove the iff
  constructor
  · -- (→) If a distance `d` exists from a `c ≠ w`, then that `c` exists.
    rintro ⟨d, c, hc_mem, hc_ne, rfl⟩
    use c, hc_mem, hc_ne
  · -- (←) If a `c ≠ w` exists in `C`, then its distance `δf w c` exists.
    rintro ⟨c, hc_mem, hc_ne⟩
    use δf w c, c, hc_mem, hc_ne

/-- The set of possible distances `δf` between distinct codewords in a code `C`.

  - Note: This allows us to express distance in non-ℝ, which is quite convenient.
          Extending to `(E)Dist` forces this into `ℝ`; give some thought.
-/
def possibleDists (C : Set (ι → F)) (δf : (ι → F) → (ι → F) → α) : Set α :=
  {d : α | ∃ p ∈ Set.offDiag C, δf p.1 p.2 = d}

/-- A generalisation of `distFromCode` for an arbitrary distance function `δf`.
-/
noncomputable def distToCode [LinearOrder α] [Zero α]
                             (w : ι → F) (C : Set (ι → F))
                             (δf : (ι → F) → (ι → F) → α)
                             (h : (possibleDistsToCode w C δf).Finite) : WithTop α :=
  haveI := @Fintype.ofFinite _ h
  (possibleDistsToCode w C δf).toFinset.min

end

lemma distToCode_of_nonempty {α : Type*} [LinearOrder α] [Zero α]
    {ι F : Type*}
                             {w : ι → F} {C : Set (ι → F)}
                             {δf : (ι → F) → (ι → F) → α}
                             (h₁ : (possibleDistsToCode w C δf).Finite)
                             (h₂ : (possibleDistsToCode w C δf).Nonempty) :
  haveI := @Fintype.ofFinite _ h₁
  distToCode w C δf h₁ = .some ((possibleDistsToCode w C δf).toFinset.min' (by simpa)) := by
  simp [distToCode, Finset.min'_eq_inf', Finset.min_eq_inf_withTop]
  rfl

/-- Computable version of the distance from a vector `u` to a finite code `C`. -/
def distFromCode' (C : Set (n → R)) [Fintype C] (u : n → R) : ℕ∞ :=
  Finset.min <| (@Finset.univ C _).image (fun v => hammingDist u v.1)

notation "Δ₀'(" u ", " C ")" => distFromCode' C u

/-- For finite nonempty codes, the computable distance equals the noncomputable distance. -/
lemma distFromCode'_eq_distFromCode (C : Set (n → R)) [Fintype C] (u : n → R) :
    Δ₀'(u, C) = Δ₀(u, C) := by
  by_cases hC_empty: C = ∅
  · subst hC_empty
    simp only [distFromCode', Finset.univ_eq_empty, Finset.image_empty, Finset.min_empty,
      distFromCode, Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false,
      _root_.sInf_empty]
    rfl
  · have hC_nonempty : Nonempty C := Set.nonempty_iff_ne_empty'.mpr hC_empty
    unfold distFromCode distFromCode'
    -- The minimum equals the infimum for finite sets
    have h_nonempty : (@Finset.univ C _).image (fun v => hammingDist u v.1) |>.Nonempty := by
      apply Finset.Nonempty.image
      exact Finset.univ_nonempty
    apply le_antisymm
    · -- Show min ≤ inf
      apply le_csInf
      · -- The inf set is nonempty
        obtain ⟨c, hc⟩ := (inferInstance : Nonempty C)
        use (hammingDist u c : ℕ∞)
        simp only [Set.mem_setOf_eq]
        exact ⟨c, hc, le_refl _⟩
      · -- min is a lower bound
        intro d hd
        simp only [Set.mem_setOf_eq] at hd
        obtain ⟨v, hv, hdist⟩ := hd
        exact le_trans (Finset.min_le (Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩))
          hdist
    · -- Show inf ≤ min
      apply csInf_le
      · -- The set is bounded below
        use 0
        intro d _
        exact bot_le
      · -- min is in the set of upper bounds
        simp only [Set.mem_setOf_eq]
        obtain ⟨min_val, hmin⟩ := Finset.min_of_nonempty h_nonempty
        -- 1. The minimum value must belong to the set
        have h_in_set : min_val ∈ (@Finset.univ C _).image (fun v => hammingDist u v.1) :=
          Finset.mem_of_min hmin
        -- 2. Unwrap the image definition to find the specific codeword `c`
        -- "There exists a c in C such that hammingDist(u, c) = min_val"
        rw [Finset.mem_image] at h_in_set
        obtain ⟨⟨c, hc_mem⟩, -, h_dist_eq⟩ := h_in_set
        -- 3. Provide `c` as the witness for the existential goal
        refine ⟨c, hc_mem, ?_⟩
        -- 4. Prove the inequality: we know `dist(u, c) = min_val`, and `result = min_val`
        rw [h_dist_eq, hmin]
        exact le_refl _

end Computable

end Code
