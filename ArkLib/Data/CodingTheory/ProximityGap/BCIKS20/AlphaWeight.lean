/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

/-!
# (P1, A.4) `AlphaGenuineRegularWeightLe` — analysis, equivalence, structured closure, obstruction

This module imports only `HenselNumerator` (whose `.olean` builds;
`GammaGenuine`/`RationalFunctions` are transitive).  It is the careful working-out of the carved
A.4 link

  `AlphaGenuineRegularWeightLe`:  `∀ t, ∃ a_t ∈ 𝒪, embedding a_t = αGenuine t ∧ Λ_𝒪(a_t) ≤ 1`

— the formal content of BCIKS20's `Λ(α_t) = Λ(Y) = 1` ("consider the weight of `α_t`", line ~4276)
on the genuine Hensel root `gammaGenuine` (`αGenuine t := coeff t gammaGenuine`).  The statement is
verbatim the one first carved in `P1Conditional.lean` (`def AlphaGenuineRegularWeightLe`).  It now
lives here as the canonical shared A.4 infrastructure imported by the conditional P1 assembly.

## Task 1 — is `AlphaGenuineRegularWeightLe` circular with the structured invariant given `hlift`?

The (P2) lift identity lives in the FIELD `𝕃 H`:
`hlift_t :  embedding (βHensel t) = αGenuine t · W^{t+1} · ξ^{e_t}`, `e_t = 2t−1` (ℕ-truncated).
`Λ_𝒪` is the weight of the canonical `F[X][Y]`-representative of `βHensel t ∈ 𝒪 H`
(`weight_Λ_over_𝒪 = weight_Λ ∘ canonicalRepOf𝒪`) — an `𝒪`-intrinsic quantity, NOT an `𝕃`-invariant.

**Finding (`alphaWeight_iff_divWeight`, PROVEN both directions).**  GIVEN `hlift`,
`AlphaGenuineRegularWeightLe` is logically *equivalent* to the `𝒪`-level

  `DivWeightLe`:  `∀ t, ∃ a_t ∈ 𝒪,  βHensel t = a_t · W𝒪^{t+1} · ξ^{e_t}  ∧  Λ_𝒪(a_t) ≤ 1`,

i.e. `βHensel t` is *divisible in `𝒪`* by the clearing product `W𝒪^{t+1}·ξ^{e_t}`, with the quotient
of `Λ_𝒪`-weight `≤ 1`.  The forward direction is injectivity of `embedding` applied to `hlift`
(`βHensel_eq_alpha_mul_of_lift`); the reverse is pushing `embedding` through the factorization and
cancelling the nonzero denominator (`den_ne_zero`).  So the genuine A.4 content, transported to
where `Λ_𝒪` lives, is exactly this divisibility-with-weight.

**It is NOT circular with the structured invariant.**  `AlphaGenuineRegularWeightLe (⟺ DivWeightLe)`
*implies* the structured invariant `Λ_𝒪(β_t) ≤ 1 + (t+1)Λ(W) + e_t·Λ(ξ)`
(`βHensel_weight_structured`, PROVEN below: factor, then sub-multiplicative `Λ_𝒪` calculus).  The
converse FAILS: `weight_Λ_over_𝒪` is only *sub*-additive (`Λ(ab) ≤ Λ(a)+Λ(b)`,
`weight_Λ_over_𝒪_mul_le`), so a weight *upper* bound on `βHensel t` cannot be "divided through" to
manufacture either the `𝒪`-divisibility (`a_t` existing) or the *sharp* `Λ(a_t) ≤ 1` (you cannot
subtract in a sub-additive valuation).  Hence
`AlphaGenuineRegularWeightLe` is *strictly stronger* than the structured invariant — it is genuine
extra input, packaging a divisibility fact, and `P1Conditional` is NOT a hidden circularity.  The
honest residual after this file is precisely `DivWeightLe`.

## The sharp `t = 0` obstruction (`W𝒪_dvd_βHensel_zero_of_alpha`, PROVEN)

At `t = 0`, `αGenuine 0 = α₀ = T/W` (`αGenuine_zero`) and the lift identity is the PROVEN,
axiom-clean `βHensel_lift_identity_zero` (`embedding (βHensel 0) = α₀·W = T`).  Any
`AlphaGenuineRegularWeightLe`
witness `a_0` therefore forces, by injectivity,

  `βHensel 0 = a_0 · W𝒪`     in `𝒪 H`,

i.e. `W𝒪 ∣ βHensel 0` in `𝒪`.  This is the concrete face of the residual: `T/W = α₀` is regular
(`∈ image embedding`) **iff** `W𝒪 ∣ βHensel 0` (equivalently `W𝒪 ∣ mk X = functionFieldT`'s
representative).  The genuine A.4 content `Λ(α_t) = 1` is exactly that this clearing divisibility
holds at every order with the quotient at weight `1`.  We prove the `t = 0` direction
unconditionally (it uses only the proven `βHensel_lift_identity_zero` + injectivity); we do not
fake the general divisibility.

## Outcome (disposition (a) forward direction + (b) equivalence FINDING + precise obstruction)

* `βHensel_eq_alpha_mul_of_lift`, `alpha_eq_embedding_of_fact` — the two halves of the `𝕃 ↔ 𝒪`
  bridge.
* `alphaWeight_iff_divWeight` — the EQUIVALENCE `AlphaGenuineRegularWeightLe ⟺ DivWeightLe` given
  `hlift` (the circularity FINDING: the genuine content is the `𝒪`-divisibility-with-weight,
  distinct from the structured bound).
* `βHensel_weight_structured` — the STRUCTURED INVARIANT, PROVEN from
  `AlphaGenuineRegularWeightLe`+`hlift`
  (so P1 truly closes when the lift identity lands and `DivWeightLe` is supplied).
* `βHensel_weight_bound_of_alphaWeight` — (P1) loose bound `Λ_𝒪(β_t) ≤ (2t+1)·natDegreeY R·D`.
* `W𝒪_dvd_βHensel_zero_of_alpha` — the sharp, PROVEN `t = 0` divisibility obstruction.

NO `axiom`/`admit`/`native_decide`/`bv_decide`/`sorry`.  Audited in-file via `#print axioms`.
-/

set_option linter.style.longLine false
-- Cohesive #138 alpha/divisibility obstruction, structured-weight, and corrected-base APIs.
set_option linter.style.longFile 1600
set_option linter.unusedSectionVars false

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ### 0. The `W` embedding bridge

`embedding (W𝒪 H) = liftToFunctionField H.leadingCoeff` — the lift identity's `W^{t+1}` factor is
literally the embedding of `W𝒪^{t+1}`.  Pure unfolding (`W𝒪 = mk (C lc)`,
`embedding ∘ mk = liftBivariate`, `liftBivariate (C p) = liftToFunctionField p`).
-/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The embedding of the `𝒪`-element `W𝒪` is the `𝕃`-element `liftToFunctionField H.leadingCoeff`
(the `W` of the lift identity). -/
theorem embeddingOf𝒪Into𝕃_W𝒪 :
    embeddingOf𝒪Into𝕃 H (W𝒪 H) = liftToFunctionField (H := H) H.leadingCoeff := by
  rw [W𝒪, embeddingOf𝒪Into𝕃_mk, liftBivariate_C]

/-! ### 1. The carved A.4 link, re-stated verbatim (the named gap)

Identical to `P1Conditional.AlphaGenuineRegularWeightLe`: the genuine Hensel-root coefficient
`αGenuine t ∈ 𝕃 H` is *regular* (an embedding of an `𝒪`-element) of `Λ_𝒪`-weight `≤ 1`.
-/

/-- **The carved A.4 link (named gap).**  At order `t`, the genuine Hensel-root coefficient
`αGenuine t` is the embedding of an `𝒪`-element `a_t` of `Λ_𝒪`-weight `≤ 1`.  This is the formal
content of BCIKS20's `Λ(α_t) = Λ(Y) = 1`. -/
def AlphaGenuineRegularWeightLe (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∀ t : ℕ, ∃ a : 𝒪 H,
    embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

/-- The `t = 0` case of `AlphaGenuineRegularWeightLe`. -/
def AlphaGenuineRegularWeightLe_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∃ a : 𝒪 H,
    embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp 0
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

/-- The successor case of `AlphaGenuineRegularWeightLe`. -/
def AlphaGenuineRegularWeightLe_succ (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) (t : ℕ) : Prop :=
  ∃ a : 𝒪 H,
    embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp (t + 1)
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

/-- Assemble `AlphaGenuineRegularWeightLe` from its base case and successor cases. -/
theorem AlphaGenuineRegularWeightLe.of_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D := by
  intro t
  cases t
  · exact h0
  · exact hsucc _

/-- Project the base case from `AlphaGenuineRegularWeightLe`. -/
theorem AlphaGenuineRegularWeightLe.zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D :=
  hα 0

/-- Project a successor case from `AlphaGenuineRegularWeightLe`. -/
theorem AlphaGenuineRegularWeightLe.succ (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t :=
  hα (t + 1)

/-- **The `𝒪`-level divisibility-with-weight form** of the carved link.  At order `t`, `βHensel t`
factors *in `𝒪 H`* as `a_t · W𝒪^{t+1} · ξ^{e_t}` with the quotient `a_t` of `Λ_𝒪`-weight `≤ 1`.
This is `AlphaGenuineRegularWeightLe` transported to the world where `Λ_𝒪` actually lives (PROVEN
equivalent to it given `hlift`, `alphaWeight_iff_divWeight`).  It exposes the genuine residual: a
clearing
divisibility `W𝒪^{t+1}·ξ^{e_t} ∣ βHensel t` in `𝒪`, with the quotient at weight `1`. -/
def DivWeightLe (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∀ t : ℕ, ∃ a : 𝒪 H,
    βHensel H x₀ R hHyp t
        = a * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

def DivWeightLe_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∃ a : 𝒪 H, βHensel H x₀ R hHyp 0 = a * (W𝒪 H) ^ (0 + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * 0 - 1) ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

def DivWeightLe_succ (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) (t : ℕ) : Prop :=
  ∃ a : 𝒪 H, βHensel H x₀ R hHyp (t + 1) = a * (W𝒪 H) ^ (t + 1 + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * (t + 1) - 1) ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

theorem DivWeightLe_of_cases (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (h0 : DivWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) :
    DivWeightLe H x₀ R hHyp hH D := by
  intro t
  cases t
  · exact h0
  · exact hsucc _

/-- Namespace-style wrapper for assembling `DivWeightLe` from its base and successor cases. -/
theorem DivWeightLe.of_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (h0 : DivWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) :
    DivWeightLe H x₀ R hHyp hH D :=
  DivWeightLe_of_cases H x₀ R hHyp hH D h0 hsucc

/-- Project the base divisibility-with-weight case from `DivWeightLe`. -/
theorem DivWeightLe.zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    DivWeightLe_zero H x₀ R hHyp hH D :=
  hdiv 0

/-- Project a successor divisibility-with-weight case from `DivWeightLe`. -/
theorem DivWeightLe.succ (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    DivWeightLe_succ H x₀ R hHyp hH D t :=
  hdiv (t + 1)

/-- The divisibility-with-weight residual is exactly its base case plus all successor cases. -/
theorem divWeight_iff_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) :
    DivWeightLe H x₀ R hHyp hH D ↔
      DivWeightLe_zero H x₀ R hHyp hH D ∧
        ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t := by
  constructor
  · intro hdiv
    exact ⟨DivWeightLe.zero H x₀ R hHyp hH D hdiv,
      fun t => DivWeightLe.succ H x₀ R hHyp hH D hdiv t⟩
  · intro hcases
    exact DivWeightLe_of_cases H x₀ R hHyp hH D hcases.1 hcases.2

/-- The base divisibility-with-weight case, with the vacuous `ξ^0` and `W𝒪^1` factors normalized
away. This is the exact base witness target. -/
theorem divWeight_zero_iff_W𝒪_factor (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) :
    DivWeightLe_zero H x₀ R hHyp hH D ↔
      ∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 := by
  simp [DivWeightLe_zero]

/-- The successor divisibility-with-weight case with the exponents normalized from the definition's
`t + 1 + 1` and `2 * (t + 1) - 1` to `t + 2` and `2 * t + 1`. -/
theorem divWeight_succ_iff_normalized_factor (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D t : ℕ) :
    DivWeightLe_succ H x₀ R hHyp hH D t ↔
      ∃ a : 𝒪 H,
        βHensel H x₀ R hHyp (t + 1)
          = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 := by
  have hξ : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  have hW : t + 1 + 1 = t + 2 := by omega
  simp [DivWeightLe_succ, hξ, hW]

/-- The full divisibility-with-weight residual is equivalent to the normalized base target and
all normalized successor targets. -/
theorem divWeight_iff_normalized_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) :
    DivWeightLe H x₀ R hHyp hH D ↔
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 := by
  constructor
  · intro hdiv
    exact
      ⟨(divWeight_zero_iff_W𝒪_factor H x₀ R hHyp hH D).1
          (DivWeightLe.zero H x₀ R hHyp hH D hdiv),
        fun t =>
          (divWeight_succ_iff_normalized_factor H x₀ R hHyp hH D t).1
            (DivWeightLe.succ H x₀ R hHyp hH D hdiv t)⟩
  · intro hcases
    exact DivWeightLe.of_cases H x₀ R hHyp hH D
      ((divWeight_zero_iff_W𝒪_factor H x₀ R hHyp hH D).2 hcases.1)
      (fun t =>
        (divWeight_succ_iff_normalized_factor H x₀ R hHyp hH D t).2 (hcases.2 t))

/-- Assemble `DivWeightLe` directly from the normalized base and successor factor targets. -/
theorem DivWeightLe.of_normalized_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    DivWeightLe H x₀ R hHyp hH D :=
  (divWeight_iff_normalized_cases H x₀ R hHyp hH D).2 ⟨h0, hsucc⟩

/-- Project the normalized base and successor factor targets from a full `DivWeightLe` proof. -/
theorem DivWeightLe.normalized_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (divWeight_iff_normalized_cases H x₀ R hHyp hH D).1 hdiv

/-- Project the normalized base factor target from a full `DivWeightLe` proof. -/
theorem DivWeightLe.normalized_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (DivWeightLe.normalized_cases H x₀ R hHyp hH D hdiv).1

/-- Project a normalized successor factor target from a full `DivWeightLe` proof. -/
theorem DivWeightLe.normalized_succ (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D t : ℕ)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (DivWeightLe.normalized_cases H x₀ R hHyp hH D hdiv).2 t

/-! ### 1′. The two halves of the `𝕃 ↔ 𝒪` bridge

-/

/-- **Bridge, `𝕃 → 𝒪`.**  Given the (P2) lift identity at order `t` (`hlift_t`) and a carved
`𝒪`-preimage `a` of `αGenuine t` (`ha`), the `βHensel t` factors, IN `𝒪 H`, as
`βHensel t = a · W𝒪^{t+1} · ξ^{2t−1}`. -/
theorem βHensel_eq_alpha_mul_of_lift (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (t : ℕ) {a : 𝒪 H}
    (ha : embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t)
    (hlift_t :
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    βHensel H x₀ R hHyp t
      = a * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1) := by
  apply embeddingOf𝒪Into𝕃_injective hH
  rw [hlift_t]
  rw [map_mul, map_mul, map_pow, map_pow, ha, embeddingOf𝒪Into𝕃_W𝒪]

/-- **Bridge, `𝒪 → 𝕃`.**  The reverse: given the `𝒪`-level factorization `hfact` and the lift
identity `hlift_t`, the quotient `a` embeds to `αGenuine t`.  Push `embedding` through `hfact`
(`embedding (β_t) = embedding a · W^{t+1} · ξ^{e_t}`), compare with `hlift_t`, and cancel the
nonzero denominator `W^{t+1}·ξ^{e_t}` (`den_ne_zero`) in the field `𝕃 H`. -/
theorem alpha_eq_embedding_of_fact (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) {a : 𝒪 H}
    (hfact : βHensel H x₀ R hHyp t
      = a * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1))
    (hlift_t :
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t := by
  have hpush : embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = embeddingOf𝒪Into𝕃 H a
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
    rw [hfact, map_mul, map_mul, map_pow, map_pow, embeddingOf𝒪Into𝕃_W𝒪]
  rw [hlift_t, mul_assoc, mul_assoc] at hpush
  exact mul_right_cancel₀ (den_ne_zero H x₀ R hHyp t) hpush.symm

/-! ### 2. THE CIRCULARITY FINDING — `AlphaGenuineRegularWeightLe ⟺ DivWeightLe` given `hlift`

The genuine A.4 content, transported to where `Λ_𝒪` lives, is exactly the
`𝒪`-divisibility-with-weight `DivWeightLe`.  Each `t`-instance of the equivalence is the two bridge
halves, with the weight bound
carried verbatim (it is the same `a`). -/

/-- **Task 1, the FINDING.**  GIVEN the (P2) lift identity `hlift` (for all `t`),
`AlphaGenuineRegularWeightLe` and the `𝒪`-level `DivWeightLe` are *equivalent*.  This pins the
genuine residual: it is the clearing divisibility `W𝒪^{t+1}·ξ^{e_t} ∣ βHensel t` in `𝒪` with the
quotient at
weight `≤ 1` — a fact about `𝒪`-divisibility, distinct from (and strictly stronger than, see
`βHensel_weight_structured`) any `Λ_𝒪`-upper-bound on `βHensel t`. -/
theorem alphaWeight_iff_divWeight (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔ DivWeightLe H x₀ R hHyp hH D := by
  constructor
  · -- `𝕃 → 𝒪`: the carved preimage `a` factors `βHensel t`, weight unchanged.
    intro hα t
    obtain ⟨a, ha_eq, ha_wt⟩ := hα t
    exact ⟨a, βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH t ha_eq (hlift t), ha_wt⟩
  · -- `𝒪 → 𝕃`: the divisor `a` embeds to `αGenuine t`, weight unchanged.
    intro hd t
    obtain ⟨a, hfact, ha_wt⟩ := hd t
    exact ⟨a, alpha_eq_embedding_of_fact H x₀ R hHyp t hfact (hlift t), ha_wt⟩

/-- Named forward adapter from the carved regularity form to the concrete `𝒪`-divisibility form,
given the lift identity. -/
theorem DivWeightLe.of_alphaWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    DivWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight H x₀ R hHyp hH D hlift).1 hα

/-- Named reverse adapter from the concrete `𝒪`-divisibility form to carved regularity, given the
lift identity. -/
theorem AlphaGenuineRegularWeightLe.of_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight H x₀ R hHyp hH D hlift).2 hdiv

/-- The base case of carved regularity is equivalent to the base case of `𝒪`-divisibility, given
the lift identity. -/
theorem alphaWeight_zero_iff_divWeight_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D ↔
      DivWeightLe_zero H x₀ R hHyp hH D := by
  constructor
  · intro hα
    obtain ⟨a, ha_eq, ha_wt⟩ := hα
    exact ⟨a, βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH 0 ha_eq (hlift 0), ha_wt⟩
  · intro hdiv
    obtain ⟨a, hfact, ha_wt⟩ := hdiv
    exact ⟨a, alpha_eq_embedding_of_fact H x₀ R hHyp 0 hfact (hlift 0), ha_wt⟩

/-- Each successor case of carved regularity is equivalent to the corresponding successor case of
`𝒪`-divisibility, given the lift identity. -/
theorem alphaWeight_succ_iff_divWeight_succ (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (t : ℕ) :
    AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t ↔
      DivWeightLe_succ H x₀ R hHyp hH D t := by
  constructor
  · intro hα
    obtain ⟨a, ha_eq, ha_wt⟩ := hα
    exact
      ⟨a, βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH (t + 1) ha_eq (hlift (t + 1)),
        ha_wt⟩
  · intro hdiv
    obtain ⟨a, hfact, ha_wt⟩ := hdiv
    exact ⟨a, alpha_eq_embedding_of_fact H x₀ R hHyp (t + 1) hfact (hlift (t + 1)), ha_wt⟩

/-- The carved alpha-weight residual is equivalent to the divisibility base/successor cases, given
the lift identity.  This is the proof target form for grinding P1 one order family at a time. -/
theorem alphaWeight_iff_divWeight_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      DivWeightLe_zero H x₀ R hHyp hH D ∧
        ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t :=
  (alphaWeight_iff_divWeight H x₀ R hHyp hH D hlift).trans
    (divWeight_iff_cases H x₀ R hHyp hH D)

/-- Assemble carved alpha-weight regularity from proved divisibility base and successor cases, given
the lift identity. -/
theorem AlphaGenuineRegularWeightLe.of_divWeight_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : DivWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_cases H x₀ R hHyp hH D hlift).2 ⟨h0, hsucc⟩

/-- Assemble the concrete `𝒪`-divisibility form from carved alpha-weight base and successor cases,
given the lift identity. This is the dual case-wise constructor to
`AlphaGenuineRegularWeightLe.of_divWeight_cases`. -/
theorem DivWeightLe.of_alphaWeight_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    DivWeightLe H x₀ R hHyp hH D :=
  DivWeightLe.of_cases H x₀ R hHyp hH D
    ((alphaWeight_zero_iff_divWeight_zero H x₀ R hHyp hH D hlift).1 h0)
    (fun t =>
      (alphaWeight_succ_iff_divWeight_succ H x₀ R hHyp hH D hlift t).1 (hsucc t))

/-! ### 3. The STRUCTURED INVARIANT — PROVEN from `AlphaGenuineRegularWeightLe` + `hlift`

This is the genuine forward closure: the carved link + the lift identity yield the paper's
structured weight invariant, via the `𝒪`-level factorization + the proven sub-multiplicative `Λ_𝒪`
calculus.  It
shows `AlphaGenuineRegularWeightLe` is at least as strong as the structured invariant (and, by §2's
sub-additivity remark, strictly stronger). -/

/-- **(P1) the STRUCTURED INVARIANT, conditional.**  Given `hlift`, the carved link `hα`, and the
`Λ(ξ)` bound `hξ` (`weight_ξ_bound`, automatic under its regime), the structured invariant
`Λ_𝒪(βHensel l) ≤ 1 + (l+1)·Λ(W) + e_l·Λ(ξ)` holds, with `Λ(W) = (lc H).natDegree`,
`Λ(ξ) ≤ (d−1)·(D−dH+1)`, `e_l = 2l−1` (ℕ-truncated).  Route: the link gives `β_l = a_l·W𝒪^{l+1}·ξ^{e_l}`
(Task-1 `𝕃 → 𝒪`), then `weight_Λ_over_𝒪_mul_le`/`_pow_le`/`_W` + `nsmul_withBot_le` + `Λ(a_l) ≤ 1`. -/
theorem βHensel_weight_structured (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (l : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
      ≤ WithBot.some
          (1 + (l + 1) * (H.leadingCoeff).natDegree
            + (2 * l - 1)
              * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
  -- Task 1 (`𝕃 → 𝒪`): extract `a_l` and the `𝒪`-level factorization.
  obtain ⟨a, ha_eq, ha_wt⟩ := hα l
  have hfact : βHensel H x₀ R hHyp l
      = a * (W𝒪 H) ^ (l + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * l - 1) :=
    βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH l ha_eq (hlift l)
  rw [hfact]
  -- Sub-multiplicativity over `𝒪`: split the two products.
  refine (weight_Λ_over_𝒪_mul_le H hH hDH _ _).trans ?_
  refine le_trans (add_le_add (weight_Λ_over_𝒪_mul_le H hH hDH _ _) (le_refl _)) ?_
  -- (ii) `Λ_𝒪(W𝒪^{l+1}) ≤ (l+1)·Λ(W) ≤ (l+1)·(lc H).natDegree`.
  have hW_pow : weight_Λ_over_𝒪 hH ((W𝒪 H) ^ (l + 1)) D
      ≤ WithBot.some ((l + 1) * (H.leadingCoeff).natDegree) := by
    refine (weight_Λ_over_𝒪_pow_le H hH hDH (W𝒪 H) (l + 1)).trans ?_
    exact nsmul_withBot_le (l + 1) _ (weight_Λ_over_𝒪_W H hH hDH)
  -- (iii) `Λ_𝒪(ξ^{2l−1}) ≤ (2l−1)·Λ(ξ) ≤ (2l−1)·((d−1)(D−dH+1))`.
  have hξ_pow : weight_Λ_over_𝒪 hH ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * l - 1)) D
      ≤ WithBot.some
          ((2 * l - 1) * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
    refine (weight_Λ_over_𝒪_pow_le H hH hDH (ClaimA2.ξ x₀ R H hHyp) (2 * l - 1)).trans ?_
    exact nsmul_withBot_le (2 * l - 1) _ hξ
  -- Combine: `(Λ(a) + Λ(W^{l+1})) + Λ(ξ^{e_l}) ≤ (1 + (l+1)Λ(W)) + e_l·Λ(ξ)`.
  refine le_trans (add_le_add (add_le_add ha_wt hW_pow) hξ_pow) ?_
  rw [← WithBot.coe_add, ← WithBot.coe_add]

/-- **Structured invariant directly from the concrete divisibility residual.**  Once
`DivWeightLe` is supplied, the `𝒪`-level factorization is already available, so the structured
weight bound no longer needs the field-level lift identity or the carved alpha regularity transport.
-/
theorem βHensel_weight_structured_of_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdiv : DivWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (l : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
      ≤ WithBot.some
          (1 + (l + 1) * (H.leadingCoeff).natDegree
            + (2 * l - 1)
              * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
  obtain ⟨a, hfact, ha_wt⟩ := hdiv l
  rw [hfact]
  refine (weight_Λ_over_𝒪_mul_le H hH hDH _ _).trans ?_
  refine le_trans (add_le_add (weight_Λ_over_𝒪_mul_le H hH hDH _ _) (le_refl _)) ?_
  have hW_pow : weight_Λ_over_𝒪 hH ((W𝒪 H) ^ (l + 1)) D
      ≤ WithBot.some ((l + 1) * (H.leadingCoeff).natDegree) := by
    refine (weight_Λ_over_𝒪_pow_le H hH hDH (W𝒪 H) (l + 1)).trans ?_
    exact nsmul_withBot_le (l + 1) _ (weight_Λ_over_𝒪_W H hH hDH)
  have hξ_pow : weight_Λ_over_𝒪 hH ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * l - 1)) D
      ≤ WithBot.some
          ((2 * l - 1) * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
    refine (weight_Λ_over_𝒪_pow_le H hH hDH (ClaimA2.ξ x₀ R H hHyp) (2 * l - 1)).trans ?_
    exact nsmul_withBot_le (2 * l - 1) _ hξ
  refine le_trans (add_le_add (add_le_add ha_wt hW_pow) hξ_pow) ?_
  rw [← WithBot.coe_add, ← WithBot.coe_add]

/-! ### 3′. Packaging the structured prefix invariant

The per-order structured bounds above are exactly the named
`βHenselStructuredWeightInvariant` prefix API consumed by the older induction surface in
`HenselNumerator`.  These wrappers expose that connection directly from each #138 residual form. -/

/-- Package the per-order structured-weight theorem into the named prefix invariant, from carved
alpha regularity and the full lift identity. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k := by
  intro l _hl
  exact βHensel_weight_structured H x₀ R hHyp hH hDH hlift hα hξ l

/-- Package the per-order structured-weight theorem into the named prefix invariant, directly from
the concrete divisibility residual. -/
theorem βHenselStructuredWeightInvariant_of_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdiv : DivWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k := by
  intro l _hl
  exact βHensel_weight_structured_of_divWeight H x₀ R hHyp hH hDH hdiv hξ l

/-- Package the named prefix invariant from the normalized base/successor divisibility targets. -/
theorem βHenselStructuredWeightInvariant_of_normalized_divWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_divWeight H x₀ R hHyp hH hDH
    (DivWeightLe.of_normalized_cases H x₀ R hHyp hH D h0 hsucc) hξ k

/-- Package the named prefix invariant from the concrete divisibility residual, with the `ξ`
side condition discharged. -/
theorem βHenselStructuredWeightInvariant_of_divWeight' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_divWeight H x₀ R hHyp hH hDH hdiv
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) k

/-- Package the named prefix invariant from normalized divisibility targets, with the `ξ` side
condition discharged. -/
theorem βHenselStructuredWeightInvariant_of_normalized_divWeight_cases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_normalized_divWeight_cases H x₀ R hHyp hH
    hDH h0 hsucc (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) k

/-- Package the named prefix invariant from carved alpha regularity and only successor-order lift
identities; the zero-order lift is the proved base theorem. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k := by
  have hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
    intro t
    cases t with
    | zero => exact βHensel_lift_identity_zero H x₀ R hHyp
    | succ t => exact hliftSucc t
  exact βHenselStructuredWeightInvariant_of_alphaWeight H x₀ R hHyp hH hDH
    hlift hα hξ k

/-- Package the named prefix invariant from carved alpha regularity and successor-order lift
identities, with the `ξ` side condition discharged. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_alphaWeight_succLift H x₀ R hHyp hH hDH
    hliftSucc hα (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) k

/-- Package the named prefix invariant directly from carved alpha-weight base and successor cases,
given the full lift identity. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_divWeight H x₀ R hHyp hH hDH
    (DivWeightLe.of_alphaWeight_cases H x₀ R hHyp hH D hlift h0 hsucc) hξ k

/-! ### 4. (P1) the loose weight bound, PROVEN from the structured invariant -/

/-- **(P1), the loose Claim-A.2 bound.**  From the structured invariant (under `hlift` + the carved
link + the `Λ(ξ)` regime), the loose target `Λ_𝒪(βHensel t) ≤ (2t+1)·natDegreeY R·D` follows by the
proven wave-5 arithmetic collapse `βHensel_weight_bound_of_structured_weight`, under the paper's
faithful regime `2 ≤ d`, `dH ≤ d`, `Λ(W)+dH ≤ D`. -/
theorem βHensel_weight_bound_of_alphaWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  have hstructured := βHensel_weight_structured H x₀ R hHyp hH hDH hlift hα hξ t
  exact βHensel_weight_bound_of_structured_weight H x₀ R hHyp hH hdR2 hdHR hW t hstructured

/-- **(P1), directly from the concrete divisibility residual.**  This version avoids the lift/alpha
equivalence route: `DivWeightLe` supplies the `𝒪`-factorization consumed by the structured-weight
proof directly. -/
theorem βHensel_weight_bound_of_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hdiv : DivWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  have hstructured := βHensel_weight_structured_of_divWeight H x₀ R hHyp hH hDH hdiv hξ t
  exact βHensel_weight_bound_of_structured_weight H x₀ R hHyp hH hdR2 hdHR hW t hstructured

/-- **(P1), directly from normalized base/successor divisibility targets.**  This is a consumer
adapter for the current normalized #138 proof target. -/
theorem βHensel_weight_bound_of_normalized_divWeight_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight H x₀ R hHyp hH hDH hdR2 hdHR hW
    (DivWeightLe.of_normalized_cases H x₀ R hHyp hH D h0 hsucc) hξ t

/-- **(P1), directly from `DivWeightLe`, with the `ξ` side condition discharged.**  Once the
concrete divisibility residual is supplied, the remaining `ξ`-weight input is exactly
`ClaimA2.weight_ξ_bound` under the faithful degree regime. -/
theorem βHensel_weight_bound_of_divWeight' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight H x₀ R hHyp hH hDH hdR2 hdHR hW hdiv
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-- **(P1), directly from normalized base/successor divisibility targets, with `ξ` discharged.** -/
theorem βHensel_weight_bound_of_normalized_divWeight_cases' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_normalized_divWeight_cases H x₀ R hHyp hH hDH hdR2 hdHR hW
    h0 hsucc (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-! ### 4′. Discharging `hξ` via the PROVEN `weight_ξ_bound` (SOLE residual: `hlift` + `hα`) -/

/-- **(P1)**, with `hξ` discharged by the proven `ClaimA2.weight_ξ_bound` under its regime.  The
sole remaining inputs are the (P2) lift identity `hlift` and the carved A.4 link `hα`. -/
theorem βHensel_weight_bound_of_alphaWeight' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_alphaWeight H x₀ R hHyp hH hDH hdR2 hdHR hW hlift hα
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-! ### 5. The sharp `t = 0` divisibility obstruction — PROVEN unconditionally

`αGenuine 0 = α₀ = T/W`; the lift identity at `t = 0` is the PROVEN, axiom-clean
`βHensel_lift_identity_zero` (`embedding (βHensel 0) = α₀·W^1·ξ^0 = α₀·W = T`).  Any
`AlphaGenuineRegularWeightLe` witness `a_0` thus forces `βHensel 0 = a_0 · W𝒪` in `𝒪`, i.e.
`W𝒪 ∣ βHensel 0`.  This is the concrete residual: `α₀ = T/W` is regular ⟺ this clearing divisibility
holds.  We do NOT need `hlift` here — only the proven base case + injectivity. -/

/-- **The sharp `t = 0` obstruction (PROVEN, no `hlift`).**  From the proven base-case lift identity
`βHensel_lift_identity_zero` and a carved preimage `a` of `αGenuine 0 = α₀ = T/W`, injectivity of
`embedding` gives `βHensel 0 = a · W𝒪` in `𝒪`.  So `AlphaGenuineRegularWeightLe` at `t = 0` is
exactly the `𝒪`-divisibility `W𝒪 ∣ βHensel 0` (with the quotient `a` at weight `≤ 1`): the genuine,
non-faked face of the residual. -/
theorem W𝒪_dvd_βHensel_zero_of_alpha (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {a : 𝒪 H}
    (ha : embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp 0) :
    βHensel H x₀ R hHyp 0 = a * W𝒪 H := by
  apply embeddingOf𝒪Into𝕃_injective hH
  rw [βHensel_lift_identity_zero, map_mul, ha, embeddingOf𝒪Into𝕃_W𝒪]
  simp only [Nat.mul_zero, Nat.zero_sub, pow_zero, mul_one, zero_add, pow_one]

/-- The corrected cleared base target: after multiplying the obstructed `αGenuine 0 = T/W` by
the single `W` factor, the cleared coefficient is represented by an `𝒪`-element of weight `≤ 1`. -/
def AlphaGenuineRegularWeightLe_zero_cleared (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∃ a : 𝒪 H,
    embeddingOf𝒪Into𝕃 H a =
        liftToFunctionField (H := H) H.leadingCoeff * αGenuine H x₀ R hHyp 0
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

/-- The direct beta-side form of the corrected cleared base witness: `βHensel 0 = mk X` has
`Λ_𝒪`-weight at most one whenever the truncation budget is at most `deg H`. -/
theorem βHensel_zero_weight_le_one (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hd : 2 ≤ H.natDegree) {D : ℕ} (hD : D ≤ H.natDegree) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1 := by
  rw [βHensel_zero]
  have hdegX : (Polynomial.X : F[X][Y]).degree < (H_tilde' H).degree := by
    rw [Polynomial.degree_X]
    rw [Polynomial.degree_eq_natDegree (H_tilde'_monic H hH).ne_zero]
    rw [natDegree_H_tilde' hH]
    exact_mod_cast (by omega : 1 < H.natDegree)
  rw [weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hdegX]
  refine (show weight_Λ (Polynomial.X : F[X][Y]) H D
      ≤ WithBot.some (D + 1 - Bivariate.natDegreeY H) from by
        simpa using (weight_Λ_X_pow_le H D 1)).trans ?_
  have hle : D + 1 - Bivariate.natDegreeY H ≤ 1 := by
    rw [show Bivariate.natDegreeY H = H.natDegree from rfl]
    omega
  exact_mod_cast hle

/-- Build the corrected cleared base predicate from the direct beta-side weight bound. -/
theorem AlphaGenuineRegularWeightLe_zero_cleared.of_betaWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hwt : weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1) :
    AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D := by
  refine ⟨βHensel H x₀ R hHyp 0, ?_, hwt⟩
  have h := βHensel_lift_identity_zero H x₀ R hHyp
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- Project the direct beta-side weight bound from the corrected cleared base predicate. -/
theorem AlphaGenuineRegularWeightLe_zero_cleared.betaWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hcleared : AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1 := by
  obtain ⟨a, ha, hwt⟩ := hcleared
  have hβ : embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp 0)
      = liftToFunctionField (H := H) H.leadingCoeff * αGenuine H x₀ R hHyp 0 := by
    have h := βHensel_lift_identity_zero H x₀ R hHyp
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have ha_eq : a = βHensel H x₀ R hHyp 0 := by
    apply embeddingOf𝒪Into𝕃_injective hH
    rw [ha, hβ]
  simpa [ha_eq] using hwt

/-- The corrected cleared base predicate is exactly the direct beta-side weight bound. -/
theorem alphaWeight_zero_cleared_iff_betaWeight_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) :
    AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D ↔
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1 := by
  constructor
  · exact AlphaGenuineRegularWeightLe_zero_cleared.betaWeight H x₀ R hHyp hH
  · exact AlphaGenuineRegularWeightLe_zero_cleared.of_betaWeight H x₀ R hHyp hH

/-- **Corrected cleared `t = 0` base witness.**  The un-cleared target
`AlphaGenuineRegularWeightLe_zero` asks for a regular preimage of `αGenuine 0 = T/W`; that is the
obstructed statement above.  After clearing by the single `W` factor, `βHensel 0 = mk X` itself is a
weight-`≤ 1` witness for `W * αGenuine 0 = T`. -/
theorem alphaWeight_zero_cleared_fixed (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hd : 2 ≤ H.natDegree) {D : ℕ} (hD : D ≤ H.natDegree) :
    ∃ a : 𝒪 H,
      embeddingOf𝒪Into𝕃 H a =
          liftToFunctionField (H := H) H.leadingCoeff * αGenuine H x₀ R hHyp 0
        ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 := by
  exact AlphaGenuineRegularWeightLe_zero_cleared.of_betaWeight H x₀ R hHyp hH
    (βHensel_zero_weight_le_one H x₀ R hHyp hH hd hD)

/-- Package the landed cleared base witness into the corrected cleared base predicate. -/
theorem AlphaGenuineRegularWeightLe_zero_cleared.of_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ} (hD : D ≤ H.natDegree) :
    AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D :=
  alphaWeight_zero_cleared_fixed H x₀ R hHyp hH hd hD

/-- The corrected beta-side base target: `βHensel 0` itself has a weight-`≤ 1` representative. -/
def DivWeightLe_zero_cleared (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∃ a : 𝒪 H,
    βHensel H x₀ R hHyp 0 = a ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

/-- Build the corrected cleared base div-weight predicate from the direct beta-side weight bound. -/
theorem DivWeightLe_zero_cleared.of_betaWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hwt : weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1) :
    DivWeightLe_zero_cleared H x₀ R hHyp hH D :=
  ⟨βHensel H x₀ R hHyp 0, rfl, hwt⟩

/-- Project the direct beta-side weight bound from the corrected cleared base div-weight predicate. -/
theorem DivWeightLe_zero_cleared.betaWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hdiv0 : DivWeightLe_zero_cleared H x₀ R hHyp hH D) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1 := by
  obtain ⟨a, hβ, hwt⟩ := hdiv0
  simpa [hβ] using hwt

/-- The corrected cleared base div-weight predicate is exactly the beta-side weight bound. -/
theorem divWeight_zero_cleared_iff_betaWeight_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) :
    DivWeightLe_zero_cleared H x₀ R hHyp hH D ↔
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1 := by
  constructor
  · exact DivWeightLe_zero_cleared.betaWeight H x₀ R hHyp hH
  · exact DivWeightLe_zero_cleared.of_betaWeight H x₀ R hHyp hH

/-- Transport the corrected cleared alpha base predicate to the corrected div-weight base target. -/
theorem DivWeightLe_zero_cleared.of_alphaWeight_zero_cleared
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hα0 : AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D) :
    DivWeightLe_zero_cleared H x₀ R hHyp hH D :=
  DivWeightLe_zero_cleared.of_betaWeight H x₀ R hHyp hH
    (AlphaGenuineRegularWeightLe_zero_cleared.betaWeight H x₀ R hHyp hH hα0)

/-- Transport the corrected cleared div-weight base target back to the corrected alpha base target. -/
theorem AlphaGenuineRegularWeightLe_zero_cleared.of_divWeight_zero_cleared
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hdiv0 : DivWeightLe_zero_cleared H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D :=
  AlphaGenuineRegularWeightLe_zero_cleared.of_betaWeight H x₀ R hHyp hH
    (DivWeightLe_zero_cleared.betaWeight H x₀ R hHyp hH hdiv0)

/-- The corrected cleared alpha and div-weight base predicates are equivalent. -/
theorem alphaWeight_zero_cleared_iff_divWeight_zero_cleared
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) :
    AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D ↔
      DivWeightLe_zero_cleared H x₀ R hHyp hH D := by
  constructor
  · exact DivWeightLe_zero_cleared.of_alphaWeight_zero_cleared H x₀ R hHyp hH
  · exact AlphaGenuineRegularWeightLe_zero_cleared.of_divWeight_zero_cleared H x₀ R hHyp hH

/-- **Corollary: `W𝒪 ∣ βHensel 0` is *necessary* for `AlphaGenuineRegularWeightLe`.**  If the carved
link holds (at the `t = 0` instance), then `W𝒪` divides `βHensel 0` in `𝒪 H`.  This is the precise,
machine-checked statement of the `α₀ = T/W` regularity obstruction: the carve forces a clearing
divisibility that the field-level lift identity alone does not. -/
theorem W𝒪_dvd_βHensel_zero_of_alphaWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    W𝒪 H ∣ βHensel H x₀ R hHyp 0 := by
  obtain ⟨a, ha_eq, _⟩ := hα 0
  refine ⟨a, ?_⟩
  rw [W𝒪_dvd_βHensel_zero_of_alpha H x₀ R hHyp hH ha_eq]
  exact mul_comm a (W𝒪 H)

/-- The base carved regularity case supplies the base divisibility-with-weight case without the
all-orders P2 lift hypothesis.  It uses only the already-proved base lift identity folded through
`W𝒪_dvd_βHensel_zero_of_alpha`. -/
theorem DivWeightLe_zero.of_alphaWeight_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hα0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D) :
    DivWeightLe_zero H x₀ R hHyp hH D := by
  obtain ⟨a, ha_eq, ha_wt⟩ := hα0
  refine ⟨a, ?_, ha_wt⟩
  rw [W𝒪_dvd_βHensel_zero_of_alpha H x₀ R hHyp hH ha_eq]
  simp only [Nat.mul_zero, Nat.zero_sub, pow_zero, mul_one, zero_add, pow_one]

/-- The base divisibility-with-weight case supplies the base carved regularity case without the
all-orders P2 lift hypothesis. -/
theorem AlphaGenuineRegularWeightLe_zero.of_divWeight_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hdiv0 : DivWeightLe_zero H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D := by
  obtain ⟨a, hfact, ha_wt⟩ := hdiv0
  refine ⟨a, ?_, ha_wt⟩
  exact alpha_eq_embedding_of_fact H x₀ R hHyp 0 hfact
    (βHensel_lift_identity_zero H x₀ R hHyp)

/-- The `t = 0` alpha/divisibility equivalence needs only the proved base lift identity, not the
full all-orders P2 lift identity used by `alphaWeight_zero_iff_divWeight_zero`. -/
theorem alphaWeight_zero_iff_divWeight_zero_base (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) :
    AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D ↔
      DivWeightLe_zero H x₀ R hHyp hH D := by
  constructor
  · exact DivWeightLe_zero.of_alphaWeight_zero H x₀ R hHyp hH D
  · exact AlphaGenuineRegularWeightLe_zero.of_divWeight_zero H x₀ R hHyp hH D

/-- A successor carved regularity case is equivalent to the corresponding successor
divisibility-with-weight case using only the lift identity at that successor order. -/
theorem alphaWeight_succ_iff_divWeight_succ_of_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (t : ℕ) :
    AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t ↔
      DivWeightLe_succ H x₀ R hHyp hH D t := by
  constructor
  · intro hα
    obtain ⟨a, ha_eq, ha_wt⟩ := hα
    exact
      ⟨a, βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH (t + 1) ha_eq
        (hliftSucc t), ha_wt⟩
  · intro hdiv
    obtain ⟨a, hfact, ha_wt⟩ := hdiv
    exact ⟨a, alpha_eq_embedding_of_fact H x₀ R hHyp (t + 1) hfact
      (hliftSucc t), ha_wt⟩

/-- The carved alpha-weight residual is equivalent to the divisibility base/successor cases when
the base case uses the unconditional zero-order bridge and only successor lift identities remain
as hypotheses. -/
theorem alphaWeight_iff_divWeight_cases_of_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      DivWeightLe_zero H x₀ R hHyp hH D ∧
        ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t := by
  constructor
  · intro hα
    exact
      ⟨DivWeightLe_zero.of_alphaWeight_zero H x₀ R hHyp hH D
          (AlphaGenuineRegularWeightLe.zero H x₀ R hHyp hH D hα),
        fun t =>
          (alphaWeight_succ_iff_divWeight_succ_of_succLift H x₀ R hHyp hH D
            hliftSucc t).1
            (AlphaGenuineRegularWeightLe.succ H x₀ R hHyp hH D hα t)⟩
  · intro hcases
    exact AlphaGenuineRegularWeightLe.of_cases H x₀ R hHyp hH D
      (AlphaGenuineRegularWeightLe_zero.of_divWeight_zero H x₀ R hHyp hH D hcases.1)
      (fun t =>
        (alphaWeight_succ_iff_divWeight_succ_of_succLift H x₀ R hHyp hH D
          hliftSucc t).2 (hcases.2 t))

/-- Assemble carved alpha-weight regularity from divisibility base and successor cases, requiring
only successor-order lift identities; the base case uses `βHensel_lift_identity_zero`. -/
theorem AlphaGenuineRegularWeightLe.of_divWeight_cases_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : DivWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_cases_of_succLift H x₀ R hHyp hH D hliftSucc).2
    ⟨h0, hsucc⟩

/-- Assemble the concrete `𝒪`-divisibility form from carved alpha-weight base and successor cases,
requiring only successor-order lift identities; the base case uses the proved zero-order bridge. -/
theorem DivWeightLe.of_alphaWeight_cases_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    DivWeightLe H x₀ R hHyp hH D :=
  DivWeightLe.of_cases H x₀ R hHyp hH D
    (DivWeightLe_zero.of_alphaWeight_zero H x₀ R hHyp hH D h0)
    (fun t =>
      (alphaWeight_succ_iff_divWeight_succ_of_succLift H x₀ R hHyp hH D
        hliftSucc t).1 (hsucc t))

/-- Package the named prefix invariant directly from carved alpha-weight base and successor cases,
requiring only successor-order lift identities. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_cases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_divWeight H x₀ R hHyp hH hDH
    (DivWeightLe.of_alphaWeight_cases_succLift H x₀ R hHyp hH D hliftSucc h0 hsucc)
    hξ k

/-- Transport the full carved alpha-weight residual to the full divisibility-with-weight residual
using only successor-order lift identities; the base case uses the proved zero-order bridge. -/
theorem DivWeightLe.of_alphaWeight_succLift (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    DivWeightLe H x₀ R hHyp hH D := by
  have hcases :=
    (alphaWeight_iff_divWeight_cases_of_succLift H x₀ R hHyp hH D hliftSucc).1 hα
  exact DivWeightLe.of_cases H x₀ R hHyp hH D hcases.1 hcases.2

/-- Transport the full divisibility-with-weight residual to the full carved alpha-weight residual
using only successor-order lift identities; the base case uses the proved zero-order bridge. -/
theorem AlphaGenuineRegularWeightLe.of_divWeight_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  AlphaGenuineRegularWeightLe.of_divWeight_cases_succLift H x₀ R hHyp hH D hliftSucc
    (DivWeightLe.zero H x₀ R hHyp hH D hdiv)
    (DivWeightLe.succ H x₀ R hHyp hH D hdiv)

/-- Assemble carved alpha-weight regularity from the normalized divisibility base/successor
targets under successor-order lift identities. -/
theorem AlphaGenuineRegularWeightLe.of_normalized_divWeight_cases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  AlphaGenuineRegularWeightLe.of_divWeight_succLift H x₀ R hHyp hH D hliftSucc
    (DivWeightLe.of_normalized_cases H x₀ R hHyp hH D h0 hsucc)

/-- The full carved alpha-weight residual is equivalent to the full divisibility-with-weight
residual using only successor-order lift identities. -/
theorem alphaWeight_iff_divWeight_of_succLift (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      DivWeightLe H x₀ R hHyp hH D := by
  constructor
  · exact DivWeightLe.of_alphaWeight_succLift H x₀ R hHyp hH D hliftSucc
  · exact AlphaGenuineRegularWeightLe.of_divWeight_succLift H x₀ R hHyp hH D hliftSucc

/-- Under successor-order lift identities, the carved alpha-weight residual is equivalent to the
normalized base and successor divisibility targets. -/
theorem alphaWeight_iff_normalized_divWeight_cases_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (alphaWeight_iff_divWeight_of_succLift H x₀ R hHyp hH D hliftSucc).trans
    (divWeight_iff_normalized_cases H x₀ R hHyp hH D)

/-- Project the normalized base and successor divisibility targets from a full carved
alpha-weight proof, using only successor-order lift identities. -/
theorem AlphaGenuineRegularWeightLe.normalized_divWeight_cases_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (alphaWeight_iff_normalized_divWeight_cases_succLift H x₀ R hHyp hH D hliftSucc).1 hα

/-- Project the normalized base divisibility target from a full carved alpha-weight proof, using
only successor-order lift identities. -/
theorem AlphaGenuineRegularWeightLe.normalized_divWeight_zero_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (AlphaGenuineRegularWeightLe.normalized_divWeight_cases_succLift
    H x₀ R hHyp hH D hliftSucc hα).1

/-- Project a normalized successor divisibility target from a full carved alpha-weight proof, using
only the successor-order lift identity family. -/
theorem AlphaGenuineRegularWeightLe.normalized_divWeight_succ_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D t : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (AlphaGenuineRegularWeightLe.normalized_divWeight_cases_succLift
    H x₀ R hHyp hH D hliftSucc hα).2 t

/-- A successor carved regularity case supplies the corresponding successor
divisibility-with-weight case from only the lift identity at that successor order. -/
theorem DivWeightLe_succ.of_alphaWeight_succ (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) (t : ℕ)
    (hlift_succ :
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hαsucc : AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    DivWeightLe_succ H x₀ R hHyp hH D t := by
  obtain ⟨a, ha_eq, ha_wt⟩ := hαsucc
  exact
    ⟨a, βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH (t + 1) ha_eq hlift_succ,
      ha_wt⟩

/-- A successor divisibility-with-weight case supplies the corresponding successor carved
regularity case from only the lift identity at that successor order. -/
theorem AlphaGenuineRegularWeightLe_succ.of_divWeight_succ
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) (t : ℕ)
    (hlift_succ :
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hdivsucc : DivWeightLe_succ H x₀ R hHyp hH D t) :
    AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t := by
  obtain ⟨a, hfact, ha_wt⟩ := hdivsucc
  exact ⟨a, alpha_eq_embedding_of_fact H x₀ R hHyp (t + 1) hfact hlift_succ, ha_wt⟩

/-- The successor alpha/divisibility equivalence only needs the lift identity at the same successor
order, not the full all-orders P2 lift hypothesis. -/
theorem alphaWeight_succ_iff_divWeight_succ_at (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) (t : ℕ)
    (hlift_succ :
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) :
    AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t ↔
      DivWeightLe_succ H x₀ R hHyp hH D t := by
  constructor
  · exact DivWeightLe_succ.of_alphaWeight_succ H x₀ R hHyp hH D t hlift_succ
  · exact AlphaGenuineRegularWeightLe_succ.of_divWeight_succ H x₀ R hHyp hH D t hlift_succ

/-- Assemble the all-order lift identity from the proved zero-order lift identity and a
successor-order lift identity family. -/
theorem βHensel_lift_identity_of_succLift (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
  cases t with
  | zero =>
      exact βHensel_lift_identity_zero H x₀ R hHyp
  | succ t =>
      exact hliftSucc t

/-- **(P1)** from carved alpha regularity using only successor-order lift identities.  The
zero-order lift is supplied by the proved base theorem. -/
theorem βHensel_weight_bound_of_alphaWeight_succLift (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_alphaWeight H x₀ R hHyp hH hDH hdR2 hdHR hW
    (βHensel_lift_identity_of_succLift H x₀ R hHyp hliftSucc) hα hξ t

/-- **(P1)** from carved alpha regularity using only successor-order lift identities, with the
`ξ`-weight side condition discharged by `ClaimA2.weight_ξ_bound`. -/
theorem βHensel_weight_bound_of_alphaWeight_succLift' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_alphaWeight_succLift H x₀ R hHyp hH hDH hdR2 hdHR hW
    hliftSucc hα (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-- **(P1)** from carved alpha-weight base and successor cases, given the full lift identity. -/
theorem βHensel_weight_bound_of_alphaWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight H x₀ R hHyp hH hDH hdR2 hdHR hW
    (DivWeightLe.of_alphaWeight_cases H x₀ R hHyp hH D hlift h0 hsucc) hξ t

/-- **(P1)** from carved alpha-weight base and successor cases using only successor-order lift
identities; the zero-order lift is supplied by the proved base theorem. -/
theorem βHensel_weight_bound_of_alphaWeight_cases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight H x₀ R hHyp hH hDH hdR2 hdHR hW
    (DivWeightLe.of_alphaWeight_cases_succLift H x₀ R hHyp hH D hliftSucc h0 hsucc)
    hξ t

end AlphaWeight

end BCIKS20.HenselNumerator

-- Axiom audit: every closed declaration in this file depends on exactly the three standard axioms
-- `[propext, Classical.choice, Quot.sound]` (no `sorry`/`admit`/`axiom`/`native_decide`).
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_succ
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.of_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.succ
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_succ
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_of_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.of_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.succ
#print axioms BCIKS20.HenselNumerator.AlphaWeight.divWeight_iff_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.divWeight_zero_iff_W𝒪_factor
#print axioms BCIKS20.HenselNumerator.AlphaWeight.divWeight_succ_iff_normalized_factor
#print axioms BCIKS20.HenselNumerator.AlphaWeight.divWeight_iff_normalized_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.of_normalized_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.normalized_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.normalized_zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.normalized_succ
#print axioms BCIKS20.HenselNumerator.AlphaWeight.embeddingOf𝒪Into𝕃_W𝒪
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_eq_alpha_mul_of_lift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alpha_eq_embedding_of_fact
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_iff_divWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.of_alphaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.of_divWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_zero_iff_divWeight_zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_succ_iff_divWeight_succ
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_iff_divWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.of_divWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_structured
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_structured_of_divWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_of_divWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_of_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_of_divWeight'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_of_normalized_divWeight_cases'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_succLift'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_alphaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_divWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_divWeight'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_normalized_divWeight_cases'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_alphaWeight'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.W𝒪_dvd_βHensel_zero_of_alpha
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_zero_cleared
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_zero_weight_le_one
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_zero_cleared.of_betaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_zero_cleared.betaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_zero_cleared_iff_betaWeight_zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_zero_cleared_fixed
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_zero_cleared.of_fixed
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_zero_cleared
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_zero_cleared.of_betaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_zero_cleared.betaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.divWeight_zero_cleared_iff_betaWeight_zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_zero_cleared.of_alphaWeight_zero_cleared
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_zero_cleared.of_divWeight_zero_cleared
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_zero_cleared_iff_divWeight_zero_cleared
#print axioms BCIKS20.HenselNumerator.AlphaWeight.W𝒪_dvd_βHensel_zero_of_alphaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_zero.of_alphaWeight_zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_zero.of_divWeight_zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_zero_iff_divWeight_zero_base
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_succ_iff_divWeight_succ_of_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_iff_divWeight_cases_of_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.of_divWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.of_alphaWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe.of_alphaWeight_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.of_divWeight_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.of_normalized_divWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_iff_divWeight_of_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_iff_normalized_divWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.normalized_divWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.normalized_divWeight_zero_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe.normalized_divWeight_succ_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_succ.of_alphaWeight_succ
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_succ.of_divWeight_succ
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_succ_iff_divWeight_succ_at
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_lift_identity_of_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_alphaWeight_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_alphaWeight_succLift'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_alphaWeight_cases_succLift
