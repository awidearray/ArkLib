STATUS: §5 RE-ANCHORED CLAIMS COMPLETE — disposition (a). Claim 5.8 PROVEN + Claim 5.8' PROVEN (1+2), Claim 5.9 ATTEMPTED with PROVEN per-coefficient reduction + carved target + precise obstruction (3). Compile exit 0, in-file axiom audit confirms the 6 hypothesis-form claims are axiom-clean (no sorryAx); only the 2 `_via_intree` convenience wrappers inherit the upstream `βHensel_lift_identity` residual sorryAx (documented).

# pc-w18 — §5 re-anchored Claims 5.8 / 5.8' / 5.9 (genuine objects)

File (NEW, UNTRACKED): `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/S5Genuine.lean`
Worktree: `/home/shaw/arklib-prize` (harness HARD-RESETS tracked tree + .lake; this file is untracked, /tmp backup at `/tmp/S5Genuine.lean.bak`). NOTE: an earlier green build was wiped by a mid-session hard-reset before I had backed up — reconstructed verbatim from context + the one-line fix, re-greened, backed up immediately.
Compile: `cd /home/shaw/arklib-prize && export PATH=$HOME/.elan/bin:$PATH && timeout 1800 lake env lean ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/S5Genuine.lean` → **EXIT 0**
Imports: `HenselNumerator` (transitively `GammaGenuine`, `RationalFunctions`). All required oleans present (HenselNumerator/GammaGenuine/RationalFunctions/P2Close/P2Match all built).

## Re-anchoring rationale (HONESTY, in every docstring)

In-tree Claims 5.8/5.8'/5.9 (`ListDecoding/Agreement.lean`, sorried) are stated about `ClaimA2.α/β/γ` — the VACUOUS `β=0` stub. That `ClaimA2.γ` is degenerate for `x₀≠0` (substitution fails `HasSubst`) and has NO functional relation to `R`; Agreement.lean's own §5 GAP block records the claims are "neither provable nor refutable" from the opaque `.choose`. Kernel-established unprovable-as-stated (old lift identity against `ClaimA2.α` was FALSE at t=0).

The genuine objects (`GammaGenuine`/`HenselNumerator`) re-anchor them: `gammaGenuine` (real Hensel root, `eval γ Q = 0`), `αGenuine t := coeff t gammaGenuine`, `βHensel t` (genuine (A.1) recursion), `βHensel_lift_identity` (the (P2) bridge), `Lemma_A_1` (the terminal vanishing). This file states the genuine versions onto `αGenuine`/`gammaGenuine` and proves them.

## Outcome table

| Task | Theorem | axioms |
|---|---|---|
| 1 (Claim 5.8, numerator vanish) | `embedding_βHensel_eq_zero_of_SβLarge` | `[propext, Classical.choice, Quot.sound]` — clean |
| 1 (Claim 5.8, α_t = 0) | `claim58_genuine` | clean (no sorryAx) |
| 2 (Claim 5.8', tail) | `claim58prime_genuine_tail` | clean |
| 2 (Claim 5.8', polynomial form γ = γ_k) | `claim58prime_genuine` | clean |
| 2 (Claim 5.8', X-degree < k) | `claim58prime_genuine_natDegree_lt` | clean |
| 3 (Claim 5.9 reduction) | `gammaGenuine_Z_linear_of_coeffs_Z_linear` | clean |
| 3 (Claim 5.9 carved target) | `gammaGenuine_Z_linear_target` (def) | — |
| wrapper (5.8 via in-tree) | `claim58_genuine_via_intree` | `[propext, sorryAx, Classical.choice, Quot.sound]` — inherits in-tree `βHensel_lift_identity` residual `coeff_succ_eval_βHenselAssembled`; documented, NOT hidden |
| wrapper (5.8' via in-tree) | `claim58prime_genuine_via_intree` | inherits same residual sorryAx |

No `sorry`/`admit`/`native_decide`/`bv_decide`/`axiom` decl in the file (only token matches are docstring honesty notes).

## KEY DESIGN DECISION (the honesty pivot)

`βHensel_lift_identity` is PROVEN-modulo-one-residual (`coeff_succ_eval_βHenselAssembled`, still open per w14/w17), so it carries an inherited `sorryAx`. The first build of this file proved 5.8/5.8' by calling `βHensel_lift_identity` DIRECTLY — and the axiom audit showed `claim58_genuine` etc. tainted with `sorryAx`. To be axiom-clean and faithful to the task spec ("under hHyp + the lift identity (hypothesis 'hlift')"), I refactored so the per-`t` lift identity is an EXPLICIT documented hypothesis `LiftIdentityAt` (= the paper's Claim A.2 normalization `α_t = β_t/(W^{t+1}·ξ^{e_t})`, the bridge §5 callers supply). The hypothesis-form claims are then genuinely sorryAx-free; the `_via_intree` wrappers discharge `hlift` from the in-tree theorem and transparently carry its residual sorryAx. When the w14/w17 residual lands, the wrappers become clean automatically, NO change to this file.

## Route for Claim 5.8 (load-bearing), narrated

largeness (`SβLargeAt`, = (5.13)/(5.14)-derived bound, the documented hyp `Lemma_A_1` consumes) → `Lemma_A_1` on `βHensel t` ⟹ `embedding(βHensel t)=0` → `hlift` (`LiftIdentityAt`) rewrites LHS=0 as `αGenuine t · W^{t+1} · ξ^{2t−1} = 0` → re-associate, `den_ne_zero` kills the denominator factor ⟹ `αGenuine t = 0`. Paper lines 1672–1681 exactly.

## Claim 5.8' (polynomial form)

`γ = γ_k`: `gammaGenuine = ↑(PowerSeries.trunc k gammaGenuine)`. By `PowerSeries.ext`: at `t<k` both sides agree by `coeff_trunc`; at `t≥k` truncation coeff is 0 (coeff_trunc) and series coeff is `αGenuine t = 0` (Claim 5.8 tail). Plus the X-degree witness `natDegree (trunc (n+1) γ) < n+1`. This is the machine-checkable "γ is a polynomial of X-degree < k ∈ L[X]" (fulltext 1695).

## Claim 5.9 (attempted) — precise obstruction

Z-linearity target `gammaGenuine_Z_linear_target` carved: `γ = v₀ + C(functionFieldT)·v₁` with `F[X]`-image (Z-degree-0) coefficients. PROVEN reduction `gammaGenuine_Z_linear_of_coeffs_Z_linear`: GIVEN per-coefficient `αGenuine t = liftToFunctionField c₀ + functionFieldT · liftToFunctionField c₁`, assemble `v_i := mk (fun t => liftToFunctionField (c_i t))` and verify coefficient-wise via `coeff_C_mul`/`coeff_mk`. OBSTRUCTION: no in-tree lemma bounds the Z-degree (RatFunc/ground-layer degree) of `αGenuine t` by 1; `weight_Λ_over_𝒪` only carries the `degreeX` (X/Z) component, not a Z-degree-1 structural fact. The paper proves Z-linearity GEOMETRICALLY (≥ k+1 good x-values + interpolation, lines 1719–1740) — a different argument from the §5.2.6 degree route, not reducible to the lift identity. So the missing piece is exactly the per-coefficient Z-degree-1 fact, now isolated as the single antecedent of the proven reduction.

## VERBATIM PROOFS (the proven core)

```lean
def SβLargeAt (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : Prop :=
  ∃ D : ℕ, D ≥ Bivariate.totalDegree H ∧
    (↑(Set.ncard (S_β (βHensel H x₀ R hHyp t))) : WithBot ℕ)
      > weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree)) (βHensel H x₀ R hHyp t) D
          * (H.natDegree : WithBot ℕ)

def LiftIdentityAt (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : Prop :=
  embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
    = αGenuine H x₀ R hHyp t
        * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)

theorem embedding_βHensel_eq_zero_of_SβLarge {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) {t : ℕ} (hlarge : SβLargeAt H x₀ R hHyp t) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t) = 0 := by
  obtain ⟨D, hD, hcard⟩ := hlarge
  exact Lemma_A_1 (Fact.out (p := 0 < H.natDegree)) (βHensel H x₀ R hHyp t) D hD hcard

theorem claim58_genuine {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) {t : ℕ} (hlarge : SβLargeAt H x₀ R hHyp t)
    (hlift : LiftIdentityAt H x₀ R hHyp t) :
    αGenuine H x₀ R hHyp t = 0 := by
  have hβ : embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t) = 0 :=
    embedding_βHensel_eq_zero_of_SβLarge H hHyp hlarge
  unfold LiftIdentityAt at hlift
  rw [hβ] at hlift
  have hprod : αGenuine H x₀ R hHyp t
      * ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) = 0 := by
    rw [← mul_assoc]; exact hlift.symm
  exact (mul_eq_zero.mp hprod).resolve_right (den_ne_zero H x₀ R hHyp t)

theorem claim58_genuine_via_intree {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) {t : ℕ} (hlarge : SβLargeAt H x₀ R hHyp t) :
    αGenuine H x₀ R hHyp t = 0 :=
  claim58_genuine H hHyp hlarge (βHensel_lift_identity H x₀ R hHyp t)

theorem claim58prime_genuine_tail {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t)
    (hlift : ∀ t ≥ k, LiftIdentityAt H x₀ R hHyp t) :
    ∀ t ≥ k, αGenuine H x₀ R hHyp t = 0 :=
  fun t ht => claim58_genuine H hHyp (hlarge t ht) (hlift t ht)

theorem claim58prime_genuine {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t)
    (hlift : ∀ t ≥ k, LiftIdentityAt H x₀ R hHyp t) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : (𝕃 H)⟦X⟧) := by
  have htail : ∀ t ≥ k, αGenuine H x₀ R hHyp t = 0 :=
    claim58prime_genuine_tail H hHyp hlarge hlift
  ext t
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases ht : t < k
  · rw [if_pos ht]
  · rw [if_neg ht]
    have hge : t ≥ k := not_lt.mp ht
    have : PowerSeries.coeff t (gammaGenuine x₀ R H hHyp) = αGenuine H x₀ R hHyp t := rfl
    rw [this, htail t hge]

theorem claim58prime_genuine_natDegree_lt {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (n : ℕ) :
    (PowerSeries.trunc (n + 1) (gammaGenuine x₀ R H hHyp)).natDegree < n + 1 :=
  PowerSeries.natDegree_trunc_lt (gammaGenuine x₀ R H hHyp) n

def gammaGenuine_Z_linear_target (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∃ v₀ v₁ : (𝕃 H)⟦X⟧,
    gammaGenuine x₀ R H hHyp = v₀ + (PowerSeries.C (functionFieldT (H := H))) * v₁ ∧
    (∀ t, ∃ c₀ c₁ : F[X],
      PowerSeries.coeff t v₀ = liftToFunctionField (H := H) c₀ ∧
      PowerSeries.coeff t v₁ = liftToFunctionField (H := H) c₁)

theorem gammaGenuine_Z_linear_of_coeffs_Z_linear {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hcoeff : ∀ t, ∃ c₀ c₁ : F[X],
      αGenuine H x₀ R hHyp t
        = liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁) :
    gammaGenuine_Z_linear_target H x₀ R hHyp := by
  classical
  choose c₀ c₁ hc using hcoeff
  refine ⟨PowerSeries.mk (fun t => liftToFunctionField (H := H) (c₀ t)),
    PowerSeries.mk (fun t => liftToFunctionField (H := H) (c₁ t)), ?_, ?_⟩
  · ext t
    rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    show αGenuine H x₀ R hHyp t = _
    rw [hc t]
  · intro t
    exact ⟨c₀ t, c₁ t, by rw [PowerSeries.coeff_mk], by rw [PowerSeries.coeff_mk]⟩
```

## Axiom audit (compile-time `#print axioms`, observed)

```
claim58_genuine                          : [propext, Classical.choice, Quot.sound]
claim58prime_genuine                     : [propext, Classical.choice, Quot.sound]
claim58prime_genuine_tail                : [propext, Classical.choice, Quot.sound]
claim58prime_genuine_natDegree_lt        : [propext, Classical.choice, Quot.sound]
embedding_βHensel_eq_zero_of_SβLarge     : [propext, Classical.choice, Quot.sound]
gammaGenuine_Z_linear_of_coeffs_Z_linear : [propext, Classical.choice, Quot.sound]
claim58_genuine_via_intree               : [propext, sorryAx, Classical.choice, Quot.sound]  (upstream residual, documented)
claim58prime_genuine_via_intree          : [propext, sorryAx, Classical.choice, Quot.sound]  (upstream residual, documented)
```

## Environment notes
- NEVER ran full `lake build`. Single-file `lake env lean`. No git commit/push.
- The 5194344-byte RationalFunctions.olean + 2288960-byte HenselNumerator.olean were present; no dep-olean race encountered.
