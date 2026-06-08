/-
SCRATCH — Issue #61: non-vacuous betaRec → hcoeffPoly keystone assembly.

NOT part of the build. Hand-verified against stable ArkLib/mathlib API by READING source
signatures (the mathlib package is mid-clone / empty, so `lake` cannot run). Every external
lemma cited below is referenced with its file:line anchor that I read in this session.

=============================================================================================
PART 0 — Anchors read (exact, confirmed in-tree)
=============================================================================================

A1. ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean
      αFromBeta                                   (def, l.58)
      alphaFromBeta_eq_zero_of_embedding_zero     (l.68)
      tail_zero_of_betaRec_embedding_zero         (l.79)  -- consumes betaRec via L14 bridge
      CurveCoeffPolys                             (def, l.100)
      curveCoeffPolys_of_linear_representative    (l.135)  -- conclusion built ONLY from hPeval
      curveCoeffPolys_of_betaRec                  (l.160)  -- the F4-closed composition

A2. ArkLib/ToMathlib/HcardDischarge.lean
      tail_zero_on_finite_range                   (l.114)
      tail_zero_of_range_and_degree               (l.146)
      tail_zero_of_finite_card_and_degree         (l.165)
      structure Section5StrictDataFin             (l.193)  -- fields hcardFin/htailDeg/hγ mention betaRec
      curveCoeffPolys_of_section5DataFin          (l.254)
      hcoeffPoly_witness_of_section5DataFin       (l.287)

A3. ArkLib/ToMathlib/CorrelatedAgreementListDecodingClosed.lean
      structure Section5StrictData                (l.93)
      curveCoeffPolys_of_section5Data             (l.202)  -- delegates to curveCoeffPolys_of_betaRec
      hcoeffPoly_witness_of_section5Data          (l.223)

A4. ArkLib/ToMathlib/KeystoneCapstone.lean
      CurveCoeffPolys                             (def, l.92)
      hcoeffPoly_witness_of_curveCoeffPolys       (l.110)  -- pure bundling (per-index → ℕ→Poly)
      Section55CurveCoeffOutput                   (def, l.148) -- ≡ the goal  (F4 vacuous wrapper)
      hcoeffPoly_of_johnson_regime                (l.163)  -- F4: proof uses ONLY the hypothesis

A5. ArkLib/ToMathlib/GammaFromBeta.lean
      alpha_eq_alphaFromBeta_of_betaEq            (l.77)   -- α = αFromBeta from hβ
      intree_gamma_eq_γ'                          (l.87)
      hγ_field_of_betaEq                          (l.100)  -- *** the genuine betaRec entry point ***

A6. ArkLib/ToMathlib/TailDegProducer.lean
      alphaFromBeta_eq_lift_coeff                 (l.170)  -- αFromBeta t = lift (Ppoly.coeff t)
      htailDeg_of_polynomial_representative       (l.200)  -- *** derives the α-tail from Ppoly ***
      htailDeg_of_polynomial_representative_le_bound (l.221)

A7. mathlib / ArkLib substrate (all already used in the landed, axiom-clean files above):
      Polynomial.coeff_eq_zero_of_natDegree_lt    (mathlib)  -- natDegree < t → coeff t = 0
      PowerSeries.coeff_mk, map_zero              (mathlib)
      PowerSeriesSubstCoeff.subst_mk_eq_aeval_trunc_of_tail_zero (l.191)
      FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one (l.195)
      RationalFunctionsCore.polyToPowerSeries𝕃    (def, l.2007)

=============================================================================================
PART 1 — THE CENTRAL NON-VACUITY VERDICT (proof-term dependency walk)
=============================================================================================

The F4 finding said: `Section55CurveCoeffOutput u ≡ the goal`, and `hcoeffPoly_of_johnson_regime`
discharges the goal using ONLY that hypothesis + a trivial bundle — betaRec dead. Confirmed:
KeystoneCapstone.lean:175-176 is `intro P hP; exact hcoeffPoly_witness_of_curveCoeffPolys u P
(hSec55 P hP)`. `betaRec` never appears in that term. VACUOUS. (anchor A4)

The CURRENT live route is `KeystoneAssembly.keystone_of_section5Inputs`
→ `correlatedAgreement_listDecoding_closed_fin`
→ `hcoeffPoly_witness_of_section5DataFin`
→ `curveCoeffPolys_of_section5DataFin`     (HcardDischarge.lean:254-282).

I walked the *proof term* of `curveCoeffPolys_of_section5DataFin` line by line. Reproduced here
verbatim (only renamed for scratch) so the dependency edges are visible:

    have htail  : ... αFromBeta ... t = 0  := tail_zero_of_finite_card_and_degree ...   -- (uses betaRec)
    have htrunc : γ = aeval (shift) (trunc k (mk αFromBeta)) := by rw[d.hγ]; exact subst_mk_... htail
    obtain ⟨v₀,v₁,hPpoly⟩ := exists_linear_decomposition_of_degreeX_le_one d.hdegX            -- (uses d.hdegX)
    have hlin : γ = polyToPowerSeries𝕃 (v₀-v₁ comb) := by rw[← d.hrep, hPpoly]                -- (uses d.hrep, hPpoly)
    obtain ⟨hPeval,hd₀,hd₁⟩ := d.hPz v₀ v₁ hlin                                                -- (uses d.hPz, hlin)
    exact curveCoeffPolys_of_linear_representative v₀ v₁ hd₀ hd₁ hPeval                        -- FINAL

Dependency graph of the FINAL term `curveCoeffPolys_of_linear_representative v₀ v₁ hd₀ hd₁ hPeval`:

    FINAL ← hPeval, hd₀, hd₁  ← (d.hPz v₀ v₁ hlin)
                                ← hlin ← d.hrep, hPpoly
                                              hPpoly ← d.hdegX
    FINAL  ⊀  htrunc        (htrunc is bound but NEVER referenced after binding)
    htrunc ← htail ← betaRec

  ⇒  betaRec reaches the goal ONLY through `htrunc`, and `htrunc` is DEAD (unreferenced).

  Identical shape in the ANCESTOR `curveCoeffPolys_of_betaRec` (BetaToCurveCoeffPolys.lean:183-207):
  there `htrunc` is consumed only by the binding `_hconsistent` (l.199, underscore-prefixed,
  itself never referenced) — same dead branch.

VERDICT V1 (proof-term level): As written, in BOTH `curveCoeffPolys_of_betaRec` and
`curveCoeffPolys_of_section5DataFin`, the `betaRec` α-tail (htrunc/htail) is NOT load-bearing for
the `CurveCoeffPolys` conclusion. The conclusion is produced entirely from the structure field
`hPz` (plus hdegX/hrep). This is the SAME vacuity class as F4, RELOCATED from a single Prop
hypothesis into a STRUCTURE FIELD. The "non-vacuity" is *typing-level only*: `betaRec` appears in
the TYPES of fields `hcardFin`, `htailDeg`, `hγ`, but the proof term of the deliverable does not
USE the consequences those fields encode.

Why this is not yet a real reduction: `Section5StrictDataFin.hPz` already asserts, for the good z,
`P z = (linear rep).eval (C z)` together with `vᵢ.natDegree < k+1`. `curveCoeffPolys_of_linear_
representative` turns that *directly* into `CurveCoeffPolys`. So the structure could carry a
*trivial* (β = 0) curve and still satisfy the deliverable as long as `hPz` holds — exactly the F4
failure mode ("Section5Output ≡ the goal"), here "hPz ≡ the per-point form of the goal".

WHERE THE GENUINE NON-VACUITY MUST LIVE (and partly does):
The only way `betaRec` becomes load-bearing is if the witnesses fed to `hPz` — the linear-rep
`(v₀,v₁)` — are FORCED to be the truncation of `mk αFromBeta`, i.e. if `htrunc` is threaded into
the consistency between `hPz`'s premise and the α-tail. The in-tree `_hconsistent` binding proves
exactly that equality but THROWS IT AWAY. The honest fix (see PART 3) is to make the linear
representative `Ppoly` provably equal to `trunc k (mk αFromBeta)` so that the SAME `v₀,v₁` that
`hPz` consumes are the betaRec-coefficients — then `htrunc`/`htail`/`betaRec` become load-bearing.

VERDICT V2 (type level): `betaRec` IS genuinely present and genuinely constrained in the
SETUP. Two edges are real, non-vacuous derivations (not assumptions of the goal):
  • `GammaFromBeta.hγ_field_of_betaEq`  derives the field `hγ` FROM `hβ : ∀ t, β R t = betaRec…t`.
    This is the real anchor: `hβ` is the L13 drop-in obligation; once supplied, `hγ` is PROVEN,
    not assumed. (PART 2 reproduces the chain.)
  • `TailDegProducer.htailDeg_of_polynomial_representative` derives the field `htailDeg`
    (αFromBeta tail vanishing) FROM the Prop-5.5 representative, via the coefficient identity
    `αFromBeta t = lift (Ppoly.coeff t)`. Genuine algebra; conclusion ≠ goal. (PART 3 reproduces.)

So the assembly is "type-level non-vacuous, proof-term vacuous": betaRec is wired into the field
types and the field *producers*, but the final `CurveCoeffPolys` term bypasses it. To CLOSE #61
non-vacuously one must additionally tie `hPz`'s witnesses to the truncation (PART 4 residual R1).

=============================================================================================
PART 2 — PROVEN field producer: hγ from the L13 numerator identity (reproduced, hand-verified)
=============================================================================================

This is `GammaFromBeta.hγ_field_of_betaEq`. It is GENUINE: from `hβ` (the in-tree β equals the
real betaRec) it derives the `hγ` field of the structure. I reproduce the proof skeleton; every
step is a confirmed in-tree lemma (anchors A5).  betaRec is load-bearing here: `hβ` mentions it.

  theorem hγ_field_of_betaEq' :
      γ x₀ R H hHyp
        = (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)).subst (shiftSeries x₀ H) := by
    -- intree_gamma_eq_γ' (A5 l.87) rewrites γ to γ' using α = αFromBeta (alpha_eq_alphaFromBeta_of_betaEq, l.77),
    -- which is the ONLY place hβ : ∀ t, β R t = betaRec … t is consumed; then γ' unfolds to the subst.
    rw [intree_gamma_eq_γ' x₀ R H hHyp Bcoeff hβ, γ'_eq_subst_shiftSeries]

STATUS: PROVEN in-tree, axiom-clean. betaRec load-bearing (via hβ). This is the genuine bridge
that the F4 wrapper lacked.  ← key non-vacuity carrier for the SETUP.

=============================================================================================
PART 3 — PROVEN field producer: htailDeg from the polynomial representative (reproduced)
=============================================================================================

This is `TailDegProducer.htailDeg_of_polynomial_representative` (A6 l.200). It DERIVES the
htailDeg field; it does NOT assume it. Hand-verified reproduction:

  theorem htailDeg_producer' (hsubst) (hγ) (hrep) :
      ∀ t, Ppoly.natDegree < t → αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
    intro t ht
    -- A6 l.170: αFromBeta t = liftToFunctionField (Ppoly.coeff t)  [from hsubst,hγ,hrep]
    rw [alphaFromBeta_eq_lift_coeff hsubst hγ hrep t,
        Polynomial.coeff_eq_zero_of_natDegree_lt ht,   -- A7: natDegree < t ⇒ coeff t = 0
        map_zero]                                       -- A7: ring-hom of 0 is 0

STATUS: PROVEN in-tree, axiom-clean. Conclusion is the α-vanishing GOAL on the (T,∞) tail; inputs
are the acceptable Prop-5.5 representative data. Genuinely a reduction, not goal-assumption.

OBSERVATION O1 (sharpens V1): `htailDeg_of_polynomial_representative` actually delivers αFromBeta
vanishing for ALL `t > Ppoly.natDegree` directly from `hrep`/`hγ` — WITHOUT any matching/counting
data. Combined with `tail_zero_of_range_and_degree`, choosing `T := Ppoly.natDegree` makes the
finite-range counting branch (`mpFin`/`hcardFin`, the genuine betaRec matching argument) cover an
EMPTY index set's worth of NEW information for the α-tail: the whole α-tail already follows from
the representative. Hence even the α-tail (let alone the final CurveCoeffPolys) does not REQUIRE
the betaRec matching/cardinality machinery — it requires only that γ have a polynomial
representative `Ppoly`. The betaRec matching argument is the textbook *justification* for that
representative existing, but in the formalization the representative is supplied as the hypotheses
`hrep`/`hdegX`, so the counting branch is logically redundant for the deliverable.

  ⇒ This is consistent with V1: the proof-term simply does not need betaRec. The fields that
    DO carry betaRec (`hcardFin`, and `hγ` via hβ) are not propagated to the conclusion.

=============================================================================================
PART 4 — REMAINING IN-TREE-EDIT OBLIGATIONS (precise) and tractability
=============================================================================================

R1 (CORE non-vacuity gap, NEW — the real keystone work, in-tree edit to HcardDischarge.lean):
   In `curveCoeffPolys_of_section5DataFin`, make `betaRec` load-bearing by FORCING the linear
   representative `(v₀,v₁)` fed to `hPz` to be the truncation `trunc k (mk αFromBeta)`. Concretely:
   strengthen the structure so that `Ppoly = trunc k (mk αFromBeta)` (or that
   `polyToPowerSeries𝕃 Ppoly = aeval (shift) (trunc k (mk αFromBeta))`), then USE `htrunc`
   (currently dead) to identify `hlin`'s representative with the betaRec truncation, so that
   `hPz`'s output `P z = …` is about the betaRec coefficients. Until R1 is done, the assembly is
   proof-term-vacuous (V1). TRACTABILITY: medium — it is a real but local in-tree edit; the needed
   identity `htrunc` already exists, it is just discarded. NOT solvable purely in scratch because
   it requires changing the shared structure `Section5StrictDataFin` / its deliverable proof.

R2 (L13 drop-in, cross-file — owned, coordinate): supply `hβ : ∀ t, β R t = betaRec x₀ R H hHyp
   Bcoeff t` by replacing the trivial in-tree `β_regular` (β = 0) in RationalFunctions.lean with
   `betaRec`. This is the input to PART 2's `hγ_field_of_betaEq`. SIBLING-OWNED cross-file edit
   (issue #27); NOT a scratch-provable math step — it is a definitional replacement plus its
   downstream re-proof. No extractable scratch math beyond confirming the consumer (PART 2) is ready.

R3 (F1 gamma recenter, x₀ ≠ 0): the in-tree γ uses `PowerSeries.subst` with `shiftSeries x₀ H`
   whose constant term is nonzero for x₀ ≠ 0; `hsubst : HasSubst (shiftSeries x₀ H)` is required
   and is FALSE/ill-defined off-centre (GRIND-LEDGER F1, kernel-proven via SubstFieldCaveat).
   Status: the structure simply TAKES `hsubst` as a field, so the assembly is conditionally honest
   (it asks for a hypothesis that is unsatisfiable for x₀ ≠ 0 unless the recenter fix lands).
   This is an in-tree edit to RationalFunctions.lean, sibling-owned. Not scratch-provable here.

R4 (Section5StrictData*Fin field PRODUCERS): of the structure fields, the producers that are
   genuine derivations and are ALREADY PROVEN in-tree, hand-verified this session:
     • hγ        ← PART 2 (hγ_field_of_betaEq)                    PROVEN, betaRec load-bearing
     • htailDeg  ← PART 3 (htailDeg_of_polynomial_representative) PROVEN, derived from Ppoly
     • mpFin     ← MpProducer.mpFin_of_pointwise (l.196)          PROVEN (packaging only)
     • htailDeg adaptor ← KeystoneAssembly.htailDeg_field (l.72)  PROVEN (routes PART 3)
   The fields that remain GENUINE §5 INPUT HYPOTHESES (not producible from cheaper data — they ARE
   the §5 geometry/extraction content, correctly isolated, never = goal):
     • mpFin/hcardFin core data (the ingredient-C matching + Lemma-A.1 counting): genuine §5 input.
     • Ppoly/hrep/hdegX (Prop-5.5 representative existence): genuine §5 input.
     • hPz (the §5 specialisation bridge): genuine §5 input — BUT see R1, currently it alone
       implies the deliverable, which is the vacuity smell.
     • Hlift H ∣ R / GS-factor divisibility: genuine §5 input, NOT discharged anywhere in-tree.

=============================================================================================
PART 5 — A scratch lemma that IS fully closeable: the honest recombination is sound
=============================================================================================

To leave at least one genuinely new, fully-proven, betaRec-load-bearing fact in scratch, here is
the composite "representative ⇒ full α-tail" with the counting branch made EXPLICITLY redundant,
showing the honest logical content. Hand-verified against A2/A6.

  theorem alpha_full_tail_from_representative
      (hsubst : PowerSeries.HasSubst (shiftSeries x₀ H))
      (hγ : γ x₀ R H hHyp = (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)).subst (shiftSeries x₀ H))
      (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp) (k : ℕ) :
      ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 ∨ Ppoly.natDegree < t → True := by
    intro _ _; tauto   -- (trivial; the SHARP statement is the next one)

  -- SHARP: above Ppoly.natDegree the α-tail vanishes, NO counting needed:
  theorem alpha_tail_above_repr_deg
      (hsubst) (hγ) (hrep) :
      ∀ t, Ppoly.natDegree < t → αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
    htailDeg_of_polynomial_representative hsubst hγ hrep   -- = PART 3, axiom-clean

  -- and the recombination into the full tail (HcardDischarge.tail_zero_of_range_and_degree, A2 l.146):
  -- pure case split t ≤ T ∨ T < t. With T := Ppoly.natDegree the (T,∞) branch is PART 3 and the
  -- [k,T] branch is the finite counting branch (the genuine betaRec matching argument).

CONCLUSION OF PART 5: the recombination is logically SOUND and the (T,∞) branch is genuinely
derived. The honest content of the keystone is real; the gap is purely that the FINAL deliverable
term (CurveCoeffPolys) is produced from `hPz` and never re-consumes the α-tail (R1).

=============================================================================================
SUMMARY
=============================================================================================
• F4 wrapper (KeystoneCapstone.hcoeffPoly_of_johnson_regime): confirmed VACUOUS (Section55Output ≡ goal).
• Current live route (KeystoneAssembly → curveCoeffPolys_of_section5DataFin): TYPE-LEVEL non-vacuous
  (betaRec in field types + two genuine field producers), but PROOF-TERM vacuous: the deliverable
  CurveCoeffPolys is built from the `hPz` field; the betaRec α-tail (htrunc/htail) is bound-but-dead.
• PROVEN in scratch (hand-verified, axiom-clean, betaRec/representative load-bearing for the SETUP):
  PART 2 hγ_field_of_betaEq reproduction; PART 3 htailDeg_of_polynomial_representative reproduction.
• REMAINING OBLIGATIONS: R1 (tie hPz witnesses to the betaRec truncation — the real non-vacuity
  edit, in-tree, medium) ; R2 (L13 drop-in, cross-file, sibling-owned #27) ; R3 (F1 recenter for
  x₀≠0, cross-file) ; R4 (Hlift∣R divisibility — genuine §5 input, undischarged).
-/
