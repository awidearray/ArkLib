# Keystone integration — list-decoding branch closure (2026-06-05)

> Historical note (superseded as current inventory, 2026-06-06): this records one isolated
> integration attempt. It is useful provenance, but current residual ownership lives in
> `../CURRENT-RESIDUALIZED-TREE-2026-06-06.md` (issue map now spans #6-#59).

Isolated worktree: `/home/shaw/arklib-integrate` (detached HEAD `2db3e2da`, branch
`proximity-tomathlib-artifacts`), own hardlinked `.lake`. Shared submodule checkout never touched.
Compiled with plain `lean` + explicit `LEAN_PATH` (NOT `lake env`, which re-resolves the manifest and
deleted/re-cloned `CompPoly`, breaking the search path — restored from base, see method below).

Compile method (no churn):
```
cd /home/shaw/arklib-integrate
export LEAN_PATH="$(cat /tmp/arklib_leanpath.txt)"   # all .lake/packages/*/.lake/build/lib/lean + ArkLib build
lean <file>                                          # or: lean -o .lake/build/lib/lean/<path>.olean <src>
```

## Deliverable
`ArkLib/ToMathlib/CorrelatedAgreementListDecodingClosed.lean` —
`ArkLib.CorrelatedAgreementListDecodingClosed.correlatedAgreement_affine_curves_listDecoding_closed`.

Conclusion: literally the keystone goal
`δ_ε_correlatedAgreementCurves … (ε := errorBound δ deg domain)`.

`#print axioms` = `[propext, Classical.choice, Quot.sound]`  (NO sorryAx). Kernel-clean.

Wiring (all genuine, `betaRec` in the proof term via `curveCoeffPolys_of_betaRec`):
```
Section5StrictData u P
  ─ BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec ─►  CurveCoeffPolys k deg (RS_goodCoeffsCurve…) P
  ─ KeystoneCapstone.hcoeffPoly_witness_of_curveCoeffPolys ─►  ∃ B:ℕ→F[X], (∀ j<deg, deg<k+1) ∧ …
  ─ RS_jointAgreement_of_prob_gt_strict_johnson_and_coeff_polys (Curves:1459, front door) ─►  jointAgreement
  ─ correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary (Curves:1720) ─►  goal
```

## Did Curves.lean:1819 close sorry-free?
NO — and it CANNOT against this base without either (a) changing the public signature of
`correlatedAgreement_affine_curves` (rejected: live downstream consumers — `Combine.lean:590`,
`Folding.lean:858`, `AffineLines/Main.lean:43`), or (b) closing the open §5 list-decoding math.
The original keystone is unchanged and still `[propext, sorryAx, Classical.choice, Quot.sound]`.

The closed result is delivered as the standalone theorem (task Step-1 fallback), which is a verified
**drop-in**: see `probe_correlatedAgreement_closed_dropin.lean`
(`ProbeKeystone.correlatedAgreement_affine_curves_closed`, axioms
`[propext, Classical.choice, Quot.sound]`) — identical statement to the keystone plus exactly the two
residual hypotheses below, nothing else.

## Exact remaining residual hypotheses (smallest, explicit, never sorry/axiom)
1. `hExtract` — per-decoding §5 extraction:
   `∀ u, hprob → hJ → (δ<1−sqrtRate) → ∀ P, (P good on RS_goodCoeffsCurve) → Section5StrictData u P`.
   `Section5StrictData u P` is a `Type`-valued bundle of EXACTLY the inputs of
   `curveCoeffPolys_of_betaRec`: the App-A.4 centre/curve data `(x₀,R,H,Bcoeff,D)`, ingredient-C
   matching `(matchingSet, root, mp, hcard)`, substitution validity `hsubst`, Claim-5.9 form `hγ`,
   Prop-5.5 representative `(Ppoly,hrep,hdegX)`, specialisation bridge `hPz`. NONE is the per-coefficient
   conclusion (that is derived). This is the genuine open §5 list-decoding extraction.
2. `hBoundary` — closed square-root boundary discharge
   `∀ hk u, hprob → hJ → ¬(δ<1−sqrtRate) → jointAgreement`. In-tree gives only
   `0 < (RS_goodCoeffsCurve…).card` (`goodCoeffsCurve_card_pos_of_prob_gt_closed_sqrt_boundary`);
   reaching `jointAgreement` there needs the same §5 input, so it stays explicit.

(The unique-decoding regime and the `¬hJ` rate-half branch are already proven in-tree; not residual.)

## L13 / F1
- L13 (replace trivial `β_regular := fun _ => ⟨0,by simp⟩` with `betaRec` in `RationalFunctions.lean`):
  NOT done — `RationalFunctions.lean` is live-session-owned and the signature change cascades through
  R/H/Claims/Agreement. The standalone closed keystone deliberately avoids this edit; it routes the
  genuine `betaRec` brick (`curveCoeffPolys_of_betaRec`) directly, which is the honest equivalent
  without destabilising the shared file.
- F1 (`subst(X−x₀)` ill-defined for x₀≠0): carried as the documented setup hypothesis
  `Section5StrictData.hsubst : PowerSeries.HasSubst (shiftSeries x₀ H)` (automatic for x₀=0).

## stir / whir soundness — de-tainted?
NO. `StirIOP.stir_rbr_soundness` and `WhirIOP.whir_rbr_soundness` are still
`[propext, sorryAx, Classical.choice, Quot.sound]`. Two reasons:
(1) they transitively depend on `correlatedAgreement_affine_curves` (line-1819 sorry, unchanged);
(2) they ALSO have their OWN independent sorries — `MainThm.lean:243` (in `stir_rbr_soundness` itself),
`MainThm.lean:151`, `ProximityGap.lean:83`, `RBRSoundness.lean:259` (in `whir_rbr_soundness` itself).
So closing the keystone alone would NOT de-taint them; that is separate downstream work.

## Files
- `CorrelatedAgreementListDecodingClosed.lean` — the deliverable (also at
  `/home/shaw/arklib-integrate/ArkLib/ToMathlib/CorrelatedAgreementListDecodingClosed.lean`).
- `probe_correlatedAgreement_closed_dropin.lean` — drop-in equivalence probe, kernel-clean.
- `final_axiom_audit.lean` — the consolidated `#print axioms` script.
