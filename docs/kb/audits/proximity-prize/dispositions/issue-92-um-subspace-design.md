# Issue #92 disposition — ABF26 T2.18/DA.7 UM subspace-design half (CLOSED 2026-06-06)

**Scope:** add the UM / derivative-coded `D_ux` Lean API and prove the UM subspace-design half of
ABF26 Theorem 2.18 — to the same standard as the FRS half (not as paper prose / an external `Prop`).

**Resolved (verify-and-close).** `ArkLib/Data/CodingTheory/SubspaceDesign.lean` (commit
`6aabd417e` "Resolve #92: Add UM codes to SubspaceDesign"):

- `D_ux` — the univariate-multiplicity derivative-coded evaluation operation (`UM[F,L,k,s]`).
- `umCode domain k s` — the UM code as `(degreeLT F k).map (D_ux domain s)`.
- `um_is_subspaceDesign_gk16` — the UM half: `umCode` is a `τ`-subspace-design for
  `τ(r) = (k-1)/n` on `[s]` (and `1` off it), **conditional on `GK16DegreeBudget k s (umCode …)`**,
  which is the SHARED degree-budget residual the FRS half is also conditional on. The proof is the
  per-coordinate `Aᵢ := A ⊓ ker(evalᵢ)` budget-division argument (real `Submodule.finrank`
  reasoning, `k=0`/off-range edge cases handled), not an external endpoint.

This brings the UM half to exact parity with the FRS half (`frs_is_subspaceDesign_gk16`), which #92
asked for.

**Verification (rc2 olean snapshot, `LEAN_PATH`):** `um_is_subspaceDesign_gk16` elaborates green,
axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

**Remaining (out of #92's scope):** `GK16DegreeBudget` is the shared GK16 degree-budget residual
(both FRS and UM are conditional on it); discharging it is the broader GK16/vector-space work, not
#92's deliverable. #92's own deliverable — the UM API + the UM design half at FRS parity — is
complete.
