# Grand Proximity Prize — remaining-residual dependency map

Date 2026-06-07. Research synthesis across all open proximity issues. Identifies the two
mathematical clusters, their shared cores, and the narrowest genuinely-open bricks, so effort
can be concentrated on the keystones rather than spread across symptoms.

## Cluster A — proximity-gap GS-interpolation + Hensel core (gates 5 issues)

The affine-curve correlated-agreement keystone `correlatedAgreement_affine_curves` and every
boundary/Johnson MCA witness reduce to ONE piece of mathematics: **extract low-degree
coefficient polynomials `B_j(z)` from a large set of δ-close curve words** (the bivariate
low-degree explanation). See `bciks20-coefficient-extraction-roadmap-2026-06-07.md`.

Issues that are facets of this single core:
- **#8** `Claim57Residuals` — GS interpolation + large-common-root-set (Claim 5.7) + the
  genericity data (`hx0`: nonzero specialization, `hsep`: separability, `hcount`: weighted-
  degree vanishing).
- **#9** `βHensel` / `FaaDiBrunoSuccSumZeroResidual` — the lift is EXACT (the assembled (A.1)
  recursion root equals the genuine Newton root).
- **#64** `BoundaryCardLatticeData` item 3 — the SAME coefficient extraction at the Johnson
  lattice point δ=1−√ρ. The Data→jointAgreement bridge is PROVEN
  (`boundaryCardLatticeResidual_of_lattice_data`); only the extraction is open.
- **#61** keystone — INTEGRATION: `curveCoeffPolys_of_betaRec` wired through `Curves.lean`.
  Conditional on the same §5 setup/extraction; downstream of #8/#9.
- **#68** Hab25 Johnson-range MCA — the SAME GS interpolation but over `F(Z)`: degree/
  factorisation data, discriminant non-vanishing, Hensel uniqueness / affine-pair extraction.

### The two narrowest open bricks for ALL of Cluster A
1. **#9 per-order Faà-di-Bruno weight identity** — a two-encoding equality of the same
   order-(t+1) coefficient: `coeff_eval_Q_faaDiBruno` (countPerms/valueMultiset form) =
   `βHensel_succ` (B_coeff/partitionProd, `W𝒪^{i1+δsave−1}·ξ^{2i1+σλ−2}` weights). Self-
   contained finite algebra over 𝒪/𝕃; closes by strong induction once the per-order identity
   holds (NOT circular — via `coeff_eq_gammaGenuine_of_root`). Needs the structured `α_t/β_t`
   weight invariant, not a loose IH.
2. **#8 genericity counting** — a good specialization `x₀` exists because the bad set (roots of
   the leading coeff/resultant for `hx0`, of the discriminant for `hsep`) is finite and
   `< |F|`. Finite counting, not analysis.

Both are **finite/algebraic**, not analytic. Closing them collapses Cluster A's 5 issues.

## Cluster B — CA/MCA up to capacity (separate machinery)

List-decoding-to-correlated-agreement and capacity constructions. Distinct from Cluster A
(subspace designs, random coding, entropy — not GS+Hensel).
- **#74** ABF26 §3 remainder — T3.10 (AGL23 large-alphabet barrier: counting extraction +
  q-ary Plotkin, no in-tree analogue), T3.11 (GLMRSW22 random-linear first moment). NB: T3.12
  (BKR06) and T3.13 (GHSZ02) are PROVEN (closed #97/#98).
- **#75** ABF26 §4 — capacity CA/MCA families (CS25 entropy witness, BCHKS25 Johnson-jump,
  GG25 subspace-design), each external-construction-gated; the `_of_residuals` reductions are
  in-tree.
- **#94** CZ25 C3.5 — folded-RS capacity; reduces through T3.4 = `CZ25DimensionCount` =
  Guruswami–Wang iterative recentring (confirmed irreducible past Johnson; the naive
  disjoint double-count is FALSE, see CZ25SpanDimension kernel refutation).
- **#22** CS25/BCHKS/BGKS bridges + deep-hole probability.

## Cross-cutting — MCA first/second moment (#67)

Second moment `|Bad²| < 1/ε` is IN-TREE (Cauchy-Schwarz machinery in `GCXK25SecondMoment.lean`).
First moment: per-codeword `2δn` is worst-case TIGHT (see
`issue-67-first-moment-tightness-2026-06-07.md`); sharp `δn` is the GLOBAL/codeword-pair charge,
the sole open piece. Feeds the capacity MCA (Cluster B).

## Recommended priority
The single highest-leverage target is the **#9 per-order Faà-di-Bruno weight identity** —
finite algebra that, with the #8 genericity counting, unlocks the entire proximity-gap keystone
(Cluster A, 5 issues). Cluster B is a parallel, mostly-independent capacity track.
