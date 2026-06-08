# BCIKS20 §5 + Appendix-A coefficient extraction — complete mathematical roadmap

Date 2026-06-07. Research note: the full proof structure behind the open lattice/Hensel
residuals (#8 `Claim57Residuals`, #9 `βHensel`/Faà-di-Bruno, #64 `BoundaryCardLatticeData`).
Build-independent; reconstructs the math so the swarm can target the genuine open cores.

## Goal of the chain

For the affine-curve correlated-agreement keystone `correlatedAgreement_affine_curves`, the
remaining boundary obligation (`BoundaryCardLatticeResidual`, δ = 1−√ρ, δn ∈ ℕ) reduces — via
the PROVEN bridge `boundaryCardLatticeResidual_of_lattice_data` (BoundaryDischarge.lean:343) —
to `BoundaryCardLatticeData`: from a large good-coefficient set `Z` produce
1. `|Z| > k`,  2. `|Z| ≥ (n+1)k`,
3. **coefficient extraction**: low-degree `B_j` (deg < k+1) with `(P_z).coeff j = B_j(z)` ∀z∈Z.

The bridge (item 3 ⟹ jointAgreement) is the curve-to-stack identity: for a coord `i` in the
common agreement domain (≥(n+1)k pigeonholes a (1−δ)n domain shared by ≥k+1 values of z), the
two degree-k z-polynomials `z ↦ Σ_t z^t u_t(i)` and `z ↦ Q(z, domain i)` agree at >k points,
hence are equal, pinning `u_t(i) = coeff_{z^t} Q(z, domain i)`. So **item 3 is the open core**;
it IS the bivariate low-degree explanation of the close curve words.

## The genuine open core = BCIKS20 §5 (Guruswami–Sudan) + Appendix A (Hensel)

### Claim 5.7 (#8 `Claim57Residuals`): interpolation + large common-root set
Build a nonzero trivariate `Q(Z,X,Y)` (the `ModifiedGuruswami m n k ωs Q u₀ u₁` solution)
vanishing with multiplicity on the agreement graph `{(z, ω_i, curveword_i) : z∈Z, i∈A_z}`.
Existence is linear algebra: # constraints `≈ |Z|·|A_z|` vs # monomials governed by the
weighted degree budget `D_X, D_Y, D_YZ`; the `hlarge` inequality
`|coeffs|/deg_Y Q > 2·D_Y²·D_X·D_YZ` is exactly "more agreement than budget" so a common
factor survives. Residual data isolated by `GraphExtractionHypotheses`:
- `hx0`: `evalX(C x₀) R ≠ 0` (genericity — x₀ avoids the finitely many roots of the leading
  coeff / resultant; a good x₀ exists once |F| exceeds that finite bad set);
- `hsep`: `(evalX(C x₀) R).Separable` (genericity — x₀ avoids the discriminant's roots);
- `hA, hcount`: the per-z agreement set `A z` with `weightedDeg(eval_Z Q z) < m·|A z|`
  (forces `eval_Z Q z` to vanish identically on the agreement ⟹ `R(z,·,P_z)=0`);
- `hlarge`: the counting inequality above (Claim 5.7's cardinality bound).
**Open content**: the two genericity facts (`hx0`,`hsep`) — a counting argument that the bad
x₀-set is finite and `< |F|` — plus the multiplicity/weighted-degree vanishing `hcount`.

### Claim 5.8–5.11: from the common factor to the coefficient polynomials
The surviving irreducible factor `H | evalX(C x₀) R` has the specialized words `P_z(x₀)` as a
common root for ≥ (large) many z. `H`'s `Y`-degree-1 part defines, over the function field
`𝕃 = Frac(F[X][Y]/H)`, a single algebraic function `Y = γ(X)` interpolating all the `P_z`.
Its `X`-Taylor coefficients are the candidate `B_j`. This is where Appendix A enters.

### Appendix A (#9 `βHensel` / Faà-di-Bruno): the lift is EXACT
`Q(X,Y)` (the bivariate from the specialization) has a power-series root `γ ∈ 𝕃⟦X⟧` with
`constantCoeff = α₀ = T/W`. Two constructions:
- `gammaGenuine` — THE Newton/Hensel root, with `eval gammaGenuine Q = 0` PROVEN
  (`gammaGenuine_root`, GammaGenuine.lean).
- `βHenselAssembled` — the (A.1) recursion `βHensel_succ`: the order-(k+1) coefficient is
  `−Σ_{i1,λ} W𝒪^{i1+δsave−1}·ξ^{2i1+σλ−2}·B_coeff·∏_l β_l^{λ_l}` (the Faà-di-Bruno partition
  sum that cancels the order-(k+1) obstruction).

The residual `FaaDiBrunoSuccSumZeroResidual` ≡ `coeff_{t+1}(eval βHenselAssembled Q) = 0 ∀t`
≡ `βHenselAssembled = gammaGenuine`. By `coeff_eq_gammaGenuine_of_root` this is a clean STRONG
INDUCTION (NOT circular): assuming `coeff_s βHensel = coeff_s gammaGenuine ∀s≤t`, the order-(t+1)
match holds **iff the βHensel_succ sum equals the Newton step** — i.e. the proven Faà-di-Bruno
expansion `coeff_eval_Q_faaDiBruno` (countPerms/valueMultiset form) equals the `βHensel_succ`
form (B_coeff/partitionProd/W𝒪-ξ-weight form). This per-order identity is the **sole open
content of #9** (the "combinatorial-weight reconciliation"): a two-encoding equality of the
same Faà-di-Bruno coefficient. The file notes the loose IH is insufficient — it needs the
structured `α_t/β_t` weight invariant (the `W𝒪^{i1+δsave−1}·ξ^{2i1+σλ−2}` prefactor matched
against `countPerms`·`liftToFunctionField` term by term).

## Dependency / priority summary
`#9 βHensel exactness` (per-order weight identity) → exact `B_j` → `#8 Claim 5.7` genericity
(`hx0`,`hsep`,`hcount`) → `BoundaryCardLatticeData` item 3 → (proven bridge) →
`BoundaryCardLatticeResidual` → `correlatedAgreement_affine_curves` boundary keystone.
The two narrowest genuinely-open bricks are: (a) the #9 per-order Faà-di-Bruno weight identity
(self-contained algebra over 𝒪/𝕃), and (b) the #8 genericity counting (`x₀` avoids a finite
bad set). Both are finite/algebraic in nature — not analytic — and are the highest-leverage
targets for closing the boundary keystone.
