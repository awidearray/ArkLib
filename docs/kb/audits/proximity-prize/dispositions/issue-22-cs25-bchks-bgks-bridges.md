STATUS: PARTIALLY CLOSED — CS25 deep-hole probability residual fully discharged in-tree (new `deepHoleProbResidual_holds`); BCHKS25/BGKS20 bad-line residuals are genuine external paper constructions, now marked EXTERNAL with issue links. Bridge algebra is proven and axiom-clean throughout.

# issue-22 — CS25/BCHKS/BGKS bridge residuals and deep-hole probability inputs

Tracking issue: lalalune/ArkLib#22

Files:
* `ArkLib/ToMathlib/CS25DeepHole.lean`
* `ArkLib/ToMathlib/CS25Claim3.lean`
* `ArkLib/ToMathlib/CS25Claim3Counting.lean`
* `ArkLib/ToMathlib/CS25DeepHoleFinish.lean` — defines `DeepHoleProbResidual`
* `ArkLib/ToMathlib/CS25DeepHoleFinish2.lean` — `deepHoleProbResidual_of_jointFar`, `DeepHoleJointFar`
* `ArkLib/ToMathlib/CS25JointFar.lean` — `deepHoleJointFar_holds`, **new** `deepHoleProbResidual_holds`
* `ArkLib/ToMathlib/Bridge2BCHKS25.lean` — `BadLineWitness`
* `ArkLib/ToMathlib/Bridge2BGKS20.lean` — `NearCertainBadLine`
* `ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean` — bridge consumers

## Finding

The issue asked for four things. On audit, the CS25 deep-hole probability residual was already
reduced to a proven minimum-distance argument; the two remaining named residuals are genuine
external paper theorems. Concretely:

### 1. Smallest remaining statement for `DeepHoleProbResidual` — CLOSED

`DeepHoleProbResidual domain k L δ ε u p` (the deep-hole distinct-value bound `numDistinct p a ≤ ε·q`
on the sampling set `T = F ∖ range domain`) is **fully discharged in-tree**, with the smallest
remaining input being the arithmetic rate condition `k < n − ⌊δ·n⌋` (the in-chain form of
`δ < 1 − k/n`), *not* a residual:

* `CS25DeepHoleFinish2.deepHoleProbResidual_of_jointFar` reduces it to the geometric joint-far
  property `DeepHoleJointFar` (not jointly `δ`-close deep-hole stack).
* `CS25JointFar.deepHoleJointFar_holds` proves `DeepHoleJointFar` outright via the minimum-distance
  argument: a common agreement set of size `> k` forces the degree-`≤ k` polynomial
  `(X − a)·q¹ − 1` to vanish on `> k` distinct points, hence to be zero, contradicting its value
  `−1` at `X = a`.
* **New this issue:** `CS25JointFar.deepHoleProbResidual_holds` composes the two into a single
  named result that instantiates `DeepHoleProbResidual` with no extra geometric/probabilistic side
  condition. This is the explicit answer to criterion 1.

The fully-discharged top-level list-size bound is
`CS25JointFar.rs_epsCA_implies_lambda_extended_cs25_complete` (its own axiom audit prints exactly
`[propext, Classical.choice, Quot.sound]`).

### 2. Proven bridge algebra vs external theorem content — SEPARATED

Each bridge file already isolates the proven ε-arithmetic / reduction plumbing from the external
geometric construction, now made explicit in module docstrings and at each residual definition:

* **BCHKS25** (`Bridge2BCHKS25.lean`): PROVEN — `ofReal_le_card_div_of_card_mul_le`,
  `epsCA_ge_inv_of_badLineWitness`, `epsCA_ge_half_inv_n_of_badLineWitness`,
  `epsCA_badLine_bridge_of_residual`, `hBadLine_of_provBadLine`. EXTERNAL — `BadLineWitness`.
* **BGKS20** (`Bridge2BGKS20.lean`): PROVEN — `ofReal_one_sub_inv_le_card_div`,
  `epsCA_ge_one_sub_inv_of_nearCertainWitness`, `epsCA_separation_bridge_of_residual`.
  EXTERNAL — `NearCertainBadLine`.

### 3. Explicit issue links / docstring markers — ADDED

Issue-#22 disposition markers added at:
* `DeepHoleProbResidual` (CS25DeepHoleFinish.lean) — marked CLOSED, with the discharge chain.
* `CS25Claim3.lean` module docstring — corrected the stale "genuinely external" framing of the
  `hDeepHole` step to point at the in-tree closure.
* `BadLineWitness` (Bridge2BCHKS25.lean) — marked EXTERNAL (BCHKS25 Theorem 1.9), with consumer.
* `NearCertainBadLine` (Bridge2BGKS20.lean) — marked EXTERNAL (BGKS20 Lemma 3.3).

### 4. Remaining external content — DOCUMENTED (open, not closeable in-tree)

`BadLineWitness` and `NearCertainBadLine` are the main geometric theorems of their source papers:

* **BCHKS25 Theorem 1.9** — affine-shift interpolation count turning `|F|` close codewords into a
  bad combining line. Requires a full port of the construction.
* **BGKS20 Lemma 3.3** — the characteristic-2 rate-`1/8` near-certain-bad-line construction.
  Requires a full port of the construction.

Neither is derivable from the in-tree `epsCA` / `Lambda` / `ReedSolomon` API; they fall in the
external-irreducible bucket tracked by #42. The in-tree ε-plumbing around both is proven and
axiom-clean, so once either construction is ported the corresponding ABF26 lower bound (Theorem 5.2
/ Theorem 5.4) closes immediately via the `_of_residual` connectors.

## Net change

* Added `CS25JointFar.deepHoleProbResidual_holds` (+ axiom-audit line) — direct, side-condition-free
  instantiation of `DeepHoleProbResidual`.
* Added Issue-#22 closure-status docstring markers at the three named residuals and the
  `CS25Claim3` consumer.
* No `sorry` introduced; no axioms beyond `[propext, Classical.choice, Quot.sound]`.
