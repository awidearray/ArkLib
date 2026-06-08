# Cluster B — CA/MCA up to capacity: math reductions (#74 §3 remainder, #75, #94, #22)

Date 2026-06-07. Companion to `proximity-prize-dependency-map-2026-06-07.md`. The capacity
track is mostly independent of the GS+Hensel proximity-gap core (Cluster A). Each item's exact
external content, and which are clean-closeable vs genuinely external.

## #74 ABF26 §3 remainder

T3.12 [BKR06] and T3.13 [GHSZ02] are PROVEN (closed #97/#98 — both reduced to finite
arithmetic / averaging, which is why they closed). The two remaining are NOT so reducible:

- **T3.10 [AGL23/BDG24] large-alphabet barrier.** External content `AGL23CountingExtraction`:
  a counting/descent extraction over linear codes + a **q-ary Plotkin bound** (no in-tree
  analogue). The pigeonhole interface is in-tree (`large_alphabet_barrier_of_counting`,
  `AGL23CountingProof.lean`); the extraction itself is the AGL23 §4 algorithm. Genuinely
  external (not finite-arithmetic).
- **T3.11 [GLMRSW22] random-linear lower bound.** Residual `0 < randomLinearLambdaLowerProbability`
  ⟺ a good generator matrix exists. Unlike GHSZ02's explicit averaging, this is a **probabilistic
  existence**: a specific bad configuration appears in a random linear code with positive
  probability (GLMRSW22's structured-subcode argument). The probability space is in-tree
  (`uniformRandomLinearGeneratorMatrix`); the positivity is the external first-moment count.
  NOT a clean averaging — genuinely external.

## #94 CZ25 C3.5 folded-RS capacity list decoding

Reduces (in-tree) through T3.4 `subspaceDesign_list_decoding_cz25` =
`CZ25DimensionCount`. The dimension count IS the **Guruswami–Wang iterative recentring** —
confirmed IRREDUCIBLE past the Johnson radius: the naive disjoint double-count is mathematically
FALSE (agreeing list elements fill an affine flat of size `q^dim`, not `dim+1`; documented as a
kernel refutation in `CZ25SpanDimension.lean`, see the #93 analysis I posted). So C3.5's open
core is the genuine GW recentring/charge, a research result with no shortcut. The greedy
disjoint-cover bound does NOT apply here for the same reason.

## #75 ABF26 §4 capacity CA/MCA families

Each headline is `def : Prop` with an in-tree `_of_residuals` reduction; the external piece is
the **construction** behind each residual:
- CS25 T4.17 — qEntropy / RS-ball-count lower witness (entropy-rate construction).
- BCHKS25 T4.18 — char-2 Johnson-jump witness family.
- BCHKS25 T4.12 — Johnson-range RS epsMCA (Hab25 algebraic core, = Cluster A's GS-over-F(Z), #68).
- GG25 T4.13/T4.14 — subspace-design + folded-RS MCA up to capacity (GK16/CZ25 design input).
- GKL24/BGKS20 T4.11 — 1.5-Johnson CA/MCA (the witness/connector bridges are in-tree).
These are external constructions; the reductions/wrappers are done. NB T4.12 (#68) loops back to
Cluster A's GS interpolation over `F(Z)`.

## #22 CS25/BCHKS/BGKS bridge residuals + deep-hole probability

Bridge residuals between the §5 proximity-gap outputs and the capacity statements, plus the
deep-hole probability inputs (the probability that a random point is a deep hole / far from the
code). The deep-hole probability is an entropy/volume estimate; the bridges are reductions.

## Closeability assessment
- **Clean-closeable (finite-arithmetic / averaging):** NONE remain — T3.12/T3.13 were the last,
  and are closed.
- **Genuinely external constructions:** T3.10 (q-ary Plotkin + extraction), T3.11 (random-linear
  probabilistic), CS25/BCHKS25/GG25 capacity witnesses.
- **Loops into Cluster A:** T4.12 / #68 (GS over `F(Z)`) — closing Cluster A's coefficient
  extraction also advances these.

## Conclusion
The capacity track has no finite-arithmetic front doors left; its residuals are external
research constructions OR loop back to the Cluster-A GS+Hensel core. The single highest-leverage
target across BOTH clusters remains the Cluster-A coefficient extraction (the #9 Faà-di-Bruno
weight identity + #8 genericity), which also unlocks #68/T4.12 in Cluster B.
