# Issue #25 OracleReduction Residual Audit

Date: 2026-06-06

Scope: `ArkLib/OracleReduction/**` and `ArkLib/ProofSystem/Logup/**`, following the audit command
from <https://github.com/lalalune/ArkLib/issues/25>.

## Result

The old commented `placeholder` theorem skeletons in `Execution.lean` and `Cast.lean` are no longer
present in the current tree. The remaining sequential-composition and Fiat-Shamir run-equality
surfaces are not hidden `sorry`/`admit` placeholders:

- `OracleReduction/FiatShamir/DuplexSponge/Security/Completeness.lean` reduces unsalted and salted
  completeness to explicit run-equality hypotheses.
- `OracleReduction/Composition/Sequential/Append.lean` exposes append completeness/soundness,
  knowledge soundness, and round-by-round obligations as explicit residual hypotheses on the public
  theorem interfaces.
- `OracleReduction/Composition/Sequential/General.lean` exposes the n-ary `seqCompose_*` security
  front doors as explicit residual hypotheses, with the private `seqComposeError_eq_append`
  challenge-index bridge available for future binary-append reductions.
- `ProofSystem/Logup/Security/{Completeness,Soundness}.lean` consumes named LogUp subphase
  residual `Prop`s rather than relying on a hidden composition `sorry`.

## Audit Commands

```sh
rg -n 'append_completeness|append_soundness|run-equality|Residual|residual|placeholder|hEq := sorry|OptionT' \
  ArkLib/OracleReduction ArkLib/ProofSystem/Logup

rg -n '^--.*placeholder|by placeholder|hEq := sorry' \
  ArkLib/OracleReduction/Execution.lean \
  ArkLib/OracleReduction/Cast.lean \
  ArkLib/OracleReduction/Salt.lean
```

The second command reports only the historical `hEq := sorry` note in `Salt.lean`, which documents
why the unsalted projection construction cannot inhabit the old `OracleVerifier.addSalt` shape in
full generality. It is an audit note, not live placeholder code.

## Remaining Work

Issue #25's mathematical framework work is narrowed to proving the explicit residual hypotheses in
`Composition/Sequential/Append.lean`, discharging or reducing the n-ary `seqCompose_*` front doors in
`Composition/Sequential/General.lean`, and proving the Fiat-Shamir run equalities. The current tree
no longer contains stale commented `placeholder` theorem bodies for these obligations.
