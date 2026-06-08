/-! # PARKED MODULE (#60, NAMED-RESIDUAL convention)

This module (landed by PR #532) targets a PolyFun API that was since redesigned
(`Spec.Strategy.withRoles` / `Spec.Counterpart` / `Spec.PublicCoinCounterpart` moved to the
`SyntaxOver`/`ShapeOver`/`StrategyOver.TwoParty` forms, PolyFun `5d3a160`).  Nothing in ArkLib
imports it.  Parked to keep the root build green; un-park by migrating to the Over-style API
(see issue #60 for the full diagnosis). -/

/-
/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
 -/
import ArkLib.Interaction.Reduction
import ArkLib.Interaction.Oracle.Spec
import PolyFun.Interaction.TwoParty.Refine

/- !
# Oracle Decoration, Oracle Verifiers, and Oracle Reductions

This module bridges the generic `Interaction.Spec` layer with VCVio's oracle
computation model. It introduces:

- `OracleDecoration` — per-node attachment of `OracleInterface` instances at
  sender nodes, specifying how prover messages can be queried as oracles.
- `OracleDecoration.QueryHandle` — an index type for oracle queries, parameterized
  by a transcript (the transcript determines the path through the interaction tree,
  and hence which oracle interfaces are available).
- `OracleDecoration.toOracleSpec` — the VCVio `OracleSpec` for querying sender
  messages along a given transcript path.

- `OracleDecoration.toMonadDecoration` — bridge from oracle decoration to per-node
  `MonadDecoration`: sender nodes get `Id`, receiver nodes get `OracleComp`.
- `OracleDecoration.liftOutput` — converts oracle-spec-indexed output to
  transcript-indexed output by threading the accumulated spec.
- `OracleCounterpart` — round-by-round challenger with growing oracle access,
  unified as `Counterpart.withMonads` via `toMonadDecoration`.
- `InteractiveOracleVerifier` — a transcript-indexed challenger whose terminal
  output is a verification function.
- `OracleVerifier` — statement-indexed verifier-side interaction together with
  statement/transcript-dependent oracle simulation.
- `OracleProver` / `OracleReduction` — prover and reduction with oracle statements,
  using the full dependency chain.

## Path-dependent oracle access

In a W-type interaction spec, move types at each node depend on prior moves.
Consequently, the oracle interfaces available to the verifier depend on the
actual transcript. This is reflected in the type of `toOracleSpec`: it takes a
`Transcript` and produces an `OracleSpec` over `QueryHandle` for that specific
path.

## Unification with `Counterpart.withMonads`

`OracleCounterpart` is defined as `Counterpart.withMonads` with a
`MonadDecoration` computed from the oracle decoration via `toMonadDecoration`.
Sender nodes use `Id` (pure observation, `Id α = α` definitionally) and receiver
nodes use `OracleComp` with the current accumulated oracle access. This means all
generic `Counterpart.withMonads` composition combinators automatically apply to
oracle counterparts.

## Universe constraints

The oracle decoration layer (`OracleDecoration`, `QueryHandle`,
`toOracleSpec`, `answerQuery`) is universe-polymorphic in its statement and
oracle families. The downstream verifier and reduction interfaces are also
polymorphic in their statement, witness, and oracle-family universes where the
underlying `Spec`, `Counterpart.withMonads`, and `OracleComp` interfaces permit
it.

## See also

- `Oracle/Continuation.lean` — intrinsic oracle composition, shared-input
  reindexing, and `Chain`
- `Oracle/Composition.lean` — append-level oracle composition infrastructure
- `Oracle/StateChain.lean` — N-ary state chain composition for oracle reductions
- `OracleReification.lean` — optional concrete oracle materialization
- `OracleSecurity.lean` — completeness, soundness, knowledge soundness
 -/

universe u v w

open OracleComp OracleSpec

namespace Interaction

/- ! ## Oracle decoration

`OracleDecoration` is a `Role.Refine` specialized to `OracleInterface`:
it carries an `OracleInterface X` at each sender node and recurses directly
at receiver nodes (no junk data).  -/

/- - An `OracleDecoration` assigns an `OracleInterface` instance (as data, not a
typeclass) to each sender node. Defined as `Role.Refine OracleInterface`.  -/
abbrev OracleDecoration (spec : Spec) (roles : RoleDecoration spec) :=
  Interaction.Role.Refine OracleInterface spec roles

/- - Oracle-statement data for an indexed oracle-statement family.  -/
abbrev OracleStatement {ιₛ : Type v} (OStmt : ιₛ → Type w) :=
  ∀ i, OStmt i

/- - A local statement bundled with oracle-statement data for a fixed ambient
input `i`. Used for both oracle inputs and oracle outputs.  -/
structure StatementWithOracles
    {Input : Type u}
    (LocalStmt : Input → Type v) {ιₛ : Input → Type v}
    (OStmt : (i : Input) → ιₛ i → Type w)
    (i : Input) where
  stmt : LocalStmt i
  oracleStmt : OracleStatement (OStmt i)

/- ! ## Query handles and oracle spec  -/

/- - Index type for oracle queries given a specific transcript path. At each
sender node, the verifier can either:
- query the current node's oracle interface (`.inl q`), or
- recurse into the subtree determined by the transcript move (`.inr h`).

At receiver nodes, there is no oracle to query, so we recurse immediately.

The transcript parameter ensures that the index type is well-typed: it
determines which subtree (and hence which oracle interfaces) are reachable.  -/
def OracleDecoration.QueryHandle :
    (spec : Spec) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    Spec.Transcript spec → Type
  | .done, _, _, _ => Empty
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, ⟨x, trRest⟩ =>
      oi.Query ⊕ QueryHandle (rest x) (rRest x) (odRest x) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, ⟨x, trRest⟩ =>
      QueryHandle (rest x) (rRest x) (odFn x) trRest

/- - The oracle specification for querying sender-node messages along a given
transcript path. Maps each `QueryHandle` to its response type.  -/
def OracleDecoration.toOracleSpec :
    (spec : Spec) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
    (tr : Spec.Transcript spec) → OracleSpec (QueryHandle spec roles od tr)
  | .done, _, _, _ => Empty.elim
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, ⟨x, trRest⟩ =>
    fun
    | .inl q => oi.toOC.spec q
    | .inr handle => toOracleSpec (rest x) (rRest x) (odRest x) trRest handle
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, ⟨x, trRest⟩ =>
      toOracleSpec (rest x) (rRest x) (odFn x) trRest

/- - Answer oracle queries using the message values from a transcript. At each
sender node, the transcript provides the actual move `x : X`, which is used as
the message argument to `OracleInterface`'s implementation.  -/
def OracleDecoration.answerQuery :
    (spec : Spec) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
    (tr : Spec.Transcript spec) →
    QueryImpl (toOracleSpec spec roles od tr) Id
  | .done, _, _, _ => fun q => q.elim
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, ⟨x, trRest⟩ =>
    fun
    | .inl q => (oi.toOC.impl q).run x
    | .inr handle => answerQuery (rest x) (rRest x) (odRest x) trRest handle
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, ⟨x, trRest⟩ =>
      answerQuery (rest x) (rRest x) (odFn x) trRest

/- - Answer queries to the combined oracle context consisting of the input oracle
statements and the sender-message oracles available along a transcript.  -/
def OracleDecoration.oracleContextImpl
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface.{0, u} (OStmtIn i)] :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) → (od : OracleDecoration.{0, 0} spec roles) →
    OracleStatement OStmtIn → (tr : Spec.Transcript spec) →
    QueryImpl ([OStmtIn]ₒ + toOracleSpec spec roles od tr) Id
  | spec, roles, od, oStmtIn, tr =>
      QueryImpl.add (OracleInterface.simOracle0 OStmtIn oStmtIn)
        (answerQuery spec roles od tr)

namespace OracleDecoration.QueryHandle

/- - Embed a first-phase query handle into the combined query-handle type for
`Spec.append`.  -/
def appendLeft :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    QueryHandle spec₁ roles₁ od₁ tr₁ →
    QueryHandle (spec₁.append spec₂) (Spec.Decoration.append roles₁ roles₂)
      (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
  | .done, _, _, _, _, _, ⟨⟩, _, q => q.elim
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q =>
      match q with
      | .inl q0 => .inl q0
      | .inr qRest =>
          .inr <| appendLeft (rest x) (fun p => spec₂ ⟨x, p⟩)
            (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
            tr₁Rest tr₂ qRest
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q =>
      appendLeft (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

/- - Embed a second-phase query handle into the combined query-handle type for
`Spec.append`.  -/
def appendRight :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    QueryHandle (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂ →
    QueryHandle (spec₁.append spec₂) (Spec.Decoration.append roles₁ roles₂)
      (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
  | .done, _, _, _, _, _, ⟨⟩, _, q => q
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q =>
      .inr <| appendRight (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q =>
      appendRight (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

theorem appendLeft_range :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (q : QueryHandle spec₁ roles₁ od₁ tr₁) →
    OracleDecoration.toOracleSpec (spec₁.append spec₂) (Spec.Decoration.append roles₁ roles₂)
      (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
      (appendLeft spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q) =
    OracleDecoration.toOracleSpec spec₁ roles₁ od₁ tr₁ q
  | .done, _, _, _, _, _, ⟨⟩, _, q => q.elim
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q => by
      cases q with
      | inl q0 => rfl
      | inr qRest =>
          simpa using appendLeft_range (rest x) (fun p => spec₂ ⟨x, p⟩)
            (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
            tr₁Rest tr₂ qRest
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using appendLeft_range (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

theorem appendRight_range :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (q : QueryHandle (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂) →
    OracleDecoration.toOracleSpec (spec₁.append spec₂) (Spec.Decoration.append roles₁ roles₂)
      (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
      (appendRight spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q) =
    OracleDecoration.toOracleSpec (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂ q
  | .done, _, _, _, _, _, ⟨⟩, _, _ => rfl
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using appendRight_range (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using appendRight_range (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

theorem answerQuery_appendLeft :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (q : QueryHandle spec₁ roles₁ od₁ tr₁) →
    cast (appendLeft_range spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
      (OracleDecoration.answerQuery (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
        (appendLeft spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) =
    OracleDecoration.answerQuery spec₁ roles₁ od₁ tr₁ q
  | .done, _, _, _, _, _, ⟨⟩, _, q => q.elim
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q => by
      cases q with
      | inl q0 =>
          rfl
      | inr qRest =>
          simpa using answerQuery_appendLeft (rest x) (fun p => spec₂ ⟨x, p⟩)
            (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
            tr₁Rest tr₂ qRest
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using answerQuery_appendLeft (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

theorem answerQuery_appendRight :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (q : QueryHandle (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂) →
    cast (appendRight_range spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
      (OracleDecoration.answerQuery (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
        (appendRight spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) =
    OracleDecoration.answerQuery (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂ q
  | .done, _, _, _, _, _, ⟨⟩, _, q => by
      rfl
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using answerQuery_appendRight (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using answerQuery_appendRight (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

end OracleDecoration.QueryHandle

section QueryRouting

variable {spec₁ : Spec} {spec₂ : Spec.Transcript spec₁ → Spec}
variable {roles₁ : RoleDecoration spec₁}
variable {roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)}
variable {od₁ : OracleDecoration spec₁ roles₁}
variable {od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)}
variable (tr₁ : Spec.Transcript spec₁) (tr₂ : Spec.Transcript (spec₂ tr₁))

/- - Route a first-phase transcript-message query into the appended transcript's
oracle specification. The only transport needed here is the response-type
equality witnessed by `QueryHandle.appendLeft_range`.  -/
def liftAppendLeftQuery :
    QueryImpl (OracleDecoration.toOracleSpec spec₁ roles₁ od₁ tr₁)
      (OracleComp
        (OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))) :=
  fun q =>
    let appendSpec :=
      OracleDecoration.toOracleSpec (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂)
        (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
    cast
      (congrArg (OracleComp appendSpec)
        (OracleDecoration.QueryHandle.appendLeft_range
          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q))
      (liftM (appendSpec.query
        (OracleDecoration.QueryHandle.appendLeft
          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)))

/- - Route a second-phase transcript-message query into the appended transcript's
oracle specification. The only transport needed here is the response-type
equality witnessed by `QueryHandle.appendRight_range`.  -/
def liftAppendRightQuery :
    QueryImpl (OracleDecoration.toOracleSpec (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂)
      (OracleComp
        (OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))) :=
  fun q =>
    let appendSpec :=
      OracleDecoration.toOracleSpec (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂)
        (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
    cast
      (congrArg (OracleComp appendSpec)
        (OracleDecoration.QueryHandle.appendRight_range
          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q))
      (liftM (appendSpec.query
        (OracleDecoration.QueryHandle.appendRight
          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)))

variable {ιₛ : Type} {OStmt : ιₛ → Type}
variable [∀ i, OracleInterface (OStmt i)]

/- - Lift the first-phase oracle context `[OStmt]ₒ + msgSpec₁` into the appended
oracle context `[OStmt]ₒ + msgSpecAppend`.  -/
def liftAppendLeftContext :
    QueryImpl ([OStmt]ₒ + OracleDecoration.toOracleSpec spec₁ roles₁ od₁ tr₁)
      (OracleComp
        ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))) :=
  fun
  | .inl q =>
      liftM (([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂)
        (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).query (.inl q))
  | .inr q =>
      let appendSpec :=
        [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
      cast
        (congrArg (OracleComp appendSpec)
          (OracleDecoration.QueryHandle.appendLeft_range
            spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q))
        (liftM (appendSpec.query
          (.inr <| OracleDecoration.QueryHandle.appendLeft
            spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)))

/- - Lift the second-phase oracle context `[OStmt]ₒ + msgSpec₂` into the
appended oracle context `[OStmt]ₒ + msgSpecAppend`.  -/
def liftAppendRightContext :
    QueryImpl ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂)
      (OracleComp
        ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))) :=
  fun
  | .inl q =>
      liftM (([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂)
        (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).query (.inl q))
  | .inr q =>
      let appendSpec :=
        [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
      cast
        (congrArg (OracleComp appendSpec)
          (OracleDecoration.QueryHandle.appendRight_range
            spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q))
        (liftM (appendSpec.query
          (.inr <| OracleDecoration.QueryHandle.appendRight
            spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)))

theorem simulateQ_ext
    {ι : Type _} {spec : OracleSpec ι} {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    {impl₁ impl₂ : QueryImpl spec r}
    (himpl : ∀ q, impl₁ q = impl₂ q) :
    ∀ {α : Type _} (oa : OracleComp spec α), simulateQ impl₁ oa = simulateQ impl₂ oa := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp [himpl t, ih]

theorem simulateQ_cast_query
    {ι : Type u} {spec : OracleSpec.{u, v} ι} {r : Type v → Type}
    [Monad r] [LawfulMonad r]
    {α β : Type v} (h : α = β) (impl : QueryImpl spec r) (q : OracleQuery spec α) :
    simulateQ impl (cast (congrArg (OracleComp spec) h) (liftM q)) =
      cast (congrArg r h) (q.cont <$> impl q.input) := by
  cases h
  simp [simulateQ_query]

theorem simulateQ_cast_query_id
    {ι : Type u} {spec : OracleSpec.{u, v} ι}
    {α β : Type v} (h : α = β) (impl : QueryImpl spec Id) (q : OracleQuery spec α) :
    simulateQ impl (cast (congrArg (OracleComp spec) h) (liftM q)) =
      cast h (q.cont (impl q.input)) := by
  cases h
  change simulateQ impl (liftM q) = q.cont (impl q.input)
  rw [simulateQ_query]
  rfl

theorem simulateQ_cast
    {ι : Type u} {spec : OracleSpec.{u, v} ι} {r : Type v → Type}
    [Monad r] [LawfulMonad r]
    {α β : Type v} (h : α = β) (impl : QueryImpl spec r) (oa : OracleComp spec α) :
    simulateQ impl (cast (congrArg (OracleComp spec) h) oa) =
      cast (congrArg r h) (simulateQ impl oa) := by
  cases h
  rfl

theorem simulateQ_cast_spec
    {ι : Type u}
    {spec₁ spec₂ : OracleSpec.{u, v} ι}
    {r : Type v → Type}
    [Monad r] [LawfulMonad r]
    {α : Type v}
    (h : spec₁ = spec₂)
    (impl : QueryImpl spec₂ r)
    (oa : OracleComp spec₁ α) :
    simulateQ impl (cast (by cases h; rfl) oa) =
      simulateQ (cast (by cases h; rfl) impl) oa := by
  cases h
  rfl

theorem simulateQ_cast_dep
    {α : Sort u}
    {Idx : α → Type v}
    {SpecFam : (a : α) → OracleSpec (Idx a)}
    {r : Type w → Type w}
    [Monad r] [LawfulMonad r]
    {a a' : α}
    {β : Type w}
    (h : a = a')
    (impl : QueryImpl (SpecFam a') r)
    (oa : OracleComp (SpecFam a) β) :
    simulateQ impl (cast (by cases h; rfl) oa) =
      simulateQ (cast (by cases h; rfl) impl) oa := by
  cases h
  rfl

theorem liftM_cast_query_add_right
    {ι₁ : Type u} {ι₂ : Type w} {spec₁ : OracleSpec.{u, v} ι₁}
    {spec₂ : OracleSpec.{w, v} ι₂}
    {t : spec₂.Domain} {α : Type v} (h : spec₂.Range t = α) :
    (liftM (cast (congrArg (OracleComp spec₂) h)
      (liftM (spec₂.query t) : OracleComp spec₂ (spec₂.Range t)) :
        OracleComp spec₂ α) :
      OracleComp (spec₁ + spec₂) α) =
    cast (congrArg (OracleComp (spec₁ + spec₂)) h)
      ((liftM ((spec₁ + spec₂).query (Sum.inr t)) :
        OracleComp (spec₁ + spec₂) ((spec₁ + spec₂).Range (Sum.inr t)))) := by
  cases h
  change
    (liftM
      ((liftM (spec₂.query t) :
        OracleQuery (spec₁ + spec₂) (spec₂.Range t))) :
        OracleComp (spec₁ + spec₂) (spec₂.Range t)) =
    liftM ((spec₁ + spec₂).query (Sum.inr t))
  simp

theorem simulateQ_liftAppendLeftContext_eq
    (oStmt : OracleStatement OStmt) :
    ∀ q,
      simulateQ
        (OracleDecoration.oracleContextImpl (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) oStmt
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
        (liftAppendLeftContext (spec₁ := spec₁) (spec₂ := spec₂)
          (roles₁ := roles₁) (roles₂ := roles₂)
          (od₁ := od₁) (od₂ := od₂) (OStmt := OStmt) tr₁ tr₂ q) =
      (OracleDecoration.oracleContextImpl spec₁ roles₁ od₁ oStmt tr₁) q := by
  intro q
  cases q with
  | inl q =>
      simp [OracleDecoration.oracleContextImpl, QueryImpl.add, liftAppendLeftContext]
  | inr q =>
      have hSim :
          simulateQ
            (OracleDecoration.oracleContextImpl (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂) oStmt
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
            (liftAppendLeftContext (spec₁ := spec₁) (spec₂ := spec₂)
              (roles₁ := roles₁) (roles₂ := roles₂)
              (od₁ := od₁) (od₂ := od₂) (OStmt := OStmt) tr₁ tr₂ (.inr q)) =
          cast
            (OracleDecoration.QueryHandle.appendLeft_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
            (OracleDecoration.answerQuery (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
              (OracleDecoration.QueryHandle.appendLeft
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) := by
        simpa [OracleDecoration.oracleContextImpl, QueryImpl.add,
          liftAppendLeftContext] using
          (simulateQ_cast_query_id
            (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
            (α := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).Range
              (Sum.inr <| OracleDecoration.QueryHandle.appendLeft
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q))
            (β := ([OStmt]ₒ + OracleDecoration.toOracleSpec spec₁ roles₁ od₁ tr₁).Range
              (Sum.inr q))
            (h := (OracleDecoration.QueryHandle.appendLeft_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q :
                ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                    (Spec.Decoration.append roles₁ roles₂)
                    (Role.Refine.append od₁ od₂)
                    (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).Range
                  (Sum.inr <| OracleDecoration.QueryHandle.appendLeft
                    spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q) =
                ([OStmt]ₒ + OracleDecoration.toOracleSpec spec₁ roles₁ od₁ tr₁).Range
                  (Sum.inr q)))
            (impl := OracleDecoration.oracleContextImpl (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂) oStmt
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
            (q := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).query
              (Sum.inr <| OracleDecoration.QueryHandle.appendLeft
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)))
      have hAns :
          cast
            (OracleDecoration.QueryHandle.appendLeft_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
            (OracleDecoration.answerQuery (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
              (OracleDecoration.QueryHandle.appendLeft
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) =
          OracleDecoration.answerQuery spec₁ roles₁ od₁ tr₁ q := by
        simpa using OracleDecoration.QueryHandle.answerQuery_appendLeft
          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q
      exact hSim.trans hAns

theorem simulateQ_liftAppendRightContext_eq
    (oStmt : OracleStatement OStmt) :
    ∀ q,
      simulateQ
        (OracleDecoration.oracleContextImpl (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) oStmt
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
        (liftAppendRightContext (spec₁ := spec₁) (spec₂ := spec₂)
          (roles₁ := roles₁) (roles₂ := roles₂)
          (od₁ := od₁) (od₂ := od₂) (OStmt := OStmt) tr₁ tr₂ q) =
      (QueryImpl.add (OracleInterface.simOracle0 OStmt oStmt)
        (OracleDecoration.answerQuery (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂)) q := by
  intro q
  cases q with
  | inl q =>
      simp [OracleDecoration.oracleContextImpl, QueryImpl.add, liftAppendRightContext]
  | inr q =>
      have hSim :
          simulateQ
            (OracleDecoration.oracleContextImpl (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂) oStmt
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
            (liftAppendRightContext (spec₁ := spec₁) (spec₂ := spec₂)
              (roles₁ := roles₁) (roles₂ := roles₂)
              (od₁ := od₁) (od₂ := od₂) (OStmt := OStmt) tr₁ tr₂ (.inr q))
            =
          cast
            (OracleDecoration.QueryHandle.appendRight_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
            (OracleDecoration.answerQuery (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
              (OracleDecoration.QueryHandle.appendRight
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) := by
        simpa [OracleDecoration.oracleContextImpl, QueryImpl.add,
          liftAppendRightContext] using
          (simulateQ_cast_query_id
            (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
            (α := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).Range
              (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q))
            (β := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₂ tr₁)
              (roles₂ tr₁) (od₂ tr₁) tr₂).Range (Sum.inr q))
            (h := (OracleDecoration.QueryHandle.appendRight_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q :
                ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                    (Spec.Decoration.append roles₁ roles₂)
                    (Role.Refine.append od₁ od₂)
                    (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).Range
                  (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                    spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q) =
                ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₂ tr₁)
                    (roles₂ tr₁) (od₂ tr₁) tr₂).Range
                  (Sum.inr q)))
            (impl := OracleDecoration.oracleContextImpl (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂) oStmt
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
            (q := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).query
              (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)))
      have hAns :
          cast
            (OracleDecoration.QueryHandle.appendRight_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
            (OracleDecoration.answerQuery (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
              (OracleDecoration.QueryHandle.appendRight
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) =
          OracleDecoration.answerQuery (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂ q := by
        simpa using OracleDecoration.QueryHandle.answerQuery_appendRight
          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q
      exact hSim.trans hAns

theorem simulateQ_liftAppendRightContext_eq_of_impl
    (impl : QueryImpl [OStmt]ₒ Id) :
    ∀ q,
      simulateQ
        (QueryImpl.add impl
          (OracleDecoration.answerQuery (spec₁.append spec₂)
            (Spec.Decoration.append roles₁ roles₂)
            (Role.Refine.append od₁ od₂)
            (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)))
        (liftAppendRightContext (spec₁ := spec₁) (spec₂ := spec₂)
          (roles₁ := roles₁) (roles₂ := roles₂)
          (od₁ := od₁) (od₂ := od₂) (OStmt := OStmt) tr₁ tr₂ q) =
      (QueryImpl.add impl
        (OracleDecoration.answerQuery (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂)) q := by
  intro q
  cases q with
  | inl q =>
      simp [QueryImpl.add, liftAppendRightContext]
  | inr q =>
      have hSim :
          simulateQ
            (QueryImpl.add impl
              (OracleDecoration.answerQuery (spec₁.append spec₂)
                (Spec.Decoration.append roles₁ roles₂)
                (Role.Refine.append od₁ od₂)
                (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)))
            (liftAppendRightContext (spec₁ := spec₁) (spec₂ := spec₂)
              (roles₁ := roles₁) (roles₂ := roles₂)
              (od₁ := od₁) (od₂ := od₂) (OStmt := OStmt) tr₁ tr₂ (.inr q)) =
          cast
            (OracleDecoration.QueryHandle.appendRight_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
            (OracleDecoration.answerQuery (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
              (OracleDecoration.QueryHandle.appendRight
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) := by
        simpa [QueryImpl.add, liftAppendRightContext] using
          (simulateQ_cast_query_id
            (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
            (α := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).Range
              (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q))
            (β := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₂ tr₁)
              (roles₂ tr₁) (od₂ tr₁) tr₂).Range (Sum.inr q))
            (h := (OracleDecoration.QueryHandle.appendRight_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q :
                ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                    (Spec.Decoration.append roles₁ roles₂)
                    (Role.Refine.append od₁ od₂)
                    (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).Range
                  (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                    spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q) =
                ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₂ tr₁)
                    (roles₂ tr₁) (od₂ tr₁) tr₂).Range
                  (Sum.inr q)))
            (impl := QueryImpl.add impl
              (OracleDecoration.answerQuery (spec₁.append spec₂)
                (Spec.Decoration.append roles₁ roles₂)
                (Role.Refine.append od₁ od₂)
                (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)))
            (q := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).query
              (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)))
      have hAns :
          cast
            (OracleDecoration.QueryHandle.appendRight_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
            (OracleDecoration.answerQuery (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
              (OracleDecoration.QueryHandle.appendRight
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) =
          OracleDecoration.answerQuery (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂ q := by
        simpa using OracleDecoration.QueryHandle.answerQuery_appendRight
          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q
      exact hSim.trans hAns

end QueryRouting

namespace OracleDecoration

/- ! ## Bridge definitions

These definitions bridge `OracleDecoration` to `MonadDecoration` and
transcript-indexed output, enabling the unification of `OracleCounterpart`
with `Counterpart.withMonads`. The oracle computation monad `OracleComp`
constrains these definitions to `Spec.{0}`.  -/

/- - Compute the per-node `MonadDecoration` from an oracle decoration and
accumulated oracle spec. Sender nodes get `Id` (pure observation, `Id α = α`
definitionally), receiver nodes get `OracleComp (oSpec + [OStmtIn]ₒ + accSpec)`
(oracle computation with current access). The accumulated spec grows at sender
nodes and stays fixed at receiver nodes.  -/
def toMonadDecoration {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface.{0, u} (OStmtIn i)] :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) → OracleDecoration.{0, 0} spec roles →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → Spec.MonadDecoration spec
  | .done, _, _, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec =>
      ⟨⟨Id, inferInstance⟩,
       fun x => toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odRest x)
         (accSpec + @OracleInterface.spec _ oi)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec =>
      ⟨⟨OracleComp (oSpec + [OStmtIn]ₒ + accSpec), inferInstance⟩,
       fun x => toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odFn x) accSpec⟩

/- - Convert oracle-spec-indexed output to transcript-indexed output by threading
the accumulated oracle spec through the tree. At each `.done` node, applies
`Output` to the final accumulated spec. At sender nodes, the accumulated spec
grows by the sender's oracle interface spec. At receiver nodes, the accumulated
spec is unchanged.  -/
def liftOutput
    (Output : {ιₐ : Type} → OracleSpec.{0, u} ιₐ → Type) :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) → OracleDecoration.{u, 0} spec roles →
    {ιₐ : Type} → OracleSpec.{0, u} ιₐ → Spec.Transcript spec → Type
  | .done, _, _, _, accSpec, _ => Output accSpec
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, ⟨x, trRest⟩ =>
      liftOutput Output (rest x) (rRest x) (odRest x)
        (accSpec + @OracleInterface.spec _ oi) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, ⟨x, trRest⟩ =>
      liftOutput Output (rest x) (rRest x) (odFn x) accSpec trRest

/- ! ## Oracle counterpart (unified with `Counterpart.withMonads`)

`OracleCounterpart` is the round-by-round challenger with growing oracle access,
defined as `Counterpart.withMonads` with the `MonadDecoration` computed from
the oracle decoration. At sender nodes the monad is `Id` (pure observation);
at receiver nodes the monad is `OracleComp` with accumulated oracle access.  -/

/- - Round-by-round challenger with growing oracle access, defined as
`Counterpart.withMonads` with the monad decoration computed from the oracle
decoration. The oracle-spec-indexed `Output` is converted to a
transcript-indexed family by `liftOutput`.  -/
abbrev OracleCounterpart {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    (Output : {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → Type)
    (spec : Spec.{0}) (roles : RoleDecoration spec) (od : OracleDecoration.{0, 0} spec roles)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :=
  Spec.Counterpart.withMonads spec roles
    (toMonadDecoration oSpec OStmtIn spec roles od accSpec)
    (liftOutput Output spec roles od accSpec)

/- - `InteractiveOracleVerifier` is the round-by-round oracle verifier whose
terminal output is a verification function. The return type may depend on both
the input statement and the realized transcript.  -/
abbrev InteractiveOracleVerifier {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (pSpec : Spec.{0}) (roles : RoleDecoration pSpec)
    (od : OracleDecoration.{0, 0} pSpec roles)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : StmtIn → Spec.Transcript pSpec → Type)
    [∀ i, OracleInterface.{0, 0} (OStmtIn i)] :=
  Spec.Counterpart.withMonads pSpec roles
    (toMonadDecoration oSpec OStmtIn pSpec roles od (ιₐ := PEmpty) []ₒ)
    (fun tr =>
      (s : StmtIn) →
        OracleComp (oSpec + [OStmtIn]ₒ + toOracleSpec pSpec roles od tr)
          (StmtOut s tr))

/- ! ## Conversions  -/

/- - Map the output of an `OracleCounterpart`, applying `f` at each `.done` leaf.
At sender nodes (monad = `Id`), the map is applied purely. At receiver nodes
(monad = `OracleComp`), the map is lifted through the oracle computation.  -/
def OracleCounterpart.mapOutput {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    {Output₁ Output₂ : {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → Type}
    (f : ∀ {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ), Output₁ accSpec → Output₂ accSpec) :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) →
    (od : OracleDecoration.{0, 0} spec roles) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) →
    OracleCounterpart oSpec OStmtIn Output₁ spec roles od accSpec →
    OracleCounterpart oSpec OStmtIn Output₂ spec roles od accSpec
  | .done, _, _, _, accSpec => f accSpec
  | .node _ rest, ⟨.sender, rRest⟩, ⟨_, odRest⟩, _, _ =>
      fun oc x => mapOutput f (rest x) (rRest x) (odRest x) _ (oc x)
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec =>
      fun oc => do
        let ⟨x, ocRest⟩ ← oc
        return ⟨x, mapOutput f (rest x) (rRest x) (odFn x) accSpec ocRest⟩

/- ! ## Oracle prover and oracle reduction  -/

/- - Oracle prover: given ambient input `i`, local statement/oracle data,
performs monadic setup in `OracleComp oSpec` and produces a role-dependent
strategy. The honest prover output is the next local statement bundled with its
output oracle statements, together with the next witness.

This is a specialization of `Prover` with `m = OracleComp oSpec` and the
local statement type bundled with named oracle statements.  -/
abbrev OracleProver {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec.{0})
    (Roles : (shared : SharedIn) → RoleDecoration (Context shared))
    (StatementIn WitnessIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type)
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type) :=
  Prover (OracleComp oSpec)
    SharedIn Context Roles
    (fun shared => StatementWithOracles StatementIn OStatementIn shared) WitnessIn
    (fun shared tr =>
      StatementWithOracles
        (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared)
    WitnessOut

/- - Oracle reduction: pairs an oracle prover with a verifier that uses per-node
monads (`Id` at sender, `OracleComp` at receiver) via `Counterpart.withMonads`.
This is the oracle analog of `Reduction`, where the verifier's per-node monad
structure (growing oracle access) replaces the fixed monad of `Counterpart`.

The honest prover outputs the next plain statement bundled with its output
oracle statements. The verifier produces the plain next statement, while the
`simulate` field exposes query-level access to the output oracle family.
Concrete reification of those output oracles is optional and lives in a
separate layer.  -/
structure OracleReduction {ι : Type} (oSpec : OracleSpec ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → RoleDecoration (Context shared))
    (oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type)
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type) where
  prover : OracleProver oSpec SharedIn Context Roles StatementIn WitnessIn OStatementIn
    StatementOut OStatementOut WitnessOut
  verifier : (shared : SharedIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    StatementIn shared →
      Spec.Counterpart.withMonads (Context shared) (Roles shared)
        (toMonadDecoration oSpec (OStatementIn shared)
          (Context shared) (Roles shared) (oracleDeco shared) accSpec)
        (fun tr => StatementOut shared tr)
  simulate : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) →
    QueryImpl [OStatementOut shared tr]ₒ
      (OracleComp
        ([OStatementIn shared]ₒ +
          toOracleSpec (Context shared) (Roles shared) (oracleDeco shared) tr))

namespace OracleReduction

/- - Full oracle-only verifier output for an oracle reduction at transcript `tr`:
the plain output statement together with the query implementation exposing the
output-oracle access.  -/
abbrev VerifierOutput
    {SharedIn : Type}
    {Context : SharedIn → Spec.{0}}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛᵢ : SharedIn → Type} {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration.{0, 0} (Context shared) (Roles shared)}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type)
    [∀ shared i, OracleInterface.{0, 0} (OStatementIn shared i)]
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (shared : SharedIn) (tr : Spec.Transcript (Context shared)) :=
  StatementOut shared tr × QueryImpl [OStatementOut shared tr]ₒ
    (OracleComp
      ([OStatementIn shared]ₒ +
        toOracleSpec (Context shared) (Roles shared) (oracleDeco shared) tr))

/- - Package the verifier's plain output statement together with the verifier's
output-oracle query access.  -/
def verifierOutput
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type} {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface.{0, 0} (OStatementIn shared i)]
    {Context : SharedIn → Spec.{0}}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration.{0, 0} (Context shared) (Roles shared)}
    {StatementIn WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn) (tr : Spec.Transcript (Context shared)) (stmtOut : StatementOut shared tr) :
    VerifierOutput (Context := Context) (StatementOut := StatementOut)
      (SharedIn := SharedIn) (OStatementIn := OStatementIn)
      (Roles := Roles) (oracleDeco := oracleDeco) OStatementOut shared tr :=
  ⟨stmtOut, reduction.simulate shared tr⟩

/- - The verifier-side monad decoration induced by an oracle reduction, starting
from an accumulated sender-message oracle spec `accSpec`.  -/
abbrev verifierMD
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type} {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface.{0, 0} (OStatementIn shared i)]
    {Context : SharedIn → Spec.{0}}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration.{0, 0} (Context shared) (Roles shared)}
    {StatementIn WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (_reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn) {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :
    Spec.MonadDecoration (Context shared) :=
  toMonadDecoration oSpec (OStatementIn shared)
    (Context shared) (Roles shared) (oracleDeco shared) accSpec

end OracleReduction

end OracleDecoration

/- - A verifier-only oracle protocol surface, analogous to `Interaction.Verifier`.
Its primary index is the shared ambient spine `SharedIn`, which determines the
protocol context, roles, oracle decoration, and oracle families. The carried
explicit claim inside that fixed protocol is `StatementIn shared`.

The verifier returns the explicit output statement directly, while `simulate`
exposes the implicit output oracle behavior at the query level. Concrete
reification of that output oracle family is an optional outer layer.  -/
structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → RoleDecoration (Context shared))
    (oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)] where
  toFun : (shared : SharedIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    StatementIn shared →
      Spec.Counterpart.withMonads (Context shared) (Roles shared)
        (OracleDecoration.toMonadDecoration oSpec (OStatementIn shared)
          (Context shared) (Roles shared) (oracleDeco shared) accSpec)
        (fun tr => StatementOut shared tr)
  simulate : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) →
    QueryImpl [OStatementOut shared tr]ₒ
      (OracleComp ([OStatementIn shared]ₒ + OracleDecoration.toOracleSpec
        (Context shared) (Roles shared) (oracleDeco shared) tr))

instance
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type} {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)] :
    CoeFun
      (OracleVerifier oSpec SharedIn Context Roles oracleDeco StatementIn OStatementIn
        StatementOut OStatementOut)
      (fun _ => (shared : SharedIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
        StatementIn shared →
          Spec.Counterpart.withMonads (Context shared) (Roles shared)
            (OracleDecoration.toMonadDecoration oSpec (OStatementIn shared)
              (Context shared) (Roles shared) (oracleDeco shared) accSpec)
            (fun tr => StatementOut shared tr)) where
  coe verifier := verifier.toFun

namespace OracleDecoration.OracleReduction

/- - Forget the prover and witness bookkeeping of an oracle reduction, keeping
only the verifier-side interaction and output-oracle simulation.  -/
def toVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type} {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut) :
    Interaction.OracleVerifier oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn StatementOut OStatementOut where
  toFun shared {_} accSpec stmt :=
    reduction.verifier shared accSpec stmt
  simulate :=
    reduction.simulate

end OracleDecoration.OracleReduction

/- ! ## Oracle.Spec-based prover, verifier, and reduction

These definitions use `Oracle.Spec` (the inductive type with `.public`/`.oracle`)
instead of `Spec` + `OracleDecoration`. Output types and `simulate` are indexed
by `Oracle.Spec.PublicTranscript`, giving definitional independence from oracle
message values.

Like the `OracleDecoration`-based types above, everything is indexed by a
`SharedIn` ambient input that determines the protocol context, roles, oracle
decoration, and statement/witness families.  -/

namespace Oracle

/- - Oracle prover on `Oracle.Spec`: given ambient input `shared`, local
statement/oracle data and witness, performs monadic setup in `OracleComp oSpec`
and produces a role-dependent strategy on `(Context shared).toInteractionSpec`.
The honest prover output is the next local statement bundled with its output
oracle statements, plus the next witness.  -/
abbrev Prover {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (StatementIn WitnessIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type) :=
  Interaction.Prover (OracleComp oSpec)
    SharedIn
    (fun shared => (Context shared).toInteractionSpec)
    (fun shared => (Context shared).toSpecRoles (Roles shared))
    (fun shared => StatementWithOracles StatementIn OStatementIn shared)
    WitnessIn
    (fun shared tr =>
      StatementWithOracles
        (fun _ => StatementOut shared ((Context shared).projectPublic tr))
        (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
        shared)
    (fun shared tr => WitnessOut shared ((Context shared).projectPublic tr))

/- - Oracle verifier on `Oracle.Spec`: the interactive verifier (`toFun`) and
output-oracle simulation (`simulate`), both on the same `Oracle.Spec`.

The verifier uses `Counterpart.withMonads` with `toMonadDecoration`, giving
`Id` monad at sender/oracle nodes and `OracleComp` at receiver nodes. The
accumulated oracle spec starts at `[]ₒ` and grows as `.oracle` nodes are
traversed, so the verifier's oracle access is fully determined by the
protocol structure.

The `simulate` field provides query-level access to output oracle statements,
indexed by `PublicTranscript` (so it is definitionally independent of oracle
message values).  -/
structure Verifier {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)] where
  toFun : (shared : SharedIn) →
    StatementIn shared →
      Interaction.Spec.Counterpart.withMonads
        (Context shared).toInteractionSpec
        ((Context shared).toSpecRoles (Roles shared))
        ((Context shared).toMonadDecoration oSpec (OStatementIn shared)
          (Roles shared) (OracleDeco shared) []ₒ)
        (fun tr => StatementOut shared ((Context shared).projectPublic tr))
  simulate : (shared : SharedIn) →
    (pt : Spec.PublicTranscript (Context shared)) →
    QueryImpl [OStatementOut shared pt]ₒ
      (OracleComp
        ([OStatementIn shared]ₒ + (Context shared).toOracleSpec (OracleDeco shared) pt))

/- - Oracle reduction on `Oracle.Spec`: bundles a prover and a verifier for the
same protocol. The prover produces strategies on `(Context shared).toInteractionSpec`
while the verifier interacts via `Counterpart.withMonads` with growing oracle
access.

All output types are indexed by `PublicTranscript`, ensuring they do not
depend on oracle message values.  -/
structure Reduction {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type)
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type) where
  prover : Prover oSpec SharedIn Context Roles StatementIn WitnessIn OStatementIn
    StatementOut OStatementOut WitnessOut
  verifier : Verifier oSpec SharedIn Context Roles OracleDeco StatementIn OStatementIn
    StatementOut OStatementOut

/- - Forget the prover and witness of an `Oracle.Reduction`, keeping the
verifier.  -/
def Reduction.toVerifier
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (r : Reduction oSpec SharedIn Context Roles OracleDeco StatementIn OStatementIn
      WitnessIn StatementOut OStatementOut WitnessOut) :
    Verifier oSpec SharedIn Context Roles OracleDeco StatementIn OStatementIn
      StatementOut OStatementOut :=
  r.verifier

end Oracle

end Interaction

-/
