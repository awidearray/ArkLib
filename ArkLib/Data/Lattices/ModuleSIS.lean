/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Rq
import ArkLib.Data.Lattices.CyclotomicRing.Vectors
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Module Short Integer Solution (Module-SIS) over the Cyclotomic Ring

A small, ArkLib-native generic `SIS` search game and its Module-SIS specialization
over the computable cyclotomic ring `Rq Φ`. The kernel-form relation: given a uniformly
random matrix `A`, find a nonzero short vector `z` with `A *ᵥ z = 0`.

This is the hardness assumption the Ajtai [Ajt96] commitment binding reductions target, in
the module form used by Greyhound [NS24] and Hachi [NOZ26].

## Main definitions

* `SIS.Problem` / `experiment` / `advantage` — the generic search game.
* `ModuleSIS.relation` / `problem` / `Adversary` / `advantage` — Module-SIS over `Rq Φ`.

## References

* [Ajtai, M., *Generating Hard Instances of Lattice Problems*][Ajt96]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp CompPoly ArkLib.Lattices
open scoped ENNReal

namespace ArkLib.Lattices

/-! ## Generic SIS search game -/

namespace SIS

variable {Sample Solution : Type}

/-- A generic SIS-style problem: public challenge data `Sample` (e.g. a matrix), a
`Solution` type, and a validity predicate. -/
structure Problem (Sample Solution : Type) where
  /-- Distribution of the public challenge. -/
  sampleChallenge : ProbComp Sample
  /-- Validity of a candidate solution (short + satisfies the linear constraint). -/
  isValid : Sample → Solution → Bool

/-- A search adversary for a SIS-style problem. -/
abbrev Adversary (_problem : Problem Sample Solution) := Sample → ProbComp Solution

/-- The SIS experiment: sample a challenge, run the adversary, check validity. -/
def experiment (problem : Problem Sample Solution) (adv : Adversary problem) : ProbComp Bool := do
  let challenge ← problem.sampleChallenge
  let solution ← adv challenge
  return problem.isValid challenge solution

/-- Search advantage for a SIS-style problem. -/
noncomputable def advantage (problem : Problem Sample Solution) (adv : Adversary problem) :
    ℝ≥0∞ :=
  Pr[= true | experiment problem adv]

end SIS

/-! ## Module-SIS over `Rq Φ` -/

namespace ModuleSIS

open CyclotomicModulus

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
  (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- A Module-SIS solution for a matrix with `cols` columns over `Rq Φ`. -/
abbrev Solution (cols : Nat) := PolyVec (Rq Φ) cols

/-- The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short,
and lies in the kernel of `A`. -/
def relation {rows cols : Nat}
    [DecidableEq (PolyVec (Rq Φ) cols)] [DecidableEq (PolyVec (Rq Φ) rows)]
    (isShort : Solution Φ cols → Bool)
    (A : PolyMatrix (Rq Φ) rows cols) (z : Solution Φ cols) : Bool :=
  decide (z ≠ 0) && isShort z && decide (A *ᵥ z = 0)

/-- Module-SIS as an instance of the generic SIS search game. -/
def problem (rows cols : Nat) [SampleableType (PolyMatrix (Rq Φ) rows cols)]
    (isShort : Solution Φ cols → Bool) :
    SIS.Problem (PolyMatrix (Rq Φ) rows cols) (Solution Φ cols) where
  sampleChallenge := $ᵗ (PolyMatrix (Rq Φ) rows cols)
  isValid := relation Φ isShort

/-- A Module-SIS adversary. -/
abbrev Adversary (rows cols : Nat) [SampleableType (PolyMatrix (Rq Φ) rows cols)]
    (isShort : Solution Φ cols → Bool) :=
  SIS.Adversary (problem Φ rows cols isShort)

/-- The Module-SIS experiment. -/
def experiment (rows cols : Nat) [SampleableType (PolyMatrix (Rq Φ) rows cols)]
    (isShort : Solution Φ cols → Bool) (adv : Adversary Φ rows cols isShort) : ProbComp Bool :=
  SIS.experiment (problem Φ rows cols isShort) adv

/-- The Module-SIS advantage. -/
noncomputable def advantage (rows cols : Nat) [SampleableType (PolyMatrix (Rq Φ) rows cols)]
    (isShort : Solution Φ cols → Bool) (adv : Adversary Φ rows cols isShort) : ℝ≥0∞ :=
  SIS.advantage (problem Φ rows cols isShort) adv

end ModuleSIS

end ArkLib.Lattices
