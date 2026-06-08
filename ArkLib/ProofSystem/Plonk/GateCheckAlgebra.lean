/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Plonk gate-check algebraic identities (issue #115)

The gate-constraint evaluation iffs (add/mul/bool/eq gates) and gateCheck_accept_iff_allGatesVanish:
all gates vanish iff every gate accepts. Pure gate algebra; the PIOP composition is separate.
-/

open scoped BigOperators

namespace Issue115Scratch

/-! ## Part A — the GATE-CHECK algebraic identity (genuine math)

The gate of Plonk is the affine-bilinear polynomial
  `G(a,b,c) = qL·a + qR·b + qO·c + qM·(a·b) + qC`.
A wire triple `(a,b,c)` satisfies the gate iff `G = 0`.  This is the algebraic core
the issue names ("the gate constraint").  Below we re-create it and prove the
specialization identities (add / mul / bool / eq) — i.e. *that the generic gate
specializes to the intended arithmetic constraint*.  These are exactly the
soundness-of-specialization facts that justify the gate model. -/

section Gate

variable {𝓡 : Type*} [CommRing 𝓡]

/-- Gate polynomial, mirroring `Plonk.Gate.eval`. -/
def gateEval (qL qR qO qM qC a b c : 𝓡) : 𝓡 :=
  qL * a + qR * b + qO * c + qM * (a * b) + qC

/-- A gate "accepts" when its polynomial vanishes. -/
def gateAccepts (qL qR qO qM qC a b c : 𝓡) : Prop :=
  gateEval qL qR qO qM qC a b c = 0

/-- **Addition gate identity.** With selector `(1,1,-1,0,0)` the gate constraint is
exactly `c = a + b`.  (Matches `Plonk.Gate.add_accepts_iff`.) -/
theorem add_gate_iff (a b c : 𝓡) :
    gateAccepts (1 : 𝓡) 1 (-1) 0 0 a b c ↔ c = a + b := by
  unfold gateAccepts gateEval
  constructor
  · intro h; linear_combination -h
  · intro h; subst h; ring

/-- **Multiplication gate identity.** Selector `(0,0,-1,1,0)` gives `c = a * b`.
(Matches `Plonk.Gate.mul_accepts_iff`.) -/
theorem mul_gate_iff (a b c : 𝓡) :
    gateAccepts (0 : 𝓡) 0 (-1) 1 0 a b c ↔ c = a * b := by
  unfold gateAccepts gateEval
  constructor
  · intro h; linear_combination -h
  · intro h; subst h; ring

/-- **Booleanity gate identity.** Selector `(-1,0,0,1,0)` with `a=b=c=j` gives
`j*(j-1) = 0`. (Matches `Plonk.Gate.bool_accepts_iff`.) -/
theorem bool_gate_iff (j : 𝓡) :
    gateAccepts (-1 : 𝓡) 0 0 1 0 j j j ↔ j * (j - 1) = 0 := by
  unfold gateAccepts gateEval
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- Over an integral domain, booleanity forces `j ∈ {0,1}`.
(Matches `Plonk.Gate.bool_accepts_iff_of_domain`.) -/
theorem bool_gate_iff_domain {𝓡 : Type*} [CommRing 𝓡] [IsDomain 𝓡] (j : 𝓡) :
    gateAccepts (-1 : 𝓡) 0 0 1 0 j j j ↔ j = 0 ∨ j = 1 := by
  rw [bool_gate_iff]
  rw [mul_eq_zero, sub_eq_zero]

/-- **Equality gate identity.** Selector `(1,0,0,0,-k)` with `a=b=c=i` gives `i = k`.
(Matches `Plonk.Gate.eq_accepts`.) -/
theorem eq_gate_iff (i k : 𝓡) :
    gateAccepts (1 : 𝓡) 0 0 0 (-k) i i i ↔ i = k := by
  unfold gateAccepts gateEval
  constructor
  · intro h; linear_combination h
  · intro h; subst h; ring

/-- **Gate-check "soundness" in the deterministic ArkLib model (no SZ).**
The landed `gateCheckVerifier` checks `cs.accepts w` DIRECTLY (a decidable guard),
not at a random evaluation point. So the only content of its soundness is:
the verifier accepting is *definitionally equivalent* to the gate identity holding.
There is no Schwartz–Zippel probability gap here — the error is exactly `0`.

We model "the system accepts" as "every gate polynomial vanishes" and show the
honest equivalence: the constant-selector gate `(1,0,0,0,G i)` evaluated at the
all-zero wire triple has `gateEval = G i`, so the verifier accepting (gate vanishes)
is *exactly* `G i = 0` — a definitional equivalence with zero error, no Schwartz–Zippel
gap. This is the honest statement of what the upstream `gateCheckVerifier_soundness`
proves. -/
theorem gateCheck_accept_iff_allGatesVanish {n : ℕ}
    (G : Fin n → 𝓡) :
    (∀ i, G i = 0) ↔ (∀ i, gateAccepts (1:𝓡) 0 0 0 (G i) 0 0 0) := by
  -- Pointwise, `gateAccepts 1 0 0 0 (G i) 0 0 0` unfolds to `G i = 0`.
  constructor
  · intro h i
    unfold gateAccepts gateEval
    simp [h i]
  · intro h i
    have := h i
    unfold gateAccepts gateEval at this
    simpa using this

end Gate

end Issue115Scratch
