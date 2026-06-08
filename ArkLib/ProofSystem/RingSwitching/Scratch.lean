/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound

/-!
# Ring-Switching Scratch Lemmas

Scratch namespace `ScratchRS` collecting auxiliary lemmas used while developing the ring-switching
protocol: a value-form classification of `finSumFinEquiv.symm` (`finSumFinEquiv_symm_dite`) and
multivariate-polynomial variable-fixing rewrites (`fixVars_eq_bind₁`, `fixVars_step`).
-/

open MvPolynomial Finset Sumcheck.Structured RingSwitching

namespace ScratchRS

set_option linter.style.longFile 0
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {L : Type} [CommRing L] [Nontrivial L] [DecidableEq L]

-- Value-form of `finSumFinEquiv.symm`: classify by whether the index value is `< m`.
theorem finSumFinEquiv_symm_dite {m n : ℕ} (x : Fin (m + n)) :
    finSumFinEquiv.symm x
      = if h : (x : ℕ) < m then Sum.inl ⟨x, h⟩
        else Sum.inr ⟨(x : ℕ) - m, by omega⟩ := by
  exact RingSwitching.finSumFinEquiv_symm_dite x

-- Characterization: fixFirstVariablesOfMQP as a `bind₁` partial substitution.
theorem fixVars_eq_bind₁ (ℓ : ℕ) (v : Fin (ℓ + 1)) (poly : MvPolynomial (Fin ℓ) L)
    (challenges : Fin v → L) :
    fixFirstVariablesOfMQP ℓ v poly challenges
      = bind₁ (fun i : Fin ℓ =>
          Sum.elim (X : Fin (ℓ - v) → MvPolynomial (Fin (ℓ - v)) L)
            (fun j => C (challenges j))
            (((finCongr (by rw [Nat.add_comm]; exact (Nat.add_sub_of_le v.is_le).symm)).trans
              (finSumFinEquiv (m := ℓ - v) (n := v).symm)) i)) poly := by
  exact RingSwitching.fixVars_eq_bind₁ ℓ v poly challenges

-- Composition (polynomial level): fix last `v`, then last `1` more, equals fix last `v+1`
-- with the repaired `Fin.cons` challenge order from the production prelude.
theorem fixVars_step (ℓ : ℕ) (poly : MvPolynomial (Fin ℓ) L) (v : Fin (ℓ + 1))
    (hv : (v : ℕ) < ℓ) (challenges : Fin v → L) (r' : L) :
    fixFirstVariablesOfMQP (ℓ - v) ⟨1, by omega⟩
        (fixFirstVariablesOfMQP ℓ v poly challenges) (fun _ => r')
      = rename (finCongr (show ℓ - ((v : ℕ) + 1) = ℓ - v - 1 by omega))
          (fixFirstVariablesOfMQP ℓ ⟨(v : ℕ) + 1, by omega⟩ poly (Fin.cons r' challenges)) := by
  exact RingSwitching.fixVars_step ℓ poly v hv challenges r'

end ScratchRS
