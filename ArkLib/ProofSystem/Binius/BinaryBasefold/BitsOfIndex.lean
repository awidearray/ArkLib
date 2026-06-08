/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

/-!
## Binary expansion of an index as a challenge vector

`bitsOfIndex` is a small self-contained helper extracted out of `Soundness/Lift.lean` so that the
Binary Basefold *completeness* layer (`ReductionLogic`, and hence the `Steps/*` modules) does not
have to import — and so does not break on — the in-progress `Soundness/` subtree just to obtain this
two-line definition.
-/

namespace Binius.BinaryBasefold

variable {L : Type} [Field L]

/-- Binary expansion of an index as a challenge vector. -/
def bitsOfIndex {n : ℕ} (k : Fin (2 ^ n)) : Fin n → L :=
  fun j => if Nat.getBit j.val k.val = 1 then 1 else 0

end Binius.BinaryBasefold
