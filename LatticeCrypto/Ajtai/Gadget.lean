/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ring.Kernel

/-!
# Ajtai Gadget Matrices

The main object is `Ajtai.gadgetMatrix ring base rows digits`, the block
diagonal gadget matrix
`I_rows ⊗ [1, base, base^2, ..., base^(digits - 1)]`.  It maps
`rows * digits` ring elements to `rows` ring elements and is used by the
inner-outer Hachi commitment layer.
-/

open scoped BigOperators

universe u

namespace LatticeCrypto
namespace Ajtai

variable {Coeff : Type u} [CommRing Coeff]

/-- Entry of the base-`base` gadget matrix `I_rows ⊗ [1, base, ..., base^(digits-1)]`. -/
def gadgetEntry (ring : NegacyclicRing Coeff) (base : Coeff)
    {rows digits : Nat} (i : Fin rows) (j : Fin (rows * digits)) : ring.Poly :=
  if j.val / digits = i.val then
    ring.scalarPoly (base ^ (j.val % digits))
  else
    ring.zero

/-- The base-`base` gadget matrix `I_rows ⊗ [1, base, ..., base^(digits-1)]`. -/
def gadgetMatrix (ring : NegacyclicRing Coeff) (base : Coeff)
    (rows digits : Nat) : PolyMatrix ring.Poly rows (rows * digits) :=
  Vector.ofFn fun i => Vector.ofFn fun j => gadgetEntry ring base i j

/-- Apply the gadget matrix to a decomposed vector. -/
def gadgetMul (ring : NegacyclicRing Coeff) (base : Coeff)
    {rows digits : Nat} (v : PolyVec ring.Poly (rows * digits)) : PolyVec ring.Poly rows :=
  ring.matVecMul (gadgetMatrix ring base rows digits) v

end Ajtai
end LatticeCrypto
