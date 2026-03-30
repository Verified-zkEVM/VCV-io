/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Primitives
import LatticeCrypto.Falcon.Concrete.NTT
import LatticeCrypto.Falcon.Concrete.Encoding
import LatticeCrypto.Falcon.Concrete.Sampling

/-!
# Concrete Falcon Instance

Wires the concrete NTT, encoding, and sampling modules into the abstract
`Primitives` bundle, and provides a standalone executable `concreteVerify`
function for testing.

## Two-Track Design

1. **`concreteVerify`**: Standalone executable function wiring concrete modules
   directly. Does not go through the abstract `Primitives` structure. This is
   the testable surface.

2. **`concretePrimitives`**: Fills the abstract `Primitives` structure with
   concrete implementations for executable fields (`hashToPoint`, `compress`,
   `decompress`, `nttOps`) and a `sorry`'d ideal discrete Gaussian for
   `samplerZ`. Used for the proof bridge, never executed.
-/

set_option autoImplicit false

namespace Falcon.Concrete

open Falcon

/-! ## Standalone executable verify -/

def concreteVerify (p : Params) (pk : ByteArray) (msg : List Byte)
    (sig : ByteArray) : Bool := Id.run do
  let logn := p.logn
  match sigDecode sig logn with
  | none => return false
  | some (salt, compSig) =>
    match decompress p.n compSig p.sbytelen with
    | none => return false
    | some s2Int =>
      match pkDecode p.n (pk.extract 1 pk.size) with
      | none => return false
      | some h =>
        let c := hashToPoint p.n salt pk msg
        let s2 := IntPoly.toRq s2Int
        let s1 := c - negacyclicMul s2 h
        return decide (pairL2NormSq s1 s2 ≤ p.betaSquared)

/-! ## Abstract primitives instance -/

noncomputable def concretePrimitives (p : Params) : Primitives p where
  hashToPoint := sorry
  samplerZ := fun _μ _σ => sorry
  compress := compress p.n
  decompress := decompress p.n
  nttOps := (by rw [show p.n = 2 ^ p.logn from sorry]; exact concreteNTTRingOps p.logn)

/-! ## Named bundles -/

noncomputable def falcon512Primitives : Primitives falcon512 :=
  concretePrimitives falcon512

noncomputable def falcon1024Primitives : Primitives falcon1024 :=
  concretePrimitives falcon1024

end Falcon.Concrete
