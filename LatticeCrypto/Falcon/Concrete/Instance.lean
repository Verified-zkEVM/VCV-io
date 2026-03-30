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
   concrete implementations for executable fields (`publicKeyBytes`,
   `hashToPoint`, `compress`, `decompress`, `nttOps`) and a `sorry`'d ideal
   discrete Gaussian for `samplerZ`. Used for the proof bridge, never executed.
-/

set_option autoImplicit false

namespace Falcon.Concrete

open Falcon

/-! ## Standalone executable verify -/

/-- Fast negacyclic multiplication using `UInt32` arithmetic, avoiding Mathlib's
`ZMod` typeclass dispatch and heap allocation overhead. Computes the same result
as `negacyclicMul` but ~1000× faster for `q = 12289`. -/
def negacyclicMulU32 {n : ℕ} (f g : Rq n) : Rq n := Id.run do
  let q : UInt32 := modulus.toUInt32
  let fa := f.toArray.map (fun c => (ZMod.val c).toUInt32)
  let ga := g.toArray.map (fun c => (ZMod.val c).toUInt32)
  let mut out : Array UInt32 := Array.replicate n 0
  for i in [0:n] do
    let fi := fa.getD i 0
    for j in [0:n] do
      let gj := ga.getD j 0
      let prod := fi * gj % q
      let k := (i + j) % n
      let cur := out.getD k 0
      if i + j < n then
        let s := cur + prod
        out := out.set! k (if s >= q then s - q else s)
      else
        out := out.set! k (if cur >= prod then cur - prod else cur + q - prod)
  return Vector.ofFn fun ⟨i, _⟩ => (Nat.cast (out.getD i 0).toNat : ZMod modulus)

/-- Fast squared ℓ₂ norm of a pair of polynomials using `Int32`/`UInt64`
arithmetic, avoiding `ℤ` and `Finset.sum` overhead. -/
def pairL2NormSqU32 {n : ℕ} (s₁ s₂ : Rq n) : Nat := Id.run do
  let q : Int64 := modulus.toUInt64.toInt64
  let halfQ : UInt32 := (modulus / 2).toUInt32
  let mut sqn : UInt64 := 0
  for i in [0:n] do
    let v := (ZMod.val (s₁.getD i 0)).toUInt32
    let c : Int64 := if v ≤ halfQ then v.toUInt64.toInt64 else v.toUInt64.toInt64 - q
    sqn := sqn + (c * c).toUInt64
  for i in [0:n] do
    let v := (ZMod.val (s₂.getD i 0)).toUInt32
    let c : Int64 := if v ≤ halfQ then v.toUInt64.toInt64 else v.toUInt64.toInt64 - q
    sqn := sqn + (c * c).toUInt64
  return sqn.toNat

/-- Standalone executable Falcon verification using the concrete hash, codec, and arithmetic
implementations. -/
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
        let s1 := c - negacyclicMulU32 s2 h
        return pairL2NormSqU32 s1 s2 ≤ p.betaSquared

/-! ## Abstract primitives instance -/

/-- Concrete Falcon primitive bundle used to connect the executable code to the abstract
Falcon interfaces. -/
noncomputable def concretePrimitives (p : Params) (hn : p.n = 2 ^ p.logn) :
    Primitives p where
  publicKeyBytes := fun h => publicKeyBytes p.logn h
  hashToPoint := fun salt pkBytes msg => hashToPoint p.n salt pkBytes msg
  samplerZ := fun _μ _σ => sorry
  compress := compress p.n
  decompress := decompress p.n
  nttOps := hn ▸ concreteNTTRingOps p.logn

/-- `publicKeyBytes` for `concretePrimitives` unfolds to the concrete Falcon encoder. -/
@[simp] theorem concretePrimitives_publicKeyBytes_eq
    (p : Params) (hn : p.n = 2 ^ p.logn) (h : Rq p.n) :
    (concretePrimitives p hn).publicKeyBytes h = publicKeyBytes p.logn h := rfl

/-- `hashToPointForPublicKey` for `concretePrimitives` unfolds to the concrete FN-DSA hash path. -/
@[simp] theorem concretePrimitives_hashToPointForPublicKey_eq
    (p : Params) (hn : p.n = 2 ^ p.logn) (h : Rq p.n)
    (salt : Bytes 40) (msg : List Byte) :
    (concretePrimitives p hn).hashToPointForPublicKey h salt msg =
      hashToPoint p.n salt (publicKeyBytes p.logn h) msg := rfl

/-! ## Named bundles -/

/-- Concrete primitives specialized to Falcon-512. -/
noncomputable def falcon512Primitives : Primitives falcon512 :=
  concretePrimitives falcon512 rfl

/-- Concrete primitives specialized to Falcon-1024. -/
noncomputable def falcon1024Primitives : Primitives falcon1024 :=
  concretePrimitives falcon1024 rfl

end Falcon.Concrete
