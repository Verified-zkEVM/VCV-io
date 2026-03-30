/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Concrete.FPR

/-!
# FloatLike: Typeclass for IEEE-754-like Floating-Point Operations

Abstracts over floating-point arithmetic so that Falcon algorithms can be
written generically and instantiated with either:
- `FPR` (UInt64 integer emulation, bit-exact with c-fn-dsa's plain path)
- `Float` (Lean's native hardware double, fast but opaque to proofs)

The typeclass captures exactly the operations used by the Falcon signing
pipeline: FFT, LDL decomposition, discrete Gaussian sampling, and the
FACCT exponential approximation.
-/

set_option autoImplicit false

class FloatLike (F : Type) where
  zero : F
  one : F
  neg : F → F
  add : F → F → F
  sub : F → F → F
  mul : F → F → F
  div : F → F → F
  sqrt : F → F
  ofInt : Int64 → F
  ofInt32 : Int32 → F
  scaled : Int64 → Int32 → F
  rint : F → Int64
  floor_ : F → Int64
  /-- Returns ⌊2^63 · ccs · exp(-x)⌋ as a UInt64.
  For FPR this is the FACCT polynomial; for Float this uses hardware exp. -/
  expm_p63 : F → F → UInt64
  /-- Convert a raw IEEE-754 double bit pattern (stored as UInt64) to `F`.
  For FPR (= UInt64), this is the identity. For Float, this decodes the bits. -/
  ofRawFPR : UInt64 → F

namespace FloatLike

variable {F : Type} [FloatLike F]

@[inline] def half : F := div one (add one one)
@[inline] def two : F := add one one
@[inline] def sqr (x : F) : F := mul x x
@[inline] def inv (x : F) : F := div one x

end FloatLike

/-! ## FPR instance -/

open Falcon.Concrete.FPR in
instance : FloatLike FPR where
  zero := zero
  one := one
  neg := neg
  add := add
  sub := sub
  mul := mul
  div := div
  sqrt := sqrt
  ofInt := ofInt
  ofInt32 x := ofInt x.toInt64
  scaled := scaled
  rint := rint
  floor_ := floor_
  expm_p63 := expm_p63
  ofRawFPR := id

/-! ## Float instance -/

private def floatOfInt64 (i : Int64) : Float :=
  if i.toInt >= 0 then Float.ofNat i.toInt.toNat
  else Float.neg (Float.ofNat (-i.toInt).toNat)

private def floatOfInt32 (i : Int32) : Float := floatOfInt64 i.toInt64

private def floatScaled (i : Int64) (sc : Int32) : Float :=
  (floatOfInt64 i).scaleB sc.toInt

private def floatExpmP63 (x ccs : Float) : UInt64 :=
  let v := ccs * Float.exp (-x)
  let twoTo63 : Float := 9223372036854775808.0
  let result := v * twoTo63
  if result <= 0.0 then 0
  else result.toUInt64

private def floatFloorInt64 (x : Float) : Int64 :=
  let r := Float.floor x
  if r >= 0.0 then r.toUInt64.toInt64
  else (0 : Int64) - ((-r).toUInt64).toInt64

private def floatRint (x : Float) : Int64 :=
  let floorInt := floatFloorInt64 x
  let frac := x - Float.floor x
  if frac < 0.5 then
    floorInt
  else if frac > 0.5 then
    floorInt + 1
  else if (floorInt.toUInt64 &&& 1) == 0 then
    floorInt
  else
    floorInt + 1

instance : FloatLike Float where
  zero := 0.0
  one := 1.0
  neg := Float.neg
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  sqrt x := if x > 0.0 then Float.sqrt x else 0.0
  ofInt := floatOfInt64
  ofInt32 := floatOfInt32
  scaled := floatScaled
  rint := floatRint
  floor_ := floatFloorInt64
  expm_p63 := floatExpmP63
  ofRawFPR := Float.ofBits
