/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ML_DSA.Ring
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Concrete Rounding for ML-DSA

Executable coefficient-wise implementations of FIPS 204 Algorithms 35–40:

- `Power2Round`
- `Decompose`
- `HighBits`
- `LowBits`
- `MakeHint`
- `UseHint`

The concrete high-order representations are kept in `Rq`, matching the rest of the
ML-DSA ring layer and avoiding conversion overhead in the verifier equation
`Az - c · (t₁ · 2^d)`.
-/

set_option autoImplicit false

namespace ML_DSA.Concrete

open LatticeCrypto

local instance : NeZero modulus := by
  unfold modulus
  exact ⟨by decide⟩

/-- The high-order representative type used by `HighBits`. -/
abbrev High := Rq

/-- The high-order representative type used by `Power2Round`. -/
abbrev Power2High := Rq

/-- One Boolean hint bit per coefficient. -/
abbrev Hint := Vector Bool ringDegree

/-- `2^d` with `d = 13`. -/
def power2Scale : ℕ := 2 ^ droppedBits

/-- Cast an integer coefficient representative back into `ZMod q`. -/
def intToCoeff (z : ℤ) : Coeff := z

/-- `r mod± m`: the centered representative of `r` modulo `m` in `(-(m/2), m/2]`. -/
def centeredMod (r : Coeff) (m : ℕ) : ℤ :=
  let t := r.val % m
  if _h : t ≤ m / 2 then t else (t : ℤ) - m

/-- FIPS 204 Algorithm 35 on one coefficient. -/
def power2RoundCoeff (r : Coeff) : ℕ × ℤ :=
  let t := r.val % power2Scale
  if _h : t ≤ power2Scale / 2 then
    (r.val / power2Scale, t)
  else
    (r.val / power2Scale + 1, (t : ℤ) - power2Scale)

/-- FIPS 204 Algorithm 36 on one coefficient. -/
def decomposeCoeff (r : Coeff) (gamma2 : ℕ) : ℕ × ℤ :=
  let alpha := 2 * gamma2
  let t := r.val % alpha
  if _h : t ≤ alpha / 2 then
    let r1 := r.val / alpha
    let r0 : ℤ := t
    if alpha * r1 = modulus - 1 then
      (0, r0 - 1)
    else
      (r1, r0)
  else
    let r1 := r.val / alpha + 1
    let r0 : ℤ := (t : ℤ) - alpha
    if alpha * r1 = modulus - 1 then
      (0, r0 - 1)
    else
      (r1, r0)

/-- FIPS 204 Algorithm 37 on one coefficient. -/
def highBitsCoeff (r : Coeff) (gamma2 : ℕ) : ℕ :=
  (decomposeCoeff r gamma2).1

/-- FIPS 204 Algorithm 38 on one coefficient. -/
def lowBitsCoeff (r : Coeff) (gamma2 : ℕ) : ℤ :=
  (decomposeCoeff r gamma2).2

/-- FIPS 204 Algorithm 39 on one coefficient. -/
def makeHintCoeff (z r : Coeff) (gamma2 : ℕ) : Bool :=
  decide (highBitsCoeff r gamma2 ≠ highBitsCoeff (r + z) gamma2)

/-- FIPS 204 Algorithm 40 on one coefficient. -/
def useHintCoeff (h : Bool) (r : Coeff) (gamma2 : ℕ) : ℕ :=
  let m := (modulus - 1) / (2 * gamma2)
  let (r1, r0) := decomposeCoeff r gamma2
  if h then
    if r0 > 0 then
      (r1 + 1) % m
    else
      (r1 + m - 1) % m
  else
    r1

/-- Coefficient-wise `Power2Round` high part. -/
def power2RoundHigh (r : Rq) : Power2High :=
  Vector.ofFn fun i => ((power2RoundCoeff (r.get i)).1 : Coeff)

/-- Coefficient-wise `Power2Round` low part. -/
def power2RoundLow (r : Rq) : Rq :=
  Vector.ofFn fun i => intToCoeff ((power2RoundCoeff (r.get i)).2)

/-- Coefficient-wise `Power2Round`. -/
def power2Round (r : Rq) : Power2High × Rq :=
  (power2RoundHigh r, power2RoundLow r)

/-- Reconstruct `t₁ · 2^d` from a power-2 rounded high representative. -/
def power2RoundShift (r1 : Power2High) : Rq :=
  Vector.map (fun x => (power2Scale : Coeff) * x) r1

/-- Reconstruct the `2γ₂`-multiple of a `HighBits` representative. -/
def highBitsShift (p : Params) (r1 : High) : Rq :=
  Vector.map (fun x => ((2 * p.gamma2 : ℕ) : Coeff) * x) r1

/-- Polynomial `HighBits`, coefficient-wise. -/
def highBits (p : Params) (r : Rq) : High :=
  Vector.ofFn fun i => (highBitsCoeff (r.get i) p.gamma2 : Coeff)

/-- Polynomial `LowBits`, coefficient-wise. -/
def lowBits (p : Params) (r : Rq) : Rq :=
  Vector.ofFn fun i => intToCoeff (lowBitsCoeff (r.get i) p.gamma2)

/-- Polynomial `MakeHint`, coefficient-wise. -/
def makeHint (p : Params) (z r : Rq) : Hint :=
  Vector.ofFn fun i => makeHintCoeff (z.get i) (r.get i) p.gamma2

/-- Polynomial `UseHint`, coefficient-wise. -/
def useHint (p : Params) (h : Hint) (r : Rq) : High :=
  Vector.ofFn fun i => (useHintCoeff (h.get i) (r.get i) p.gamma2 : Coeff)

/-- Count the number of `true` entries in one hint polynomial. -/
def hintWeight (h : Hint) : ℕ :=
  h.toList.foldl (fun acc b => acc + cond b 1 0) 0

/-- Concrete `Power2RoundOps` with `Power2High = Rq`. -/
def concretePower2RoundOps : ML_DSA.Power2RoundOps where
  High2 := Power2High
  power2Round := power2RoundHigh
  shift2 := power2RoundShift

/-- Concrete `RoundingOps` with `High = Rq` and Boolean hints. -/
def concreteRoundingOps (p : Params) : ML_DSA.RoundingOps (2 * p.gamma2) where
  High := High
  Hint := Hint
  lowBits := lowBits p
  highBits := highBits p
  shift := highBitsShift p
  makeHint := makeHint p
  useHint := useHint p

end ML_DSA.Concrete
