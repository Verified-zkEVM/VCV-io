/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ML_DSA.Ring
import Batteries.Data.Vector.Lemmas
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.NatAbs
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
  Vector.ofFn fun i => (power2Scale : Coeff) * r1.get i

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

/-- Transport the standard additive group structure from functions to `Rq` for proofs. -/
private noncomputable def polyEquiv : Rq ≃ (Fin ringDegree → Coeff) where
  toFun := LatticeCrypto.Poly.toPi
  invFun := LatticeCrypto.Poly.ofPi
  left_inv := LatticeCrypto.Poly.ofPi_toPi
  right_inv := LatticeCrypto.Poly.toPi_ofPi

local instance : Add Rq := Vector.instAdd
local instance : Sub Rq := Vector.instSub
local instance : Neg Rq := Vector.instNeg
noncomputable local instance : AddCommGroup Rq := polyEquiv.addCommGroup

/-- Casting `centeredRepr` back into `ZMod q` recovers the original coefficient. -/
private theorem centeredRepr_cast (x : Coeff) :
    x = intToCoeff (LatticeCrypto.centeredRepr x) := by
  by_cases h : (x.val : ℤ) ≤ (modulus : ℤ) / 2
  · rw [LatticeCrypto.centeredRepr_of_le h, intToCoeff, Int.cast_natCast, ZMod.natCast_zmod_val]
  · have hgt : (modulus : ℤ) / 2 < x.val := lt_of_not_ge h
    rw [LatticeCrypto.centeredRepr_of_gt hgt, intToCoeff, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_self]
    simp

/-- `centeredRepr x` lies in the `valMinAbs` interval `(-q/2, q/2]`. -/
private theorem centeredRepr_mem_Ioc (x : Coeff) :
    LatticeCrypto.centeredRepr x * 2 ∈ Set.Ioc (-(modulus : ℤ)) modulus := by
  by_cases h : (x.val : ℤ) ≤ (modulus : ℤ) / 2
  · rw [LatticeCrypto.centeredRepr_of_le h]
    have hx : 0 ≤ (x.val : ℤ) := by positivity
    have hmod : (0 : ℤ) < modulus := by norm_num [modulus]
    constructor <;> omega
  · have hgt : (modulus : ℤ) / 2 < x.val := lt_of_not_ge h
    rw [LatticeCrypto.centeredRepr_of_gt hgt]
    have hval := ZMod.val_lt x
    constructor <;> omega

/-- `centeredRepr` agrees with Mathlib's `valMinAbs` on `ZMod q`. -/
private theorem centeredRepr_eq_valMinAbs (x : Coeff) :
    LatticeCrypto.centeredRepr x = x.valMinAbs := by
  simpa using ((ZMod.valMinAbs_spec x (LatticeCrypto.centeredRepr x)).2
    ⟨centeredRepr_cast x, centeredRepr_mem_Ioc x⟩).symm

private theorem centeredRepr_intToCoeff_eq (z : ℤ)
    (hzlo : -(modulus : ℤ) < z * 2) (hzhi : z * 2 ≤ modulus) :
    LatticeCrypto.centeredRepr (intToCoeff z) = z := by
  rw [centeredRepr_eq_valMinAbs]
  exact (ZMod.valMinAbs_spec (intToCoeff z) z).2 ⟨rfl, ⟨hzlo, hzhi⟩⟩

private theorem power2RoundCoeff_eq (r : Coeff) :
    let (r1, r0) := power2RoundCoeff r
    ((power2Scale : Coeff) * (r1 : Coeff)) + (intToCoeff r0) = r := by
  unfold power2RoundCoeff
  set t : ℕ := r.val % power2Scale
  have hdiv : t + power2Scale * (r.val / power2Scale) = r.val := by
    subst t
    exact Nat.mod_add_div _ _
  have hdiv' : ((t + power2Scale * (r.val / power2Scale) : ℕ) : Coeff) = r := by
    simpa [ZMod.natCast_zmod_val] using congrArg (fun n : ℕ => (n : Coeff)) hdiv
  by_cases h : t ≤ power2Scale / 2
  · simp only [h, ↓reduceDIte, intToCoeff, Int.cast_natCast]
    calc
      ((power2Scale : Coeff) * ((r.val / power2Scale : ℕ) : Coeff)) + (t : Coeff)
          = ((power2Scale * (r.val / power2Scale) + t : ℕ) : Coeff) := by
              rw [← Nat.cast_mul, ← Nat.cast_add]
      _ = r := by
            simpa [Nat.add_comm] using hdiv'
  · simp only [h, ↓reduceDIte, Nat.cast_add, Nat.cast_one, intToCoeff, Int.cast_sub,
      Int.cast_natCast]
    calc
      (↑power2Scale : Coeff) * (↑(r.val / power2Scale) + 1) + ((t : Coeff) - power2Scale)
          = ((power2Scale : Coeff) * ((r.val / power2Scale : ℕ) : Coeff)) + (t : Coeff) := by
              ring
      _ = ((power2Scale * (r.val / power2Scale) + t : ℕ) : Coeff) := by
            rw [← Nat.cast_mul, ← Nat.cast_add]
      _ = r := by
            simpa [Nat.add_comm] using hdiv'

private theorem power2RoundCoeff_bound (r : Coeff) :
    (power2RoundCoeff r).2.natAbs ≤ power2Scale / 2 := by
  unfold power2RoundCoeff
  set t : ℕ := r.val % power2Scale
  have htlt : t < power2Scale := by
    subst t
    simpa [power2Scale] using Nat.mod_lt r.val (show 0 < power2Scale by decide)
  by_cases h : t ≤ power2Scale / 2
  · simp only [h, ↓reduceDIte, Int.natAbs_natCast]
  · have ht : power2Scale / 2 < t := Nat.lt_of_not_ge h
    simp only [h, ↓reduceDIte, ge_iff_le]
    rw [Int.natAbs_natCast_sub_natCast_of_le htlt.le]
    omega

private theorem power2RoundLow_centeredRepr (r : Coeff) :
    LatticeCrypto.centeredRepr (intToCoeff ((power2RoundCoeff r).2)) = (power2RoundCoeff r).2 := by
  let z : ℤ := (power2RoundCoeff r).2
  have hbound : z.natAbs ≤ power2Scale / 2 := by
    simpa [z] using power2RoundCoeff_bound r
  have hzupper : z ≤ power2Scale / 2 := by
    have hz : z ≤ (z.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := z))
    have hb : (z.natAbs : ℤ) ≤ power2Scale / 2 := by
      exact_mod_cast hbound
    omega
  have hzlower : -(power2Scale / 2 : ℤ) ≤ z := by
    have hz : -z ≤ (z.natAbs : ℤ) := by
      have hz' := Int.le_natAbs (a := -z)
      simpa using hz'
    have hb : (z.natAbs : ℤ) ≤ power2Scale / 2 := by
      exact_mod_cast hbound
    omega
  apply centeredRepr_intToCoeff_eq
  · have hscale : (power2Scale : ℤ) = 2 ^ droppedBits := by
      norm_num [power2Scale, droppedBits]
    have hmod : (power2Scale : ℤ) < modulus := by
      norm_num [power2Scale, droppedBits, modulus]
    omega
  · have hscale : (power2Scale : ℤ) = 2 ^ droppedBits := by
      norm_num [power2Scale, droppedBits]
    have hmod : (power2Scale : ℤ) ≤ modulus := by
      norm_num [power2Scale, droppedBits, modulus]
    omega

private theorem modulus_sub_one_eq_neg_one : ((modulus - 1 : ℕ) : Coeff) = (-1 : Coeff) := by
  rw [Nat.cast_sub (show 1 ≤ modulus by norm_num [modulus])]
  rw [ZMod.natCast_self]
  simp

private theorem decomposeCoeff_eq (r : Coeff) {gamma2 : ℕ} (hγ : 0 < gamma2) :
    let (r1, r0) := decomposeCoeff r gamma2
    (((2 * gamma2 : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 = r := by
  unfold decomposeCoeff
  set alpha : ℕ := 2 * gamma2
  set t : ℕ := r.val % alpha
  have hα : 0 < alpha := by
    dsimp [alpha]
    omega
  have hdiv : t + alpha * (r.val / alpha) = r.val := by
    subst t
    exact Nat.mod_add_div _ _
  have hdiv' : ((t + alpha * (r.val / alpha) : ℕ) : Coeff) = r := by
    calc
      ((t + alpha * (r.val / alpha) : ℕ) : Coeff) = (r.val : Coeff) := by
        exact congrArg (fun n : ℕ => (n : Coeff)) hdiv
      _ = r := by
        exact ZMod.natCast_zmod_val r
  by_cases h : t ≤ alpha / 2
  · have base : ((alpha : Coeff) * ((r.val / alpha : ℕ) : Coeff)) + intToCoeff (t : ℤ) = r := by
      calc
        ((alpha : Coeff) * ((r.val / alpha : ℕ) : Coeff)) + intToCoeff (t : ℤ)
            = ((alpha * (r.val / alpha) + t : ℕ) : Coeff) := by
                rw [intToCoeff, Int.cast_natCast, ← Nat.cast_mul, ← Nat.cast_add]
        _ = r := by
              simpa [Nat.add_comm] using hdiv'
    by_cases hs : alpha * (r.val / alpha) = modulus - 1
    · have hsCoeff : ((alpha : Coeff) * ((r.val / alpha : ℕ) : Coeff)) = (-1 : Coeff) := by
        rw [← Nat.cast_mul, hs]
        exact modulus_sub_one_eq_neg_one
      rw [hsCoeff] at base
      simpa [t, h, hs, intToCoeff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        base
    · simpa [t, h, hs, intToCoeff] using base
  · have base :
        ((alpha : Coeff) * (((r.val / alpha) + 1 : ℕ) : Coeff)) +
          intToCoeff ((t : ℤ) - alpha) = r := by
      calc
        ((alpha : Coeff) * (((r.val / alpha) + 1 : ℕ) : Coeff)) + intToCoeff ((t : ℤ) - alpha)
            = ((alpha : Coeff) * ((r.val / alpha : ℕ) : Coeff)) + (t : Coeff) := by
                simp [intToCoeff]
                ring
        _ = ((alpha * (r.val / alpha) + t : ℕ) : Coeff) := by
              rw [← Nat.cast_mul, ← Nat.cast_add]
        _ = r := by
              simpa [Nat.add_comm] using hdiv'
    by_cases hs : alpha * (1 + r.val / alpha) = modulus - 1
    · have hsCoeff : ((alpha : Coeff) * ((1 + r.val / alpha : ℕ) : Coeff)) = (-1 : Coeff) := by
        rw [← Nat.cast_mul, hs]
        exact modulus_sub_one_eq_neg_one
      rw [show ((alpha : Coeff) * (((r.val / alpha) + 1 : ℕ) : Coeff)) =
            ((alpha : Coeff) * ((1 + r.val / alpha : ℕ) : Coeff)) by simp [Nat.add_comm]] at base
      rw [hsCoeff] at base
      simpa [t, h, hs, intToCoeff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        Nat.add_comm] using base
    · have hs' : alpha * ((r.val / alpha) + 1) ≠ modulus - 1 := by
        simpa [Nat.add_comm] using hs
      simpa [t, h, hs', intToCoeff] using base

private theorem lowBitsCoeff_bound (r : Coeff) {gamma2 : ℕ} (hγ : 0 < gamma2) :
    (lowBitsCoeff r gamma2).natAbs ≤ gamma2 := by
  unfold lowBitsCoeff decomposeCoeff
  set alpha : ℕ := 2 * gamma2
  set t : ℕ := r.val % alpha
  have hα : 0 < alpha := by
    dsimp [alpha]
    omega
  have htlt : t < alpha := by
    subst t
    exact Nat.mod_lt _ hα
  have hhalf : alpha / 2 = gamma2 := by
    dsimp [alpha]
    omega
  by_cases h : t ≤ alpha / 2
  · have htγ : t ≤ gamma2 := by simpa [hhalf] using h
    have hcond : r.val % (2 * gamma2) ≤ gamma2 := by
      simpa [alpha, t] using htγ
    by_cases hs : alpha * (r.val / alpha) = modulus - 1
    · have hbound : Int.natAbs ((t : ℤ) - 1) ≤ gamma2 := by
        simpa using Int.natAbs_coe_sub_coe_le_of_le htγ (show 1 ≤ gamma2 by omega)
      simpa [lowBitsCoeff, decomposeCoeff, alpha, t, hcond, hs] using hbound
    · have hbound : Int.natAbs (t : ℤ) ≤ gamma2 := by
        simpa using htγ
      simpa [lowBitsCoeff, decomposeCoeff, alpha, t, hcond, hs] using hbound
  · have htgt : alpha / 2 < t := Nat.lt_of_not_ge h
    have htgeγ : gamma2 + 1 ≤ t := by
      have : gamma2 < t := by simpa [hhalf] using htgt
      omega
    have hnotcond : ¬r.val % (2 * gamma2) ≤ gamma2 := by
      intro hcond
      apply h
      simpa [alpha, t, hhalf] using hcond
    by_cases hs : alpha * (1 + r.val / alpha) = modulus - 1
    · have hs' : (2 * gamma2) * (1 + r.val / (2 * gamma2)) = modulus - 1 := by
        simpa [alpha] using hs
      have hbound : Int.natAbs ((t : ℤ) - ((alpha + 1 : ℕ) : ℤ)) ≤ gamma2 := by
        rw [Int.natAbs_natCast_sub_natCast_of_le (show t ≤ alpha + 1 by omega)]
        rw [show alpha = 2 * gamma2 by rfl]
        omega
      have hbound' : Int.natAbs ((t : ℤ) - alpha - 1) ≤ gamma2 := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hbound
      simpa [lowBitsCoeff, decomposeCoeff, alpha, t, hnotcond, hs', Nat.add_comm] using hbound'
    · have hs' : (2 * gamma2) * (1 + r.val / (2 * gamma2)) ≠ modulus - 1 := by
        simpa [alpha] using hs
      have hbound : Int.natAbs ((t : ℤ) - alpha) ≤ gamma2 := by
        rw [Int.natAbs_natCast_sub_natCast_of_le htlt.le]
        rw [show alpha = 2 * gamma2 by rfl]
        omega
      simpa [lowBitsCoeff, decomposeCoeff, alpha, t, hnotcond, hs', Nat.add_comm] using hbound

private theorem lowBits_centeredRepr (r : Coeff) {gamma2 : ℕ}
    (hγ : 0 < gamma2) (hq : 2 * gamma2 < modulus) :
    LatticeCrypto.centeredRepr (intToCoeff (lowBitsCoeff r gamma2)) = lowBitsCoeff r gamma2 := by
  let z : ℤ := lowBitsCoeff r gamma2
  have hbound : z.natAbs ≤ gamma2 := by
    simpa [z] using lowBitsCoeff_bound (r := r) hγ
  have hzupper : z ≤ gamma2 := by
    have hz : z ≤ (z.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := z))
    have hb : (z.natAbs : ℤ) ≤ gamma2 := by
      exact_mod_cast hbound
    omega
  have hzlower : -(gamma2 : ℤ) ≤ z := by
    have hz : -z ≤ (z.natAbs : ℤ) := by
      have hz' := Int.le_natAbs (a := -z)
      simpa using hz'
    have hb : (z.natAbs : ℤ) ≤ gamma2 := by
      exact_mod_cast hbound
    omega
  have hqz : ((2 * gamma2 : ℕ) : ℤ) < modulus := by
    exact_mod_cast hq
  apply centeredRepr_intToCoeff_eq
  · omega
  · omega

private theorem power2RoundShift_high_get (r : Rq) (i : Fin ringDegree) :
    (power2RoundShift (power2RoundHigh r)).get i =
      (power2Scale : Coeff) * ((power2RoundCoeff (r.get i)).1 : Coeff) := by
  simp [power2RoundShift, power2RoundHigh]

private theorem power2RoundLow_get (r : Rq) (i : Fin ringDegree) :
    (power2RoundLow r).get i = intToCoeff ((power2RoundCoeff (r.get i)).2) := by
  simp [power2RoundLow]

theorem concretePower2Round_high_low_decomp (r : Rq) :
    power2RoundShift (power2RoundHigh r) + power2RoundLow r = r := by
  apply Vector.ext
  intro i hi
  let j : Fin ringDegree := ⟨i, hi⟩
  rw [Vector.getElem_add]
  change (power2RoundShift (power2RoundHigh r)).get j +
      (power2RoundLow r).get j = r.get j
  rw [power2RoundShift_high_get, power2RoundLow_get]
  exact power2RoundCoeff_eq (r.get j)

theorem concretePower2Round_remainder_eq_low (r : Rq) :
    r - power2RoundShift (power2RoundHigh r) = power2RoundLow r := by
  apply Vector.ext
  intro i hi
  let j : Fin ringDegree := ⟨i, hi⟩
  rw [Vector.getElem_sub]
  change r.get j - (power2RoundShift (power2RoundHigh r)).get j =
      (power2RoundLow r).get j
  rw [power2RoundShift_high_get, power2RoundLow_get]
  exact sub_eq_iff_eq_add'.2 (power2RoundCoeff_eq (r.get j)).symm

theorem concretePower2Round_bound (r : Rq) :
    LatticeCrypto.cInfNorm (r - power2RoundShift (power2RoundHigh r)) ≤ 2 ^ (droppedBits - 1) := by
  rw [concretePower2Round_remainder_eq_low]
  refine LatticeCrypto.cInfNorm_le_of_coeff_le ?_
  intro i
  rw [power2RoundLow_get]
  rw [power2RoundLow_centeredRepr (r.get i)]
  simpa [power2Scale, droppedBits] using power2RoundCoeff_bound (r.get i)

private theorem highBitsShift_high_get (p : Params) (r : Rq) (i : Fin ringDegree) :
    (highBitsShift p (highBits p r)).get i =
      ((2 * p.gamma2 : ℕ) : Coeff) * (highBitsCoeff (r.get i) p.gamma2 : Coeff) := by
  simp [highBitsShift, highBits]

private theorem lowBits_get (p : Params) (r : Rq) (i : Fin ringDegree) :
    (lowBits p r).get i = intToCoeff (lowBitsCoeff (r.get i) p.gamma2) := by
  simp [lowBits]

theorem concreteRounding_high_low_decomp (p : Params) (hγ : 0 < p.gamma2) (r : Rq) :
    highBitsShift p (highBits p r) + lowBits p r = r := by
  apply Vector.ext
  intro i hi
  let j : Fin ringDegree := ⟨i, hi⟩
  rw [Vector.getElem_add]
  change (highBitsShift p (highBits p r)).get j + (lowBits p r).get j = r.get j
  rw [highBitsShift_high_get, lowBits_get]
  simpa [highBitsCoeff, lowBitsCoeff] using decomposeCoeff_eq (r.get j) hγ

theorem concreteRounding_lowBits_bound (p : Params)
    (hγ : 0 < p.gamma2) (hq : 2 * p.gamma2 < modulus) (r : Rq) :
    LatticeCrypto.cInfNorm (lowBits p r) ≤ p.gamma2 := by
  refine LatticeCrypto.cInfNorm_le_of_coeff_le ?_
  intro i
  rw [lowBits_get]
  rw [lowBits_centeredRepr (r := r.get i) hγ hq]
  simpa using lowBitsCoeff_bound (r := r.get i) hγ

private theorem gamma2_pos_of_isApproved {p : Params} (hp : p.isApproved) :
    0 < p.gamma2 := by
  rcases hp with rfl | rfl | rfl <;> decide

private theorem gamma2_double_lt_modulus_of_isApproved {p : Params} (hp : p.isApproved) :
    2 * p.gamma2 < modulus := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem concreteRounding_high_low_decomp_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) :
    highBitsShift p (highBits p r) + lowBits p r = r :=
  concreteRounding_high_low_decomp p (gamma2_pos_of_isApproved hp) r

theorem concreteRounding_lowBits_bound_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) :
    LatticeCrypto.cInfNorm (lowBits p r) ≤ p.gamma2 :=
  concreteRounding_lowBits_bound p (gamma2_pos_of_isApproved hp)
    (gamma2_double_lt_modulus_of_isApproved hp) r

private theorem coeff_mul_left_injective_of_isUnit {c : Coeff} (hc : IsUnit c) :
    Function.Injective fun x : Coeff => c * x := by
  intro x y hxy
  rcases hc with ⟨u, rfl⟩
  have hxy' := congrArg (fun z : Coeff => ↑u⁻¹ * z) hxy
  simpa [mul_assoc] using hxy'

private theorem twoGamma_coprime_modulus_of_isApproved {p : Params} (hp : p.isApproved) :
    Nat.Coprime (2 * p.gamma2) modulus := by
  rcases hp with rfl | rfl | rfl <;> decide

private theorem twoGamma_isUnit_of_isApproved {p : Params} (hp : p.isApproved) :
    IsUnit (((2 * p.gamma2 : ℕ) : Coeff)) := by
  simpa using (ZMod.isUnit_iff_coprime (2 * p.gamma2) modulus).2
    (twoGamma_coprime_modulus_of_isApproved hp)

theorem highBitsShift_injective_of_isApproved (p : Params)
    (hp : p.isApproved) :
    Function.Injective (highBitsShift p) := by
  intro x y hxy
  apply Vector.ext
  intro i hi
  let j : Fin ringDegree := ⟨i, hi⟩
  have hcoeff :
      (((2 * p.gamma2 : ℕ) : Coeff) * x.get j) =
        (((2 * p.gamma2 : ℕ) : Coeff) * y.get j) := by
    simpa [highBitsShift] using congrArg (fun v : Rq => v.get j) hxy
  exact coeff_mul_left_injective_of_isUnit (twoGamma_isUnit_of_isApproved hp) hcoeff

/-- Concrete `Power2RoundOps` with `Power2High = Rq`. -/
def concretePower2RoundOps : ML_DSA.Power2RoundOps where
  Power2High := Power2High
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

/-
The vector-level `Power2Round` decomposition and bound lemmas above compile. The remaining
unresolved wrapper is `concretePower2RoundLaws`, followed by the harder `RoundingOps.Laws`
obligations for `decompose`/`highBits`/`lowBits`.
-/

end ML_DSA.Concrete
