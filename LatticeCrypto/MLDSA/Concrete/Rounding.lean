/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Ring
import LatticeCrypto.Norm
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

namespace MLDSA.Concrete

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

private def rqNSMul (n : ℕ) (x : Rq) : Rq :=
  Vector.ofFn fun i => n • x.get i

private def rqZSMul (n : ℤ) (x : Rq) : Rq :=
  Vector.ofFn fun i => n • x.get i

local instance : Add Rq := Vector.instAdd
local instance : Zero Rq := Vector.instZero
local instance : Sub Rq := Vector.instSub
local instance : Neg Rq := Vector.instNeg

local instance instRqAddCommGroup : AddCommGroup Rq where
  add := (· + ·)
  add_assoc a b c := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_add, Vector.getElem_add, Vector.getElem_add, Vector.getElem_add]
    exact add_assoc _ _ _
  zero := 0
  zero_add a := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_add, Vector.getElem_zero]
    exact zero_add _
  add_zero a := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_add, Vector.getElem_zero]
    exact add_zero _
  nsmul := rqNSMul
  nsmul_zero x := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_zero]
    simp [rqNSMul]
  nsmul_succ n x := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_add]
    simpa [rqNSMul] using AddMonoid.nsmul_succ n (x.get ⟨i, hi⟩)
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg a b := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_sub, Vector.getElem_add, Vector.getElem_neg]
    exact sub_eq_add_neg _ _
  zsmul := rqZSMul
  zsmul_zero' a := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_zero]
    simp [rqZSMul]
  zsmul_succ' n a := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_add]
    simpa [rqZSMul] using SubNegMonoid.zsmul_succ' n (a.get ⟨i, hi⟩)
  zsmul_neg' n a := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_neg]
    simpa [rqZSMul] using SubNegMonoid.zsmul_neg' n (a.get ⟨i, hi⟩)
  neg_add_cancel a := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_add, Vector.getElem_neg, Vector.getElem_zero]
    exact neg_add_cancel _
  add_comm a b := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_add, Vector.getElem_add]
    exact add_comm _ _

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

theorem centeredRepr_eq_of_natAbs_le (z : ℤ) {b : ℕ}
    (hbound : z.natAbs ≤ b) (hbq : 2 * b < modulus) :
    LatticeCrypto.centeredRepr (intToCoeff z) = z := by
  have hzupper : z ≤ b := by
    have hz : z ≤ (z.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := z))
    have hb : (z.natAbs : ℤ) ≤ b := by
      exact_mod_cast hbound
    omega
  have hzlower : -(b : ℤ) ≤ z := by
    have hz : -z ≤ (z.natAbs : ℤ) := by
      have hz' := Int.le_natAbs (a := -z)
      simpa using hz'
    have hb : (z.natAbs : ℤ) ≤ b := by
      exact_mod_cast hbound
    omega
  have hbqz : ((2 * b : ℕ) : ℤ) < modulus := by
    exact_mod_cast hbq
  apply centeredRepr_intToCoeff_eq
  · omega
  · omega

private theorem power2RoundLow_centeredRepr (r : Coeff) :
    LatticeCrypto.centeredRepr (intToCoeff ((power2RoundCoeff r).2)) = (power2RoundCoeff r).2 := by
  apply centeredRepr_eq_of_natAbs_le
  · exact power2RoundCoeff_bound r
  · norm_num [power2Scale, droppedBits, modulus]

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
  apply centeredRepr_eq_of_natAbs_le
  · exact lowBitsCoeff_bound r hγ
  · linarith

private theorem neg_le_and_le_of_natAbs_le {z : ℤ} {b : ℕ}
    (hbound : z.natAbs ≤ b) : -(b : ℤ) ≤ z ∧ z ≤ b := by
  constructor
  · have hz : -z ≤ (z.natAbs : ℤ) := by
      have hz' := Int.le_natAbs (a := -z)
      simpa using hz'
    have hb : (z.natAbs : ℤ) ≤ b := by
      exact_mod_cast hbound
    omega
  · have hz : z ≤ (z.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := z))
    have hb : (z.natAbs : ℤ) ≤ b := by
      exact_mod_cast hbound
    omega

private theorem natAbs_le_of_bounds {z : ℤ} {b : ℕ}
    (hl : -(b : ℤ) ≤ z) (hu : z ≤ b) : z.natAbs ≤ b := by
  exact_mod_cast (show (z.natAbs : ℤ) ≤ b from by
    by_cases hz : 0 ≤ z
    · rw [Int.natAbs_of_nonneg hz]
      exact hu
    · have hnegz : 0 ≤ -z := by omega
      have hnat : (z.natAbs : ℤ) = -z := by
        simpa [Int.natAbs_neg] using (Int.natAbs_of_nonneg (a := -z) hnegz)
      rw [hnat]
      omega)

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

private theorem useHintModulus_pos_of_isApproved {p : Params} (hp : p.isApproved) :
    0 < (modulus - 1) / (2 * p.gamma2) := by
  rcases hp with rfl | rfl | rfl <;> decide

private theorem twoGamma_dvd_modulus_sub_one_of_isApproved {p : Params} (hp : p.isApproved) :
    2 * p.gamma2 ∣ modulus - 1 := by
  rcases hp with rfl | rfl | rfl <;> decide

private theorem alphaPlusOne_double_lt_modulus_of_isApproved {p : Params} (hp : p.isApproved) :
    2 * (2 * p.gamma2 + 1) < modulus := by
  rcases hp with rfl | rfl | rfl <;> decide

private theorem highBitsCoeff_lt_useHintModulus_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Coeff) :
    highBitsCoeff r p.gamma2 < (modulus - 1) / (2 * p.gamma2) := by
  unfold highBitsCoeff decomposeCoeff
  set alpha : ℕ := 2 * p.gamma2
  set m : ℕ := (modulus - 1) / alpha
  set t : ℕ := r.val % alpha
  have hα : 0 < alpha := by
    have hγ := gamma2_pos_of_isApproved hp
    dsimp [alpha]
    omega
  have hm : 0 < m := by
    simpa [m, alpha] using useHintModulus_pos_of_isApproved hp
  have hqm : alpha * m = modulus - 1 := by
    have hdvd : alpha ∣ modulus - 1 := by
      simpa [alpha] using twoGamma_dvd_modulus_sub_one_of_isApproved hp
    simpa [m] using (Nat.mul_div_cancel' hdvd)
  have htlt : t < alpha := by
    subst t
    exact Nat.mod_lt _ hα
  have hdiv : t + alpha * (r.val / alpha) = r.val := by
    subst t
    exact Nat.mod_add_div _ _
  by_cases h : t ≤ alpha / 2
  · have hcond : r.val % (2 * p.gamma2) ≤ p.gamma2 := by
      simpa [alpha, t] using h
    by_cases hs : alpha * (r.val / alpha) = modulus - 1
    · simpa [t, h, hs] using hm
    · have hlt : r.val / alpha < m := by
        by_contra hge
        have hmle : m ≤ r.val / alpha := Nat.not_lt.mp hge
        have hmul : modulus - 1 ≤ alpha * (r.val / alpha) := by
          simpa [hqm] using Nat.mul_le_mul_left alpha hmle
        have hupper : alpha * (r.val / alpha) ≤ r.val := by
          have hhdiv := hdiv
          omega
        have hval : r.val = modulus - 1 := by
          have hltq : r.val < modulus := ZMod.val_lt r
          omega
        have heq : alpha * (r.val / alpha) = modulus - 1 := by
          have hhdiv := hdiv
          omega
        exact hs heq
      simpa [t, h, hs] using hlt
  · have hnotcond : ¬r.val % (2 * p.gamma2) ≤ p.gamma2 := by
      intro hcond
      apply h
      simpa [alpha, t] using hcond
    by_cases hs : alpha * (1 + r.val / alpha) = modulus - 1
    · simpa [t, h, hs, Nat.add_comm] using hm
    · have hlt : r.val / alpha + 1 < m := by
        have hqdiv_lt_m : r.val / alpha < m := by
          by_contra hge
          have hmle : m ≤ r.val / alpha := Nat.not_lt.mp hge
          have hmul : modulus - 1 ≤ alpha * (r.val / alpha) := by
            simpa [hqm] using Nat.mul_le_mul_left alpha hmle
          have htpos : 0 < t := by
            have htgt : alpha / 2 < t := Nat.lt_of_not_ge h
            omega
          have hval : modulus ≤ r.val := by
            have hhdiv := hdiv
            omega
          exact (Nat.not_lt.mpr hval) (ZMod.val_lt r)
        have hle : r.val / alpha + 1 ≤ m := Nat.succ_le_of_lt hqdiv_lt_m
        have hne : r.val / alpha + 1 ≠ m := by
          intro heq
          have heq' : alpha * (1 + r.val / alpha) = modulus - 1 := by
            rw [Nat.add_comm, heq, hqm]
          exact hs heq'
        exact lt_of_le_of_ne hle hne
      simpa [t, h, hs, Nat.add_comm] using hlt

private theorem alphaMulUseHintModulus_eq_neg_one_of_isApproved (p : Params)
    (hp : p.isApproved) :
    let alpha := 2 * p.gamma2
    let m := (modulus - 1) / alpha
    (((alpha : ℕ) : Coeff) * (m : Coeff)) = (-1 : Coeff) := by
  dsimp
  have hdvd : 2 * p.gamma2 ∣ modulus - 1 := twoGamma_dvd_modulus_sub_one_of_isApproved hp
  rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  exact modulus_sub_one_eq_neg_one

private theorem alphaMulUseHintModulus_eq_modulus_sub_one_of_isApproved (p : Params)
    (hp : p.isApproved) :
    let alpha := 2 * p.gamma2
    let m := (modulus - 1) / alpha
    alpha * m = modulus - 1 := by
  dsimp
  exact Nat.mul_div_cancel' (twoGamma_dvd_modulus_sub_one_of_isApproved hp)

private theorem centeredRepr_alpha_mul_natAbs_ge_of_isApproved (p : Params)
    (hp : p.isApproved) {delta : ℕ}
    (hdelta0 : 0 < delta)
    (hdeltalt : delta < (modulus - 1) / (2 * p.gamma2)) :
    2 * p.gamma2 ≤
      (LatticeCrypto.centeredRepr
        ((((2 * p.gamma2 : ℕ) * delta : ℕ) : Coeff))).natAbs := by
  rcases hp with rfl | rfl | rfl
  · have hdeltalt' : delta < 44 := by
      simpa [mldsa44, modulus] using hdeltalt
    interval_cases delta <;> decide
  · have hdeltalt' : delta < 16 := by
      simpa [mldsa65, modulus] using hdeltalt
    interval_cases delta <;> decide
  · have hdeltalt' : delta < 16 := by
      simpa [mldsa87, modulus] using hdeltalt
    interval_cases delta <;> decide

private theorem highBitsCoeff_add_eq_of_small_of_isApproved (p : Params)
    (hp : p.isApproved) (r s : Coeff) {b : ℕ}
    (hs : (LatticeCrypto.centeredRepr s).natAbs ≤ b)
    (hr : (lowBitsCoeff r p.gamma2).natAbs < p.gamma2 - b) :
    highBitsCoeff (r + s) p.gamma2 = highBitsCoeff r p.gamma2 := by
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  let decr := decomposeCoeff r p.gamma2
  let r1 : ℕ := decr.1
  let r0 : ℤ := decr.2
  let decrs := decomposeCoeff (r + s) p.gamma2
  let u : ℕ := decrs.1
  let w : ℤ := decrs.2
  let z : ℤ := LatticeCrypto.centeredRepr s
  let v : ℤ := r0 + z
  have hγ := gamma2_pos_of_isApproved hp
  have hm : 0 < m := by
    simpa [alpha, m] using useHintModulus_pos_of_isApproved hp
  have hr1lt : r1 < m := by
    simpa [alpha, m, decr, r1] using highBitsCoeff_lt_useHintModulus_of_isApproved p hp r
  have hult : u < m := by
    simpa [alpha, m, decrs, u] using highBitsCoeff_lt_useHintModulus_of_isApproved p hp (r + s)
  have hdecomp_r : (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 = r := by
    simpa [alpha, decr, r1, r0] using decomposeCoeff_eq (r := r) (gamma2 := p.gamma2) hγ
  have hdecomp_rs : (((alpha : ℕ) : Coeff) * (u : Coeff)) + intToCoeff w = r + s := by
    simpa [alpha, decrs, u, w] using decomposeCoeff_eq (r := r + s) (gamma2 := p.gamma2) hγ
  have hwbound : w.natAbs ≤ p.gamma2 := by
    simpa [decrs, w] using lowBitsCoeff_bound (r := r + s) (gamma2 := p.gamma2) hγ
  have hrpred : r0.natAbs ≤ p.gamma2 - b - 1 := Nat.le_pred_of_lt hr
  have hr0bounds := neg_le_and_le_of_natAbs_le hrpred
  have hzbounds := neg_le_and_le_of_natAbs_le hs
  have hvupper : v ≤ ((p.gamma2 - 1 : ℕ) : ℤ) := by
    dsimp [v]
    omega
  have hvlower : -((p.gamma2 - 1 : ℕ) : ℤ) ≤ v := by
    dsimp [v]
    omega
  have hvbound : v.natAbs ≤ p.gamma2 - 1 := by
    exact natAbs_le_of_bounds hvlower hvupper
  have hzcast : s = intToCoeff z := by
    simpa [z] using centeredRepr_cast s
  have hcandidate : (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v = r + s := by
    calc
      (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v
          = ((((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0) + intToCoeff z := by
              dsimp [v]
              simp [intToCoeff]
              ring
      _ = r + s := by
            simpa [intToCoeff, hdecomp_r, hzcast]
  by_contra hneq
  have hsmallq : 2 * (alpha - 1) < modulus := by
    have hbase : 2 * (alpha + 1) < modulus := by
      simpa [alpha, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, two_mul] using
        alphaPlusOne_double_lt_modulus_of_isApproved hp
    omega
  have hvbounds := neg_le_and_le_of_natAbs_le hvbound
  have hwbounds := neg_le_and_le_of_natAbs_le hwbound
  have hdiffupper : v - w ≤ ((alpha - 1 : ℕ) : ℤ) := by
    omega
  have hdifflower : -((alpha - 1 : ℕ) : ℤ) ≤ v - w := by
    omega
  have hdiffbound : (v - w).natAbs ≤ alpha - 1 := by
    exact natAbs_le_of_bounds hdifflower hdiffupper
  have hrepr_diff : LatticeCrypto.centeredRepr (intToCoeff (v - w)) = v - w := by
    exact centeredRepr_eq_of_natAbs_le (z := v - w) hdiffbound hsmallq
  have heq :
      (((alpha : ℕ) : Coeff) * (u : Coeff)) + intToCoeff w =
        (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v := by
    exact hdecomp_rs.trans hcandidate.symm
  have hneq' : u ≠ r1 := by
    simpa [u, r1, decrs, decr, highBitsCoeff] using hneq
  have hlt_or_gt : r1 < u ∨ u < r1 := lt_or_gt_of_ne hneq'.symm
  cases hlt_or_gt with
  | inl hr1ltu =>
      let delta : ℕ := u - r1
      have hdelta0 : 0 < delta := by
        dsimp [delta]
        omega
      have hdeltalt : delta < m := by
        dsimp [delta]
        omega
      have hudelta : u = r1 + delta := by
        dsimp [delta]
        omega
      have hsub :
          (((alpha : ℕ) : Coeff) * (u : Coeff)) -
              (((alpha : ℕ) : Coeff) * (r1 : Coeff)) = intToCoeff (v - w) := by
        have htmp := congrArg
          (fun x : Coeff => x - ((((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff w)) heq
        simpa [intToCoeff] using htmp
      have hdeltaeq :
          (((alpha : ℕ) : Coeff) * (delta : Coeff)) = intToCoeff (v - w) := by
        have hdelta_cast : (u : Coeff) = (r1 : Coeff) + (delta : Coeff) := by
          rw [hudelta]
          simp
        calc
          (((alpha : ℕ) : Coeff) * (delta : Coeff))
              = (((alpha : ℕ) : Coeff) * (u : Coeff)) -
                  (((alpha : ℕ) : Coeff) * (r1 : Coeff)) := by
                    rw [hdelta_cast]
                    ring
          _ = intToCoeff (v - w) := hsub
      have hbig :
          alpha ≤ (LatticeCrypto.centeredRepr
            ((((alpha : ℕ) * delta : ℕ) : Coeff))).natAbs := by
        have hbig0 := centeredRepr_alpha_mul_natAbs_ge_of_isApproved (p := p) hp hdelta0
          (delta := delta) (by simpa [alpha, m] using hdeltalt)
        simpa [alpha] using hbig0
      have hrepr_eq := congrArg LatticeCrypto.centeredRepr hdeltaeq
      rw [hrepr_diff] at hrepr_eq
      have hbig' : alpha ≤ (v - w).natAbs := by
        rw [← hrepr_eq]
        simpa [Nat.cast_mul] using hbig
      omega
  | inr hurt1 =>
      let delta : ℕ := r1 - u
      have hdelta0 : 0 < delta := by
        dsimp [delta]
        omega
      have hdeltalt : delta < m := by
        dsimp [delta]
        omega
      have hr1delta : r1 = u + delta := by
        dsimp [delta]
        omega
      have hsub :
          (((alpha : ℕ) : Coeff) * (r1 : Coeff)) -
              (((alpha : ℕ) : Coeff) * (u : Coeff)) = intToCoeff (w - v) := by
        have htmp := congrArg
          (fun x : Coeff => x - ((((alpha : ℕ) : Coeff) * (u : Coeff)) + intToCoeff v)) heq.symm
        simpa [intToCoeff] using htmp
      have hdeltaeq :
          (((alpha : ℕ) : Coeff) * (delta : Coeff)) = intToCoeff (w - v) := by
        have hdelta_cast : (r1 : Coeff) = (u : Coeff) + (delta : Coeff) := by
          rw [hr1delta]
          simp
        calc
          (((alpha : ℕ) : Coeff) * (delta : Coeff))
              = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) -
                  (((alpha : ℕ) : Coeff) * (u : Coeff)) := by
                    rw [hdelta_cast]
                    ring
          _ = intToCoeff (w - v) := hsub
      have hbig :
          alpha ≤ (LatticeCrypto.centeredRepr
            ((((alpha : ℕ) * delta : ℕ) : Coeff))).natAbs := by
        have hbig0 := centeredRepr_alpha_mul_natAbs_ge_of_isApproved (p := p) hp hdelta0
          (delta := delta) (by simpa [alpha, m] using hdeltalt)
        simpa [alpha] using hbig0
      have hdiffbound' : (w - v).natAbs ≤ alpha - 1 := by
        have hwvupper : w - v ≤ ((alpha - 1 : ℕ) : ℤ) := by omega
        have hwvlower : -((alpha - 1 : ℕ) : ℤ) ≤ w - v := by omega
        exact natAbs_le_of_bounds hwvlower hwvupper
      have hrepr_diff' : LatticeCrypto.centeredRepr (intToCoeff (w - v)) = w - v := by
        exact centeredRepr_eq_of_natAbs_le (z := w - v) hdiffbound' hsmallq
      have hrepr_eq := congrArg LatticeCrypto.centeredRepr hdeltaeq
      rw [hrepr_diff'] at hrepr_eq
      have hbig' : alpha ≤ (w - v).natAbs := by
        rw [← hrepr_eq]
        simpa [Nat.cast_mul] using hbig
      omega

private theorem highBitsCoeff_nonneg_repr_of_isApproved (p : Params)
    (hp : p.isApproved) (u n : ℕ)
    (hu : u < (modulus - 1) / (2 * p.gamma2))
    (hn : n ≤ p.gamma2) :
    highBitsCoeff
        (intToCoeff (((((2 * p.gamma2 : ℕ) * u) + n : ℕ) : ℤ))) p.gamma2 = u := by
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  have hα : 0 < alpha := by
    have hγ : 0 < p.gamma2 := gamma2_pos_of_isApproved hp
    dsimp [alpha]
    omega
  have hm : 0 < m := by
    simpa [alpha, m] using useHintModulus_pos_of_isApproved hp
  have hqm1 : alpha * m = modulus - 1 := by
    simpa [alpha, m] using alphaMulUseHintModulus_eq_modulus_sub_one_of_isApproved p hp
  have hu_lt_m : u < m := by
    simpa [alpha, m] using hu
  have huqm1 : alpha * u < modulus - 1 := by
    exact lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_left hu_lt_m hα) hqm1
  have hltα : n < alpha := by
    dsimp [alpha]
    omega
  have hltq : alpha * u + n < modulus := by
    have hu_le : u ≤ m - 1 := by omega
    have hbound : alpha * u + n ≤ alpha * (m - 1) + p.gamma2 := by
      gcongr
    have htop : alpha * (m - 1) + p.gamma2 < modulus := by
      have hγ : 0 < p.gamma2 := gamma2_pos_of_isApproved hp
      have hlt_am : alpha * (m - 1) + p.gamma2 < alpha * m := by
        calc
          alpha * (m - 1) + p.gamma2
              < alpha * (m - 1) + p.gamma2 + p.gamma2 := Nat.lt_add_of_pos_right hγ
          _ = alpha * m := by
                calc
                  alpha * (m - 1) + p.gamma2 + p.gamma2 = alpha * (m - 1) + alpha := by
                    dsimp [alpha]
                    ring
                  _ = alpha * m := by
                    calc
                      alpha * (m - 1) + alpha = alpha * ((m - 1) + 1) := by ring
                      _ = alpha * m := by congr; omega
      have hαm_lt_mod : alpha * m < modulus := by
        rw [hqm1]
        omega
      exact lt_trans hlt_am hαm_lt_mod
    exact lt_of_le_of_lt hbound htop
  have hval :
      (intToCoeff (((alpha * u + n : ℕ) : ℤ))).val = alpha * u + n := by
    simpa [intToCoeff] using (ZMod.val_natCast_of_lt (n := modulus) (a := alpha * u + n) hltq)
  unfold highBitsCoeff decomposeCoeff
  rw [hval]
  have hmod : (alpha * u + n) % alpha = n := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hltα]
  have hdiv : (alpha * u + n) / alpha = u := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hα, Nat.div_eq_of_lt hltα, zero_add]
  have hle : (alpha * u + n) % alpha ≤ alpha / 2 := by
    rw [hmod]
    dsimp [alpha]
    omega
  have hspe : alpha * ((alpha * u + n) / alpha) ≠ modulus - 1 := by
    rw [hdiv]
    exact ne_of_lt huqm1
  simp [hmod, hdiv, hn, huqm1.ne, alpha]

private theorem highBitsCoeff_neg_repr_of_isApproved (p : Params)
    (hp : p.isApproved) (u n : ℕ)
    (hu : u < (modulus - 1) / (2 * p.gamma2))
    (hu0 : 0 < u) (hn0 : 0 < n) (hn : n < p.gamma2) :
    highBitsCoeff
        (intToCoeff ((((2 * p.gamma2 : ℕ) * u - n : ℕ) : ℤ))) p.gamma2 = u := by
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  have hα : 0 < alpha := by
    have hγ : 0 < p.gamma2 := gamma2_pos_of_isApproved hp
    dsimp [alpha]
    omega
  have hqm1 : alpha * m = modulus - 1 := by
    simpa [alpha, m] using alphaMulUseHintModulus_eq_modulus_sub_one_of_isApproved p hp
  have hu_lt_m : u < m := by
    simpa [alpha, m] using hu
  have huqm1 : alpha * u < modulus - 1 := by
    exact lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_left hu_lt_m hα) hqm1
  have hltαn : n < alpha := by
    dsimp [alpha]
    omega
  have hnle : n ≤ alpha * u := by
    have hα_le : alpha ≤ alpha * u := by
      calc
        alpha = alpha * 1 := by ring
        _ ≤ alpha * u := Nat.mul_le_mul_left alpha (show 1 ≤ u by omega)
    exact le_trans hltαn.le hα_le
  have hαu : alpha ≤ alpha * u := by
    calc
      alpha = alpha * 1 := by ring
      _ ≤ alpha * u := Nat.mul_le_mul_left alpha (show 1 ≤ u by omega)
  have hltq : alpha * u - n < modulus := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_trans huqm1 (by omega))
  have hval :
      (intToCoeff (((alpha * u - n : ℕ) : ℤ))).val = alpha * u - n := by
    simpa [intToCoeff] using (ZMod.val_natCast_of_lt (n := modulus) (a := alpha * u - n) hltq)
  have hrepr : alpha * u - n = (alpha - n) + (u - 1) * alpha := by
    have hnα : n ≤ alpha := hltαn.le
    calc
      alpha * u - n = alpha * u - alpha + (alpha - n) := by omega
      _ = (u - 1) * alpha + (alpha - n) := by
            rw [show alpha * u - alpha = alpha * (u - 1) by
              have hpred' : u - 1 + 1 = u := by omega
              calc
                alpha * u - alpha = alpha * (u - 1 + 1) - alpha := by
                  rw [hpred']
                _ = alpha * (u - 1) + alpha - alpha := by rw [Nat.mul_add, mul_one]
                _ = alpha * (u - 1) := by rw [Nat.add_sub_cancel]]
            rw [Nat.mul_comm]
      _ = (alpha - n) + (u - 1) * alpha := by rw [add_comm]
  have hltα : alpha - n < alpha := by
    exact Nat.sub_lt hα hn0
  have hmod : (alpha * u - n) % alpha = alpha - n := by
    rw [hrepr, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hltα]
  have hdiv : (alpha * u - n) / alpha = u - 1 := by
    rw [hrepr, Nat.add_mul_div_right _ _ hα, Nat.div_eq_of_lt hltα, zero_add]
  have hprev_lt : alpha * (u - 1) < modulus - 1 := by
    have hltu : u - 1 < u := Nat.sub_lt hu0 (by omega)
    exact lt_trans (Nat.mul_lt_mul_of_pos_left hltu hα) huqm1
  have hcross : ¬2 * p.gamma2 ≤ p.gamma2 + n := by
    omega
  have hpred : u - 1 + 1 = u := by
    omega
  simp [highBitsCoeff, decomposeCoeff, hval, hmod, hdiv, hcross, hpred, huqm1.ne, alpha]

private theorem highBitsCoeff_wrap_neg_repr_of_isApproved (p : Params)
    (hp : p.isApproved) (n : ℕ)
    (hn0 : 0 < n) (hn : n ≤ p.gamma2) :
    highBitsCoeff (intToCoeff (-(n : ℤ))) p.gamma2 = 0 := by
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  have hα : 0 < alpha := by
    have hγ : 0 < p.gamma2 := gamma2_pos_of_isApproved hp
    dsimp [alpha]
    omega
  have hm : 0 < m := by
    simpa [alpha, m] using useHintModulus_pos_of_isApproved hp
  have hqm1 : alpha * m = modulus - 1 := by
    simpa [alpha, m] using alphaMulUseHintModulus_eq_modulus_sub_one_of_isApproved p hp
  have hnltq : n < modulus := by
    have hγlt : p.gamma2 < modulus := by
      have hq := gamma2_double_lt_modulus_of_isApproved hp
      omega
    exact lt_of_le_of_lt hn hγlt
  have hneq : ((n : ℕ) : Coeff) ≠ 0 := by
    intro hzero
    have hdvd : modulus ∣ n := (ZMod.natCast_eq_zero_iff n modulus).mp hzero
    have hle : modulus ≤ n := Nat.le_of_dvd hn0 hdvd
    omega
  haveI : NeZero (((n : ℕ) : Coeff)) := ⟨hneq⟩
  have hvaln : (((n : ℕ) : Coeff)).val = n := by
    simpa using (ZMod.val_natCast_of_lt hnltq : (((n : ℕ) : Coeff)).val = n)
  have hval : (intToCoeff (-(n : ℤ))).val = modulus - n := by
    simpa [intToCoeff, hvaln] using (ZMod.val_neg_of_ne_zero (a := ((n : ℕ) : Coeff)))
  by_cases hn1 : n = 1
  · subst hn1
    unfold highBitsCoeff decomposeCoeff
    rw [hval]
    have hmod : (modulus - 1) % alpha = 0 := by
      rw [← hqm1]
      simp
    have hdiv : (modulus - 1) / alpha = m := by
      rw [← hqm1]
      simp [Nat.mul_div_right _ hα]
    simp [hmod, hdiv, hqm1, alpha, m]
  · have hn2 : 2 ≤ n := by omega
    have hreprNat : modulus - n = (alpha + 1 - n) + (m - 1) * alpha := by
      have hq : modulus = alpha * m + 1 := by
        omega
      have hm1 : m - 1 + 1 = m := by omega
      calc
        modulus - n = alpha * m + 1 - n := by rw [hq]
        _ = alpha * (m - 1 + 1) + 1 - n := by rw [hm1]
        _ = alpha * (m - 1) + alpha + 1 - n := by rw [Nat.mul_add, Nat.mul_one]
        _ = (alpha + 1 - n) + (m - 1) * alpha := by
              rw [Nat.mul_comm (m - 1) alpha]
              omega
    have hltα : alpha + 1 - n < alpha := by
      dsimp [alpha]
      omega
    have hmod : (modulus - n) % alpha = alpha + 1 - n := by
      rw [hreprNat, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hltα]
    have hdiv : (modulus - n) / alpha = m - 1 := by
      rw [hreprNat, Nat.add_mul_div_right _ _ hα, Nat.div_eq_of_lt hltα, zero_add]
    unfold highBitsCoeff decomposeCoeff
    rw [hval]
    have hcross : ¬(alpha + 1 - n ≤ alpha / 2) := by
      dsimp [alpha]
      omega
    have houter : ¬2 * p.gamma2 < p.gamma2 + n := by
      omega
    have hspecial : alpha * (m - 1 + 1) = modulus - 1 := by
      have hpred : m - 1 + 1 = m := by omega
      simpa [hpred] using hqm1
    simp [hmod, hdiv, houter, hspecial, alpha, m]

private theorem useHintCoeff_shift_sub_bound_of_isApproved (p : Params)
    (hp : p.isApproved) (h : Bool) (r : Coeff) :
    (LatticeCrypto.centeredRepr
      (r - (((2 * p.gamma2 : ℕ) : Coeff) * (useHintCoeff h r p.gamma2 : Coeff)))).natAbs ≤
        2 * p.gamma2 + 1 := by
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  let dec := decomposeCoeff r p.gamma2
  let r1 : ℕ := dec.1
  let r0 : ℤ := dec.2
  have hγ := gamma2_pos_of_isApproved hp
  have hm : 0 < m := by
    simpa [m, alpha] using useHintModulus_pos_of_isApproved hp
  have hsmall : 2 * (alpha + 1) < modulus := by
    simpa [alpha, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, two_mul] using
      alphaPlusOne_double_lt_modulus_of_isApproved hp
  have hdec : decomposeCoeff r p.gamma2 = (r1, r0) := by
    simp [dec, r1, r0]
  have hdecomp : (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 = r := by
    simpa [alpha, dec, r1, r0] using decomposeCoeff_eq (r := r) (gamma2 := p.gamma2) hγ
  have hr1lt : r1 < m := by
    simpa [alpha, m, dec, r1] using highBitsCoeff_lt_useHintModulus_of_isApproved p hp r
  have hr0bound : r0.natAbs ≤ p.gamma2 := by
    simpa [dec, r0] using lowBitsCoeff_bound (r := r) (gamma2 := p.gamma2) hγ
  have hr0bounds := neg_le_and_le_of_natAbs_le hr0bound
  have hr0low : -(p.gamma2 : ℤ) ≤ r0 := hr0bounds.1
  have hr0up : r0 ≤ p.gamma2 := hr0bounds.2
  cases h with
  | false =>
      have huse : useHintCoeff false r p.gamma2 = r1 := by
        simp [useHintCoeff, hdec]
      have hcoeff :
          r - (((alpha : ℕ) : Coeff) * (useHintCoeff false r p.gamma2 : Coeff)) =
            intToCoeff r0 := by
        rw [huse]
        exact sub_eq_iff_eq_add'.2 hdecomp.symm
      have hbound : r0.natAbs ≤ alpha + 1 := by
        dsimp [alpha]
        omega
      rw [hcoeff, centeredRepr_eq_of_natAbs_le (z := r0) hbound hsmall]
      exact hbound
  | true =>
      by_cases hr0pos : 0 < r0
      · by_cases hwrap : r1 + 1 < m
        · have huse : useHintCoeff true r p.gamma2 = r1 + 1 := by
            simpa [m, alpha, useHintCoeff, hdec, hr0pos] using (Nat.mod_eq_of_lt hwrap)
          have hcoeff :
              r - (((alpha : ℕ) : Coeff) * (useHintCoeff true r p.gamma2 : Coeff)) =
                intToCoeff (r0 - alpha) := by
            rw [huse]
            exact sub_eq_iff_eq_add'.2 <| by
              calc
                r = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 := hdecomp.symm
                _ = (((alpha : ℕ) : Coeff) * ((r1 + 1 : ℕ) : Coeff)) + intToCoeff (r0 - alpha) := by
                      simp [intToCoeff]
                      ring
          have hr0ge1 : 1 ≤ r0 := by omega
          have hbound : (r0 - alpha).natAbs ≤ alpha + 1 := by
            dsimp [alpha]
            omega
          rw [hcoeff, centeredRepr_eq_of_natAbs_le (z := r0 - alpha) hbound hsmall]
          exact hbound
        · have heq : r1 + 1 = m := by omega
          have hr1eq : r1 = m - 1 := by omega
          have huse : useHintCoeff true r p.gamma2 = 0 := by
            simp [useHintCoeff, hdec, hr0pos, heq, m, alpha]
          have hmulm : (((alpha : ℕ) : Coeff) * (m : Coeff)) = (-1 : Coeff) := by
            simpa [alpha, m] using alphaMulUseHintModulus_eq_neg_one_of_isApproved p hp
          have hm_succ_cast : (m : Coeff) = (((m - 1 : ℕ) : Coeff) + 1) := by
            rw [show m = (m - 1) + 1 by omega]
            norm_num
          have hcastm1 : (((m - 1 : ℕ) : Coeff)) = (m : Coeff) - 1 := by
            calc
              (((m - 1 : ℕ) : Coeff)) = ((((m - 1 : ℕ) : Coeff) + 1) - 1) := by ring
              _ = (m : Coeff) - 1 := by rw [← hm_succ_cast]
          have hmcoeff : (((alpha : ℕ) : Coeff) * (r1 : Coeff)) = (-1 : Coeff) - alpha := by
            calc
              (((alpha : ℕ) : Coeff) * (r1 : Coeff))
                  = (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff)) := by rw [hr1eq]
              _ = (((alpha : ℕ) : Coeff) * ((m : Coeff) - 1)) := by rw [hcastm1]
              _ = (((alpha : ℕ) : Coeff) * (m : Coeff)) - alpha := by
                    ring
              _ = (-1 : Coeff) - alpha := by rw [hmulm]
          have hcoeff :
              r - (((alpha : ℕ) : Coeff) * (useHintCoeff true r p.gamma2 : Coeff)) =
                intToCoeff (r0 - alpha - 1) := by
            rw [huse]
            simp only [Nat.cast_zero, mul_zero, sub_zero]
            calc
              r = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 := hdecomp.symm
              _ = intToCoeff (r0 - alpha - 1) := by
                    rw [hmcoeff]
                    simp [intToCoeff]
                    ring
          have hr0ge1 : 1 ≤ r0 := by omega
          have hbound : (r0 - alpha - 1).natAbs ≤ alpha + 1 := by
            dsimp [alpha]
            omega
          rw [hcoeff, centeredRepr_eq_of_natAbs_le (z := r0 - alpha - 1) hbound hsmall]
          exact hbound
      · have hr0nonpos : r0 ≤ 0 := le_of_not_gt hr0pos
        by_cases hr1zero : r1 = 0
        · have huse : useHintCoeff true r p.gamma2 = m - 1 := by
            have hpred : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (Nat.pred_lt hm.ne')
            simp [useHintCoeff, hdec, alpha, m, hr0pos, hr1zero, hpred]
          have hmulm : (((alpha : ℕ) : Coeff) * (m : Coeff)) = (-1 : Coeff) := by
            simpa [alpha, m] using alphaMulUseHintModulus_eq_neg_one_of_isApproved p hp
          have hm_succ_cast : (m : Coeff) = (((m - 1 : ℕ) : Coeff) + 1) := by
            rw [show m = (m - 1) + 1 by omega]
            norm_num
          have hcastm1 : (((m - 1 : ℕ) : Coeff)) = (m : Coeff) - 1 := by
            calc
              (((m - 1 : ℕ) : Coeff)) = ((((m - 1 : ℕ) : Coeff) + 1) - 1) := by ring
              _ = (m : Coeff) - 1 := by rw [← hm_succ_cast]
          have hmcoeff :
              (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff)) = (-1 : Coeff) - alpha := by
            calc
              (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff))
                  = (((alpha : ℕ) : Coeff) * ((m : Coeff) - 1)) := by rw [hcastm1]
              _ = (((alpha : ℕ) : Coeff) * (m : Coeff)) - alpha := by
                      ring
              _ = (-1 : Coeff) - alpha := by rw [hmulm]
          have hcoeff :
              r - (((alpha : ℕ) : Coeff) * (useHintCoeff true r p.gamma2 : Coeff)) =
                intToCoeff (r0 + alpha + 1) := by
            rw [huse]
            exact sub_eq_iff_eq_add'.2 <| by
              calc
                r = intToCoeff r0 := by simpa [hr1zero] using hdecomp.symm
                _ =
                    (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff)) +
                      intToCoeff (r0 + alpha + 1) := by
                      rw [hmcoeff]
                      simp [intToCoeff]
                      ring
          have hbound : (r0 + alpha + 1).natAbs ≤ alpha + 1 := by
            dsimp [alpha]
            omega
          rw [hcoeff, centeredRepr_eq_of_natAbs_le (z := r0 + alpha + 1) hbound hsmall]
          exact hbound
        · have hr1pos : 0 < r1 := Nat.pos_of_ne_zero hr1zero
          have hmle : m ≤ r1 + (m - 1) := by omega
          have hadd : (r1 + (m - 1)) % m + m = r1 + (m - 1) := by
            have hc : m ≤ r1 % m + (m - 1) % m := by
              simpa [Nat.mod_eq_of_lt hr1lt, Nat.mod_eq_of_lt (Nat.pred_lt hm.ne')] using hmle
            simpa [Nat.mod_eq_of_lt hr1lt, Nat.mod_eq_of_lt (Nat.pred_lt hm.ne')] using
              (Nat.add_mod_add_of_le_add_mod (a := r1) (b := m - 1) (c := m) hc)
          have hmod : (r1 + (m - 1)) % m = r1 - 1 := by
            omega
          have hmod' : (r1 + m - 1) % m = r1 - 1 := by
            have hsum : r1 + m - 1 = r1 + (m - 1) := by omega
            rw [hsum]
            exact hmod
          have huse : useHintCoeff true r p.gamma2 = r1 - 1 := by
            simpa [useHintCoeff, hdec, hr0pos, m, alpha] using hmod'
          have hr1_succ_cast : (r1 : Coeff) = (((r1 - 1 : ℕ) : Coeff) + 1) := by
            rw [show r1 = (r1 - 1) + 1 by omega]
            norm_num
          have hcastr1 : (((r1 - 1 : ℕ) : Coeff)) = (r1 : Coeff) - 1 := by
            calc
              (((r1 - 1 : ℕ) : Coeff)) = ((((r1 - 1 : ℕ) : Coeff) + 1) - 1) := by ring
              _ = (r1 : Coeff) - 1 := by rw [← hr1_succ_cast]
          have hcoeff :
              r - (((alpha : ℕ) : Coeff) * (useHintCoeff true r p.gamma2 : Coeff)) =
                intToCoeff (r0 + alpha) := by
            rw [huse]
            exact sub_eq_iff_eq_add'.2 <| by
              calc
                r = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 := hdecomp.symm
                _ = (((alpha : ℕ) : Coeff) * ((r1 - 1 : ℕ) : Coeff)) + intToCoeff (r0 + alpha) := by
                      rw [hcastr1]
                      simp [intToCoeff]
                      ring
          have hbound : (r0 + alpha).natAbs ≤ alpha + 1 := by
            dsimp [alpha]
            omega
          rw [hcoeff, centeredRepr_eq_of_natAbs_le (z := r0 + alpha) hbound hsmall]
          exact hbound

private theorem highBitsCoeff_eq_of_mid_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Coeff) (z0 : ℤ)
    (hvlow : let r0 : ℤ := (decomposeCoeff r p.gamma2).2; -(p.gamma2 : ℤ) < r0 + z0)
    (hvup : let r0 : ℤ := (decomposeCoeff r p.gamma2).2; r0 + z0 ≤ p.gamma2) :
    highBitsCoeff (r + intToCoeff z0) p.gamma2 = highBitsCoeff r p.gamma2 := by
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  let decr := decomposeCoeff r p.gamma2
  let r1 : ℕ := decr.1
  let r0 : ℤ := decr.2
  let v : ℤ := r0 + z0
  have hvlow' : -(p.gamma2 : ℤ) < v := by
    simpa [decr, r0, v] using hvlow
  have hvup' : v ≤ p.gamma2 := by
    simpa [decr, r0, v] using hvup
  have hγ := gamma2_pos_of_isApproved hp
  have hdec : decomposeCoeff r p.gamma2 = (r1, r0) := by
    simp [decr, r1, r0]
  have hr1lt : r1 < m := by
    simpa [alpha, m, decr, r1] using highBitsCoeff_lt_useHintModulus_of_isApproved p hp r
  have hr1eq : highBitsCoeff r p.gamma2 = r1 := by
    simp [highBitsCoeff, decr, r1]
  have hdecomp :
      (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 = r := by
    simpa [alpha, decr, r1, r0] using decomposeCoeff_eq (r := r) (gamma2 := p.gamma2) hγ
  have hsum :
      (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v = r + intToCoeff z0 := by
    calc
      (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v
          = ((((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0) + intToCoeff z0 := by
              dsimp [v]
              simp [intToCoeff]
              ring
      _ = r + intToCoeff z0 := by rw [hdecomp]
  by_cases hvnonneg : 0 ≤ v
  · have hvnat : (((v.natAbs : ℕ) : ℤ)) = v := by
      simpa using (Int.natAbs_of_nonneg hvnonneg)
    have hvnat_le : v.natAbs ≤ p.gamma2 := by
      have : (((v.natAbs : ℕ) : ℤ)) ≤ p.gamma2 := by
        rw [hvnat]
        exact_mod_cast hvup'
      exact_mod_cast this
    have hvcast : intToCoeff v = ((v.natAbs : ℕ) : Coeff) := by
      simpa [intToCoeff] using (congrArg (fun z : ℤ => (z : Coeff)) hvnat).symm
    have hcoeff :
        r + intToCoeff z0 =
          ((alpha * r1 + v.natAbs : ℕ) : Coeff) := by
      calc
        r + intToCoeff z0 = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v := by
          simpa [add_comm] using hsum.symm
        _ = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + ((v.natAbs : ℕ) : Coeff) := by
          rw [hvcast]
        _ = ((alpha * r1 + v.natAbs : ℕ) : Coeff) := by
          simp [Nat.cast_add, Nat.cast_mul]
    have hgoal :
        highBitsCoeff (r + intToCoeff z0) p.gamma2 = r1 := by
      rw [hcoeff]
      simpa [intToCoeff, alpha] using
        (highBitsCoeff_nonneg_repr_of_isApproved p hp r1 v.natAbs
          (by simpa [alpha, m] using hr1lt) hvnat_le)
    simpa [hr1eq] using hgoal
  · have hvneg : v < 0 := lt_of_not_ge hvnonneg
    have hnatv : (((v.natAbs : ℕ) : ℤ)) = -v := by
      simpa using (Int.ofNat_natAbs_of_nonpos hvneg.le)
    have hnatv0 : 0 < v.natAbs := by
      have : (0 : ℤ) < (((v.natAbs : ℕ) : ℤ)) := by
        rw [hnatv]
        omega
      exact_mod_cast this
    have hnatv_lt : v.natAbs < p.gamma2 := by
      have : (((v.natAbs : ℕ) : ℤ)) < p.gamma2 := by
        rw [hnatv]
        omega
      exact_mod_cast this
    have hvcast : intToCoeff v = -((v.natAbs : ℕ) : Coeff) := by
      calc
        intToCoeff v = -intToCoeff (-v) := by simp [intToCoeff]
        _ = -((v.natAbs : ℕ) : Coeff) := by
          congr 1
          simpa [intToCoeff] using
            (congrArg (fun z : ℤ => (z : Coeff)) hnatv).symm
    by_cases hr1zero : r1 = 0
    · have hcoeff : r + intToCoeff z0 = -((v.natAbs : ℕ) : Coeff) := by
        calc
          r + intToCoeff z0 = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v := by
            simpa [add_comm] using hsum.symm
          _ = intToCoeff v := by rw [hr1zero]; simp
          _ = -((v.natAbs : ℕ) : Coeff) := by
            rw [hvcast]
      rw [hcoeff, hr1eq, hr1zero]
      simpa [intToCoeff, alpha] using
        (highBitsCoeff_wrap_neg_repr_of_isApproved p hp v.natAbs hnatv0 hnatv_lt.le)
    · have hr1pos : 0 < r1 := Nat.pos_of_ne_zero hr1zero
      have hnatv_le : v.natAbs ≤ alpha * r1 := by
        have hltα : v.natAbs < alpha := by
          have : (((v.natAbs : ℕ) : ℤ)) < alpha := by
            rw [hnatv]
            dsimp [alpha]
            omega
          exact_mod_cast this
        have hαu : alpha ≤ alpha * r1 := by
          calc
            alpha = alpha * 1 := by ring
            _ ≤ alpha * r1 := Nat.mul_le_mul_left alpha (show 1 ≤ r1 by omega)
        exact le_trans hltα.le hαu
      have hcoeff :
          r + intToCoeff z0 =
            ((alpha * r1 - v.natAbs : ℕ) : Coeff) := by
        calc
          r + intToCoeff z0 = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v := by
            simpa [add_comm] using hsum.symm
          _ = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) - ((v.natAbs : ℕ) : Coeff) := by
            rw [hvcast]
            ring
          _ = ((alpha * r1 - v.natAbs : ℕ) : Coeff) := by
            rw [← Nat.cast_mul, ← Nat.cast_sub hnatv_le]
      rw [hcoeff, hr1eq]
      simpa [intToCoeff, alpha] using
        (highBitsCoeff_neg_repr_of_isApproved p hp r1 v.natAbs
          (by simpa [alpha, m] using hr1lt) hr1pos hnatv0 hnatv_lt)

private theorem useHintCoeff_correct_of_small_of_isApproved (p : Params)
    (hp : p.isApproved) (z r : Coeff)
    (hz : (LatticeCrypto.centeredRepr z).natAbs ≤ p.gamma2) :
    useHintCoeff (makeHintCoeff z r p.gamma2) r p.gamma2 =
      highBitsCoeff (r + z) p.gamma2 := by
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  let decr := decomposeCoeff r p.gamma2
  let r1 : ℕ := decr.1
  let r0 : ℤ := decr.2
  let z0 : ℤ := LatticeCrypto.centeredRepr z
  let v : ℤ := r0 + z0
  have hγ := gamma2_pos_of_isApproved hp
  have hm : 0 < m := by
    simpa [alpha, m] using useHintModulus_pos_of_isApproved hp
  have hdec : decomposeCoeff r p.gamma2 = (r1, r0) := by
    simp [decr, r1, r0]
  have hr1eq : highBitsCoeff r p.gamma2 = r1 := by
    simp [highBitsCoeff, decr, r1]
  have hr1lt : r1 < m := by
    simpa [alpha, m, decr, r1] using highBitsCoeff_lt_useHintModulus_of_isApproved p hp r
  have hr0bound : r0.natAbs ≤ p.gamma2 := by
    simpa [decr, r0] using lowBitsCoeff_bound (r := r) (gamma2 := p.gamma2) hγ
  have hr0bounds := neg_le_and_le_of_natAbs_le hr0bound
  have hr0low : -(p.gamma2 : ℤ) ≤ r0 := hr0bounds.1
  have hr0up : r0 ≤ p.gamma2 := hr0bounds.2
  have hzbounds := neg_le_and_le_of_natAbs_le hz
  have hzlow : -(p.gamma2 : ℤ) ≤ z0 := hzbounds.1
  have hzup : z0 ≤ p.gamma2 := hzbounds.2
  have hzcast : z = intToCoeff z0 := by
    simpa [z0] using centeredRepr_cast z
  have hdecomp :
      (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 = r := by
    simpa [alpha, decr, r1, r0] using decomposeCoeff_eq (r := r) (gamma2 := p.gamma2) hγ
  have hsum :
      (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v = r + z := by
    calc
      (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v
          = ((((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0) + intToCoeff z0 := by
              dsimp [v]
              simp [intToCoeff]
              ring
      _ = r + z := by rw [hdecomp]; simp [hzcast]
  by_cases hneq : highBitsCoeff r p.gamma2 ≠ highBitsCoeff (r + z) p.gamma2
  · have hhint : makeHintCoeff z r p.gamma2 = true := by
      simp [makeHintCoeff, hneq]
    by_cases hr0pos : 0 < r0
    · have hvlow : -(p.gamma2 : ℤ) < v := by
        dsimp [v]
        omega
      have hvupα : v ≤ alpha := by
        dsimp [v, alpha]
        omega
      have hvnotmid : ¬ v ≤ p.gamma2 := by
        intro hvmid
        have hsame := highBitsCoeff_eq_of_mid_of_isApproved p hp r z0
          (hvlow := by simpa [decr, r0, z0, v] using hvlow)
          (hvup := by simpa [decr, r0, z0, v] using hvmid)
        exact hneq (by simpa [hzcast] using hsame.symm)
      have hvgt : p.gamma2 < v := by
        omega
      have hvnonneg : 0 ≤ v := by omega
      have hvnat : (((v.natAbs : ℕ) : ℤ)) = v := by
        simpa using (Int.natAbs_of_nonneg hvnonneg)
      have hvcast : intToCoeff v = ((v.natAbs : ℕ) : Coeff) := by
        simpa [intToCoeff] using (congrArg (fun z : ℤ => (z : Coeff)) hvnat).symm
      by_cases hwrap : r1 + 1 < m
      · have huse : useHintCoeff true r p.gamma2 = r1 + 1 := by
          simpa [m, alpha, useHintCoeff, hdec, hr0pos] using (Nat.mod_eq_of_lt hwrap)
        by_cases hvEqAlpha : v.natAbs = alpha
        · have hgoal : highBitsCoeff (r + z) p.gamma2 = r1 + 1 := by
            have hcoeff :
                r + z = ((alpha * (r1 + 1) : ℕ) : Coeff) := by
              calc
                r + z = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v := by
                  simpa [add_comm] using hsum.symm
                _ = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + ((v.natAbs : ℕ) : Coeff) := by
                  rw [hvcast]
                _ = ((alpha * (r1 + 1) : ℕ) : Coeff) := by
                  rw [show alpha * (r1 + 1) = alpha + alpha * r1 by ring]
                  rw [hvEqAlpha]
                  simp [Nat.cast_mul, Nat.cast_add, add_comm]
            rw [hcoeff]
            simpa [intToCoeff, alpha] using
              (highBitsCoeff_nonneg_repr_of_isApproved p hp (r1 + 1) 0
                (by simpa [alpha, m] using hwrap) (show 0 ≤ p.gamma2 by omega))
          simpa [hhint, huse] using hgoal.symm
        · let n : ℕ := alpha - v.natAbs
          have hnatabs_le_alpha : v.natAbs ≤ alpha := by
            have : (((v.natAbs : ℕ) : ℤ)) ≤ alpha := by
              rw [hvnat]
              exact_mod_cast hvupα
            exact_mod_cast this
          have hnatabs_lt_alpha : v.natAbs < alpha := by
            exact lt_of_le_of_ne hnatabs_le_alpha (by simpa using hvEqAlpha)
          have hnatabs_gt_gamma : p.gamma2 < v.natAbs := by
            have : (p.gamma2 : ℤ) < ((v.natAbs : ℕ) : ℤ) := by
              rw [hvnat]
              exact_mod_cast hvgt
            exact_mod_cast this
          have hn0 : 0 < n := by
            dsimp [n]
            omega
          have hnlt : n < p.gamma2 := by
            dsimp [n]
            omega
          have hgoal : highBitsCoeff (r + z) p.gamma2 = r1 + 1 := by
            have hcoeff :
                r + z = ((alpha * (r1 + 1) - n : ℕ) : Coeff) := by
              calc
                r + z = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v := by
                  simpa [add_comm] using hsum.symm
                _ = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + ((v.natAbs : ℕ) : Coeff) := by
                  rw [hvcast]
                _ = ((alpha * r1 + v.natAbs : ℕ) : Coeff) := by
                  simp [Nat.cast_add, Nat.cast_mul]
                _ = ((alpha * (r1 + 1) - n : ℕ) : Coeff) := by
                  have hrepr : alpha * (r1 + 1) - n = alpha * r1 + v.natAbs := by
                    dsimp [n]
                    have hle : v.natAbs ≤ alpha := hnatabs_le_alpha
                    calc
                      alpha * (r1 + 1) - (alpha - v.natAbs)
                          = alpha * r1 + alpha - (alpha - v.natAbs) := by
                              rw [Nat.mul_add, Nat.mul_one]
                      _ = alpha * r1 + (alpha - (alpha - v.natAbs)) := by
                            omega
                      _ = alpha * r1 + v.natAbs := by
                            rw [Nat.sub_sub_self hle]
                  rw [hrepr]
            rw [hcoeff]
            simpa [intToCoeff, alpha, n] using
              (highBitsCoeff_neg_repr_of_isApproved p hp (r1 + 1) n
                (by simpa [alpha, m] using hwrap) (show 0 < r1 + 1 by omega) hn0 hnlt)
          simpa [hhint, huse] using hgoal.symm
      · have heq : r1 + 1 = m := by
          omega
        have hr1eqm1 : r1 = m - 1 := by
          omega
        have huse : useHintCoeff true r p.gamma2 = 0 := by
          simp [useHintCoeff, hdec, hr0pos, heq, m, alpha]
        have hmulm : (((alpha : ℕ) : Coeff) * (m : Coeff)) = (-1 : Coeff) := by
          simpa [alpha, m] using alphaMulUseHintModulus_eq_neg_one_of_isApproved p hp
        have hm_succ_cast : (m : Coeff) = (((m - 1 : ℕ) : Coeff) + 1) := by
          rw [show m = (m - 1) + 1 by omega]
          norm_num
        have hcastm1 : (((m - 1 : ℕ) : Coeff)) = (m : Coeff) - 1 := by
          calc
            (((m - 1 : ℕ) : Coeff)) = ((((m - 1 : ℕ) : Coeff) + 1) - 1) := by ring
            _ = (m : Coeff) - 1 := by rw [← hm_succ_cast]
        have hmcoeff :
            (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff)) = (-1 : Coeff) - alpha := by
          calc
            (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff))
                = (((alpha : ℕ) : Coeff) * ((m : Coeff) - 1)) := by rw [hcastm1]
            _ = (((alpha : ℕ) : Coeff) * (m : Coeff)) - alpha := by ring
            _ = (-1 : Coeff) - alpha := by rw [hmulm]
        let n : ℕ := alpha + 1 - v.natAbs
        have hnatabs_le_alpha : v.natAbs ≤ alpha := by
          have : (((v.natAbs : ℕ) : ℤ)) ≤ alpha := by
            rw [hvnat]
            exact_mod_cast hvupα
          exact_mod_cast this
        have hnatabs_gt_gamma : p.gamma2 < v.natAbs := by
          have : (p.gamma2 : ℤ) < ((v.natAbs : ℕ) : ℤ) := by
            rw [hvnat]
            exact_mod_cast hvgt
          exact_mod_cast this
        have hn0 : 0 < n := by
          dsimp [n]
          omega
        have hnle : n ≤ p.gamma2 := by
          dsimp [n]
          omega
        have hgoal : highBitsCoeff (r + z) p.gamma2 = 0 := by
          have hcoeff : r + z = intToCoeff (-(n : ℤ)) := by
            calc
              r + z = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v := by
                simpa [add_comm] using hsum.symm
              _ = (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff)) + intToCoeff v := by
                rw [hr1eqm1]
              _ = (-1 : Coeff) - alpha + intToCoeff v := by
                rw [hmcoeff]
              _ = intToCoeff (-(n : ℤ)) := by
                rw [hvcast]
                have hrepr : (-(n : ℤ)) = ((v.natAbs : ℕ) : ℤ) - alpha - 1 := by
                  dsimp [n]
                  omega
                rw [hrepr]
                simp [intToCoeff]
                ring
          rw [hcoeff]
          simpa [intToCoeff, alpha, n] using
            (highBitsCoeff_wrap_neg_repr_of_isApproved p hp n hn0 hnle)
        simpa [hhint, huse] using hgoal.symm
    · have hr0nonpos : r0 ≤ 0 := le_of_not_gt hr0pos
      have hvup : v ≤ p.gamma2 := by
        dsimp [v]
        omega
      by_cases hr1zero : r1 = 0
      · have hvnotmid : ¬ -(p.gamma2 : ℤ) < v := by
          intro hvlow
          have hsame := highBitsCoeff_eq_of_mid_of_isApproved p hp r z0
            (hvlow := by simpa [decr, r0, z0, v] using hvlow)
            (hvup := by simpa [decr, r0, z0, v] using hvup)
          exact hneq (by simpa [hzcast] using hsame.symm)
        have hveq_not : v ≠ -(p.gamma2 : ℤ) := by
          intro hveq
          have hcoeff : r + z = -((p.gamma2 : ℕ) : Coeff) := by
            calc
              r + z = intToCoeff v := by
                simpa [hr1zero, add_comm] using hsum.symm
              _ = -((p.gamma2 : ℕ) : Coeff) := by
                rw [hveq]
                simp [intToCoeff]
          have hsame0 : highBitsCoeff (r + z) p.gamma2 = 0 := by
            rw [hcoeff]
            simpa [intToCoeff, alpha] using
              (highBitsCoeff_wrap_neg_repr_of_isApproved p hp p.gamma2 hγ le_rfl)
          exact hneq (by simpa [hr1eq, hr1zero] using hsame0.symm)
        have hvlt : v < -(p.gamma2 : ℤ) := by
          omega
        have huse : useHintCoeff true r p.gamma2 = m - 1 := by
          have hpred : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (Nat.pred_lt hm.ne')
          simp [useHintCoeff, hdec, alpha, m, hr0pos, hr1zero, hpred]
        have hmulm : (((alpha : ℕ) : Coeff) * (m : Coeff)) = (-1 : Coeff) := by
          simpa [alpha, m] using alphaMulUseHintModulus_eq_neg_one_of_isApproved p hp
        have hm_succ_cast : (m : Coeff) = (((m - 1 : ℕ) : Coeff) + 1) := by
          rw [show m = (m - 1) + 1 by omega]
          norm_num
        have hcastm1 : (((m - 1 : ℕ) : Coeff)) = (m : Coeff) - 1 := by
          calc
            (((m - 1 : ℕ) : Coeff)) = ((((m - 1 : ℕ) : Coeff) + 1) - 1) := by ring
            _ = (m : Coeff) - 1 := by rw [← hm_succ_cast]
        have hmcoeff :
            (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff)) = (-1 : Coeff) - alpha := by
          calc
            (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff))
                = (((alpha : ℕ) : Coeff) * ((m : Coeff) - 1)) := by rw [hcastm1]
            _ = (((alpha : ℕ) : Coeff) * (m : Coeff)) - alpha := by ring
            _ = (-1 : Coeff) - alpha := by rw [hmulm]
        have hvneg : v < 0 := by omega
        have hnatv : (((v.natAbs : ℕ) : ℤ)) = -v := by
          simpa using (Int.ofNat_natAbs_of_nonpos hvneg.le)
        let n : ℕ := alpha + 1 - v.natAbs
        have hnatabs_gt_gamma : p.gamma2 < v.natAbs := by
          have : (p.gamma2 : ℤ) < ((v.natAbs : ℕ) : ℤ) := by
            rw [hnatv]
            omega
          exact_mod_cast this
        have hn0 : 0 < n := by
          dsimp [n]
          omega
        have hnle : n ≤ p.gamma2 := by
          dsimp [n]
          omega
        have hgoal : highBitsCoeff (r + z) p.gamma2 = m - 1 := by
          have hcoeff : r + z = ((alpha * (m - 1) + n : ℕ) : Coeff) := by
            calc
              r + z = intToCoeff v := by
                simpa [hr1zero, add_comm] using hsum.symm
              _ = intToCoeff (-((v.natAbs : ℕ) : ℤ)) := by
                have hvrepr : v = -((v.natAbs : ℕ) : ℤ) := by
                  rw [hnatv]
                  ring
                rw [hvrepr]
                have hnonpos : -((v.natAbs : ℕ) : ℤ) ≤ 0 := by omega
                simp [intToCoeff]
              _ = (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff)) + (n : Coeff) := by
                rw [hmcoeff]
                have hrepr : (-((v.natAbs : ℕ) : ℤ)) = (n : ℤ) - alpha - 1 := by
                  dsimp [n]
                  omega
                rw [hrepr]
                simp [intToCoeff]
                ring
              _ = ((alpha * (m - 1) + n : ℕ) : Coeff) := by
                simp [Nat.cast_add, Nat.cast_mul]
          rw [hcoeff]
          simpa [intToCoeff, alpha, n] using
            (highBitsCoeff_nonneg_repr_of_isApproved p hp (m - 1) n
              (Nat.pred_lt hm.ne') hnle)
        simpa [hhint, huse] using hgoal.symm
      · have hvnotmid : ¬ -(p.gamma2 : ℤ) < v := by
          intro hvlow
          have hsame := highBitsCoeff_eq_of_mid_of_isApproved p hp r z0
            (hvlow := by simpa [decr, r0, z0, v] using hvlow)
            (hvup := by simpa [decr, r0, z0, v] using hvup)
          exact hneq (by simpa [hzcast] using hsame.symm)
        have hvle : v ≤ -(p.gamma2 : ℤ) := by
          omega
        have hr1pos : 0 < r1 := Nat.pos_of_ne_zero hr1zero
        have hmle : m ≤ r1 + (m - 1) := by omega
        have hadd : (r1 + (m - 1)) % m + m = r1 + (m - 1) := by
          have hc : m ≤ r1 % m + (m - 1) % m := by
            simpa [Nat.mod_eq_of_lt hr1lt, Nat.mod_eq_of_lt (Nat.pred_lt hm.ne')] using hmle
          simpa [Nat.mod_eq_of_lt hr1lt, Nat.mod_eq_of_lt (Nat.pred_lt hm.ne')] using
            (Nat.add_mod_add_of_le_add_mod (a := r1) (b := m - 1) (c := m) hc)
        have hmod : (r1 + (m - 1)) % m = r1 - 1 := by
          omega
        have hmod' : (r1 + m - 1) % m = r1 - 1 := by
          have hsum' : r1 + m - 1 = r1 + (m - 1) := by omega
          rw [hsum']
          exact hmod
        have huse : useHintCoeff true r p.gamma2 = r1 - 1 := by
          simpa [useHintCoeff, hdec, hr0pos, m, alpha] using hmod'
        have hvneg : v < 0 := by omega
        have hnatv : (((v.natAbs : ℕ) : ℤ)) = -v := by
          simpa using (Int.ofNat_natAbs_of_nonpos hvneg.le)
        have hr1pred_lt : r1 - 1 < m := by
          omega
        have hr0gt : -(p.gamma2 : ℤ) < r0 := by
          by_contra hr0le
          have hr0eq : r0 = -(p.gamma2 : ℤ) := by
            omega
          have hγle : p.gamma2 ≤ alpha * r1 := by
            have hαu : alpha ≤ alpha * r1 := by
              calc
                alpha = alpha * 1 := by ring
                _ ≤ alpha * r1 := Nat.mul_le_mul_left alpha (show 1 ≤ r1 by omega)
            exact le_trans (by dsimp [alpha]; omega) hαu
          have hcoeff0 : r = ((alpha * (r1 - 1) + p.gamma2 : ℕ) : Coeff) := by
            calc
              r = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 := hdecomp.symm
              _ = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff (-(p.gamma2 : ℤ)) := by
                    rw [hr0eq]
              _ = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) - ((p.gamma2 : ℕ) : Coeff) := by
                    simp [intToCoeff]
                    ring
              _ = ((alpha * r1 - p.gamma2 : ℕ) : Coeff) := by
                    rw [← Nat.cast_mul, ← Nat.cast_sub hγle]
              _ = ((alpha * (r1 - 1) + p.gamma2 : ℕ) : Coeff) := by
                    have hrepr : alpha * r1 - p.gamma2 = alpha * (r1 - 1) + p.gamma2 := by
                      have hr1succ : r1 = (r1 - 1) + 1 := by omega
                      rw [hr1succ, Nat.mul_add, Nat.mul_one]
                      dsimp [alpha]
                      omega
                    rw [hrepr]
          have hsame0 : highBitsCoeff r p.gamma2 = r1 - 1 := by
            rw [hcoeff0]
            simpa [intToCoeff, alpha] using
              (highBitsCoeff_nonneg_repr_of_isApproved p hp (r1 - 1) p.gamma2 hr1pred_lt le_rfl)
          have : r1 = r1 - 1 := by
            simpa [hr1eq] using hsame0
          omega
        have hvgt_neg_alpha : -(alpha : ℤ) < v := by
          dsimp [v, alpha]
          omega
        have hnatv_ltα : v.natAbs < alpha := by
          have : (((v.natAbs : ℕ) : ℤ)) < alpha := by
            rw [hnatv]
            simpa using (neg_lt_neg hvgt_neg_alpha)
          exact_mod_cast this
        have hnatv_le : v.natAbs ≤ alpha * r1 := by
          have hαu : alpha ≤ alpha * r1 := by
            calc
              alpha = alpha * 1 := by ring
              _ ≤ alpha * r1 := Nat.mul_le_mul_left alpha (show 1 ≤ r1 by omega)
          exact le_trans hnatv_ltα.le hαu
        let n : ℕ := alpha - v.natAbs
        have hnle : n ≤ p.gamma2 := by
          dsimp [n]
          omega
        have hgoal : highBitsCoeff (r + z) p.gamma2 = r1 - 1 := by
          have hvcast : intToCoeff v = -((v.natAbs : ℕ) : Coeff) := by
            calc
              intToCoeff v = -intToCoeff (-v) := by simp [intToCoeff]
              _ = -((v.natAbs : ℕ) : Coeff) := by
                congr 1
                simpa [intToCoeff] using
                  (congrArg (fun z : ℤ => (z : Coeff)) hnatv).symm
          have hcoeff : r + z = ((alpha * (r1 - 1) + n : ℕ) : Coeff) := by
            calc
              r + z = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v := by
                simpa [add_comm] using hsum.symm
              _ = (((alpha : ℕ) : Coeff) * (r1 : Coeff)) - ((v.natAbs : ℕ) : Coeff) := by
                rw [hvcast]
                ring
              _ = ((alpha * r1 - v.natAbs : ℕ) : Coeff) := by
                rw [← Nat.cast_mul, ← Nat.cast_sub hnatv_le]
              _ = ((alpha * (r1 - 1) + n : ℕ) : Coeff) := by
                have hrepr : alpha * (r1 - 1) + n = alpha * r1 - v.natAbs := by
                  dsimp [n]
                  have hle : v.natAbs ≤ alpha := hnatv_ltα.le
                  calc
                    alpha * (r1 - 1) + (alpha - v.natAbs)
                        = alpha * (r1 - 1) + alpha - v.natAbs := by
                            rw [Nat.add_sub_assoc hle]
                    _ = alpha * r1 - v.natAbs := by
                          have hr1repr : alpha * r1 = alpha * (r1 - 1) + alpha := by
                            have hr1succ : r1 - 1 + 1 = r1 := by omega
                            have hpred : r1 - 1 + 1 - 1 = r1 - 1 := by omega
                            rw [← hr1succ, Nat.mul_add, Nat.mul_one, hpred]
                          rw [hr1repr]
                rw [hrepr]
          rw [hcoeff]
          simpa [intToCoeff, alpha, n] using
            (highBitsCoeff_nonneg_repr_of_isApproved p hp (r1 - 1) n
              hr1pred_lt hnle)
        simpa [hhint, huse] using hgoal.symm
  · have hsame : highBitsCoeff r p.gamma2 = highBitsCoeff (r + z) p.gamma2 := by
      exact not_ne_iff.mp hneq
    calc
      useHintCoeff (makeHintCoeff z r p.gamma2) r p.gamma2 = r1 := by
        simp [makeHintCoeff, hneq, useHintCoeff, hdec]
      _ = highBitsCoeff (r + z) p.gamma2 := by
        simpa [hr1eq] using hsame

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
def concretePower2RoundOps : MLDSA.Power2RoundOps where
  Power2High := Power2High
  power2Round := power2RoundHigh
  shift2 := power2RoundShift

theorem concretePower2Round_bound_field (r : Rq) :
    LatticeCrypto.cInfNorm
      (r - concretePower2RoundOps.shift2 (concretePower2RoundOps.power2Round r)) ≤
        2 ^ (droppedBits - 1) := by
  simpa [concretePower2RoundOps] using concretePower2Round_bound r

/-- Concrete `RoundingOps` with `High = Rq` and Boolean hints. -/
def concreteRoundingOps (p : Params) : MLDSA.RoundingOps (2 * p.gamma2) where
  High := High
  Hint := Hint
  lowBits := lowBits p
  highBits := highBits p
  shift := highBitsShift p
  makeHint := makeHint p
  useHint := useHint p

theorem concreteRounding_high_low_decomp_field_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) :
    (concreteRoundingOps p).shift ((concreteRoundingOps p).highBits r) +
      (concreteRoundingOps p).lowBits r = r := by
  change highBitsShift p (highBits p r) + lowBits p r = r
  exact concreteRounding_high_low_decomp_of_isApproved p hp r

theorem concreteRounding_lowBits_bound_field_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) :
    LatticeCrypto.cInfNorm ((concreteRoundingOps p).lowBits r) ≤ (2 * p.gamma2) / 2 := by
  have hbound := concreteRounding_lowBits_bound_of_isApproved p hp r
  have hhalf : (2 * p.gamma2) / 2 = p.gamma2 := by
    omega
  change LatticeCrypto.cInfNorm (lowBits p r) ≤ (2 * p.gamma2) / 2
  simpa [hhalf] using hbound

theorem concreteRounding_shift_injective_field_of_isApproved (p : Params)
    (hp : p.isApproved) :
    Function.Injective (concreteRoundingOps p).shift := by
  change Function.Injective (highBitsShift p)
  exact highBitsShift_injective_of_isApproved p hp

private theorem highBitsShift_useHint_get (p : Params) (h : Hint) (r : Rq) (i : Fin ringDegree) :
    (highBitsShift p (useHint p h r)).get i =
      ((2 * p.gamma2 : ℕ) : Coeff) * (useHintCoeff (h.get i) (r.get i) p.gamma2 : Coeff) := by
  simp [highBitsShift, useHint]

private theorem useHint_get (p : Params) (h : Hint) (r : Rq) (i : Fin ringDegree) :
    (useHint p h r).get i = (useHintCoeff (h.get i) (r.get i) p.gamma2 : Coeff) := by
  simp [useHint]

private theorem makeHint_get (p : Params) (z r : Rq) (i : Fin ringDegree) :
    (makeHint p z r).get i = makeHintCoeff (z.get i) (r.get i) p.gamma2 := by
  simp [makeHint]

theorem concreteRounding_useHint_correct_of_isApproved (p : Params)
    (hp : p.isApproved) (z r : Rq) :
    LatticeCrypto.cInfNorm z ≤ p.gamma2 →
    useHint p (makeHint p z r) r = highBits p (r + z) := by
  intro hz
  apply Vector.ext
  intro i hi
  let j : Fin ringDegree := ⟨i, hi⟩
  have hzj : (LatticeCrypto.centeredRepr (z.get j)).natAbs ≤ p.gamma2 := by
    exact (LatticeCrypto.cInfNorm_le_iff.mp hz) j
  have hcoef :
      (useHint p (makeHint p z r) r).get j = (highBits p (r + z)).get j := by
    rw [useHint_get]
    rw [makeHint_get]
    rw [highBits, Vector.get_ofFn]
    have hadd : (r + z).get j = r.get j + z.get j := by
      rw [Vector.get_eq_getElem, Vector.getElem_add]
      simp [Vector.get_eq_getElem]
    rw [hadd]
    exact congrArg (fun n : ℕ => (n : Coeff))
      (useHintCoeff_correct_of_small_of_isApproved p hp (z := z.get j) (r := r.get j) hzj)
  simpa [Vector.get_eq_getElem] using hcoef

theorem concreteRounding_useHint_bound_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) (h : Hint) :
    LatticeCrypto.cInfNorm (r - highBitsShift p (useHint p h r)) ≤ 2 * p.gamma2 + 1 := by
  refine LatticeCrypto.cInfNorm_le_of_coeff_le ?_
  intro i
  rw [Vector.get_eq_getElem]
  rw [Vector.getElem_sub]
  have hshift :
      (highBitsShift p (useHint p h r))[i.1] =
        ((2 * p.gamma2 : ℕ) : Coeff) * (useHintCoeff (h.get i) (r.get i) p.gamma2 : Coeff) := by
    simpa [Vector.get_eq_getElem] using highBitsShift_useHint_get p h r i
  rw [hshift]
  simpa [Vector.get_eq_getElem] using
    useHintCoeff_shift_sub_bound_of_isApproved p hp (h.get i) (r.get i)

theorem concreteRounding_hide_low_of_isApproved (p : Params)
    (hp : p.isApproved) (r s : Rq) (b : ℕ) :
    LatticeCrypto.cInfNorm s ≤ b →
    LatticeCrypto.cInfNorm (lowBits p r) + b < p.gamma2 →
    highBits p (r + s) = highBits p r := by
  intro hs hlow
  have hfin : ∀ j : Fin ringDegree, (highBits p (r + s)).get j = (highBits p r).get j := by
    intro j
    have hsj : (LatticeCrypto.centeredRepr (s.get j)).natAbs ≤ b := by
      exact (LatticeCrypto.cInfNorm_le_iff.mp hs) j
    have hlowj0 :
        (LatticeCrypto.centeredRepr ((lowBits p r).get j)).natAbs < p.gamma2 - b := by
      have hcoeff := LatticeCrypto.coeff_le_cInfNorm (lowBits p r) j
      omega
    have hlowj : (lowBitsCoeff (r.get j) p.gamma2).natAbs < p.gamma2 - b := by
      have hq := gamma2_double_lt_modulus_of_isApproved hp
      rw [lowBits_get, lowBits_centeredRepr (r := r.get j)
        (hγ := gamma2_pos_of_isApproved hp) (hq := hq)] at hlowj0
      exact hlowj0
    rw [highBits, Vector.get_ofFn, highBits, Vector.get_ofFn]
    have hadd : (r + s).get j = r.get j + s.get j := by
      rw [Vector.get_eq_getElem, Vector.getElem_add]
      simp [Vector.get_eq_getElem]
    rw [hadd]
    exact congrArg (fun n : ℕ => (n : Coeff))
      (highBitsCoeff_add_eq_of_small_of_isApproved p hp (r := r.get j)
        (s := s.get j) (b := b) hsj hlowj)
  apply Vector.ext
  intro i hi
  exact hfin ⟨i, hi⟩

theorem concreteRounding_useHint_bound_field_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) (h : Hint) :
    LatticeCrypto.cInfNorm
      (r - (concreteRoundingOps p).shift ((concreteRoundingOps p).useHint h r)) ≤
        2 * p.gamma2 + 1 := by
  change LatticeCrypto.cInfNorm (r - highBitsShift p (useHint p h r)) ≤ 2 * p.gamma2 + 1
  exact concreteRounding_useHint_bound_of_isApproved p hp r h

theorem concreteRounding_useHint_correct_field_of_isApproved (p : Params)
    (hp : p.isApproved) (z r : Rq) :
    LatticeCrypto.cInfNorm z ≤ (2 * p.gamma2) / 2 →
    (concreteRoundingOps p).useHint ((concreteRoundingOps p).makeHint z r) r =
      (concreteRoundingOps p).highBits (r + z) := by
  intro hz
  have hhalf : (2 * p.gamma2) / 2 = p.gamma2 := by
    omega
  change useHint p (makeHint p z r) r = highBits p (r + z)
  exact concreteRounding_useHint_correct_of_isApproved p hp z r (by simpa [hhalf] using hz)

theorem concreteRounding_hide_low_field_of_isApproved (p : Params)
    (hp : p.isApproved) (r s : Rq) (b : ℕ) :
    LatticeCrypto.cInfNorm s ≤ b →
    LatticeCrypto.cInfNorm ((concreteRoundingOps p).lowBits r) + b < (2 * p.gamma2) / 2 →
    (concreteRoundingOps p).highBits (r + s) = (concreteRoundingOps p).highBits r := by
  intro hs hlow
  have hhalf : (2 * p.gamma2) / 2 = p.gamma2 := by
    omega
  change highBits p (r + s) = highBits p r
  exact concreteRounding_hide_low_of_isApproved p hp r s b hs (by simpa [hhalf] using hlow)

theorem concretePower2RoundLaws :
    @LatticeCrypto.Power2RoundOps.Laws Rq instRqAddCommGroup droppedBits
      concretePower2RoundOps LatticeCrypto.cInfNorm := by
  exact ⟨concretePower2Round_bound_field⟩

theorem concreteRoundingLaws_of_isApproved (p : Params) (hp : p.isApproved) :
    @LatticeCrypto.RoundingOps.Laws Rq instRqAddCommGroup (2 * p.gamma2)
      (concreteRoundingOps p) LatticeCrypto.cInfNorm := by
  refine
    { high_low_decomp := concreteRounding_high_low_decomp_field_of_isApproved p hp
      lowBits_bound := concreteRounding_lowBits_bound_field_of_isApproved p hp
      hide_low := concreteRounding_hide_low_field_of_isApproved p hp
      shift_injective := concreteRounding_shift_injective_field_of_isApproved p hp
      useHint_correct := concreteRounding_useHint_correct_field_of_isApproved p hp
      useHint_bound := concreteRounding_useHint_bound_field_of_isApproved p hp }

/-
The concrete `Power2Round` and approved-parameter `RoundingOps` wrappers now compile.
-/

end MLDSA.Concrete
