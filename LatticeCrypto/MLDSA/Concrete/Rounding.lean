/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Arithmetic
import LatticeCrypto.Ring.Norms
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

@[simp] theorem Rq.get_zero (i : Fin ringDegree) : (0 : Rq).get i = 0 :=
  NegacyclicRing.coeff_zero coeffRing i

@[simp] theorem Rq.get_add (a b : Rq) (i : Fin ringDegree) :
    (a + b).get i = a.get i + b.get i :=
  NegacyclicRing.coeff_add coeffRing a b i

@[simp] theorem Rq.get_neg (a : Rq) (i : Fin ringDegree) :
    (-a).get i = -a.get i :=
  NegacyclicRing.coeff_neg coeffRing a i

@[simp] theorem Rq.get_sub (a b : Rq) (i : Fin ringDegree) :
    (a - b).get i = a.get i - b.get i :=
  NegacyclicRing.coeff_sub coeffRing a b i

@[simp] theorem coeffRing_sub_eq (r s : Rq) : coeffRing.sub r s = r - s := by
  ext i; simp only [NegacyclicRing.coeff_sub, coeffRing.sub_coeff]

@[simp] theorem coeffRing_add_eq (r s : Rq) : coeffRing.add r s = r + s := by
  ext i; simp only [NegacyclicRing.coeff_add, coeffRing.add_coeff]

private structure BalancedDecomp (alpha m : ℕ) : Prop where
  hα   : 0 < alpha
  hm   : 0 < m
  hqm1 : alpha * m = modulus - 1
  hq   : alpha < modulus
  hdvd : alpha ∣ modulus - 1
  hsmall : 2 * (alpha + 1) < modulus

private def BalancedDecomp.ofApproved {p : Params} (hp : p.isApproved) :
    BalancedDecomp (2 * p.gamma2) ((modulus - 1) / (2 * p.gamma2)) where
  hα     := by rcases hp with rfl | rfl | rfl <;> decide
  hm     := by rcases hp with rfl | rfl | rfl <;> decide
  hqm1   := Nat.mul_div_cancel' (by rcases hp with rfl | rfl | rfl <;> decide)
  hq     := by rcases hp with rfl | rfl | rfl <;> decide
  hdvd   := by rcases hp with rfl | rfl | rfl <;> decide
  hsmall := by rcases hp with rfl | rfl | rfl <;> decide

private theorem power2RoundCoeff_eq (r : Coeff) :
    let (r1, r0) := power2RoundCoeff r
    ((power2Scale : Coeff) * (r1 : Coeff)) + r0 = r := by
  unfold power2RoundCoeff
  set t : ℕ := r.val % power2Scale
  have hdiv : t + power2Scale * (r.val / power2Scale) = r.val := by
    subst t
    exact Nat.mod_add_div _ _
  have hdiv' : ((t + power2Scale * (r.val / power2Scale) : ℕ) : Coeff) = r := by
    simpa [ZMod.natCast_zmod_val] using congrArg (fun n : ℕ => (n : Coeff)) hdiv
  by_cases h : t ≤ power2Scale / 2
  · simp only [h, ↓reduceDIte, Int.cast_natCast]
    rw [← Nat.cast_mul, ← Nat.cast_add]
    simp [Nat.add_comm, hdiv']
  · simp only [h, ↓reduceDIte, Nat.cast_add, Nat.cast_one, Int.cast_sub, Int.cast_natCast]
    ring_nf
    rw [← Nat.cast_mul, ← Nat.cast_add]
    simp [Nat.add_comm, hdiv']

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
    centeredRepr (intToCoeff z) = z :=
  centeredRepr_intCast_eq_of_natAbs_le z hbound hbq

private theorem power2RoundLow_centeredRepr (r : Coeff) :
    centeredRepr (intToCoeff ((power2RoundCoeff r).2)) = (power2RoundCoeff r).2 := by
  apply centeredRepr_eq_of_natAbs_le
  · exact power2RoundCoeff_bound r
  · norm_num [power2Scale, droppedBits, modulus]

private theorem decomposeCoeff_eq (r : Coeff) {r1 gamma2 : ℕ} {r0 : ℤ}
    (hdecomp : (r1, r0) = decomposeCoeff r gamma2) :
    (((2 * gamma2 : ℕ) : Coeff) * (r1 : Coeff)) + r0 = r := by
  simp only [decomposeCoeff] at hdecomp
  set alpha : ℕ := 2 * gamma2
  set t : ℕ := r.val % alpha
  set q := r.val / alpha
  have hbase : ((alpha : ℕ) : Coeff) * (q : Coeff) + (t : Coeff) = r := by
    have : alpha * q + t = r.val := by rw [Nat.div_add_mod]
    apply congrArg (↑· : ℕ → Coeff) at this
    rw [ZMod.natCast_zmod_val r ] at this
    push_cast at this
    exact this
  have hwrap : ∀ (k : ℕ), alpha * k = modulus - 1 →
      ((alpha : ℕ) : Coeff) * (k : Coeff) = -1 := fun k hk => by
    rw [← Nat.cast_mul, hk, Nat.cast_sub (by norm_num [modulus]),
      ZMod.natCast_self, zero_sub, Nat.cast_one]
  split_ifs at hdecomp with h hs hs <;>
    simp only [Prod.mk.injEq] at hdecomp <;>
    obtain ⟨rfl, rfl⟩ := hdecomp
  · rw [hwrap q hs] at hbase
    simp only [Nat.cast_zero, mul_zero, Int.cast_sub, Int.cast_natCast, Int.cast_one, zero_add]
    exact hbase
  · exact hbase
  · have h1 : (alpha:Coeff) * (q:Coeff) = (alpha:Coeff) * (((q + 1):ℕ):Coeff) - alpha := by
      simp [mul_add]
    rw [← hbase, h1, hwrap (q+1) hs]
    simp [mul_zero]
    ring
  · simp [← hbase, mul_add]

private theorem lowBitsCoeff_bound (r : Coeff) {gamma2 : ℕ} (hγ : 0 < gamma2) :
    (lowBitsCoeff r gamma2).natAbs ≤ gamma2 := by
  simp only [lowBitsCoeff, decomposeCoeff]
  set alpha : ℕ := 2 * gamma2
  set t : ℕ := r.val % alpha
  have htlt : t < alpha := Nat.mod_lt _ (by omega)
  split_ifs with h hs hs <;> omega

private theorem lowBits_centeredRepr (r : Coeff) {gamma2 : ℕ}
    (hγ : 0 < gamma2) (hq : 2 * gamma2 < modulus) :
    centeredRepr (intToCoeff (lowBitsCoeff r gamma2)) = lowBitsCoeff r gamma2 := by
  apply centeredRepr_eq_of_natAbs_le
  · exact lowBitsCoeff_bound r hγ
  · linarith

private theorem power2RoundShift_high_get (r : Rq) (i : Fin ringDegree) :
    (power2RoundShift (power2RoundHigh r)).get i =
      (power2Scale : Coeff) * ((power2RoundCoeff (r.get i)).1 : Coeff) := by
  simp [power2RoundShift, power2RoundHigh]

private theorem power2RoundLow_get (r : Rq) (i : Fin ringDegree) :
    (power2RoundLow r).get i = intToCoeff ((power2RoundCoeff (r.get i)).2) := by
  simp [power2RoundLow]

theorem concretePower2Round_high_low_decomp (r : Rq) :
    power2RoundShift (power2RoundHigh r) + power2RoundLow r = r :=
  Poly.ext_get_eq fun j => by
    rw [Rq.get_add, power2RoundShift_high_get, power2RoundLow_get]
    exact power2RoundCoeff_eq (r.get j)

theorem concretePower2Round_remainder_eq_low (r : Rq) :
    r - power2RoundShift (power2RoundHigh r) = power2RoundLow r :=
  Poly.ext_get_eq fun j => by
    rw [Rq.get_sub, power2RoundShift_high_get, power2RoundLow_get]
    exact sub_eq_iff_eq_add'.2 (power2RoundCoeff_eq (r.get j)).symm

theorem concretePower2Round_bound (r : Rq) :
    ‖r - power2RoundShift (power2RoundHigh r)‖∞ ≤ 2 ^ (droppedBits - 1) := by
  rw [concretePower2Round_remainder_eq_low]
  refine cInfNorm_le_of_coeff_le ?_
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

theorem concreteRounding_high_low_decomp (p : Params) (r : Rq) :
    highBitsShift p (highBits p r) + lowBits p r = r :=
  Poly.ext_get_eq fun j => by
    rw [Rq.get_add, highBitsShift_high_get, lowBits_get]
    exact decomposeCoeff_eq (r.get j) (Prod.eta _)

theorem concreteRounding_lowBits_bound (p : Params)
    (hγ : 0 < p.gamma2) (hq : 2 * p.gamma2 < modulus) (r : Rq) :
    ‖lowBits p r‖∞ ≤ p.gamma2 := by
  refine cInfNorm_le_of_coeff_le ?_
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

private theorem gamma2_half (p : Params) : (2 * p.gamma2) / 2 = p.gamma2 := by omega

private theorem highBitsCoeff_lt_useHintModulus_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Coeff) :
    highBitsCoeff r p.gamma2 < (modulus - 1) / (2 * p.gamma2) := by
  let ctx := BalancedDecomp.ofApproved hp
  unfold highBitsCoeff decomposeCoeff
  set alpha : ℕ := 2 * p.gamma2
  set m : ℕ := (modulus - 1) / alpha
  set t : ℕ := r.val % alpha
  by_cases h : t ≤ alpha / 2
  · by_cases hs : alpha * (r.val / alpha) = modulus - 1
    · simp [h, t, hs, ctx.hm]
    · have hlt : r.val / alpha < m := by
        have hle : r.val ≤ alpha * m := by
          have := ZMod.val_lt r; rw [ctx.hqm1]; omega
        have hdiv_le : r.val / alpha ≤ m := by
          rw [← Nat.mul_div_cancel_left m ctx.hα]
          exact Nat.div_le_div_right hle
        exact lt_of_le_of_ne hdiv_le fun h => hs (by rw [h]; exact ctx.hqm1)
      simp [h, t, hs, hlt]
  · by_cases hs : alpha * (r.val / alpha + 1) = modulus - 1
    · simp [h, t, hs, ctx.hm]
    · have hqdiv_lt : r.val / alpha < m := by
        by_contra hge
        have hmle : alpha * m ≤ alpha * (r.val / alpha) :=
          Nat.mul_le_mul_left alpha (Nat.not_lt.mp hge)
        have hdadd : alpha * (r.val / alpha) + t = r.val := Nat.div_add_mod r.val alpha
        have htpos : 0 < t := by have := Nat.lt_of_not_le h; omega
        have hmod : alpha * m + 1 = modulus := by rw[ctx.hqm1]; norm_cast
        linarith [ZMod.val_lt r]
      have hlt : r.val / alpha + 1 < m :=
        lt_of_le_of_ne (Nat.succ_le_of_lt hqdiv_lt)
          (fun heq => hs (by rw [heq]; exact ctx.hqm1))
      simp [h, t, hs, hlt]

private theorem alphaMul_pred_m_eq_coeff {alpha m : ℕ} (ctx : BalancedDecomp alpha m) :
    ((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff) = (-1 : Coeff) - ((alpha : ℕ) : Coeff) := by
  have hmulm: (((alpha : ℕ) : Coeff) * (m : Coeff)) = (-1 : Coeff) := by
    rw [← Nat.cast_mul, ctx.hqm1,
      Nat.cast_sub (show 1 ≤ modulus by norm_num [modulus]),
      ZMod.natCast_self, zero_sub]
    push_cast; rfl
  have hcast : ((m - 1 : ℕ) : Coeff) = (m : Coeff) - 1 := by
    push_cast [show 1 ≤ m from ctx.hm]; rfl
  rw [hcast, mul_sub, mul_one, hmulm]

private theorem highBitsCoeff_of_nonneg_val {r : Coeff} {gamma2 r1 t : ℕ}
    (hα : 0 < 2 * gamma2)
    (hval : r.val = 2 * gamma2 * r1 + t)
    (ht : t ≤ gamma2)
    (hwrap : 2 * gamma2 * r1 ≠ modulus - 1) :
    highBitsCoeff r gamma2 = r1 := by
  simp only [highBitsCoeff, decomposeCoeff]
  have hmod : r.val % (2 * gamma2) = t := by
    rw [hval, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : r.val / (2 * gamma2) = r1 := by
    rw [hval, Nat.add_comm, Nat.add_mul_div_left _ _ hα, Nat.div_eq_of_lt (by omega), zero_add]
  rw [hmod, hdiv]
  simp [mul_div_cancel_left₀, ht, hwrap]

private theorem highBitsCoeff_of_neg_val {r : Coeff} {gamma2 r1 t : ℕ}
    (hα : 0 < 2 * gamma2)
    (hval : r.val = 2 * gamma2 * (r1 - 1) + t)
    (htγ : gamma2 < t)
    (ht_lt : t < 2 * gamma2)
    (hr1 : 0 < r1)
    (hwrap : 2 * gamma2 * r1 ≠ modulus - 1) :
    highBitsCoeff r gamma2 = r1 := by
  simp only [highBitsCoeff, decomposeCoeff]
  have hmod : r.val % (2 * gamma2) = t := by
    rw [hval, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht_lt]
  have hdiv : r.val / (2 * gamma2) = r1 - 1 := by
    rw [hval, Nat.add_comm, Nat.add_mul_div_left _ _ hα, Nat.div_eq_of_lt ht_lt, zero_add]
  have hnowrap : 2 * gamma2 * (r1 - 1 + 1) ≠ modulus - 1 := by rwa [Nat.sub_add_cancel hr1]
  rw [hmod, hdiv, if_neg hnowrap, Nat.sub_add_cancel hr1]
  simp [htγ.not_ge]

private theorem highBitsCoeff_of_repr (p : Params) (hp : p.isApproved)
    {r : Coeff} (r1 : ℕ) (r0 : ℤ)
    (hr1 : r1 < (modulus - 1) / (2 * p.gamma2))
    (hr0 : r0.natAbs ≤ p.gamma2)
    (hr0_neg : r0 < 0 → r1 = 0 ∨ r0.natAbs < p.gamma2)
    (hdecomp : ((2 * p.gamma2 : ℕ) : Coeff) * (r1 : Coeff) + r0 = r) :
    highBitsCoeff r p.gamma2 = r1 := by
  let ctx := BalancedDecomp.ofApproved hp
  let alpha : ℕ := 2 * p.gamma2
  let n := r0.natAbs
  let m : ℕ := (modulus - 1) / alpha
  have hqm1 : alpha * m = modulus - 1 := ctx.hqm1
  have hr1m : r1 < m := hr1
  have hn_lt : n < alpha := by
    change r0.natAbs < 2 * p.gamma2
    have hγ : 0 < p.gamma2 := gamma2_pos_of_isApproved hp
    linarith [hr0]
  have hmul : alpha * (m - 1) + alpha = alpha * m := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel]
    exact Nat.le_mul_of_pos_right alpha ctx.hm
  have hltq : alpha * r1 + n < modulus := by
    have hle : alpha * r1 + n ≤ alpha * (m - 1) + p.gamma2 :=
      Nat.add_le_add (Nat.mul_le_mul_left alpha (by omega)) hr0
    have htop : alpha * (m - 1) + p.gamma2 < modulus := by
      rw[Nat.mul_sub_one, ctx.hqm1]
      omega
    linarith
  by_cases hr0nn: 0 ≤ r0
  · have hval : r.val = alpha * r1 + r0.natAbs := by
      have hrcast : r = ((alpha * r1 + n : ℕ) : Coeff) := by
        rw [← hdecomp]
        simp [alpha, n]
        congr 1
        simp [abs_eq_self.mpr hr0nn]
      rw [hrcast, ZMod.val_natCast_of_lt hltq]
    exact highBitsCoeff_of_nonneg_val ctx.hα hval hr0
      (ne_of_lt (by rw [← ctx.hqm1]; exact Nat.mul_lt_mul_of_pos_left hr1 ctx.hα))
  · by_cases hr1z : r1 = 0
    · push Not at hr0nn
      have hn0 : 0 < n := Int.natAbs_pos.mpr (by omega)
      have hrn : r =  (-(n : ℤ)) := by
        simp [hr1z, ← hdecomp, n, abs_eq_neg_self.mpr (Int.le_of_lt hr0nn)]
      have hnltq : n < modulus := lt_of_le_of_lt hr0
          (by linarith [gamma2_double_lt_modulus_of_isApproved hp])
      have hneq : ((n : ℕ) : Coeff) ≠ 0 := by
        intro h
        exact absurd (Nat.le_of_dvd hn0 ((ZMod.natCast_eq_zero_iff n modulus).mp h)) (by omega)
      have hval : r.val = modulus - n := by
        haveI : NeZero ((n : ℕ) : Coeff) := ⟨hneq⟩
        simp [hrn, ZMod.val_neg_of_ne_zero ((n : ℕ) : Coeff),
            ZMod.val_natCast_of_lt hnltq]
      by_cases hn1 : n = 1
      · simp_rw [hn1] at *
        have hmod : r.val % alpha = 0 := by
          rw [hval, show modulus - 1 = alpha * m by omega, Nat.mul_mod_right]
        have hdiv : r.val / alpha = m := by
          rw [hval, show modulus - 1 = alpha * m by omega, Nat.mul_div_cancel_left _ ctx.hα]
        have hcond1 : r.val % alpha ≤ alpha / 2 := by rw [hmod]; omega
        have hcond2 : alpha * (r.val / alpha) = modulus - 1 := by rw [hdiv]; omega
        simp [highBitsCoeff, decomposeCoeff, hr1z, hval]
        rw [hval] at hcond1 hcond2
        unfold alpha at hcond1 hcond2
        simp [mul_div_cancel_left₀] at hcond1
        simp [hcond1, hcond2]
      · have hn2 : 2 ≤ n := by omega
        have hrepr : modulus - n = (alpha + 1 - n) + (m - 1) * alpha := by
          zify [show n ≤ alpha + 1 by omega,
                show n ≤ modulus by linarith [ctx.hqm1],
                show alpha ≤ m * alpha from Nat.le_mul_of_pos_left alpha ctx.hm]
          have : (alpha : ℤ) * m = modulus - 1 := by omega
          linarith
        have hltα : alpha + 1 - n < alpha := by omega
        have hmod : r.val % alpha = alpha + 1 - n := by
          rw [hval, hrepr, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hltα]
        have hdiv : r.val / alpha = m - 1 := by
          rw [hval, hrepr, Nat.add_mul_div_right _ _ ctx.hα, Nat.div_eq_of_lt hltα, zero_add]
        have hcond1 : ¬(r.val % alpha ≤ alpha / 2) := by rw [hmod]; omega
        have hcond2 : alpha * (r.val / alpha + 1) = modulus - 1 := by
          rw [hdiv, show m - 1 + 1 = m by omega]; omega
        simp only [hval, alpha] at hcond1 hcond2
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀] at hcond1
        simp [highBitsCoeff, decomposeCoeff, hr1z, hval, hcond1, hcond2]
    · have hr0neg : r0 < 0 := lt_of_not_ge hr0nn
      have hr1pos : 0 < r1 := Nat.pos_of_ne_zero hr1z
      have hn_lt : r0.natAbs < p.gamma2 := by
        rcases hr0_neg hr0neg with h | h
        · exact absurd h hr1z
        · exact h
      have hr1qm1 : alpha * r1 < modulus - 1 := by
        rw[← ctx.hqm1]
        exact Nat.mul_lt_mul_of_pos_left hr1 ctx.hα
      have hn0   : 0 < n := Int.natAbs_pos.mpr (by omega)
      have hn_lt_alpha : n < alpha := by change r0.natAbs < 2 * p.gamma2; omega
      have hnle  : n ≤ alpha * r1 :=
        le_trans hn_lt_alpha.le (Nat.le_mul_of_pos_right alpha hr1pos)
      have hltq  : alpha * r1 - n < modulus :=
        lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
      have hval  : r.val = alpha * r1 - n := by
        have hrcast : r = ((alpha * r1 - n : ℕ) : Coeff) := by
          rw [← hdecomp]
          rw [show (r0 : Coeff) = -((n : ℕ) : Coeff) from by
            simp only [Nat.cast_natAbs, n]; rw [abs_eq_neg_self.mpr (Int.le_of_lt hr0neg)]; simp]
          push_cast [Nat.cast_sub hnle]
          simp [alpha]
          ring_nf
        rw [hrcast, ZMod.val_natCast_of_lt hltq]
      have hval_repr : r.val = alpha * (r1 - 1) + (alpha - n) := by
        have h1 : alpha ≤ alpha * r1 := Nat.le_mul_of_pos_right alpha hr1pos
        rw [mul_tsub, mul_one, hval]
        omega
      exact highBitsCoeff_of_neg_val ctx.hα hval_repr
        (by omega)
        (by omega)
        hr1pos
        (ne_of_lt (by rw [← ctx.hqm1]; exact Nat.mul_lt_mul_of_pos_left hr1 ctx.hα))

private theorem centeredRepr_alpha_mul_natAbs_ge
    {alpha m : ℕ} (ctx : BalancedDecomp alpha m)
    {delta : ℕ} (hd0 : 0 < delta) (hdm : delta < m) :
    alpha ≤ (centeredRepr ((alpha * delta : ℕ) : Coeff)).natAbs := by
  have hqm1 := ctx.hqm1
  have hq : modulus = alpha * m + 1 := by
    have := ctx.hsmall; omega
  have hlt : alpha * delta < modulus :=
    calc alpha * delta < alpha * m := Nat.mul_lt_mul_of_pos_left hdm ctx.hα
      _ = modulus - 1 := ctx.hqm1
      _ < modulus := Nat.sub_lt (by omega) one_pos
  have hval : ((alpha * delta : ℕ) : Coeff).val = alpha * delta := ZMod.val_natCast_of_lt hlt
  have hval' : (((alpha * delta : ℕ) : Coeff).val : ℤ) = (alpha * delta : ℕ) := by
    exact_mod_cast hval
  by_cases hle : (((alpha * delta : ℕ) : Coeff).val : ℤ) ≤ (modulus : ℤ) / 2
  · rw [centeredRepr_of_le hle, hval', Int.natAbs_natCast]
    nlinarith [ctx.hα]
  · push Not at hle
    rw [centeredRepr_of_gt hle, hval']
    have hnat : (((alpha * delta : ℕ) : ℤ) - modulus).natAbs = modulus - alpha * delta := by
      omega
    rw [hnat]
    have hdelt_le : alpha * delta ≤ alpha * (m - 1) := Nat.mul_le_mul_left alpha (by omega)
    have hmul : alpha * (m - 1) + alpha = alpha * m := by
      cases m with
      | zero => exact absurd ctx.hm (by omega)
      | succ k => ring_nf; simp only [add_tsub_cancel_left]
    omega

private theorem decomposeCoeff_unique (p : Params) (hp : p.isApproved)
    {r : Coeff} (r1 : ℕ) (r0 : ℤ)
    (hr1 : r1 < (modulus - 1) / (2 * p.gamma2))
    (hr0 : r0.natAbs ≤ p.gamma2)
    (hr0_neg : r0 < 0 → r1 = 0 ∨ r0.natAbs < p.gamma2)
    (hdecomp : ((2 * p.gamma2 : ℕ) : Coeff) * (r1 : Coeff) + r0 = r) :
    decomposeCoeff r p.gamma2 = (r1, r0) := by
  let ctx := BalancedDecomp.ofApproved hp
  have hγ := gamma2_pos_of_isApproved hp
  have h1 : highBitsCoeff r p.gamma2 = r1 :=
    highBitsCoeff_of_repr p hp r1 r0 hr1 hr0 hr0_neg hdecomp
  have hdecomp' : ((2 * p.gamma2 : ℕ) : Coeff) * (r1 : Coeff) +
      (lowBitsCoeff r p.gamma2) = r := by
    have h : ((2 * p.gamma2 : ℕ) : Coeff) * ((decomposeCoeff r p.gamma2).1 : Coeff) +
        (decomposeCoeff r p.gamma2).2 = r := decomposeCoeff_eq r (Prod.eta _)
    have h1' : (decomposeCoeff r p.gamma2).1 = r1 := h1
    rw [h1'] at h; exact h
  have hlow_eq : intToCoeff (lowBitsCoeff r p.gamma2) = intToCoeff r0 :=
    add_left_cancel (hdecomp'.trans hdecomp.symm)
  have h2 : lowBitsCoeff r p.gamma2 = r0 := by
    have cr_eq := congrArg centeredRepr hlow_eq
    rw [centeredRepr_eq_of_natAbs_le _ (lowBitsCoeff_bound r hγ) ctx.hq,
        centeredRepr_eq_of_natAbs_le _ hr0 ctx.hq] at cr_eq
    exact cr_eq
  exact Prod.ext h1 h2

private theorem highBitsCoeff_add_eq_of_small_of_isApproved (p : Params)
    (hp : p.isApproved) (r s : Coeff) {b : ℕ}
    (hs : (centeredRepr s).natAbs ≤ b)
    (hr : (lowBitsCoeff r p.gamma2).natAbs < p.gamma2 - b) :
    highBitsCoeff (r + s) p.gamma2 = highBitsCoeff r p.gamma2 := by
  let ctx := BalancedDecomp.ofApproved hp
  rcases hdecomp_r : decomposeCoeff r p.gamma2 with ⟨r1, r0⟩
  rcases hdecomp_rs : decomposeCoeff (r + s) p.gamma2 with ⟨u, w⟩
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  let z : ℤ := centeredRepr s
  let v : ℤ := r0 + z
  by_contra hneq; push Not at hneq
  have hdiffbound : (v - w).natAbs ≤ alpha - 1 := by
    have hwbound : w.natAbs ≤ p.gamma2 := by
      have h := lowBitsCoeff_bound (r := r + s) (gamma2_pos_of_isApproved hp)
      rwa [lowBitsCoeff, hdecomp_rs] at h
    have hvbound : v.natAbs ≤ p.gamma2 - 1 := by
      rw [lowBitsCoeff, hdecomp_r] at hr
      have h1 : r0.natAbs ≤ p.gamma2 - b - 1 := Nat.le_pred_of_lt hr
      have h2 := Int.natAbs_add_le r0 z
      omega
    exact (Int.natAbs_sub_le v w).trans
      (Nat.add_le_add hvbound hwbound |>.trans_eq (by omega))
  have heq :
      (((alpha : ℕ) : Coeff) * (u : Coeff)) + w =
        (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + v := by
    have hcandidate : (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + v = r + s := by
      rw[centeredRepr_intCast s]
      simp only [Int.cast_add, ← add_assoc, v]
      rw[decomposeCoeff_eq r hdecomp_r.symm]
    exact (decomposeCoeff_eq (r + s) hdecomp_rs.symm).trans hcandidate.symm
  have contra : ∀ (lo hi : ℕ) (e1 e2 : ℤ),
      lo < hi → hi < m →
      (e1 - e2).natAbs ≤ alpha - 1 →
      (((alpha : ℕ) : Coeff) * (lo : Coeff)) + e1 =
      (((alpha : ℕ) : Coeff) * (hi : Coeff)) + e2 →
      False := fun lo hi e1 e2 hlt hhi hbound heq' => by
    have hdelta0 : 0 < hi - lo := Nat.sub_pos_of_lt hlt
    have hdeltaeq : (((alpha : ℕ) : Coeff) * ((hi - lo : ℕ) : Coeff)) = intToCoeff (e1 - e2) := by
      rw [Nat.cast_sub (le_of_lt hlt), mul_sub]
      simp only [intToCoeff, Int.cast_sub] at ⊢ heq'
      apply sub_eq_sub_iff_add_eq_add.mpr
      ring_nf
      exact heq'.symm
    have hbig := centeredRepr_alpha_mul_natAbs_ge ctx hdelta0 (by simp [alpha, m] at hhi; omega)
    have hsmallq : 2 * (alpha - 1) < modulus := by
      have hbase : 2 * (alpha + 1) < modulus := ctx.hsmall; omega
    have hrepr := congrArg centeredRepr hdeltaeq
    rw [centeredRepr_eq_of_natAbs_le _ hbound hsmallq] at hrepr
    apply congrArg Int.natAbs at hrepr
    simp only [alpha, ← Nat.cast_mul] at hrepr
    omega
  have hlt_or_gt : r1 < u ∨ u < r1 := by
    simp only [highBitsCoeff, hdecomp_rs, hdecomp_r] at hneq
    exact lt_or_gt_of_ne hneq.symm
  cases hlt_or_gt with
  | inl hr1ltu =>
      have hult : u < m := by
        have := highBitsCoeff_lt_useHintModulus_of_isApproved p hp (r + s)
        rwa [highBitsCoeff, hdecomp_rs] at this
      exact contra r1 u v w hr1ltu hult hdiffbound heq.symm
  | inr hultr1 =>
      have hdiffbound2: (w - v).natAbs ≤ alpha - 1 := by
        rw [show w - v = -(v - w) from by ring, Int.natAbs_neg]
        exact hdiffbound
      have hr1lt : r1 < m := by
        have := highBitsCoeff_lt_useHintModulus_of_isApproved p hp r
        rwa [highBitsCoeff, hdecomp_r] at this
      exact contra u r1 w v hultr1 hr1lt hdiffbound2 heq

private theorem useHintCoeff_shift_sub_bound_of_isApproved (p : Params)
    (hp : p.isApproved) (h : Bool) (r : Coeff) :
    (centeredRepr
      (r - (((2 * p.gamma2 : ℕ) : Coeff) * (useHintCoeff h r p.gamma2 : Coeff)))).natAbs ≤
        2 * p.gamma2 + 1 := by
  let ctx := BalancedDecomp.ofApproved hp
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  rcases hdec : decomposeCoeff r p.gamma2 with ⟨r1, r0⟩
  have hdecomp : (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 = r :=
    decomposeCoeff_eq r hdec.symm
  have hr1lt : r1 < m := by
    have := highBitsCoeff_lt_useHintModulus_of_isApproved p hp r
    rwa [highBitsCoeff, hdec] at this
  have hr0bound : r0.natAbs ≤ p.gamma2 := by
    have := lowBitsCoeff_bound r (gamma2 := p.gamma2) (gamma2_pos_of_isApproved hp)
    rwa [lowBitsCoeff, hdec] at this
  cases h with
  | false =>
      have hcoeff :
          r - (((alpha : ℕ) : Coeff) * (useHintCoeff false r p.gamma2 : Coeff)) =
            intToCoeff r0 := by
        simp [useHintCoeff, hdec, sub_eq_iff_eq_add'.2 hdecomp.symm]
      have hbound : r0.natAbs ≤ alpha + 1 := by omega
      rw [hcoeff, centeredRepr_eq_of_natAbs_le (z := r0) hbound ctx.hsmall]
      exact hbound
  | true =>
      by_cases hr0pos : 0 < r0
      · by_cases hwrap : r1 + 1 < m
        · have hcoeff :
              r - (((alpha : ℕ) : Coeff) * (useHintCoeff true r p.gamma2 : Coeff)) =
                intToCoeff (r0 - alpha) := by
            simp only [useHintCoeff, ↓reduceIte, hdec, gt_iff_lt, hr0pos]
            rw [Nat.mod_eq_of_lt hwrap, ← hdecomp]
            simp [intToCoeff]
            ring
          have hbound : (r0 - alpha).natAbs ≤ alpha + 1 := by omega
          rw [hcoeff, centeredRepr_eq_of_natAbs_le (z := r0 - alpha) hbound ctx.hsmall]
          exact hbound
        · have hcoeff :
              r - (((alpha : ℕ) : Coeff) * (useHintCoeff true r p.gamma2 : Coeff)) =
                intToCoeff (r0 - alpha - 1) := by
            have heq : r1 + 1 = m := by omega
            have hr1eq : r1 = m - 1 := by omega
            have huse : useHintCoeff true r p.gamma2 = 0 := by
              simp [useHintCoeff, hdec, hr0pos, heq, m, alpha]
            have hmcoeff : (((alpha : ℕ) : Coeff) * (r1 : Coeff)) = (-1 : Coeff) - alpha := by
              rw[hr1eq]
              exact alphaMul_pred_m_eq_coeff ctx
            rw [huse]
            simp only [Nat.cast_zero, mul_zero, sub_zero, ← hdecomp, hmcoeff]
            rw[intToCoeff, intToCoeff, Int.cast_sub, Int.cast_sub]
            zify
            ring_nf
          have hbound : (r0 - alpha - 1).natAbs ≤ alpha + 1 := by
            dsimp [alpha]
            omega
          rw [hcoeff, centeredRepr_eq_of_natAbs_le (z := r0 - alpha - 1) hbound ctx.hsmall]
          exact hbound
      · by_cases hr1zero : r1 = 0
        · have hcoeff :
              r - (((alpha : ℕ) : Coeff) * (useHintCoeff true r p.gamma2 : Coeff)) =
                intToCoeff (r0 + alpha + 1) := by
            have huse : useHintCoeff true r p.gamma2 = m - 1 := by
              have hpred : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (Nat.pred_lt ctx.hm.ne')
              simp [useHintCoeff, hdec, alpha, m, hr0pos, hr1zero, hpred]
            have hmcoeff :
                (((alpha : ℕ) : Coeff) * ((m - 1 : ℕ) : Coeff)) = (-1 : Coeff) - alpha := by
              exact alphaMul_pred_m_eq_coeff ctx
            rw [huse, hmcoeff, ← hdecomp, hr1zero]
            simp [mul_zero, intToCoeff, Int.cast_add, sub_sub_eq_add_sub]
          have hbound : (r0 + alpha + 1).natAbs ≤ alpha + 1 := by omega
          rw [hcoeff, centeredRepr_eq_of_natAbs_le (z := r0 + alpha + 1) hbound ctx.hsmall]
          exact hbound
        · have huse : useHintCoeff true r p.gamma2 = r1 - 1 := by
            have hmod' : (r1 + m - 1) % m = r1 - 1 := by
              rw [show r1 + m - 1 = r1 - 1 + m by omega, Nat.add_mod_right,
                  Nat.mod_eq_of_lt (by omega)]
            simp [useHintCoeff, hdec, hr0pos, ← hmod', m, alpha]
          have hcoeff :
              r - ((alpha : ℕ) : Coeff) * (useHintCoeff true r p.gamma2 : Coeff) =
                intToCoeff (r0 + alpha) := by
            rw [huse, ← hdecomp, Nat.cast_sub (Nat.pos_of_ne_zero hr1zero)]
            simp [intToCoeff]
            ring_nf
          have hbound : (r0 + alpha).natAbs ≤ alpha + 1 := by omega
          rw [hcoeff, centeredRepr_eq_of_natAbs_le (z := r0 + alpha) hbound ctx.hsmall]
          exact hbound

private theorem decomposeCoeff_mid_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Coeff) (z0 r0 : ℤ) (r1 : ℕ)
    (hdec : (r1, r0) = decomposeCoeff r p.gamma2)
    (hvlow : -(p.gamma2 : ℤ) < r0 + z0)
    (hvup : r0 + z0 ≤ p.gamma2) :
    decomposeCoeff (r + intToCoeff z0) p.gamma2 =
      (highBitsCoeff r p.gamma2, lowBitsCoeff r p.gamma2 + z0) := by
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  let v : ℤ := r0 + z0
  have hr1lt : r1 < m := by
    have := highBitsCoeff_lt_useHintModulus_of_isApproved p hp r
    simp only [highBitsCoeff, ← hdec] at this
    exact this
  have hcore : (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff v = r + intToCoeff z0 := by
    have hd : (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + intToCoeff r0 = r := decomposeCoeff_eq r hdec
    simp only [v, intToCoeff, Int.cast_add, ← hd]; ring
  have hv_bound : v.natAbs ≤ p.gamma2 := natAbs_le_of_neg_le_and_le (le_of_lt hvlow) hvup
  have hv_neg_cond : v < 0 → r1 = 0 ∨ v.natAbs < p.gamma2 := fun hvneg =>
    Or.inr (by
      have h : (v.natAbs : ℤ) = -v := Int.ofNat_natAbs_of_nonpos hvneg.le
      exact_mod_cast h ▸ (show -v < (p.gamma2 : ℤ) by linarith))
  have huniq := decomposeCoeff_unique p hp r1 v hr1lt hv_bound hv_neg_cond hcore
  rw [huniq]
  simp [highBitsCoeff, lowBitsCoeff, v, ← hdec]

private theorem highBitsCoeff_of_pos_overflow (p : Params) (hp : p.isApproved)
    {s : Coeff} (r1 : ℕ) (v : ℤ)
    (hr1 : r1 < (modulus - 1) / (2 * p.gamma2))
    (hv_lo : (p.gamma2 : ℤ) < v)
    (hv_hi : v ≤ (2 * p.gamma2 : ℤ))
    (hsum : ((2 * p.gamma2 : ℕ) : Coeff) * (r1 : Coeff) + intToCoeff v = s) :
    highBitsCoeff s p.gamma2 = (r1 + 1) % ((modulus - 1) / (2 * p.gamma2)) := by
  let ctx := BalancedDecomp.ofApproved hp
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  by_cases hwrap : r1 + 1 < m
  · have hmod : (r1 + 1) % m = r1 + 1 := Nat.mod_eq_of_lt hwrap
    rw [hmod]
    refine highBitsCoeff_of_repr p hp (r1+1) (v - alpha) hwrap (by omega) (by omega) ?_
    · dsimp only [alpha]
      rw [← hsum]
      simp only [intToCoeff, Nat.cast_add, Nat.cast_one]
      push_cast; ring
  · have hmr1 : r1 < m := hr1
    push Not at hwrap
    have hwrap' : r1 + 1 = m := by omega
    have hmod : (r1 + 1) % m = 0 := by rw [hwrap', Nat.mod_self]
    rw [hmod]
    refine highBitsCoeff_of_repr p hp 0 (v - alpha - 1) ctx.hm (by omega) (by omega) ?_
    · have hmcoeff : ((alpha : ℕ) : Coeff) * (r1 : Coeff) =
            (-1 : Coeff) - ((alpha : ℕ) : Coeff) := by
        rw [show r1 = m - 1 from by omega]
        exact alphaMul_pred_m_eq_coeff ctx
      simp only [Nat.cast_zero, mul_zero, zero_add]
      rw [← hsum, hmcoeff]
      simp only [intToCoeff]; dsimp only [alpha]; push_cast; ring

private theorem highBitsCoeff_of_neg_overflow (p : Params) (hp : p.isApproved)
    {s : Coeff} (r1 : ℕ) (v : ℤ)
    (hr1 : r1 < (modulus - 1) / (2 * p.gamma2))
    (hv_lo : -(2 * p.gamma2 : ℤ) ≤ v)
    (hv_hi : v ≤ -(p.gamma2 : ℤ))
    (hbdry : v = -(p.gamma2 : ℤ) → 0 < r1)
    (hsum : ((2 * p.gamma2 : ℕ) : Coeff) * (r1 : Coeff) + v = s) :
    highBitsCoeff s p.gamma2 =
      (r1 + (modulus - 1) / (2 * p.gamma2) - 1) % ((modulus - 1) / (2 * p.gamma2)) := by
  let ctx := BalancedDecomp.ofApproved hp
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  rcases Nat.eq_zero_or_pos r1 with hr1z | hr1pos
  · have hvlt : v < -(p.gamma2 : ℤ) :=
      lt_of_le_of_ne hv_hi (fun h => absurd (hbdry h) (by omega))
    have hmod : (r1 + m - 1) % m = m - 1 := by
      subst hr1z; simp only [zero_add]
      exact Nat.mod_eq_of_lt (Nat.sub_lt ctx.hm (by norm_num))
    rw [hmod]
    refine highBitsCoeff_of_repr p hp
      (m - 1) (v + alpha + 1) (Nat.pred_lt ctx.hm.ne') (by omega) (by omega) ?_
    · rw [alphaMul_pred_m_eq_coeff ctx, ← hsum, hr1z]
      dsimp only [alpha]; push_cast; ring
  · have hmr1 : r1 < m := hr1
    have hmod : (r1 + m - 1) % m = r1 - 1 := by
      rw [show r1 + m - 1 = (r1 - 1) + m from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    refine highBitsCoeff_of_repr p hp (r1 - 1) (v + alpha) (by omega) (by omega) (by omega) ?_
    · rw[Nat.cast_sub hr1pos, ← hsum]; dsimp[alpha]; push_cast; ring

private theorem useHintCoeff_correct_of_small_of_isApproved (p : Params)
    (hp : p.isApproved) (z r : Coeff)
    (hz : (centeredRepr z).natAbs ≤ p.gamma2) :
    useHintCoeff (makeHintCoeff z r p.gamma2) r p.gamma2 =
      highBitsCoeff (r + z) p.gamma2 := by
  let ctx := BalancedDecomp.ofApproved hp
  let alpha : ℕ := 2 * p.gamma2
  let m : ℕ := (modulus - 1) / alpha
  rcases hdec : decomposeCoeff r p.gamma2 with ⟨r1, r0⟩
  let z0 : ℤ := centeredRepr z
  let v : ℤ := r0 + z0
  have hr1eq : highBitsCoeff r p.gamma2 = r1 := by simp [highBitsCoeff, hdec]
  have hr1lt : r1 < m := by
    have h := highBitsCoeff_lt_useHintModulus_of_isApproved p hp r
    rwa [highBitsCoeff, hdec] at h
  have hr0bound : r0.natAbs ≤ p.gamma2 := by
    have h := lowBitsCoeff_bound r (gamma2 := p.gamma2) (gamma2_pos_of_isApproved hp)
    rwa [lowBitsCoeff, hdec] at h
  have hzcast : z = intToCoeff z0 := centeredRepr_intCast z
  have hsum : ((alpha : ℕ) : Coeff) * (r1 : Coeff) + v = r + z := by
    have hdecomp :
      (((alpha : ℕ) : Coeff) * (r1 : Coeff)) + r0 = r :=
      decomposeCoeff_eq r hdec.symm
    simp only [Int.cast_add, hzcast, v]
    rw [← hdecomp, intToCoeff]; ring_nf
  by_cases heq : highBitsCoeff r p.gamma2 = highBitsCoeff (r + z) p.gamma2
  · simp [useHintCoeff, makeHintCoeff, heq, hdec, ← hr1eq]
  · push Not at heq; rename' heq => hneq
    have hhint : makeHintCoeff z r p.gamma2 = true := by simp [makeHintCoeff, hneq]
    have hvnotmid : ¬ (-(p.gamma2 : ℤ) < v ∧ v ≤ p.gamma2) := by
      by_contra ⟨hlo, hhi⟩
      have : highBitsCoeff (r + z) p.gamma2 = highBitsCoeff r p.gamma2 := by
        simp [highBitsCoeff,
          decomposeCoeff_mid_of_isApproved p hp r z0 r0 r1  hdec.symm hlo hhi, hzcast]
      exact absurd this.symm hneq
    rcases show (p.gamma2 : ℤ) < v ∨ v ≤ -(p.gamma2 : ℤ) by omega with hvpos | hvneg
    · have hr0pos : 0 < r0 := by omega
      have huse : useHintCoeff true r p.gamma2 = (r1 + 1) % m := by
        simp [useHintCoeff, hdec, hr0pos, m, alpha]
      have hgoal : highBitsCoeff (r + z) p.gamma2 = (r1 + 1) % m :=
        highBitsCoeff_of_pos_overflow p hp r1 v hr1lt hvpos (by omega) hsum
      rw [hhint, huse, hgoal]
    · have hr0nonpos : ¬ 0 < r0 := by omega
      have huse : useHintCoeff true r p.gamma2 = (r1 + m - 1) % m := by
        simp [useHintCoeff, hdec, hr0nonpos, m, alpha]
      have hbdry : v = -(p.gamma2 : ℤ) → 0 < r1 := fun hveq => by
        by_contra hr1z
        have hr1z' : r1 = 0 := by omega
        have hcoeff : (-(p.gamma2 : ℤ)) = r + z := by
          simpa [hr1z', hveq] using hsum
        have hzero : highBitsCoeff (r + z) p.gamma2 = 0 :=
          hcoeff ▸ highBitsCoeff_of_repr p hp 0 (-(p.gamma2 : ℤ)) ctx.hm
            (by simp) (by omega) (by simp)
        exact hneq (by simpa [hr1eq, hr1z'] using hzero.symm)
      have hgoal : highBitsCoeff (r + z) p.gamma2 = (r1 + m - 1) % m :=
        highBitsCoeff_of_neg_overflow p hp r1 v hr1lt (by omega) hvneg hbdry hsum
      rw [hhint, huse, hgoal]

theorem concreteRounding_high_low_decomp_of_isApproved (p : Params)
    (_hp : p.isApproved) (r : Rq) :
    highBitsShift p (highBits p r) + lowBits p r = r :=
  concreteRounding_high_low_decomp p r

theorem concreteRounding_lowBits_bound_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) :
    ‖lowBits p r‖∞ ≤ p.gamma2 :=
  concreteRounding_lowBits_bound p (gamma2_pos_of_isApproved hp)
    (gamma2_double_lt_modulus_of_isApproved hp) r

private theorem coeff_mul_left_injective_of_isUnit {c : Coeff} (hc : IsUnit c) :
    Function.Injective fun x : Coeff => c * x := by
  intro x y hxy
  rcases hc with ⟨u, rfl⟩
  have hxy' := congrArg (fun z : Coeff => ↑u⁻¹ * z) hxy
  simpa [mul_assoc] using hxy'

private theorem twoGamma_isUnit_of_isApproved {p : Params} (hp : p.isApproved) :
    IsUnit (((2 * p.gamma2 : ℕ) : Coeff)) := by
  have : Nat.Coprime (2 * p.gamma2) modulus := by rcases hp with rfl | rfl | rfl <;> decide
  exact (ZMod.isUnit_iff_coprime (2 * p.gamma2) modulus).mpr this

theorem highBitsShift_injective_of_isApproved (p : Params)
    (hp : p.isApproved) :
    Function.Injective (highBitsShift p) := by
  intro x y hxy
  refine Poly.ext_get_eq fun j => ?_
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
    ‖r - concretePower2RoundOps.shift2 (concretePower2RoundOps.power2Round r)‖∞ ≤
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

theorem concreteRounding_lowBits_bound_field_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) :
    ‖ (concreteRoundingOps p).lowBits r‖∞ ≤ (2 * p.gamma2) / 2 := by
  change ‖lowBits p r‖∞ ≤ (2 * p.gamma2) / 2
  simp only [gamma2_half]
  exact concreteRounding_lowBits_bound_of_isApproved p hp r

theorem concreteRounding_shift_injective_field_of_isApproved (p : Params)
    (hp : p.isApproved) :
    Function.Injective (concreteRoundingOps p).shift := by
  change Function.Injective (highBitsShift p)
  exact highBitsShift_injective_of_isApproved p hp

theorem concreteRounding_useHint_correct_of_isApproved (p : Params)
    (hp : p.isApproved) (z r : Rq) :
    ‖z‖∞ ≤ p.gamma2 →
    useHint p (makeHint p z r) r = highBits p (r + z) := by
  intro hz
  refine Poly.ext_get_eq fun j => ?_
  have hzj : (centeredRepr (z.get j)).natAbs ≤ p.gamma2 := cInfNorm_le_iff.mp hz j
  simp only [useHint, makeHint, highBits, Vector.get_ofFn, Rq.get_add]
  apply congrArg fun n : ℕ => (n : Coeff)
  exact useHintCoeff_correct_of_small_of_isApproved p hp (z := z.get j) (r := r.get j) hzj

theorem concreteRounding_useHint_bound_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) (h : Hint) :
    ‖r - highBitsShift p (useHint p h r)‖∞ ≤ 2 * p.gamma2 + 1 := by
  apply cInfNorm_le_iff.mpr
  intro j
  have hcoeff : (r - highBitsShift p (useHint p h r)).get j =
      r.get j -
        (((2 * p.gamma2 : ℕ) : Coeff) *
          (useHintCoeff (h.get j) (r.get j) p.gamma2 : Coeff)) := by
    simp only [Rq.get_sub, highBitsShift, Nat.cast_mul, Nat.cast_ofNat, useHint, Vector.map_ofFn,
      Vector.get_ofFn, Function.comp_apply]
  rw [hcoeff]
  exact useHintCoeff_shift_sub_bound_of_isApproved p hp (h.get j) (r.get j)

theorem concreteRounding_hide_low_of_isApproved (p : Params)
    (hp : p.isApproved) (r s : Rq) (b : ℕ) :
    ‖s‖∞ ≤ b →
    ‖lowBits p r‖∞ + b < p.gamma2 →
    highBits p (r + s) = highBits p r := by
  intro hs hlow
  refine Poly.ext_get_eq fun j => ?_
  simp only [highBits, Vector.get_ofFn, Rq.get_add]
  apply congrArg fun n : ℕ => (n : Coeff)
  apply highBitsCoeff_add_eq_of_small_of_isApproved p hp
  · exact cInfNorm_le_iff.mp hs j
  · have hcoeff := coeff_le_cInfNorm (lowBits p r) j
    rw [lowBits_get, lowBits_centeredRepr (r := r.get j)
      (hγ := gamma2_pos_of_isApproved hp)
      (hq := gamma2_double_lt_modulus_of_isApproved hp)] at hcoeff
    omega

theorem concreteRounding_useHint_bound_field_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) (h : Hint) :
    ‖r - (concreteRoundingOps p).shift ((concreteRoundingOps p).useHint h r)‖∞ ≤
        2 * p.gamma2 + 1 := by
  change ‖r - highBitsShift p (useHint p h r)‖∞ ≤ 2 * p.gamma2 + 1
  exact concreteRounding_useHint_bound_of_isApproved p hp r h

theorem concreteRounding_useHint_correct_field_of_isApproved (p : Params)
    (hp : p.isApproved) (z r : Rq) :
    ‖z‖∞ ≤ (2 * p.gamma2) / 2 →
    (concreteRoundingOps p).useHint ((concreteRoundingOps p).makeHint z r) r =
      (concreteRoundingOps p).highBits (r + z) := by
  intro hz
  change useHint p (makeHint p z r) r = highBits p (r + z)
  exact concreteRounding_useHint_correct_of_isApproved p hp z r (by simpa [gamma2_half] using hz)

theorem concreteRounding_hide_low_field_of_isApproved (p : Params)
    (hp : p.isApproved) (r s : Rq) (b : ℕ) :
    ‖s‖∞ ≤ b →
    ‖ (concreteRoundingOps p).lowBits r‖∞ + b < (2 * p.gamma2) / 2 →
    (concreteRoundingOps p).highBits (r + s) = (concreteRoundingOps p).highBits r := by
  intro hs hlow
  change highBits p (r + s) = highBits p r
  exact concreteRounding_hide_low_of_isApproved p hp r s b hs (by simpa [gamma2_half] using hlow)

theorem concretePower2RoundLaws :
    Power2RoundOps.Laws (ring := coeffRing) concretePower2RoundOps cInfNorm := by
  refine { power2Round_bound := ?_ }
  intro r
  change ‖coeffRing.sub _ _‖∞ ≤ _
  simp only [coeffRing_sub_eq]
  exact concretePower2Round_bound_field r

theorem concreteRoundingLaws_of_isApproved (p : Params) (hp : p.isApproved) :
    RoundingOps.Laws (ring := coeffRing) (concreteRoundingOps p) cInfNorm := by
  let cp := concreteRoundingOps p
  refine {
    high_low_decomp x := by
      change coeffRing.add (cp.shift (cp.highBits x)) (cp.lowBits x) = x
      simp only [coeffRing_add_eq]
      exact concreteRounding_high_low_decomp p x
    lowBits_bound := concreteRounding_lowBits_bound_field_of_isApproved p hp
    hide_low r s b h1 h2 := by
      change cp.highBits (coeffRing.add r s) = cp.highBits r
      change ‖lowBits p r‖∞ + b < 2 * p.gamma2 / 2 at h2
      simp only [coeffRing_add_eq, gamma2_half] at ⊢ h2
      exact concreteRounding_hide_low_of_isApproved p hp r s b h1 h2
    shift_injective := concreteRounding_shift_injective_field_of_isApproved p hp
    useHint_correct z r h := by
      change cp.useHint (cp.makeHint z r) r = cp.highBits (coeffRing.add r z)
      simp only [coeffRing_add_eq]
      exact concreteRounding_useHint_correct_field_of_isApproved p hp z r h
    useHint_bound r h := by
      change ‖coeffRing.sub _ _‖∞ ≤ _
      simp only [coeffRing_sub_eq]
      exact concreteRounding_useHint_bound_of_isApproved p hp r h
  }

end MLDSA.Concrete
