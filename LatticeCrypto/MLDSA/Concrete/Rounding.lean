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
  Vector.ofFn fun i => (power2RoundCoeff (r.get i)).2

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
  Vector.ofFn fun i => lowBitsCoeff (r.get i) p.gamma2

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

private structure BalancedDecomp (alpha m : ℕ) : Prop where
  hα   : 0 < alpha
  heven: Even alpha
  hqm1 : alpha * m = modulus - 1
  hsmall : 2 * (alpha + 1) < modulus

private def BalancedDecomp.ofApproved {p : Params} (hp : p.isApproved) :
    BalancedDecomp (2 * p.gamma2) ((modulus - 1) / (2 * p.gamma2)) where
  hα     := by rcases hp with rfl | rfl | rfl <;> decide
  heven  := by simp only [even_two, Even.mul_right]
  hqm1   := Nat.mul_div_cancel' (by rcases hp with rfl | rfl | rfl <;> decide)
  hsmall := by rcases hp with rfl | rfl | rfl <;> decide

namespace BalancedDecomp
variable {alpha m : ℕ}

@[simp] private lemma h2α {ctx : BalancedDecomp alpha m} : 2 * (alpha / 2) = alpha :=
  Nat.two_mul_div_two_of_even ctx.heven

@[simp] private lemma hγ {ctx : BalancedDecomp alpha m} : 0 < alpha / 2 := by
  have := ctx.hα; rw[← ctx.h2α] at this; omega

@[simp] private lemma hmdef {ctx : BalancedDecomp alpha m} : (modulus - 1) / alpha = m :=
  Nat.div_eq_of_eq_mul_right ctx.hα ctx.hqm1.symm

@[simp] private lemma hq {ctx : BalancedDecomp alpha m} : alpha < modulus := by
  have := ctx.hsmall; omega

@[simp] private lemma hm {ctx : BalancedDecomp alpha m} : 0 < m := by
  have h : 0 < modulus - 1 := by decide
  rw [← ctx.hqm1, mul_comm] at h
  exact Nat.pos_of_mul_pos_right h

private lemma hunit {ctx : BalancedDecomp alpha m} : IsUnit (alpha : Coeff) :=
  IsUnit.of_mul_eq_one (-(m : Coeff)) (by
    rw[mul_neg, ← Nat.cast_mul, ctx.hqm1, Nat.cast_sub (show 1 ≤ modulus by norm_num [modulus]),
      ZMod.natCast_self, zero_sub, neg_neg]; rfl)

end BalancedDecomp

private theorem natCast_div_add_mod (r : Coeff) (s : ℕ) :
    s * ((r.val / s):Coeff) + ((r.val % s): Coeff) = r := by
  rw [← Nat.cast_mul, ← Nat.cast_add]
  nth_rewrite 3 [← ZMod.natCast_zmod_val r]
  congr 1; exact Nat.div_add_mod r.val s

private theorem power2RoundCoeff_eq (r : Coeff) {r1 : ℕ} {r0 : ℤ}
  (hdecomp : power2RoundCoeff r = (r1, r0)) :
    ((power2Scale : Coeff) * (r1 : Coeff)) + r0 = r := by
  simp only [power2RoundCoeff] at hdecomp
  have hdam := natCast_div_add_mod r power2Scale
  split_ifs at hdecomp <;> rcases hdecomp with ⟨rfl, rfl⟩ <;> push_cast
  · exact hdam
  · ring_nf; exact hdam

private theorem power2RoundCoeff_bound (r : Coeff) :
    (power2RoundCoeff r).2.natAbs ≤ power2Scale / 2 := by
  simp only [power2RoundCoeff]
  split_ifs with h
  · simp only [h, Int.natAbs_natCast]
  · have htlt := Nat.mod_lt r.val (show 0 < power2Scale by decide)
    rw [Int.natAbs_natCast_sub_natCast_of_le htlt.le]
    omega

private theorem decomposeCoeff_eq
    {alpha r1 : ℕ} (r : Coeff) {r0 : ℤ}
    (h2α : 2 * (alpha / 2) = alpha)
    (hdecomp : decomposeCoeff r (alpha / 2) = (r1, r0)) :
    alpha * r1  + r0 = r := by
  simp only [decomposeCoeff, h2α] at hdecomp
  set t : ℕ := r.val % alpha
  set q := r.val / alpha
  have hdam : (alpha: Coeff) * q  + t = r := natCast_div_add_mod r alpha
  have hwrap : ∀ (k : ℕ), alpha * k = modulus - 1 → (alpha : Coeff) * k = -1 := fun k hk => by
    rw [← Nat.cast_mul, hk, Nat.cast_sub (by norm_num [modulus]),
      ZMod.natCast_self, zero_sub, Nat.cast_one]
  split_ifs at hdecomp with h hs hs <;>
    simp only [Prod.mk.injEq] at hdecomp <;>
    obtain ⟨rfl, rfl⟩ := hdecomp <;>
    push_cast <;> ring_nf
  · rw [← hwrap q hs]; exact hdam
  · exact hdam
  · rw [← hwrap (q+1) hs]; push_cast; ring_nf; exact hdam
  · exact hdam

private theorem lowBitsCoeff_bound (r : Coeff) {r1 gamma2 : ℕ} {r0 : ℤ} (hγ : 0 < gamma2)
    (hdec : decomposeCoeff r gamma2 = (r1, r0)) :
    r0.natAbs ≤ gamma2 := by
  simp only [decomposeCoeff] at hdec
  set alpha : ℕ := 2 * gamma2
  set t : ℕ := r.val % alpha
  have htlt : t < alpha := Nat.mod_lt _ (by omega)
  split_ifs at hdec with h hs hs <;> simp_all <;> omega

private theorem centeredRepr_intCast_lowBitsCoeff (r : Coeff) {gamma2 : ℕ}
    (hγ : 0 < gamma2) (hq : 2 * gamma2 < modulus) :
    centeredRepr ((lowBitsCoeff r gamma2):Coeff) = lowBitsCoeff r gamma2 := by
  have : (lowBitsCoeff r gamma2).natAbs ≤ gamma2 := by
    simp only [lowBitsCoeff]
    rcases hdec : decomposeCoeff r gamma2 with ⟨r1, r0⟩
    exact lowBitsCoeff_bound r hγ hdec
  exact centeredRepr_intCast_eq_of_natAbs_le
    (b:=gamma2) (lowBitsCoeff r gamma2) this hq

private theorem power2RoundShift_high_get (r : Rq) (i : Fin ringDegree) :
    (power2RoundShift (power2RoundHigh r)).get i =
      (power2Scale : Coeff) * ((power2RoundCoeff (r.get i)).1 : Coeff) := by
  simp [power2RoundShift, power2RoundHigh]

private theorem power2RoundLow_get (r : Rq) (i : Fin ringDegree) :
    (power2RoundLow r).get i = (power2RoundCoeff (r.get i)).2 := by
  simp [power2RoundLow]

theorem concretePower2Round_high_low_decomp (r : Rq) :
    power2RoundShift (power2RoundHigh r) + power2RoundLow r = r :=
  Poly.ext_get_eq fun j => by
    rw [Rq.get_add, power2RoundShift_high_get, power2RoundLow_get]
    exact power2RoundCoeff_eq (r.get j) rfl

theorem concretePower2Round_remainder_eq_low (r : Rq) :
    r - power2RoundShift (power2RoundHigh r) = power2RoundLow r :=
  sub_eq_iff_eq_add'.2 (concretePower2Round_high_low_decomp r).symm

theorem concretePower2Round_bound (r : Rq) :
    cInfNorm (r - power2RoundShift (power2RoundHigh r)) ≤ 2 ^ (droppedBits - 1) := by
  rw [concretePower2Round_remainder_eq_low]
  refine cInfNorm_le_of_coeff_le fun i => ?_
  simp only [power2RoundLow, Vector.get_ofFn]
  rw [centeredRepr_intCast_eq_of_natAbs_le
      (power2RoundCoeff (r.get i)).2
      (power2RoundCoeff_bound (r.get i))
      (by norm_num [power2Scale, droppedBits, modulus])]
  exact power2RoundCoeff_bound (r.get i)

private theorem highBitsShift_high_get (p : Params) (r : Rq) (i : Fin ringDegree) :
    (highBitsShift p (highBits p r)).get i =
      ((2 * p.gamma2 : ℕ) : Coeff) * (highBitsCoeff (r.get i) p.gamma2 : Coeff) := by
  simp [highBitsShift, highBits]

private theorem lowBits_get (p : Params) (r : Rq) (i : Fin ringDegree) :
    (lowBits p r).get i = lowBitsCoeff (r.get i) p.gamma2 := by
  simp [lowBits]

theorem concreteRounding_high_low_decomp (p : Params) (r : Rq) :
    highBitsShift p (highBits p r) + lowBits p r = r :=
  Poly.ext_get_eq fun j => by
    rw [Rq.get_add, highBitsShift_high_get, lowBits_get]
    have : 2 * p.gamma2 / 2 = p.gamma2 := by simp
    exact decomposeCoeff_eq (alpha := 2 * p.gamma2) (r.get j) (by omega)
      (by simp only [this]; exact Prod.eta _)

theorem concreteRounding_lowBits_bound (p : Params)
    (hγ : 0 < p.gamma2) (hq : 2 * p.gamma2 < modulus) (r : Rq) :
    cInfNorm (lowBits p r) ≤ p.gamma2 := by
  refine cInfNorm_le_of_coeff_le ?_
  intro i
  rw [lowBits_get]
  rw [centeredRepr_intCast_lowBitsCoeff (r := r.get i) hγ hq]
  simp only [lowBitsCoeff]
  rcases hdec : decomposeCoeff (r.get i) p.gamma2 with ⟨r1, r0⟩
  exact lowBitsCoeff_bound (r := r.get i) hγ hdec

private theorem gamma2_pos {p : Params} (hp : p.isApproved) :
    0 < p.gamma2 := by
  rcases hp with rfl | rfl | rfl <;> decide

private theorem two_gamma2_lt_modulus {p : Params} (hp : p.isApproved) :
    2 * p.gamma2 < modulus := by
  rcases hp with rfl | rfl | rfl <;> decide

private theorem highBitsCoeff_lt_m {alpha m : ℕ}
    (ctx : BalancedDecomp alpha m) (r : Coeff) :
    highBitsCoeff r (alpha / 2) < m := by
  simp only [highBitsCoeff, decomposeCoeff, ctx.h2α]
  set t : ℕ := r.val % alpha
  have hle : r.val ≤ alpha * m := by
    simp [ctx.hqm1, (Nat.le_sub_one_iff_lt (show 0 < modulus by decide)).mpr (ZMod.val_lt r)]
  split_ifs with h hs hs
  · exact ctx.hm
  · change r.val / alpha < m
    have hdiv_le : r.val / alpha ≤ m := by
      rw [← Nat.mul_div_cancel_left m ctx.hα]
      exact Nat.div_le_div_right hle
    exact lt_of_le_of_ne hdiv_le fun hm => hs (by rw [hm, ctx.hqm1])
  · exact ctx.hm
  · change r.val / alpha + 1 < m
    have hlt : ZMod.val r / alpha < m := by
      apply (Nat.mul_lt_mul_left ctx.hα).mp
      calc alpha * (r.val / alpha)
          < alpha * (r.val / alpha) + t := lt_add_of_pos_right _ (show 0 < t by omega)
        _ = r.val                       := Nat.div_add_mod r.val alpha
        _ ≤ alpha * m                   := hle
    have hdiv_le := Nat.add_one_le_of_lt hlt
    exact lt_of_le_of_ne hdiv_le fun hm => hs (by rw [hm, ctx.hqm1])

private theorem alpha_mul_pred_m_eq {alpha m : ℕ} (ctx : BalancedDecomp alpha m) :
    (alpha: Coeff) * ((m - 1 : ℕ) : Coeff) = (-1 : Coeff) - (alpha : Coeff) := by
  rw [Nat.cast_sub (show 1 ≤ m from ctx.hm), mul_sub, ← Nat.cast_mul,
    ctx.hqm1, Nat.cast_sub (show 1 ≤ modulus by decide), ZMod.natCast_self]
  ring_nf

private theorem highBitsCoeff_eq_of_repr {alpha m : ℕ} (ctx : BalancedDecomp alpha m)
    {r : Coeff} (r1 : ℕ) (r0 : ℤ)
    (hr1 : r1 < m)
    (hr0 : r0.natAbs ≤ alpha / 2)
    (hr0_neg : r0 < 0 → r1 = 0 ∨ r0.natAbs < alpha / 2)
    (hdecomp : (alpha : Coeff) * (r1 : Coeff) + r0 = r) :
    highBitsCoeff r (alpha / 2) = r1 := by
  set n := r0.natAbs
  have hn_lt : n < alpha := by have := ctx.hα; omega
  have hltq : alpha * r1 + n < modulus := by
    have hle : alpha * r1 + n ≤ alpha * (m - 1) + alpha/2 :=
      Nat.add_le_add (Nat.mul_le_mul_left alpha (by omega)) (by simp [hr0])
    have htop : alpha * (m - 1) + alpha/2 < modulus := by
      rw [Nat.mul_sub_one, ctx.hqm1]
      have hle : alpha ≤ modulus - 1 := ctx.hqm1 ▸ Nat.le_mul_of_pos_right alpha ctx.hm
      omega
    linarith
  suffices hRecoverPath : ∃ (q t : ℕ), r.val = alpha * q + t ∧ t < alpha ∧
      ((  t ≤ alpha / 2 ∧ ((alpha * q       = modulus - 1 ∧ r1 = 0) ∨ r1 = q )) ∨
      (   alpha / 2 < t ∧ ((alpha * (q + 1) = modulus - 1 ∧ r1 = 0) ∨ r1 = q + 1))) by
    obtain ⟨q, t, hrepr, ht, hside⟩ := hRecoverPath
    have hmod : r.val % alpha = t := by
      rw [hrepr, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
    have hdiv : r.val / alpha = q := by
      rw [hrepr, Nat.add_comm, Nat.add_mul_div_left _ _ ctx.hα, Nat.div_eq_of_lt ht, zero_add]
    simp only [highBitsCoeff, decomposeCoeff, ctx.h2α, hmod, hdiv]
    have hwrap : alpha * r1 ≠ modulus - 1 :=
      ne_of_lt (by rw [← ctx.hqm1]; exact Nat.mul_lt_mul_of_pos_left hr1 ctx.hα)
    rcases hside with ⟨hle, hcond2⟩ | ⟨hgt, hcond2⟩
    · rcases hcond2 with ⟨heq, hr1z⟩ | ⟨hr1q⟩
      · simp [hle, heq, hr1z]
      · simp [hle, ← hr1q, hwrap]
    · rcases hcond2 with ⟨heq, hr1z⟩ | ⟨hr1q⟩
      · simp [not_le.mpr hgt, heq, hr1z]
      · simp [not_le.mpr hgt, ← hr1q, hwrap]
  cases le_or_gt 0 r0 with
  | inl hr0nn =>
    refine ⟨r1, r0.natAbs, ?_, by omega, ?_⟩
    · have hrcast : r = ((alpha * r1 + n : ℕ) : Coeff) := by
        simp [← hdecomp, n]; congr 1; simp [abs_eq_self.mpr hr0nn]
      rw [hrcast, ZMod.val_natCast_of_lt hltq]
    · left; exact ⟨show n ≤ alpha/2 by omega, by right; rfl⟩
  | inr hr0neg =>
    cases Nat.eq_zero_or_pos r1 with
    | inl hr1z =>
      have hrn : r = -(n : ℤ) := by simp [hr1z, ← hdecomp, n, abs_eq_neg_self.mpr hr0neg.le]
      have hnltq : n < modulus := by simp only [hr1z, mul_zero, zero_add] at hltq; exact hltq
      have hneq : ((n : ℕ) : Coeff) ≠ 0 := by
        by_contra h; exact hnltq.not_ge
          (Nat.le_of_dvd (Int.natAbs_pos.mpr hr0neg.ne) ((ZMod.natCast_eq_zero_iff n modulus).mp h))
      have hval : r.val = modulus - n := by
        haveI : NeZero ((n : ℕ) : Coeff) := ⟨hneq⟩
        simp [hrn, ZMod.val_neg_of_ne_zero n, ZMod.val_natCast_of_lt hnltq]
      by_cases hn1 : n = 1
      · refine ⟨m, 0, ?_, ctx.hα, ?_⟩
        · simp [hn1, hval, ctx.hqm1]
        · left; exact ⟨by omega, by left; exact ⟨ctx.hqm1, hr1z⟩⟩
      · refine ⟨m - 1, alpha + 1 - n, ?_, by omega, ?_⟩
        · change r.val = alpha * (m - 1) + (alpha + 1 - n)
          rw [hval, Nat.mul_sub, mul_one, ctx.hqm1]
          zify [show n ≤ alpha + 1 by omega,
                ctx.hqm1 ▸ Nat.le_mul_of_pos_right alpha ctx.hm,
                show 1 ≤ modulus by omega, hnltq.le]
          ring
        · right; constructor
          · omega
          · rw [Nat.sub_add_cancel (by omega)]; left; exact ⟨ctx.hqm1, hr1z⟩
    | inr hr1pos =>
      refine ⟨r1 - 1, alpha - n, ?_, by omega, ?_⟩
      · change r.val = alpha * (r1 - 1) + (alpha - n)
        have hnle : n ≤ alpha * r1 :=
          le_trans hn_lt.le (Nat.le_mul_of_pos_right alpha hr1pos)
        have hval : r.val = alpha * r1 - n := by
          have hrcast : r = ((alpha * r1 - n : ℕ) : Coeff) := by
            zify [← hdecomp, Nat.cast_sub hnle,
              show (r0 : Coeff) = -((n : ℕ) : Coeff) by
                simp [Nat.cast_natAbs, n, abs_eq_neg_self.mpr (Int.le_of_lt hr0neg)]]
            ring_nf
          have hltq : alpha * r1 - n < modulus := lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
          rw [hrcast, ZMod.val_natCast_of_lt hltq]
        zify [hval, hn_lt, hnle,
          show 1 ≤ r1 from Nat.add_one_le_of_lt hr1pos,
          show alpha ≤ alpha * r1 from Nat.le_mul_of_pos_right alpha hr1pos]
        ring_nf
      · right; omega

private theorem alpha_le_natAbs_centeredRepr_mul
    {alpha m : ℕ} (ctx : BalancedDecomp alpha m)
    {z : ℤ} (hz0 : 0 < z) (hzm : z.toNat < m) :
    alpha ≤ (centeredRepr ((alpha : Coeff) * (z : Coeff))).natAbs := by
  have hznn : (0 : ℤ) ≤ z := le_of_lt hz0
  have hcoeff_eq : (alpha : Coeff) * (z : Coeff) = ((alpha * z.toNat : ℕ) : Coeff) := by
    have hz : (z : Coeff) = ((z.toNat : ℕ) : Coeff) := by
      rw [← Int.cast_natCast (R := Coeff), Int.toNat_of_nonneg hznn]
    rw [hz, ← Nat.cast_mul]
  rw [hcoeff_eq]
  have hlt : alpha * z.toNat < modulus :=
    calc alpha * z.toNat < alpha * m := Nat.mul_lt_mul_of_pos_left hzm ctx.hα
      _ = modulus - 1 := ctx.hqm1
      _ < modulus := Nat.sub_lt (by decide) one_pos
  by_cases hle : (((alpha * z.toNat : ℕ) : Coeff).val : ℤ) ≤ (modulus : ℤ) / 2
  · rw [centeredRepr_of_le hle, ZMod.val_natCast_of_lt hlt, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right alpha (by have := Int.toNat_of_nonneg hznn; omega)
  · push Not at hle
    have hq : modulus = alpha * m + 1 := by have := ctx.hsmall; have := ctx.hqm1; omega
    rw [centeredRepr_of_gt hle, ZMod.val_natCast_of_lt hlt,
      Int.natAbs_natCast_sub_natCast_of_le hlt.le, Nat.le_sub_iff_add_le hlt.le, hq]
    calc alpha + alpha * z.toNat
        = alpha * (z.toNat + 1) := by ring
      _ ≤ alpha * m             := Nat.mul_le_mul_left alpha (Nat.succ_le_of_lt hzm)
      _ ≤ alpha * m + 1         := Nat.le_succ _

private theorem decomposeCoeff_unique {alpha m : ℕ} (ctx : BalancedDecomp alpha m)
    {r : Coeff} (r1 : ℕ) (r0 : ℤ)
    (hr1 : r1 < m)
    (hr0 : r0.natAbs ≤ alpha / 2)
    (hr0_neg : r0 < 0 → r1 = 0 ∨ r0.natAbs < alpha / 2)
    (hdecomp : (alpha : Coeff) * (r1 : Coeff) + r0 = r) :
    decomposeCoeff r (alpha / 2) = (r1, r0) := by
  have h1 := highBitsCoeff_eq_of_repr ctx r1 r0 hr1 hr0 hr0_neg hdecomp
  have hdecomp' : (alpha : Coeff) * r1 + lowBitsCoeff r (alpha / 2) = r := by
    have h := decomposeCoeff_eq r ctx.h2α (Prod.eta _)
    simp only [highBitsCoeff, lowBitsCoeff, ← h1] at h ⊢; exact h
  have hlow_eq := add_left_cancel (hdecomp'.trans hdecomp.symm)
  have h2 : lowBitsCoeff r (alpha / 2) = r0 := by
    have cr_eq := congrArg centeredRepr hlow_eq
    have hγ2 := by have := ctx.hq; rwa [← ctx.h2α] at this
    rwa [centeredRepr_intCast_lowBitsCoeff r ctx.hγ hγ2,
        centeredRepr_intCast_eq_of_natAbs_le r0 hr0 hγ2] at cr_eq
  exact Prod.ext h1 h2

private theorem highBitsCoeff_add_eq_of_centeredRepr_lt
    {alpha m b : ℕ} (ctx : BalancedDecomp alpha m) (r s : Coeff)
    (hs : (centeredRepr s).natAbs ≤ b)
    (hr : (lowBitsCoeff r (alpha / 2)).natAbs < (alpha / 2) - b) :
    highBitsCoeff (r + s) (alpha / 2) = highBitsCoeff r (alpha / 2) := by
  rcases hdecomp_r : decomposeCoeff r (alpha / 2) with ⟨r1, r0⟩
  rcases hdecomp_rs : decomposeCoeff (r + s) (alpha / 2) with ⟨u, w⟩
  let z : ℤ := centeredRepr s
  let v : ℤ := r0 + z
  by_contra hneq; push Not at hneq
  have hdiffbound : (v - w).natAbs ≤ alpha - 1 := by
    have hwbound := lowBitsCoeff_bound (r := r + s) ctx.hγ hdecomp_rs
    have hvbound : v.natAbs ≤ alpha / 2 - 1 := by
      rw [lowBitsCoeff, hdecomp_r] at hr
      have h1 : r0.natAbs ≤ alpha / 2 - b - 1 := Nat.le_pred_of_lt hr
      have h2 := Int.natAbs_add_le r0 z
      omega
    have : alpha / 2 - 1 + alpha / 2 = alpha - 1 := by
      nth_rewrite 3 [← ctx.h2α]
      rw [two_mul, add_comm, Nat.add_sub_assoc]
      omega
    exact (Int.natAbs_sub_le v w).trans (Nat.add_le_add hvbound hwbound |>.trans_eq this)
  have heq : alpha * (u : Coeff) + w = alpha * (r1 : Coeff) + v := by
    have hcandidate : (alpha * (r1 : Coeff)) + v = r + s := by
      rw [centeredRepr_intCast s, Int.cast_add, ← add_assoc, decomposeCoeff_eq r ctx.h2α hdecomp_r]
    exact (decomposeCoeff_eq (r + s) ctx.h2α hdecomp_rs).trans hcandidate.symm
  have contra : ∀ (lo hi : ℕ) (e1 e2 : ℤ),
      lo < hi → hi < m →
      (e1 - e2).natAbs ≤ alpha - 1 →
      alpha * (lo : Coeff) + e1 = alpha * (hi : Coeff) + e2 →
      False := fun lo hi e1 e2 hlt hhi hbound heq' => by
    let delta := (hi : ℤ) - (lo : ℤ)
    have hbig := alpha_le_natAbs_centeredRepr_mul (z:= delta) ctx (by omega) (by omega)
    have hsmallq : 2 * (alpha - 1) < modulus := by have := ctx.hsmall; omega
    have hdeltaeq : alpha * (delta : Coeff) = e1 - e2 := by
      zify[delta, mul_sub]
      apply sub_eq_sub_iff_add_eq_add.mpr
      ring_nf
      exact heq'.symm
    rw [hdeltaeq, ← Int.cast_sub, centeredRepr_intCast_eq_of_natAbs_le _ hbound hsmallq] at hbig
    exact absurd (hbig.trans hbound) (Nat.not_le.mpr (Nat.sub_lt ctx.hα one_pos))
  have hlt_or_gt : r1 < u ∨ u < r1 := by
    simp only [highBitsCoeff, hdecomp_rs, hdecomp_r] at hneq
    exact lt_or_gt_of_ne hneq.symm
  cases hlt_or_gt with
  | inl hr1ltu =>
      have hult : u < m := by
        have := highBitsCoeff_lt_m ctx (r + s)
        rwa [highBitsCoeff, hdecomp_rs] at this
      exact contra r1 u v w hr1ltu hult hdiffbound heq.symm
  | inr hultr1 =>
      have hdiffbound2: (w - v).natAbs ≤ alpha - 1 := by
        rw [show w - v = -(v - w) from by ring, Int.natAbs_neg]
        exact hdiffbound
      have hr1lt : r1 < m := by
        have := highBitsCoeff_lt_m ctx r
        rwa [highBitsCoeff, hdecomp_r] at this
      exact contra u r1 w v hultr1 hr1lt hdiffbound2 heq

private theorem useHintCoeff_shift_sub_le
    {alpha m : ℕ} (ctx : BalancedDecomp alpha m) (hbit : Bool) (r : Coeff) :
    (centeredRepr
      (r - (alpha : Coeff) * (useHintCoeff hbit r (alpha / 2) : Coeff))).natAbs ≤
        alpha + 1 := by
  rcases hdec : decomposeCoeff r (alpha / 2) with ⟨r1, r0⟩
  have hdecomp : alpha * (r1 : Coeff) + r0 = r := decomposeCoeff_eq r ctx.h2α hdec
  have hr1lt : r1 < m := by
    have := highBitsCoeff_lt_m ctx r
    rwa [highBitsCoeff, hdec] at this
  have hr0bound := lowBitsCoeff_bound r ctx.hγ hdec
  suffices h : ∃ v : ℤ, r - (alpha : Coeff) * (useHintCoeff _ r (alpha / 2) : Coeff) = v
      ∧ v.natAbs ≤ alpha + 1 by
    obtain ⟨v, hveq, hvb⟩ := h
    rw [hveq, centeredRepr_intCast_eq_of_natAbs_le v hvb ctx.hsmall]; exact hvb
  cases hbit with
  | false =>
      use r0; exact ⟨by simp [useHintCoeff, hdec, sub_eq_iff_eq_add'.2 hdecomp.symm], by omega⟩
  | true =>
      by_cases hr0pos : 0 < r0
      · by_cases hwrap : r1 + 1 < m
        · use r0 - alpha; constructor
          · simp only [useHintCoeff, if_true, hdec, hr0pos, ctx.h2α, ctx.hmdef]
            rw [Nat.mod_eq_of_lt hwrap, ←hdecomp]
            push_cast
            ring_nf
          · omega
        · use r0 - alpha - 1; constructor
          · rw [show useHintCoeff true r (alpha / 2) = 0 by
                simp [useHintCoeff, hdec, hr0pos, ctx.h2α, ctx.hmdef, show r1 + 1 = m by omega]]
            zify [← hdecomp, show r1 = m - 1 by omega, alpha_mul_pred_m_eq ctx]
            ring_nf
          · omega
      · by_cases hr1zero : r1 = 0
        · use r0 + alpha + 1; constructor
          · have huse : useHintCoeff true r (alpha / 2) = m - 1 := by
              have hpred : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (Nat.pred_lt ctx.hm.ne')
              simp [useHintCoeff, hdec, hr0pos, hr1zero, ctx.h2α, ctx.hmdef, hpred]
            rw [huse, alpha_mul_pred_m_eq ctx, ← hdecomp, hr1zero]
            simp [sub_sub_eq_add_sub]
          · omega
        · use r0 + alpha; constructor
          · have huse : useHintCoeff true r (alpha / 2) = r1 - 1 := by
              have hmod' : (r1 + m - 1) % m = r1 - 1 := by
                rw [show r1 + m - 1 = r1 - 1 + m by omega, Nat.add_mod_right,
                    Nat.mod_eq_of_lt (by omega)]
              simp [useHintCoeff, hdec, hr0pos, ctx.h2α, ctx.hmdef, hmod']
            rw [huse, ← hdecomp, Nat.cast_sub (Nat.pos_of_ne_zero hr1zero),
              Nat.succ_eq_add_one, zero_add, Nat.cast_one, Int.cast_add, Int.cast_natCast]
            ring_nf
          · omega

private theorem decomposeCoeff_mid_of_isApproved
    {alpha m : ℕ} (ctx : BalancedDecomp alpha m) (r : Coeff) (z0 r0 : ℤ) (r1 : ℕ)
    (hdec : decomposeCoeff r (alpha / 2) = (r1, r0))
    (hvlow : -(alpha / 2 : ℤ) < r0 + z0)
    (hvup : r0 + z0 ≤ alpha / 2) :
    decomposeCoeff (r + z0) (alpha / 2) =
      (highBitsCoeff r (alpha / 2), lowBitsCoeff r (alpha / 2) + z0) := by
  set v : ℤ := r0 + z0
  have hr1lt : r1 < m := by
    have := highBitsCoeff_lt_m ctx r
    rwa [highBitsCoeff, hdec] at this
  have hcore : alpha * (r1 : Coeff) + v = r + z0 := by
    dsimp [v]; push_cast; rw [← add_assoc, decomposeCoeff_eq r ctx.h2α hdec]
  have hv_bound : v.natAbs ≤ alpha / 2 := natAbs_le_of_neg_le_and_le (le_of_lt hvlow) hvup
  have hv_neg_cond : v < 0 → r1 = 0 ∨ v.natAbs < alpha / 2 := fun hvneg =>
    Or.inr (by
      have h : (v.natAbs : ℤ) = -v := Int.ofNat_natAbs_of_nonpos hvneg.le
      exact_mod_cast h ▸ (show -v < alpha / 2 by omega))
  rw [decomposeCoeff_unique ctx r1 v hr1lt hv_bound hv_neg_cond hcore]
  simp [highBitsCoeff, lowBitsCoeff, v, hdec]

private theorem highBitsCoeff_eq_of_pos_overflow {alpha m : ℕ} (ctx : BalancedDecomp alpha m)
    {s : Coeff} (r1 : ℕ) (v : ℤ)
    (hr1 : r1 < m)
    (hv_lo : (alpha / 2 : ℤ) < v)
    (hv_hi : v ≤ (alpha : ℤ))
    (hsum : alpha * (r1 : Coeff) + v = s) :
    highBitsCoeff s (alpha/2) = (r1 + 1) % m := by
  have : v - (alpha :ℤ ) ≤ 0 := by omega
  have h2α := ctx.h2α
  by_cases hwrap : r1 + 1 < m
  · rw [Nat.mod_eq_of_lt hwrap]
    exact highBitsCoeff_eq_of_repr ctx (r1+1) (v - alpha) hwrap (by omega) (by omega)
      (by rw [← hsum, Nat.cast_add, Nat.cast_one]; push_cast; ring)
  · push Not at hwrap
    rw [show r1 + 1 = m  by omega, Nat.mod_self]
    exact highBitsCoeff_eq_of_repr ctx 0 (v - alpha - 1) ctx.hm (by omega) (by omega)
      (by
        rw [Nat.cast_zero, mul_zero, zero_add, ← hsum,
        show r1 = m - 1 from by omega, alpha_mul_pred_m_eq ctx]
        push_cast; ring)

private theorem highBitsCoeff_eq_of_neg_overflow {alpha m : ℕ} (ctx : BalancedDecomp alpha m)
    {s : Coeff} (r1 : ℕ) (v : ℤ)
    (hr1 : r1 < m)
    (hv_lo : -(alpha : ℤ) ≤ v)
    (hv_hi : v < -(alpha / 2 : ℤ) ∨ (v = -(alpha / 2 : ℤ) ∧ 0 < r1))
    (hsum : alpha * (r1 : Coeff) + v = s) :
    highBitsCoeff s (alpha / 2) = (r1 + m - 1) % m := by
  have h2α := ctx.h2α
  rcases Nat.eq_zero_or_pos r1 with hr1z | hr1pos
  · rw [hr1z, zero_add, Nat.mod_eq_of_lt (Nat.sub_lt ctx.hm (by decide))]
    exact highBitsCoeff_eq_of_repr ctx
      (m - 1) (v + alpha + 1) (Nat.pred_lt ctx.hm.ne') (by omega) (by omega)
      (by rw [alpha_mul_pred_m_eq ctx, ← hsum, hr1z]; push_cast; ring)
  · rw [show r1 + m - 1 = (r1 - 1) + m from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    exact highBitsCoeff_eq_of_repr ctx (r1 - 1) (v + alpha)
      (show r1 - 1 < m by omega) (by omega) (by omega)
      (by rw [Nat.cast_sub hr1pos, ← hsum]; push_cast; ring)

private theorem useHintCoeff_makeHintCoeff_eq_of_small
    {alpha m : ℕ} (ctx : BalancedDecomp alpha m) (z r : Coeff)
    (hz : (centeredRepr z).natAbs ≤ alpha / 2) :
    useHintCoeff (makeHintCoeff z r (alpha / 2)) r (alpha / 2) =
      highBitsCoeff (r + z) (alpha / 2) := by
  rcases hdec : decomposeCoeff r (alpha / 2) with ⟨r1, r0⟩
  set z0 : ℤ := centeredRepr z
  set v : ℤ := r0 + z0
  have hr1eq : highBitsCoeff r (alpha / 2) = r1 := by simp [highBitsCoeff, hdec]
  have hr1lt : r1 < m := by
    have h := highBitsCoeff_lt_m ctx r
    rwa [highBitsCoeff, hdec] at h
  have hr0bound := lowBitsCoeff_bound r ctx.hγ hdec
  have hzcast : z = z0 := centeredRepr_intCast z
  have hsum : alpha * (r1 : Coeff) + v = r + z := by
    dsimp [v]; rw [Int.cast_add, ← add_assoc, hzcast, decomposeCoeff_eq r ctx.h2α hdec]
  by_cases heq : highBitsCoeff r (alpha / 2) = highBitsCoeff (r + z) (alpha / 2)
  · simp [useHintCoeff, makeHintCoeff, heq, hdec, ← hr1eq]
  · push Not at heq; rename' heq => hneq
    rcases show
      (alpha / 2 : ℤ) < v ∨
      (-(alpha / 2 : ℤ) < v ∧ v ≤ alpha / 2) ∨
      v ≤ -(alpha / 2 : ℤ) by omega
    with hvpos | ⟨hlo, hhi⟩ | hvneg
    · have huse : useHintCoeff true r (alpha / 2) = (r1 + 1) % m := by
        simp [useHintCoeff, hdec, show 0 < r0 by omega, ctx.h2α, ctx.hmdef]
      simp only [makeHintCoeff, ne_eq, hneq, not_false_eq_true, decide_true, huse]
      exact (highBitsCoeff_eq_of_pos_overflow ctx r1 v hr1lt (by omega) (by omega) hsum).symm
    · have : highBitsCoeff (r + z) (alpha / 2) = highBitsCoeff r (alpha / 2) := by
        rw [highBitsCoeff, hzcast, decomposeCoeff_mid_of_isApproved ctx r z0 r0 r1 hdec hlo hhi]
      exact absurd this.symm hneq
    · have huse : useHintCoeff true r (alpha / 2) = (r1 + m - 1) % m := by
        simp [useHintCoeff, hdec, show ¬0 < r0 by omega, ctx.h2α, ctx.hmdef]
      have hv_hi : v < -(alpha / 2 : ℤ) ∨ (v = -(alpha / 2 : ℤ) ∧ 0 < r1) := by
        rcases lt_or_eq_of_le hvneg with h | hv
        · exact Or.inl h
        · exact Or.inr ⟨hv, by
            by_contra hr1z
            have hr1z' : r1 = 0 := by omega
            have hrz : r + z = (-(alpha / 2 : ℤ) : Coeff) := by simpa [hv, hr1z'] using hsum.symm
            have hrepr: highBitsCoeff (-(alpha / 2 : ℤ) : Coeff) (alpha / 2) = 0 :=
              highBitsCoeff_eq_of_repr ctx 0 (-(alpha / 2 : ℤ)) ctx.hm
                (by omega) (fun _ => Or.inl rfl) (by simp)
            exact hneq (by rw [hr1eq, hr1z', hrz, hrepr])⟩
      simp only [makeHintCoeff, ne_eq, hneq, not_false_eq_true, decide_true, huse]
      rw [highBitsCoeff_eq_of_neg_overflow ctx r1 v hr1lt (by omega) hv_hi hsum]

private theorem mul_left_injective_of_isUnit {c : Coeff} (hc : IsUnit c) :
    Function.Injective fun x : Coeff => c * x := by
  intro x y hxy
  rcases hc with ⟨u, rfl⟩
  have hxy' := congrArg (fun z : Coeff => ↑u⁻¹ * z) hxy
  simpa [mul_assoc] using hxy'

theorem highBitsShift_injective_of_isApproved (p : Params)
    (hp : p.isApproved) :
    Function.Injective (highBitsShift p) := by
  intro x y hxy
  refine Poly.ext_get_eq fun j => ?_
  have hcoeff : (2 * p.gamma2 : ℕ) * x.get j = (2 * p.gamma2 : ℕ) * y.get j := by
    simpa [highBitsShift] using congrArg (fun v : Rq => v.get j) hxy
  exact mul_left_injective_of_isUnit (BalancedDecomp.ofApproved hp).hunit hcoeff

/-- Concrete `Power2RoundOps` with `Power2High = Rq`. -/
def concretePower2RoundOps : MLDSA.Power2RoundOps where
  Power2High := Power2High
  power2Round := power2RoundHigh
  shift2 := power2RoundShift

/-- Concrete `RoundingOps` with `High = Rq` and Boolean hints. -/
def concreteRoundingOps (p : Params) : MLDSA.RoundingOps (2 * p.gamma2) where
  High := High
  Hint := Hint
  lowBits := lowBits p
  highBits := highBits p
  shift := highBitsShift p
  makeHint := makeHint p
  useHint := useHint p

theorem concreteRounding_useHint_correct_of_isApproved (p : Params)
    (hp : p.isApproved) (z r : Rq) :
    cInfNorm z ≤ p.gamma2 →
    useHint p (makeHint p z r) r = highBits p (r + z) := by
  intro hz
  refine Poly.ext_get_eq fun j => ?_
  simp only [useHint, makeHint, highBits, Vector.get_ofFn, Rq.get_add]
  apply congrArg fun n : ℕ => (n : Coeff)
  simpa using useHintCoeff_makeHintCoeff_eq_of_small (BalancedDecomp.ofApproved hp)
    (z := z.get j) (r := r.get j) (by simpa using cInfNorm_le_iff.mp hz j)

theorem concreteRounding_useHint_bound_of_isApproved (p : Params)
    (hp : p.isApproved) (r : Rq) (h : Hint) :
    cInfNorm (r - highBitsShift p (useHint p h r)) ≤ 2 * p.gamma2 + 1 := by
  refine cInfNorm_le_iff.mpr fun j => ?_
  simp only [Rq.get_sub, highBitsShift, Nat.cast_mul, Nat.cast_ofNat, useHint, Vector.map_ofFn,
      Vector.get_ofFn, Function.comp_apply]
  simpa using useHintCoeff_shift_sub_le
    (BalancedDecomp.ofApproved hp) (h.get j) (r.get j)

theorem concreteRounding_hide_low_of_isApproved (p : Params)
    (hp : p.isApproved) (r s : Rq) (b : ℕ) :
    cInfNorm s ≤ b →
    cInfNorm (lowBits p r) + b < p.gamma2 →
    highBits p (r + s) = highBits p r := by
  intro hs hlow
  refine Poly.ext_get_eq fun j => ?_
  simp only [highBits, Vector.get_ofFn, Rq.get_add]
  apply congrArg fun n : ℕ => (n : Coeff)
  have hr : (lowBitsCoeff (r.get j) p.gamma2).natAbs < p.gamma2 - b := by
    have hcoeff : (lowBitsCoeff (r.get j) p.gamma2).natAbs ≤ cInfNorm (lowBits p r) := by
      have := coeff_le_cInfNorm (lowBits p r) j
      rwa [lowBits_get, centeredRepr_intCast_lowBitsCoeff (r := r.get j)
        (hγ := gamma2_pos hp)
        (hq := two_gamma2_lt_modulus hp)] at this
    exact hcoeff.trans_lt (Nat.lt_sub_of_add_lt hlow)
  set alpha : ℕ := 2 * p.gamma2
  have : p.gamma2 = alpha /2 := by omega
  rw [this] at hr ⊢
  exact highBitsCoeff_add_eq_of_centeredRepr_lt
    (BalancedDecomp.ofApproved hp) (r.get j) (s.get j) (cInfNorm_le_iff.mp hs j) hr

theorem concretePower2RoundLaws :
    Power2RoundOps.Laws (ring := coeffRing) concretePower2RoundOps cInfNorm where
  power2Round_bound := concretePower2Round_bound

theorem concreteRoundingLaws_of_isApproved (p : Params) (hp : p.isApproved) :
    RoundingOps.Laws (ring := coeffRing) (concreteRoundingOps p) cInfNorm where
  high_low_decomp := concreteRounding_high_low_decomp p
  lowBits_bound r := by
    simpa using concreteRounding_lowBits_bound p (gamma2_pos hp)
      (two_gamma2_lt_modulus hp) r
  hide_low r s b hs hlow :=
    concreteRounding_hide_low_of_isApproved p hp r s b hs (by simpa using hlow)
  shift_injective := highBitsShift_injective_of_isApproved p hp
  useHint_correct z r hz :=
    concreteRounding_useHint_correct_of_isApproved p hp z r (by simpa using hz)
  useHint_bound := concreteRounding_useHint_bound_of_isApproved p hp

end MLDSA.Concrete
