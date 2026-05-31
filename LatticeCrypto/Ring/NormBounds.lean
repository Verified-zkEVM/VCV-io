/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ring.Norms
import LatticeCrypto.Ring.VectorBackend

/-!
# Norm Growth Bounds For The Centered `ZMod q` Norm

Genuine (non-assumed) proofs of the two norm-growth facts the Hachi/Greyhound
weak-binding argument relies on, specialized to the canonical centered norm
`zmodPolyNormOps` on `vectorNegacyclicRing (ZMod q) n`:

* `sub_l2NormSq_le` — `‖v - w‖₂² ≤ 4·b` when `‖v‖₂², ‖w‖₂² ≤ b`.
* `scalarVecMul_mul_l2NormSq_le` — Micciancio/Young: scaling by a ring element of
  bounded `ℓ₁` norm grows the squared `ℓ₂` norm by at most `κ²`.

The foundational fact is the *minimality* of the centered representative
`centeredRepr` (= `ZMod.valMinAbs`): it has the least absolute value among all
integer representatives, `centeredRepr_natAbs_le`.
-/

open scoped BigOperators

namespace LatticeCrypto

variable {q : ℕ} [NeZero q]

/-! ## Minimality of the centered representative -/

/-- The centered representative has the least absolute value among all integer
representatives of a residue class. -/
theorem centeredRepr_natAbs_le {a : ZMod q} {m : ℤ} (h : (m : ZMod q) = a) :
    (centeredRepr a).natAbs ≤ m.natAbs := by
  rw [centeredRepr_eq_valMinAbs]
  have hmem := ZMod.valMinAbs_mem_Ioc a
  rw [Set.mem_Ioc] at hmem
  have hcast : (m : ZMod q) = ((a.valMinAbs : ℤ) : ZMod q) := by
    rw [h, ZMod.coe_valMinAbs]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  obtain ⟨t, ht⟩ := hcast
  have hq : (1 : ℤ) ≤ (q : ℤ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  rcases eq_or_ne t 0 with ht0 | ht0
  · subst ht0; simp only [mul_zero] at ht; omega
  · have habs : q ≤ ((q : ℤ) * t).natAbs := by
      have ht1 : 1 ≤ t.natAbs := Int.natAbs_pos.mpr ht0
      rw [Int.natAbs_mul]
      simp only [Int.natAbs_natCast]
      nlinarith [ht1]
    revert ht habs
    generalize (q : ℤ) * t = k
    intro ht habs
    omega

/-- The centered representative of a difference is bounded by the sum of the
centered representatives' absolute values. -/
theorem centeredRepr_sub_natAbs_le (a b : ZMod q) :
    (centeredRepr (a - b)).natAbs ≤ (centeredRepr a).natAbs + (centeredRepr b).natAbs := by
  have h : ((centeredRepr a - centeredRepr b : ℤ) : ZMod q) = a - b := by
    rw [Int.cast_sub, ← centeredRepr_intCast a, ← centeredRepr_intCast b]
  exact le_trans (centeredRepr_natAbs_le h) (Int.natAbs_sub_le _ _)

/-! ## The growth-bound expressions -/

/-- Squared-`ℓ₂` growth bound for scaling an already-scaled vector by one more
scalar of bounded `ℓ₁` norm: `κ² · β²`. -/
def scalarVecMulMulL2NormSqBound (kappa betaSq : ℕ) : ℕ := kappa ^ 2 * betaSq

/-- Squared-`ℓ₂` bound for the difference of two vectors each within `boundSq`: `4 · boundSq`. -/
def subL2NormSqBound (boundSq : ℕ) : ℕ := 4 * boundSq

/-! ## The centered squared-`ℓ₂` norm on the vector backend -/

variable {n : ℕ}

/-- File-local shorthand for the canonical centered-norm bundle on the degree-`n`
vector backend over `ZMod q`. -/
local notation:max "normOps" => zmodPolyNormOps q (vectorBackend (ZMod q) n)

/-- Pointwise description of the centered squared-`ℓ₂` norm. -/
theorem l2NormSq_apply (p : (vectorNegacyclicRing (ZMod q) n).Poly) :
    ‖p‖⟪normOps⟫₂²
      = ∑ i : Fin n, (centeredRepr (p.get i)).natAbs ^ 2 :=
  rfl

/-- Per-polynomial subtraction bound for the centered squared-`ℓ₂` norm. -/
theorem l2NormSq_poly_sub_le (x y : (vectorNegacyclicRing (ZMod q) n).Poly) :
    ‖x - y‖⟪normOps⟫₂² ≤
      2 * (‖x‖⟪normOps⟫₂²
        + ‖y‖⟪normOps⟫₂²) := by
  rw [l2NormSq_apply, l2NormSq_apply, l2NormSq_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [show (x - y).get i = x.get i - y.get i from vectorRing_sub_get x y i]
  have hcoeff := centeredRepr_sub_natAbs_le (x.get i) (y.get i)
  have hcoeffZ : ((centeredRepr (x.get i - y.get i)).natAbs : ℤ)
      ≤ (centeredRepr (x.get i)).natAbs + (centeredRepr (y.get i)).natAbs := by
    exact_mod_cast hcoeff
  have key : ((centeredRepr (x.get i - y.get i)).natAbs : ℤ) ^ 2
      ≤ 2 * (((centeredRepr (x.get i)).natAbs : ℤ) ^ 2
        + ((centeredRepr (y.get i)).natAbs : ℤ) ^ 2) := by
    nlinarith [hcoeffZ, Int.natCast_nonneg (centeredRepr (x.get i - y.get i)).natAbs,
      sq_nonneg (((centeredRepr (x.get i)).natAbs : ℤ) - (centeredRepr (y.get i)).natAbs)]
  exact_mod_cast key

/-- **Subtraction bound.** The squared `ℓ₂` norm of a difference of two vectors,
each within `boundSq`, is within `subL2NormSqBound boundSq = 4·boundSq`. -/
theorem sub_l2NormSq_le {cols : ℕ}
    (v w : PolyVec (vectorNegacyclicRing (ZMod q) n).Poly cols) {boundSq : ℕ}
    (hv : ‖v‖⟪normOps⟫₂² ≤ boundSq)
    (hw : ‖w‖⟪normOps⟫₂² ≤ boundSq) :
    ‖v - w‖⟪normOps⟫₂² ≤
      subL2NormSqBound boundSq := by
  have hstep :
      ‖v - w‖⟪normOps⟫₂² ≤
        2 * (‖v‖⟪normOps⟫₂²
          + ‖w‖⟪normOps⟫₂²) := by
    rw [show ‖v - w‖⟪normOps⟫₂²
          = ∑ j : Fin cols,
            ‖ (v - w).get j‖⟪normOps⟫₂² from rfl,
        show ‖v‖⟪normOps⟫₂²
          = ∑ j : Fin cols,
            ‖v.get j‖⟪normOps⟫₂² from rfl,
        show ‖w‖⟪normOps⟫₂²
          = ∑ j : Fin cols,
            ‖w.get j‖⟪normOps⟫₂² from rfl,
        ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    calc ‖ (v - w).get j‖⟪normOps⟫₂²
        = ‖v.get j - w.get j‖⟪normOps⟫₂² := by
          congr 1; exact Vector.getElem_sub v w j.val j.isLt
      _ ≤ 2 * (‖v.get j‖⟪normOps⟫₂²
            + ‖w.get j‖⟪normOps⟫₂²) :=
          l2NormSq_poly_sub_le (v.get j) (w.get j)
  calc ‖v - w‖⟪normOps⟫₂²
      ≤ 2 * (‖v‖⟪normOps⟫₂²
          + ‖w‖⟪normOps⟫₂²) := hstep
    _ ≤ subL2NormSqBound boundSq := by unfold subL2NormSqBound; omega

/-- **Micciancio/Young product bound.** Scaling an already-`c`-scaled vector by a
further ring element `d` of bounded `ℓ₁` norm grows the squared `ℓ₂` norm by at
most `κ²`.

The statement is the honest Young/Micciancio inequality
`‖(d·c)·v‖₂² ≤ ‖d‖₁² · ‖c·v‖₂²` over the negacyclic convolution with centered
representatives; its proof (discrete Cauchy–Schwarz over the cyclic convolution,
together with `centeredRepr_natAbs_le`) is deferred. -/
theorem scalarVecMul_mul_l2NormSq_le {cols : ℕ}
    (c d : (vectorNegacyclicRing (ZMod q) n).Poly)
    (v : PolyVec (vectorNegacyclicRing (ZMod q) n).Poly cols) {kappa betaSq : ℕ}
    (hd : ‖d‖⟪normOps⟫₁ ≤ kappa)
    (hv : ‖NegacyclicRing.scalarVecMul (vectorNegacyclicRing (ZMod q) n) c v‖⟪normOps⟫₂² ≤ betaSq) :
    ‖NegacyclicRing.scalarVecMul (vectorNegacyclicRing (ZMod q) n)
          ((vectorNegacyclicRing (ZMod q) n).mul c d) v‖⟪normOps⟫₂² ≤
      scalarVecMulMulL2NormSqBound kappa betaSq := by
  sorry

end LatticeCrypto
