/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Sign.Basic

/-!
# Absolute values against a sign-determined factor
-/

public section

section abs

variable {G : Type*} [CommRing G] [LinearOrder G] [IsStrictOrderedRing G] {a b : G}

lemma mul_abs_of_nonneg (h : 0 ≤ a) : a * |b| = |a * b| := by
  rw [abs_mul, abs_of_nonneg h]

lemma abs_mul_of_nonneg (h : 0 ≤ b) : |a| * b = |a * b| := by
  rw [abs_mul, abs_of_nonneg h]

lemma mul_abs_of_nonpos (h : a < 0) : a * |b| = - |a * b| := by
  rw (occs := [1]) [← sign_mul_abs a]
  rw [abs_mul, neg_eq_neg_one_mul, mul_assoc]
  congr; simp [h]

lemma abs_mul_of_nonpos (h : b < 0) : |a| * b = - |a * b| := by
  rw (occs := [1]) [← sign_mul_abs b]
  rw [abs_mul, neg_eq_neg_one_mul, ← mul_assoc, mul_comm |a| _, mul_assoc]
  congr; simp [h]

end abs
