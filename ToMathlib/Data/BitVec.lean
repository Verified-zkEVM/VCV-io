/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Data.FinEnum

/-!
# `BitVec` cardinality and xor cancellation
-/

public section

/-- `BitVec n` has `2 ^ n` elements, read off Mathlib's `FinEnum (BitVec n)`. -/
@[simp]
lemma Fintype.card_bitVec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n :=
  FinEnum.card_eq_fintypeCard.symm.trans (FinEnum.card_bitVec n)

@[simp]
lemma BitVec.xor_self_xor {n : ℕ} (x y : BitVec n) : x ^^^ (x ^^^ y) = y := by
  rw [← BitVec.xor_assoc, xor_self, zero_xor]
