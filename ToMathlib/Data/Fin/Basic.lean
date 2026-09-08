/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Membership in `Fin` intervals through `Fin.ofNat`
-/

public section

lemma Fin.ofNat_Icc_iff {n m : ℕ} (h : n < m) (x : Fin (m + 1)) :
    (Fin.ofNat (m + 1) n ≤ x ∧ x ≤ Fin.ofNat (m + 1) m) ↔ n ≤ x.val := by
  constructor
  · intro ⟨h1, _⟩
    have h1' : (Fin.ofNat (m + 1) n).val ≤ x.val := h1
    simp only [Fin.val_ofNat, Nat.mod_eq_of_lt (show n < m + 1 by omega)] at h1'
    exact h1'
  · intro hx
    exact ⟨show (Fin.ofNat (m + 1) n).val ≤ x.val by
              simp only [Fin.val_ofNat, Nat.mod_eq_of_lt (show n < m + 1 by omega)]; exact hx,
           show x.val ≤ (Fin.ofNat (m + 1) m).val by
              simp only [Fin.val_ofNat, Nat.mod_eq_of_lt (show m < m + 1 by omega)]; omega⟩
