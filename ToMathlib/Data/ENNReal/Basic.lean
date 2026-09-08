/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Finite products in `ℝ≥0∞`

A list product of natural-number casts never reaches `⊤`.
-/

public section

namespace ENNReal

lemma list_prod_natCast_ne_top {ι : Type*} (f : ι → ℕ) (js : List ι) :
    (js.map (fun j => (f j : ℝ≥0∞))).prod ≠ ⊤ := by
  have h : (js.map (fun j => (f j : ℝ≥0∞))).prod = ↑((js.map f).prod) := by
    induction js with
    | nil => simp
    | cons j js ih => simp [ih, Nat.cast_mul]
  rw [h]; exact natCast_ne_top _

end ENNReal
