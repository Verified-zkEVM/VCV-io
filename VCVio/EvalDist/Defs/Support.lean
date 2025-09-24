/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Possible Ouptuts of Computations

This file contains lemmas about `HasEvalSet` and `HasEvalFinset`.
We need to treat these somewhat uniquely due to the lack of global `Monad` instances.

dtumad: should consider when/where we use `Set` vs. `SetM`.
-/

open ENNReal

universe u v w

namespace HasEvalSet

variable {m : Type u → Type v} {α β γ : Type u} [Monad m] [HasEvalSet m]

@[simp] lemma support_pure (x : α) : support (pure x : m α) = {x} := by
  simp [support]

lemma mem_support_pure_iff (x y : α) : x ∈ support (pure y : m α) ↔ x = y := by aesop
lemma mem_support_pure_iff' (x y : α) : x ∈ support (pure y : m α) ↔ y = x := by aesop

@[simp] lemma support_bind (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) := by
  simp [support]

lemma mem_support_bind_iff (mx : m α) (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp

@[simp] lemma support_map [LawfulMonad m] (f : α → β) (mx : m α) :
    support (f <$> mx) = f '' support mx := by
  rw [map_eq_bind_pure_comp]
  aesop

@[simp] lemma support_seq [LawfulMonad m] (mf : m (α → β)) (mx : m α) :
    support (mf <*> mx) = ⋃ f ∈ support mf, f '' support mx := by
  simp [seq_eq_bind_map]

open Classical in
@[simp] lemma support_seqLeft [LawfulMonad m] (mx : m α) (my : m β) :
    support (mx <* my) = if support my = ∅ then ∅ else support mx := by
  simp [seqLeft_eq, Set.ext_iff]

open Classical in
@[simp] lemma support_seqRight [LawfulMonad m] (mx : m α) (my : m β) :
    support (mx *> my) = if support mx = ∅ then ∅ else support my := by
  simp [seqRight_eq, Set.ext_iff]

end HasEvalSet
