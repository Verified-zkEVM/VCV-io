/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs

/-!
# Small logic and function lemmas

`Prod.mk` as an injective binary function, swapping the arguments of an injective binary
function, `cast` through `Option`, and an inhabitant of the bijections of a type.
-/

public section

universe u

lemma Prod.mk.injective2 {α β : Type*} :
    Function.Injective2 (Prod.mk : α → β → α × β) := by
  simp [Function.Injective2]

lemma Function.injective2_swap_iff {α β γ : Type*} (f : α → β → γ) :
    (Function.swap f).Injective2 ↔ f.Injective2 :=
  ⟨fun h _ _ _ _ h' ↦ and_comm.1 (h h'), fun h _ _ _ _ h' ↦ and_comm.1 (h h')⟩

instance (α : Type) [Inhabited α] : Inhabited {f : α → α // f.Bijective} :=
  ⟨id, Function.bijective_id⟩

theorem Option.cast_eq_some_iff {α β : Type u} {x : Option α} {b : β} (h : α = β) :
    cast (congrArg Option h) x = some b ↔ x = some (cast h.symm b) := by
  subst h; simp only [cast_eq]
