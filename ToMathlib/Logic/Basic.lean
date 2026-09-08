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

`Prod.mk` as an injective binary function and an inhabitant of the bijections of a type.
-/

public section

universe u

lemma Prod.mk.injective2 {α β : Type*} :
    Function.Injective2 (Prod.mk : α → β → α × β) := by
  simp [Function.Injective2]

instance (α : Type) [Inhabited α] : Inhabited {f : α → α // f.Bijective} :=
  ⟨id, Function.bijective_id⟩
