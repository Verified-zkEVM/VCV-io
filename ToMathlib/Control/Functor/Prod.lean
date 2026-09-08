/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Control.Basic

/-!
# Projections of functorial maps on products

The `fst <$> (Prod.map f g <$> x)` family for a lawful functor.
-/

public section

universe u v w x

@[simp, grind =]
lemma fst_map_prod_map {m : Type u → Type v} [Functor m] [LawfulFunctor m] {α β γ δ : Type u}
    (mx : m (α × β)) (f : α → γ) (g : β → δ) :
    Prod.fst <$> Prod.map f g <$> mx = (f ∘ Prod.fst) <$> mx := by
  simp [Functor.map_map]; rfl

@[simp, grind =]
lemma snd_map_prod_map {m : Type u → Type v} [Functor m] [LawfulFunctor m] {α β γ δ : Type u}
    (mx : m (α × β)) (f : α → γ) (g : β → δ) :
    Prod.snd <$> Prod.map f g <$> mx = (g ∘ Prod.snd) <$> mx := by
  simp [Functor.map_map]; rfl

/-- Split form: the second projection after `Prod.map` equals the mapped projection. -/
lemma snd_map_prod_map_eq_map {m : Type u → Type v} [Functor m] [LawfulFunctor m]
    {α β γ δ : Type u} (mx : m (α × β)) (f : α → γ) (g : β → δ) :
    Prod.snd <$> Prod.map f g <$> mx = g <$> (Prod.snd <$> mx) :=
  (snd_map_prod_map mx f g).trans (Functor.map_map Prod.snd g mx).symm
