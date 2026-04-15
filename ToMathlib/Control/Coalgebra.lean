/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.FunLike.Basic

/-!
# F-coalgebras

An `F`-coalgebra for an endofunctor `F` on `Type` is a type `S` together with a
structure map `out : S → F S`.

This is the categorical dual of `MonadAlgebra`: where an algebra collapses a
functor layer, a coalgebra *observes* one layer of structure from a state.

## Main definitions

* `Coalg F S`: typeclass packaging `out : S → F S`.
* `Coalg.Hom S₁ S₂`: a function `S₁ → S₂` that commutes with the structure
  maps (`Functor.map f ∘ out = out ∘ f`). Equipped with coercion, `id`, `comp`.

## Relationship to Mathlib and Poly

`CategoryTheory.Endofunctor.Coalgebra` in Mathlib defines coalgebras for
endofunctors on an arbitrary category. This file instead provides a Lean-native
typeclass for `Type`-endofunctors, following the style of `MonadAlgebra`.
The `Type`-level definition suffices for the interaction framework, where
the step functors (`StepOver Γ`, `Machine.StepFun`) are polynomial
endofunctors on `Type` in the sense of the Poly book (Spivak, 2022).
-/

universe u v

/-- An `F`-coalgebra on `S` is a structure map `out : S → F S`.

Named `Coalg` to avoid collision with `Mathlib.RingTheory.Coalgebra`.
This is the dual of `MonadAlgebra`. No `[Functor F]` constraint is imposed on the
class itself so that the definition applies to arbitrary type-level maps. -/
class Coalg (F : Type u → Type v) (S : Type u) where
  out : S → F S

export Coalg (out)

/-! ## Coalg morphisms -/

/-- A coalgebra morphism between `F`-coalgebras on `S₁` and `S₂` is a function
that commutes with the structure maps:
```
      out
  S₁ -----> F S₁
  |          |
  f        F f
  |          |
  v          v
  S₂ -----> F S₂
      out
```
In the interaction framework, coalgebra morphisms between processes correspond
to forward simulations that preserve step structure. -/
structure Coalg.Hom (F : Type u → Type v) [Functor F]
    (S₁ : Type u) (S₂ : Type u) [Coalg F S₁] [Coalg F S₂] where
  /-- The underlying function between state spaces. -/
  toFun : S₁ → S₂
  /-- The commutativity condition: `F.map f ∘ out = out ∘ f`. -/
  comm : Functor.map toFun ∘ (out : S₁ → F S₁) = (out : S₂ → F S₂) ∘ toFun

namespace Coalg.Hom

variable {F : Type u → Type v} [Functor F]
variable {S₁ S₂ S₃ : Type u} [Coalg F S₁] [Coalg F S₂] [Coalg F S₃]

instance : FunLike (Coalg.Hom F S₁ S₂) S₁ S₂ where
  coe := Coalg.Hom.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[ext]
theorem ext {f g : Coalg.Hom F S₁ S₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable [LawfulFunctor F]

/-- The identity coalgebra morphism. -/
def id : Coalg.Hom F S₁ S₁ where
  toFun := _root_.id
  comm := by funext x; simp [Function.comp, id_map]

/-- Composition of coalgebra morphisms. -/
def comp (g : Coalg.Hom F S₂ S₃) (f : Coalg.Hom F S₁ S₂) :
    Coalg.Hom F S₁ S₃ where
  toFun := g.toFun ∘ f.toFun
  comm := by
    funext x
    simp only [Function.comp_apply]
    have hf := congrFun f.comm x
    have hg := congrFun g.comm (f.toFun x)
    simp only [Function.comp_apply] at hf hg
    rw [comp_map, hf, hg]

@[simp]
theorem id_apply (x : S₁) : (Coalg.Hom.id : Coalg.Hom F S₁ S₁) x = x := rfl

@[simp]
theorem comp_apply (g : Coalg.Hom F S₂ S₃) (f : Coalg.Hom F S₁ S₂) (x : S₁) :
    (Coalg.Hom.comp g f) x = g (f x) := rfl

end Coalg.Hom
