/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# F-coalgebras

An `F`-coalgebra for an endofunctor `F` on `Type` is a type `S` together with a
structure map `out : S → F S`.

This is the categorical dual of `MonadAlgebra`: where an algebra collapses a
functor layer, a coalgebra *observes* one layer of structure from a state.

## Main definitions

* `Coalgebra F S`: typeclass packaging `out : S → F S`.
* `Coalgebra.Hom S₁ S₂`: a function `S₁ → S₂` that commutes with the structure
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

This is the dual of `MonadAlgebra`. No `[Functor F]` constraint is imposed on the
class itself so that the definition applies to arbitrary type-level maps. -/
class Coalgebra (F : Type u → Type v) (S : Type u) where
  out : S → F S

export Coalgebra (out)

/-! ## Coalgebra morphisms -/

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
structure Coalgebra.Hom (F : Type u → Type v) [Functor F]
    (S₁ : Type u) (S₂ : Type u) [Coalgebra F S₁] [Coalgebra F S₂] where
  /-- The underlying function between state spaces. -/
  toFun : S₁ → S₂
  /-- The commutativity condition: `F.map f ∘ out = out ∘ f`. -/
  comm : Functor.map toFun ∘ (out : S₁ → F S₁) = (out : S₂ → F S₂) ∘ toFun

namespace Coalgebra.Hom

variable {F : Type u → Type v} [Functor F]
variable {S₁ S₂ S₃ : Type u} [Coalgebra F S₁] [Coalgebra F S₂] [Coalgebra F S₃]

instance : CoeFun (Coalgebra.Hom F S₁ S₂) (fun _ => S₁ → S₂) where
  coe := Coalgebra.Hom.toFun

@[ext]
theorem ext {f g : Coalgebra.Hom F S₁ S₂} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g; congr; funext x; exact h x

variable [LawfulFunctor F]

/-- The identity coalgebra morphism. -/
def id : Coalgebra.Hom F S₁ S₁ where
  toFun := _root_.id
  comm := by funext x; simp [Function.comp, id_map]

/-- Composition of coalgebra morphisms. -/
def comp (g : Coalgebra.Hom F S₂ S₃) (f : Coalgebra.Hom F S₁ S₂) :
    Coalgebra.Hom F S₁ S₃ where
  toFun := g.toFun ∘ f.toFun
  comm := by
    funext x
    show (g.toFun ∘ f.toFun) <$> (out : S₁ → F S₁) x =
      (out : S₃ → F S₃) (g.toFun (f.toFun x))
    have hf := congrFun f.comm x
    have hg := congrFun g.comm (f.toFun x)
    simp only [Function.comp_apply] at hf hg
    rw [comp_map, hf, hg]

end Coalgebra.Hom
