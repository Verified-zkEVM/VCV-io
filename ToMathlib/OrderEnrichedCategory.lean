module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.Order.Category.Preord
public import Mathlib.Order.Monotone.Basic

open CategoryTheory

/-! # Order enriched category

We show that the general definition of an enriched category over a monoidal category specializes to
an order-enriched category when the monoidal category is the category of preorders.
-/

@[expose] public section

universe w v u u₁ u₂

namespace Preord

/-- The category of preorders is monoidal. -/
instance : MonoidalCategory (Preord) where
  tensorObj X Y := ⟨X.carrier × Y.carrier⟩
  whiskerLeft X Y := fun f => ofHom ⟨fun x => (x.1, f.1 x.2),
      (by simp [Monotone]; intro _ _ _ _ h h'; exact ⟨h, f.hom.2 h'⟩)⟩
  whiskerRight f Y := ofHom ⟨fun y => (f.hom y.1, y.2),
      (by simp [Monotone]; intro _ _ _ _ h h'; exact ⟨f.hom.2 h, h'⟩)⟩
  tensorUnit := ⟨PUnit⟩
  associator X Y Z := {
    hom := ofHom ⟨fun ⟨⟨x, y⟩, z⟩ => ⟨x, ⟨y, z⟩⟩, by
      simp only [Monotone, Prod.mk_le_mk, Prod.forall, and_imp]
      intro _ _ _ _ _ _ h1 h2 h3; exact ⟨h1, h2, h3⟩⟩
    inv := ofHom ⟨fun ⟨x, ⟨y, z⟩⟩ => ⟨⟨x, y⟩, z⟩, by
      simp only [Monotone, Prod.mk_le_mk, Prod.forall, and_imp]
      intro _ _ _ _ _ _ h1 h2 h3; exact ⟨⟨h1, h2⟩, h3⟩⟩ }
  leftUnitor X := {
    hom := ofHom ⟨Prod.snd, (by simp [Monotone])⟩
    inv := ofHom ⟨fun x => (PUnit.unit, x), by simp [Monotone]⟩ }
  rightUnitor X := {
    hom := ofHom ⟨Prod.fst, (by simp [Monotone])⟩
    inv := ofHom ⟨fun x => (x, PUnit.unit), by simp [Monotone]⟩ }
  tensorHom_def f g := rfl
  -- tensor_id _ _ := rfl
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := rfl
  whiskerLeft_id _ _ := rfl
  id_whiskerRight _ _ := rfl
  associator_naturality f₁ f₂ f₃ := rfl
  leftUnitor_naturality f := rfl
  rightUnitor_naturality f := rfl
  pentagon _ _ _ _ := rfl
  triangle _ _ := rfl

end Preord

namespace CategoryTheory

open MonoidalCategory

namespace EnrichedCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

variable {c : Type u → Type v} [Category.{w} (Bundled c)] [MonoidalCategory (Bundled c)]

variable (C : Type u₁) (D : Type u₂) [𝒞 : EnrichedCategory V C] [𝒟 : EnrichedCategory V D]

@[simps]
instance instProduct : EnrichedCategory V (C × D) where
  Hom X Y := (𝒞.Hom X.1 Y.1) ⊗ (𝒟.Hom X.2 Y.2)
  id X := (λ_ _).inv ≫ (sorry)
  -- ((𝒞.id X.1) ⊗ (𝒟.id X.2))
  comp X Y Z := by stop simpa using (𝒞.comp X.1 Y.1 Z.1) ⊗ (𝒟.comp X.2 Y.2 Z.2)
  -- (α_ _ _ _).inv ≫ (
  -- id_comp X Y := by
  --   ext ⟨⟨x, y⟩, z⟩
  --   simp [id_comp]

-- structure RelativeMonad (J : C ⥤ D) where
--   /-- The monadic mapping on objects. -/
--   T : C → D
--   /-- The unit for the relative monad. -/
--   η : ∀ {X}, J.obj X ⟶ T X
--   /-- The multiplication for the monad. -/
--   μ : ∀ {X Y}, ((J.obj X) ⟶ (T Y)) → ((T X) ⟶ (T Y))
--   /-- `μ` applied to `η` is identity. -/
--   left_unit : ∀ {X}, μ η = 𝟙 (T X) := by aesop_cat
--   /-- `η` composed with `μ` is identity. -/
--   right_unit : ∀ {X Y}, ∀ f : (J.obj X) ⟶ (T Y), η ≫ (μ f) = f := by aesop_cat
--   /-- `μ` is associative. -/
--   assoc : ∀ {X Y Z}, ∀ f : (J.obj X) ⟶ (T Y), ∀ g : (J.obj Y) ⟶ (T Z),
--     μ (f ≫ μ g) = (μ f) ≫ (μ g) := by aesop_cat

variable (C : Type u₁) (D : Type u₂)
  [𝒞 : EnrichedCategory (Bundled c) C] [𝒟 : EnrichedCategory (Bundled c) D]

variable (J : EnrichedFunctor (Bundled c) C D)

structure RelativeMonad where
  T : C → D
  η : {A : C} → (J.obj A ⟶[ Bundled c ] T A)
  μ : {A B : C} → (J.obj A ⟶[ Bundled c ] T B) ⟶ (T A ⟶[ Bundled c ] T B)
  -- assoc : (α_ _ _ _).inv ≫ J.map (μ ⊗ 𝟭 _) ≫ μ = J.map (𝟭 _ ⊗ μ) ≫ μ
  -- left_unit : (λ_ _).inv ≫ J.map (𝟭 _ ⊗ η) ≫ μ = η
  -- right_unit : (ρ_ _).inv ≫ J.map (η ⊗ 𝟭 _) ≫ μ = η

namespace RelativeMonad

@[simps]
def inducedFunctor (M : RelativeMonad C D J) : EnrichedFunctor (Bundled c) C D where
  obj A := M.T A
  map f := sorry

-- def prod

-- def ofNatIso

-- def precompose

-- def postcompose

-- def lift (F : EnrichedFunctor C D) (φ : J₂ ≅ (J₁ ⋙ F)) (M : RelativeMonad C D₂ J₂) : RelativeMonad C D₁ J₁ where

end RelativeMonad

-- (lax) morphism between relative monads in enriched categories
structure RelativeMonadHom (M N : RelativeMonad C D J) where
  -- f : M.inducedFunctor J ⟶ N.inducedFunctor J

class RelativeMonadHom.IsStrict (M N : RelativeMonad C D J) (F : RelativeMonadHom C D J M N) where


end EnrichedCategory

/-- Categories enriched over the monoidal category of preorders are preorder-enriched categories. -/
abbrev PreordEnrichedCategory (C : Type u) := EnrichedCategory Preord C

#check Category.assoc

namespace PreordEnrichedCategory

variable {C : Type u} [PreordEnrichedCategory C]


end PreordEnrichedCategory

-- TODO: simplify the enriched category definition to see the order-enriched category structure.

end CategoryTheory
