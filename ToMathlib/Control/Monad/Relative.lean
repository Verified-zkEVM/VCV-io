/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Relative monad

This file defines the `RelativeMonad` type class, both as a category-theoretic object and a
programming object.

-/

@[expose] public section

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Iso

-- def assoc : (f ⋙ g) ⋙ h ≅ f ⋙ (g ⋙ h)

end Iso

-- morphism levels before object levels. See note [CategoryTheory universes].
variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/-- The data of a **relative monad** over a functor `J : C ⟶ D` consists of:
- a map between objects `T : C → D`
- a natural transformation `η : ∀ {X}, J X ⟶ T X`
- a natural transformation `μ : ∀ {X Y}, (J X ⟶ T Y) ⟶ (T X ⟶ T Y)`
satisfying three equations:
- `μ_{X, X} ∘ η_X = 1_{T X}` (left unit)
- `∀ f, η_X ≫ μ_{X, Y} = f` (right unit)
- `∀ f g, μ_{X, Z} (f ≫ μ_{Y, Z} g) = μ_{X, Y} f ≫ μ_{Y, Z} g` (associativity)
-/
structure RelativeMonad (J : C ⥤ D) where
  /-- The monadic mapping on objects. -/
  T : C → D
  /-- The unit for the relative monad. -/
  η : ∀ {X}, J.obj X ⟶ T X
  /-- The multiplication for the monad. -/
  μ : ∀ {X Y}, ((J.obj X) ⟶ (T Y)) → ((T X) ⟶ (T Y))
  /-- `μ` applied to `η` is identity. -/
  left_unit : ∀ {X}, μ η = 𝟙 (T X) := by aesop_cat
  /-- `η` composed with `μ` is identity. -/
  right_unit : ∀ {X Y}, ∀ f : (J.obj X) ⟶ (T Y), η ≫ (μ f) = f := by aesop_cat
  /-- `μ` is associative. -/
  assoc : ∀ {X Y Z}, ∀ f : (J.obj X) ⟶ (T Y), ∀ g : (J.obj Y) ⟶ (T Z),
    μ (f ≫ μ g) = (μ f) ≫ (μ g) := by aesop_cat

attribute [reassoc (attr := simp)] RelativeMonad.left_unit RelativeMonad.right_unit
attribute [reassoc (attr := simp)] RelativeMonad.assoc

namespace RelativeMonad

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {J : C ⥤ D}

/-- The functor induced by a relative monad.

**Note:** this is _not_ the same as the underlying functor of the relative monad. -/
@[simps]
def inducedFunctor (M : RelativeMonad C D J) : C ⥤ D where
  obj X := M.T X
  map f := M.μ (J.map f ≫ M.η)
  map_comp f g := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← assoc, Category.assoc, right_unit]

/-- The natural transformation from the underlying functor of the relative monad, to the functor
induced by the relative monad. -/
def inducedNatTrans (M : RelativeMonad C D J) : NatTrans J M.inducedFunctor where
  app X := M.η

/-- If a relative monad is over the identity functor, it is a monad. -/
def monadOfId (M : RelativeMonad C _ (𝟭 _)) : Monad C where
  toFunctor := M.inducedFunctor
  η := { app X := M.η }
  μ := NatTrans.mk (fun X => M.μ (𝟙 (M.T X)))
    (fun X Y f => by simp; rw [← assoc, ← assoc]; simp)
  right_unit _ := by simp; rw [← assoc]; simp
  assoc _ := by simp; rw [← assoc, ← assoc]; simp

/-- Transport a relative monad along a natural isomorphism of the underlying functor. -/
def ofNatIso {J₁ J₂ : C ⥤ D} (φ : J₁ ≅ J₂) (M : RelativeMonad C D J₁) : RelativeMonad C D J₂ where
  T := M.T
  η := φ.inv.app _ ≫ M.η
  μ := fun f => M.μ (φ.hom.app _ ≫ f)
  assoc f g := by rw [← assoc]; simp

/-- Precompose a relative monad `M : RelativeMonad C D J` along a functor `J' : C' ⥤ C`. -/
def precompose {C' : Type u₃} [Category.{v₃} C'] (J' : C' ⥤ C) (M : RelativeMonad C D J) :
    RelativeMonad C' D (J' ⋙ J) where
  T := M.T ∘ J'.obj
  η := M.η
  μ := M.μ

-- TODO: post-composition by a fully faithful functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {D₂ : Type u₄} [Category.{v₄} D₂]
  {J₁ : C₁ ⥤ D₁} {J₂ : C₂ ⥤ D₂}

/-- The product of two relative monads is a relative monad on the corresponding product categories.
  -/
@[simps!]
def prod (M₁ : RelativeMonad C₁ D₁ J₁) (M₂ : RelativeMonad C₂ D₂ J₂) :
    RelativeMonad (C₁ × C₂) (D₁ × D₂) (Functor.prod J₁ J₂) where
  T := fun X => (M₁.T X.fst, M₂.T X.snd)
  η := ⟨M₁.η, M₂.η⟩
  μ := fun f => ⟨M₁.μ f.fst, M₂.μ f.snd⟩

end RelativeMonad

variable {C : Type u₁} [Category.{v₁} C] {D₁ : Type u₂} [Category.{v₂} D₁]
  {D₂ : Type u₃} [Category.{v₃} D₂] {J₁ : C ⥤ D₁} {J₂ : C ⥤ D₂}

/-- A morphism of relative monads, where the two ending categories may be different. We require
another functor & a natural isomorphism to correct for this discrepancy. -/
structure RelativeMonadHom (M₁ : RelativeMonad C D₁ J₁) (M₂ : RelativeMonad C D₂ J₂) where
  J₁₂ : D₁ ⥤ D₂
  φ : J₂ ≅ (J₁ ⋙ J₁₂)
  map : ∀ {X}, J₁₂.obj (M₁.T X) ⟶ M₂.T X
  map_η : ∀ {X}, J₁₂.map M₁.η ≫ map = φ.inv.app X ≫ M₂.η := by aesop_cat
  map_μ : ∀ {X Y}, ∀ f : (J₁.obj X) ⟶ M₁.T Y,
    J₁₂.map (M₁.μ f) ≫ map = map ≫ M₂.μ (φ.hom.app _ ≫ J₁₂.map f ≫ map) := by aesop_cat

attribute [reassoc (attr := simp)] RelativeMonadHom.map_η RelativeMonadHom.map_μ

namespace RelativeMonadHom

variable {C' : Type u₄} [Category.{v₄} C'] {J' : C' ⥤ C}
  {M₁ : RelativeMonad C D₁ J₁} {M₂ : RelativeMonad C D₂ J₂}

-- @[simps!]
-- def precompose (f : RelativeMonadHom M₁ M₂) :
--     RelativeMonadHom (M₁.precompose J') (M₂.precompose J') where
--   J₁₂ := f.J₁₂
--   φ := sorry
--   map := f.map

end RelativeMonadHom

-- #check CategoryTheory.isoEquivOfFullyFaithful

end CategoryTheory


/-! ## Old stuff below.

Turns out one cannot just work with `Type u → Type v`, since in the relational context, relative
relational specification monad actually has signature `Type u₁ × Type u₂ → Type v₁ × Type v₂`. This
means that we have to develop the general theory at the category-theoretic level.

-/

universe u w v

/-- Type class for the relative pure operation -/
class RelativePure (j : Type u → Type w) (f : Type u → Type v) where
  /-- The relative pure operation -/
  pureᵣ : {α : Type u} → j α → f α

export RelativePure (pureᵣ)

/-- Type class for the relative bind operation -/
class RelativeBind (j : Type u → Type w) (m : Type u → Type v) where
  /-- The relative bind operation -/
  bindᵣ : {α β : Type u} → m α → (j α → m β) → m β

export RelativeBind (bindᵣ)

/-- Type class for the relative map operation -/
class RelativeFunctor (j : Type u → Type w) (f : Type u → Type v) where
  /-- The relative map operation -/
  mapᵣ : {α β : Type u} → (j α → j β) → (f α → f β)
  mapConstᵣ : {α β : Type u} → j α → f β → f α := mapᵣ ∘ Function.const _

export RelativeFunctor (mapᵣ mapConstᵣ)

-- Don't think sequencing makes sense in the relative setting?

-- class RelativeSeq (r : Type u → Type w) (m : Type u → Type v) where
--   /-- The relative seq operation -/
--   seqᵣ : {α β : Type u} → m (α → β) → (Unit → m α) → m β

-- export RelativeSeq (seqᵣ)

-- class RelativeSeqLeft (r : Type u → Type w) (m : Type u → Type v) where
--   /-- The relative seq left operation -/
--   seqLeftᵣ : {α β : Type u} → m α → (Unit → m β) → m α

-- export RelativeSeqLeft (seqLeftᵣ)

-- class RelativeSeqRight (r : Type u → Type w) (m : Type u → Type v) where
--   /-- The relative seq right operation -/
--   seqRightᵣ : {α β : Type u} → m α → (Unit → m β) → m β

-- export RelativeSeqRight (seqRightᵣ)

@[inherit_doc] infixl:55  " >>=ᵣ " => RelativeBind.bindᵣ
@[inherit_doc] infixr:100 " <$>ᵣ " => RelativeFunctor.mapᵣ

-- class RelativeApplicative (r : Type u → Type w) (m : Type u → Type v)
--     [Seq r] [SeqLeft r] [SeqRight r] extends
--     RelativeFunctor r m, RelativePure r m, Seq m, SeqLeft m, SeqRight m where
--   map f x := Seq.seq (pureᵣ x) (fun _ => f)
--   seqLeft x y := Seq.seq (mapᵣ (fun y => ·) x) y
--   seqRight x y := Seq.seq (mapᵣ (fun y => y *> ·) x) y

/-- Type class for the relative monad -/
class RelativeMonad (j : Type u → Type w) (m : Type u → Type v)
    extends RelativePure j m, RelativeBind j m, RelativeFunctor j m where
  mapᵣ f x := bindᵣ x (pureᵣ ∘ f)

-- bind f fun y => Functor.map y (x ())

def instFunctorOfRelativeMonad {j : Type u → Type w} [Functor j] {m : Type u → Type v}
    [RelativeMonad j m] : Functor m where
  map f x := bindᵣ (j := j) x (pureᵣ ∘ (Functor.map f))

def instSeqOfRelativeMonadOfSeq {j : Type u → Type w} [Seq j] {m : Type u → Type v}
    [RelativeMonad j m] : Seq m where
  seq f x := bindᵣ (j := j) (m := m) f (fun y => mapᵣ (y <*> ·) (x ()))

variable {j : Type u → Type w} {m f : Type u → Type v}

instance [RelativePure Id f] : Pure f where
  pure := @pureᵣ Id f _

instance [RelativeBind Id m] : Bind m where
  bind := @bindᵣ Id m _

instance [RelativeFunctor Id f] : Functor f where
  map := @mapᵣ Id f _
  mapConst := @mapConstᵣ Id f _

instance [RelativeMonad Id m] : Monad m where
  pure := @pureᵣ Id m _
  bind := @bindᵣ Id m _

section Lawful

class LawfulRelativeFunctor (j : Type u → Type w) (f : Type u → Type v)
    [RelativeFunctor j f] where

  map_constᵣ {α β : Type u} : (mapConstᵣ : j α → f β → _) = mapᵣ ∘ (Function.const _)

  id_mapᵣ {α : Type u} (x : f α) : (id : j α → _) <$>ᵣ x = x

  comp_mapᵣ {α β γ : Type u} (g : j α → j β) (h : j β → j γ) (x : f α) :
    (h ∘ g) <$>ᵣ x = h <$>ᵣ g <$>ᵣ x

export LawfulRelativeFunctor (map_constᵣ id_mapᵣ comp_mapᵣ)

attribute [simp] id_mapᵣ

variable {α β γ : Type u}

@[simp] theorem id_mapᵣ' [RelativeFunctor j f] [LawfulRelativeFunctor j f] (x : f α) :
    (fun a : j α => a) <$>ᵣ x = x :=
  id_mapᵣ x

@[simp] theorem RelativeFunctor.map_map [RelativeFunctor j f] [LawfulRelativeFunctor j f]
    (h : j α → j β) (g : j β → j γ) (x : f α) :
      g <$>ᵣ h <$>ᵣ x = (fun a => g (h a)) <$>ᵣ x :=
  (comp_mapᵣ _ _ _).symm

class LawfulRelativeMonad (j : Type u → Type w) (m : Type u → Type v)
    [RelativeMonad j m] extends LawfulRelativeFunctor j m where

  pure_bindᵣ {α β : Type u} (x : j α) (f : j α → m β) :
    (pureᵣ x) >>=ᵣ f = f x

  -- bind_mapᵣ : ∀ {α β : Type u} (f : m (α → β)) (x : m α),
  --   f >>=ᵣ (fun y => mapᵣ (f := m) y x) =
  --   @Seq.seq m (instSeqOfRelativeMonadOfSeq) _ _ f (fun _ => x)

  bind_pure_compᵣ {α β : Type u} (f : j α → j β) (x : m α) :
    x >>=ᵣ (fun y => pureᵣ (f y)) = f <$>ᵣ x

  bind_assocᵣ {α β γ : Type u} (x : m α) (f : j α → m β) (g : j β → m γ) :
    x >>=ᵣ f >>=ᵣ g = x >>=ᵣ fun x ↦ f x >>=ᵣ g

export LawfulRelativeMonad (pure_bindᵣ bind_pure_compᵣ bind_assocᵣ)
attribute [simp] pure_bindᵣ bind_pure_compᵣ bind_assocᵣ

@[simp] theorem bind_pureᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] (x : m α) :
    x >>=ᵣ pureᵣ (j := j) = x := by
  show x >>=ᵣ (fun a => pureᵣ (id a)) = x
  rw [bind_pure_compᵣ, id_mapᵣ]

theorem map_eq_pure_bindᵣ [RelativeMonad j m] [LawfulRelativeMonad j m]
    (f : j α → j β) (x : m α) : f <$>ᵣ x = x >>=ᵣ fun a => pureᵣ (f a) := by
  rw [← bind_pure_compᵣ]

-- theorem seq_eq_bind_mapᵣ [RelativeMonad j m] [LawfulRelativeMonad j m]
--     (f : m (α → β)) (x : m α) : f <*> x = f >>=ᵣ (. <$>ᵣ x) := by
--   rw [← bind_mapᵣ]

theorem bind_congrᵣ [RelativeBind j m] {x : m α} {f g : j α → m β} (h : ∀ a, f a = g a) :
    x >>=ᵣ f = x >>=ᵣ g := by
  simp [funext h]

theorem bind_pure_unitᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] {x : m PUnit} :
    (x >>=ᵣ fun y : j PUnit => pureᵣ y) = x := by
  rw [bind_pure_compᵣ]; exact id_mapᵣ x

theorem map_congrᵣ [RelativeFunctor j m] {x : m α} {f g : j α → j β} (h : ∀ a, f a = g a) :
    (f <$>ᵣ x : m β) = g <$>ᵣ x := by
  simp [funext h]

-- theorem seq_eq_bindᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] (mf : m (α → β)) (x : m α) :
--     mf <*> x = mf >>=ᵣ fun f => f <$>ᵣ x := by
--   rw [← bind_mapᵣ]

-- theorem seqRight_eq_bind [Monad m] [LawfulMonad m] (x : m α) (y : m β) :
--   x *> y = x >>= fun _ => y := by
--   rw [seqRight_eq]
--   simp only [map_eq_pure_bind, const, seq_eq_bind_map, bind_assoc, pure_bind, id_eq, bind_pure]

-- theorem seqLeft_eq_bind [RelativeMonad j m] [LawfulRelativeMonad j m] (x : m α) (y : m β) :
--     x <* y = x >>= fun a => y >>= fun _ => pure a := by
--   rw [seqLeft_eq]
--   simp only [map_eq_pure_bind, seq_eq_bind_map, bind_assoc, pure_bind, const_apply]

@[simp] theorem map_bindᵣ [RelativeMonad j m] [LawfulRelativeMonad j m]
    (f : j β → j γ) (x : m α) (g : j α → m β) :
      f <$>ᵣ (x >>=ᵣ g) = x >>=ᵣ fun a : j α => f <$>ᵣ g a := by
  rw [← bind_pure_compᵣ, bind_assocᵣ]
  simp only [bind_pure_compᵣ]

@[simp] theorem bind_map_leftᵣ [RelativeMonad j m] [LawfulRelativeMonad j m]
    (f : j α → j β) (x : m α) (g : j β → m γ) :
      ((f <$>ᵣ x) >>=ᵣ fun b => g b) = (x >>=ᵣ fun a : j α => g (f a)) := by
  rw [← bind_pure_compᵣ, bind_assocᵣ]
  simp only [pure_bindᵣ]

theorem RelativeFunctor.map_unitᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] {a : m PUnit} :
    (fun y : j PUnit => y) <$>ᵣ a = a := by
  simp

instance [RelativeFunctor Id f] [LawfulRelativeFunctor Id f] : LawfulFunctor f where
  map_const := @map_constᵣ Id f _ _
  id_map := @id_mapᵣ Id f _ _
  comp_map := @comp_mapᵣ Id f _ _

-- instance [RelativeMonad Id m] [LawfulRelativeMonad Id m] : LawfulMonad m where
--   seqLeft_eq x y := by simp [instMonadOfRelativeMonadId, instFunctorOfRelativeFunctorId]; sorry
--   seqRight_eq x y := by
--     simp [instMonadOfRelativeMonadId, instFunctorOfRelativeFunctorId]
--     sorry
--   pure_seq g x := by simp only [instMonadOfRelativeMonadId, pure_bindᵣ]
--   bind_pure_comp f x := by simp [instMonadOfRelativeMonadId, instFunctorOfRelativeFunctorId]
--   bind_map f x := by simp only [instMonadOfRelativeMonadId, instFunctorOfRelativeFunctorId]
--   pure_bind x f := by
--     simp only [instMonadOfRelativeMonadId, instFunctorOfRelativeFunctorId, pure_bindᵣ]
--   bind_assoc x f g := by simp only [instMonadOfRelativeMonadId, bind_assocᵣ, Id]

end Lawful

class MonadIso (m : Type u → Type v) (n : Type u → Type w) where
  toLift : MonadLiftT m n
  invLift : MonadLiftT n m
  monadLift_left_inv {α : Type u} :
    Function.LeftInverse (toLift.monadLift (α := α)) (invLift.monadLift (α := α))
  monadLift_right_inv {α : Type u} :
    Function.RightInverse (toLift.monadLift (α := α)) (invLift.monadLift (α := α))

universe u₁ u₂ v₁ v₂ w₁ w₂

-- structure RelativeMonadHom (M₁ : RelativeMonad C D₁) (M₂ : RelativeMonad C D₂) where
--   J₁₂ : D₁ ⥤ D₂
--   φ : M₂.toFunctor ≅ (M₁.toFunctor ⋙ J₁₂)
--   map : ∀ {X}, J₁₂.obj (M₁.T X) ⟶ M₂.T X
--   map_η : ∀ {X}, J₁₂.map (@M₁.η X) ≫ map = φ.inv.app X ≫ (@M₂.η X)
--   map_μ : ∀ {X Y}, ∀ f : (M₁.toFunctor.obj X) ⟶ M₁.T Y,
--     J₁₂.map (M₁.μ f) ≫ map = map ≫ M₂.μ (φ.hom.app _ ≫ J₁₂.map f ≫ map)

class RelativeMonadMorphism (r₁ : Type u → Type v₁) (m₁ : Type u → Type v₁)
    (r₂ : Type u → Type v₂) (m₂ : Type u → Type v₂)
    [RelativeMonad r₁ m₁] [RelativeMonad r₂ m₂] where
  r₁₂ : Type v₁ → Type v₂
  [instFunctor : Functor r₁₂]
  φ : MonadIso r₂ (r₁₂ ∘ r₁)
  mmapᵣ {α : Type u} : r₁₂ (m₁ α) → m₂ α
  mmapᵣ_pureᵣ {α} :
    mmapᵣ ∘ (Functor.map (f := r₁₂) (@pureᵣ r₁ m₁ _ α)) = pureᵣ ∘ φ.invLift.monadLift
  mmapᵣ_bindᵣ {α β : Type u} (f : r₁ α → m₁ β) :
    mmapᵣ ∘ (Functor.map (f := r₁₂) (bindᵣ · f)) =
      (· >>=ᵣ mmapᵣ ∘ Functor.map (f := r₁₂) f ∘ φ.toLift.monadLift) ∘ mmapᵣ
