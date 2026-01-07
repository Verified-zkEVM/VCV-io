/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Control.Monad.Basic
import Mathlib.Control.Monad.Cont
import Mathlib.CategoryTheory.Monad.Basic
import ToMathlib.Control.Monad.Ordered
import ToMathlib.Control.Monad.Free

/-!
# Dijkstra monad

This file aims to formalize the content of the paper
[Dijkstra monads for all](https://dl.acm.org/doi/pdf/10.1145/3341708).

-/

universe u v w z

open scoped OrderedMonad

class DijkstraMonad (w : Type u → Type v) (d : {α : Type u} → w α → Type z) [Monad w] where
  -- d {α : Type u} : w α → Type z
  dPure {α : Type u} : (x : α) → d (pure x)
  dBind {α β : Type u} {wa : w α} {wb : α → w β} : d wa → ((a : α) → d (wb a)) → d (wa >>= wb)

export DijkstraMonad (dPure dBind)

infixl:55  " >>=ᵈ " => DijkstraMonad.dBind

def DijkstraMonad.dMap {w d} [Monad w] [DijkstraMonad w d] {α β} {a : w α} (f : α → β) :
    d a → d (a >>= fun b => pure (f b)) := fun x => x >>=ᵈ (fun a => dPure (f a))

export DijkstraMonad (dMap)

infixr:100 " <$>ᵈ " => DijkstraMonad.dMap

class LawfulDijkstraMonad (w : Type u → Type v) (d : {α : Type u} → w α → Type z) [Monad w]
    [LawfulMonad w] [DijkstraMonad w d] where
  dPure_dBind {α β} {f : α → w β} (x : α) (g : (a : α) → d (f a)) :
    (pure_bind x f) ▸ (dPure x >>=ᵈ g) = g x
  dBind_dPure {α} {a : w α} (x : d a) :
    (bind_pure a) ▸ (x >>=ᵈ dPure) = x
  dBind_assoc {α β γ} {a} {f : α → w β} {g : β → w γ} (x : d a)
    (f' : (a : α) → d (f a)) (g' : (b : β) → d (g b)) :
      (bind_assoc a f g) ▸ ((x >>=ᵈ f') >>=ᵈ g') = x >>=ᵈ (fun a => f' a >>=ᵈ g')

export LawfulDijkstraMonad (dPure_dBind dBind_dPure dBind_assoc)

attribute [simp] dPure_dBind dBind_dPure dBind_assoc

class OrderedDijkstraMonad (w : Type u → Type v) (d : {α : Type u} → w α → Type z)
    [OrderedMonad w] extends DijkstraMonad w d where
  dWeaken {α} {wa wa' : w α} : d wa → (wa ≤ₘ wa') → d wa'
  dWeaken_refl {α} {wa : w α} (x : d wa) : dWeaken x (le_refl _) = x
  dWeaken_trans {α} {wa wa' wa'' : w α} (x : d wa) (h1 : wa ≤ₘ wa') (h2 : wa' ≤ₘ wa'') :
    dWeaken (dWeaken x h1) h2 = dWeaken x (le_trans h1 h2)
  dWeaken_dBind {α β} {wa wa' : w α} {f f' : α → w β} (x : d wa) (g : (a : α) → d (f a))
    (ha : wa ≤ₘ wa') (hf : ∀ a, f a ≤ₘ f' a) :
      (dWeaken x ha) >>=ᵈ (fun a => dWeaken (g a) (hf a)) = dWeaken (x >>=ᵈ g) (bind_mono ha hf)

export OrderedDijkstraMonad (dWeaken dWeaken_refl dWeaken_trans dWeaken_dBind)

attribute [simp] dWeaken_refl dWeaken_trans dWeaken_dBind

namespace DijkstraMonad

def dDite {w d} [Monad w] [DijkstraMonad w d] {α} (c : Prop) [h : Decidable c] {t : c → w α}
    {e : ¬c → w α} : ((c' : c) → d (t c')) → ((c' : ¬c) → d (e c')) → d (dite c t e) :=
  fun dt de => Decidable.casesOn h (fun h => de h) (fun h => dt h)

def dIte {w d} [Monad w] [DijkstraMonad w d] {α} (c : Prop) [Decidable c] {t e : w α} :
    d t → d e → d (ite c t e) :=
  fun dt de => dDite c (fun _ => dt) (fun _ => de)

end DijkstraMonad

class DijkstraMonadMorphism (w₁ : Type u → Type v) (w₂ : Type u → Type w)
    (d₁ : {α : Type u} → w₁ α → Type z) (d₂ : {α : Type u} → w₂ α → Type z)
    [Monad w₁] [Monad w₂] [MonadLiftT w₁ w₂] [DijkstraMonad w₁ d₁] [DijkstraMonad w₂ d₂] where
  dMorphism {α : Type u} {a : w₁ α} : d₁ a → d₂ (monadLift a)

export DijkstraMonadMorphism (dMorphism)

class LawfulDijkstraMonadLift (w₁ : Type u → Type v) (w₂ : Type u → Type w)
    (d₁ : {α : Type u} → w₁ α → Type z) (d₂ : {α : Type u} → w₂ α → Type z)
    [Monad w₁] [Monad w₂] [MonadLiftT w₁ w₂] [DijkstraMonad w₁ d₁] [DijkstraMonad w₂ d₂]
    [inst : DijkstraMonadMorphism w₁ w₂ d₁ d₂]
    [LawfulMonad w₁] [LawfulMonad w₂] [LawfulMonadLiftT w₁ w₂] where
  dMorphism_dPure {α : Type u} (a : α) :
    (monadLift_pure (m := w₁) (n := w₂) a) ▸ (dMorphism (dPure a : d₁ _)) = (dPure a : d₂ _)
  dMorphism_dBind {α β : Type u} {a : w₁ α} {f : α → w₁ β} (x : d₁ a) (g : (a : α) → d₁ (f a)) :
    (monadLift_bind (m := w₁) (n := w₂) a f) ▸ (dMorphism x >>=ᵈ (fun a => dMorphism (g a))) =
      inst.dMorphism (x >>=ᵈ g)

export LawfulDijkstraMonadLift (dMorphism_dPure dMorphism_dBind)

attribute [simp] dMorphism_dPure dMorphism_dBind

namespace DijkstraMonad

/-! ## Constructing Dijkstra monads from monad relations and vice versa -/

variable {m : Type u → Type v} {n : Type u → Type w}

instance instOfMonadRelation {m n} [Monad m] [Monad n] [MonadRelation m n]
    [LawfulMonadRelation m n] : DijkstraMonad n (fun na => { ma : m _ // monadRel ma na}) where
  dPure x := ⟨pure x, monadRel_pure x⟩
  dBind x f := ⟨x.1 >>= (fun a => (f a).1), monadRel_bind x.2 (fun a => (f a).2)⟩

open MonadRelation in
instance instOfMonadMorphism {m n} [Monad m] [Monad n] [h : MonadLiftT m n]
    [h' : LawfulMonadLiftT m n] :
      DijkstraMonad n (fun na => { ma : m _ // monadLift ma = na }) :=
  @instOfMonadRelation m n _ _ (@instOfMonadLiftT m n h) (@instOfLawfulMonadLiftT m n _ _ h h')

-- instance [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [MonadRelation m n]
--     [LawfulMonadRelation m n] :
--     LawfulDijkstraMonad n (fun na => { ma : m _ // monadRel ma na}) where
--   dPure_dBind x f := by sorry
--   dBind_dPure x := by sorry
--   dBind_assoc x f g := by sorry

/-- A Dijkstra monad `d` on a monad `w` can be seen as a monad on the dependent pair `(w, d)`. -/
instance instMonadSigma {w d} [Monad w] [DijkstraMonad w d] :
    Monad (fun α => (w : w α) × d w) where
  pure x := ⟨pure x, dPure x⟩
  bind x f := ⟨x.1 >>= (fun a => (f a).1), x.2 >>=ᵈ (fun a => (f a).2)⟩

-- /-- A lawful Dijkstra monad `d` on a lawful monad `w` can be seen
--   as a lawful monad on the dependent pair `(w, d)`. -/
-- instance {w d} [Monad w] [DijkstraMonad w d] [h : LawfulMonad w] [LawfulDijkstraMonad w d] :
--     LawfulMonad (fun α => (w : w α) × d w) :=
--   LawfulMonad.mk' _
--     (by
--       intro α ⟨x, y⟩; simp [instMonadSigma]; sorry)
--       -- constructor
--       -- · show x >>= (fun a => pure a) = x; simp only [bind_pure]
--       -- · rw (occs := .pos [2]) [← dBind_dPure y]
--       --   symm; exact eqRec_heq (bind_pure x) (y >>=ᵈ dPure))
--     (by
--       intro α β x f; simp [instMonadSigma]; congr
--       · simp only [pure_bind]
--       · rw [← dPure_dBind x (fun a => (f a).2)]
--         exact HEq.symm (eqRec_heq _ _))
--     (fun x f g => by
--       simp [instMonadSigma]
--       rw [← dBind_assoc x.2 _ _]
--       exact HEq.symm (eqRec_heq _ _))

instance {w d} [Monad w] [DijkstraMonad w d] : MonadLiftT (fun α => (w : w α) × d w) w where
  monadLift x := x.1

open MonadRelation in
instance {w d} [Monad w] [DijkstraMonad w d] : MonadRelation (fun α => (w : w α) × d w) w :=
  instOfMonadLiftT

-- TODO: state that this forms an adjunction

/-! The ordered setting -/

-- def quotientDijkstraMonadOfOrderedMonadRelation {m n} [Monad m] [OrderedMonad n]
--     [MonadRelation m n] [LawfulMonad m] [LawfulMonad n] [MonadRelation.IsUpperClosed m n] :
--     {α : Type u} → n α → Type _ := sorry

-- instance [Monad m] [OrderedMonad n] [MonadRelation m n]
--     [LawfulMonad m] [LawfulMonad n] [LawfulMonadRelation m n] :
--     OrderedDijkstraMonad n (fun na => { ma : m _ // monadRel ma na}) where
--   dWeaken x h := ⟨x.1, by simp_all [monadRel]; sorry⟩
--   dWeaken_refl x := by simp
--   dWeaken_trans x h1 h2 := by simp
--   dWeaken_dBind x g ha hf := by simp; sorry

end DijkstraMonad

/-! ## The Free Dijkstra Monad -/

-- /-- The free monad on a functor `f` is the type freely generated by values of type `f α`
-- and the operations `pure` and `bind`. Implemented directly rather than as a quotient.
-- Slightly different than constructions of free monads in Haskell because of universe issues. -/
-- inductive FreeMonad (f : Type v → Type w) (α : Type u) : Type (max u (v + 1) w)
--   | protected pure (x : α) : FreeMonad f α
--   | roll {β : Type v} (x : f β) (r : β → FreeMonad f α) : FreeMonad f α

-- TODO: double-check definition
inductive FreeDijkstra (m : Type u → Type v) [Monad m] : {α : Type u} → m α → Type _ where
  | protected pure {α} (x : α) : FreeDijkstra m (pure x)
  | roll {α β} (x : m α) {f : α → m β} (r : α → FreeDijkstra m (x >>= f)) : FreeDijkstra m (x >>= f)

-- instance {m} [Monad m] : DijkstraMonad (FreeMonad m) (FreeDijkstra (FreeMonad m)) where
--   dPure x := FreeDijkstra.pure x
  -- dBind x f := FreeDijkstra.roll x (fun a => f a)

namespace FreeD



end FreeD
