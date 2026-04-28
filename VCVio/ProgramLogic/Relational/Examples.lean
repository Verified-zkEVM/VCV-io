/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Relational

/-!
# Relational program-logic examples

This file gives small compositionality examples for:
- heterogeneous transformer stacks (`StateT` vs `OptionT`/`ExceptT`), and
- the `OracleComp` relational API (`RelTriple`).
-/

universe u v₁ v₂

section MixedStacks

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
variable [Monad m₁] [Monad m₂] [LawfulMonad m₁] [LawfulMonad m₂]
variable [Preorder l] [OrderBot l] [MAlgRelOrdered m₁ m₂ l]

variable {σ : Type u} {ε : Type u}
variable {α β γ δ : Type u}

example
    {pre : σ → l}
    {x : StateT σ m₁ α} {y : OptionT m₂ β}
    {cut : α → β → σ → l}
    {f : α → StateT σ m₁ γ} {g : β → OptionT m₂ δ}
    {post : γ → δ → σ → l}
    (hxy : MAlgRelOrdered.Triple pre x y cut)
    (hfg : ∀ a b, MAlgRelOrdered.Triple (cut a b) (f a) (g b) post) :
    MAlgRelOrdered.Triple pre (x >>= f) (y >>= g) post :=
  MAlgRelOrdered.triple_bind hxy hfg

example
    {pre : σ → l}
    {x : StateT σ m₁ α} {y : ExceptT ε m₂ β}
    {cut : α → β → σ → l}
    {f : α → StateT σ m₁ γ} {g : β → ExceptT ε m₂ δ}
    {post : γ → δ → σ → l}
    (hxy : MAlgRelOrdered.Triple pre x y cut)
    (hfg : ∀ a b, MAlgRelOrdered.Triple (cut a b) (f a) (g b) post) :
    MAlgRelOrdered.Triple pre (x >>= f) (y >>= g) post :=
  MAlgRelOrdered.triple_bind hxy hfg

end MixedStacks

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β γ δ : Type}

/-! ### Term-mode examples (direct lemma application) -/

example {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {R : RelPost α β} {S : RelPost γ δ}
    (hxy : RelTriple oa ob R)
    (hfg : ∀ a b, R a b → RelTriple (fa a) (fb b) S) :
    RelTriple (oa >>= fa) (ob >>= fb) S :=
  relTriple_bind hxy hfg

example (oa : OracleComp spec₁ α) :
    RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa oa (EqRel α) :=
  relTriple_refl (spec₁ := spec₁) oa

example {a : α} {b : β} {R : RelPost α β} (h : R a b) :
    RelTriple (spec₁ := spec₁) (spec₂ := spec₂)
      (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) R :=
  relTriple_pure_pure h

/-! ### Tactic-mode examples (using `rvcstep`) -/

example {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {R : RelPost α β} {S : RelPost γ δ}
    (hxy : RelTriple oa ob R)
    (hfg : ∀ a b, R a b → RelTriple (fa a) (fb b) S) :
    RelTriple (oa >>= fa) (ob >>= fb) S := by
  rvcstep using R

example (oa : OracleComp spec₁ α) :
    RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa oa (EqRel α) := by
  rvcstep

/-! ### Trivial postcondition discharge (via product coupling)

The product coupling exists for any pair of `OracleComp` computations, so any goal whose
postcondition is structurally `fun _ _ => True` (or reduces to one through bind/map normalization)
is closed by the leaf closer without intermediate planning. -/

example (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) :
    RelTriple oa ob (fun _ _ => True) := by
  rvcstep

example (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (fa : α → OracleComp spec₁ γ) (fb : β → OracleComp spec₂ δ) :
    RelTriple (oa >>= fa) (ob >>= fb) (fun _ _ => True) := by
  rvcstep

example (sp : ℕ) (msg₀ msg₁ : BitVec sp) :
    RelTriple
      (do let key ← $ᵗ BitVec sp; pure (key ^^^ msg₀, ()))
      (do let key ← $ᵗ BitVec sp; pure (key ^^^ msg₁, ()))
      (fun z₁ z₂ => z₁.2 = z₂.2) := by
  refine relTriple_bind_uniformSample_bij (f := fun key : BitVec sp => key) ?_ ?_
  · intro key
    exact relTriple_pure_pure rfl
  · exact Function.bijective_id

end OracleComp.ProgramLogic.Relational
