/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Order.CompleteLattice.Basic

/-!
# Relational monad algebras

This file introduces a two-monad relational analogue of `MAlgOrdered`:

* `MAlgRelOrdered m₁ m₂ l` with a relational weakest-precondition operator `rwp`.
* Generic relational triple rules (`pure`, `consequence`, `bind`).
* Side-lifting instances for heterogeneous stacks (`StateT`, `OptionT`, `ExceptT`).

Attribution:
- Loom repository: https://github.com/verse-lab/loom
- POPL 2026 paper: *Foundational Multi-Modal Program Verifiers*,
  Vladimir Gladshtein, George Pîrlea, Qiyuan Zhao, Vitaly Kurin, Ilya Sergey.
  DOI: https://doi.org/10.1145/3776719
-/

@[expose] public section

universe u v₁ v₂ v₃ v₄

/-- Ordered relational monad algebra between two monads. -/
class MAlgRelOrdered (m₁ : Type u → Type v₁) (m₂ : Type u → Type v₂) (l : Type u)
    [Monad m₁] [Monad m₂] [Preorder l] where
  /-- Relational weakest precondition. -/
  rwp : {α β : Type u} → m₁ α → m₂ β → (α → β → l) → l
  /-- Pure rule for the relational weakest precondition. -/
  rwp_pure {α β : Type u} (a : α) (b : β) (post : α → β → l) :
      rwp (pure a) (pure b) post = post a b
  /-- Monotonicity in the relational postcondition. -/
  rwp_mono {α β : Type u} {x : m₁ α} {y : m₂ β} {post post' : α → β → l}
      (hpost : ∀ a b, post a b ≤ post' a b) :
      rwp x y post ≤ rwp x y post'
  /-- Sequential composition rule for relational WPs. -/
  rwp_bind_le {α β γ δ : Type u}
      (x : m₁ α) (y : m₂ β) (f : α → m₁ γ) (g : β → m₂ δ) (post : γ → δ → l) :
      rwp x y (fun a b => rwp (f a) (g b) post) ≤ rwp (x >>= f) (y >>= g) post

namespace MAlgRelOrdered

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
variable [Monad m₁] [Monad m₂] [Preorder l] [MAlgRelOrdered m₁ m₂ l]
variable {α β γ δ : Type u}

/-- Relational weakest precondition induced by `MAlgRelOrdered`. -/
abbrev RelWP (x : m₁ α) (y : m₂ β) (post : α → β → l) : l :=
  MAlgRelOrdered.rwp x y post

/-- Relational Hoare-style triple. -/
def Triple (pre : l) (x : m₁ α) (y : m₂ β) (post : α → β → l) : Prop :=
  pre ≤ RelWP x y post

@[simp]
theorem relWP_pure [LawfulMonad m₁] [LawfulMonad m₂] (a : α) (b : β) (post : α → β → l) :
    RelWP (pure a : m₁ α) (pure b : m₂ β) post = post a b :=
  MAlgRelOrdered.rwp_pure a b post

theorem relWP_mono (x : m₁ α) (y : m₂ β) {post post' : α → β → l}
    (hpost : ∀ a b, post a b ≤ post' a b) :
    RelWP x y post ≤ RelWP x y post' :=
  MAlgRelOrdered.rwp_mono hpost

theorem relWP_bind_le (x : m₁ α) (y : m₂ β) (f : α → m₁ γ) (g : β → m₂ δ)
    (post : γ → δ → l) :
    RelWP x y (fun a b => RelWP (f a) (g b) post) ≤ RelWP (x >>= f) (y >>= g) post :=
  MAlgRelOrdered.rwp_bind_le x y f g post

theorem triple_conseq {pre pre' : l} {x : m₁ α} {y : m₂ β} {post post' : α → β → l}
    (hpre : pre' ≤ pre) (hpost : ∀ a b, post a b ≤ post' a b) :
    Triple pre x y post → Triple pre' x y post' := by
  intro hxy
  exact le_trans hpre (le_trans hxy (relWP_mono x y hpost))

theorem triple_pure [LawfulMonad m₁] [LawfulMonad m₂]
    {pre : l} {a : α} {b : β} {post : α → β → l}
    (hpre : pre ≤ post a b) :
    Triple pre (pure a : m₁ α) (pure b : m₂ β) post := by
  simpa [Triple, relWP_pure] using hpre

theorem triple_bind {pre : l} {x : m₁ α} {y : m₂ β}
    {f : α → m₁ γ} {g : β → m₂ δ}
    {cut : α → β → l} {post : γ → δ → l}
    (hxy : Triple pre x y cut)
    (hfg : ∀ a b, Triple (cut a b) (f a) (g b) post) :
    Triple pre (x >>= f) (y >>= g) post := by
  have hcut : pre ≤ RelWP x y (fun a b => RelWP (f a) (g b) post) := by
    exact le_trans hxy (relWP_mono x y hfg)
  exact le_trans hcut (relWP_bind_le x y f g post)

/-- Mapping on the left program is monotone for relational WP. -/
theorem relWP_map_left [LawfulMonad m₁] [LawfulMonad m₂]
    (f : α → γ) (x : m₁ α) (y : m₂ β) (post : γ → β → l) :
    RelWP x y (fun a b => post (f a) b) ≤ RelWP (f <$> x) y post := by
  have hbind := relWP_bind_le x y (fun a => pure (f a)) (fun b => pure b) post
  simpa [Functor.map, bind_pure_comp, relWP_pure] using hbind

/-- Mapping on the right program is monotone for relational WP. -/
theorem relWP_map_right [LawfulMonad m₁] [LawfulMonad m₂]
    (g : β → δ) (x : m₁ α) (y : m₂ β) (post : α → δ → l) :
    RelWP x y (fun a b => post a (g b)) ≤ RelWP x (g <$> y) post := by
  have hbind := relWP_bind_le x y (fun a => pure a) (fun b => pure (g b)) post
  simpa [Functor.map, bind_pure_comp, relWP_pure] using hbind

end MAlgRelOrdered

namespace MAlgRelOrdered

section Instances

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
variable [Monad m₁] [Monad m₂] [LawfulMonad m₁] [LawfulMonad m₂] [Preorder l]
variable [MAlgRelOrdered m₁ m₂ l]

/-- Left `StateT` lift for heterogeneous relational algebras. -/
noncomputable instance instStateTLeft (σ : Type u) :
    MAlgRelOrdered (StateT σ m₁) m₂ (σ → l) where
  rwp x y post := fun s =>
    MAlgRelOrdered.rwp (x.run s) y (fun xs b => post xs.1 b xs.2)
  rwp_pure a b post := by
    funext s
    simp [StateT.run_pure]
  rwp_mono hpost := by
    intro s
    exact MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l) (fun xs b => hpost xs.1 b xs.2)
  rwp_bind_le x y f g post := by
    intro s
    simpa [StateT.run_bind] using
      (MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
        (x := x.run s) (y := y)
        (f := fun xs => (f xs.1).run xs.2) (g := g)
        (post := fun zs d => post zs.1 d zs.2))

/-- Right `StateT` lift for heterogeneous relational algebras. -/
noncomputable instance instStateTRight (σ : Type u) :
    MAlgRelOrdered m₁ (StateT σ m₂) (σ → l) where
  rwp x y post := fun s =>
    MAlgRelOrdered.rwp x (y.run s) (fun a ys => post a ys.1 ys.2)
  rwp_pure a b post := by
    funext s
    simp [StateT.run_pure]
  rwp_mono hpost := by
    intro s
    exact MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l) (fun a ys => hpost a ys.1 ys.2)
  rwp_bind_le x y f g post := by
    intro s
    simpa [StateT.run_bind] using
      (MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
        (x := x) (y := y.run s)
        (f := f) (g := fun ys => (g ys.1).run ys.2)
        (post := fun c td => post c td.1 td.2))

/-- Two-sided `StateT` instance: both sides carry their own state.
The postcondition takes both output values and both final states. -/
noncomputable instance instStateTBoth (σ₁ σ₂ : Type u) :
    MAlgRelOrdered (StateT σ₁ m₁) (StateT σ₂ m₂) (σ₁ → σ₂ → l) where
  rwp x y post := fun s₁ s₂ =>
    MAlgRelOrdered.rwp (x.run s₁) (y.run s₂)
      (fun p₁ p₂ => post p₁.1 p₂.1 p₁.2 p₂.2)
  rwp_pure a b post := by
    funext s₁ s₂
    simp [StateT.run_pure]
  rwp_mono hpost := by
    intro s₁ s₂
    exact MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l)
      (fun p₁ p₂ => hpost p₁.1 p₂.1 p₁.2 p₂.2)
  rwp_bind_le x y f g post := by
    intro s₁ s₂
    simpa [StateT.run_bind] using
      (MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
        (x := x.run s₁) (y := y.run s₂)
        (f := fun p₁ => (f p₁.1).run p₁.2) (g := fun p₂ => (g p₂.1).run p₂.2)
        (post := fun p₁ p₂ => post p₁.1 p₂.1 p₁.2 p₂.2))

end Instances

section FailureInstances

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
variable [Monad m₁] [Monad m₂] [LawfulMonad m₁] [LawfulMonad m₂] [Preorder l] [OrderBot l]
variable [MAlgRelOrdered m₁ m₂ l]

/-- Right `OptionT` lift (interpreting `none` as `⊥`). -/
noncomputable instance instOptionTRight :
    MAlgRelOrdered m₁ (OptionT m₂) l where
  rwp x y post :=
    MAlgRelOrdered.rwp x y.run (fun a ob =>
      match ob with
      | none => ⊥
      | some b => post a b)
  rwp_pure a b post := by
    simp
  rwp_mono hpost := by
    exact MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l) (fun a ob => by
      cases ob with
      | none => exact le_rfl
      | some b => simpa using hpost a b)
  rwp_bind_le {α β γ δ} x y f g post := by
    let collapse : γ → Option δ → l := fun c od =>
      match od with
      | none => ⊥
      | some d => post c d
    let gRun : Option β → m₂ (Option δ) := fun ob =>
      Option.elim ob (pure none) (fun b => (g b).run)
    have hmono :
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) x y.run
          (fun a ob =>
            match ob with
            | none => ⊥
            | some b => MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) (f a) (g b).run collapse)
        ≤
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) x y.run
          (fun a ob => MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) (f a) (gRun ob) collapse) := by
      apply MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l)
      intro a ob
      cases ob with
      | none =>
          simp [gRun, collapse]
      | some b =>
          simp [gRun]
    exact le_trans hmono <|
      by
        simpa [OptionT.run_bind, Option.elimM, gRun, collapse] using
          (MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
            x y.run f gRun collapse)

/-- Left `OptionT` lift (interpreting `none` as `⊥`). -/
noncomputable instance instOptionTLeft :
    MAlgRelOrdered (OptionT m₁) m₂ l where
  rwp x y post :=
    MAlgRelOrdered.rwp x.run y (fun oa b =>
      match oa with
      | none => ⊥
      | some a => post a b)
  rwp_pure a b post := by
    simp
  rwp_mono hpost := by
    exact MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l) (fun oa b => by
      cases oa with
      | none => exact le_rfl
      | some a => simpa using hpost a b)
  rwp_bind_le {α β γ δ} x y f g post := by
    let collapse : Option γ → δ → l := fun oa b =>
      match oa with
      | none => ⊥
      | some a => post a b
    let fRun : Option α → m₁ (Option γ) := fun oa =>
      Option.elim oa (pure none) (fun a => (f a).run)
    have hmono :
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) x.run y
          (fun oa b =>
            match oa with
            | none => ⊥
            | some a => MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) (f a).run (g b) collapse)
        ≤
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) x.run y
          (fun oa b => MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) (fRun oa) (g b) collapse) := by
      apply MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l)
      intro oa b
      cases oa with
      | none =>
          simp [fRun, collapse]
      | some a =>
          simp [fRun]
    have hmono' :
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) x.run y
          (fun oa b =>
            match oa with
            | none => ⊥
            | some a => MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) (f a).run (g b) collapse)
        ≤
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) x.run y
          (fun oa b => MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) (fRun oa) (g b) collapse) := by
      simpa [collapse] using hmono
    exact le_trans hmono' <|
      by
        simpa [OptionT.run_bind, Option.elimM, fRun, collapse] using
          (MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
            x.run y fRun g collapse)

/-- Right `ExceptT` lift (interpreting exceptions as `⊥`). -/
noncomputable instance instExceptTRight (ε : Type u) :
    MAlgRelOrdered m₁ (ExceptT ε m₂) l where
  rwp x y post :=
    MAlgRelOrdered.rwp x y.run (fun a eb =>
      match eb with
      | Except.error _ => ⊥
      | Except.ok b => post a b)
  rwp_pure a b post := by
    simp
  rwp_mono hpost := by
    exact MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l) (fun a eb => by
      cases eb with
      | error e => exact le_rfl
      | ok b => simpa using hpost a b)
  rwp_bind_le {α β γ δ} x y f g post := by
    let collapse : γ → Except ε δ → l := fun c ed =>
      match ed with
      | Except.error _ => ⊥
      | Except.ok d => post c d
    let gRun : Except ε β → m₂ (Except ε δ) := fun eb =>
      match eb with
      | Except.ok b => (g b).run
      | Except.error e => pure (Except.error e)
    have hmono :
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) x y.run
          (fun a eb =>
            match eb with
            | Except.error _ => ⊥
            | Except.ok b =>
                MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) (f a) (g b).run collapse)
        ≤
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) x y.run
          (fun a eb => MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) (f a) (gRun eb) collapse) := by
      apply MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l)
      intro a eb
      cases eb with
      | error e =>
          simp [gRun, collapse]
      | ok b =>
          simp [gRun]
    exact le_trans hmono <|
      by
        simpa [ExceptT.run_bind, gRun, collapse] using
          (MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
            x y.run f gRun collapse)

/-- Left `ExceptT` lift (interpreting exceptions as `⊥`). -/
noncomputable instance instExceptTLeft (ε : Type u) :
    MAlgRelOrdered (ExceptT ε m₁) m₂ l where
  rwp x y post :=
    MAlgRelOrdered.rwp x.run y (fun ea b =>
      match ea with
      | Except.error _ => ⊥
      | Except.ok a => post a b)
  rwp_pure a b post := by
    simp
  rwp_mono hpost := by
    exact MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l) (fun ea b => by
      cases ea with
      | error e => exact le_rfl
      | ok a => simpa using hpost a b)
  rwp_bind_le {α β γ δ} x y f g post := by
    let collapse : Except ε γ → δ → l := fun ec d =>
      match ec with
      | Except.error _ => ⊥
      | Except.ok c => post c d
    let fRun : Except ε α → m₁ (Except ε γ) := fun ea =>
      match ea with
      | Except.ok a => (f a).run
      | Except.error e => pure (Except.error e)
    have hmono :
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) x.run y
          (fun ea b =>
            match ea with
            | Except.error _ => ⊥
            | Except.ok a =>
                MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) (f a).run (g b) collapse)
        ≤
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) x.run y
          (fun ea b => MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (l := l) (fRun ea) (g b) collapse) := by
      apply MAlgRelOrdered.rwp_mono (m₁ := m₁) (m₂ := m₂) (l := l)
      intro ea b
      cases ea with
      | error e =>
          simp [fRun, collapse]
      | ok a =>
          simp [fRun]
    exact le_trans hmono <|
      by
        simpa [ExceptT.run_bind, fRun, collapse] using
          (MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
            x.run y fRun g collapse)

end FailureInstances

end MAlgRelOrdered
