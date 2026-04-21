/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Order.CompleteLattice.Basic

/-!
# Monad algebras

This file contains two layers:

1. A minimal `MonadAlgebra` interface used by existing `ToMathlib` files.
2. A Loom-style ordered monad algebra interface `MAlgOrdered` with `wp`/`triple`.

Public credit / attribution:
- Loom project: https://github.com/verse-lab/loom
- POPL 2026 paper: "Foundational Multi-Modal Program Verifiers", Vladimir Gladshtein, George
  Pîrlea, Qiyuan Zhao, Vitaly Kurin, and Ilya Sergey.
  DOI: https://doi.org/10.1145/3776719

The ordered monad algebra perspective (`MAlgOrdered`, `wp`, `triple`) in this file is adapted from
Loom's `MonadAlgebras` development.
-/

@[expose] public section

universe u v

class MonadAlgebra (m : Type u → Type v) where
  monadAlg {α : Type u} : m α → α

export MonadAlgebra (monadAlg)

class LawfulMonadAlgebra (m : Type u → Type v) [Monad m] [MonadAlgebra m] where
  monadAlg_pure {α : Type u} (a : α) : monadAlg (pure a : m α) = a
  monadAlg_bind {α β : Type u} (ma : m α) (mb : α → m β) :
    monadAlg (mb (monadAlg ma)) = monadAlg (ma >>= mb)

export LawfulMonadAlgebra (monadAlg_pure monadAlg_bind)

attribute [simp] monadAlg_pure monadAlg_bind

/-! ## Loom-style ordered monad algebras -/

universe w

/-- Ordered monad algebra interface used for quantitative WP/triple reasoning. -/
class MAlgOrdered (m : Type u → Type v) (l : Type u) [Monad m] [CompleteLattice l] where
  μ : m l → l
  μ_pure : ∀ x : l, μ (pure x) = x
  μ_bind_mono {α : Type u} :
    ∀ (f g : α → m l), (∀ a, μ (f a) ≤ μ (g a)) →
      ∀ x : m α, μ (x >>= f) ≤ μ (x >>= g)

namespace MAlgOrdered

variable {m : Type u → Type v} {l : Type u} [Monad m] [CompleteLattice l] [MAlgOrdered m l]
variable {α β : Type u}

/-- Weakest precondition induced by `μ`. -/
def wp (x : m α) (post : α → l) : l :=
  MAlgOrdered.μ (x >>= fun a => pure (post a))

/-- Hoare-style triple induced by `wp`. -/
def Triple (pre : l) (x : m α) (post : α → l) : Prop :=
  pre ≤ wp x post

theorem μ_bind (x : m α) (f g : α → m l) (h : ∀ a, MAlgOrdered.μ (f a) = MAlgOrdered.μ (g a)) :
    MAlgOrdered.μ (x >>= f) = MAlgOrdered.μ (x >>= g) := by
  apply le_antisymm
  · exact MAlgOrdered.μ_bind_mono f g (fun a => by simp [h a]) x
  · exact MAlgOrdered.μ_bind_mono g f (fun a => by simp [h a]) x

@[simp]
theorem wp_pure [LawfulMonad m] (x : α) (post : α → l) :
    wp (pure x : m α) post = post x := by
  unfold wp
  simp [MAlgOrdered.μ_pure]

theorem wp_bind [LawfulMonad m] (x : m α) (f : α → m β) (post : β → l) :
    wp (x >>= f) post = wp x (fun a => wp (f a) post) := by
  unfold wp
  rw [bind_assoc]
  exact μ_bind
    x
    (fun a => f a >>= fun b => pure (post b))
    (fun a => pure (MAlgOrdered.μ (f a >>= fun b => pure (post b))))
    (fun a => by
      simpa using
        (MAlgOrdered.μ_pure
          (m := m) (l := l) (x := MAlgOrdered.μ (f a >>= fun b => pure (post b)))).symm)

theorem wp_mono (x : m α) {post post' : α → l} (h : ∀ a, post a ≤ post' a) :
    wp x post ≤ wp x post' := by
  unfold wp
  exact MAlgOrdered.μ_bind_mono
    (f := fun a => pure (post a))
    (g := fun a => pure (post' a))
    (fun a => by simpa [MAlgOrdered.μ_pure] using h a)
    x

/-- `wp` is functorial in the program return value. -/
theorem wp_map [LawfulMonad m] (f : α → β) (x : m α) (post : β → l) :
    wp (f <$> x) post = wp x (fun a => post (f a)) := by
  simpa [Functor.map, bind_pure_comp] using
    (wp_bind (m := m) (l := l) x (fun a => pure (f a)) post)

/-- `wp` preserves applicative sequencing. -/
theorem wp_seq [LawfulMonad m] (f : m (α → β)) (x : m α) (post : β → l) :
    wp (f <*> x) post = wp f (fun g => wp x (fun a => post (g a))) := by
  rw [seq_eq_bind_map, wp_bind]
  congr
  funext g
  simp [wp_map]

theorem triple_conseq {pre pre' : l} {x : m α} {post post' : α → l}
    (hpre : pre' ≤ pre) (hpost : ∀ a, post a ≤ post' a) :
    Triple pre x post → Triple pre' x post' := by
  intro h
  exact le_trans hpre (le_trans h (wp_mono x hpost))

/-- Rule for `pure` computations in `Triple`. -/
theorem triple_pure [LawfulMonad m] {pre : l} {x : α} {post : α → l}
    (h : pre ≤ post x) :
    Triple pre (pure x : m α) post := by
  simpa [Triple, wp_pure] using h

/-- Rule for `map` in `Triple`. -/
theorem triple_map [LawfulMonad m] {pre : l} {x : m α} {f : α → β} {post : β → l}
    (h : Triple pre x (fun a => post (f a))) :
    Triple pre (f <$> x) post := by
  simpa [Triple, wp_map] using h

/-- Monotonicity of `Triple` in its postcondition. -/
theorem triple_mono_post {pre : l} {x : m α} {post post' : α → l}
    (h : Triple pre x post) (hpost : ∀ a, post a ≤ post' a) :
    Triple pre x post' :=
  triple_conseq (m := m) (l := l) (le_rfl : pre ≤ pre) hpost h

/-- Monotonicity of `Triple` in its precondition. -/
theorem triple_mono_pre {pre pre' : l} {x : m α} {post : α → l}
    (h : Triple pre x post) (hpre : pre' ≤ pre) :
    Triple pre' x post :=
  triple_conseq (m := m) (l := l) hpre (fun _ => le_rfl) h

theorem triple_bind [LawfulMonad m] {pre : l} {x : m α} {cut : α → l}
    {f : α → m β} {post : β → l}
    (hx : Triple pre x cut) (hf : ∀ a, Triple (cut a) (f a) post) :
    Triple pre (x >>= f) post := by
  unfold Triple at *
  rw [wp_bind]
  exact le_trans hx (wp_mono x hf)

end MAlgOrdered

/-! ## Transformer lifting instances -/

namespace MAlgOrdered

variable {m : Type u → Type v} {l : Type u}
variable [Monad m] [LawfulMonad m] [CompleteLattice l] [MAlgOrdered m l]

/-- Lift an ordered monad algebra through `StateT`. -/
@[implicit_reducible] noncomputable def instStateT (σ : Type u) :
    MAlgOrdered (StateT σ m) (σ → l) where
  μ x := fun s => MAlgOrdered.μ (x.run s >>= fun y => pure (y.1 y.2))
  μ_pure x := by
    funext s
    simp [StateT.run_pure, MAlgOrdered.μ_pure]
  μ_bind_mono f g hfg x := by
    intro s
    simp only [StateT.run_bind, bind_assoc]
    exact MAlgOrdered.μ_bind_mono
      (f := fun y => (f y.1).run y.2 >>= fun z => pure (z.1 z.2))
      (g := fun y => (g y.1).run y.2 >>= fun z => pure (z.1 z.2))
      (fun y => (hfg y.1) y.2)
      (x.run s)

attribute [instance] instStateT

/-- Lift an ordered monad algebra through `ReaderT`. -/
@[implicit_reducible] noncomputable def instReaderT (ρ : Type u) :
    MAlgOrdered (ReaderT ρ m) (ρ → l) where
  μ x := fun r => MAlgOrdered.μ (x.run r >>= fun q => pure (q r))
  μ_pure x := by
    funext r
    simp [ReaderT.run_pure, MAlgOrdered.μ_pure]
  μ_bind_mono f g hfg x := by
    intro r
    simp only [ReaderT.run_bind, bind_assoc]
    exact MAlgOrdered.μ_bind_mono
      (f := fun a => (f a).run r >>= fun q => pure (q r))
      (g := fun a => (g a).run r >>= fun q => pure (q r))
      (fun a => (hfg a) r)
      (x.run r)

attribute [instance] instReaderT

/-- Lift an ordered monad algebra through `ExceptT` by interpreting exceptions as `⊥`. -/
@[implicit_reducible] noncomputable def instExceptT (ε : Type u) :
    MAlgOrdered (ExceptT ε m) l where
  μ x := MAlgOrdered.μ <| (fun y : Except ε l =>
    match y with
    | Except.ok z => z
    | Except.error _ => ⊥) <$> x.run
  μ_pure x := by
    simp [MAlgOrdered.μ_pure]
  μ_bind_mono f g hfg x := by
    let collapse : Except ε l → l := fun y =>
      match y with
      | Except.ok z => z
      | Except.error _ => ⊥
    simpa [ExceptT.run_bind, collapse] using
      (MAlgOrdered.μ_bind_mono
        (f := fun y => collapse <$>
          (match y with
          | Except.ok a => (f a).run
          | Except.error e => pure (Except.error e)))
        (g := fun y => collapse <$>
          (match y with
          | Except.ok a => (g a).run
          | Except.error e => pure (Except.error e)))
        (by
          intro y
          cases y with
          | error e =>
              simp [collapse, MAlgOrdered.μ_pure]
          | ok a =>
              simpa [collapse] using hfg a)
        x.run)

attribute [instance] instExceptT

/-- Lift an ordered monad algebra through `OptionT` by interpreting `none` as `⊥`. -/
@[implicit_reducible] noncomputable def instOptionT :
    MAlgOrdered (OptionT m) l where
  μ x := MAlgOrdered.μ <| (fun y : Option l =>
    match y with
    | some z => z
    | none => ⊥) <$> x.run
  μ_pure x := by
    simp [MAlgOrdered.μ_pure]
  μ_bind_mono f g hfg x := by
    let collapse : Option l → l := fun y =>
      match y with
      | some z => z
      | none => ⊥
    simpa [OptionT.run_bind, Option.elimM, collapse] using
      (MAlgOrdered.μ_bind_mono
        (f := fun y => collapse <$> y.elim (pure none) (fun a => (f a).run))
        (g := fun y => collapse <$> y.elim (pure none) (fun a => (g a).run))
        (by
          intro y
          cases y with
          | none =>
              simp [collapse, MAlgOrdered.μ_pure]
          | some a =>
              simpa [collapse] using hfg a)
        x.run)

attribute [instance] instOptionT

end MAlgOrdered

/-! ## Honest exception WP

`wpExc` is a derived weakest-precondition combinator for `ExceptT` that records *both*
a success postcondition `postOk : α → l` and a failure postcondition `postErr : ε → l`,
rather than collapsing failures to `⊥`. Symmetrically, `wpOpt` is the analogue for
`OptionT`.

These are derived: they use only the unary algebra `MAlgOrdered m l` of the underlying
monad. The standard `MAlgOrdered (ExceptT ε m)` / `MAlgOrdered (OptionT m)` lifts then
correspond to `wpExc · · (fun _ => ⊥)` and `wpOpt · · ⊥` respectively, which is the
"lossy" case. The honest combinators come with their own `pure`/`throw`/`bind`/
`tryCatch` rules that enable side-by-side reasoning about success and failure paths.
-/

namespace MAlgOrdered

variable {m : Type u → Type v} {l : Type u}
variable [Monad m] [CompleteLattice l] [MAlgOrdered m l]
variable {α β ε : Type u}

/-- Honest weakest precondition for `ExceptT`: takes a success postcondition `postOk`
and a failure postcondition `postErr`, and returns the unary `wp` over the underlying
monad with the postcondition split by case. -/
def wpExc (x : ExceptT ε m α) (postOk : α → l) (postErr : ε → l) : l :=
  MAlgOrdered.wp (m := m) x.run (fun ea =>
    match ea with
    | Except.ok a => postOk a
    | Except.error e => postErr e)

/-- Honest weakest precondition for `OptionT`: takes a `some` postcondition and a
`none` postcondition. -/
def wpOpt (x : OptionT m α) (postSome : α → l) (postNone : l) : l :=
  MAlgOrdered.wp (m := m) x.run (fun oa =>
    match oa with
    | some a => postSome a
    | none => postNone)

variable [LawfulMonad m]

/-- Generic case-split postcondition for `Except`-valued returns, used internally
by `wpExc`. -/
private def excPost (postOk : α → l) (postErr : ε → l) : Except ε α → l := fun ea =>
  match ea with
  | Except.ok a => postOk a
  | Except.error e => postErr e

omit [LawfulMonad m] in
private theorem wpExc_def (x : ExceptT ε m α) (postOk : α → l) (postErr : ε → l) :
    wpExc x postOk postErr = MAlgOrdered.wp (m := m) x.run (excPost postOk postErr) :=
  rfl

@[simp]
theorem wpExc_pure (a : α) (postOk : α → l) (postErr : ε → l) :
    wpExc (pure a : ExceptT ε m α) postOk postErr = postOk a := by
  rw [wpExc_def, ExceptT.run_pure, wp_pure]
  rfl

/-- `throw e` is `ExceptT.mk (pure (Except.error e))`. -/
@[simp]
theorem wpExc_throw (e : ε) (postOk : α → l) (postErr : ε → l) :
    wpExc (ExceptT.mk (pure (Except.error e)) : ExceptT ε m α) postOk postErr = postErr e := by
  change MAlgOrdered.wp (m := m) (pure (Except.error e)) (excPost postOk postErr) = _
  rw [wp_pure]
  rfl

/-- Bind law for `wpExc`: only the success branch threads through the post-bind
continuation; the failure postcondition is preserved at every step. -/
theorem wpExc_bind (x : ExceptT ε m α) (f : α → ExceptT ε m β)
    (postOk : β → l) (postErr : ε → l) :
    wpExc (x >>= f) postOk postErr =
      wpExc x (fun a => wpExc (f a) postOk postErr) postErr := by
  rw [wpExc_def, wpExc_def, ExceptT.run_bind, wp_bind]
  congr 1
  funext ea
  cases ea with
  | ok a => rfl
  | error e =>
      rw [wp_pure]
      rfl

/-- Catch law for `wpExc`: `tryCatch x h` exchanges its failure postcondition for the
honest WP of the handler. -/
theorem wpExc_tryCatch (x : ExceptT ε m α) (h : ε → ExceptT ε m α)
    (postOk : α → l) (postErr : ε → l) :
    wpExc (ExceptT.tryCatch x h) postOk postErr =
      wpExc x postOk (fun e => wpExc (h e) postOk postErr) := by
  unfold wpExc
  unfold ExceptT.tryCatch ExceptT.run ExceptT.mk
  rw [wp_bind]
  congr 1
  funext ea
  cases ea with
  | ok a => rw [wp_pure]
  | error e => rfl

omit [LawfulMonad m] in
/-- `wpExc` is monotone in both postconditions. -/
theorem wpExc_mono (x : ExceptT ε m α)
    {postOk postOk' : α → l} {postErr postErr' : ε → l}
    (hOk : ∀ a, postOk a ≤ postOk' a) (hErr : ∀ e, postErr e ≤ postErr' e) :
    wpExc x postOk postErr ≤ wpExc x postOk' postErr' := by
  rw [wpExc_def, wpExc_def]
  apply wp_mono
  intro ea
  cases ea with
  | ok a => exact hOk a
  | error e => exact hErr e

/-- Generic case-split postcondition for `Option`-valued returns. -/
private def optPost (postSome : α → l) (postNone : l) : Option α → l := fun oa =>
  match oa with
  | some a => postSome a
  | none => postNone

omit [LawfulMonad m] in
private theorem wpOpt_def (x : OptionT m α) (postSome : α → l) (postNone : l) :
    wpOpt x postSome postNone = MAlgOrdered.wp (m := m) x.run (optPost postSome postNone) :=
  rfl

@[simp]
theorem wpOpt_pure (a : α) (postSome : α → l) (postNone : l) :
    wpOpt (pure a : OptionT m α) postSome postNone = postSome a := by
  change MAlgOrdered.wp (m := m) (pure (some a)) (optPost postSome postNone) = _
  rw [wp_pure]
  rfl

@[simp]
theorem wpOpt_fail (postSome : α → l) (postNone : l) :
    wpOpt (OptionT.mk (pure none) : OptionT m α) postSome postNone = postNone := by
  change MAlgOrdered.wp (m := m) (pure none) (optPost postSome postNone) = _
  rw [wp_pure]
  rfl

theorem wpOpt_bind (x : OptionT m α) (f : α → OptionT m β)
    (postSome : β → l) (postNone : l) :
    wpOpt (x >>= f) postSome postNone =
      wpOpt x (fun a => wpOpt (f a) postSome postNone) postNone := by
  rw [wpOpt_def, wpOpt_def, OptionT.run_bind]
  change MAlgOrdered.wp (m := m) (x.run >>= fun oa =>
      Option.elim oa (pure none) (fun a => (f a).run)) (optPost postSome postNone) = _
  rw [wp_bind]
  congr 1
  funext oa
  cases oa with
  | some a => rfl
  | none =>
      change MAlgOrdered.wp (m := m) (pure none) _ = _
      rw [wp_pure]
      rfl

omit [LawfulMonad m] in
theorem wpOpt_mono (x : OptionT m α)
    {postSome postSome' : α → l} {postNone postNone' : l}
    (hSome : ∀ a, postSome a ≤ postSome' a) (hNone : postNone ≤ postNone') :
    wpOpt x postSome postNone ≤ wpOpt x postSome' postNone' := by
  rw [wpOpt_def, wpOpt_def]
  apply wp_mono
  intro oa
  cases oa with
  | some a => exact hSome a
  | none => exact hNone

end MAlgOrdered
