/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
module

public import ToMathlib.Control.Monad.RelationalAlgebra

/-!
# Honest exception relational WPs

This file derives "honest" relational weakest-precondition combinators for `ExceptT` and
`OptionT` from `MAlgRelOrdered.Anchored`, mirroring the unary `MAlgOrdered.wpExc` /
`MAlgOrdered.wpOpt` derivations in `ToMathlib/Control/Monad/Algebra.lean`.

Unlike the lossy lifts `MAlgRelOrdered.instExceptTLeft` / `instExceptTRight` /
`instOptionTLeft` / `instOptionTRight`, which collapse exceptions and `none` to `⊥`,
these combinators record case-split postconditions for both the success and the
failure branches. The two-sided combinators carry one postcondition for each of the
four (success/failure × success/failure) corners; the one-sided combinators carry a
success and a failure postcondition for the side that has the transformer.

The combinators are:

* `rwpExc x y postOO postEO postOE postEE` — both sides are `ExceptT`; postconditions
  for each of the four ok/error case combinations.
* `rwpExcLeft x y postOk postErr` — only the left side is `ExceptT`.
* `rwpExcRight x y postOk postErr` — only the right side is `ExceptT`.
* `rwpOpt x y postSS postSN postNS postNN` — analogue for `OptionT`.
* `rwpOptLeft`, `rwpOptRight` — one-sided `OptionT` analogues.

Pure / `throw` / `fail` / `mono` rules hold under just `MAlgRelOrdered`. The bind laws
and the "pure on one side reduces to unary `wpExc` / `wpOpt`" reductions additionally
require `MAlgRelOrdered.Anchored`: the `(error, ok)`, `(ok, error)`, and `(none, some)`
mixed cases collapse to a unary expectation on the still-running side via the
anchoring axioms.
-/

@[expose] public section

universe u v₁ v₂ v₃ v₄

namespace MAlgRelOrdered

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
variable [Monad m₁] [Monad m₂] [Preorder l] [MAlgRelOrdered m₁ m₂ l]
variable {α β γ δ : Type u} {ε ε₁ ε₂ : Type u}

/-! ## Honest two-sided exception WP -/

/-- Two-sided 2×2 exception postcondition: the relational postcondition that case-splits
on whether each side returned `Except.ok` or `Except.error`. Used internally by `rwpExc`
to package its four corner postconditions into a single relational postcondition over
`Except ε₁ α × Except ε₂ β`. -/
def excPostBoth
    (postOO : α → β → l) (postEO : ε₁ → β → l)
    (postOE : α → ε₂ → l) (postEE : ε₁ → ε₂ → l) :
    Except ε₁ α → Except ε₂ β → l := fun ea eb =>
  match ea, eb with
  | Except.ok a, Except.ok b => postOO a b
  | Except.error e, Except.ok b => postEO e b
  | Except.ok a, Except.error e => postOE a e
  | Except.error e₁, Except.error e₂ => postEE e₁ e₂

/-- Honest two-sided exception relational weakest precondition: takes one postcondition
per (left ok/error × right ok/error) corner and tracks them all separately, rather than
collapsing failure cases to `⊥` as `instExceptTLeft` / `instExceptTRight` do. -/
def rwpExc
    (x : ExceptT ε₁ m₁ α) (y : ExceptT ε₂ m₂ β)
    (postOO : α → β → l) (postEO : ε₁ → β → l)
    (postOE : α → ε₂ → l) (postEE : ε₁ → ε₂ → l) : l :=
  MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x.run y.run
    (excPostBoth postOO postEO postOE postEE)

/-! ## Honest one-sided exception WPs -/

/-- Left-only exception postcondition: case-splits on whether the left's `Except`
returned `ok` or `error`, leaving the right's `β` untouched. -/
def excPostLeft (postOk : α → β → l) (postErr : ε → β → l) :
    Except ε α → β → l := fun ea b =>
  match ea with
  | Except.ok a => postOk a b
  | Except.error e => postErr e b

/-- Honest left-side exception relational WP: only the left side carries an `ExceptT`,
and we record separate success and failure postconditions for the left side while
leaving the right side as a plain monadic computation in `m₂`. -/
def rwpExcLeft (x : ExceptT ε m₁ α) (y : m₂ β)
    (postOk : α → β → l) (postErr : ε → β → l) : l :=
  MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x.run y (excPostLeft postOk postErr)

/-- Right-only exception postcondition: symmetric to `excPostLeft`, case-splitting on
the right's `Except`. -/
def excPostRight (postOk : α → β → l) (postErr : α → ε → l) :
    α → Except ε β → l := fun a eb =>
  match eb with
  | Except.ok b => postOk a b
  | Except.error e => postErr a e

/-- Honest right-side exception relational WP: only the right side carries an
`ExceptT`. -/
def rwpExcRight (x : m₁ α) (y : ExceptT ε m₂ β)
    (postOk : α → β → l) (postErr : α → ε → l) : l :=
  MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x y.run (excPostRight postOk postErr)

/-! ## Honest two-sided option WP -/

/-- Two-sided `Option` postcondition. -/
def optPostBoth
    (postSS : α → β → l) (postSN : α → l)
    (postNS : β → l) (postNN : l) :
    Option α → Option β → l := fun oa ob =>
  match oa, ob with
  | some a, some b => postSS a b
  | some a, none => postSN a
  | none, some b => postNS b
  | none, none => postNN

/-- Honest two-sided `Option` relational WP. -/
def rwpOpt
    (x : OptionT m₁ α) (y : OptionT m₂ β)
    (postSS : α → β → l) (postSN : α → l)
    (postNS : β → l) (postNN : l) : l :=
  MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x.run y.run
    (optPostBoth postSS postSN postNS postNN)

/-! ## Honest one-sided option WPs -/

/-- Left-only `Option` postcondition. -/
def optPostLeft (postSome : α → β → l) (postNone : β → l) :
    Option α → β → l := fun oa b =>
  match oa with
  | some a => postSome a b
  | none => postNone b

/-- Honest left-side `Option` relational WP. -/
def rwpOptLeft (x : OptionT m₁ α) (y : m₂ β)
    (postSome : α → β → l) (postNone : β → l) : l :=
  MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x.run y (optPostLeft postSome postNone)

/-- Right-only `Option` postcondition. -/
def optPostRight (postSome : α → β → l) (postNone : α → l) :
    α → Option β → l := fun a ob =>
  match ob with
  | some b => postSome a b
  | none => postNone a

/-- Honest right-side `Option` relational WP. -/
def rwpOptRight (x : m₁ α) (y : OptionT m₂ β)
    (postSome : α → β → l) (postNone : α → l) : l :=
  MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x y.run (optPostRight postSome postNone)

end MAlgRelOrdered

/-! ## Pure and monotonicity rules

These hold under just `MAlgRelOrdered`. The pure rules cover the (Ok, Ok),
(Error, Ok), (Ok, Error), (Error, Error) corners when both sides are syntactic
`pure` / `throw`; mixed pure / non-pure cases need anchoring (further down).
-/

namespace MAlgRelOrdered

section Lawful

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
variable [Monad m₁] [Monad m₂] [Preorder l]
variable [MAlgRelOrdered m₁ m₂ l]
variable {α β γ δ : Type u} {ε ε₁ ε₂ : Type u}

/-! ### `rwpExc` pure rules -/

@[simp]
theorem rwpExc_pure_pure (a : α) (b : β)
    (postOO : α → β → l) (postEO : ε₁ → β → l)
    (postOE : α → ε₂ → l) (postEE : ε₁ → ε₂ → l) :
    rwpExc (pure a : ExceptT ε₁ m₁ α) (pure b : ExceptT ε₂ m₂ β)
        postOO postEO postOE postEE = postOO a b := by
  unfold rwpExc
  rw [show (pure a : ExceptT ε₁ m₁ α).run = pure (Except.ok a) from
      ExceptT.run_pure a, show (pure b : ExceptT ε₂ m₂ β).run = pure (Except.ok b) from
      ExceptT.run_pure b]
  rw [MAlgRelOrdered.rwp_pure]
  rfl

@[simp]
theorem rwpExc_throw_pure (e : ε₁) (b : β)
    (postOO : α → β → l) (postEO : ε₁ → β → l)
    (postOE : α → ε₂ → l) (postEE : ε₁ → ε₂ → l) :
    rwpExc (throw e : ExceptT ε₁ m₁ α) (pure b : ExceptT ε₂ m₂ β)
        postOO postEO postOE postEE = postEO e b := by
  unfold rwpExc
  rw [show (throw e : ExceptT ε₁ m₁ α).run = pure (Except.error e) from
      ExceptT.run_throw, show (pure b : ExceptT ε₂ m₂ β).run = pure (Except.ok b) from
      ExceptT.run_pure b]
  rw [MAlgRelOrdered.rwp_pure]
  rfl

@[simp]
theorem rwpExc_pure_throw (a : α) (e : ε₂)
    (postOO : α → β → l) (postEO : ε₁ → β → l)
    (postOE : α → ε₂ → l) (postEE : ε₁ → ε₂ → l) :
    rwpExc (pure a : ExceptT ε₁ m₁ α) (throw e : ExceptT ε₂ m₂ β)
        postOO postEO postOE postEE = postOE a e := by
  unfold rwpExc
  rw [show (pure a : ExceptT ε₁ m₁ α).run = pure (Except.ok a) from
      ExceptT.run_pure a, show (throw e : ExceptT ε₂ m₂ β).run = pure (Except.error e) from
      ExceptT.run_throw]
  rw [MAlgRelOrdered.rwp_pure]
  rfl

@[simp]
theorem rwpExc_throw_throw (e₁ : ε₁) (e₂ : ε₂)
    (postOO : α → β → l) (postEO : ε₁ → β → l)
    (postOE : α → ε₂ → l) (postEE : ε₁ → ε₂ → l) :
    rwpExc (throw e₁ : ExceptT ε₁ m₁ α) (throw e₂ : ExceptT ε₂ m₂ β)
        postOO postEO postOE postEE = postEE e₁ e₂ := by
  unfold rwpExc
  rw [show (throw e₁ : ExceptT ε₁ m₁ α).run = pure (Except.error e₁) from
      ExceptT.run_throw, show (throw e₂ : ExceptT ε₂ m₂ β).run = pure (Except.error e₂) from
      ExceptT.run_throw]
  rw [MAlgRelOrdered.rwp_pure]
  rfl

/-! ### `rwpExcLeft` pure rules -/

@[simp]
theorem rwpExcLeft_pure (a : α) (y : m₂ β)
    (postOk : α → β → l) (postErr : ε → β → l) :
    rwpExcLeft (pure a : ExceptT ε m₁ α) y postOk postErr =
      MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure (Except.ok a)) y
        (excPostLeft postOk postErr) := by
  unfold rwpExcLeft
  rw [show (pure a : ExceptT ε m₁ α).run = pure (Except.ok a) from ExceptT.run_pure a]

@[simp]
theorem rwpExcLeft_throw (e : ε) (y : m₂ β)
    (postOk : α → β → l) (postErr : ε → β → l) :
    rwpExcLeft (throw e : ExceptT ε m₁ α) y postOk postErr =
      MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure (Except.error e)) y
        (excPostLeft postOk postErr) := by
  unfold rwpExcLeft
  rw [show (throw e : ExceptT ε m₁ α).run = pure (Except.error e) from ExceptT.run_throw]

/-! ### `rwpExcRight` pure rules -/

@[simp]
theorem rwpExcRight_pure (x : m₁ α) (b : β)
    (postOk : α → β → l) (postErr : α → ε → l) :
    rwpExcRight x (pure b : ExceptT ε m₂ β) postOk postErr =
      MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x (pure (Except.ok b))
        (excPostRight postOk postErr) := by
  unfold rwpExcRight
  rw [show (pure b : ExceptT ε m₂ β).run = pure (Except.ok b) from ExceptT.run_pure b]

@[simp]
theorem rwpExcRight_throw (x : m₁ α) (e : ε)
    (postOk : α → β → l) (postErr : α → ε → l) :
    rwpExcRight x (throw e : ExceptT ε m₂ β) postOk postErr =
      MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x (pure (Except.error e))
        (excPostRight postOk postErr) := by
  unfold rwpExcRight
  rw [show (throw e : ExceptT ε m₂ β).run = pure (Except.error e) from ExceptT.run_throw]

/-! ### `rwpOpt` pure rules -/

@[simp]
theorem rwpOpt_pure_pure (a : α) (b : β)
    (postSS : α → β → l) (postSN : α → l) (postNS : β → l) (postNN : l) :
    rwpOpt (pure a : OptionT m₁ α) (pure b : OptionT m₂ β)
        postSS postSN postNS postNN = postSS a b := by
  unfold rwpOpt
  rw [show (pure a : OptionT m₁ α).run = pure (some a) from OptionT.run_pure a,
      show (pure b : OptionT m₂ β).run = pure (some b) from OptionT.run_pure b]
  rw [MAlgRelOrdered.rwp_pure]
  rfl

@[simp]
theorem rwpOpt_fail_pure (b : β)
    (postSS : α → β → l) (postSN : α → l) (postNS : β → l) (postNN : l) :
    rwpOpt (OptionT.mk (pure none) : OptionT m₁ α) (pure b : OptionT m₂ β)
        postSS postSN postNS postNN = postNS b := by
  unfold rwpOpt
  rw [show (pure b : OptionT m₂ β).run = pure (some b) from OptionT.run_pure b]
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure none) (pure (some b))
    (optPostBoth postSS postSN postNS postNN) = _
  rw [MAlgRelOrdered.rwp_pure]
  rfl

@[simp]
theorem rwpOpt_pure_fail (a : α)
    (postSS : α → β → l) (postSN : α → l) (postNS : β → l) (postNN : l) :
    rwpOpt (pure a : OptionT m₁ α) (OptionT.mk (pure none) : OptionT m₂ β)
        postSS postSN postNS postNN = postSN a := by
  unfold rwpOpt
  rw [show (pure a : OptionT m₁ α).run = pure (some a) from OptionT.run_pure a]
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure (some a)) (pure none)
    (optPostBoth postSS postSN postNS postNN) = _
  rw [MAlgRelOrdered.rwp_pure]
  rfl

@[simp]
theorem rwpOpt_fail_fail
    (postSS : α → β → l) (postSN : α → l) (postNS : β → l) (postNN : l) :
    rwpOpt (OptionT.mk (pure none) : OptionT m₁ α) (OptionT.mk (pure none) : OptionT m₂ β)
        postSS postSN postNS postNN = postNN := by
  unfold rwpOpt
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure none) (pure none)
    (optPostBoth postSS postSN postNS postNN) = _
  rw [MAlgRelOrdered.rwp_pure]
  rfl

/-! ### Monotonicity -/

theorem rwpExc_mono (x : ExceptT ε₁ m₁ α) (y : ExceptT ε₂ m₂ β)
    {postOO postOO' : α → β → l} {postEO postEO' : ε₁ → β → l}
    {postOE postOE' : α → ε₂ → l} {postEE postEE' : ε₁ → ε₂ → l}
    (hOO : ∀ a b, postOO a b ≤ postOO' a b)
    (hEO : ∀ e b, postEO e b ≤ postEO' e b)
    (hOE : ∀ a e, postOE a e ≤ postOE' a e)
    (hEE : ∀ e₁ e₂, postEE e₁ e₂ ≤ postEE' e₁ e₂) :
    rwpExc x y postOO postEO postOE postEE ≤ rwpExc x y postOO' postEO' postOE' postEE' := by
  unfold rwpExc
  apply MAlgRelOrdered.rwp_mono
  intro ea eb
  cases ea with
  | ok a =>
      cases eb with
      | ok b => exact hOO a b
      | error e => exact hOE a e
  | error e =>
      cases eb with
      | ok b => exact hEO e b
      | error e' => exact hEE e e'

theorem rwpExcLeft_mono (x : ExceptT ε m₁ α) (y : m₂ β)
    {postOk postOk' : α → β → l} {postErr postErr' : ε → β → l}
    (hOk : ∀ a b, postOk a b ≤ postOk' a b)
    (hErr : ∀ e b, postErr e b ≤ postErr' e b) :
    rwpExcLeft x y postOk postErr ≤ rwpExcLeft x y postOk' postErr' := by
  unfold rwpExcLeft
  apply MAlgRelOrdered.rwp_mono
  intro ea b
  cases ea with
  | ok a => exact hOk a b
  | error e => exact hErr e b

theorem rwpExcRight_mono (x : m₁ α) (y : ExceptT ε m₂ β)
    {postOk postOk' : α → β → l} {postErr postErr' : α → ε → l}
    (hOk : ∀ a b, postOk a b ≤ postOk' a b)
    (hErr : ∀ a e, postErr a e ≤ postErr' a e) :
    rwpExcRight x y postOk postErr ≤ rwpExcRight x y postOk' postErr' := by
  unfold rwpExcRight
  apply MAlgRelOrdered.rwp_mono
  intro a eb
  cases eb with
  | ok b => exact hOk a b
  | error e => exact hErr a e

theorem rwpOpt_mono (x : OptionT m₁ α) (y : OptionT m₂ β)
    {postSS postSS' : α → β → l} {postSN postSN' : α → l}
    {postNS postNS' : β → l} {postNN postNN' : l}
    (hSS : ∀ a b, postSS a b ≤ postSS' a b)
    (hSN : ∀ a, postSN a ≤ postSN' a)
    (hNS : ∀ b, postNS b ≤ postNS' b)
    (hNN : postNN ≤ postNN') :
    rwpOpt x y postSS postSN postNS postNN ≤ rwpOpt x y postSS' postSN' postNS' postNN' := by
  unfold rwpOpt
  apply MAlgRelOrdered.rwp_mono
  intro oa ob
  cases oa with
  | some a =>
      cases ob with
      | some b => exact hSS a b
      | none => exact hSN a
  | none =>
      cases ob with
      | some b => exact hNS b
      | none => exact hNN

theorem rwpOptLeft_mono (x : OptionT m₁ α) (y : m₂ β)
    {postSome postSome' : α → β → l} {postNone postNone' : β → l}
    (hSome : ∀ a b, postSome a b ≤ postSome' a b)
    (hNone : ∀ b, postNone b ≤ postNone' b) :
    rwpOptLeft x y postSome postNone ≤ rwpOptLeft x y postSome' postNone' := by
  unfold rwpOptLeft
  apply MAlgRelOrdered.rwp_mono
  intro oa b
  cases oa with
  | some a => exact hSome a b
  | none => exact hNone b

theorem rwpOptRight_mono (x : m₁ α) (y : OptionT m₂ β)
    {postSome postSome' : α → β → l} {postNone postNone' : α → l}
    (hSome : ∀ a b, postSome a b ≤ postSome' a b)
    (hNone : ∀ a, postNone a ≤ postNone' a) :
    rwpOptRight x y postSome postNone ≤ rwpOptRight x y postSome' postNone' := by
  unfold rwpOptRight
  apply MAlgRelOrdered.rwp_mono
  intro a ob
  cases ob with
  | some b => exact hSome a b
  | none => exact hNone a

end Lawful

end MAlgRelOrdered

/-! ## Anchored reductions and bind laws

These rules require `MAlgRelOrdered.Anchored m₁ m₂ l`: the mixed `(error, ok)`,
`(ok, error)`, and `(none, some)` cases collapse to a unary `wpExc` / `wpOpt` of the
still-running side via the anchoring axioms.
-/

namespace MAlgRelOrdered.Anchored

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂} {l : Type u}
variable [Monad m₁] [Monad m₂]
variable [CompleteLattice l]
variable [MAlgOrdered m₁ l] [MAlgOrdered m₂ l] [MAlgRelOrdered m₁ m₂ l] [Anchored m₁ m₂ l]
variable {α β γ δ : Type u} {ε ε₁ ε₂ : Type u}

/-! ### `rwpExc` pure-side reductions to unary `wpExc` -/

/-- When the left side is a `pure ok`, the two-sided honest exception WP collapses to
the unary honest exception WP of the right side, specialized at the left's value. -/
theorem rwpExc_pure_left (a : α) (y : ExceptT ε₂ m₂ β)
    (postOO : α → β → l) (postEO : ε₁ → β → l)
    (postOE : α → ε₂ → l) (postEE : ε₁ → ε₂ → l) :
    rwpExc (pure a : ExceptT ε₁ m₁ α) y postOO postEO postOE postEE =
      MAlgOrdered.wpExc y (postOO a) (postOE a) := by
  unfold rwpExc MAlgOrdered.wpExc
  rw [show (pure a : ExceptT ε₁ m₁ α).run = pure (Except.ok a) from ExceptT.run_pure a]
  rw [Anchored.rwp_pure_left]
  congr 1
  funext eb
  cases eb with
  | ok b => rfl
  | error e => rfl

/-- When the left side is a `throw e`, the two-sided honest exception WP collapses to
the unary honest exception WP of the right side, with postconditions specialized at
the left's error `e`. -/
theorem rwpExc_throw_left (e : ε₁) (y : ExceptT ε₂ m₂ β)
    (postOO : α → β → l) (postEO : ε₁ → β → l)
    (postOE : α → ε₂ → l) (postEE : ε₁ → ε₂ → l) :
    rwpExc (throw e : ExceptT ε₁ m₁ α) y postOO postEO postOE postEE =
      MAlgOrdered.wpExc y (postEO e) (postEE e) := by
  unfold rwpExc MAlgOrdered.wpExc
  rw [show (throw e : ExceptT ε₁ m₁ α).run = pure (Except.error e) from ExceptT.run_throw]
  rw [Anchored.rwp_pure_left]
  congr 1
  funext eb
  cases eb with
  | ok b => rfl
  | error e' => rfl

/-- Symmetric to `rwpExc_pure_left` on the right side. -/
theorem rwpExc_pure_right (x : ExceptT ε₁ m₁ α) (b : β)
    (postOO : α → β → l) (postEO : ε₁ → β → l)
    (postOE : α → ε₂ → l) (postEE : ε₁ → ε₂ → l) :
    rwpExc x (pure b : ExceptT ε₂ m₂ β) postOO postEO postOE postEE =
      MAlgOrdered.wpExc x (fun a => postOO a b) (fun e => postEO e b) := by
  unfold rwpExc MAlgOrdered.wpExc
  rw [show (pure b : ExceptT ε₂ m₂ β).run = pure (Except.ok b) from ExceptT.run_pure b]
  rw [Anchored.rwp_pure_right]
  congr 1
  funext ea
  cases ea with
  | ok a => rfl
  | error e => rfl

/-- Symmetric to `rwpExc_throw_left` on the right side. -/
theorem rwpExc_throw_right (x : ExceptT ε₁ m₁ α) (e : ε₂)
    (postOO : α → β → l) (postEO : ε₁ → β → l)
    (postOE : α → ε₂ → l) (postEE : ε₁ → ε₂ → l) :
    rwpExc x (throw e : ExceptT ε₂ m₂ β) postOO postEO postOE postEE =
      MAlgOrdered.wpExc x (fun a => postOE a e) (fun e₁ => postEE e₁ e) := by
  unfold rwpExc MAlgOrdered.wpExc
  rw [show (throw e : ExceptT ε₂ m₂ β).run = pure (Except.error e) from ExceptT.run_throw]
  rw [Anchored.rwp_pure_right]
  congr 1
  funext ea
  cases ea with
  | ok a => rfl
  | error e' => rfl

/-! ### `rwpExcLeft` / `rwpExcRight` pure-side reductions -/

/-- When the left's `ExceptT` is `pure a`, the left-only honest exception WP collapses
to the unary `MAlgOrdered.wp` of the right side at `postOk a`. -/
theorem rwpExcLeft_pure_left (a : α) (y : m₂ β)
    (postOk : α → β → l) (postErr : ε → β → l) :
    rwpExcLeft (pure a : ExceptT ε m₁ α) y postOk postErr =
      MAlgOrdered.wp y (postOk a) := by
  unfold rwpExcLeft
  rw [show (pure a : ExceptT ε m₁ α).run = pure (Except.ok a) from ExceptT.run_pure a]
  rw [Anchored.rwp_pure_left]
  rfl

/-- When the left's `ExceptT` is `throw e`, the left-only honest exception WP collapses
to the unary `MAlgOrdered.wp` of the right side at `postErr e`. -/
theorem rwpExcLeft_throw_left (e : ε) (y : m₂ β)
    (postOk : α → β → l) (postErr : ε → β → l) :
    rwpExcLeft (throw e : ExceptT ε m₁ α) y postOk postErr =
      MAlgOrdered.wp y (postErr e) := by
  unfold rwpExcLeft
  rw [show (throw e : ExceptT ε m₁ α).run = pure (Except.error e) from ExceptT.run_throw]
  rw [Anchored.rwp_pure_left]
  rfl

/-- Symmetric to `rwpExcLeft_pure_left` on the right side. -/
theorem rwpExcRight_pure_right (x : m₁ α) (b : β)
    (postOk : α → β → l) (postErr : α → ε → l) :
    rwpExcRight x (pure b : ExceptT ε m₂ β) postOk postErr =
      MAlgOrdered.wp x (fun a => postOk a b) := by
  unfold rwpExcRight
  rw [show (pure b : ExceptT ε m₂ β).run = pure (Except.ok b) from ExceptT.run_pure b]
  rw [Anchored.rwp_pure_right]
  rfl

/-- Symmetric to `rwpExcLeft_throw_left` on the right side. -/
theorem rwpExcRight_throw_right (x : m₁ α) (e : ε)
    (postOk : α → β → l) (postErr : α → ε → l) :
    rwpExcRight x (throw e : ExceptT ε m₂ β) postOk postErr =
      MAlgOrdered.wp x (fun a => postErr a e) := by
  unfold rwpExcRight
  rw [show (throw e : ExceptT ε m₂ β).run = pure (Except.error e) from ExceptT.run_throw]
  rw [Anchored.rwp_pure_right]
  rfl

/-! ### `rwpOpt` pure-side reductions -/

/-- When the left side is a `pure a`, the two-sided honest option WP collapses to the
unary honest option WP of the right side, specialized at the left's value. -/
theorem rwpOpt_pure_left (a : α) (y : OptionT m₂ β)
    (postSS : α → β → l) (postSN : α → l) (postNS : β → l) (postNN : l) :
    rwpOpt (pure a : OptionT m₁ α) y postSS postSN postNS postNN =
      MAlgOrdered.wpOpt y (postSS a) (postSN a) := by
  unfold rwpOpt MAlgOrdered.wpOpt
  rw [show (pure a : OptionT m₁ α).run = pure (some a) from OptionT.run_pure a]
  rw [Anchored.rwp_pure_left]
  congr 1
  funext ob
  cases ob with
  | some b => rfl
  | none => rfl

/-- When the left side is `OptionT.mk (pure none)`, the two-sided honest option WP
collapses to the unary honest option WP of the right side, with postconditions
specialized to the failure case. -/
theorem rwpOpt_fail_left (y : OptionT m₂ β)
    (postSS : α → β → l) (postSN : α → l) (postNS : β → l) (postNN : l) :
    rwpOpt (OptionT.mk (pure none) : OptionT m₁ α) y postSS postSN postNS postNN =
      MAlgOrdered.wpOpt y postNS postNN := by
  unfold rwpOpt MAlgOrdered.wpOpt
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure none) y.run
    (optPostBoth postSS postSN postNS postNN) = _
  rw [Anchored.rwp_pure_left]
  congr 1
  funext ob
  cases ob with
  | some b => rfl
  | none => rfl

/-- Symmetric to `rwpOpt_pure_left` on the right side. -/
theorem rwpOpt_pure_right (x : OptionT m₁ α) (b : β)
    (postSS : α → β → l) (postSN : α → l) (postNS : β → l) (postNN : l) :
    rwpOpt x (pure b : OptionT m₂ β) postSS postSN postNS postNN =
      MAlgOrdered.wpOpt x (fun a => postSS a b) (postNS b) := by
  unfold rwpOpt MAlgOrdered.wpOpt
  rw [show (pure b : OptionT m₂ β).run = pure (some b) from OptionT.run_pure b]
  rw [Anchored.rwp_pure_right]
  congr 1
  funext oa
  cases oa with
  | some a => rfl
  | none => rfl

/-- Symmetric to `rwpOpt_fail_left` on the right side. -/
theorem rwpOpt_fail_right (x : OptionT m₁ α)
    (postSS : α → β → l) (postSN : α → l) (postNS : β → l) (postNN : l) :
    rwpOpt x (OptionT.mk (pure none) : OptionT m₂ β) postSS postSN postNS postNN =
      MAlgOrdered.wpOpt x postSN postNN := by
  unfold rwpOpt MAlgOrdered.wpOpt
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x.run (pure none)
    (optPostBoth postSS postSN postNS postNN) = _
  rw [Anchored.rwp_pure_right]
  congr 1
  funext oa
  cases oa with
  | some a => rfl
  | none => rfl

/-! ### `rwpOptLeft` / `rwpOptRight` pure-side reductions -/

theorem rwpOptLeft_pure_left (a : α) (y : m₂ β)
    (postSome : α → β → l) (postNone : β → l) :
    rwpOptLeft (pure a : OptionT m₁ α) y postSome postNone =
      MAlgOrdered.wp y (postSome a) := by
  unfold rwpOptLeft
  rw [show (pure a : OptionT m₁ α).run = pure (some a) from OptionT.run_pure a]
  rw [Anchored.rwp_pure_left]
  rfl

theorem rwpOptLeft_fail_left (y : m₂ β)
    (postSome : α → β → l) (postNone : β → l) :
    rwpOptLeft (OptionT.mk (pure none) : OptionT m₁ α) y postSome postNone =
      MAlgOrdered.wp y postNone := by
  unfold rwpOptLeft
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure none) y
    (optPostLeft postSome postNone) = _
  rw [Anchored.rwp_pure_left]
  rfl

theorem rwpOptRight_pure_right (x : m₁ α) (b : β)
    (postSome : α → β → l) (postNone : α → l) :
    rwpOptRight x (pure b : OptionT m₂ β) postSome postNone =
      MAlgOrdered.wp x (fun a => postSome a b) := by
  unfold rwpOptRight
  rw [show (pure b : OptionT m₂ β).run = pure (some b) from OptionT.run_pure b]
  rw [Anchored.rwp_pure_right]
  rfl

theorem rwpOptRight_fail_right (x : m₁ α)
    (postSome : α → β → l) (postNone : α → l) :
    rwpOptRight x (OptionT.mk (pure none) : OptionT m₂ β) postSome postNone =
      MAlgOrdered.wp x postNone := by
  unfold rwpOptRight
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x (pure none)
    (optPostRight postSome postNone) = _
  rw [Anchored.rwp_pure_right]
  rfl

/-! ### Bind laws

The two-sided `rwpExc` bind law is the key payoff of anchoring: each of the four cases
in the inner relational WP either chains relationally (when both sides succeed) or
collapses to the unary `wpExc` of the still-running side (when one side fails). The
one-sided `rwpExcLeft` / `rwpExcRight` bind laws are the simpler analogues. The same
pattern applies to `rwpOpt` / `rwpOptLeft` / `rwpOptRight`.
-/

/-- Bind law for the honest left-only exception WP. The (ok) branch chains
relationally; the (error) branch collapses to a unary `wp` on the right side via
anchoring. -/
theorem rwpExcLeft_bind_le (x : ExceptT ε m₁ α) (y : m₂ β)
    (f : α → ExceptT ε m₁ γ) (g : β → m₂ δ)
    (postOk : γ → δ → l) (postErr : ε → δ → l) :
    rwpExcLeft x y
        (fun a b => rwpExcLeft (f a) (g b) postOk postErr)
        (fun e b => MAlgOrdered.wp (g b) (postErr e)) ≤
      rwpExcLeft (x >>= f) (y >>= g) postOk postErr := by
  simp only [rwpExcLeft]
  let MID : Except ε α → β → l := fun ea b =>
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (ExceptT.bindCont f ea) (g b)
      (excPostLeft postOk postErr)
  let LHSpost : Except ε α → β → l := fun ea b =>
    match ea with
    | Except.ok a =>
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a).run (g b) (excPostLeft postOk postErr)
    | Except.error e => MAlgOrdered.wp (g b) (postErr e)
  have hpost : LHSpost = MID := by
    funext ea b
    cases ea with
    | ok a => rfl
    | error e =>
        change MAlgOrdered.wp (g b) (postErr e) =
          MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure (Except.error e)) (g b)
            (excPostLeft postOk postErr)
        rw [Anchored.rwp_pure_left]
        rfl
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x.run y LHSpost ≤
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (x >>= f).run (y >>= g) (excPostLeft postOk postErr)
  rw [hpost]
  have hbind := MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
    (x := x.run) (y := y)
    (f := ExceptT.bindCont f) (g := g)
    (post := excPostLeft postOk postErr)
  refine le_trans hbind ?_
  rw [show (x >>= f).run = x.run >>= ExceptT.bindCont f from rfl]

/-- Bind law for the honest right-only exception WP. -/
theorem rwpExcRight_bind_le (x : m₁ α) (y : ExceptT ε m₂ β)
    (f : α → m₁ γ) (g : β → ExceptT ε m₂ δ)
    (postOk : γ → δ → l) (postErr : γ → ε → l) :
    rwpExcRight x y
        (fun a b => rwpExcRight (f a) (g b) postOk postErr)
        (fun a e => MAlgOrdered.wp (f a) (fun c => postErr c e)) ≤
      rwpExcRight (x >>= f) (y >>= g) postOk postErr := by
  simp only [rwpExcRight]
  let MID : α → Except ε β → l := fun a eb =>
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a) (ExceptT.bindCont g eb)
      (excPostRight postOk postErr)
  let LHSpost : α → Except ε β → l := fun a eb =>
    match eb with
    | Except.ok b =>
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a) (g b).run (excPostRight postOk postErr)
    | Except.error e => MAlgOrdered.wp (f a) (fun c => postErr c e)
  have hpost : LHSpost = MID := by
    funext a eb
    cases eb with
    | ok b => rfl
    | error e =>
        change MAlgOrdered.wp (f a) (fun c => postErr c e) =
          MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a) (pure (Except.error e))
            (excPostRight postOk postErr)
        rw [Anchored.rwp_pure_right]
        rfl
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x y.run LHSpost ≤
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (x >>= f) (y >>= g).run (excPostRight postOk postErr)
  rw [hpost]
  have hbind := MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
    (x := x) (y := y.run)
    (f := f) (g := ExceptT.bindCont g)
    (post := excPostRight postOk postErr)
  refine le_trans hbind ?_
  rw [show (y >>= g).run = y.run >>= ExceptT.bindCont g from rfl]

/-- Bind law for the honest two-sided exception WP. The four cases are:

* `(ok, ok)`: chain relationally via `rwpExc`.
* `(error, ok)`: collapse to the unary honest exception WP of the right's `g`.
* `(ok, error)`: collapse to the unary honest exception WP of the left's `f`.
* `(error, error)`: trivially `postEE e₁ e₂`.
-/
theorem rwpExc_bind_le
    (x : ExceptT ε₁ m₁ α) (y : ExceptT ε₂ m₂ β)
    (f : α → ExceptT ε₁ m₁ γ) (g : β → ExceptT ε₂ m₂ δ)
    (postOO : γ → δ → l) (postEO : ε₁ → δ → l)
    (postOE : γ → ε₂ → l) (postEE : ε₁ → ε₂ → l) :
    rwpExc x y
        (fun a b => rwpExc (f a) (g b) postOO postEO postOE postEE)
        (fun e b => MAlgOrdered.wpExc (g b) (postEO e) (postEE e))
        (fun a e => MAlgOrdered.wpExc (f a) (fun c => postOE c e) (fun e₁ => postEE e₁ e))
        postEE ≤
      rwpExc (x >>= f) (y >>= g) postOO postEO postOE postEE := by
  simp only [rwpExc]
  let MID : Except ε₁ α → Except ε₂ β → l := fun ea eb =>
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (ExceptT.bindCont f ea) (ExceptT.bindCont g eb)
      (excPostBoth postOO postEO postOE postEE)
  let LHSpost : Except ε₁ α → Except ε₂ β → l := fun ea eb =>
    match ea, eb with
    | Except.ok a, Except.ok b =>
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a).run (g b).run
          (excPostBoth postOO postEO postOE postEE)
    | Except.error e, Except.ok b => MAlgOrdered.wpExc (g b) (postEO e) (postEE e)
    | Except.ok a, Except.error e =>
        MAlgOrdered.wpExc (f a) (fun c => postOE c e) (fun e₁ => postEE e₁ e)
    | Except.error e₁, Except.error e₂ => postEE e₁ e₂
  have hpost : LHSpost = MID := by
    funext ea eb
    cases ea with
    | ok a =>
        cases eb with
        | ok b => rfl
        | error e =>
            change MAlgOrdered.wpExc (f a) (fun c => postOE c e) (fun e₁ => postEE e₁ e) =
              MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a) (pure (Except.error e))
                (excPostBoth postOO postEO postOE postEE)
            rw [Anchored.rwp_pure_right]
            unfold MAlgOrdered.wpExc
            congr 1
            funext ec
            cases ec with
            | ok c => rfl
            | error e₁ => rfl
    | error e =>
        cases eb with
        | ok b =>
            change MAlgOrdered.wpExc (g b) (postEO e) (postEE e) =
              MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure (Except.error e)) (g b)
                (excPostBoth postOO postEO postOE postEE)
            rw [Anchored.rwp_pure_left]
            unfold MAlgOrdered.wpExc
            congr 1
            funext ed
            cases ed with
            | ok d => rfl
            | error e₂ => rfl
        | error e' =>
            change postEE e e' =
              MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂)
                (pure (Except.error e)) (pure (Except.error e'))
                (excPostBoth postOO postEO postOE postEE)
            rw [MAlgRelOrdered.rwp_pure]
            rfl
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x.run y.run LHSpost ≤
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (x >>= f).run (y >>= g).run
      (excPostBoth postOO postEO postOE postEE)
  rw [hpost]
  have hbind := MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
    (x := x.run) (y := y.run)
    (f := ExceptT.bindCont f) (g := ExceptT.bindCont g)
    (post := excPostBoth postOO postEO postOE postEE)
  refine le_trans hbind ?_
  rw [show (x >>= f).run = x.run >>= ExceptT.bindCont f from rfl,
      show (y >>= g).run = y.run >>= ExceptT.bindCont g from rfl]

/-! ## Bind laws for the `OptionT` derived combinators -/

/-- Bind law for the honest left-only `Option` WP. The (some) branch chains
relationally; the (none) branch collapses to a unary `wp` on the right side
via anchoring. -/
theorem rwpOptLeft_bind_le (x : OptionT m₁ α) (y : m₂ β)
    (f : α → OptionT m₁ γ) (g : β → m₂ δ)
    (postSome : γ → δ → l) (postNone : δ → l) :
    rwpOptLeft x y
        (fun a b => rwpOptLeft (f a) (g b) postSome postNone)
        (fun b => MAlgOrdered.wp (g b) postNone) ≤
      rwpOptLeft (x >>= f) (y >>= g) postSome postNone := by
  simp only [rwpOptLeft]
  let bindCont : Option α → m₁ (Option γ) := fun oa =>
    Option.elim oa (pure none) (fun a => (f a).run)
  let MID : Option α → β → l := fun oa b =>
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (bindCont oa) (g b)
      (optPostLeft postSome postNone)
  let LHSpost : Option α → β → l := fun oa b =>
    match oa with
    | some a =>
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a).run (g b) (optPostLeft postSome postNone)
    | none => MAlgOrdered.wp (g b) postNone
  have hpost : LHSpost = MID := by
    funext oa b
    cases oa with
    | some a => rfl
    | none =>
        change MAlgOrdered.wp (g b) postNone =
          MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure none) (g b)
            (optPostLeft postSome postNone)
        rw [Anchored.rwp_pure_left]
        rfl
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x.run y LHSpost ≤
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (x >>= f).run (y >>= g) (optPostLeft postSome postNone)
  rw [hpost]
  have hbind := MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
    (x := x.run) (y := y)
    (f := bindCont) (g := g)
    (post := optPostLeft postSome postNone)
  refine le_trans hbind ?_
  rw [show (x >>= f).run = x.run >>= bindCont by
    simp only [OptionT.run_bind, Option.elimM, bindCont]]

/-- Bind law for the honest right-only `Option` WP. -/
theorem rwpOptRight_bind_le (x : m₁ α) (y : OptionT m₂ β)
    (f : α → m₁ γ) (g : β → OptionT m₂ δ)
    (postSome : γ → δ → l) (postNone : γ → l) :
    rwpOptRight x y
        (fun a b => rwpOptRight (f a) (g b) postSome postNone)
        (fun a => MAlgOrdered.wp (f a) postNone) ≤
      rwpOptRight (x >>= f) (y >>= g) postSome postNone := by
  simp only [rwpOptRight]
  let bindCont : Option β → m₂ (Option δ) := fun ob =>
    Option.elim ob (pure none) (fun b => (g b).run)
  let MID : α → Option β → l := fun a ob =>
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a) (bindCont ob)
      (optPostRight postSome postNone)
  let LHSpost : α → Option β → l := fun a ob =>
    match ob with
    | some b =>
        MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a) (g b).run (optPostRight postSome postNone)
    | none => MAlgOrdered.wp (f a) postNone
  have hpost : LHSpost = MID := by
    funext a ob
    cases ob with
    | some b => rfl
    | none =>
        change MAlgOrdered.wp (f a) postNone =
          MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a) (pure none)
            (optPostRight postSome postNone)
        rw [Anchored.rwp_pure_right]
        rfl
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x y.run LHSpost ≤
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (x >>= f) (y >>= g).run
      (optPostRight postSome postNone)
  rw [hpost]
  have hbind := MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
    (x := x) (y := y.run)
    (f := f) (g := bindCont)
    (post := optPostRight postSome postNone)
  refine le_trans hbind ?_
  rw [show (y >>= g).run = y.run >>= bindCont by
    simp only [OptionT.run_bind, Option.elimM, bindCont]]

/-- Bind law for the honest two-sided `Option` WP. The four cases are:

* `(some, some)`: chain relationally via `rwpOpt`.
* `(none, some)`: collapse to the unary honest `Option` WP of the right's `g`.
* `(some, none)`: collapse to the unary honest `Option` WP of the left's `f`.
* `(none, none)`: trivially `postNN`.
-/
theorem rwpOpt_bind_le
    (x : OptionT m₁ α) (y : OptionT m₂ β)
    (f : α → OptionT m₁ γ) (g : β → OptionT m₂ δ)
    (postSS : γ → δ → l) (postSN : γ → l)
    (postNS : δ → l) (postNN : l) :
    rwpOpt x y
        (fun a b => rwpOpt (f a) (g b) postSS postSN postNS postNN)
        (fun a => MAlgOrdered.wpOpt (f a) postSN postNN)
        (fun b => MAlgOrdered.wpOpt (g b) postNS postNN)
        postNN ≤
      rwpOpt (x >>= f) (y >>= g) postSS postSN postNS postNN := by
  simp only [rwpOpt]
  let bindContF : Option α → m₁ (Option γ) := fun oa =>
    Option.elim oa (pure none) (fun a => (f a).run)
  let bindContG : Option β → m₂ (Option δ) := fun ob =>
    Option.elim ob (pure none) (fun b => (g b).run)
  let MID : Option α → Option β → l := fun oa ob =>
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (bindContF oa) (bindContG ob)
      (optPostBoth postSS postSN postNS postNN)
  let postSS' : α → β → l := fun a b =>
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a).run (g b).run
      (optPostBoth postSS postSN postNS postNN)
  let postSN' : α → l := fun a => MAlgOrdered.wpOpt (f a) postSN postNN
  let postNS' : β → l := fun b => MAlgOrdered.wpOpt (g b) postNS postNN
  have hpost : optPostBoth postSS' postSN' postNS' postNN = MID := by
    funext oa ob
    cases oa with
    | some a =>
        cases ob with
        | some b => rfl
        | none =>
            change MAlgOrdered.wpOpt (f a) postSN postNN =
              MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (f a) (pure none)
                (optPostBoth postSS postSN postNS postNN)
            rw [Anchored.rwp_pure_right]
            unfold MAlgOrdered.wpOpt
            congr 1
            funext oc
            cases oc with
            | some c => rfl
            | none => rfl
    | none =>
        cases ob with
        | some b =>
            change MAlgOrdered.wpOpt (g b) postNS postNN =
              MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure none) (g b)
                (optPostBoth postSS postSN postNS postNN)
            rw [Anchored.rwp_pure_left]
            unfold MAlgOrdered.wpOpt
            congr 1
            funext od
            cases od with
            | some d => rfl
            | none => rfl
        | none =>
            change postNN =
              MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (pure none) (pure none)
                (optPostBoth postSS postSN postNS postNN)
            rw [MAlgRelOrdered.rwp_pure]
            rfl
  change MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) x.run y.run
      (optPostBoth postSS' postSN' postNS' postNN) ≤
    MAlgRelOrdered.rwp (m₁ := m₁) (m₂ := m₂) (x >>= f).run (y >>= g).run
      (optPostBoth postSS postSN postNS postNN)
  rw [hpost]
  have hbind := MAlgRelOrdered.rwp_bind_le (m₁ := m₁) (m₂ := m₂) (l := l)
    (x := x.run) (y := y.run)
    (f := bindContF) (g := bindContG)
    (post := optPostBoth postSS postSN postNS postNN)
  refine le_trans hbind ?_
  rw [show (x >>= f).run = x.run >>= bindContF by
        simp only [OptionT.run_bind, Option.elimM, bindContF],
      show (y >>= g).run = y.run >>= bindContG by
        simp only [OptionT.run_bind, Option.elimM, bindContG]]

end MAlgRelOrdered.Anchored
