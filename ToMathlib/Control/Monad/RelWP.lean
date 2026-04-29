/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
module

public import Loom.WP.Basic

@[expose] public section

/-!
# Relational Weakest Precondition Interpretation (Loom2-style)

This module defines the relational analogue of Loom2's `Std.Do'.WP`: a
typeclass `Std.Do'.RelWP m₁ m₂ Pred EPred₁ EPred₂` that interprets a
*pair* of monadic programs `(x : m₁ α, y : m₂ β)` as a predicate
transformer

```
rwp x y : (α → β → Pred) → EPred₁ → EPred₂ → Pred
```

against an assertion language `Pred` and *two* per-side exception
postcondition lattices `EPred₁`, `EPred₂` (asymmetric on purpose, see
"Asymmetric `EPred`" below).

This is the underlying class for the new relational program logic in
`VCVio/ProgramLogic/Relational/Loom/`. Its three carrier instances on
`OracleComp` (Quantitative `ℝ≥0∞` / Probabilistic `Prob` / Qualitative
`Prop`) are registered there. They wrap, respectively, the existing
`eRelWP` (`VCVio/ProgramLogic/Relational/QuantitativeDefs.lean`),
clamped-to-`Prob`, and `CouplingPost`
(`VCVio/ProgramLogic/Relational/Basic.lean`) developments unchanged.

## Why an inline function shape (no `RelPredTrans` wrapper)?

Loom2's unary `WP m Pred EPred` is stated against a `PredTrans Pred
EPred α := (α → Pred) → EPred → Pred` wrapper that carries its own
`Monad` / `MonadStateOf` / `MonadExceptOf` instances, threading
postconditions through monadic combinators. The relational analogue
would be `RelPredTrans Pred EPred₁ EPred₂ α β := (α → β → Pred) →
EPred₁ → EPred₂ → Pred`, but the natural `Monad` shape on
`RelPredTrans` is *not* the obvious one: relational `bind` is
asymmetric, and the monad laws of `PredTrans` already encode the
sequential structure that the relational logic deliberately avoids
fixing (it wants room for the `bind_le` direction to be a *strict*
inequality, as it is for the coupling-based `OracleComp` instance).

We therefore inline the function shape directly. If a `Monad`
structure on `RelPredTrans` ever earns its keep (e.g. for a SymM-style
tactic interpretation), it can be promoted in a follow-up without
breaking any client code.

## Asymmetric `EPred`

The class takes two per-side exception assertion types `EPred₁` and
`EPred₂`, not a single joint `EPred`. This is intentional:

* **Honest for asymmetric monad transformers.** A relational instance
  for `(StateT σ m₁) ↔ (ExceptT ε m₂)` only typechecks if the two
  exception slots are independent.
* **Aligns with `Anchored` coherence.** When one side is `pure`, the
  relational `rwp` collapses to the *unary* `wp` of the other side,
  which carries its own `EPred`. A joint slot would force spurious
  fusion of the two per-side `EPred`s.
* **No-exception specialisation is no harder.** All three
  `OracleComp`-relational carriers in
  `VCVio/ProgramLogic/Relational/Loom/` specialise both `EPred` slots
  to `EPost.nil`; the asymmetric machinery never gets in the way for
  the no-exception case but is there when needed.

## Layout

* `RelWP m₁ m₂ Pred EPred₁ EPred₂` — the class itself.
* `rwp x y post epost₁ epost₂` — the user-facing wrapper around
  `RelWP.rwpTrans`.
* `RelTriple pre x y post epost₁ epost₂ : Prop` — the relational
  Hoare-style triple, defined as `pre ⊑ rwp x y post epost₁ epost₂`.
* Derived consequence / monotonicity / bind lemmas mirroring loom2's
  `WP.{wp_pure, wp_bind, wp_consequence, wp_econs, …}`.

## Attribution

* Loom2 (`verse-lab/loom2`): the unary `Std.Do'.WP` class this mirrors.
  Pinned at `quangvdao/loom2#v4.29.0` @ `589fbd5`.
* Maillard et al., *The Next 700 Relational Program Logics*, POPL 2020:
  the asynchronous bind shape and the `Anchored` coherence pattern.
* Avanzini, Barthe, Grégoire, Davoli, *eRHL*, POPL 2025: the
  quantitative relational logic that the default `ℝ≥0∞` carrier
  realises.
-/

universe u v₁ v₂ w w₁ w₂

open Lean.Order Std.Do'

namespace Std.Do'

/-!
## RelWP Typeclass

The `RelWP` typeclass defines weakest precondition semantics for a
*pair* of monads. A `RelWP m₁ m₂ Pred EPred₁ EPred₂` instance provides
a relational predicate transformer
`rwpTrans : m₁ α → m₂ β → (α → β → Pred) → EPred₁ → EPred₂ → Pred`
satisfying:

* `rwp_trans_pure`: `(pure a, pure b)` is at least as strong as its
  joint predicate transformer at `(a, b)`.
* `rwp_trans_bind_le`: sequential composition of the two sides is
  sound (one-directional `⊑`; the bind law is *lax* because the
  optimal coupling for a composite computation can be more precise
  than the sequential composition of optimal couplings).
* `rwp_trans_monotone`: the relational transformer is monotone in
  each of its three postcondition slots.
-/

/-- Weakest precondition class for a pair of monads `m₁`, `m₂`, with
shared assertion language `Pred`, and asymmetric per-side exception
postcondition lattices `EPred₁`, `EPred₂`.

We do *not* `extends LawfulMonad m₁, LawfulMonad m₂` here, because
Lean's `structure` parent inference identifies parents by head and
silently drops the second `LawfulMonad` parent. Instead we require
`[LawfulMonad m₁] [LawfulMonad m₂]` as instance arguments at the class
header, which makes them available to every theorem about `RelWP`. -/
class RelWP
    (m₁ : Type u → Type v₁) (m₂ : Type u → Type v₂)
    (Pred : outParam (Type w))
    (EPred₁ : outParam (Type w₁))
    (EPred₂ : outParam (Type w₂))
    [Monad m₁] [Monad m₂]
    [LawfulMonad m₁] [LawfulMonad m₂]
    [Assertion Pred] [Assertion EPred₁] [Assertion EPred₂]
    where
  /-- The relational weakest precondition transformer for a pair of
  monadic programs. -/
  rwpTrans {α β : Type u} : m₁ α → m₂ β → (α → β → Pred) → EPred₁ → EPred₂ → Pred
  /-- Soundness of `pure`: the joint postcondition applied to `(a, b)`
  implies the relational WP of `(pure a, pure b)`. -/
  rwp_trans_pure {α β : Type u} (a : α) (b : β) :
    ∀ post epost₁ epost₂,
      post a b ⊑ rwpTrans (pure a : m₁ α) (pure b : m₂ β) post epost₁ epost₂
  /-- Soundness of `bind`: composing relational WPs is at least as strong as
  the relational WP of the pair of `>>=`. -/
  rwp_trans_bind_le {α β γ δ : Type u}
    (x : m₁ α) (y : m₂ β) (f : α → m₁ γ) (g : β → m₂ δ) :
    ∀ post epost₁ epost₂,
      rwpTrans x y (fun a b => rwpTrans (f a) (g b) post epost₁ epost₂) epost₁ epost₂
        ⊑ rwpTrans (x >>= f) (y >>= g) post epost₁ epost₂
  /-- Monotonicity: weaker per-side exception postconditions and a weaker
  joint normal postcondition yield a weaker precondition. -/
  rwp_trans_monotone {α β : Type u} (x : m₁ α) (y : m₂ β)
    (post post' : α → β → Pred)
    (epost₁ epost₁' : EPred₁) (epost₂ epost₂' : EPred₂) :
    epost₁ ⊑ epost₁' → epost₂ ⊑ epost₂' → (∀ a b, post a b ⊑ post' a b) →
      rwpTrans x y post epost₁ epost₂ ⊑ rwpTrans x y post' epost₁' epost₂'

/-- User-facing relational weakest precondition. Compute the relational
WP of the pair `(x, y)` for joint normal postcondition `post`, left
exception postcondition `epost₁`, and right exception postcondition
`epost₂`. -/
def rwp
    {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂}
    {Pred : Type w} {EPred₁ : Type w₁} {EPred₂ : Type w₂}
    [Monad m₁] [Monad m₂]
    [LawfulMonad m₁] [LawfulMonad m₂]
    [Assertion Pred] [Assertion EPred₁] [Assertion EPred₂]
    [RelWP m₁ m₂ Pred EPred₁ EPred₂]
    {α β : Type u} (x : m₁ α) (y : m₂ β) (post : α → β → Pred)
    (epost₁ : EPred₁) (epost₂ : EPred₂) : Pred :=
  RelWP.rwpTrans x y post epost₁ epost₂

/-- Relational Hoare-style triple
`⦃pre⦄ x ~ y ⦃post | epost₁ | epost₂⦄`, defined as
`pre ⊑ rwp x y post epost₁ epost₂`. -/
def RelTriple
    {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂}
    {Pred : Type w} {EPred₁ : Type w₁} {EPred₂ : Type w₂}
    [Monad m₁] [Monad m₂]
    [LawfulMonad m₁] [LawfulMonad m₂]
    [Assertion Pred] [Assertion EPred₁] [Assertion EPred₂]
    [RelWP m₁ m₂ Pred EPred₁ EPred₂]
    {α β : Type u} (pre : Pred) (x : m₁ α) (y : m₂ β) (post : α → β → Pred)
    (epost₁ : EPred₁) (epost₂ : EPred₂) : Prop :=
  pre ⊑ rwp x y post epost₁ epost₂

namespace RelWP

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂}
variable {Pred : Type w} {EPred₁ : Type w₁} {EPred₂ : Type w₂}
variable [Monad m₁] [Monad m₂]
variable [LawfulMonad m₁] [LawfulMonad m₂]
variable [Assertion Pred] [Assertion EPred₁] [Assertion EPred₂]
variable [RelWP m₁ m₂ Pred EPred₁ EPred₂]
variable {α β γ δ : Type u}

/-!
## Derived Lemmas

One-directional consequences of the `RelWP` axioms for `pure`, `bind`,
monotonicity, and weakening, mirroring `Std.Do'.WP.{wp_pure, wp_bind,
wp_consequence, wp_econs, …}` in
`Loom.WP.Basic`.
-/

/-- Pure rule: the joint postcondition at `(a, b)` is below the
relational WP of `(pure a, pure b)`. -/
theorem rwp_pure (a : α) (b : β) (post : α → β → Pred)
    (epost₁ : EPred₁) (epost₂ : EPred₂) :
    post a b ⊑ rwp (pure a : m₁ α) (pure b : m₂ β) post epost₁ epost₂ :=
  rwp_trans_pure a b post epost₁ epost₂

/-- Bind rule: iterated relational WP is below the relational WP of the
joint `>>=`. -/
theorem rwp_bind_le
    (x : m₁ α) (y : m₂ β) (f : α → m₁ γ) (g : β → m₂ δ)
    (post : γ → δ → Pred) (epost₁ : EPred₁) (epost₂ : EPred₂) :
    rwp x y (fun a b => rwp (f a) (g b) post epost₁ epost₂) epost₁ epost₂
      ⊑ rwp (x >>= f) (y >>= g) post epost₁ epost₂ :=
  rwp_trans_bind_le x y f g post epost₁ epost₂

/-- Consequence rule for the joint normal postcondition. -/
theorem rwp_consequence
    (x : m₁ α) (y : m₂ β) (post post' : α → β → Pred)
    (epost₁ : EPred₁) (epost₂ : EPred₂)
    (h : ∀ a b, post a b ⊑ post' a b) :
    rwp x y post epost₁ epost₂ ⊑ rwp x y post' epost₁ epost₂ :=
  rwp_trans_monotone x y post post' epost₁ epost₁ epost₂ epost₂
    PartialOrder.rel_refl PartialOrder.rel_refl h

/-- Consequence rule on both exception postconditions plus the joint
normal postcondition. -/
theorem rwp_consequence_econs
    (x : m₁ α) (y : m₂ β) (post post' : α → β → Pred)
    (epost₁ epost₁' : EPred₁) (epost₂ epost₂' : EPred₂)
    (h : ∀ a b, post a b ⊑ post' a b)
    (h₁ : epost₁ ⊑ epost₁') (h₂ : epost₂ ⊑ epost₂') :
    rwp x y post epost₁ epost₂ ⊑ rwp x y post' epost₁' epost₂' :=
  rwp_trans_monotone x y post post' epost₁ epost₁' epost₂ epost₂' h₁ h₂ h

/-- Weaken the left exception postcondition. -/
theorem rwp_econs_left
    (x : m₁ α) (y : m₂ β) (post : α → β → Pred)
    (epost₁ epost₁' : EPred₁) (epost₂ : EPred₂)
    (h : epost₁ ⊑ epost₁') :
    rwp x y post epost₁ epost₂ ⊑ rwp x y post epost₁' epost₂ :=
  rwp_trans_monotone x y post post epost₁ epost₁' epost₂ epost₂
    h PartialOrder.rel_refl (fun _ _ => PartialOrder.rel_refl)

/-- Weaken the right exception postcondition. -/
theorem rwp_econs_right
    (x : m₁ α) (y : m₂ β) (post : α → β → Pred)
    (epost₁ : EPred₁) (epost₂ epost₂' : EPred₂)
    (h : epost₂ ⊑ epost₂') :
    rwp x y post epost₁ epost₂ ⊑ rwp x y post epost₁ epost₂' :=
  rwp_trans_monotone x y post post epost₁ epost₁ epost₂ epost₂'
    PartialOrder.rel_refl h (fun _ _ => PartialOrder.rel_refl)

/-- Pre-composing a stronger pre with a `RelTriple` keeps the same
consequence by transitivity. -/
theorem rwp_consequence_rel
    (x : m₁ α) (y : m₂ β) (post post' : α → β → Pred)
    (epost₁ : EPred₁) (epost₂ : EPred₂)
    (h : ∀ a b, post a b ⊑ post' a b) {pre : Pred}
    (h' : pre ⊑ rwp x y post epost₁ epost₂) :
    pre ⊑ rwp x y post' epost₁ epost₂ :=
  PartialOrder.rel_trans h' (rwp_consequence x y post post' epost₁ epost₂ h)

/-! ### Asynchronous (one-sided) bind rules

Direct corollaries of `rwp_bind_le` and `bind_pure`: chain a bind on
one side while the other side stays inert via `pure`. These are the
relational counterparts of SSProve's `apply_left` / `apply_right` and
Maillard et al.'s asynchronous bind shapes (Eqs. 5–6 of *The Next 700
Relational Program Logics*). -/

/-- Asynchronous bind on the left: the right side performs no bind. -/
theorem rwp_bind_left_le
    (x : m₁ α) (f : α → m₁ γ) (y : m₂ β) (post : γ → β → Pred)
    (epost₁ : EPred₁) (epost₂ : EPred₂) :
    rwp x y (fun a b => rwp (f a) (pure b : m₂ β) post epost₁ epost₂) epost₁ epost₂
      ⊑ rwp (x >>= f) y post epost₁ epost₂ := by
  have h := rwp_bind_le (γ := γ) (δ := β)
    (m₁ := m₁) (m₂ := m₂) x y f (fun b : β => (pure b : m₂ β))
    post epost₁ epost₂
  simpa [bind_pure] using h

/-- Asynchronous bind on the right: the left side performs no bind. -/
theorem rwp_bind_right_le
    (x : m₁ α) (y : m₂ β) (g : β → m₂ δ) (post : α → δ → Pred)
    (epost₁ : EPred₁) (epost₂ : EPred₂) :
    rwp x y (fun a b => rwp (pure a : m₁ α) (g b) post epost₁ epost₂) epost₁ epost₂
      ⊑ rwp x (y >>= g) post epost₁ epost₂ := by
  have h := rwp_bind_le (γ := α) (δ := δ)
    (m₁ := m₁) (m₂ := m₂) x y (fun a : α => (pure a : m₁ α)) g
    post epost₁ epost₂
  simpa [bind_pure] using h

end RelWP

/-! ### `RelTriple` variants

Hoare-style restatements of the `rwp_*` lemmas above. We use flat
snake_case names rather than `RelTriple.{pure, bind, …}` to avoid
shadowing `Pure.pure` and `Bind.bind` inside the `RelTriple` namespace
when later definitions in the same namespace need them. -/

variable {m₁ : Type u → Type v₁} {m₂ : Type u → Type v₂}
variable {Pred : Type w} {EPred₁ : Type w₁} {EPred₂ : Type w₂}
variable [Monad m₁] [Monad m₂]
variable [LawfulMonad m₁] [LawfulMonad m₂]
variable [Assertion Pred] [Assertion EPred₁] [Assertion EPred₂]
variable [RelWP m₁ m₂ Pred EPred₁ EPred₂]
variable {α β γ δ : Type u}

/-- Consequence rule for `RelTriple`: weaken pre, strengthen each post. -/
theorem relTriple_conseq {pre pre' : Pred} {x : m₁ α} {y : m₂ β}
    {post post' : α → β → Pred}
    {epost₁ epost₁' : EPred₁} {epost₂ epost₂' : EPred₂}
    (hpre : pre' ⊑ pre) (hpost : ∀ a b, post a b ⊑ post' a b)
    (h₁ : epost₁ ⊑ epost₁') (h₂ : epost₂ ⊑ epost₂')
    (h : RelTriple pre x y post epost₁ epost₂) :
    RelTriple pre' x y post' epost₁' epost₂' :=
  PartialOrder.rel_trans hpre
    (PartialOrder.rel_trans h
      (RelWP.rwp_consequence_econs x y post post' epost₁ epost₁' epost₂ epost₂' hpost h₁ h₂))

/-- Pure rule for `RelTriple`. -/
theorem relTriple_pure {pre : Pred} {a : α} {b : β}
    {post : α → β → Pred} {epost₁ : EPred₁} {epost₂ : EPred₂}
    (hpre : pre ⊑ post a b) :
    RelTriple pre (Pure.pure a : m₁ α) (Pure.pure b : m₂ β) post epost₁ epost₂ :=
  PartialOrder.rel_trans hpre (RelWP.rwp_pure a b post epost₁ epost₂)

/-- Bind rule for `RelTriple` with a `cut` joint postcondition. -/
theorem relTriple_bind {pre : Pred} {x : m₁ α} {y : m₂ β}
    {f : α → m₁ γ} {g : β → m₂ δ}
    {cut : α → β → Pred} {post : γ → δ → Pred}
    {epost₁ : EPred₁} {epost₂ : EPred₂}
    (hxy : RelTriple pre x y cut epost₁ epost₂)
    (hfg : ∀ a b, RelTriple (cut a b) (f a) (g b) post epost₁ epost₂) :
    RelTriple pre (x >>= f) (y >>= g) post epost₁ epost₂ := by
  have hcut : pre ⊑ rwp x y (fun a b => rwp (f a) (g b) post epost₁ epost₂) epost₁ epost₂ :=
    PartialOrder.rel_trans hxy (RelWP.rwp_consequence x y _ _ epost₁ epost₂ hfg)
  exact PartialOrder.rel_trans hcut (RelWP.rwp_bind_le x y f g post epost₁ epost₂)

/-- Asynchronous bind rule (left) for `RelTriple`. -/
theorem relTriple_bind_left {pre : Pred} {x : m₁ α} {y : m₂ β} {f : α → m₁ γ}
    {cut : α → β → Pred} {post : γ → β → Pred}
    {epost₁ : EPred₁} {epost₂ : EPred₂}
    (hxy : RelTriple pre x y cut epost₁ epost₂)
    (hf : ∀ a b, RelTriple (cut a b) (f a) (Pure.pure b : m₂ β) post epost₁ epost₂) :
    RelTriple pre (x >>= f) y post epost₁ epost₂ := by
  have hcut : pre ⊑
      rwp x y (fun a b => rwp (f a) (Pure.pure b : m₂ β) post epost₁ epost₂) epost₁ epost₂ :=
    PartialOrder.rel_trans hxy (RelWP.rwp_consequence x y _ _ epost₁ epost₂ hf)
  exact PartialOrder.rel_trans hcut (RelWP.rwp_bind_left_le x f y post epost₁ epost₂)

/-- Asynchronous bind rule (right) for `RelTriple`. -/
theorem relTriple_bind_right {pre : Pred} {x : m₁ α} {y : m₂ β} {g : β → m₂ δ}
    {cut : α → β → Pred} {post : α → δ → Pred}
    {epost₁ : EPred₁} {epost₂ : EPred₂}
    (hxy : RelTriple pre x y cut epost₁ epost₂)
    (hg : ∀ a b, RelTriple (cut a b) (Pure.pure a : m₁ α) (g b) post epost₁ epost₂) :
    RelTriple pre x (y >>= g) post epost₁ epost₂ := by
  have hcut : pre ⊑
      rwp x y (fun a b => rwp (Pure.pure a : m₁ α) (g b) post epost₁ epost₂) epost₁ epost₂ :=
    PartialOrder.rel_trans hxy (RelWP.rwp_consequence x y _ _ epost₁ epost₂ hg)
  exact PartialOrder.rel_trans hcut (RelWP.rwp_bind_right_le x y g post epost₁ epost₂)

end Std.Do'
