/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Loom.PredTrans
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.Do'

/-!
# Weakest Precondition Interpretation

This module defines the weakest precondition interpretation `WP` of monadic programs
in terms of predicate transformers `PredTrans`.

An instance `WP m Pred EPred` determines a function `wpTrans : m α → PredTrans Pred EPred α` that
interprets a program `x : m α` as a predicate transformer. The function `wp` is the
user-facing wrapper: `wp x post epost` computes the weakest precondition for `x` to
satisfy normal postcondition `post` and exception postcondition `epost`.

## Assertion Language Classes

`Assertion` and `Assertion` are both just alias type classes for `CompleteLattice`.
We introduce them for readability: `Assertion Pred` marks `Pred` as the assertion language for
normal postconditions, while `Assertion EPred` marks `EPred` as the type of exception
postconditions.

## Pre-defined instances

* `WP Id Prop EPost.nil` — pure computations.
* `WP (StateT σ m) (σ → Pred) EPred` — stateful computations.
* `WP (ExceptT ε m) Pred (EPost.cons (ε → Pred) EPred)` — computations with exceptions.
* `WP (ReaderT ρ m) (ρ → Pred) EPred` — reader computations.
* `WP (Except ε) Prop EPost⟨ε → Prop⟩` — concrete exception type.
* `WP (EStateM ε σ) (σ → Prop) (ε → σ → Prop)` — concrete error-state monad.
-/

namespace Std.Do'

variable {m : Type u → Type z}

/-- An assertion type is equipped with a `CompleteLattice` structure,
used as the carrier for pre- and postconditions. -/
class abbrev Assertion (α : Type w) := CompleteLattice α

/-- An assertion type is a chain-complete partial order. -/
scoped instance [Assertion EPred] : CCPO EPred where
  has_csup {c} _ := CompleteLattice.has_sup c

/-!
## WP Typeclass

The `WP` typeclass defines weakest precondition semantics for monads.
A `WP m Pred EPred` instance provides a monad morphism `wpTrans : m α → PredTrans Pred EPred α`
satisfying:
- `wp_trans_pure`: `pure x` is at least as strong as its predicate transformer.
- `wp_trans_bind`: sequential composition is sound.
- `wp_trans_monotone`: the transformer is monotone in both postconditions.
-/

/-- Weakest precondition monad: a monad `m` with a sound interpretation as predicate
transformers over assertion language `Pred` with exception postconditions `EPred`. -/
class WP (m : Type u → Type v) (Pred : outParam (Type w)) (EPred : outParam (Type w'))
    [Monad m] [Assertion Pred] [Assertion EPred] extends LawfulMonad m where
  /-- The weakest precondition transformer for a monadic program. -/
  wpTrans : m α → PredTrans Pred EPred α
  /-- Soundness of `pure`: the postcondition applied to `x` implies the WP of `pure x`. -/
  wp_trans_pure (x : α) : pure x ⊑ wpTrans (pure (f := m) x)
  /-- Soundness of `bind`: composing WPs is at least as strong as the WP of `>>=`. -/
  wp_trans_bind (x : m α) (f : α → m β) :
    wpTrans x >>= (wpTrans <| f ·) ⊑ wpTrans (x >>= f)
  /-- Monotonicity: weaker postconditions yield weaker preconditions. -/
  wp_trans_monotone (x : m α) : wpTrans x |>.monotone

/-- Compute the weakest precondition of `x` for normal postcondition `post` and
exception postcondition `epost`. -/
def wp [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] {α} (x : m α) (post : α → Pred) (epost : EPred) : Pred :=
  (WP.wpTrans x).apply post epost

@[simp, grind =] theorem WP.wp_impl_eq_wp [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] {α} (x : m α) :
  (WP.wpTrans x).apply = wp x := rfl

/-!
## Derived WP Lemmas

One-directional consequences of the `WP` axioms for `pure`, `bind`, monotonicity,
and weakening.
-/

theorem WP.wp_pure [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : α) (post : α → Pred) (epost : EPred) :
    post x ⊑ wp (pure (f := m) x) post epost := wp_trans_pure x post epost

theorem WP.wp_bind [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : m α) (f : α → m β)
  (post : β → Pred) (epost : EPred) :
    wp x (fun x => wp (f x) post epost) epost ⊑ wp (x >>= f) post epost :=
  wp_trans_bind x f post epost

theorem WP.wp_consequence [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : m α)
  (post post' : α → Pred) (epost : EPred) (h : post ⊑ post') :
    wp x post epost ⊑ wp x post' epost :=
  WP.wp_trans_monotone x post post' epost epost PartialOrder.rel_refl h

theorem WP.wp_consequence_econs [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : m α)
  (post post' : α → Pred) (epost epost' : EPred) (h : post ⊑ post') (h' : epost ⊑ epost') :
    wp x post epost ⊑ wp x post' epost' :=
  WP.wp_trans_monotone x post post' epost epost' h' h

theorem WP.wp_econs [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : m α)
  (post : α → Pred) (epost epost' : EPred) (h' : epost ⊑ epost') :
    wp x post epost ⊑ wp x post epost' :=
  WP.wp_trans_monotone x post post epost epost' h' PartialOrder.rel_refl

theorem WP.wp_econs_bot [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : m α)
  (post : α → Pred) (epost : EPred) :
    wp x post ⊥ ⊑ wp x post epost := by
  solve_by_elim [WP.wp_econs, bot_le]

theorem WP.wp_consequence_rel [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : m α)
  (post post' : α → Pred) (epost : EPred) (h : post ⊑ post') {pre : Pred}
    (h' : pre ⊑ wp x post epost) :
    pre ⊑ wp x post' epost :=
  PartialOrder.rel_trans h' (WP.wp_consequence x post post' epost h)

theorem WP.wp_econs_rel [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : m α)
  (post : α → Pred) (epost epost' : EPred) (h : epost ⊑ epost') {pre : Pred}
    (h' : pre ⊑ wp x post epost) :
    pre ⊑ wp x post epost' :=
  PartialOrder.rel_trans h' (WP.wp_econs x post epost epost' h)

theorem WP.wp_econs_bot_rel [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : m α)
  (post : α → Pred) (epost : EPred) {pre : Pred} (h : pre ⊑ wp x post ⊥) :
    pre ⊑ wp x post epost :=
  PartialOrder.rel_trans h (WP.wp_econs_bot x post epost)

/-!
## Derived Theorems for `map` and `seq`

One direction of the derived theorems `wp_map` and `wp_seq`. The full bidirectional
equality from `Std.Do` cannot be proven with our current axioms since `wp_bind` only
gives one direction (`⊑`).
-/

theorem WP.wp_map [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (f : α → β) (x : m α) :
  ∀ post epost, wp x (fun a => post (f a)) epost ⊑ wp (f <$> x) post epost := by
  intro post epost
  rw [← bind_pure_comp]
  apply PartialOrder.rel_trans; rotate_left
  exact WP.wp_trans_bind x (pure <| f ·) post epost
  apply WP.wp_consequence
  intro a; exact WP.wp_trans_pure (f a) post epost

theorem WP.wp_map' [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (f : α → β) (x : m α) :
  ∀ post post' epost (_ : post = fun a => post' (f a)),
    wp x post epost ⊑ wp (f <$> x) post' epost := by
  intro post post' epost h
  subst h
  apply wp_map

theorem WP.wp_seq [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (f : m (α → β)) (x : m α) :
  ∀ post epost,
    wp f (fun g => wp x (fun a => post (g a)) epost) epost ⊑
      wp (f <*> x) post epost := by
  intro post epost
  rw [← bind_map]
  apply PartialOrder.rel_trans _ (WP.wp_bind f (fun g => g <$> x) post epost)
  apply WP.wp_consequence; intro g; exact WP.wp_map g x post epost

/-!
## WP Instances
-/

/-- `Id` is a WP with `Prop` assertions and no exceptions. -/
instance Id.instWP : WP Id.{u} Prop EPost.nil where
  wpTrans x := ⟨fun post _epost => post x⟩
  wp_trans_pure _x := PartialOrder.rel_refl
  wp_trans_bind _x _f := PartialOrder.rel_refl
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x

@[simp, grind =]
theorem apply_pushExcept {α ε Pred EPred}
    (x : PredTrans Pred EPred (Except ε α)) (post : α → Pred)
    (epost : EPost.cons (ε → Pred) EPred) :
    (PredTrans.pushExcept x).apply post epost = x.apply (epost.pushExcept post) epost.tail := rfl

/-- `ExceptT` lifts a `WP` instance by adding an exception postcondition layer. -/
instance ExceptT.instWP {Pred : Type v}
  [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] :
    WP (ExceptT ε m) Pred (EPost.cons (ε → Pred) EPred) where
  wpTrans x := PredTrans.pushExcept (WP.wpTrans x.run)
  wp_trans_pure x := fun post epost =>
    WP.wp_pure (m := m) (Except.ok x) (epost.pushExcept post) epost.tail
  wp_trans_bind x f := fun post epost => by
    simp only [apply_pushExcept, ExceptT.run_bind]
    apply PartialOrder.rel_trans _ (WP.wp_bind (m := m) x ..)
    apply WP.wp_consequence (m := m)
    · intro r; cases r with
      | ok a => exact PartialOrder.rel_refl
      | error el =>
        exact WP.wp_pure (m := m) (Except.error el) (epost.pushExcept post) epost.tail
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    change wp x.run (epost.pushExcept post) epost.tail ⊑
           wp x.run (epost'.pushExcept post') epost'.tail
    have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := by
      simpa [PartialOrder.rel, meet_prop_eq_and] using hepost
    let hhead := hepost'.1
    let htail := hepost'.2
    apply WP.wp_consequence_econs (m := m) (x := x.run)
    · intro r
      cases r with
      | ok a => exact hpost a
      | error el => exact hhead el
    · exact htail

@[simp, grind =]
theorem ExceptT.apply_wp {α ε Pred EPred}
  [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : ExceptT ε m α)
  (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    wp x post epost = wp x.run (epost.pushExcept post) epost.tail := rfl

/-- `OptionT` lifts a `WP` instance by adding a `PUnit` exception postcondition layer. -/
instance OptionT.instWP {Pred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] :
    WP (OptionT m) Pred (EPost.cons Pred EPred) where
  wpTrans x := PredTrans.pushOption (WP.wpTrans x.run)
  wp_trans_pure x := fun post epost =>
    WP.wp_pure (m := m) (some x) (epost.pushOption post) epost.tail
  wp_trans_bind x f := fun post epost => by
    simp only [PredTrans.apply_pushOption, OptionT.run_bind]
    apply PartialOrder.rel_trans _ (WP.wp_bind (m := m) x ..)
    apply WP.wp_consequence (m := m)
    · intro r; cases r with
      | some a => exact PartialOrder.rel_refl
      | none =>
        exact WP.wp_pure (m := m) none (epost.pushOption post) epost.tail
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    change wp x.run (epost.pushOption post) epost.tail ⊑
           wp x.run (epost'.pushOption post') epost'.tail
    have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := hepost
    apply WP.wp_consequence_econs (m := m) (x := x.run)
    · intro r; cases r with
      | some a => exact hpost a
      | none => exact hepost'.1
    · exact hepost'.2

@[simp, grind =]
theorem OptionT.apply_wp {α : Type u} {Pred : Type u} {EPred}
  [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : OptionT m α)
  (post : α → Pred) (epost : EPost.cons Pred EPred) :
    wp x post epost = wp x.run (epost.pushOption post) epost.tail := rfl

/-- `StateT` lifts a `WP` instance by adding a state argument. -/
instance (priority := low) StateT.instWP {EPred : Type v} {σ : Type u} {Pred : Type w}
  [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] :
    WP (StateT σ m) (σ → Pred) EPred where
  wpTrans x := pushArg (WP.wpTrans <| x.run ·)
  wp_trans_pure x := fun post epost s =>
    WP.wp_pure (m := m) (x, s) (fun p => post p.1 p.2) epost
  wp_trans_bind x f := fun post epost s => by
    simp only [apply_pushArg, StateT.run_bind]
    apply WP.wp_bind
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    apply WP.wp_consequence_econs (m := m) (x := x.run s)
    · intro ⟨a, s'⟩
      exact hpost a s'
    · exact hepost

@[simp, grind =]
theorem StateT.apply_wp {σ : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : StateT σ m α)
  (post : α → σ → Pred) (epost : EPred) (s : σ) :
    wp x post epost s = wp (x.run s) (fun (a, s) => post a s) epost := rfl

/-- `ReaderT` lifts a `WP` instance by adding a reader argument. -/
instance ReaderT.instWP {Pred : Type v}
  [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] :
    WP (ReaderT ρ m) (ρ → Pred) EPred where
  wpTrans x := ⟨fun post epost r => wp (x.run r) (fun a => post a r) epost⟩
  wp_trans_pure x := fun post epost r =>
    WP.wp_pure (m := m) x (fun a => post a r) epost
  wp_trans_bind x f := fun post epost r => by
    simp only [ReaderT.run_bind]
    apply PartialOrder.rel_trans
    · apply WP.wp_consequence (m := m)
      intro a; exact PartialOrder.rel_refl
    · apply WP.wp_bind
  wp_trans_monotone x := fun post post' epost epost' hepost hpost r => by
    apply WP.wp_consequence_econs (m := m) (x := x.run r)
    · intro a
      exact hpost a r
    · exact hepost

@[simp, grind =]
theorem ReaderT.apply_wp {ρ : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] (x : ReaderT ρ m α)
  (post : α → ρ → Pred) (epost : EPred) (r : ρ) :
    wp x post epost r = wp (x.run r) (fun a => post a r) epost := rfl

/-!
## Type Alias Instances

`WP` instances for concrete monads that are type aliases for transformer stacks.
-/

/-- `Option` is a WP with `Prop` assertions and a single `Prop` exception postcondition. -/
instance Option.instWP : WP Option.{u} Prop Prop where
  wpTrans x := ⟨fun post epost => x.elim epost post⟩
  wp_trans_pure x := PartialOrder.rel_refl
  wp_trans_bind x f := fun post epost => by cases x <;> exact id
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    cases x with
    | none => exact hepost
    | some a => exact hpost a

/-- `Except ε` is a WP with `Prop` assertions and a single exception postcondition. -/
instance Except.instWP : WP (Except ε) Prop EPost⟨ε → Prop⟩ where
  wpTrans x := ⟨fun post epost => match x with
    | .ok a => post a
    | .error el => epost.head el⟩
  wp_trans_pure x := PartialOrder.rel_refl
  wp_trans_bind x f := fun post epost => by cases x <;> exact id
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    cases x with
    | ok a => exact hpost a
    | error el =>
      have hhead : epost.head ⊑ epost'.head := by
        have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := by
          simpa [PartialOrder.rel, meet_prop_eq_and] using hepost
        exact hepost'.1
      exact hhead el

/-- `EStateM ε σ` is a WP combining state and exceptions. -/
instance EStateM.instWP : WP (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  wpTrans x := ⟨fun post epost s => match x s with
    | .ok a s' => post a s'
    | .error el s' => epost el s'⟩
  wp_trans_pure x := fun post epost s => PartialOrder.rel_refl
  wp_trans_bind x f := fun post epost s => by
    simp only [bind, EStateM.bind]
    cases (x s) <;> exact PartialOrder.rel_refl
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    cases hxs : x s with
    | ok a s' =>
      simpa [hxs] using hpost a s'
    | error el s' =>
      simpa [hxs] using hepost el s'

/-!
## Adequacy Lemmas

These lemmas bridge `wp` reasoning to concrete program properties. Each one says:
if `wp prog ...` holds, then a property `P` holds of the program's result.
-/

theorem Id.of_wp_run_eq {α : Type u} {x : α} {prog : Id α}
  (h : Id.run prog = x) (P : α → Prop)
  (hwp : wp prog P EPost.nil.mk) : P x := by
  rw [← h]
  exact hwp

theorem Option.of_wp_eq {α : Type u} {x prog : Option α}
  (h : prog = x) (P : Option α → Prop)
  (hwp : wp prog (fun a => P (some a)) (P none)) : P x := by
  subst h
  cases prog with
  | none => exact hwp
  | some a => exact hwp

theorem StateM.of_wp_run_eq {x : α × σ} {prog : StateM σ α} {s : σ}
  (h : StateT.run prog s = x) (P : α × σ → Prop)
  (hwp : wp prog (fun a s' => P (a, s')) EPost.nil.mk s) : P x := by
  rw [← h]
  exact hwp

theorem StateM.of_wp_run'_eq {α σ : Type} {x : α} {prog : StateM σ α} {s : σ}
  (h : StateT.run' prog s = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) EPost.nil.mk s) : P x := by
  rw [← h]
  exact hwp

theorem ReaderM.of_wp_run_eq {α ρ : Type} {x : α} {prog : ReaderM ρ α} {r : ρ}
  (h : ReaderT.run prog r = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) EPost.nil.mk r) : P x := by
  rw [← h]
  exact hwp

theorem Except.of_wp_eq {ε α : Type} {x prog : Except ε α}
  (h : prog = x) (P : Except ε α → Prop)
  (hwp : wp prog (fun a => P (.ok a)) epost⟨fun e => P (.error e)⟩) : P x := by
  subst h
  cases prog with
  | ok a => simpa only [wp] using hwp
  | error e => simpa only [wp] using hwp

theorem EStateM.of_wp_run_eq {ε σ α : Type} {x : EStateM.Result ε σ α}
  {prog : EStateM ε σ α} {s : σ}
  (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop)
  (hwp : wp prog (fun a s' => P (.ok a s')) (fun e s' => P (.error e s')) s) :
    P x := by
  rw [← h]
  change P (prog s)
  cases heq : prog s with
  | ok a s' =>
    simpa [wp, WP.wpTrans, heq] using hwp
  | error e s' =>
    simpa [wp, WP.wpTrans, heq] using hwp

end Std.Do'
