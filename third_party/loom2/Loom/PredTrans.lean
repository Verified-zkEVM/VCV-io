/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Loom.LatticeExt
public import Loom.ExceptPost
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order

/-!
# Predicate Transformers

This module defines the type `PredTrans Pred EPred α` of *predicate transformers* for weakest
precondition reasoning over monadic programs with exception postconditions.

A predicate transformer `x : PredTrans Pred EPred α` takes a normal postcondition `post : α → Pred`,
an exception postcondition `epost : EPred`, and returns a precondition of type `Pred`.

`PredTrans` forms a monad, so monadic programs can be interpreted by a monad morphism into
`PredTrans`; this is exactly what `WP` encodes.

## Main definitions

- `PredTrans Pred EPred α` — the type of monotone predicate transformers
- `PredTrans.pushExcept` — adds an exception layer to a predicate transformer
- `pushArg` — adds a state argument to a predicate transformer
- Instances for `Monad`, `LawfulMonad`, `MonadStateOf`, `MonadExceptOf`, etc.
-/

namespace Std.Do'

/-- A monotone predicate transformer from postconditions to preconditions.

Given a return type `α`, a lattice `Pred` for assertions, and an exception assertion type `EPred`,
`PredTrans Pred EPred α` wraps a function `(α → Pred) → EPred → Pred`. -/
structure PredTrans (Pred : Type u) (EPred : Type v) (α : Type w) where
  /-- Apply the predicate transformer to a postcondition and exception postcondition. -/
  apply : (α → Pred) → EPred → Pred

/-- Extensionality for predicate transformers. -/
@[ext] theorem PredTrans.ext {x y : PredTrans Pred EPred α}
    (h : ∀ post epost, x.apply post epost = y.apply post epost) : x = y := by
  cases x; cases y; congr; funext post epost; exact h post epost

/-- Partial order on predicate transformers, inherited from the function space. -/
instance [PartialOrder Pred] : PartialOrder (PredTrans Pred EPred α) where
  rel x y := x.apply ⊑ y.apply
  rel_refl := PartialOrder.rel_refl
  rel_trans h1 h2 := PartialOrder.rel_trans h1 h2
  rel_antisymm h1 h2 := PredTrans.ext fun post epost =>
    PartialOrder.rel_antisymm (h1 post epost) (h2 post epost)

/-- Chain-complete partial order on predicate transformers, for fixed-point reasoning. -/
instance [CCPO Pred] : CCPO (PredTrans Pred EPred α) where
  has_csup {c} hc := by
    let c' : ((α → Pred) → EPred → Pred) → Prop := fun f => ∃ pt, c pt ∧ pt.apply = f
    have hc' : chain c' := by
      intro _ _ ⟨pf, hpf, hpf_eq⟩ ⟨pg, hpg, hpg_eq⟩
      subst hpf_eq; subst hpg_eq
      exact hc pf pg hpf hpg
    obtain ⟨sup, hsup⟩ := CCPO.has_csup hc'
    refine ⟨⟨sup⟩, fun q => ?_⟩
    constructor
    · intro h pt hpt
      exact (hsup q.apply).mp h pt.apply ⟨pt, hpt, rfl⟩
    · intro h
      exact (hsup q.apply).mpr fun f ⟨pf, hpf, hpf_eq⟩ => by subst hpf_eq; exact h pf hpf

/-- `Monad` instance for `PredTrans`: `pure` returns the postcondition applied to the value,
and `bind` threads the postcondition through the continuation. -/
instance instMonadPredTrans (Pred : Type u) (EPred : Type v) : Monad (PredTrans Pred EPred) where
  pure x := ⟨fun post _epost => post x⟩
  bind x f := ⟨fun post epost => x.apply (fun a => (f a).apply post epost) epost⟩

/-- `PredTrans` is a lawful monad: all monad laws hold definitionally. -/
instance instLawfulMonadPredTrans (Pred : Type u) (EPred : Type v) : LawfulMonad (PredTrans Pred EPred) where
  map_const := funext fun _ => funext fun _ => PredTrans.ext fun _ _ => rfl
  id_map _ := PredTrans.ext fun _ _ => rfl
  seqLeft_eq _ _ := PredTrans.ext fun _ _ => rfl
  seqRight_eq _ _ := PredTrans.ext fun _ _ => rfl
  pure_seq _ _ := PredTrans.ext fun _ _ => rfl
  bind_pure_comp _ _ := PredTrans.ext fun _ _ => rfl
  bind_map _ _ := PredTrans.ext fun _ _ => rfl
  pure_bind _ _ := PredTrans.ext fun _ _ => rfl
  bind_assoc _ _ _ := PredTrans.ext fun _ _ => rfl

/-- Monotonicity property for a predicate transformer: if both `post` and `epost` grow,
then the resulting precondition grows. -/
def PredTrans.monotone [PartialOrder Pred] [PartialOrder EPred] (pt : PredTrans Pred EPred α) :=
  ∀ post post' epost epost', epost ⊑ epost' → post ⊑ post' → pt.apply post epost ⊑ pt.apply post' epost'

/-!
## `apply_*` simp framework

Simp lemmas for reducing `(expr).apply post epost` for each monadic combinator.
-/

/-- Unfolding `pure` through `apply`. -/
@[simp, grind =]
theorem PredTrans.apply_pure {Pred : Type u} {EPred : Type v}
    (a : α) (post : α → Pred) (epost : EPred) :
    (pure a : PredTrans Pred EPred α).apply post epost = post a := rfl

/-- Unfolding `>>=` through `apply`. -/
@[simp, grind =]
theorem PredTrans.apply_bind {Pred : Type u} {EPred : Type v}
    (x : PredTrans Pred EPred α) (f : α → PredTrans Pred EPred β)
    (post : β → Pred) (epost : EPred) :
    (x >>= f).apply post epost = x.apply (fun a => (f a).apply post epost) epost := rfl

/-- Unfolding `<$>` through `apply`. -/
@[simp, grind =]
theorem PredTrans.apply_map {Pred : Type u} {EPred : Type v} {α : Type w}
    (trans : PredTrans Pred EPred α) (f : α → β) (post : β → Pred) (epost : EPred) :
    (f <$> trans).apply post epost = trans.apply (post ∘ f) epost := rfl

/-- Unfolding `<*>` through `apply`. -/
@[simp]
theorem PredTrans.apply_seq {Pred : Type u} {EPred : Type v}
    (f : PredTrans Pred EPred (α → β)) (x : PredTrans Pred EPred α)
    (post : β → Pred) (epost : EPred) :
    (f <*> x).apply post epost =
      f.apply (fun g => x.apply (fun a => post (g a)) epost) epost := rfl

/-- Unfolding `dite` through `apply`. -/
@[simp]
theorem PredTrans.apply_dite {Pred : Type u} {EPred : Type v}
    (c : Prop) [Decidable c]
    (t : c → PredTrans Pred EPred α) (e : ¬ c → PredTrans Pred EPred α)
    (post : α → Pred) (epost : EPred) :
    (if h : c then t h else e h).apply post epost =
      if h : c then (t h).apply post epost else (e h).apply post epost := by
  split <;> rfl

/-- Unfolding `ite` through `apply`. -/
@[simp]
theorem PredTrans.apply_ite {Pred : Type u} {EPred : Type v}
    (c : Prop) [Decidable c]
    (t : PredTrans Pred EPred α) (e : PredTrans Pred EPred α)
    (post : α → Pred) (epost : EPred) :
    (if c then t else e).apply post epost =
      if c then t.apply post epost else e.apply post epost := by
  split <;> rfl

/-!
## Exception Handling

Definitions for pushing and lifting exception layers through predicate transformers.
-/

/-- Push an `Except ε α` result into separate normal and exception postconditions:
`ok a` uses `post a`, and `error e` uses `epost.head e`. -/
@[simp]
abbrev EPost.cons.pushExcept {α : Type u} {ε : Type v} {Pred : Type w} {EPred : Type z}
    (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) : Except ε α → Pred :=
  fun
  | .ok a => post a
  | .error e => epost.head e

/-- Adds an exception layer to a predicate transformer.

Given a transformer over `Except ε α`, produces one over `α` with an additional
exception postcondition for `ε`. The normal and error postconditions are combined
via `pushExcept`. -/
def PredTrans.pushExcept {α : Type u} {ε : Type v} {Pred : Type w} {EPred : Type z}
    (x : PredTrans Pred EPred (Except ε α)) : PredTrans Pred (EPost.cons (ε → Pred) EPred) α :=
  ⟨fun post epost => x.apply (epost.pushExcept post) epost.tail⟩

/-- Push an `Option α` result into separate normal and none postconditions:
`some a` uses `post a`, and `none` uses `epost.head`. -/
@[simp]
abbrev EPost.cons.pushOption {α : Type u} {Pred : Type u} {EPred : Type v}
    (post : α → Pred) (epost : EPost.cons Pred EPred) : Option α → Pred :=
  fun
  | .some a => post a
  | .none => epost.head

/-- Adds an early-termination layer to a predicate transformer, modelling `Option` as
early termination. Given a transformer over `Option α`, produces one over `α` with an
additional exception postcondition for the `none` case. -/
def PredTrans.pushOption {α : Type u} {Pred : Type u} {EPred : Type v}
    (x : PredTrans Pred EPred (Option α)) : PredTrans Pred (EPost.cons Pred EPred) α :=
  ⟨fun post epost => x.apply (epost.pushOption post) epost.tail⟩

/-- Unfolding `pushOption` through `apply`. -/
@[simp, grind =]
theorem PredTrans.apply_pushOption {α : Type u} {Pred : Type u} {EPred : Type v}
    (x : PredTrans Pred EPred (Option α)) (post : α → Pred)
    (epost : EPost.cons Pred EPred) :
    (PredTrans.pushOption x).apply post epost = x.apply (epost.pushOption post) epost.tail := rfl

/-- Lift a predicate transformer to one with an additional exception layer,
ignoring the new exception postcondition. -/
instance {ε : Type v} {Pred : Type w} {EPred : Type z} :
    MonadLift (PredTrans Pred EPred) (PredTrans Pred (EPost.cons (ε → Pred) EPred)) where
  monadLift x := ⟨fun post epost => x.apply post epost.tail⟩

/-!
## State Handling

Definitions for adding state arguments to predicate transformers.
-/

/-- Adds a state argument to a predicate transformer.

Given a state-dependent transformer `σ → PredTrans l e (α × σ)`, produces a transformer
over `σ → l` that threads the state through postconditions. -/
def pushArg {σ : Type u} {Pred : Type v} {EPred : Type w} {α : Type z}
    (x : σ → PredTrans Pred EPred (α × σ)) : PredTrans (σ → Pred) EPred α :=
  ⟨fun post epost s => (x s).apply (fun (a, s) => post a s) epost⟩

/-- Lift a predicate transformer to one with a state argument,
pairing the result with the original state. -/
instance {σ : Type u} {Pred : Type v} {EPred : Type w}
    : MonadLift (PredTrans Pred EPred) (PredTrans (σ → Pred) EPred) where
  monadLift x := pushArg fun s => ⟨fun post epost => x.apply (fun x => post (x, s)) epost⟩

/-- Unfolding lemma for `pushArg`: applies the state-threaded transformer at state `s`. -/
@[simp, grind =]
theorem apply_pushArg {σ : Type u} {Pred : Type v} {EPred : Type w} {α : Type z}
    (x : σ → PredTrans Pred EPred (α × σ)) (post : α → σ → Pred) (epost : EPred) (s : σ) :
    (pushArg x).apply post epost s = (x s).apply (fun (a, s) => post a s) epost := rfl

/-- Lift a predicate transformer to one with a state argument (pointwise). -/
instance {σ : Type u} {Pred : Type v} {EPred : Type w} :
    MonadLift (PredTrans Pred EPred) (PredTrans (σ → Pred) EPred) where
  monadLift x := ⟨fun post epost s => x.apply (fun a => post a s) epost⟩

/-- Lift a predicate transformer to one with an additional exception layer (high priority). -/
instance (priority := high) {ε : Type u} {Pred : Type u} {EPred : Type u} :
    MonadLift (PredTrans Pred EPred) (PredTrans Pred (EPost.cons (ε → Pred) EPred)) where
  monadLift x := ⟨fun post epost => x.apply post epost.tail⟩

/-!
## Monad Instances

Standard monad class instances for `PredTrans`.
-/

/-- `MonadStateOf` instance: `get` returns the state, `set` replaces it,
`modifyGet` applies a function to the state. -/
instance {σ : Type u} {Pred : Type v} {EPred : Type w} :
    MonadStateOf σ (PredTrans (σ → Pred) EPred) where
  get := ⟨fun post _epost => fun s => post s s⟩
  set s := ⟨fun post _epost => fun _ => post ⟨⟩ s⟩
  modifyGet f := ⟨fun post _epost => fun s => post (f s).1 (f s).2⟩

/-- `MonadReaderOf` instance: `read` provides the state without consuming it. -/
instance {σ : Type u} {Pred : Type v} {EPred : Type w} :
    MonadReaderOf σ (PredTrans (σ → Pred) EPred) where
  read := ⟨fun post _epost => fun s => post s s⟩

/-- `MonadExceptOf` instance for the outermost exception layer:
`throw` invokes the head exception postcondition, `tryCatch` intercepts it. -/
instance {ε : Type u} {Pred : Type v} {EPred : Type w} :
    MonadExceptOf ε (PredTrans Pred (EPost.cons (ε → Pred) EPred)) where
  throw e := ⟨fun _post epost => epost.head e⟩
  tryCatch x handle := ⟨fun post epost => x.apply post ⟨(fun e => (handle e).apply post epost), epost.tail⟩⟩

/-- `MonadExceptOf` instance lifted through a state layer:
delegates `throw` and `tryCatch` to the inner `PredTrans l e` instance. -/
instance {ε : Type u} {Pred : Type v} {EPred : Type w} {σ : Type z}
    [MonadExceptOf ε (PredTrans Pred EPred)] :
    MonadExceptOf ε (PredTrans (σ → Pred) EPred) where
  throw {α} x := ⟨fun post epost s =>
    (throw (m := PredTrans Pred EPred) (α := α) x).apply (post · s) epost⟩
  tryCatch x handle := ⟨fun post epost s =>
    (tryCatch (m := PredTrans Pred EPred)
      (⟨fun post epost => x.apply (fun r s => post (r, s)) epost s⟩)
      (fun e => ⟨fun post epost => (handle e).apply (fun r s => post (r, s)) epost s⟩)).apply
      (fun rs => post rs.1 rs.2) epost⟩

/-- `MonadExceptOf` instance lifted through an unrelated exception layer:
delegates to the inner instance, threading the extra exception postcondition. -/
instance {ε : Type u} {Pred : Type v} {EPred : Type w} {ε' : Type u}
    [MonadExceptOf ε (PredTrans Pred EPred)] :
    MonadExceptOf ε (PredTrans Pred (EPost.cons (ε' → Pred) EPred)) where
  throw x := ⟨fun post epost => (throw (m := PredTrans Pred EPred) x).apply post epost.tail⟩
  tryCatch x handle := ⟨fun post epost =>
    (tryCatch (m := PredTrans Pred EPred)
      (⟨fun post' epost' => x.apply post' ⟨epost.head, epost'⟩⟩)
      (fun e => ⟨fun post' epost' => (handle e).apply post' ⟨epost.head, epost'⟩⟩)).apply
      post epost.tail⟩

end Std.Do'
