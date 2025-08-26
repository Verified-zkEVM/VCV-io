/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Logic.Equiv.Prod

/-! # Comonads

This file defines the `Comonad` typeclass hierarchy, dual to `Monad`.

It follows the structure of the `Monad` hierarchy:
`Extract` (`pure`), `Extend` (`bind`), `Coseq` (`seq`),
`Coapplicative` (`Applicative`), `Comonad` (`Monad`).

## Hierarchy

* `Extract (w)`: Provides `extract : w α → α`.
* `Extend (w)`: Provides `extend : w α → (w α → β) → w β`.
* `Coseq (w)`: Provides `coseq : w α → w β → w (α × β)` (operator `<@>`).
* `CoseqLeft (w)`: Provides `coseqLeft : w α → w β → w α` (operator `<@`).
* `CoseqRight (w)`: Provides `coseqRight : w α → w β → w β` (operator `@>`).
* `Coapplicative (w)`: Extends `Functor`, `Extract`, `Coseq`, `CoseqLeft`, `CoseqRight`.
* `Comonad (w)`: Extends `Coapplicative`, `Extend`. Provides default `map`.
* `Lawful` variants mirroring `LawfulFunctor`, `LawfulApplicative`, `LawfulMonad`.

-/

universe u v z

/-- The `Extract` typeclass provides the `extract` operation, dual to `Pure.pure`. -/
class Extract (w : Type u → Type v) where
  /-- Extract a value from the comonadic context. -/
  extract {α : Type u} : w α → α

/-- The `Extend` typeclass provides the `extend` operation, dual to `Bind.bind`. -/
class Extend (w : Type u → Type v) where
  /-- Extend a function across the comonadic context. -/
  extend {α β : Type u} : w α → (w α → β) → w β

/-- The `Coseq` typeclass provides the `coseq` operation (`<@>`), dual to `Seq.seq` (`<*>`).
    It combines two comonadic contexts, pairing their results. -/
class Coseq (w : Type u → Type v) where
  /-- Combine two comonadic contexts. -/
  coseq : {α β : Type u} → w α → w β → w (α × β)

/-- The `CoseqLeft` typeclass provides the `coseqLeft` operation (`<@`), dual to `SeqLeft.seqLeft`
  (`<*`). Evaluates two contexts but returns the result of the first. -/
class CoseqLeft (w : Type u → Type v) where
  /-- Evaluate two contexts, returning the first result. -/
  coseqLeft : {α β : Type u} → w α → w β → w α

/-- The `CoseqRight` typeclass provides the `coseqRight` operation (`@>`), dual to
  `SeqRight.seqRight` (`*>`). Evaluates two contexts but returns the result of the second. -/
class CoseqRight (w : Type u → Type v) where
  /-- Evaluate two contexts, returning the second result. -/
  coseqRight : {α β : Type u} → w α → w β → w β

export Extract (extract)
export Extend (extend)
export Coseq (coseq)
export CoseqLeft (coseqLeft)
export CoseqRight (coseqRight)

-- Notation for cosequencing operations
infixl:60 " <@> " => Coseq.coseq
infixl:60 " <@ "  => CoseqLeft.coseqLeft
infixl:60 " @> "  => CoseqRight.coseqRight

/-- `Coapplicative` functor. Dual to `Applicative`.
    Combines `Functor`, `Extract`, and `Coseq` operations. -/
class Coapplicative (w : Type u → Type v) extends
    Functor w, Extract w, Coseq w, CoseqLeft w, CoseqRight w where
  /-- Default implementation for `coseqLeft` using `coseq` and `map`. -/
  coseqLeft wa wb := Functor.map Prod.fst (coseq wa wb)
  /-- Default implementation for `coseqRight` using `coseq` and `map`. -/
  coseqRight wa wb := Functor.map Prod.snd (coseq wa wb)

/-- `Comonad`. Dual to `Monad`.
    Combines `Coapplicative` structure with `Extend`. -/
class Comonad (w : Type u → Type v) extends Coapplicative w, Extend w where
  /-- Default implementation for `map` using `extend` and `extract`.
      Note: This requires that the `Functor` instance provided to `Coapplicative`
      is compatible with this definition. `LawfulComonad` ensures this. -/
  map f wa := extend wa (f ∘ extract)
  /-- Default `coseq` built only from `extend` and `extract`.

      For two contexts `wa : w α`, `wb : w β` we:
      1. `extend` over the first context, so we may look inside it,
      2. pair its extracted value with the *already* extracted value of `wb`.

      This yields `w (α × β)` as required.  -/
  coseq wa wb := extend wa (fun wa' => (extract wa', extract wb))

-- Lawful Hierarchy --

/-- Lawful `Coapplicative` functor. Dual to `LawfulApplicative`. -/
class LawfulCoapplicative (w : Type u → Type v) [Coapplicative w] extends LawfulFunctor w where
  /-- Ensure default `coseqLeft` law holds even if overridden. -/
  coseqLeft_eq : ∀ {α β : Type u} (wa : w α) (wb : w β),
    @coseqLeft w _ α β wa wb = Functor.map (@Prod.fst α β) (coseq wa wb)
  /-- Ensure default `coseqRight` law holds even if overridden. -/
  coseqRight_eq : ∀ {α β : Type u} (wa : w α) (wb : w β),
    coseqRight wa wb = Functor.map (@Prod.snd α β) (coseq wa wb)
  /-- Associativity law for `coseq`. `assoc` maps `(α × β) × γ` to `α × (β × γ)`. -/
  coseq_assoc : ∀ {α β γ : Type u} (wa : w α) (wb : w β) (wc : w γ),
    Functor.map (Equiv.prodAssoc α β γ) (coseq (coseq wa wb) wc) = coseq wa (coseq wb wc)
  -- Other potential laws like extract_coseq : extract (wa <@> wb) = (extract wa, extract wb)
  -- are often added but require `w (α × β)` structure, so omitted here for generality.

export LawfulCoapplicative (coseqLeft_eq coseqRight_eq coseq_assoc)

/-- Lawful `Comonad`. Dual to `LawfulMonad`. -/
class LawfulComonad (w : Type u → Type v) [Comonad w] extends LawfulCoapplicative w where
  /-- Compatibility between `map` and `extend`/`extract`.
      Since `Comonad.map` defines map this way, this law ensures the `Functor` instance
      used by `LawfulCoapplicative` (and `LawfulFunctor`) is consistent. -/
  map_eq_extend_extract : ∀ {α β : Type u} (f : α → β) (wa : w α),
    Functor.map f wa = extend wa (f ∘ extract)
  /-- Extending with `extract` is the identity (Left identity dual). -/
  extend_extract : ∀ {α : Type u} (wa : w α), extend wa (@extract w _ α) = wa
  /-- Extracting after extending yields the original function application (Right identity dual). -/
  extract_extend : ∀ {α β : Type u} (wa : w α) (f : w α → β),
    extract (extend wa f) = f wa
  /-- Extend is associative (Associativity dual). -/
  extend_assoc : ∀ {α β γ : Type u} (wa : w α) (f : w α → β) (g : w β → γ),
    extend (extend wa f) g = extend wa (fun w'a => g (extend w'a f))

export LawfulComonad (map_eq_extend_extract extend_extract extract_extend extend_assoc)

-- Theorems derived from lawful classes --

section LawfulnessProofs
variable {w : Type u → Type v} [Comonad w] [LawfulComonad w]

@[simp] theorem comonad_id_map {α : Type u} (wa : w α) : Functor.map id wa = wa :=
  id_map wa

@[simp] theorem comonad_comp_map {α β γ : Type u} (f : β → γ) (g : α → β) (wa : w α) :
    Functor.map (f ∘ g) wa = Functor.map f (Functor.map g wa) :=
  comp_map g f wa

-- Proof for extract_map
@[simp] theorem extract_map {α β : Type u} (f : α → β) (wa : w α) :
  extract (Functor.map f wa) = f (extract wa) :=
by
  rw [map_eq_extend_extract, extract_extend, Function.comp_apply]

end LawfulnessProofs


-- Define duplicate and derived laws (require w : Type u → Type u)
section Duplicate
variable {w : Type u → Type u} [Comonad w]

/-- Duplicate the comonadic context. Defined via `extend`. -/
@[simp]
def duplicate {α : Type u} (wa : w α) : w (w α) :=
  extend wa id

variable [LawfulComonad w]
variable {α : Type u} (wa : w α)

@[simp] theorem extract_duplicate_eq_id : extract (duplicate wa) = wa :=
  extract_extend wa id

@[simp] theorem map_extract_duplicate_eq_id : Functor.map extract (duplicate wa) = wa :=
by
  rw [duplicate, map_eq_extend_extract, extend_assoc]
  simp only [Function.comp_apply, extract_extend, id_def]
  rw [extend_extract]

@[simp] theorem extend_eq_map_duplicate {β : Type u} (f : w α → β) :
  extend wa f = Functor.map f (duplicate wa) :=
by
  rw [duplicate, map_eq_extend_extract, extend_assoc]
  simp only [Function.comp_apply, extract_extend, id_def]

@[simp] theorem duplicate_duplicate_eq_map_duplicate :
    duplicate (duplicate wa) = Functor.map duplicate (duplicate wa) :=
by
  have h_lhs : duplicate (duplicate wa) = extend wa duplicate := by
    rw [duplicate, duplicate, extend_assoc]
    simp only [id_def]
    rfl
  have h_rhs : Functor.map duplicate (duplicate wa) = extend wa duplicate := by
    rw [duplicate, map_eq_extend_extract, extend_assoc]
    simp only [Function.comp_apply, extract_extend, id_def]
  rw [h_lhs, h_rhs]

end Duplicate
