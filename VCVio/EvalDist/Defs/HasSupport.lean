/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.SPMF
import ToMathlib.Control.Monad.Hom
import ToMathlib.Control.StateT

/-!
# Support of a Monadic Computation

dt: Consider switching naming conventions to `supportM` to avoid naming clashes more.
-/

open ENNReal

universe u v w

section HasSupport

/-- Class for monads with a lawful embedding into `Set`, representing the possible outputs
for the computation, using the `SetM` definition to get a monad instance on `Set`.
For monads like `StateM` should consider all possible input states. -/
class HasSupport (m : Type u → Type v) [Monad m]
  extends m →ᵐ SetM

/-- Given a monad with a lawful set embedding get the support by applying the map.
dt: might be good to call this `supportM` due to namespacing. -/
def support {m : Type u → Type v} [Monad m] {α : Type u}
    [hm : HasSupport m] (mx : m α) : Set α := SetM.run (hm.toFun mx)

variable {α β γ : Type u} {m : Type u → Type v} [Monad m] [hm : HasSupport m]

@[simp] lemma support_pure (x : α) : support (pure x : m α) = {x} :=
  hm.toFun_pure' x

lemma mem_support_pure_iff (x y : α) : x ∈ support (pure y : m α) ↔ x = y := by simp

@[simp] lemma support_bind (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) :=
  hm.toFun_bind' mx my

lemma mem_support_bind_iff (mx : m α) (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp

@[simp] lemma support_eqRec (mx : m α) (h : α = β) :
    support (h ▸ mx) = h.symm ▸ support mx := by induction h; rfl

@[simp] lemma support_map [LawfulMonad m] (mx : m α) (f : α → β) :
    support (f <$> mx) = f '' support mx := by
  simp [map_eq_bind_pure_comp, Set.ext_iff]
  aesop

lemma mem_support_map_iff [LawfulMonad m] (mx : m α) (f : α → β) (y : β) :
    y ∈ support (f <$> mx) ↔ ∃ x ∈ support mx, f x = y := by simp

lemma mem_support_map [LawfulMonad m] {mx : m α} {x : α} (hx : x ∈ support mx)
    (f : α → β) : f x ∈ support (f <$> mx) := by aesop

@[simp] lemma support_ite (p : Prop) [Decidable p] (mx mx' : m α) :
    support (if p then mx else mx') = if p then support mx else support mx' :=
  apply_ite support p mx mx'

lemma mem_support_ite_iff (p : Prop) [Decidable p] (mx mx' : m α) (x : α) :
    x ∈ support (if p then mx else mx') ↔ p ∧ x ∈ support mx ∨ ¬ p ∧ x ∈ support mx' := by
  split_ifs with h <;> simp [h]

@[simp] lemma support_dite (p : Prop) [Decidable p] (mx : p → m α) (mx' : ¬ p → m α) :
    support (if h : p then mx h else mx' h) = if h : p then support (mx h) else support (mx' h) :=
  apply_dite support p mx mx'

@[simp] lemma mem_support_dite_iff (p : Prop) [Decidable p] (mx : p → m α) (mx' : ¬ p → m α)
    (x : α) : x ∈ support (if h : p then mx h else mx' h) ↔
      (∃ h : p, x ∈ support (mx h)) ∨ (∃ h : ¬ p, x ∈ support (mx' h)) := by
  split_ifs with h <;> simp [h]

end HasSupport

section decidable

/-- Typeclass for decidable membership in the support of a computation. -/
class HasSupport.Decidable {m : Type _ → Type _} [Monad m] [HasSupport m] where
  mem_support_decidable {α : Type _} (mx : m α) : DecidablePred (· ∈ support mx)

end decidable

section LawfulFailure

/-- Mixin typeclass for `HasSupport` embeddings that give no support to `failure`.
This isn't an actual extend to avoid complex instance trees with `HasSPMF` and others. -/
class HasSupport.LawfulFailure (m : Type u → Type v)
    [AlternativeMonad m] [hm : HasSupport m] : Prop where
  support_failure' {α : Type u} : support (failure : m α) = ∅

variable {α β γ : Type u} {m : Type u → Type v}
  [AlternativeMonad m] [hm : HasSupport m] [HasSupport.LawfulFailure m]

@[simp] lemma support_failure : support (failure : m α) = ∅ :=
  HasSupport.LawfulFailure.support_failure'

end LawfulFailure

namespace PMF

instance : HasSupport PMF where
  toFun := PMF.support
  toFun_pure' := by simp
  toFun_bind' := by simp

@[simp] lemma support_eq {α} (p : PMF α) : support p = PMF.support p := rfl

end PMF

namespace SPMF

instance : HasSupport SPMF where
  toFun x := Function.support x
  toFun_pure' x := by
    refine Set.ext fun y => ?_
    simp
  toFun_bind' x y := by
    refine Set.ext fun y => ?_
    simp [Option.elimM, Function.comp_def]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨z, hz⟩ := h
      cases z with
      | none =>
          simp at hz
      | some z =>
          use z
          simp at hz
          simp [hz]
    · obtain ⟨z, hz⟩ := h
      use some z
      simp [hz]

@[simp] lemma support_eq {α} (p : SPMF α) : support p = Function.support p := rfl

instance : HasSupport.LawfulFailure SPMF where
  support_failure' {α} := by ext; simp

end SPMF

namespace StateT

variable {σ : Type u} {m : Type u → Type v} [Monad m] [HasSupport m]
variable {α β : Type u}

/-- Pair-level support for `StateT`: the set of reachable `(α, σ)` pairs from an initial state `s`.
This is the lawful notion that composes through bind. -/
def supportPair (mx : StateT σ m α) (s : σ) : Set (α × σ) :=
  support (mx.run s)

@[simp] lemma supportPair_pure (x : α) (s : σ) :
    supportPair (pure x : StateT σ m α) s = {(x, s)} := by
  change support (pure ((x, s) : α × σ) : m (α × σ)) = { (x, s) }
  simp

@[simp] lemma supportPair_bind (x : StateT σ m α) (y : α → StateT σ m β) (s : σ) :
    supportPair (x >>= y) s = ⋃ p ∈ supportPair x s, supportPair (y p.1) p.2 := by
  -- Unfold and apply `support_bind` at the base monad level.
  -- `(x >>= y).run s = do let (a, s') ← x.run s; (y a).run s'`
  change support ((x >>= y).run s) = _
  -- Use the definitional bind for StateT.
  -- `StateT.run_bind` is available via the imported helpers; fall back to simp if needed.
  simp [supportPair, StateT.run, StateT.bind, bind, support_bind]

/-- Projected (α-only) support at a fixed initial state, obtained from `supportPair`.
This is a convenient view, but does not compose as a monad hom without threading the state. -/
def supportAt (mx : StateT σ m α) (s : σ) : Set α :=
  Prod.fst '' supportPair mx s

@[simp] lemma supportAt_pure (x : α) (s : σ) :
    supportAt (pure x : StateT σ m α) s = {x} := by
  simp [supportAt, supportPair_pure, Set.image_singleton]

end StateT
