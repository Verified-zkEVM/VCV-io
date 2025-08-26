/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.SPMF
import ToMathlib.Control.MonadHom

/-!
# Support of a Monadic Computation

dt: Consider switching naming conventions to `supportM` to avoid naming clashes more.
-/

open ENNReal

universe u v w

section HasSupportM

/-- Class for monads with a lawful embedding into `Set`, representing the possible outputs
for the computation, using the `SetM` definition to get a monad instance on `Set`.
For monads like `StateM` should consider all possible input states. -/
class HasSupportM (m : Type u → Type v) [Monad m]
  extends m →ᵐ SetM

/-- Given a monad with a lawful set embedding get the support by applying the map.
dt: might be good to call this `supportM` due to namespacing. -/
def support {m : Type u → Type v} [Monad m] {α : Type u}
    [hm : HasSupportM m] (mx : m α) : Set α := SetM.run (hm.toFun mx)

variable {α β γ : Type u} {m : Type u → Type v} [Monad m] [hm : HasSupportM m]

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

end HasSupportM

section decidable

/-- Typeclass for decidable membership in the support of a computation. -/
class HasSupportM.decidable {m : Type _ → Type _} [Monad m] [HasSupportM m] where
  mem_support_decidable {α : Type _} (mx : m α) : DecidablePred (· ∈ support mx)

end decidable

section LawfulFailure

/-- Mixin typeclass for `HasSupportM` embeddings that give no support to `failure`.
This isn't an actual extend to avoid complex instance trees with `HasEvalDist` and others. -/
class HasSupportM.LawfulFailure (m : Type u → Type v)
    [AlternativeMonad m] [hm : HasSupportM m] : Prop where
  support_failure' {α : Type u} : support (failure : m α) = ∅

variable {α β γ : Type u} {m : Type u → Type v}
  [AlternativeMonad m] [hm : HasSupportM m] [HasSupportM.LawfulFailure m]

@[simp] lemma support_failure : support (failure : m α) = ∅ :=
  HasSupportM.LawfulFailure.support_failure'

end LawfulFailure

namespace PMF

instance : HasSupportM PMF where
  toFun := PMF.support
  toFun_pure' := by simp
  toFun_bind' := by simp

@[simp] lemma support_eq {α} (p : PMF α) : support p = PMF.support p := rfl

end PMF

namespace SPMF

instance : HasSupportM SPMF where
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

instance : HasSupportM.LawfulFailure SPMF where
  support_failure' {α} := by ext; simp

end SPMF

namespace StateT

/-- Support of a stateful computation is the union of support for each possible initial states. -/
instance {m : Type _ → Type _} [Monad m] [HasSupportM m]
    {σ : Type _} : HasSupportM (StateT σ m) where
  toFun {α} := fun mx => ⋃ s : σ, support (mx.run' s)
  toFun_pure' := sorry
  toFun_bind' := sorry

-- protected lemma support_def

end StateT
