/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.SPMF

/-!
# Typeclasses for Denotational Monad Support

This file defines typeclasses `HasEvalSet m` and `HasEvalFinset m` for asigning a
set of possible outputs to computations in a monad `m`.
-/

open ENNReal

universe u v w

variable {m : Type u → Type v} [Monad m] {α β γ : Type u}

section support

/-- The monad `m` can be evaluated to get a set of possible outputs.
Note that we don't implement this for `Set` with the monad type-class strangeness.
Should not be implemented manually if a `HasEvalSPMF` instance already exists. -/
class HasEvalSet (m : Type u → Type v) [Monad m] where
  toSet : m →ᵐ SetM

/-- The set of possible outputs of running the monadic computation `mx`. -/
def support [HasEvalSet m] {α : Type u} (mx : m α) : Set α :=
  HasEvalSet.toSet.toFun mx

-- dtumad: not sure if this should actually be in the ruleset?
@[aesop norm (rule_sets := [UnfoldEvalDist])]
lemma support_def [HasEvalSet m] {α : Type u} (mx : m α) :
    support mx = HasEvalSet.toSet.toFun mx := rfl

/-- `support` is an (implicit) monad morphism. -/
instance [HasEvalSet m] : MonadHomClass m SetM (@support m _ _) :=
  inferInstanceAs (MonadHomClass m SetM @HasEvalSet.toSet.toFun)

/-- The support of a `SetM` computation is the resulting set. -/
instance : HasEvalSet SetM where toSet := MonadHom.id SetM

@[simp] lemma SetM.support_eq (x : SetM α) : support x = x.run := rfl

/-- The monad `m` can be evaluated to get a finite set of possible outputs.
We restrict to the case of decidable equality of the output type, so `Finset.biUnion` exists. -/
class HasEvalFinset (m : Type u → Type v) [Monad m] [HasEvalSet m] where
  finSupport {α : Type u} [DecidableEq α] (mx : m α) : Finset α
  coe_finSupport {α : Type u} [DecidableEq α] (mx : m α) :
    (↑(finSupport mx) : Set α) = support mx

export HasEvalFinset (finSupport coe_finSupport)

attribute [simp] coe_finSupport

lemma mem_finSupport_iff_mem_support [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (x : α) : x ∈ finSupport mx ↔ x ∈ support mx := by
  rw [← Finset.mem_coe, coe_finSupport]

lemma finSupport_eq_iff_support_eq_coe [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (s : Finset α) : finSupport mx = s ↔ support mx = ↑s := by
  rw [← Finset.coe_inj, coe_finSupport]

@[aesop unsafe 60% apply]
lemma finSupport_eq_of_support_eq_coe [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {s : Finset α} (h : support mx = ↑s) : finSupport mx = s := by
  rwa [finSupport_eq_iff_support_eq_coe]

@[aesop unsafe 85% apply]
lemma mem_finSupport_of_mem_support [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {x : α} (h : x ∈ support mx) : x ∈ finSupport mx := by
  rwa [← Finset.mem_coe, coe_finSupport]

lemma mem_support_of_mem_finSupport [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {x : α} (h : x ∈ finSupport mx) : x ∈ support mx := by
  rwa [← Finset.mem_coe, coe_finSupport] at h

@[aesop unsafe 85% apply]
lemma not_mem_finSupport_of_not_mem_support [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {x : α} (h : x ∉ support mx) : x ∉ finSupport mx := by
  rwa [← Finset.mem_coe, coe_finSupport]

lemma not_mem_support_of_not_mem_finSupport [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {x : α} (h : x ∉ finSupport mx) : x ∉ support mx := by
  rwa [← Finset.mem_coe, coe_finSupport] at h

end support

variable (p : Prop) [Decidable p]

@[simp] lemma support_ite [HasEvalSet m] (mx mx' : m α) :
    support (if p then mx else mx') = if p then support mx else support mx' := by aesop

@[simp] lemma finSupport_ite [HasEvalSet m] [HasEvalFinset m] [DecidableEq α] (mx mx' : m α) :
    finSupport (if p then mx else mx') = if p then finSupport mx else finSupport mx' := by aesop

lemma support_eqRec [HasEvalSet m] (h : α = β) (mx : m α) :
    support (h ▸ mx : m β) = h ▸ support mx := by induction h; rfl

-- dtumad: this is not really useful in this form very often...
lemma finSupport_eqRec {m} [hm : Monad m] [hms : HasEvalSet m] [hmfs : HasEvalFinset m]
    [hα : DecidableEq α] (h : α = β) (mx : m α) :
    (@finSupport m hm hms hmfs β (h ▸ hα) (h ▸ mx : m β) : Finset β) =
      (h ▸ (@finSupport m hm hms hmfs α hα mx : Finset α) : Finset β) := by
  induction h; rfl

section decidable

/-- Membership in the support of computations in  -/
protected class HasEvalSet.Decidable (m : Type u → Type v) [Monad m] [HasEvalSet m] where
  mem_support_decidable {α : Type u} (mx : m α) : DecidablePred (· ∈ support mx)

instance decidablePred_mem_support [HasEvalSet m] [HasEvalSet.Decidable m]
    (mx : m α) : DecidablePred (· ∈ support mx) :=
  HasEvalSet.Decidable.mem_support_decidable mx

instance decidablePred_mem_finSupport [HasEvalSet m] [HasEvalSet.Decidable m] [HasEvalFinset m]
    [DecidableEq α] (mx : m α) : DecidablePred (· ∈ finSupport mx) := by
  simpa only [mem_finSupport_iff_mem_support] using decidablePred_mem_support mx

end decidable
