/-
Copyright (c) 2025 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.Prelude
import ToMathlib.ProbabilityTheory.SPMF

/-!
# Typeclasses for Denotational Monad Support

This file defines typeclasses `HasEvalSet m` and `HasEvalFinset m` for asigning a
set of possible outputs to computations in a monad `m`.
-/

open ENNReal

universe u v w

variable {m : Type u → Type v} [Monad m] {α β γ : Type u}

section support

@[simp]
lemma SetM.pure_def (x : α) : (pure x : SetM α) = ({x} : Set α) := rfl

@[simp]
lemma SetM.bind_def (mx : SetM α) (my : α → SetM β) :
    mx >>= my = ⋃ x ∈ mx.run, my x := rfl

/-- The monad `m` can be evaluated to get a set of possible outputs.
Note that we don't implement this for `Set` with the monad type-class strangeness.
Should not be implemented manually if a `HasEvalSPMF` instance already exists. -/
class HasEvalSet (m : Type u → Type v) [Monad m] where
  toSet : m →ᵐ SetM

/-- The set of possible outputs of running the monadic computation `mx`. -/
def support [HasEvalSet m] {α : Type u} (mx : m α) : Set α :=
  SetM.run (HasEvalSet.toSet mx)

-- dtumad: not sure if this should actually be in the ruleset?
@[aesop norm (rule_sets := [UnfoldEvalDist]), grind =]
lemma support_def [HasEvalSet m] {α : Type u} (mx : m α) :
    support mx = SetM.run (HasEvalSet.toSet mx) := rfl

/-- The monad `m` can be evaluated to get a finite set of possible outputs.
We restrict to the case of decidable equality of the output type, so `Finset.biUnion` exists.
Note: we can't use `MonadHomClass` since `Finset` has no `Monad` instance. -/
class HasEvalFinset (m : Type u → Type v) [Monad m] [HasEvalSet m] where
  finSupport {α : Type u} [DecidableEq α] (mx : m α) : Finset α
  coe_finSupport {α : Type u} [DecidableEq α] (mx : m α) :
    (↑(finSupport mx) : Set α) = support mx

export HasEvalFinset (finSupport coe_finSupport)

attribute [simp, grind =] coe_finSupport

@[grind =, aesop unsafe norm]
lemma mem_finSupport_iff_mem_support [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (x : α) : x ∈ finSupport mx ↔ x ∈ support mx := by
  rw [← Finset.mem_coe, coe_finSupport]

lemma finSupport_eq_iff_support_eq_coe [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (s : Finset α) : finSupport mx = s ↔ support mx = ↑s := by grind

@[aesop unsafe 60% apply]
lemma finSupport_eq_of_support_eq_coe [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {s : Finset α} (h : support mx = ↑s) : finSupport mx = s := by grind

@[aesop unsafe 85% apply]
lemma mem_finSupport_of_mem_support [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {x : α} (h : x ∈ support mx) : x ∈ finSupport mx := by grind

lemma mem_support_of_mem_finSupport [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {x : α} (h : x ∈ finSupport mx) : x ∈ support mx := by grind

@[aesop unsafe 85% apply]
lemma not_mem_finSupport_of_not_mem_support [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {x : α} (h : x ∉ support mx) : x ∉ finSupport mx := by grind

lemma not_mem_support_of_not_mem_finSupport [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {x : α} (h : x ∉ finSupport mx) : x ∉ support mx := by grind

end support

section forall_support

variable {m : Type u → Type v} [Monad m] [HasEvalSet m] {α : Type u}

/-- A predicate holds on every output reachable from a monadic computation `mx`,
i.e. `∀ x ∈ support mx, p x`. This is the "almost-sure" assertion at the qualitative
denotational level provided by `HasEvalSet`.

For `OracleComp`, see also the structural-recursion variant
`OracleComp.allOutputsSatisfyWhen` in `VCVio/OracleComp/Traversal.lean`, which is
parameterized by a set of possible oracle outputs. -/
def allOutputsSatisfy (p : α → Prop) (mx : m α) : Prop :=
  ∀ x ∈ support mx, p x

/-- A predicate holds on some output reachable from a monadic computation `mx`,
i.e. `∃ x ∈ support mx, p x`. -/
def someOutputSatisfies (p : α → Prop) (mx : m α) : Prop :=
  ∃ x ∈ support mx, p x

lemma allOutputsSatisfy_iff_forall_support (p : α → Prop) (mx : m α) :
    allOutputsSatisfy p mx ↔ ∀ x ∈ support mx, p x := Iff.rfl

lemma someOutputSatisfies_iff_exists_support (p : α → Prop) (mx : m α) :
    someOutputSatisfies p mx ↔ ∃ x ∈ support mx, p x := Iff.rfl

lemma allOutputsSatisfy_mono {p q : α → Prop} (hpq : ∀ a, p a → q a) (mx : m α) :
    allOutputsSatisfy p mx → allOutputsSatisfy q mx :=
  fun h x hx => hpq x (h x hx)

lemma someOutputSatisfies_mono {p q : α → Prop} (hpq : ∀ a, p a → q a) (mx : m α) :
    someOutputSatisfies p mx → someOutputSatisfies q mx := by
  rintro ⟨x, hx, hpx⟩
  exact ⟨x, hx, hpq x hpx⟩

end forall_support

variable (p : Prop) [Decidable p]

@[simp] lemma support_ite [HasEvalSet m] (mx mx' : m α) :
    support (if p then mx else mx') = if p then support mx else support mx' := by aesop

@[simp] lemma finSupport_ite [HasEvalSet m] [HasEvalFinset m] [DecidableEq α] (mx mx' : m α) :
    finSupport (if p then mx else mx') = if p then finSupport mx else finSupport mx' := by aesop

lemma support_eqRec [HasEvalSet m] (h : α = β) (mx : m α) :
    support (h ▸ mx : m β) = h ▸ support mx := by grind

-- dtumad: this is not really useful in this form very often...
lemma finSupport_eqRec {m} [hm : Monad m] [hms : HasEvalSet m] [hmfs : HasEvalFinset m]
    [hα : DecidableEq α] (h : α = β) (mx : m α) :
    (@finSupport m hm hms hmfs β (h ▸ hα) (h ▸ mx : m β) : Finset β) =
      (h ▸ (@finSupport m hm hms hmfs α hα mx : Finset α) : Finset β) := by grind

section decidable

/-- Membership in the support of computations in. -/
protected class HasEvalSet.Decidable (m : Type u → Type v) [Monad m] [HasEvalSet m] where
  mem_support_decidable {α : Type u} (mx : m α) : DecidablePred (· ∈ support mx)

instance decidablePred_mem_support [HasEvalSet m] [HasEvalSet.Decidable m]
    (mx : m α) : DecidablePred (· ∈ support mx) :=
  HasEvalSet.Decidable.mem_support_decidable mx

instance decidablePred_mem_finSupport [HasEvalSet m] [HasEvalSet.Decidable m] [HasEvalFinset m]
    [DecidableEq α] (mx : m α) : DecidablePred (· ∈ finSupport mx) := by
  simpa only [mem_finSupport_iff_mem_support] using decidablePred_mem_support mx

end decidable
