/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.SPMF

/-!
# Typeclasses for Denotational Monad Semantics

dtumad: should evaluate if making the definitions `reducible` is a good idea.
Depends how well `MonadHomClass` works to be fair.
-/

open ENNReal

universe u v w

variable {m : Type u → Type v} [Monad m] {α β γ : Type u}

/-- The monad `m` can be evaluated to get a set of possible outputs.
Note that we don't implement this for `Set` with the monad type-class strangeness. -/
class HasEvalSet (m : Type u → Type v) [Monad m] where
  toSet : m →ᵐ SetM

/-- The monad `m` can be evaluated to get a finite set of possible outputs.
Note: this definition avoids needing `Finset` monad instances. -/
class HasEvalFinset (m : Type u → Type v) [Monad m] [HasEvalSet m] where
  toFinset : NatHom m Finset
  coe_toFinset {α : Type u} (mx : m α) :
    ((toFinset mx) : Set α) = HasEvalSet.toSet mx

/-- The monad `m` can be evaluated to get a sub-distribution of outputs. -/
class HasEvalSPMF (m : Type u → Type v) [Monad m] where
  toSPMF : m →ᵐ SPMF

/-- The monad `m` can be evaluated to get a distribution of outputs. -/
class HasEvalPMF (m : Type u → Type v) [Monad m] where
  toPMF : m →ᵐ PMF

/-- Evaluate a `SPMF` to itself via identity. Mostly exists to give notation access. -/
instance : HasEvalSPMF SPMF where toSPMF := MonadHom.id SPMF

/-- Evaluate a `PMF` to itself via identity. Mostly exists to give notation access.
Note: this requires `SPMF` to avoid circular type-class search. -/
instance : HasEvalPMF PMF where toPMF := MonadHom.id PMF

/-- The set of possible outputs of running the monadic computation `mx`. -/
def support [HasEvalSet m] (mx : m α) : Set α :=
  HasEvalSet.toSet.toFun mx

/-- The finite set of outputs of running the monadic computation `mx`. -/
def finSupport [HasEvalSet m] [HasEvalFinset m] (mx : m α) : Finset α :=
  HasEvalFinset.toFinset.toFun mx

@[simp] lemma coe_finSupport [HasEvalSet m] [HasEvalFinset m]
    (mx : m α) : (↑(finSupport mx) : Set α) = support mx := HasEvalFinset.coe_toFinset mx

/-- The resulting distribution of running the monadic computation `mx`. -/
def evalDist [HasEvalSPMF m] (mx : m α) : SPMF α :=
  HasEvalSPMF.toSPMF mx

instance [HasEvalSet m] : MonadHomClass m SetM support := by
  refine inferInstanceAs (MonadHomClass m SetM HasEvalSet.toSet.toFun)

instance [HasEvalSPMF m] : MonadHomClass m SPMF evalDist := by
  refine inferInstanceAs (MonadHomClass m SPMF HasEvalSPMF.toSPMF.toFun)

section test

@[simp] lemma evalDist_pure {m : Type u → Type v} [Monad m] [hm : HasEvalSPMF m]
    (x : α) : evalDist (pure x : m α) = pure x := by

  rw [MonadHomClass.mmap_pure m SPMF evalDist]


variable {m : Type u → Type v} [Monad m] [hm : HasEvalSet m]

@[simp] lemma support_pure (x : α) : support (pure x : m α) = {x} :=
  by simp [support]

lemma mem_support_pure_iff (x y : α) : x ∈ support (pure y : m α) ↔ x = y := by simp

@[simp] lemma support_bind (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) :=
  by simp [support]

lemma mem_support_bind_iff (mx : m α) (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp

end test

section probability_notation

/-- Probability that a computation `mx` returns the value `x`. -/
def probOutput [HasEvalSPMF m] (mx : m α) (x : α) : ℝ≥0∞ :=
  evalDist mx x

/-- Probability that a computation `mx` outputs a value satisfying `p`. -/
noncomputable def probEvent [HasEvalSPMF m] (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  (evalDist mx).run.toOuterMeasure (some '' {x | p x})

/-- Probability that a computation `mx` will fail to return a value. -/
def probFailure [HasEvalSPMF m] (mx : m α) : ℝ≥0∞ :=
  (evalDist mx).run none

/-- Probability that a computation returns a particular output. -/
notation "Pr[=" x " | " mx "]" => probOutput mx x

/-- Probability that a computation returns a value satisfying a predicate. -/
notation "Pr[" p " | " mx "]" => probEvent mx p

/-- Probability that a computation fails to return a value. -/
notation "Pr[⊥" " | " mx "]" => probFailure mx

/-- Probability that a computation returns a value satisfying a predicate. -/
syntax (name := probEventBinding1)
  "Pr[" term " | " ident " ← " term "]" : term

macro_rules (kind := probEventBinding1)
  | `(Pr[$cond:term | $var:ident ← $src:term]) => `(Pr[fun $var => $cond | $src])

/-- Probability that a computation returns a value satisfying a predicate. -/
syntax (name := probEventBinding2) "Pr{" doSeq "}[" term "]" : term

macro_rules (kind := probEventBinding2)
  -- `doSeqBracketed`
  | `(Pr{{$items*}}[$t]) => `(probOutput (do $items:doSeqItem* return $t:term) True)
  -- `doSeqIndent`
  | `(Pr{$items*}[$t]) => `(probOutput (do $items:doSeqItem* return $t:term) True)

/-- Tests for all the different probability notations. -/
example {m : Type → Type u} [Monad m] [HasEvalSPMF m] (mx : m ℕ) : Unit :=
  let _ := Pr[= 10 | mx]
  let _ := Pr[fun x => x^2 + x < 10 | mx]
  let _ := Pr[x^2 + x < 10 | x ← mx]
  let _ := Pr{let x ← mx}[x = 10]
  let _ := Pr[⊥ | mx]
  ()

end probability_notation

section decidable

/-- Typeclass for decidable membership in the support of a computation. -/
protected class HasEvalSet.Decidable (m : Type u → Type v) [Monad m] [HasEvalSet m] where
  mem_support_decidable {α : Type u} (mx : m α) : DecidablePred (· ∈ support mx)

instance [HasEvalSet m] [HasEvalSet.Decidable m] (mx : m α) :
    DecidablePred (· ∈ support mx) :=
  HasEvalSet.Decidable.mem_support_decidable mx

instance [HasEvalSet m] [HasEvalSet.Decidable m] [HasEvalFinset m] (mx : m α) :
    DecidablePred (· ∈ finSupport mx) := by
  sorry

end decidable

section hasEvalSet_of_hasEvalSPMF

/-- Given a `SPMF` evaluation instance, set the support to values of `non-zero` probability.-/
instance hasEvalSet_of_hasEvalSPMF [HasEvalSPMF m] : HasEvalSet m where
  toSet := MonadHom.comp SPMF.support HasEvalSPMF.toSPMF

instance [HasEvalSPMF m] [HasEvalSet.Decidable m] (mx : m α) :
    DecidablePred (Pr[= · | mx] = 0) :=
  sorry

end hasEvalSet_of_hasEvalSPMF

section hasEvalSPMF_of_hasEvalPMF

/-- Given a `PMF` evaluation instance, get a `SPMF` evaluation by the natural lifting. -/
noncomputable instance hasEvalSPMF_of_hasEvalPMF [HasEvalPMF m] : HasEvalSPMF m where
  toSPMF := MonadHom.comp PMF.toSPMF HasEvalPMF.toPMF

end hasEvalSPMF_of_hasEvalPMF
