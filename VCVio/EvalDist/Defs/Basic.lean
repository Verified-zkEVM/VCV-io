/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, František Silváši
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

/-- The monad `m` can be evaluated to get a set of possible outputs. -/
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

/-- Given a `SPMF` evaluation instance, set the support to values of `non-zero` probability.-/
instance [HasEvalSPMF m] : HasEvalSet m where
  toSet := MonadHom.comp SPMF.support HasEvalSPMF.toSPMF

/-- Given a `PMF` evaluation instance, get a `SPMF` evaluation by the natural lifting. -/
noncomputable instance [HasEvalPMF m] : HasEvalSPMF m where
  toSPMF := MonadHom.comp PMF.toSPMF HasEvalPMF.toPMF

/-- The set of possible outputs of running the monadic computation `mx`.
dtumad: does namespacing ever become an issue exposing this globally? -/
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

attribute [local instance] Set.monad in
instance [HasEvalSet m] : MonadHomClass m Set support := by
  refine inferInstanceAs (MonadHomClass m Set HasEvalSet.toSet.toFun)

instance [HasEvalSPMF m] : MonadHomClass m SPMF evalDist := by
  refine inferInstanceAs (MonadHomClass m SPMF HasEvalSPMF.toSPMF.toFun)

section probability

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

/-- Test for all the different probability notations. -/
example {m : Type → Type u} [Monad m] [HasEvalSPMF m] (mx : m ℕ) : Unit :=
  let _ := Pr[= 10 | mx]
  let _ := Pr[fun x => x^2 + x < 10 | mx]
  let _ := Pr[x^2 + x < 10 | x ← mx]
  let _ := Pr{let x ← mx}[x = 10]
  let _ := Pr[⊥ | mx]
  ()

end probability
