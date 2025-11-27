/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Support

/-!
# Typeclasses for Denotational Monad Semantics

dt: should evaluate if making the definitions `reducible` is a good idea.
Depends how well `MonadHomClass` works to be fair.
-/

open ENNReal

universe u v w

variable {m : Type u → Type v} [Monad m] {α β γ : Type u}

/-- The monad `m` can be evaluated to get a sub-distribution of outputs.
Should not be implemented manually if a `HasEvalPMF` instance already exists. -/
class HasEvalSPMF (m : Type u → Type v) [Monad m]
    extends HasEvalSet m where
  toSPMF : m →ᵐ SPMF

/-- The monad `m` can be evaluated to get a distribution of outputs. -/
class HasEvalPMF (m : Type u → Type v) [Monad m]
    extends HasEvalSPMF m where
  toPMF : m →ᵐ PMF

/-- The resulting distribution of running the monadic computation `mx`. -/
def evalDist [HasEvalSPMF m] {α : Type u} (mx : m α) : SPMF α :=
  HasEvalSPMF.toSPMF mx

instance [HasEvalSPMF m] : MonadHomClass m SPMF (@evalDist m _ _) :=
  inferInstanceAs (MonadHomClass m SPMF @HasEvalSPMF.toSPMF.toFun)

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

section probOutput

-- dtumad: I think maybe we want to simp in the `←` direction here?
@[aesop norm (rule_sets := [UnfoldEvalDist])]
lemma probOutput_def [HasEvalSPMF m] (mx : m α) (x : α) :
    Pr[= x | mx] = (evalDist mx).run (some x) := rfl

end probOutput

section probEvent

@[aesop norm (rule_sets := [UnfoldEvalDist])]
lemma probEvent_def [HasEvalSPMF m] (mx : m α) (p : α → Prop) :
    Pr[p | mx] = (evalDist mx).run.toOuterMeasure (some '' {x | p x}) := rfl

lemma probEvent_eq_tsum_indicator [HasEvalSPMF m] (mx : m α) (p : α → Prop) :
    Pr[p | mx] = ∑' x : α, {x | p x}.indicator (Pr[= · | mx]) x := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable,
    Set.indicator_image (Option.some_injective _), Function.comp_def, probOutput_def]

lemma probEvent_eq_sum_fintype_indicator [HasEvalSPMF m] [Fintype α]
    (mx : m α) (p : α → Prop) : Pr[p | mx] = ∑ x : α, {x | p x}.indicator (Pr[= · | mx]) x :=
  (probEvent_eq_tsum_indicator mx p).trans (tsum_fintype _)

lemma probEvent_eq_tsum_ite [HasEvalSPMF m] (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑' x : α, if p x then Pr[= x | mx] else 0 := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable, Set.indicator,
    probOutput_def]

lemma probEvent_eq_sum_fintype_ite [HasEvalSPMF m] [Fintype α]
    (mx : m α) (p : α → Prop) [DecidablePred p] : Pr[p | mx] = ∑ x : α, if p x then Pr[= x | mx] else 0 :=
  (probEvent_eq_tsum_ite mx p).trans (tsum_fintype _)

lemma probEvent_eq_tsum_subtype [HasEvalSPMF m] (mx : m α) (p : α → Prop) :
    Pr[p | mx] = ∑' x : {x | p x}, Pr[= x | mx] := by
  rw [probEvent_eq_tsum_indicator, tsum_subtype]

lemma probEvent_eq_sum_filter_univ [HasEvalSPMF m] [Fintype α]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑ x ∈ Finset.univ.filter p, Pr[= x | mx] := by
  rw [probEvent_eq_sum_fintype_ite, Finset.sum_filter]

end probEvent

section probFailure

@[aesop norm (rule_sets := [UnfoldEvalDist])]
lemma probFailure_def [HasEvalSPMF m] (mx : m α) :
    Pr[⊥ | mx] = (evalDist mx).run none := rfl

end probFailure

/-- Probability that a computation returns a value satisfying a predicate. -/
syntax (name := probEventBinding1)
  "Pr[" term " | " ident " ← " term "]" : term

macro_rules (kind := probEventBinding1)
  | `(Pr[$cond:term | $var:ident ← $src:term]) => `(Pr[fun $var => $cond | $src])

/-- Probability that a computation returns a value satisfying a predicate.
See `probOutput_true_eq_probEvent` for relation to the above definitions. -/
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

lemma evalDist_ext {m n} [Monad m] [HasEvalSPMF m] [Monad n] [HasEvalSPMF n]
    {mx : m α} {mx' : n α} (h : ∀ x, Pr[= x | mx] = Pr[= x | mx']) : evalDist mx = evalDist mx' :=
  SPMF.ext h

lemma evalDist_ext_iff {m n} [Monad m] [HasEvalSPMF m] [Monad n] [HasEvalSPMF n]
    {mx : m α} {mx' : n α} : evalDist mx = evalDist mx' ↔ ∀ x, Pr[= x | mx] = Pr[= x | mx'] := by
  refine ⟨fun h => ?_, evalDist_ext⟩
  simp [probOutput_def, h]

end probability_notation

section ite

variable (p : Prop) [Decidable p]

@[simp] lemma evalDist_ite [HasEvalSPMF m] (mx mx' : m α) :
    evalDist (if p then mx else mx') = if p then evalDist mx else evalDist mx' := by aesop

@[simp] lemma probOutput_ite [HasEvalSPMF m] (x : α) (mx mx' : m α) :
    Pr[= x | if p then mx else mx'] = if p then Pr[= x | mx] else Pr[= x | mx'] := by aesop

@[simp] lemma probFailure_ite [HasEvalSPMF m] (mx mx' : m α) :
    Pr[⊥ | if p then mx else mx'] = if p then Pr[⊥ | mx] else Pr[⊥ | mx'] := by aesop

@[simp] lemma probEvent_ite [HasEvalSPMF m] (mx mx' : m α) (q : α → Prop) :
    Pr[q | if p then mx else mx'] = if p then Pr[q | mx] else Pr[q | mx'] := by aesop

end ite

section eqRec

lemma evalDist_eqRec [HasEvalSPMF m] (h : α = β) (mx : m α) :
    evalDist (h ▸ mx : m β) = h ▸ evalDist mx := by induction h; rfl

lemma probOutput_eqRec [HasEvalSPMF m] (h : α = β) (mx : m α) (y : β) :
    Pr[= y | h ▸ mx] = Pr[= h ▸ y | mx] := by induction h; rfl

@[simp] lemma probFailure_eqRec [HasEvalSPMF m] (h : α = β) (mx : m α) :
    Pr[⊥ | h ▸ mx] = Pr[⊥ | mx] := by induction h; rfl

lemma probEvent_eqRec [HasEvalSPMF m] (h : α = β) (mx : m α) (q : β → Prop) :
    Pr[q | h ▸ mx] = Pr[fun x ↦ q (h ▸ x) | mx] := by induction h; rfl

end eqRec

section sums

/-- Connection between the two different probability notations. -/
lemma probOutput_true_eq_probEvent {α} {m : Type → Type u} [Monad m] [HasEvalSPMF m]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] = Pr[p | mx] := by
  rw [probEvent_eq_tsum_indicator, probOutput_def]
  simp [PMF.monad_map_eq_map, tsum_option]
  refine tsum_congr fun α => by aesop

@[simp] lemma tsum_probOutput_add_probFailure [HasEvalSPMF m] (mx : m α) :
    (∑' x, Pr[= x | mx]) + Pr[⊥ | mx] = 1 := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp] lemma probFailure_add_tsum_probOutput [HasEvalSPMF m] (mx : m α) :
    Pr[⊥ | mx] + ∑' x, Pr[= x | mx] = 1 := by
  aesop (rule_sets := [UnfoldEvalDist])

end sums

section bounds

variable {mx : m α} {mxe : OptionT m α} {x : α} {p : α → Prop}

@[simp] lemma probOutput_le_one [HasEvalSPMF m] :
    Pr[= x | mx] ≤ 1 := PMF.coe_le_one (evalDist mx) x
@[simp] lemma probOutput_ne_top [HasEvalSPMF m] :
    Pr[= x | mx] ≠ ∞ := PMF.apply_ne_top (evalDist mx) x
@[simp] lemma probOutput_lt_top [HasEvalSPMF m] :
    Pr[= x | mx] < ∞ := PMF.apply_lt_top (evalDist mx) x
@[simp] lemma not_one_lt_probOutput [HasEvalSPMF m] :
    ¬ 1 < Pr[= x | mx] := not_lt.2 probOutput_le_one

@[simp] lemma tsum_probOutput_le_one [HasEvalSPMF m] : ∑' x : α, Pr[= x | mx] ≤ 1 :=
  le_of_le_of_eq (le_add_self) (probFailure_add_tsum_probOutput mx)
@[simp] lemma tsum_probOutput_ne_top [HasEvalSPMF m] : ∑' x : α, Pr[= x | mx] ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one

@[simp] lemma probEvent_le_one [HasEvalSPMF m] : Pr[p | mx] ≤ 1 := by
  rw [probEvent_def, PMF.toOuterMeasure_apply]
  refine le_of_le_of_eq (ENNReal.tsum_le_tsum ?_) ((evalDist mx).tsum_coe)
  exact Set.indicator_le_self (some '' {x | p x}) _

@[simp] lemma probEvent_ne_top [HasEvalSPMF m] :
    Pr[p | mx] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
@[simp] lemma probEvent_lt_top [HasEvalSPMF m] :
    Pr[p | mx] < ∞ := lt_top_iff_ne_top.2 probEvent_ne_top
@[simp] lemma not_one_lt_probEvent [HasEvalSPMF m] :
    ¬ 1 < Pr[p | mx] := not_lt.2 probEvent_le_one

@[simp] lemma probFailure_le_one [HasEvalSPMF m] :
    Pr[⊥ | mx] ≤ 1 := PMF.coe_le_one (evalDist mx) none
@[simp] lemma probFailure_ne_top [HasEvalSPMF m] :
    Pr[⊥ | mx] ≠ ∞ := PMF.apply_ne_top (evalDist mx) none
@[simp] lemma probFailure_lt_top [HasEvalSPMF m] :
    Pr[⊥ | mx] < ∞ := PMF.apply_lt_top (evalDist mx) none
@[simp] lemma not_one_lt_probFailure [HasEvalSPMF m] :
    ¬ 1 < Pr[⊥ | mx] := not_lt.2 probFailure_le_one

@[simp] lemma one_le_probOutput_iff [HasEvalSPMF m] : 1 ≤ Pr[= x | mx] ↔ Pr[= x | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probOutput, or_false, eq_comm]
@[simp] lemma one_le_probEvent_iff [HasEvalSPMF m] : 1 ≤ Pr[p | mx] ↔ Pr[p | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probEvent, or_false, eq_comm]
@[simp] lemma one_le_probFailure_iff [HasEvalSPMF m] : 1 ≤ Pr[⊥ | mx] ↔ Pr[⊥ | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probFailure, or_false, eq_comm]

end bounds

lemma tsum_probOutput_eq_sub [HasEvalSPMF m] (mx : m α) :
    ∑' x : α, Pr[= x | mx] = 1 - Pr[⊥ | mx] := by
  refine ENNReal.eq_sub_of_add_eq probFailure_ne_top (tsum_probOutput_add_probFailure mx)

@[aesop safe apply]
lemma tsum_probOutput_eq_one' [HasEvalSPMF m] (mx : m α) (h : Pr[⊥ | mx] = 0) :
    ∑' x : α, Pr[= x | mx] = 1 := by
  rw [tsum_probOutput_eq_sub, h, tsub_zero]

lemma sum_probOutput_eq_sub [HasEvalSPMF m] [Fintype α] (mx : m α) :
    ∑ x : α, Pr[= x | mx] = 1 - Pr[⊥ | mx] := by
  rw [← tsum_fintype (L := .unconditional _), tsum_probOutput_eq_sub]

@[aesop safe apply]
lemma sum_probOutput_eq_one [HasEvalSPMF m] [Fintype α] (mx : m α) (h : Pr[⊥ | mx] = 0) :
    ∑ x : α, Pr[= x | mx] = 1 := by
  rw [sum_probOutput_eq_sub, h, tsub_zero]

lemma probFailure_eq_sub_tsum [HasEvalSPMF m] (mx : m α) :
    Pr[⊥ | mx] = 1 - ∑' x : α, Pr[= x | mx] := by
  refine ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
    (probFailure_add_tsum_probOutput mx)

lemma probFailure_eq_sub_sum [HasEvalSPMF m] [Fintype α] (mx : m α) :
    Pr[⊥ | mx] = 1 - ∑ x : α, Pr[= x | mx] := by
  rw [← tsum_fintype (L := .unconditional _), probFailure_eq_sub_tsum]

section bool

@[simp] lemma probEvent_False [HasEvalSPMF m] (mx : m α) : Pr[fun _ => False | mx] = 0 := by
  simp [probEvent_def]

lemma probEvent_false [HasEvalSPMF m] (mx : m α) : Pr[fun _ => false | mx] = 0 := by simp

@[simp] lemma probEvent_true_eq_sub [HasEvalSPMF m] (mx : m α) :
    Pr[fun _ => True | mx] = 1 - Pr[⊥ | mx] := by
  simp [probEvent_eq_tsum_indicator, probFailure_eq_sub_tsum]
  rw [sub_sub_cancel] <;> aesop

lemma probFailure_eq_sub_probEvent [HasEvalSPMF m] (mx : m α) :
    Pr[⊥ | mx] = 1 - Pr[fun _ => True | mx] := by
  refine ENNReal.eq_sub_of_add_eq (by simp only [ne_eq, probEvent_ne_top, not_false_eq_true]) ?_
  simp

end bool
