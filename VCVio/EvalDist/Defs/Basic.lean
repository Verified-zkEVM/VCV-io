/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Support

/-!
# Typeclasses for Denotational Monad Semantics

This file defines typeclasses `HasEvalSPMF` and `HasEvalPMF` for assigning denotational
probability semantics to monadic computations. We also introduce functions
`probOutput`, `probEvent`, and `probFailrue` with associated notation.

-- dtumad: document various probability notation definitions here
-/

open ENNReal

universe u v w

variable {m : Type u → Type v} [Monad m] {α β γ : Type u}

/-- The monad `m` can be evaluated to get a sub-distribution of outputs.
Should not be implemented manually if a `HasEvalPMF` instance already exists. -/
class HasEvalSPMF (m : Type u → Type v) [Monad m]
    extends HasEvalSet m where
  toSPMF : m →ᵐ SPMF
  support_eq {α : Type u} (mx : m α) : support mx = (toSPMF mx).support
  toSet := MonadHom.comp {
    toFun := @SPMF.support
    toFun_pure' x := Set.ext fun y => by simp
    toFun_bind' p q :=  Set.ext fun y => by simp
   } toSPMF

/-- The resulting distribution of running the monadic computation `mx`.
dtumad: I think we should eventually just deprecate this, just say `toSPMF`. -/
def evalDist [HasEvalSPMF m] {α : Type u} (mx : m α) : SPMF α :=
  HasEvalSPMF.toSPMF mx

lemma evalDist_def [HasEvalSPMF m] {α : Type u} (mx : m α) :
    evalDist mx = HasEvalSPMF.toSPMF mx := rfl

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

variable [HasEvalSPMF m]

-- dtumad: I think maybe we want to simp in the `←` direction here?
@[aesop norm (rule_sets := [UnfoldEvalDist]), grind =]
lemma probOutput_def (mx : m α) (x : α) : Pr[= x | mx] = evalDist mx x := rfl

@[grind =]
lemma mem_support_iff (mx : m α) (x : α) :
    x ∈ support mx ↔ Pr[= x | mx] ≠ 0 := by
  simp [HasEvalSPMF.support_eq, probOutput_def, evalDist_def]

lemma mem_support_iff_evalDist_apply_ne_zero (mx : m α) (x : α) :
    x ∈ support mx ↔ evalDist mx x ≠ 0 := by grind

@[grind =]
lemma mem_finSupport_iff [DecidableEq α] [HasEvalFinset m] (mx : m α) (x : α) :
    x ∈ finSupport mx ↔ Pr[= x | mx] ≠ 0 := by grind

@[aesop unsafe 50% forward]
lemma probOutput_ne_zero_of_mem_support {mx : m α} {x : α}
   (h : x ∈ support mx) : Pr[= x | mx] ≠ 0 := by rwa [mem_support_iff] at h

@[aesop safe norm, grind =]
lemma probOutput_eq_zero_of_not_mem_support {mx : m α} {x : α}
    (h : x ∉ support mx) : Pr[= x | mx] = 0 := by rwa [mem_support_iff, not_not] at h

@[simp low, grind =] lemma probOutput_eq_zero_iff (mx : m α) (x : α) :
    Pr[= x | mx] = 0 ↔ x ∉ support mx := by aesop

alias ⟨not_mem_support_of_probOutput_eq_zero, probOutput_eq_zero⟩ := probOutput_eq_zero_iff

variable (mx : m α) (x : α)

@[simp low] lemma zero_eq_probOutput_iff : 0 = Pr[= x | mx] ↔ x ∉ support mx := by
  rw [eq_comm, probOutput_eq_zero_iff]
alias ⟨_, zero_eq_probOutput⟩ := zero_eq_probOutput_iff

@[simp] lemma probOutput_eq_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[= x | mx] = 0 ↔ x ∉ finSupport mx := by rw [mem_finSupport_iff_mem_support]; aesop
alias ⟨not_mem_fin_support_of_probOutput_eq_zero, probOutput_eq_zero'⟩ := probOutput_eq_zero_iff

@[simp] lemma zero_eq_probOutput_iff' [HasEvalFinset m] [DecidableEq α] :
    0 = Pr[= x | mx] ↔ x ∉ finSupport mx := by rw [eq_comm, probOutput_eq_zero_iff']
alias ⟨_, zero_eq_probOutput'⟩ := zero_eq_probOutput_iff'

@[simp, grind =]
lemma probOutput_pos_iff : 0 < Pr[= x | mx] ↔ x ∈ support mx := by
  rw [pos_iff_ne_zero, ne_eq, probOutput_eq_zero_iff, not_not]
alias ⟨mem_support_of_probOutput_pos, probOutput_pos⟩ := probOutput_pos_iff

@[simp]
lemma probOutput_pos_iff' [HasEvalFinset m] [DecidableEq α] :
    0 < Pr[= x | mx] ↔ x ∈ finSupport mx := by grind
alias ⟨mem_finSupport_of_probOutput_pos, probOutput_pos'⟩ := probOutput_pos_iff'

instance decidablePred_probOutput_eq_zero [HasEvalSPMF m]
    [hm : HasEvalSet.Decidable m] (mx : m α) :
    DecidablePred (Pr[= · | mx] = 0) := by
  simp only [probOutput_eq_zero_iff]
  infer_instance

@[aesop unsafe apply]
lemma probOutput_ne_zero (h : x ∈ support mx) : Pr[= x | mx] ≠ 0 := by simp [h]

@[aesop unsafe apply]
lemma probOutput_ne_zero' [HasEvalFinset m] [DecidableEq α]
    (h : x ∈ finSupport mx) : Pr[= x | mx] ≠ 0 := by
  exact probOutput_ne_zero mx x (mem_support_of_mem_finSupport h)

@[simp]
lemma support_probOutput : Function.support (probOutput mx) = support mx := by aesop

end probOutput

section probEvent

@[aesop norm (rule_sets := [UnfoldEvalDist])]
lemma probEvent_def [HasEvalSPMF m] (mx : m α) (p : α → Prop) :
    Pr[p | mx] = (evalDist mx).run.toOuterMeasure (some '' {x | p x}) := rfl

@[grind =]
lemma probEvent_eq_tsum_indicator [HasEvalSPMF m] (mx : m α) (p : α → Prop) :
    Pr[p | mx] = ∑' x : α, {x | p x}.indicator (Pr[= · | mx]) x := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable,
    Set.indicator_image (Option.some_injective _), Function.comp_def, probOutput_def,
    SPMF.apply_eq_toPMF_some]

@[grind =]
lemma probEvent_eq_sum_fintype_indicator [HasEvalSPMF m] [Fintype α]
    (mx : m α) (p : α → Prop) : Pr[p | mx] = ∑ x : α, {x | p x}.indicator (Pr[= · | mx]) x :=
  (probEvent_eq_tsum_indicator mx p).trans (tsum_fintype _)

@[grind =]
lemma probEvent_eq_tsum_ite [HasEvalSPMF m] (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑' x : α, if p x then Pr[= x | mx] else 0 := by
  grind [Set.indicator]

@[grind =]
lemma probEvent_eq_sum_fintype_ite [HasEvalSPMF m] [Fintype α] (mx : m α)
    (p : α → Prop) [DecidablePred p] : Pr[p | mx] = ∑ x : α, if p x then Pr[= x | mx] else 0 := by
  grind [Set.indicator]

lemma probEvent_eq_tsum_subtype [HasEvalSPMF m] (mx : m α) (p : α → Prop) :
    Pr[p | mx] = ∑' x : {x | p x}, Pr[= x | mx] := by
  rw [probEvent_eq_tsum_indicator, tsum_subtype]

lemma probEvent_eq_sum_filter_univ [HasEvalSPMF m] [Fintype α]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑ x ∈ Finset.univ.filter p, Pr[= x | mx] := by
  rw [probEvent_eq_sum_fintype_ite, Finset.sum_filter]

variable [HasEvalSPMF m]

section zero

variable {mx : m α} {p : α → Prop}

@[simp, grind =]
lemma probEvent_eq_zero_iff :
    Pr[p | mx] = 0 ↔ ∀ x ∈ support mx, ¬ p x := by
  rw [probEvent_eq_tsum_indicator]; aesop
alias ⟨_, probEvent_eq_zero⟩ := probEvent_eq_zero_iff

@[simp]
lemma probEvent_eq_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[p | mx] = 0 ↔ ∀ x ∈ finSupport mx, ¬ p x := by grind
alias ⟨_, probEvent_eq_zero'⟩ := probEvent_eq_zero_iff'

lemma probEvent_ne_zero_iff : Pr[p | mx] ≠ 0 ↔ ∃ x ∈ support mx, p x := by  grind
alias ⟨_, probEvent_ne_zero⟩ := probEvent_ne_zero_iff

lemma probEvent_ne_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[p | mx] ≠ 0 ↔ ∃ x ∈ finSupport mx, p x := by aesop
alias ⟨_, probEvent_ne_zero'⟩ := probEvent_ne_zero_iff'

@[simp, grind =]
lemma probEvent_pos_iff : 0 < Pr[p | mx] ↔ ∃ x ∈ support mx, p x := by
  simp [pos_iff_ne_zero]
alias ⟨_, probEvent_pos⟩ := probEvent_pos_iff

@[simp]
lemma probEvent_pos_iff' [HasEvalFinset m] [DecidableEq α] :
    0 < Pr[p | mx] ↔ ∃ x ∈ finSupport mx, p x := by grind
alias ⟨_, probEvent_pos'⟩ := probEvent_pos_iff'

end zero

lemma probEvent_eq_tsum_subtype_mem_support (mx : m α) (p : α → Prop) :
    Pr[p | mx] = ∑' x : {x ∈ support mx | p x}, Pr[= x | mx] := by
  simp_rw [probEvent_eq_tsum_subtype, tsum_subtype]
  refine tsum_congr (λ x ↦ ?_)
  by_cases hpx : p x
  · refine (if_pos hpx).trans ?_
    by_cases hx : x ∈ support mx
    · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_self, ↓reduceIte]
    · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_true, ↓reduceIte,
      probOutput_eq_zero_iff, not_false_eq_true]
  · exact (if_neg hpx).trans (by simp [Set.indicator, hpx])

lemma probEvent_eq_tsum_subtype_support_ite (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑' x : support mx, if p x then Pr[= x | mx] else 0 :=
calc
  Pr[p | mx] = (∑' x, if p x then Pr[= x | mx] else 0) := by rw [probEvent_eq_tsum_ite mx p]
  _ = ∑' x, (support mx).indicator (λ x ↦ if p x then Pr[= x | mx] else 0) x := by
    refine tsum_congr (λ x ↦ ?_)
    unfold Set.indicator
    split_ifs with h1 h2 h2 <;> simp [h1, h2]
  _ = ∑' x : support mx, if p x then Pr[= x | mx] else 0 := by
    rw [tsum_subtype (support mx) (λ x ↦ if p x then Pr[= x | mx] else 0)]

lemma probEvent_eq_sum_filter_finSupport [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑ x ∈ (finSupport mx).filter p, Pr[= x | mx] :=
  (probEvent_eq_tsum_ite mx p).trans <|
    (tsum_eq_sum' <| by simp; tauto).trans
      (Finset.sum_congr rfl <| λ x hx ↦ if_pos (Finset.mem_filter.1 hx).2)

lemma probEvent_eq_sum_finSupport_ite [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[p | mx] = ∑ x ∈ finSupport mx, if p x then Pr[= x | mx] else 0 := by
  rw [probEvent_eq_sum_filter_finSupport, Finset.sum_filter]

/-- If two events are equivalent on the support of `mx` then they have the same output chance. -/
@[aesop unsafe apply, grind .]
lemma probEvent_ext {mx : m α} {p q : α → Prop}
    (h : ∀ x ∈ support mx, p x ↔ q x) : Pr[p | mx] = Pr[q | mx] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr fun x => ?_
  split_ifs <;> grind

@[simp, grind =_, aesop unsafe norm]
lemma probEvent_eq_eq_probOutput (mx : m α) (x : α) :
    Pr[(· = x) | mx] = Pr[= x | mx] := by
  simp [probEvent_def, PMF.toOuterMeasure_apply_singleton, probOutput_def,
    SPMF.apply_eq_toPMF_some]

@[simp, grind =_, aesop unsafe norm]
lemma probEvent_eq_eq_probOutput' (mx : m α) (x : α) :
    Pr[(x = ·) | mx] = Pr[= x | mx] := by
  grind

end probEvent

section probFailure

@[aesop norm (rule_sets := [UnfoldEvalDist]), grind =]
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

end probability_notation

@[simp] -- TODO: versions for other constructions?
lemma evalDist_cast {m} [Monad m] [HasEvalSPMF m] (h : α = β) (mx : m α):
    evalDist (cast (congrArg m h) mx) =
      cast (congrArg SPMF h) (evalDist mx) := by
  induction h; rfl

lemma evalDist_ext {m n} [Monad m] [HasEvalSPMF m] [Monad n] [HasEvalSPMF n]
    {mx : m α} {mx' : n α} (h : ∀ x, Pr[= x | mx] = Pr[= x | mx']) : evalDist mx = evalDist mx' :=
  SPMF.ext h

lemma evalDist_ext_iff {m n} [Monad m] [HasEvalSPMF m] [Monad n] [HasEvalSPMF n]
    {mx : m α} {mx' : n α} : evalDist mx = evalDist mx' ↔ ∀ x, Pr[= x | mx] = Pr[= x | mx'] := by
  refine ⟨fun h => ?_, evalDist_ext⟩
  simp [probOutput_def, h]

@[simp, grind =]
lemma evalDist_eq_liftM_iff [HasEvalSPMF m] (mx : m α) (p : PMF α) :
    evalDist mx = liftM p ↔ ∀ x, Pr[= x | mx] = p x := by
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · simp [probOutput_def, h]
  · simpa [SPMF.eq_liftM_iff_forall, probOutput_def] using h

@[simp, grind =]
lemma evalDist_eq_mk_iff [HasEvalSPMF m] (mx : m α) (p : PMF (Option α)) :
    evalDist mx = SPMF.mk p ↔ ∀ x, Pr[= x | mx] = p (some x) := by aesop

@[aesop unsafe apply]
lemma evalDist_eq_liftM [HasEvalSPMF m] {mx : m α} {p : PMF α}
    (h : ∀ x, Pr[= x | mx] = p x) : evalDist mx = liftM p := by aesop

@[simp]
lemma evalDist_apply_eq_zero_iff [HasEvalSPMF m] (mx : m α)
    (x : Option α) :
    (evalDist mx).run x = 0 ↔ x.rec (Pr[⊥ | mx] = 0) (· ∉ support mx) := by
  induction x with
  | none => simp [probFailure_def]
  | some y => simp [OptionT.run, mem_support_iff_evalDist_apply_ne_zero,
      SPMF.apply_eq_toPMF_some, SPMF.toPMF]

@[simp]
lemma evalDist_apply_eq_zero_iff' [HasEvalSPMF m] [HasEvalFinset m] [DecidableEq α] (mx : m α)
    (x : Option α) : (evalDist mx).run x = 0 ↔ x.rec (Pr[⊥ | mx] = 0) (· ∉ finSupport mx) := by
  rw [evalDist_apply_eq_zero_iff]
  grind

section ite

variable (p : Prop) [Decidable p]

@[simp] lemma evalDist_ite [HasEvalSPMF m] (mx mx' : m α) :
    evalDist (if p then mx else mx') = if p then evalDist mx else evalDist mx' := by grind

@[simp] lemma probOutput_ite [HasEvalSPMF m] (x : α) (mx mx' : m α) :
    Pr[= x | if p then mx else mx'] = if p then Pr[= x | mx] else Pr[= x | mx'] := by aesop

@[simp] lemma probFailure_ite [HasEvalSPMF m] (mx mx' : m α) :
    Pr[⊥ | if p then mx else mx'] = if p then Pr[⊥ | mx] else Pr[⊥ | mx'] := by grind

@[simp] lemma probEvent_ite [HasEvalSPMF m] (mx mx' : m α) (q : α → Prop) :
    Pr[q | if p then mx else mx'] = if p then Pr[q | mx] else Pr[q | mx'] := by aesop

end ite

section eqRec

lemma evalDist_eqRec [HasEvalSPMF m] (h : α = β) (mx : m α) :
    evalDist (h ▸ mx : m β) = h ▸ evalDist mx := by grind

lemma probOutput_eqRec [HasEvalSPMF m] (h : α = β) (mx : m α) (y : β) :
    Pr[= y | h ▸ mx] = Pr[= h ▸ y | mx] := by grind

@[simp] lemma probFailure_eqRec [HasEvalSPMF m] (h : α = β) (mx : m α) :
    Pr[⊥ | h ▸ mx] = Pr[⊥ | mx] := by grind

lemma probEvent_eqRec [HasEvalSPMF m] (h : α = β) (mx : m α) (q : β → Prop) :
    Pr[q | h ▸ mx] = Pr[fun x ↦ q (h ▸ x) | mx] := by induction h; rfl

end eqRec

section sums

/-- Connection between the two different probability notations. -/
lemma probOutput_true_eq_probEvent {α} {m : Type → Type u} [Monad m] [HasEvalSPMF m]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] = Pr[p | mx] := by
  simp [probEvent_eq_tsum_indicator, probOutput_def, evalDist, map_eq_bind_pure_comp]
  congr 1; aesop

@[simp] lemma tsum_probOutput_add_probFailure [HasEvalSPMF m] (mx : m α) :
    (∑' x, Pr[= x | mx]) + Pr[⊥ | mx] = 1 := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp] lemma probFailure_add_tsum_probOutput [HasEvalSPMF m] (mx : m α) :
    Pr[⊥ | mx] + ∑' x, Pr[= x | mx] = 1 := by
  aesop (rule_sets := [UnfoldEvalDist])

end sums

section bounds

variable {mx : m α} {mxe : OptionT m α} {x : α} {p : α → Prop}

@[simp, grind .] lemma probOutput_le_one [HasEvalSPMF m] :
    Pr[= x | mx] ≤ 1 := PMF.coe_le_one (evalDist mx) x
@[simp, grind .] lemma probOutput_ne_top [HasEvalSPMF m] :
    Pr[= x | mx] ≠ ∞ := PMF.apply_ne_top (evalDist mx) x
@[simp, grind .] lemma probOutput_lt_top [HasEvalSPMF m] :
    Pr[= x | mx] < ∞ := PMF.apply_lt_top (evalDist mx) x
@[simp, grind .] lemma not_one_lt_probOutput [HasEvalSPMF m] :
    ¬ 1 < Pr[= x | mx] := not_lt.2 probOutput_le_one

@[simp] lemma tsum_probOutput_le_one [HasEvalSPMF m] : ∑' x : α, Pr[= x | mx] ≤ 1 :=
  le_of_le_of_eq (le_add_self) (probFailure_add_tsum_probOutput mx)
@[simp] lemma tsum_probOutput_ne_top [HasEvalSPMF m] : ∑' x : α, Pr[= x | mx] ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one

@[simp, grind .] lemma probEvent_le_one [HasEvalSPMF m] : Pr[p | mx] ≤ 1 := by
  rw [probEvent_def, PMF.toOuterMeasure_apply]
  refine le_of_le_of_eq (ENNReal.tsum_le_tsum ?_) ((evalDist mx).tsum_coe)
  exact Set.indicator_le_self (some '' {x | p x}) _

@[simp, grind .] lemma probEvent_ne_top [HasEvalSPMF m] :
    Pr[p | mx] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
@[simp, grind .] lemma probEvent_lt_top [HasEvalSPMF m] :
    Pr[p | mx] < ∞ := lt_top_iff_ne_top.2 probEvent_ne_top
@[simp, grind .] lemma not_one_lt_probEvent [HasEvalSPMF m] :
    ¬ 1 < Pr[p | mx] := not_lt.2 probEvent_le_one

@[simp, grind .] lemma probFailure_le_one [HasEvalSPMF m] :
    Pr[⊥ | mx] ≤ 1 := PMF.coe_le_one (evalDist mx) none
@[simp, grind .] lemma probFailure_ne_top [HasEvalSPMF m] :
    Pr[⊥ | mx] ≠ ∞ := PMF.apply_ne_top (evalDist mx) none
@[simp, grind .] lemma probFailure_lt_top [HasEvalSPMF m] :
    Pr[⊥ | mx] < ∞ := PMF.apply_lt_top (evalDist mx) none
@[simp, grind .] lemma not_one_lt_probFailure [HasEvalSPMF m] :
    ¬ 1 < Pr[⊥ | mx] := not_lt.2 probFailure_le_one

@[simp, grind =]
lemma one_le_probOutput_iff [HasEvalSPMF m] : 1 ≤ Pr[= x | mx] ↔ Pr[= x | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probOutput, or_false, eq_comm]

@[simp, grind =]
lemma one_le_probEvent_iff [HasEvalSPMF m] : 1 ≤ Pr[p | mx] ↔ Pr[p | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probEvent, or_false, eq_comm]

@[simp, grind =]
lemma one_le_probFailure_iff [HasEvalSPMF m] : 1 ≤ Pr[⊥ | mx] ↔ Pr[⊥ | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probFailure, or_false, eq_comm]

@[simp, grind =]
lemma probOutput_eq_one_iff [HasEvalSPMF m] :
    Pr[= x | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ support mx = {x} := by
  rw [← probEvent_eq_eq_probOutput]
  simp [probOutput_def, probFailure_def, SPMF.apply_eq_toPMF_some, PMF.apply_eq_one_iff,
    Set.ext_iff, Option.forall, mem_support_iff_evalDist_apply_ne_zero]
alias ⟨_, probOutput_eq_one⟩ := probOutput_eq_one_iff

@[simp, grind =]
lemma one_eq_probOutput_iff [HasEvalSPMF m] :
    1 = Pr[= x | mx] ↔ Pr[⊥ | mx] = 0 ∧ support mx = {x} := by
  rw [eq_comm, probOutput_eq_one_iff]
alias ⟨_, one_eq_probOutput⟩ := one_eq_probOutput_iff

@[simp, grind =]
lemma probOutput_eq_one_iff' [HasEvalSPMF m] [HasEvalFinset m] [DecidableEq α] :
    Pr[= x | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ finSupport mx = {x} := by
  rw [probOutput_eq_one_iff, finSupport_eq_iff_support_eq_coe, Finset.coe_singleton]
alias ⟨_, probOutput_eq_one'⟩ := probOutput_eq_one_iff'

@[simp, grind =]
lemma one_eq_probOutput_iff' [HasEvalSPMF m] [HasEvalFinset m] [DecidableEq α] :
    1 = Pr[= x | mx] ↔ Pr[⊥ | mx] = 0 ∧ finSupport mx = {x} := by
  rw [eq_comm, probOutput_eq_one_iff']
alias ⟨_, one_eq_probOutput'⟩ := one_eq_probOutput_iff'

end bounds

section mono_le

variable [HasEvalSPMF m] (mx : m α) (r : ℝ≥0∞)

@[simp]  lemma probFailure_mul_le : Pr[⊥ | mx] * r ≤ r :=
  mul_le_of_le_one_left' <| by simp

@[simp]  lemma mul_probFailure_le : r * Pr[⊥ | mx] ≤ r :=
  mul_le_of_le_one_right' <| by simp

@[simp] lemma probOutput_mul_le (x : α) : Pr[= x | mx] * r ≤ r :=
  mul_le_of_le_one_left' <| by simp

@[simp] lemma mul_probOutput_le (x : α) : r * Pr[= x | mx] ≤ r :=
  mul_le_of_le_one_right' <| by simp

@[simp] lemma probEvent_mul_le (p : α → Prop) : Pr[p | mx] * r ≤ r :=
  mul_le_of_le_one_left' <| by simp

@[simp] lemma mul_probEvent_le (p : α → Prop) : r * Pr[p | mx] ≤ r :=
  mul_le_of_le_one_right' <| by simp

end mono_le

section sum_probOutput

variable [HasEvalSPMF m]

@[simp]
lemma tsum_probOutput_eq_sub (mx : m α) :
    ∑' x : α, Pr[= x | mx] = 1 - Pr[⊥ | mx] := by
  refine ENNReal.eq_sub_of_add_eq probFailure_ne_top (tsum_probOutput_add_probFailure mx)

lemma tsum_probOutput_eq_one' {mx : m α} (h : Pr[⊥ | mx] = 0) :
    ∑' x : α, Pr[= x | mx] = 1 := by simp [h]

@[simp]
lemma tsum_support_probOutput_eq_sub (mx : m α) :
    ∑' x : support mx, Pr[= x | mx] = 1 - Pr[⊥ | mx] := by
  rw [tsum_subtype_eq_of_support_subset] <;> simp

lemma tsum_support_probOutput_eq_one' {mx : m α} (h : Pr[⊥ | mx] = 0) :
    ∑' x : support mx, Pr[= x | mx] = 1 := by simp [h]

@[simp]
lemma sum_probOutput_eq_sub [Fintype α] (mx : m α) :
    ∑ x : α, Pr[= x | mx] = 1 - Pr[⊥ | mx] := by
  rw [← tsum_fintype (L := .unconditional _), tsum_probOutput_eq_sub]

lemma sum_probOutput_eq_one [Fintype α] {mx : m α} (h : Pr[⊥ | mx] = 0) :
    ∑ x : α, Pr[= x | mx] = 1 := by simp [h]

@[simp]
lemma sum_finSupport_probOutput_eq_sub [HasEvalFinset m] [DecidableEq α] (mx : m α) :
    ∑ x ∈ finSupport mx, Pr[= x | mx] = 1 - Pr[⊥ | mx] := by
  rw [← tsum_probOutput_eq_sub, tsum_eq_sum]
  simp

lemma sum_finSupport_probOutput_eq_one [HasEvalFinset m] [DecidableEq α]
    {mx : m α} (h : Pr[⊥ | mx] = 0) : ∑ x ∈ finSupport mx, Pr[= x | mx] = 1 := by simp [h]

end sum_probOutput

lemma probFailure_eq_sub_tsum [HasEvalSPMF m] (mx : m α) :
    Pr[⊥ | mx] = 1 - ∑' x : α, Pr[= x | mx] := by
  refine ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
    (probFailure_add_tsum_probOutput mx)

lemma probFailure_eq_sub_sum [HasEvalSPMF m] [Fintype α] (mx : m α) :
    Pr[⊥ | mx] = 1 - ∑ x : α, Pr[= x | mx] := by
  rw [← tsum_fintype (L := .unconditional _), probFailure_eq_sub_tsum]

section bool

variable [HasEvalSPMF m]

@[simp]
lemma probEvent_False (mx : m α) :
    Pr[fun _ => False | mx] = 0 := by grind

lemma probEvent_false (mx : m α) :
    Pr[fun _ => false | mx] = 0 := by aesop

@[simp, grind =]
lemma probEvent_True_eq_sub (mx : m α) :
    Pr[fun _ => True | mx] = 1 - Pr[⊥ | mx] := by
  simp [probEvent_eq_tsum_indicator]

lemma probEvent_true_eq_sub (mx : m α) :
    Pr[fun _ => true | mx] = 1 - Pr[⊥ | mx] := by grind

lemma probFailure_eq_sub_probEvent (mx : m α) :
    Pr[⊥ | mx] = 1 - Pr[fun _ => True | mx] := by
  refine ENNReal.eq_sub_of_add_eq (by simp only [ne_eq, probEvent_ne_top, not_false_eq_true]) ?_
  simp only [probEvent_True_eq_sub, probFailure_le_one, add_tsub_cancel_of_le]

lemma probFailure_eq_one_iff_probEvent_true (mx : m α) :
    Pr[⊥ | mx] = 1 ↔ Pr[fun _ => True | mx] = 0 := by
  rw [probFailure_eq_sub_probEvent, ← ENNReal.toReal_eq_one_iff]
  rw [ENNReal.toReal_sub_of_le (by grind) (by simp)]
  simp [tsub_eq_zero_iff_le, ENNReal.toReal_eq_one_iff]

@[simp, grind =]
lemma probFailure_eq_one_iff (mx : m α) : Pr[⊥ | mx] = 1 ↔ support mx = ∅ := by
  simp [probFailure_eq_one_iff_probEvent_true, probEvent_eq_tsum_subtype_mem_support, Set.ext_iff]

@[aesop unsafe forward]
lemma probFailure_eq_one {mx : m α} (h : support mx = ∅) : Pr[⊥ | mx] = 1 := by grind

@[simp, aesop norm]
lemma probEvent_const (mx : m α) (p : Prop) [Decidable p] :
    Pr[fun _ => p | mx] = if p then (1 - Pr[⊥ | mx]) else 0 := by
  aesop

end bool

/-- The monad `m` can be evaluated to get a distribution of outputs. -/
class HasEvalPMF (m : Type u → Type v) [Monad m]
    extends HasEvalSPMF m where
  toPMF : m →ᵐ PMF
  toSPMF := MonadHom.comp PMF.toSPMF' toPMF
  toSPMF_eq {α : Type u} (mx : m α) : toSPMF mx = liftM (toPMF mx) := by rfl

attribute [grind =] HasEvalPMF.toSPMF_eq

namespace HasEvalPMF

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]
  [HasEvalPMF m] (mx : m α) (x : α)

lemma evalDist_of_hasEvalPMF_def (mx : m α) :
    evalDist mx = liftM (HasEvalPMF.toPMF mx) := by
  simp [evalDist_def, HasEvalPMF.toSPMF_eq]

/-- The `evalDist` arising from a `HasEvalPMF` instance never fails. -/
@[simp, grind =]
lemma probFailure_eq_zero (mx : m α) : Pr[⊥ | mx] = 0 := by
  simp [probFailure_def, evalDist_of_hasEvalPMF_def]

lemma tsum_probOutput_eq_one (mx : m α) :
    ∑' x, Pr[= x | mx] = 1 := by simp

lemma tsum_support_probOutput_eq_one (mx : m α) :
    ∑' x : support mx, Pr[= x | mx] = 1 := by simp

lemma sum_probOutput_eq_one [Fintype α] (mx : m α) : ∑ x : α, Pr[= x | mx] = 1 := by simp

lemma sum_finSupport_probOutput_eq_one [HasEvalFinset m] [DecidableEq α] (mx : m α) :
    ∑ x ∈ finSupport mx, Pr[= x | mx] = 1 := by simp

end HasEvalPMF

-- @[simp low]
-- lemma probEvent_eq_one_iff : [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x := by
--   rw [probEvent, PMF.toOuterMeasure_apply_eq_one_iff]
--   simp [support_evalDist]
--   split_ifs with hoa
--   · simp [hoa, Set.preimage_image_eq _ (some_injective α), Set.subset_def]
--   · simp [hoa]
--     intro h
--     specialize h (Set.mem_insert none _)
--     simp at h
-- alias ⟨_, probEvent_eq_one⟩ := probEvent_eq_one_iff
-- @[simp low]
-- lemma one_eq_probEvent_iff : 1 = [p | oa] ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x := by
--   rw [eq_comm, probEvent_eq_one_iff]
-- alias ⟨_, one_eq_probEvent⟩ := probEvent_eq_one_iff

-- @[simp]
-- lemma probEvent_eq_one_iff' [spec.DecidableEq] [DecidableEq α] :
--     [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.finSupport, p x := by
--   simp_rw [probEvent_eq_one_iff, mem_finSupport_iff_mem_support]
-- alias ⟨_, probEvent_eq_one'⟩ := probEvent_eq_one_iff'
-- @[simp]
-- lemma one_eq_probEvent_iff' [spec.DecidableEq] [DecidableEq α] :
--     1 = [p | oa] ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.finSupport, p x := by
--   rw [eq_comm, probEvent_eq_one_iff']
-- alias ⟨_, one_eq_probEvent'⟩ := one_eq_probEvent_iff'

-- lemma mem_support_iff_probOutput_ne_zero : x ∈ oa.support ↔ [= x | oa] ≠ 0 := by
--   simp only [ne_eq, probOutput_eq_zero_iff, not_not]
-- lemma mem_finSupport_iff_probOutput_ne_zero [spec.DecidableEq] [DecidableEq α] :
--     x ∈ oa.finSupport ↔ [= x | oa] ≠ 0 := by
--   rw [mem_finSupport_iff_mem_support, mem_support_iff_probOutput_ne_zero]

-- lemma mem_support_iff_probOutput_pos : x ∈ oa.support ↔ 0 < [= x | oa] := by
--   simp only [probOutput_pos_iff]

-- lemma not_mem_support_iff_probOutput_eq_zero : x ∉ oa.support ↔ [= x | oa] = 0 := by
--   simp only [probOutput_eq_zero_iff]

-- variable {oa x p q}

-- /-- If `p` implies `q` on the `support` of a computation then it is more likely to happen. -/
-- lemma probEvent_mono (h : ∀ x ∈ oa.support, p x → q x) : [p | oa] ≤ [q | oa] := by
--   refine PMF.toOuterMeasure_mono _ λ x hx ↦ match x with
--   | none => by simp at hx
--   | some x => by
--       simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, some.injEq, exists_eq_right,
--         PMF.mem_support_iff, ne_eq, evalDist_apply_eq_zero_iff, not_not] at hx
--       exact ⟨x, h x hx.2 hx.1, rfl⟩

-- /-- If `p` implies `q` on the `finSupport` of a computation then it is more likely to happen. -/
-- lemma probEvent_mono' [spec.DecidableEq] [DecidableEq α]
--     (h : ∀ x ∈ oa.finSupport, p x → q x) : [p | oa] ≤ [q | oa] :=
--   probEvent_mono (λ x hx hpx ↦ h x (mem_finSupport_of_mem_support oa hx) hpx)

-- @[simp]
-- lemma function_support_probOutput : Function.support ([= · | oa]) = oa.support := by
--   simp only [Function.support, ne_eq, probOutput_eq_zero_iff, not_not, Set.setOf_mem_eq]

-- lemma mem_support_iff_of_evalDist_eq {oa : OracleComp spec α} {oa' : OracleComp spec' α}
--     (h : evalDist oa = evalDist oa') (x : α) : x ∈ oa.support ↔ x ∈ oa'.support := by
--   simp only [mem_support_iff_probOutput_ne_zero, probOutput_def, h]

-- lemma mem_finSupport_iff_of_evalDist_eq [spec.DecidableEq] [spec'.DecidableEq]
--     [DecidableEq α] {oa : OracleComp spec α} {oa' : OracleComp spec' α}
--     (h : evalDist oa = evalDist oa') (x : α) : x ∈ oa.finSupport ↔ x ∈ oa'.finSupport := by
--   simp only [mem_finSupport_iff_mem_support, mem_support_iff_of_evalDist_eq h]
