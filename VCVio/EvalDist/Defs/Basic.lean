/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.EvalDist.Defs.Support
import ToMathlib.ProbabilityTheory.SPMF

/-!
# Typeclasses for Denotational Monad Semantics

This file builds atop `MonadLiftT m SPMF` / `MonadLiftT m PMF` for assigning denotational
probability semantics to monadic computations. We also introduce functions
`probOutput`, `probEvent`, and `probFailure` with associated notation.

-- dtumad: document various probability notation definitions here
-/

open ENNReal

universe u v w

variable {m : Type u → Type v} {α β γ : Type u}

/-! ## `MonadLiftT m SetM` and `MonadLiftT m SPMF`

The `SetM` / `SPMF` lifts exposed by this layer are declared as `MonadLiftT`,
not `MonadLift`. Total semantic sources may still expose a plain `MonadLift`
into `PMF`; the important point here is that support is never obtained by a
transitive `m → SPMF → SetM` path, and parameterized/typeclass-gated
probability lifts avoid `MonadLift` instance search. There are two independent
reasons.

**No transitive `SPMF → SetM` lift.** The `MonadLiftT SPMF SetM` instance below
exists so `support` and friends work on raw `SPMF α`. Crucially it is declared
as `MonadLiftT` rather than `MonadLift`, which means Lean's `monadLiftTrans`
(which requires `MonadLift n o` for the outer hop) cannot chain it: a monad
`m` with `MonadLiftT m SPMF` does **not** automatically gain `MonadLiftT m SetM`
via transitivity. Each monad declares its `MonadLiftT m SetM` directly — e.g.
`OracleComp` uses the syntactic `simulateQ` into `SetM` (which doesn't require
`[spec.Fintype]`), and `EvalDistCompatible` records the propositional coherence
between that syntactic support and `SPMF.support ∘ evalDist`.

**Resolution fragility for parameterized + typeclass-gated lifts.** Lifts whose
source is parameterized (`OracleComp spec`, `OptionT m`, `StateT σ m`, …) and
which are gated by a typeclass on the parameter (`[IsProbabilitySpec spec]`,
`[MonadLiftT m SPMF]`, …) must also be `MonadLiftT`, not `MonadLift`. Demoting
to `MonadLift` forces Lean to find the instance through its transitive
instance, whose outer hop is `MonadLift n o` with `n` a `semiOutParam`. When
the recursion lands on a parameterized head like `MonadLift (OracleComp ?spec) PMF`,
Lean has to simultaneously unify `?spec` through the `semiOutParam`, discharge
the typeclass premise on `?spec`, and pin down `?spec` from the inner reflexive
premise — a combination Lean's instance search refuses to chase. The direct
`MonadLiftT` declaration sidesteps this with a single-step head match. -/

/-- Direct `MonadLiftT SPMF SetM` (only on `SPMF` itself — not the transitive
`MonadLift` that would create a diamond). -/
instance instMonadLiftTSPMFSetM : MonadLiftT SPMF SetM where
  monadLift := SPMF.support

instance instLawfulMonadLiftTSPMFSetM : LawfulMonadLiftT SPMF SetM where
  monadLift_pure := SPMF.support_pure
  monadLift_bind := SPMF.support_bind

/-- Coherence between `support` (via `MonadLiftT m SetM`) and `evalDist`
(via `MonadLiftT m SPMF`): `x ∈ support mx` iff `Pr[= x | mx] ≠ 0`.

This typeclass is exported by every monad that admits both lifts and they
agree on outputs — i.e. `support mx = SPMF.support (evalDist mx)`. -/
class EvalDistCompatible (m : Type u → Type v) [MonadLiftT m SetM]
    [MonadLiftT m SPMF] : Prop where
  /-- The reachable outputs of `mx` (via `support`) are exactly the outputs with
  nonzero probability in `evalDist mx`. -/
  support_eq_SPMF_support {α : Type u} (mx : m α) :
    SetM.run (liftM mx : SetM α) = SPMF.support (liftM mx : SPMF α)

export EvalDistCompatible (support_eq_SPMF_support)

/-- `SPMF` is trivially compatible: both lifts coincide on the nose. -/
instance : EvalDistCompatible SPMF where
  support_eq_SPMF_support _ := rfl

/-- The resulting distribution of running the monadic computation `mx`. -/
@[reducible, inline]
def evalDist [MonadLiftT m SPMF] {α : Type u} (mx : m α) : SPMF α := liftM mx

/-- Evaluation distribution notation for any monad lifting into `SPMF`. -/
notation "𝒟[" mx "]" => evalDist mx

lemma evalDist_def [MonadLiftT m SPMF] {α : Type u} (mx : m α) :
    𝒟[mx] = liftM mx := rfl

section probability_notation

/-- Probability that a computation `mx` returns the value `x`. -/
def probOutput [MonadLiftT m SPMF] (mx : m α) (x : α) : ℝ≥0∞ :=
  𝒟[mx] x

/-- Probability that a computation `mx` outputs a value satisfying `p`. -/
noncomputable def probEvent [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  (𝒟[mx]).run.toOuterMeasure (some '' {x | p x})

/-- Probability that a computation `mx` will fail to return a value. -/
def probFailure [MonadLiftT m SPMF] (mx : m α) : ℝ≥0∞ :=
  (𝒟[mx]).run none

/-- Probability that a computation returns a particular output. -/
notation "Pr[= " x " | " mx "]" => probOutput mx x

/-- Probability that a computation returns a value satisfying a predicate. -/
macro (name := probEventNotation) "Pr[ " p:term " | " mx:term "]" : term =>
  `(probEvent $mx $p)

/-- Probability that a computation fails to return a value. -/
notation "Pr[⊥" " | " mx "]" => probFailure mx

section probOutput

variable [MonadLiftT m SPMF]

-- dtumad: I think maybe we want to simp in the `←` direction here?
@[aesop norm (rule_sets := [UnfoldEvalDist]), grind =]
lemma probOutput_def (mx : m α) (x : α) : Pr[= x | mx] = evalDist mx x := rfl

variable [MonadLiftT m SetM] [EvalDistCompatible m]

@[grind =]
lemma mem_support_iff (mx : m α) (x : α) :
    x ∈ support mx ↔ Pr[= x | mx] ≠ 0 := by
  rw [support_def, support_eq_SPMF_support, SPMF.mem_support_iff, probOutput_def, evalDist_def]

lemma mem_support_iff_evalDist_apply_ne_zero (mx : m α) (x : α) :
    x ∈ support mx ↔ 𝒟[mx] x ≠ 0 := by grind

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

@[simp, grind =] lemma probOutput_eq_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[= x | mx] = 0 ↔ x ∉ finSupport mx := by rw [mem_finSupport_iff_mem_support]; aesop
alias ⟨not_mem_fin_support_of_probOutput_eq_zero, probOutput_eq_zero'⟩ := probOutput_eq_zero_iff'

@[simp, grind =] lemma zero_eq_probOutput_iff' [HasEvalFinset m] [DecidableEq α] :
    0 = Pr[= x | mx] ↔ x ∉ finSupport mx := by rw [eq_comm, probOutput_eq_zero_iff']
alias ⟨_, zero_eq_probOutput'⟩ := zero_eq_probOutput_iff'

@[simp, grind =]
lemma probOutput_pos_iff : 0 < Pr[= x | mx] ↔ x ∈ support mx := by
  rw [pos_iff_ne_zero, ne_eq, probOutput_eq_zero_iff, not_not]
alias ⟨mem_support_of_probOutput_pos, probOutput_pos⟩ := probOutput_pos_iff

@[simp, grind =]
lemma probOutput_pos_iff' [HasEvalFinset m] [DecidableEq α] :
    0 < Pr[= x | mx] ↔ x ∈ finSupport mx := by grind
alias ⟨mem_finSupport_of_probOutput_pos, probOutput_pos'⟩ := probOutput_pos_iff'

instance decidablePred_probOutput_eq_zero
    [hm : HasEvalSet.Decidable m] (mx : m α) :
    DecidablePred (Pr[= · | mx] = 0) := by
  simp only [probOutput_eq_zero_iff]
  infer_instance

@[aesop unsafe apply]
lemma probOutput_ne_zero (h : x ∈ support mx) : Pr[= x | mx] ≠ 0 := by simp [h]

@[aesop unsafe apply]
lemma probOutput_ne_zero' [HasEvalFinset m] [DecidableEq α]
    (h : x ∈ finSupport mx) : Pr[= x | mx] ≠ 0 :=
  probOutput_ne_zero mx x (mem_support_of_mem_finSupport h)

@[simp]
lemma support_probOutput : Function.support (probOutput mx) = support mx := by aesop

end probOutput

section probEvent

@[aesop norm (rule_sets := [UnfoldEvalDist])]
lemma probEvent_def [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) :
    Pr[ p | mx] = (𝒟[mx]).run.toOuterMeasure (some '' {x | p x}) := rfl

@[grind =]
lemma probEvent_eq_tsum_indicator [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) :
    Pr[ p | mx] = ∑' x : α, {x | p x}.indicator (Pr[= · | mx]) x := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable,
    Set.indicator_image (Option.some_injective _), Function.comp_def, probOutput_def,
    SPMF.apply_eq_toPMF_some]

@[grind =]
lemma probEvent_eq_sum_fintype_indicator [MonadLiftT m SPMF] [Fintype α]
    (mx : m α) (p : α → Prop) : Pr[ p | mx] = ∑ x : α, {x | p x}.indicator (Pr[= · | mx]) x :=
  (probEvent_eq_tsum_indicator mx p).trans (tsum_fintype _)

@[grind =]
lemma probEvent_eq_tsum_ite [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | mx] = ∑' x : α, if p x then Pr[= x | mx] else 0 := by
  grind [Set.indicator]

@[grind =]
lemma probEvent_eq_sum_fintype_ite [MonadLiftT m SPMF] [Fintype α] (mx : m α)
    (p : α → Prop) [DecidablePred p] : Pr[ p | mx] = ∑ x : α, if p x then Pr[= x | mx] else 0 := by
  grind [Set.indicator]

lemma probEvent_eq_tsum_subtype [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) :
    Pr[ p | mx] = ∑' x : {x | p x}, Pr[= x | mx] := by
  rw [probEvent_eq_tsum_indicator, tsum_subtype]

lemma probEvent_eq_sum_filter_univ [MonadLiftT m SPMF] [Fintype α]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | mx] = ∑ x ∈ Finset.univ.filter p, Pr[= x | mx] := by
  rw [probEvent_eq_sum_fintype_ite, Finset.sum_filter]

variable [MonadLiftT m SPMF]

section zero

variable [MonadLiftT m SetM] [EvalDistCompatible m] {mx : m α} {p : α → Prop}

@[simp, grind =]
lemma probEvent_eq_zero_iff :
    Pr[ p | mx] = 0 ↔ ∀ x ∈ support mx, ¬ p x := by
  rw [probEvent_eq_tsum_indicator]; aesop
alias ⟨_, probEvent_eq_zero⟩ := probEvent_eq_zero_iff

@[simp, grind =]
lemma probEvent_eq_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[ p | mx] = 0 ↔ ∀ x ∈ finSupport mx, ¬ p x := by grind
alias ⟨_, probEvent_eq_zero'⟩ := probEvent_eq_zero_iff'

@[simp, grind =]
lemma probEvent_ne_zero_iff : Pr[ p | mx] ≠ 0 ↔ ∃ x ∈ support mx, p x := by  grind
alias ⟨_, probEvent_ne_zero⟩ := probEvent_ne_zero_iff

@[simp, grind =]
lemma probEvent_ne_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[ p | mx] ≠ 0 ↔ ∃ x ∈ finSupport mx, p x := by aesop
alias ⟨_, probEvent_ne_zero'⟩ := probEvent_ne_zero_iff'

@[simp, grind =]
lemma probEvent_pos_iff : 0 < Pr[ p | mx] ↔ ∃ x ∈ support mx, p x := by
  simp [pos_iff_ne_zero]
alias ⟨_, probEvent_pos⟩ := probEvent_pos_iff

@[simp, grind =]
lemma probEvent_pos_iff' [HasEvalFinset m] [DecidableEq α] :
    0 < Pr[ p | mx] ↔ ∃ x ∈ finSupport mx, p x := by grind
alias ⟨_, probEvent_pos'⟩ := probEvent_pos_iff'

end zero

section supportMixed

variable [MonadLiftT m SetM] [EvalDistCompatible m]

lemma probEvent_eq_tsum_subtype_mem_support (mx : m α) (p : α → Prop) :
    Pr[ p | mx] = ∑' x : {x ∈ support mx | p x}, Pr[= x | mx] := by
  simp_rw [probEvent_eq_tsum_subtype, tsum_subtype]
  refine tsum_congr (fun x ↦ ?_)
  by_cases hpx : p x
  · refine (if_pos hpx).trans ?_
    by_cases hx : x ∈ support mx
    · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_self, ↓reduceIte]
    · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_true, ↓reduceIte,
      probOutput_eq_zero_iff, not_false_eq_true]
  · exact (if_neg hpx).trans (by simp [Set.indicator, hpx])

lemma probEvent_eq_tsum_subtype_support_ite (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | mx] = ∑' x : support mx, if p x then Pr[= x | mx] else 0 :=
calc
  Pr[ p | mx] = (∑' x, if p x then Pr[= x | mx] else 0) := by rw [probEvent_eq_tsum_ite mx p]
  _ = ∑' x, (support mx).indicator (fun x ↦ if p x then Pr[= x | mx] else 0) x := by
    refine tsum_congr (fun x ↦ ?_)
    unfold Set.indicator
    split_ifs with h1 h2 h2 <;> simp [h1, h2]
  _ = ∑' x : support mx, if p x then Pr[= x | mx] else 0 := by
    rw [tsum_subtype (support mx) (fun x ↦ if p x then Pr[= x | mx] else 0)]

lemma probEvent_eq_sum_filter_finSupport [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | mx] = ∑ x ∈ (finSupport mx).filter p, Pr[= x | mx] :=
  (probEvent_eq_tsum_ite mx p).trans <|
    (tsum_eq_sum' <| by simp; tauto).trans
      (Finset.sum_congr rfl <| fun x hx ↦ if_pos (Finset.mem_filter.1 hx).2)

lemma probEvent_eq_sum_finSupport_ite [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | mx] = ∑ x ∈ finSupport mx, if p x then Pr[= x | mx] else 0 := by
  rw [probEvent_eq_sum_filter_finSupport, Finset.sum_filter]

/-- If two events are equivalent on the support of `mx` then they have the same output chance. -/
@[aesop unsafe apply, grind .]
lemma probEvent_ext {mx : m α} {p q : α → Prop}
    (h : ∀ x ∈ support mx, p x ↔ q x) : Pr[ p | mx] = Pr[ q | mx] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr fun x => ?_
  split_ifs <;> grind

end supportMixed

@[simp, grind =_, aesop unsafe norm]
lemma probEvent_eq_eq_probOutput (mx : m α) (x : α) :
    Pr[ (· = x) | mx] = Pr[= x | mx] := by
  simp [probEvent_def, PMF.toOuterMeasure_apply_singleton, probOutput_def,
    SPMF.apply_eq_toPMF_some]

@[simp, grind =_, aesop unsafe norm]
lemma probEvent_eq_eq_probOutput' (mx : m α) (x : α) :
    Pr[ (x = ·) | mx] = Pr[= x | mx] := by
  have h : (fun y => x = y) = (fun y => y = x) := funext fun _ => propext eq_comm
  rw [h]; exact probEvent_eq_eq_probOutput mx x

end probEvent

section probFailure

@[aesop norm (rule_sets := [UnfoldEvalDist]), grind =]
lemma probFailure_def [MonadLiftT m SPMF] (mx : m α) :
    Pr[⊥ | mx] = (𝒟[mx]).run none := rfl

end probFailure

/-- Probability that a computation returns a value satisfying a predicate. -/
syntax (name := probEventBinding1)
  "Pr[ " term " | " ident " ← " term "]" : term

macro_rules (kind := probEventBinding1)
  | `(Pr[ $cond:term | $var:ident ← $src:term]) => `(Pr[ fun $var => $cond | $src])

/-- Probability that a computation returns a value satisfying a predicate.
See `probOutput_true_eq_probEvent` for relation to the above definitions. -/
syntax (name := probEventBinding2) "Pr{" doSeq "}[" term "]" : term

macro_rules (kind := probEventBinding2)
  -- `doSeqBracketed`
  | `(Pr{{$items*}}[$t]) => `(probOutput (do $items:doSeqItem* return $t:term) True)
  -- `doSeqIndent`
  | `(Pr{$items*}[$t]) => `(probOutput (do $items:doSeqItem* return $t:term) True)

/-- Tests for all the different probability notations. -/
noncomputable example {m : Type → Type u} [Monad m] [MonadLiftT m SPMF] (mx : m ℕ) : Unit :=
  let _ := Pr[= 10 | mx]
  let _ := Pr[ fun x => x^2 + x < 10 | mx]
  let _ := Pr[ x^2 + x < 10 | x ← mx]
  let _ := Pr{let x ← mx}[x = 10]
  let _ := Pr[⊥ | mx]
  ()

end probability_notation

@[simp] -- TODO: versions for other constructions?
lemma evalDist_cast {m} [Monad m] [MonadLiftT m SPMF] (h : α = β) (mx : m α) :
    𝒟[cast (congrArg m h) mx] =
      cast (congrArg SPMF h) (𝒟[mx]) := by
  induction h; rfl

lemma evalDist_ext {m n} [Monad m] [MonadLiftT m SPMF] [Monad n] [MonadLiftT n SPMF]
    {mx : m α} {mx' : n α} (h : ∀ x, Pr[= x | mx] = Pr[= x | mx']) : 𝒟[mx] = 𝒟[mx'] :=
  SPMF.ext h

lemma evalDist_ext_iff {m n} [Monad m] [MonadLiftT m SPMF] [Monad n] [MonadLiftT n SPMF]
    {mx : m α} {mx' : n α} : 𝒟[mx] = 𝒟[mx'] ↔ ∀ x, Pr[= x | mx] = Pr[= x | mx'] := by
  refine ⟨fun h => ?_, evalDist_ext⟩
  simp [probOutput_def, h]

@[simp, grind =]
lemma evalDist_eq_liftM_iff [MonadLiftT m SPMF] (mx : m α) (p : PMF α) :
    𝒟[mx] = liftM p ↔ ∀ x, Pr[= x | mx] = p x := by
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · simp [probOutput_def, h]
  · simpa [SPMF.eq_liftM_iff_forall, probOutput_def] using h

@[simp, grind =]
lemma evalDist_eq_mk_iff [MonadLiftT m SPMF] (mx : m α) (p : PMF (Option α)) :
    𝒟[mx] = SPMF.mk p ↔ ∀ x, Pr[= x | mx] = p (some x) := by aesop

@[aesop unsafe apply]
lemma evalDist_eq_liftM [MonadLiftT m SPMF] {mx : m α} {p : PMF α}
    (h : ∀ x, Pr[= x | mx] = p x) : 𝒟[mx] = liftM p := by aesop

@[simp]
lemma evalDist_apply_eq_zero_iff [MonadLiftT m SPMF] [MonadLiftT m SetM]
    [EvalDistCompatible m] (mx : m α)
    (x : Option α) :
    (𝒟[mx]).run x = 0 ↔ x.rec (Pr[⊥ | mx] = 0) (· ∉ support mx) := by
  induction x with
  | none => simp [probFailure_def]
  | some y => simp [OptionT.run, mem_support_iff_evalDist_apply_ne_zero,
      SPMF.apply_eq_toPMF_some, SPMF.toPMF]

@[simp]
lemma evalDist_apply_eq_zero_iff' [MonadLiftT m SPMF] [MonadLiftT m SetM]
    [EvalDistCompatible m] [HasEvalFinset m] [DecidableEq α] (mx : m α)
    (x : Option α) : (𝒟[mx]).run x = 0 ↔ x.rec (Pr[⊥ | mx] = 0) (· ∉ finSupport mx) := by
  rw [evalDist_apply_eq_zero_iff]
  grind

/-! ## Pushing probabilities through `ite` and `Eq.rec` -/

section ite

variable (p : Prop) [Decidable p]

@[simp] lemma evalDist_ite [MonadLiftT m SPMF] (mx mx' : m α) :
    𝒟[if p then mx else mx'] = if p then 𝒟[mx] else 𝒟[mx'] := by grind

@[simp] lemma probOutput_ite [MonadLiftT m SPMF] (x : α) (mx mx' : m α) :
    Pr[= x | if p then mx else mx'] = if p then Pr[= x | mx] else Pr[= x | mx'] := by aesop

@[simp] lemma probFailure_ite [MonadLiftT m SPMF] (mx mx' : m α) :
    Pr[⊥ | if p then mx else mx'] = if p then Pr[⊥ | mx] else Pr[⊥ | mx'] := by grind

@[simp] lemma probEvent_ite [MonadLiftT m SPMF] (mx mx' : m α) (q : α → Prop) :
    Pr[ q | if p then mx else mx'] = if p then Pr[ q | mx] else Pr[ q | mx'] := by aesop

end ite

section eqRec

lemma evalDist_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) :
    𝒟[(h ▸ mx : m β)] = h ▸ 𝒟[mx] := by grind

lemma probOutput_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) (y : β) :
    Pr[= y | h ▸ mx] = Pr[= h ▸ y | mx] := by grind

@[simp] lemma probFailure_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) :
    Pr[⊥ | h ▸ mx] = Pr[⊥ | mx] := by grind

lemma probEvent_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) (q : β → Prop) :
    Pr[ q | h ▸ mx] = Pr[ fun x ↦ q (h ▸ x) | mx] := by induction h; rfl

end eqRec

section sums

/-- Connection between the two different probability notations. -/
lemma probOutput_true_eq_probEvent {α} {m : Type → Type u} [Monad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] = Pr[ p | mx] := by
  simp [probEvent_eq_tsum_indicator, probOutput_def, evalDist, map_eq_bind_pure_comp]
  congr 1; aesop

@[simp] lemma tsum_probOutput_add_probFailure [MonadLiftT m SPMF] (mx : m α) :
    (∑' x, Pr[= x | mx]) + Pr[⊥ | mx] = 1 := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp] lemma probFailure_add_tsum_probOutput [MonadLiftT m SPMF] (mx : m α) :
    Pr[⊥ | mx] + ∑' x, Pr[= x | mx] = 1 := by
  aesop (rule_sets := [UnfoldEvalDist])

end sums

/-! ## Probability bounds and total-probability sums -/

section bounds

variable {mx : m α} {mxe : OptionT m α} {x : α} {p : α → Prop}

@[simp, grind .] lemma probOutput_le_one [MonadLiftT m SPMF] :
    Pr[= x | mx] ≤ 1 := PMF.coe_le_one (𝒟[mx]) x
@[simp, grind .] lemma probOutput_ne_top [MonadLiftT m SPMF] :
    Pr[= x | mx] ≠ ∞ := PMF.apply_ne_top (𝒟[mx]) x
@[simp, grind .] lemma probOutput_lt_top [MonadLiftT m SPMF] :
    Pr[= x | mx] < ∞ := PMF.apply_lt_top (𝒟[mx]) x
@[simp, grind .] lemma not_one_lt_probOutput [MonadLiftT m SPMF] :
    ¬ 1 < Pr[= x | mx] := not_lt.2 probOutput_le_one

@[simp] lemma tsum_probOutput_le_one [MonadLiftT m SPMF] : ∑' x : α, Pr[= x | mx] ≤ 1 :=
  le_of_le_of_eq (le_add_self) (probFailure_add_tsum_probOutput mx)
@[simp] lemma tsum_probOutput_ne_top [MonadLiftT m SPMF] : ∑' x : α, Pr[= x | mx] ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one

@[simp, grind .] lemma probEvent_le_one [MonadLiftT m SPMF] : Pr[ p | mx] ≤ 1 := by
  rw [probEvent_def, PMF.toOuterMeasure_apply]
  refine le_of_le_of_eq (ENNReal.tsum_le_tsum ?_) ((𝒟[mx]).tsum_coe)
  exact Set.indicator_le_self (some '' {x | p x}) _

@[simp, grind .] lemma probEvent_ne_top [MonadLiftT m SPMF] :
    Pr[ p | mx] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
@[simp, grind .] lemma probEvent_lt_top [MonadLiftT m SPMF] :
    Pr[ p | mx] < ∞ := lt_top_iff_ne_top.2 probEvent_ne_top
@[simp, grind .] lemma not_one_lt_probEvent [MonadLiftT m SPMF] :
    ¬ 1 < Pr[ p | mx] := not_lt.2 probEvent_le_one

@[simp, grind .] lemma probFailure_le_one [MonadLiftT m SPMF] :
    Pr[⊥ | mx] ≤ 1 := PMF.coe_le_one (𝒟[mx]) none
@[simp, grind .] lemma probFailure_ne_top [MonadLiftT m SPMF] :
    Pr[⊥ | mx] ≠ ∞ := PMF.apply_ne_top (𝒟[mx]) none
@[simp, grind .] lemma probFailure_lt_top [MonadLiftT m SPMF] :
    Pr[⊥ | mx] < ∞ := PMF.apply_lt_top (𝒟[mx]) none
@[simp, grind .] lemma not_one_lt_probFailure [MonadLiftT m SPMF] :
    ¬ 1 < Pr[⊥ | mx] := not_lt.2 probFailure_le_one

@[simp, grind =]
lemma one_le_probOutput_iff [MonadLiftT m SPMF] : 1 ≤ Pr[= x | mx] ↔ Pr[= x | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probOutput, or_false, eq_comm]

@[simp, grind =]
lemma one_le_probEvent_iff [MonadLiftT m SPMF] : 1 ≤ Pr[ p | mx] ↔ Pr[ p | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probEvent, or_false, eq_comm]

@[simp, grind =]
lemma one_le_probFailure_iff [MonadLiftT m SPMF] : 1 ≤ Pr[⊥ | mx] ↔ Pr[⊥ | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probFailure, or_false, eq_comm]

@[simp, grind =]
lemma probOutput_eq_one_iff [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m] :
    Pr[= x | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ support mx = {x} := by
  rw [← probEvent_eq_eq_probOutput]
  simp [probOutput_def, probFailure_def, SPMF.apply_eq_toPMF_some, PMF.apply_eq_one_iff,
    Set.ext_iff, Option.forall, mem_support_iff_evalDist_apply_ne_zero]
alias ⟨_, probOutput_eq_one⟩ := probOutput_eq_one_iff

@[simp, grind =]
lemma one_eq_probOutput_iff [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m] :
    1 = Pr[= x | mx] ↔ Pr[⊥ | mx] = 0 ∧ support mx = {x} := by
  rw [eq_comm, probOutput_eq_one_iff]
alias ⟨_, one_eq_probOutput⟩ := one_eq_probOutput_iff

@[simp, grind =]
lemma probOutput_eq_one_iff' [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] :
    Pr[= x | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ finSupport mx = {x} := by
  rw [probOutput_eq_one_iff, finSupport_eq_iff_support_eq_coe, Finset.coe_singleton]
alias ⟨_, probOutput_eq_one'⟩ := probOutput_eq_one_iff'

@[simp, grind =]
lemma one_eq_probOutput_iff' [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] :
    1 = Pr[= x | mx] ↔ Pr[⊥ | mx] = 0 ∧ finSupport mx = {x} := by
  rw [eq_comm, probOutput_eq_one_iff']
alias ⟨_, one_eq_probOutput'⟩ := one_eq_probOutput_iff'

/-- If a non-failing computation can only return `x`, then it returns `x` with probability one. -/
lemma probOutput_eq_one_of_support_subset_singleton [MonadLiftT m SPMF] [MonadLiftT m SetM]
    [EvalDistCompatible m]
    (hnf : Pr[⊥ | mx] = 0) (huniq : ∀ y ∈ support mx, y = x) :
    Pr[= x | mx] = 1 := by
  have hnot : ∀ y ≠ x, Pr[= y | mx] = 0 :=
    fun y hy => (probOutput_eq_zero_iff _ _).mpr (fun hmem => hy (huniq y hmem))
  have hsum : ∑' y, Pr[= y | mx] = Pr[= x | mx] :=
    tsum_eq_single x hnot
  have htot := probFailure_add_tsum_probOutput mx
  rw [hnf, hsum, zero_add] at htot
  exact htot

end bounds

section mono_le

variable [MonadLiftT m SPMF] (mx : m α) (r : ℝ≥0∞)

@[simp]
lemma probFailure_mul_le : Pr[⊥ | mx] * r ≤ r :=
  mul_le_of_le_one_left' <| by simp

@[simp]
lemma mul_probFailure_le : r * Pr[⊥ | mx] ≤ r :=
  mul_le_of_le_one_right' <| by simp

@[simp] lemma probOutput_mul_le (x : α) : Pr[= x | mx] * r ≤ r :=
  mul_le_of_le_one_left' <| by simp

@[simp] lemma mul_probOutput_le (x : α) : r * Pr[= x | mx] ≤ r :=
  mul_le_of_le_one_right' <| by simp

@[simp] lemma probEvent_mul_le (p : α → Prop) : Pr[ p | mx] * r ≤ r :=
  mul_le_of_le_one_left' <| by simp

@[simp] lemma mul_probEvent_le (p : α → Prop) : r * Pr[ p | mx] ≤ r :=
  mul_le_of_le_one_right' <| by simp

end mono_le

section sum_probOutput

variable [MonadLiftT m SPMF]

@[simp]
lemma tsum_probOutput_eq_sub (mx : m α) :
    ∑' x : α, Pr[= x | mx] = 1 - Pr[⊥ | mx] := by
  refine ENNReal.eq_sub_of_add_eq probFailure_ne_top (tsum_probOutput_add_probFailure mx)

lemma tsum_probOutput_eq_one' {mx : m α} (h : Pr[⊥ | mx] = 0) :
    ∑' x : α, Pr[= x | mx] = 1 := by simp [h]

@[simp]
lemma tsum_support_probOutput_eq_sub [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) :
    ∑' x : support mx, Pr[= x | mx] = 1 - Pr[⊥ | mx] := by
  rw [tsum_subtype_eq_of_support_subset] <;> simp

lemma tsum_support_probOutput_eq_one' [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} (h : Pr[⊥ | mx] = 0) :
    ∑' x : support mx, Pr[= x | mx] = 1 := by simp [h]

@[simp]
lemma sum_probOutput_eq_sub [Fintype α] (mx : m α) :
    ∑ x : α, Pr[= x | mx] = 1 - Pr[⊥ | mx] := by
  rw [← tsum_fintype (L := .unconditional _), tsum_probOutput_eq_sub]

lemma sum_probOutput_eq_one [Fintype α] {mx : m α} (h : Pr[⊥ | mx] = 0) :
    ∑ x : α, Pr[= x | mx] = 1 := by simp [h]

@[simp]
lemma sum_finSupport_probOutput_eq_sub [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] (mx : m α) :
    ∑ x ∈ finSupport mx, Pr[= x | mx] = 1 - Pr[⊥ | mx] := by
  rw [← tsum_probOutput_eq_sub, tsum_eq_sum]
  simp

lemma sum_finSupport_probOutput_eq_one [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α]
    {mx : m α} (h : Pr[⊥ | mx] = 0) : ∑ x ∈ finSupport mx, Pr[= x | mx] = 1 := by simp [h]

end sum_probOutput

@[grind =]
lemma probFailure_eq_sub_tsum [MonadLiftT m SPMF] (mx : m α) :
    Pr[⊥ | mx] = 1 - ∑' x : α, Pr[= x | mx] := by
  refine ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
    (probFailure_add_tsum_probOutput mx)

lemma probFailure_eq_sub_sum [MonadLiftT m SPMF] [Fintype α] (mx : m α) :
    Pr[⊥ | mx] = 1 - ∑ x : α, Pr[= x | mx] := by
  rw [← tsum_fintype (L := .unconditional _), probFailure_eq_sub_tsum]

section bool

variable [MonadLiftT m SPMF]

@[simp]
lemma probEvent_False (mx : m α) :
    Pr[ fun _ => False | mx] = 0 := by
  simp [probEvent_eq_tsum_indicator]

@[simp]
lemma probEvent_false (mx : m α) :
    Pr[ fun _ => false | mx] = 0 := by aesop

@[simp, grind =]
lemma probEvent_True_eq_sub (mx : m α) :
    Pr[ fun _ => True | mx] = 1 - Pr[⊥ | mx] := by
  simp [probEvent_eq_tsum_indicator]

lemma probEvent_true_eq_sub (mx : m α) :
    Pr[ fun _ => true | mx] = 1 - Pr[⊥ | mx] := by grind

lemma probFailure_eq_sub_probEvent (mx : m α) :
    Pr[⊥ | mx] = 1 - Pr[ fun _ => True | mx] := by
  refine ENNReal.eq_sub_of_add_eq (by simp only [ne_eq, probEvent_ne_top, not_false_eq_true]) ?_
  simp only [probEvent_True_eq_sub, probFailure_le_one, add_tsub_cancel_of_le]

lemma probFailure_eq_one_iff_probEvent_true (mx : m α) :
    Pr[⊥ | mx] = 1 ↔ Pr[ fun _ => True | mx] = 0 := by
  rw [probFailure_eq_sub_probEvent, ← ENNReal.toReal_eq_one_iff]
  rw [ENNReal.toReal_sub_of_le (by grind) (by simp)]
  simp [tsub_eq_zero_iff_le, ENNReal.toReal_eq_one_iff]

@[simp, grind =]
lemma probFailure_eq_one_iff [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) :
    Pr[⊥ | mx] = 1 ↔ support mx = ∅ := by
  simp [probFailure_eq_one_iff_probEvent_true, probEvent_eq_tsum_subtype_mem_support, Set.ext_iff]

@[aesop unsafe forward]
lemma probFailure_eq_one [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} (h : support mx = ∅) : Pr[⊥ | mx] = 1 := by grind

@[simp, aesop norm]
lemma probEvent_const (mx : m α) (p : Prop) [Decidable p] :
    Pr[ fun _ => p | mx] = if p then (1 - Pr[⊥ | mx]) else 0 := by
  aesop

end bool

/-! ### Lemmas for monads with a total `PMF` denotation

These lemmas hold when `m` lifts into `PMF` (so computations never fail). They expose the
absence of failure mass and total normalization of the resulting distribution. -/

section pmf_denotation

variable {α β γ : Type u} {m : Type u → Type v}
  [MonadLiftT m PMF]

/-- A computation interpreted via a `PMF` lift has zero failure probability. -/
@[simp, grind =]
lemma probFailure_of_liftM_PMF (mx : m α) : Pr[⊥ | mx] = 0 := by
  rw [probFailure_def, show 𝒟[mx] = (liftM (liftM mx : PMF α) : SPMF α) from rfl,
    SPMF.run_eq_toPMF]
  change (some <$> (liftM mx : PMF α)) none = 0
  simp [PMF.monad_map_eq_map, PMF.map_apply]

lemma tsum_probOutput_of_liftM_PMF (mx : m α) :
    ∑' x, Pr[= x | mx] = 1 := by simp

lemma tsum_support_probOutput_of_liftM_PMF [MonadLiftT m SetM] [EvalDistCompatible m]
    (mx : m α) :
    ∑' x : support mx, Pr[= x | mx] = 1 := by simp

lemma sum_probOutput_of_liftM_PMF [Fintype α] (mx : m α) :
    ∑ x : α, Pr[= x | mx] = 1 := by simp

lemma sum_finSupport_probOutput_of_liftM_PMF [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] (mx : m α) :
    ∑ x ∈ finSupport mx, Pr[= x | mx] = 1 := by simp

lemma finSupport_nonempty_of_liftM_PMF [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α] (mx : m α) :
    (finSupport mx).Nonempty := by
  by_contra h
  have hsum := sum_finSupport_probOutput_of_liftM_PMF (m := m) mx
  rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
  exact zero_ne_one hsum

lemma probOutput_eq_inv_finSupport_card_of_liftM_PMF [MonadLiftT m SetM] [EvalDistCompatible m]
    [HasEvalFinset m] [DecidableEq α]
    {mx : m α} {c : ENNReal}
    (hconst : ∀ x ∈ support mx, Pr[= x | mx] = c) :
    c = 1 / (finSupport mx).card := by
  have hconst' : ∀ x ∈ finSupport mx, Pr[= x | mx] = c :=
    fun x hx => hconst x (mem_support_of_mem_finSupport hx)
  have hcard_mul : ((finSupport mx).card : ENNReal) * c = 1 := by
    have h := sum_finSupport_probOutput_of_liftM_PMF (m := m) mx
    rwa [show ∑ x ∈ finSupport mx, Pr[= x | mx] = ∑ x ∈ finSupport mx, c from
      Finset.sum_congr rfl fun x hx => hconst' x hx, Finset.sum_const, nsmul_eq_mul] at h
  have : c * ((finSupport mx).card : ENNReal) = 1 := by rwa [mul_comm] at hcard_mul
  calc c = ((finSupport mx).card : ENNReal)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left this
    _ = 1 / (finSupport mx).card := by rw [one_div]

end pmf_denotation

/-! ## Monotonicity and complementation for `probEvent` -/

section probEvent_mono_compl

variable [MonadLiftT m SPMF]
  {mx : m α} {p q : α → Prop}

lemma probEvent_compl (mx : m α) (p : α → Prop) :
    Pr[ p | mx] + Pr[ fun x => ¬p x | mx] = 1 - Pr[⊥ | mx] := by
  have := Classical.decPred p
  rw [probEvent_eq_tsum_ite mx p, probEvent_eq_tsum_ite mx (fun x => ¬p x)]
  rw [← ENNReal.tsum_add, ← tsum_probOutput_eq_sub]
  refine tsum_congr fun x => ?_
  split_ifs <;> simp_all

/-- Union bound: the probability of `p ∨ q` is at most the sum of probabilities. -/
lemma probEvent_or_le (mx : m α) (p q : α → Prop) :
    Pr[ fun x => p x ∨ q x | mx] ≤ Pr[ p | mx] + Pr[ q | mx] := by
  have := Classical.decPred p; have := Classical.decPred q
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

variable [MonadLiftT m SetM] [EvalDistCompatible m]

/-- If `p` implies `q` on the `support` of a computation then it is more likely to happen. -/
lemma probEvent_mono (h : ∀ x ∈ support mx, p x → q x) : Pr[ p | mx] ≤ Pr[ q | mx] := by
  have := Classical.decPred p; have := Classical.decPred q
  simp only [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun x => ?_
  split_ifs with hp hq
  · exact le_rfl
  · exact le_of_eq (probOutput_eq_zero_of_not_mem_support (fun hx => hq (h x hx hp)))
  · exact zero_le
  · exact le_rfl

/-- If `p` implies `q` on the `finSupport` of a computation then it is more likely to happen. -/
lemma probEvent_mono' [HasEvalFinset m] [DecidableEq α]
    (h : ∀ x ∈ finSupport mx, p x → q x) : Pr[ p | mx] ≤ Pr[ q | mx] :=
  probEvent_mono (fun x hx hpx => h x (mem_finSupport_of_mem_support hx) hpx)

/-- If `p` implies `q` everywhere then `p` is less likely than `q`. Convenience
specialisation of `probEvent_mono` that drops the support hypothesis. -/
lemma probEvent_mono'' (h : ∀ x, p x → q x) : Pr[ p | mx] ≤ Pr[ q | mx] :=
  probEvent_mono (fun x _ => h x)

@[simp low, grind =]
lemma probEvent_eq_one_iff :
    Pr[ p | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, p x := by
  constructor
  · intro h
    have hcompl := probEvent_compl mx p
    rw [h] at hcompl
    have hfail : Pr[⊥ | mx] = 0 := by
      by_contra hne
      have h1 : 1 - Pr[⊥ | mx] < 1 :=
        ENNReal.sub_lt_self one_ne_top one_ne_zero hne
      exact not_lt.mpr (hcompl ▸ le_add_right le_rfl) h1
    refine ⟨hfail, fun x hx => ?_⟩
    rw [hfail, tsub_zero] at hcompl
    have h3 : Pr[ fun x => ¬p x | mx] = 0 := by
      have hcancel : AddLECancellable (1 : ℝ≥0∞) :=
        WithTop.addLECancellable_iff_ne_top.mpr one_ne_top
      exact le_antisymm (hcancel (by rw [add_zero]; exact hcompl.le)) (zero_le)
    rw [probEvent_eq_zero_iff] at h3
    exact by_contra (h3 x hx)
  · intro ⟨hf, hp⟩
    have := Classical.decPred p
    rw [probEvent_eq_tsum_ite]
    conv_rhs => rw [show (1 : ℝ≥0∞) = 1 - Pr[⊥ | mx] from by simp [hf]]
    rw [← tsum_probOutput_eq_sub]
    refine tsum_congr fun x => ?_
    split_ifs with hpx
    · rfl
    · exact (probOutput_eq_zero_of_not_mem_support (fun hx' => hpx (hp x hx'))).symm

alias ⟨_, probEvent_eq_one⟩ := probEvent_eq_one_iff

/-- Pointwise variant of `probOutput_eq_one_iff`: `Pr[= x | mx] = 1` iff the support is
a subset of `{x}` (phrased as a forall over the support) and the computation never fails.

More usable than `probOutput_eq_one_iff` when the caller wants to iterate over arbitrary
support elements rather than prove a set equality. -/
lemma probOutput_eq_one_iff_forall (mx : m α) (x : α) :
    Pr[= x | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ ∀ y ∈ support mx, y = x := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]

@[simp low, grind =]
lemma one_eq_probEvent_iff :
    1 = Pr[ p | mx] ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, p x := by
  rw [eq_comm, probEvent_eq_one_iff]

alias ⟨_, one_eq_probEvent⟩ := one_eq_probEvent_iff

@[simp, grind =]
lemma probEvent_eq_one_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[ p | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ finSupport mx, p x := by
  simp_rw [probEvent_eq_one_iff, mem_finSupport_iff_mem_support]

alias ⟨_, probEvent_eq_one'⟩ := probEvent_eq_one_iff'

@[simp, grind =]
lemma one_eq_probEvent_iff' [HasEvalFinset m] [DecidableEq α] :
    1 = Pr[ p | mx] ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ finSupport mx, p x := by
  rw [eq_comm, probEvent_eq_one_iff']

alias ⟨_, one_eq_probEvent'⟩ := one_eq_probEvent_iff'

@[simp]
lemma function_support_probOutput :
    Function.support (Pr[= · | mx]) = support mx := by
  simp only [Function.support, ne_eq, probOutput_eq_zero_iff, not_not, Set.setOf_mem_eq]

lemma mem_support_iff_of_evalDist_eq {m n} [Monad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    [Monad n] [MonadLiftT n SPMF] [MonadLiftT n SetM] [EvalDistCompatible n]
    {mx : m α} {mx' : n α} (h : 𝒟[mx] = 𝒟[mx']) (x : α) :
    x ∈ support mx ↔ x ∈ support mx' := by
  simp only [mem_support_iff, probOutput_def, h]

lemma mem_finSupport_iff_of_evalDist_eq {m n} [Monad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    [Monad n] [MonadLiftT n SPMF] [MonadLiftT n SetM] [EvalDistCompatible n]
    [HasEvalFinset m] [HasEvalFinset n] [DecidableEq α]
    {mx : m α} {mx' : n α} (h : 𝒟[mx] = 𝒟[mx']) (x : α) :
    x ∈ finSupport mx ↔ x ∈ finSupport mx' := by
  simp only [mem_finSupport_iff_mem_support, mem_support_iff_of_evalDist_eq h]

open Classical in
omit [MonadLiftT m SetM] [EvalDistCompatible m] in
lemma indicator_objective_eq_probEvent (mx : m (α × β)) (R : α → β → Prop) :
    (∑' z, Pr[= z | mx] * (if R z.1 z.2 then 1 else 0)) = Pr[ fun z => R z.1 z.2 | mx] := by
  rw [probEvent_eq_tsum_ite]
  refine tsum_congr fun z => ?_
  by_cases hR : R z.1 z.2 <;> simp [hR]

end probEvent_mono_compl
