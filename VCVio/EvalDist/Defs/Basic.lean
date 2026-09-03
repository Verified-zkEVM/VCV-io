/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Measure

/-!
# Typeclasses for Denotational Monad Semantics

The primary distribution `evalDist` is a Mathlib `Measure`. The explicit `evalSPMF` / `𝒮[…]`
surface remains available for finite executable distributions, and `probOutput`, `probEvent`, and
`probFailure` are discrete scalar adapters with theorems stating their meaning in `evalDist`.

-- dtumad: document various probability notation definitions here
-/

@[expose] public section

open MeasureTheory ENNReal

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
between that syntactic support and `SPMF.support ∘ evalSPMF`.

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

/-- Coherence between `support` (via `MonadLiftT m SetM`) and `evalSPMF`
(via `MonadLiftT m SPMF`): `x ∈ support mx` iff `Pr[= x | mx] ≠ 0`.

This typeclass is exported by every monad that admits both lifts and they
agree on outputs — i.e. `support mx = SPMF.support (evalSPMF mx)`. -/
class EvalDistCompatible (m : Type u → Type v) [MonadLiftT m SetM]
    [MonadLiftT m SPMF] : Prop where
  /-- The reachable outputs of `mx` (via `support`) are exactly the outputs with
  nonzero probability in `evalSPMF mx`. -/
  support_eq_SPMF_support {α : Type u} (mx : m α) :
    SetM.run (liftM mx : SetM α) = SPMF.support (liftM mx : SPMF α)

export EvalDistCompatible (support_eq_SPMF_support)

/-- `SPMF` is trivially compatible: both lifts coincide on the nose. -/
instance : EvalDistCompatible SPMF where
  support_eq_SPMF_support _ := rfl

/-- The resulting distribution of running the monadic computation `mx`. -/
@[reducible, inline]
def evalSPMF [MonadLiftT m SPMF] {α : Type u} (mx : m α) : SPMF α := liftM mx

/-- Evaluation distribution notation for any monad lifting into `SPMF`. -/
notation "𝒮[" mx "]" => evalSPMF mx

lemma evalSPMF_def [MonadLiftT m SPMF] {α : Type u} (mx : m α) :
    𝒮[mx] = liftM mx := rfl

@[simp]
lemma evalSPMF_id (p : SPMF α) : 𝒮[p] = p :=
  monadLift_self p

/-- The sole deprecated whole-denotation bridge from the finite evaluator to the primary measure
semantics.

The theorem deliberately has only the legacy `MonadLiftT m SPMF` assumption. Consequently the
measure on the left is the canonical adapter instance defined in `Defs.Measure`; a measure-native
semantics should be reasoned about directly instead of being converted back to an `SPMF`. -/
@[deprecated evalDist (since := "2026-08-25")]
theorem evalDist_eq_evalSPMF_toMeasure [MonadLiftT m SPMF]
    [MeasurableSpace α] (mx : m α) :
    𝒟[mx] = (𝒮[mx]).toMeasure := rfl

section probability_notation

/-- Probability that a computation `mx` returns the value `x`.

This remains definitionally the point mass of the executable `SPMF` semantics. The
`probOutput_eq_evalSPMF_toMeasure` theorem exposes the equivalent measure-level reading. -/
def probOutput [MonadLiftT m SPMF] (mx : m α) (x : α) : ℝ≥0∞ :=
  evalSPMF mx x

/-- Probability that a computation `mx` outputs a value satisfying `p`.

The traditional notation remains the executable `SPMF` event API and is therefore usable for
arbitrary predicates. General measure developments should apply `𝒟[mx]` to a measurable event;
`probEvent_eq_evalSPMF_toMeasure` bridges the two on discrete spaces. -/
noncomputable def probEvent [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  (evalSPMF mx).run.toOuterMeasure (some '' {x | p x})

/-- Probability that a computation `mx` will fail to return a value. -/
def probFailure [MonadLiftT m SPMF] (mx : m α) : ℝ≥0∞ :=
  (evalSPMF mx).run none

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
lemma probOutput_def (mx : m α) (x : α) : Pr[= x | mx] = evalSPMF mx x := rfl

/-- A point probability is the singleton mass of the explicit compatibility measure. -/
lemma probOutput_eq_evalSPMF_toMeasure [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (x : α) : Pr[= x | mx] = (evalSPMF mx).toMeasure {x} := by
  rw [probOutput_def]
  exact (SPMF.toMeasure_apply_singleton (evalSPMF mx) x).symm

variable [MonadLiftT m SetM] [EvalDistCompatible m]

@[grind =]
lemma mem_support_iff (mx : m α) (x : α) :
    x ∈ support mx ↔ Pr[= x | mx] ≠ 0 := by
  rw [support_def, support_eq_SPMF_support, SPMF.mem_support_iff,
    probOutput_def, evalSPMF_def]

/-- The legacy support interpretation agrees with positive singleton mass in the canonical
`SPMF.toMeasure` adapter. This is the explicit dictionary-specific coherence theorem; it does not
claim that an unrelated measure-native semantics instance has the same support. -/
lemma mem_support_iff_evalSPMF_toMeasure_singleton_ne_zero
    [MeasurableSpace α] [DiscreteMeasurableSpace α] (mx : m α) (x : α) :
    x ∈ support mx ↔ (evalSPMF mx).toMeasure {x} ≠ 0 := by
  rw [SPMF.toMeasure_apply_singleton]
  exact mem_support_iff mx x

lemma mem_support_iff_evalSPMF_apply_ne_zero (mx : m α) (x : α) :
    x ∈ support mx ↔ 𝒮[mx] x ≠ 0 := by grind

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
    Pr[ p | mx] = (𝒮[mx]).run.toOuterMeasure (some '' {x | p x}) := rfl

/-- A discrete event probability is the mass of that event in the compatibility measure. -/
lemma probEvent_eq_evalSPMF_toMeasure [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p : α → Prop) [MonadLiftT m SPMF] :
    Pr[p | mx] = (evalSPMF mx).toMeasure {x | p x} := by
  rw [probEvent_def]
  exact (SPMF.toMeasure_apply (evalSPMF mx) {x | p x}).symm

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

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp]
lemma probEvent_eq_zero_iff :
    Pr[ p | mx] = 0 ↔ ∀ x ∈ support mx, ¬ p x := by
  rw [probEvent_eq_tsum_indicator]; aesop
alias ⟨_, probEvent_eq_zero⟩ := probEvent_eq_zero_iff

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp]
lemma probEvent_eq_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[ p | mx] = 0 ↔ ∀ x ∈ finSupport mx, ¬ p x := by grind [probEvent_eq_zero_iff]
alias ⟨_, probEvent_eq_zero'⟩ := probEvent_eq_zero_iff'

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp]
lemma probEvent_ne_zero_iff : Pr[ p | mx] ≠ 0 ↔ ∃ x ∈ support mx, p x := by
  grind [probEvent_eq_zero_iff]
alias ⟨_, probEvent_ne_zero⟩ := probEvent_ne_zero_iff

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp]
lemma probEvent_ne_zero_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[ p | mx] ≠ 0 ↔ ∃ x ∈ finSupport mx, p x := by aesop
alias ⟨_, probEvent_ne_zero'⟩ := probEvent_ne_zero_iff'

-- `grind`-safe in isolation: this support-quantifier characterization saturates `grind` only in
-- combination with the `probEvent_eq_one_iff` family (kept `simp`-only). See `probability.md`.
@[simp, grind =]
lemma probEvent_pos_iff : 0 < Pr[ p | mx] ↔ ∃ x ∈ support mx, p x := by
  simp [pos_iff_ne_zero]
alias ⟨_, probEvent_pos⟩ := probEvent_pos_iff

-- `grind`-safe in isolation; see `probEvent_pos_iff`.
@[simp, grind =]
lemma probEvent_pos_iff' [HasEvalFinset m] [DecidableEq α] :
    0 < Pr[ p | mx] ↔ ∃ x ∈ finSupport mx, p x := by grind [probEvent_pos_iff]
alias ⟨_, probEvent_pos'⟩ := probEvent_pos_iff'

/-- `Set.Nonempty` companion to the `simp`-only `probEvent_ne_zero_iff`: the event has positive
probability iff some reachable output satisfies `p`. The `Set.Nonempty` witness stays atomic under
`grind` (unlike the saturating `∃ x ∈ support mx, p x` form). Mirrors
`probFailure_eq_one_iff_not_nonempty`.

Deliberately NOT in the default `grind` set: together with `probEvent_eq_zero_iff_not_nonempty`
and `probFailure_eq_one_iff_not_nonempty` it re-forms a saturation cycle in the generic-monad
context (`grind` times out on the `probEvent_eq_one_iff` statement shape with all three tagged;
dropping any one of the trio restores fail-fast, and dropping this one is free: `grind` recovers
`≠ 0 ↔ Nonempty` from the kept `= 0 ↔ ¬ Nonempty` sibling by classical negation). Gated by
`VCVioTest/GrindFailFast.lean`. -/
lemma probEvent_ne_zero_iff_nonempty :
    Pr[ p | mx] ≠ 0 ↔ {x ∈ support mx | p x}.Nonempty := by
  rw [probEvent_ne_zero_iff]; simp [Set.nonempty_def]

/-- `grind`-friendly companion to the `simp`-only `probEvent_eq_zero_iff`: the event has probability
zero iff no reachable output satisfies `p`, phrased via `Set.Nonempty` rather than the saturating
`∀ x ∈ support mx, ¬ p x`. The negation of `probEvent_ne_zero_iff_nonempty`. -/
@[grind =]
lemma probEvent_eq_zero_iff_not_nonempty :
    Pr[ p | mx] = 0 ↔ ¬ {x ∈ support mx | p x}.Nonempty := by
  rw [probEvent_eq_zero_iff]
  simp [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem]

end zero

section supportMixed

variable [MonadLiftT m SetM] [EvalDistCompatible m]

lemma probEvent_eq_tsum_subtype_mem_support (mx : m α) (p : α → Prop) :
    Pr[ p | mx] = ∑' x : {x ∈ support mx | p x}, Pr[= x | mx] := by
  rw [probEvent_eq_tsum_subtype, tsum_subtype, tsum_subtype, ← support_probOutput,
    ← Set.indicator_inter_support]
  simp [Set.inter_def, and_comm]

lemma probEvent_eq_tsum_subtype_support_ite (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | mx] = ∑' x : support mx, if p x then Pr[= x | mx] else 0 := by
  rw [probEvent_eq_tsum_ite, ← tsum_subtype_eq_of_support_subset (s := support mx)]
  grind [Function.support_subset_iff]

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
    Pr[⊥ | mx] = (𝒮[mx]).run none := rfl

@[simp]
lemma probOutput_evalSPMF [MonadLiftT m SPMF] (mx : m α) (x : α) :
    Pr[= x | 𝒮[mx]] = Pr[= x | mx] := by
  rw [probOutput_def, probOutput_def, evalSPMF_id]

@[simp]
lemma probEvent_evalSPMF [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) :
    Pr[p | 𝒮[mx]] = Pr[p | mx] := by
  rw [probEvent_def, probEvent_def, evalSPMF_id]

@[simp]
lemma probFailure_evalSPMF [MonadLiftT m SPMF] (mx : m α) :
    Pr[⊥ | 𝒮[mx]] = Pr[⊥ | mx] := by
  rw [probFailure_def, probFailure_def, evalSPMF_id]

/-- Failure probability is the mass missing from the compatibility measure. -/
lemma probFailure_eq_evalSPMF_toMeasure [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MonadLiftT m SPMF] (mx : m α) :
    Pr[⊥ | mx] = 1 - (evalSPMF mx).toMeasure Set.univ := by
  rw [probFailure_def, SPMF.toMeasure_apply_univ]
  exact SPMF.toPMF_none_eq_one_sub_tsum (evalSPMF mx)

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
lemma evalSPMF_cast {m} [Monad m] [MonadLiftT m SPMF] (h : α = β) (mx : m α) :
    𝒮[cast (congrArg m h) mx] =
      cast (congrArg SPMF h) (𝒮[mx]) := by
  induction h; rfl

lemma evalSPMF_ext {m n} [Monad m] [MonadLiftT m SPMF] [Monad n] [MonadLiftT n SPMF]
    {mx : m α} {mx' : n α} (h : ∀ x, Pr[= x | mx] = Pr[= x | mx']) : 𝒮[mx] = 𝒮[mx'] := by
  apply SPMF.ext
  intro x
  simpa only [probOutput_def] using h x

lemma evalSPMF_ext_iff {m n} [Monad m] [MonadLiftT m SPMF] [Monad n] [MonadLiftT n SPMF]
    {mx : m α} {mx' : n α} : 𝒮[mx] = 𝒮[mx'] ↔ ∀ x, Pr[= x | mx] = Pr[= x | mx'] := by
  refine ⟨fun h => ?_, evalSPMF_ext⟩
  simp [probOutput_def, h]

@[simp, grind =]
lemma evalSPMF_eq_liftM_iff [MonadLiftT m SPMF] (mx : m α) (p : PMF α) :
    𝒮[mx] = liftM p ↔ ∀ x, Pr[= x | mx] = p x := by
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · simp [probOutput_def, h]
  · simpa [SPMF.eq_liftM_iff_forall, probOutput_def] using h

@[simp, grind =]
lemma evalSPMF_eq_mk_iff [MonadLiftT m SPMF] (mx : m α) (p : PMF (Option α)) :
    𝒮[mx] = SPMF.mk p ↔ ∀ x, Pr[= x | mx] = p (some x) := by
  constructor
  · intro h x
    rw [probOutput_def, h]
    rfl
  · intro h
    apply SPMF.ext
    intro x
    change (evalSPMF mx) x = p (some x)
    simpa only [probOutput_def] using h x

@[aesop unsafe apply]
lemma evalSPMF_eq_liftM [MonadLiftT m SPMF] {mx : m α} {p : PMF α}
    (h : ∀ x, Pr[= x | mx] = p x) : 𝒮[mx] = liftM p := by aesop

@[simp]
lemma evalSPMF_apply_eq_zero_iff [MonadLiftT m SPMF] [MonadLiftT m SetM]
    [EvalDistCompatible m] (mx : m α) (x : Option α) :
    (𝒮[mx]).run x = 0 ↔ x.rec (Pr[⊥ | mx] = 0) (· ∉ support mx) := by
  induction x with
  | none => simp [probFailure_def]
  | some y => simp [OptionT.run, mem_support_iff_evalSPMF_apply_ne_zero,
      SPMF.apply_eq_toPMF_some, SPMF.toPMF]

@[simp]
lemma evalSPMF_apply_eq_zero_iff' [MonadLiftT m SPMF] [MonadLiftT m SetM]
    [EvalDistCompatible m] [HasEvalFinset m] [DecidableEq α] (mx : m α)
    (x : Option α) : (𝒮[mx]).run x = 0 ↔ x.rec (Pr[⊥ | mx] = 0) (· ∉ finSupport mx) := by
  rw [evalSPMF_apply_eq_zero_iff]
  grind

/-! ## Pushing probabilities through `ite`, `dite`, and `Eq.rec` -/

section ite

variable (p : Prop) [Decidable p]

@[simp] lemma evalSPMF_ite [MonadLiftT m SPMF] (mx mx' : m α) :
    𝒮[if p then mx else mx'] = if p then 𝒮[mx] else 𝒮[mx'] := by grind

@[simp] lemma probOutput_ite [MonadLiftT m SPMF] (x : α) (mx mx' : m α) :
    Pr[= x | if p then mx else mx'] = if p then Pr[= x | mx] else Pr[= x | mx'] := by aesop

@[simp] lemma probFailure_ite [MonadLiftT m SPMF] (mx mx' : m α) :
    Pr[⊥ | if p then mx else mx'] = if p then Pr[⊥ | mx] else Pr[⊥ | mx'] := by grind

@[simp] lemma probEvent_ite [MonadLiftT m SPMF] (mx mx' : m α) (q : α → Prop) :
    Pr[ q | if p then mx else mx'] = if p then Pr[ q | mx] else Pr[ q | mx'] := by aesop

@[simp] lemma evalSPMF_dite [MonadLiftT m SPMF] (mx : p → m α) (mx' : ¬p → m α) :
    𝒮[if h : p then mx h else mx' h] = if h : p then 𝒮[mx h] else 𝒮[mx' h] := by
  split <;> rfl

@[simp] lemma probOutput_dite [MonadLiftT m SPMF] (x : α) (mx : p → m α) (mx' : ¬p → m α) :
    Pr[= x | if h : p then mx h else mx' h] =
      if h : p then Pr[= x | mx h] else Pr[= x | mx' h] := by
  split <;> rfl

@[simp] lemma probFailure_dite [MonadLiftT m SPMF] (mx : p → m α) (mx' : ¬p → m α) :
    Pr[⊥ | if h : p then mx h else mx' h] =
      if h : p then Pr[⊥ | mx h] else Pr[⊥ | mx' h] := by
  split <;> rfl

@[simp] lemma probEvent_dite [MonadLiftT m SPMF] (mx : p → m α) (mx' : ¬p → m α) (q : α → Prop) :
    Pr[ q | if h : p then mx h else mx' h] =
      if h : p then Pr[ q | mx h] else Pr[ q | mx' h] := by
  split <;> rfl

end ite

section eqRec

lemma evalSPMF_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) :
    𝒮[(h ▸ mx : m β)] = h ▸ 𝒮[mx] := by grind

lemma probOutput_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) (y : β) :
    Pr[= y | h ▸ mx] = Pr[= h ▸ y | mx] := by induction h; rfl

@[simp] lemma probFailure_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) :
    Pr[⊥ | h ▸ mx] = Pr[⊥ | mx] := by induction h; rfl

lemma probEvent_eqRec [MonadLiftT m SPMF] (h : α = β) (mx : m α) (q : β → Prop) :
    Pr[ q | h ▸ mx] = Pr[ fun x ↦ q (h ▸ x) | mx] := by induction h; rfl

end eqRec

section sums

/-- Connection between the two different probability notations. -/
lemma probOutput_true_eq_probEvent {α} {m : Type → Type u} [Monad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] = Pr[ p | mx] := by
  simp [probEvent_eq_tsum_indicator, probOutput_def, evalSPMF, map_eq_bind_pure_comp]
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

section spmf

variable [MonadLiftT m SPMF]

@[simp, grind .] lemma probOutput_le_one :
    Pr[= x | mx] ≤ 1 := by rw [probOutput_def]; exact PMF.coe_le_one (𝒮[mx]) x
@[simp, grind ., aesop (rule_sets := [finiteness]) safe apply]
lemma probOutput_ne_top :
    Pr[= x | mx] ≠ ∞ := by rw [probOutput_def]; exact PMF.apply_ne_top (𝒮[mx]) x
@[simp, grind .] lemma probOutput_lt_top :
    Pr[= x | mx] < ∞ := by rw [probOutput_def]; exact PMF.apply_lt_top (𝒮[mx]) x
@[simp, grind .] lemma not_one_lt_probOutput :
    ¬ 1 < Pr[= x | mx] := not_lt.2 probOutput_le_one

@[simp] lemma tsum_probOutput_le_one : ∑' x : α, Pr[= x | mx] ≤ 1 :=
  le_of_le_of_eq (le_add_self) (probFailure_add_tsum_probOutput mx)
@[simp, aesop (rule_sets := [finiteness]) safe apply]
lemma tsum_probOutput_ne_top : ∑' x : α, Pr[= x | mx] ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one

@[simp, grind .] lemma probEvent_le_one : Pr[ p | mx] ≤ 1 := by
  rw [probEvent_def, PMF.toOuterMeasure_apply]
  refine le_of_le_of_eq (ENNReal.tsum_le_tsum ?_) ((𝒮[mx]).tsum_coe)
  exact Set.indicator_le_self (some '' {x | p x}) _

@[simp, grind ., aesop (rule_sets := [finiteness]) safe apply]
lemma probEvent_ne_top :
    Pr[ p | mx] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
@[simp, grind .] lemma probEvent_lt_top :
    Pr[ p | mx] < ∞ := lt_top_iff_ne_top.2 probEvent_ne_top
@[simp, grind .] lemma not_one_lt_probEvent :
    ¬ 1 < Pr[ p | mx] := not_lt.2 probEvent_le_one

@[simp, grind .] lemma probFailure_le_one :
    Pr[⊥ | mx] ≤ 1 := by rw [probFailure_def]; exact PMF.coe_le_one (𝒮[mx]) none
@[simp, grind ., aesop (rule_sets := [finiteness]) safe apply]
lemma probFailure_ne_top :
    Pr[⊥ | mx] ≠ ∞ := by rw [probFailure_def]; exact PMF.apply_ne_top (𝒮[mx]) none
@[simp, grind .] lemma probFailure_lt_top :
    Pr[⊥ | mx] < ∞ := by rw [probFailure_def]; exact PMF.apply_lt_top (𝒮[mx]) none
@[simp, grind .] lemma not_one_lt_probFailure :
    ¬ 1 < Pr[⊥ | mx] := not_lt.2 probFailure_le_one

end spmf

@[simp, grind =]
lemma one_le_probOutput_iff [MonadLiftT m SPMF] : 1 ≤ Pr[= x | mx] ↔ Pr[= x | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probOutput, or_false, eq_comm]

@[simp, grind =]
lemma one_le_probEvent_iff [MonadLiftT m SPMF] : 1 ≤ Pr[ p | mx] ↔ Pr[ p | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probEvent, or_false, eq_comm]

@[simp, grind =]
lemma one_le_probFailure_iff [MonadLiftT m SPMF] : 1 ≤ Pr[⊥ | mx] ↔ Pr[⊥ | mx] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probFailure, or_false, eq_comm]

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp]
lemma probOutput_eq_one_iff [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m] :
    Pr[= x | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ support mx = {x} := by
  rw [← probEvent_eq_eq_probOutput]
  simp [probOutput_def, probFailure_def, SPMF.apply_eq_toPMF_some, PMF.apply_eq_one_iff,
    Set.ext_iff, Option.forall, mem_support_iff_evalSPMF_apply_ne_zero]
alias ⟨_, probOutput_eq_one⟩ := probOutput_eq_one_iff

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp]
lemma one_eq_probOutput_iff [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m] :
    1 = Pr[= x | mx] ↔ Pr[⊥ | mx] = 0 ∧ support mx = {x} := by
  rw [eq_comm, probOutput_eq_one_iff]
alias ⟨_, one_eq_probOutput⟩ := one_eq_probOutput_iff

-- `grind`-safe in isolation, and the natural mirror of `one_eq_probOutput_iff'` (which kept its
-- `grind` tag): both are the `finSupport`-singleton characterization. See `probability.md`.
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
  simpa [hnf, tsum_eq_single (f := (Pr[= · | mx])) x
    fun y hy ↦ (probOutput_eq_zero_iff _ _).mpr fun hmem ↦ hy (huniq y hmem)]
    using probFailure_add_tsum_probOutput mx

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

-- also `@[grind =]`: without the tag `grind` routes the impossible event through the support
-- machinery and fails on `Pr[ fun _ => False | mx] = 0`
@[simp, grind =]
lemma probEvent_False (mx : m α) :
    Pr[ fun _ => False | mx] = 0 := by
  simp [probEvent_eq_tsum_indicator]

@[simp, grind =]
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

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp]
lemma probFailure_eq_one_iff [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) :
    Pr[⊥ | mx] = 1 ↔ support mx = ∅ := by
  simp [probFailure_eq_one_iff_probEvent_true, probEvent_eq_tsum_subtype_mem_support, Set.ext_iff]

@[aesop unsafe forward]
lemma probFailure_eq_one [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} (h : support mx = ∅) : Pr[⊥ | mx] = 1 := (probFailure_eq_one_iff mx).mpr h

/-- `grind`-friendly companion to `probFailure_eq_one_iff`: phrasing "fails with probability one"
via `Set.Nonempty` — which `grind` keeps atomic — avoids the support quantifier that makes the
`support = ∅` form saturate, so this stays in the default `grind` set. -/
@[grind =]
lemma probFailure_eq_one_iff_not_nonempty [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) :
    Pr[⊥ | mx] = 1 ↔ ¬ (support mx).Nonempty := by
  simp only [probFailure_eq_one_iff, Set.not_nonempty_iff_eq_empty]

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
  rw [probFailure_def, SPMF.run_eq_toPMF]
  change (some <$> (liftM mx : PMF α)) none = 0
  simp [PMF.monad_map_eq_map, PMF.map_apply]

lemma tsum_probOutput_of_liftM_PMF (mx : m α) :
    ∑' x, Pr[= x | mx] = 1 := by simp

lemma tsum_support_probOutput_of_liftM_PMF [MonadLiftT m SetM] [EvalDistCompatible m]
    (mx : m α) : ∑' x : support mx, Pr[= x | mx] = 1 := by simp

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
    [HasEvalFinset m] [DecidableEq α] {mx : m α} {c : ENNReal}
    (hconst : ∀ x ∈ support mx, Pr[= x | mx] = c) :
    c = 1 / (finSupport mx).card := by
  have h := sum_finSupport_probOutput_of_liftM_PMF (m := m) mx
  rw [Finset.sum_congr rfl fun x hx => hconst x (mem_support_of_mem_finSupport hx),
    Finset.sum_const, nsmul_eq_mul, mul_comm] at h
  simpa using ENNReal.eq_inv_of_mul_eq_one_left h

end pmf_denotation

/-! ## Monotonicity and complementation for `probEvent` -/

section probEvent_mono_compl

variable [MonadLiftT m SPMF]
  {mx : m α} {p q : α → Prop}

lemma probEvent_compl (mx : m α) (p : α → Prop) :
    Pr[ p | mx] + Pr[ fun x => ¬p x | mx] = 1 - Pr[⊥ | mx] := by
  have := Classical.decPred p
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add, ← tsum_probOutput_eq_sub]
  exact tsum_congr fun x => by split_ifs <;> simp_all

/-- Union bound: the probability of `p ∨ q` is at most the sum of probabilities. -/
lemma probEvent_or_le (mx : m α) (p q : α → Prop) :
    Pr[ fun x => p x ∨ q x | mx] ≤ Pr[ p | mx] + Pr[ q | mx] := by
  have := Classical.decPred p; have := Classical.decPred q
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

/-- **First-moment / Markov bound.** The probability of `p` is at most the expectation of any
`ℝ≥0∞`-valued cost `c` that is `≥ 1` wherever `p` holds. This is the elementary core of a
first-moment (union) argument: a monotone "bad" event whose occurrence forces a unit of some
nonnegative cost has probability bounded by the expected cost. -/
lemma probEvent_le_tsum_probOutput_mul_cost (mx : m α) (p : α → Prop) (c : α → ℝ≥0∞)
    (hc : ∀ x, p x → 1 ≤ c x) :
    Pr[ p | mx] ≤ ∑' x : α, Pr[= x | mx] * c x := by
  have := Classical.decPred p
  rw [probEvent_eq_tsum_ite mx p]
  refine ENNReal.tsum_le_tsum fun x => ?_
  split_ifs with hp
  · calc Pr[= x | mx] = Pr[= x | mx] * 1 := (mul_one _).symm
      _ ≤ Pr[= x | mx] * c x := by gcongr; exact hc x hp
  · exact zero_le

variable [MonadLiftT m SetM] [EvalDistCompatible m]

/-- **First-moment / Markov bound** (`support`-restricted cost). Variant of
`probEvent_le_tsum_probOutput_mul_cost` whose `c ≥ 1` hypothesis need only hold on the
`support` of `mx`. -/
lemma probEvent_le_tsum_probOutput_mul_cost_of_mem_support
    (mx : m α) (p : α → Prop) (c : α → ℝ≥0∞)
    (hc : ∀ x ∈ support mx, p x → 1 ≤ c x) :
    Pr[ p | mx] ≤ ∑' x : α, Pr[= x | mx] * c x := by
  have := Classical.decPred p
  rw [probEvent_eq_tsum_ite mx p]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · split_ifs with hp
    · calc Pr[= x | mx] = Pr[= x | mx] * 1 := (mul_one _).symm
        _ ≤ Pr[= x | mx] * c x := by
              gcongr
              exact hc x hx hp
    · exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hx]
    simp

/-- If `p` implies `q` on the `support` of a computation then it is more likely to happen. -/
@[gcongr]
lemma probEvent_mono (h : ∀ x ∈ support mx, p x → q x) : Pr[ p | mx] ≤ Pr[ q | mx] := by
  have := Classical.decPred p; have := Classical.decPred q
  simp only [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun x => ?_
  split_ifs with hp hq <;>
    first
    | rfl
    | exact zero_le
    | exact le_of_eq (probOutput_eq_zero_of_not_mem_support fun hx => hq (h x hx hp))

/-- If `p` implies `q` on the `finSupport` of a computation then it is more likely to happen. -/
lemma probEvent_mono' [HasEvalFinset m] [DecidableEq α]
    (h : ∀ x ∈ finSupport mx, p x → q x) : Pr[ p | mx] ≤ Pr[ q | mx] :=
  probEvent_mono (fun x hx hpx => h x (mem_finSupport_of_mem_support hx) hpx)

/-- If `p` implies `q` everywhere then `p` is less likely than `q`. Convenience
specialisation of `probEvent_mono` that drops the support hypothesis. -/
@[gcongr low]
lemma probEvent_mono'' (h : ∀ x, p x → q x) : Pr[ p | mx] ≤ Pr[ q | mx] :=
  probEvent_mono (fun x _ => h x)

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp low]
lemma probEvent_eq_one_iff :
    Pr[ p | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, p x := by
  rw [show (∀ x ∈ support mx, p x) ↔ Pr[ fun x => ¬p x | mx] = 0 by
    simp [probEvent_eq_zero_iff]]
  have hadd : Pr[ p | mx] + (Pr[ fun x => ¬p x | mx] + Pr[⊥ | mx]) = 1 := by
    rw [← add_assoc, probEvent_compl mx p, tsub_add_cancel_of_le probFailure_le_one]
  refine ⟨fun h => ?_, fun ⟨hf, hb⟩ => by simpa [hf, hb] using hadd⟩
  rw [h] at hadd
  exact and_comm.1 (add_eq_zero.1 (by simpa using hadd))

alias ⟨_, probEvent_eq_one⟩ := probEvent_eq_one_iff

/-- Pointwise variant of `probOutput_eq_one_iff`: `Pr[= x | mx] = 1` iff the support is
a subset of `{x}` (phrased as a forall over the support) and the computation never fails.

More usable than `probOutput_eq_one_iff` when the caller wants to iterate over arbitrary
support elements rather than prove a set equality. -/
lemma probOutput_eq_one_iff_forall (mx : m α) (x : α) :
    Pr[= x | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ ∀ y ∈ support mx, y = x := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp low]
lemma one_eq_probEvent_iff :
    1 = Pr[ p | mx] ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, p x := by
  rw [eq_comm, probEvent_eq_one_iff]

alias ⟨_, one_eq_probEvent⟩ := one_eq_probEvent_iff

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp]
lemma probEvent_eq_one_iff' [HasEvalFinset m] [DecidableEq α] :
    Pr[ p | mx] = 1 ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ finSupport mx, p x := by
  simp_rw [probEvent_eq_one_iff, mem_finSupport_iff_mem_support]

alias ⟨_, probEvent_eq_one'⟩ := probEvent_eq_one_iff'

-- `simp`-only: `grind` saturates on this support-quantifier characterization.
@[simp]
lemma one_eq_probEvent_iff' [HasEvalFinset m] [DecidableEq α] :
    1 = Pr[ p | mx] ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ finSupport mx, p x := by
  rw [eq_comm, probEvent_eq_one_iff']

alias ⟨_, one_eq_probEvent'⟩ := one_eq_probEvent_iff'

@[simp]
lemma function_support_probOutput :
    Function.support (Pr[= · | mx]) = support mx := by
  simp only [Function.support, ne_eq, probOutput_eq_zero_iff, not_not, Set.ofPred_mem_eq]

lemma mem_support_iff_of_evalSPMF_eq {m n} [Monad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    [Monad n] [MonadLiftT n SPMF] [MonadLiftT n SetM] [EvalDistCompatible n]
    {mx : m α} {mx' : n α} (h : 𝒮[mx] = 𝒮[mx']) (x : α) :
    x ∈ support mx ↔ x ∈ support mx' := by
  simp only [mem_support_iff, probOutput_def, h]

lemma mem_finSupport_iff_of_evalSPMF_eq {m n} [Monad m] [MonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    [Monad n] [MonadLiftT n SPMF] [MonadLiftT n SetM] [EvalDistCompatible n]
    [HasEvalFinset m] [HasEvalFinset n] [DecidableEq α]
    {mx : m α} {mx' : n α} (h : 𝒮[mx] = 𝒮[mx']) (x : α) :
    x ∈ finSupport mx ↔ x ∈ finSupport mx' := by
  simp only [mem_finSupport_iff_mem_support, mem_support_iff_of_evalSPMF_eq h]

open Classical in
omit [MonadLiftT m SetM] [EvalDistCompatible m] in
lemma indicator_objective_eq_probEvent (mx : m (α × β)) (R : α → β → Prop) :
    (∑' z, Pr[= z | mx] * (if R z.1 z.2 then 1 else 0)) = Pr[ fun z => R z.1 z.2 | mx] := by
  rw [probEvent_eq_tsum_ite]
  refine tsum_congr fun z => ?_
  by_cases hR : R z.1 z.2 <;> simp [hR]

end probEvent_mono_compl

/-! ## Expected values -/

section expectedValue

variable [MonadLiftT m SPMF]

namespace OracleComp.EvalDist

/-- The expected value `∑' x, Pr[= x | mx] * g x` of `g` on the output of `mx`. Failing runs
contribute nothing, so on a computation that can fail this is the expectation of the
conditional-on-success value scaled by the success probability, not a conditional expectation.
`expectedValue` is the head symbol `gcongr` keys on for bind bounds (see
`probEvent_bind_eq_expectedValue`). -/
noncomputable def expectedValue (mx : m α) (g : α → ℝ≥0∞) : ℝ≥0∞ := ∑' x, Pr[= x | mx] * g x

theorem expectedValue_def (mx : m α) (g : α → ℝ≥0∞) :
    expectedValue mx g = ∑' x, Pr[= x | mx] * g x := rfl

/-- Expectation is monotone in the functional. Tagged at low `gcongr` priority so that
`expectedValue_mono_of_support`, which only asks for the bound on `support mx`, is tried first. -/
@[gcongr low]
theorem expectedValue_mono (mx : m α) {g h : α → ℝ≥0∞} (hgh : ∀ x, g x ≤ h x) :
    expectedValue mx g ≤ expectedValue mx h :=
  ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (hgh x)

/-- A pointwise bound on the functional bounds the expectation, since the total mass is at most
one. -/
theorem expectedValue_le_of_le (mx : m α) {g : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, g x ≤ c) :
    expectedValue mx g ≤ c :=
  (expectedValue_mono mx h).trans <| by
    rw [expectedValue, ENNReal.tsum_mul_right]
    exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

theorem expectedValue_add (mx : m α) (g h : α → ℝ≥0∞) :
    expectedValue mx (fun x => g x + h x) = expectedValue mx g + expectedValue mx h := by
  simp only [expectedValue, mul_add]
  exact ENNReal.tsum_add

variable [MonadLiftT m SetM] [EvalDistCompatible m]

/-- `expectedValue_mono` with the hypothesis restricted to `support mx`. After `gcongr with x hx`
the goal is `g x ≤ h x` with `hx : x ∈ support mx` in context. -/
@[gcongr]
theorem expectedValue_mono_of_support {mx : m α} {g h : α → ℝ≥0∞}
    (hgh : ∀ x ∈ support mx, g x ≤ h x) : expectedValue mx g ≤ expectedValue mx h := by
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · exact mul_le_mul' le_rfl (hgh x hx)
  · simp [probOutput_eq_zero_of_not_mem_support hx]

/-- A bound on the functional over `support mx` bounds the expectation. -/
theorem expectedValue_le_of_support {mx : m α} {g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ x ∈ support mx, g x ≤ c) : expectedValue mx g ≤ c :=
  (expectedValue_mono_of_support h).trans (expectedValue_le_of_le mx fun _ => le_rfl)

end OracleComp.EvalDist

/-- A constant bound on the functional bounds the expectation `∑' x, Pr[= x | mx] * f x`. -/
lemma tsum_probOutput_mul_le_of_le (mx : m α) {f : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, f x ≤ c) :
    ∑' x, Pr[= x | mx] * f x ≤ c :=
  OracleComp.EvalDist.expectedValue_le_of_le mx h

end expectedValue
