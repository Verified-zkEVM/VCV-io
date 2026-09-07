/-
Copyright (c) 2026 Devon Tuma, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import PolyFun.PFunctor.Free.Cursor.Fork
public import VCVio.EvalDist.Prod
public import VCVio.OracleComp.EvalDist

/-!
# Probability Bounds for Forking Oracle Computations

This file connects PolyFun's typed occurrence forks to `OracleComp` probability.
It packages the conditional-square argument for two independent completions of
one occurrence context, leaving cryptographic reductions to supply only an
output observation and a reachability hypothesis.

The `OracleComp.Cursor` namespace transports PolyFun's `PFunctor.FreeM.Cursor` operations
across the `OracleComp` abstraction boundary; the probability content lives in the
theorems below.

## Main definitions

* `observedForkPair`: the observed outputs of both completions of a fixed typed occurrence.
* `OutputSelectsOccurrence`: the hypothesis that an observed output witnesses the occurrence.

## Main results

* `sq_probOutput_map_le_observedForkPair`: observed success squares under two independent
  completions of the selected occurrence context.
* `probEvent_answer_ofFreeM_complete`: completing an occurrence resamples the focused answer
  as a fresh query.
* `probEvent_focusCollision_ofFreeM_fork_le`: the two focused answers of a located fork collide
  with probability at most the inverse answer-space cardinality.
-/

@[expose] public section

open OracleSpec ENNReal

open scoped PFunctor

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

namespace Cursor

/-- Execute an intrinsic path through the `OracleComp` abstraction boundary. -/
@[reducible] def withPath (main : OracleComp spec α) : OracleComp spec (PFunctor.FreeM.Path main) :=
  ofFreeM (PFunctor.FreeM.withPath (toFreeM main))

@[simp] private theorem map_output_withPath (main : OracleComp spec α) :
    (PFunctor.FreeM.output main <$> withPath main : OracleComp spec α) = main :=
  PFunctor.FreeM.map_output_withPath main

/-- Split at an occurrence through the `OracleComp` abstraction boundary. -/
@[reducible] def splitAtValid [spec.DecidableEq] (main : OracleComp spec α) (i : ι) (n : Nat) :
    OracleComp spec {split : PFunctor.FreeM.Cursor.Split i main n // split.Valid} :=
  ofFreeM (PFunctor.FreeM.Cursor.splitAtValid i (toFreeM main) n)

/-- Complete one occurrence split through the `OracleComp` abstraction boundary. -/
@[reducible] def complete {main : OracleComp spec α} {i : ι} {n : Nat}
    (split : PFunctor.FreeM.Cursor.Split i main n) : OracleComp spec (PFunctor.FreeM.Path main) :=
  ofFreeM split.complete

/-- Complete a fork through the `OracleComp` abstraction boundary. -/
@[reducible] def completeFork {main : OracleComp spec α} {i : ι} {n : Nat}
    (split : PFunctor.FreeM.Cursor.Split i main n) :
    OracleComp spec (Option (PFunctor.FreeM.Cursor.ForkView i main n)) :=
  ofFreeM split.completeFork

/-- Complete an occurrence through the `OracleComp` abstraction boundary. -/
@[reducible] def completeOccurrence {main : OracleComp spec α} {i : ι} {n : Nat}
    (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) :
    OracleComp spec occurrence.Completion :=
  ofFreeM occurrence.complete

end Cursor

/-- Observe the outputs of both completions of a fixed typed occurrence. -/
def observedForkPair [spec.DecidableEq] (main : OracleComp spec α) (i : ι) (n : Nat)
    (observe : α → β) : OracleComp spec (Option (β × β)) :=
  Option.map (fun view =>
    (observe (PFunctor.FreeM.output main view.firstPath),
      observe (PFunctor.FreeM.output main view.secondPath))) <$>
        PFunctor.FreeM.Cursor.locateAndForkAt (P := spec.toPFunctor) i main n

/-- An observed output selects an occurrence only if that occurrence exists on
the corresponding intrinsic execution path. -/
def OutputSelectsOccurrence [spec.DecidableEq] (main : OracleComp spec α) (i : ι) (n : Nat)
    (observe : α → Option β) (value : β) : Prop :=
  ∀ path : PFunctor.FreeM.Path main,
    observe (PFunctor.FreeM.output main path) = some value →
      (PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path n).isSome

private theorem splitAtValid_bind_complete_oracleComp [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (n : Nat) :
    (Cursor.splitAtValid main i n >>= fun certified => Cursor.complete certified.1) =
      Cursor.withPath main :=
  PFunctor.FreeM.Cursor.splitAtValid_bind_complete i main n

private theorem splitAtValid_bind_completeFork_oracleComp [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (n : Nat) :
    (Cursor.splitAtValid main i n >>= fun certified => Cursor.completeFork certified.1) =
      PFunctor.FreeM.Cursor.locateAndForkAt (P := spec.toPFunctor) i main n :=
  (PFunctor.FreeM.Cursor.splitAtValid_bind_completeFork i main n).trans
    (PFunctor.FreeM.Cursor.forkAt_eq_locateAndForkAt i main n)

private theorem map_completeFork_found_oracleComp {main : OracleComp spec α} {i : ι} {n : Nat}
    (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) {γ : Type}
    (observe : PFunctor.FreeM.Cursor.ForkView i main n → γ) :
    Option.map observe <$> Cursor.completeFork (PFunctor.FreeM.Cursor.Split.found occurrence) =
      (Cursor.completeOccurrence occurrence >>= fun first =>
        (fun second => some (observe { occurrence, first, second })) <$>
          Cursor.completeOccurrence occurrence) :=
  PFunctor.FreeM.Cursor.Split.map_completeFork_found occurrence observe

/-- A certified missing split cannot produce an output selecting its nominal occurrence. -/
lemma ne_some_of_valid_missing [spec.DecidableEq]
    {main : OracleComp spec α} {i : ι} {n : Nat}
    {observe : α → Option β} {value : β}
    (hselect : OutputSelectsOccurrence main i n observe value)
    (path : PFunctor.FreeM.Path main)
    (hvalid : (PFunctor.FreeM.Cursor.Split.missing path :
      PFunctor.FreeM.Cursor.Split i main n).Valid) :
    observe (PFunctor.FreeM.output main path) ≠ some value :=
  fun hvalue => Nat.not_lt_of_ge hvalid
    ((PFunctor.FreeM.Cursor.locateAt?_isSome_iff_lt_occurrences _ _ _ _).mp
      (hselect path hvalue))

private theorem probOutput_pair_eq_observedForkPair_missing [spec.DecidableEq] [IsUniformSpec spec]
    {main : OracleComp spec α} (i : ι) (n : Nat) {observe : α → Option β} {value : β}
    {path : PFunctor.FreeM.Path main}
    (hvalid : (PFunctor.FreeM.Cursor.Split.missing path :
      PFunctor.FreeM.Cursor.Split i main n).Valid)
    (hselect : OutputSelectsOccurrence main i n observe value) :
    (Pr[= (some value, some value) | (do
        let a ← Cursor.complete (PFunctor.FreeM.Cursor.Split.missing path :
          PFunctor.FreeM.Cursor.Split i main n) >>=
          fun p => (pure (observe (PFunctor.FreeM.output main p)) : OracleComp spec (Option β))
        let b ← Cursor.complete (PFunctor.FreeM.Cursor.Split.missing path :
          PFunctor.FreeM.Cursor.Split i main n) >>=
          fun p => pure (observe (PFunctor.FreeM.output main p))
        pure (a, b) : OracleComp spec (Option β × Option β))]) =
      Pr[= some (some value, some value) | Option.map
        (fun view => (observe (PFunctor.FreeM.output main view.firstPath),
          observe (PFunctor.FreeM.output main view.secondPath))) <$>
          Cursor.completeFork (PFunctor.FreeM.Cursor.Split.missing path :
          PFunctor.FreeM.Cursor.Split i main n)] := by
  classical
  have hne' : some value ≠ observe (PFunctor.FreeM.output main path) :=
    Ne.symm (ne_some_of_valid_missing hselect path hvalid)
  have hforkNone : (Option.map (fun view => (observe (PFunctor.FreeM.output main view.firstPath),
      observe (PFunctor.FreeM.output main view.secondPath))) <$>
        Cursor.completeFork (PFunctor.FreeM.Cursor.Split.missing path :
          PFunctor.FreeM.Cursor.Split i main n) :
        OracleComp spec (Option (Option β × Option β))) = pure none := rfl
  have hcomplete : (do
      let a ← Cursor.complete (PFunctor.FreeM.Cursor.Split.missing path :
          PFunctor.FreeM.Cursor.Split i main n) >>=
        fun p => (pure (observe (PFunctor.FreeM.output main p)) : OracleComp spec (Option β))
      let b ← Cursor.complete (PFunctor.FreeM.Cursor.Split.missing path :
          PFunctor.FreeM.Cursor.Split i main n) >>=
        fun p => pure (observe (PFunctor.FreeM.output main p))
      pure (a, b) : OracleComp spec (Option β × Option β)) =
      pure (observe (PFunctor.FreeM.output main path),
        observe (PFunctor.FreeM.output main path)) := rfl
  rw [hforkNone, hcomplete]
  simp [hne']

private theorem probOutput_pair_eq_observedForkPair_found [spec.DecidableEq] [IsUniformSpec spec]
    {main : OracleComp spec α} {i : ι} {n : Nat} {observe : α → Option β} {value : β}
    (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) :
    (Pr[= (some value, some value) | (do
        let a ← Cursor.complete (PFunctor.FreeM.Cursor.Split.found occurrence) >>=
          fun p => (pure (observe (PFunctor.FreeM.output main p)) : OracleComp spec (Option β))
        let b ← Cursor.complete (PFunctor.FreeM.Cursor.Split.found occurrence) >>=
          fun p => pure (observe (PFunctor.FreeM.output main p))
        pure (a, b) : OracleComp spec (Option β × Option β))]) =
      Pr[= some (some value, some value) | Option.map
        (fun view => (observe (PFunctor.FreeM.output main view.firstPath),
          observe (PFunctor.FreeM.output main view.secondPath))) <$>
          Cursor.completeFork (PFunctor.FreeM.Cursor.Split.found occurrence)] := by
  let completion : OracleComp spec occurrence.Completion := Cursor.completeOccurrence occurrence
  let observeCompletion : occurrence.Completion → Option β := fun completed =>
    observe (PFunctor.FreeM.output main completed.path)
  symm
  rw [map_completeFork_found_oracleComp]
  change Pr[= some (some value, some value) | completion >>= fun first =>
      (fun second => some (observeCompletion first, observeCompletion second)) <$> completion] = _
  have hpair : (completion >>= fun first =>
      (fun second => some (observeCompletion first, observeCompletion second)) <$> completion) =
      some <$> (do
        let first ← completion
        let second ← completion
        pure (observeCompletion first, observeCompletion second) : OracleComp spec _) := by
    simp [monad_norm]
  rw [hpair, probOutput_some_map_some, probOutput_bind_bind_prod_mk_eq_mul',
    probOutput_bind_bind_prod_mk_eq_mul']
  have hkernel : (observeCompletion <$> completion : OracleComp spec _) =
      Cursor.complete (PFunctor.FreeM.Cursor.Split.found occurrence) >>=
        fun p => (pure (observe (PFunctor.FreeM.output main p)) : OracleComp spec (Option β)) := by
    change PFunctor.FreeM.map observeCompletion occurrence.complete =
      occurrence.completePath >>= fun p =>
        (pure (observe (PFunctor.FreeM.output main p)) : OracleComp spec (Option β))
    rw [bind_pure_comp]
    change _ = PFunctor.FreeM.map (observe ∘ PFunctor.FreeM.output main)
      (PFunctor.FreeM.map PFunctor.FreeM.Cursor.Occurrence.Completion.path occurrence.complete)
    rw [← PFunctor.FreeM.comp_map]
    apply congrArg (fun f => PFunctor.FreeM.map f occurrence.complete)
    funext completed
    rw [Function.comp_apply, Function.comp_apply]
  rw [hkernel]
  have hid : (fun a : Option β => a) <$>
      (Cursor.complete (PFunctor.FreeM.Cursor.Split.found occurrence) >>=
        fun p => (pure (observe (PFunctor.FreeM.output main p)) : OracleComp spec (Option β))) =
      Cursor.complete (PFunctor.FreeM.Cursor.Split.found occurrence) >>=
        fun p => pure (observe (PFunctor.FreeM.output main p)) := id_map _
  rw [hid]

/-- Fixed-index observed success squares under two independent completions of
the selected occurrence context. -/
theorem sq_probOutput_map_le_observedForkPair [spec.DecidableEq] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (n : Nat) (observe : α → Option β) (value : β)
    (hselect : OutputSelectsOccurrence main i n observe value) :
    Pr[= value | observe <$> main] ^ 2 ≤
      Pr[= (some (some value, some value) : Option (Option β × Option β)) |
        observedForkPair main i n observe] := by
  classical
  let : DecidableEq spec.Domain := inferInstance
  let (j : spec.Domain) : DecidableEq (spec.Range j) := inferInstance
  set y : Option β := some value
  let splitComp : OracleComp spec
      {split : PFunctor.FreeM.Cursor.Split i main n // split.Valid} :=
    Cursor.splitAtValid main i n
  let finish : PFunctor.FreeM.Path main → OracleComp spec (Option β) :=
    fun path => pure (observe (PFunctor.FreeM.output main path))
  let kernel : {split : PFunctor.FreeM.Cursor.Split i main n // split.Valid} →
      OracleComp spec (Option β) := fun certified =>
    Cursor.complete certified.1 >>= finish
  have hprogram : (observe <$> main : OracleComp spec (Option β)) = splitComp >>= kernel := by
    simp only [splitComp, kernel]
    rw [← bind_assoc, splitAtValid_bind_complete_oracleComp]
    calc
      observe <$> main = observe <$>
          (PFunctor.FreeM.output main <$> Cursor.withPath main) := by
        rw [Cursor.map_output_withPath]
      _ = (observe ∘ PFunctor.FreeM.output main) <$>
          Cursor.withPath main := by
        simp only [Functor.map_map, Function.comp_def]
      _ = Cursor.withPath main >>= finish := by
        simp [finish, Function.comp_def]
  rw [hprogram]
  refine (sq_probOutput_bind_le_probOutput_bind_prod splitComp kernel y).trans_eq ?_
  let observeView : PFunctor.FreeM.Cursor.ForkView i main n → Option β × Option β :=
    fun view =>
      (observe (PFunctor.FreeM.output main view.firstPath),
        observe (PFunctor.FreeM.output main view.secondPath))
  have hpair : observedForkPair main i n observe =
      splitComp >>= fun certified => Option.map observeView <$>
        Cursor.completeFork certified.1 := by
    unfold observedForkPair
    rw [← splitAtValid_bind_completeFork_oracleComp, map_bind]
  rw [hpair, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun certified => congrArg
    (fun z => Pr[= certified | splitComp] * z) ?_
  rcases certified with ⟨split, hvalid⟩
  cases split with
  | missing path => exact probOutput_pair_eq_observedForkPair_missing i n hvalid hselect
  | found occurrence => exact probOutput_pair_eq_observedForkPair_found occurrence

/-! ## Focused-answer collision bound

The two focused answers of a completed fork collide with probability at most the
inverse answer-space cardinality: the second focused answer is a fresh uniform
draw, independent of the first path and of the resampled suffix. -/

/-- Completing an occurrence resamples the focused answer as a fresh `query i`:
any event on that answer marginalizes the resampled suffix away. -/
theorem probEvent_answer_ofFreeM_complete [spec.DecidableEq] [IsProbabilitySpec spec]
    {main : OracleComp spec α} {i : ι} {n : Nat}
    (occ : PFunctor.FreeM.Cursor.Occurrence i main n) (P : spec.Range i → Prop) :
    Pr[fun completion => P completion.answer | OracleComp.ofFreeM occ.complete] =
      Pr[P | (query i : OracleComp spec (spec.Range i))] := by
  classical
  unfold PFunctor.FreeM.Cursor.Occurrence.complete
  rw [PFunctor.FreeM.liftBind_eq, probEvent_ofFreeM_bind_eq_tsum,
    probEvent_eq_tsum_ite (query i)]
  refine tsum_congr fun a => ?_
  simp only [probEvent_ofFreeM_map, Function.comp_def, probEvent_const]
  by_cases hPa : P a <;> simp [hPa]
  rfl

/-- The two focused answers of a located fork collide with probability at most
the inverse answer-space cardinality: the second answer is a fresh uniform
draw, independent of the first completion. Any additional guard on the first
output only tightens the event. -/
theorem probEvent_focusCollision_ofFreeM_fork_le [spec.DecidableEq] [IsUniformSpec spec]
    {main : OracleComp spec α} {i : ι} {n : Nat} {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) (accept : α → Prop) :
    Pr[fun view => view.firstAnswer = view.secondAnswer ∧
        accept (PFunctor.FreeM.output main view.firstPath) |
          OracleComp.ofFreeM located.fork] ≤ (Fintype.card (spec.Range i) : ℝ≥0∞)⁻¹ := by
  rw [PFunctor.FreeM.Cursor.Located.fork_eq_map_complete, probEvent_ofFreeM_map]
  exact (probEvent_mono fun completion _ h => h.1).trans <|
    (probEvent_answer_ofFreeM_complete located.occurrence
      (fun a => located.completion.answer = a)).trans_le
      (probEvent_query_le_inv_of_unique i _ fun x y hx hy => hx.symm.trans hy)

end OracleComp
