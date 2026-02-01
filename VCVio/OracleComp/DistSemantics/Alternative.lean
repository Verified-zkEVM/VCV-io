/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist
import ToMathlib.General

/-!
# Lemmas About the Distribution Semantics of Failure Operations

This file collects various lemmas about the operations associated to `Alternative`,
like `guard`, `orElse`, `tryM?`, etc.
-/

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type v}

/-- `OptionT.lift` distributes over `orElse` when on the left of a bind. -/
lemma OptionT.lift_bind_orElse {m : Type u → Type v} [Monad m] [LawfulMonad m] {α β : Type u}
    (x : m α) (f : α → OptionT m β) (y : OptionT m β) :
    ((OptionT.lift x >>= f) <|> y) = (OptionT.lift x >>= fun a ↦ f a <|> y) := by
  ext; simp [OptionT.run_bind, OptionT.lift]

@[simp]
lemma evalDist_orElse [h : spec.FiniteRange] (oa oa' : OracleComp spec α) :
    evalDist (oa <|> oa') = (evalDist oa <|> evalDist oa') := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    simp only [evalDist_pure]
    convert evalDist_pure _ using 1; ext x; simp [Option.elimM]
  | failure => simp
  | query_bind i t oa h =>
    have hle : ((liftM (OracleSpec.query i t) >>= oa) <|> oa') =
        (liftM (OracleSpec.query i t) >>= fun u ↦ oa u <|> oa') := OptionT.lift_bind_orElse ..
    convert congr_arg _ hle using 1
    simp only [evalDist, simulateQ_bind, simulateQ_query]
    convert OptionT.lift_bind_orElse .. using 1
    · congr! 1
      exact funext fun u ↦ by simpa using h u
    · exact PMF.instLawfulMonad

@[simp]
lemma probFailure_orElse {ι : Type u} {spec : OracleSpec ι} {α : Type u} [spec.FiniteRange]
    (oa oa' : OracleComp spec α) : [⊥ | oa <|> oa'] = [⊥ | oa] * [⊥ | oa'] := by
  simp [probFailure_def, Option.elimM, tsum_option _ ENNReal.summable]

/-- `orElse` distributes over a query bind. -/
lemma orElse_distrib_query {ι : Type u} {spec : OracleSpec ι} {α : Type u}
    (i : ι) (t : spec.domain i) (oa : spec.range i → OracleComp spec α)
    (oa' : OracleComp spec α) :
    ((liftM (OracleSpec.query i t) >>= oa) <|> oa') =
      (liftM (OracleSpec.query i t) >>= fun u ↦ oa u <|> oa') := rfl

@[simp]
lemma support_orElse {ι : Type u} {spec : OracleSpec ι} {α : Type u}
    (oa oa' : OracleComp spec α) [Decidable oa.neverFails] : (oa <|> oa').support =
      if oa.neverFails then oa.support else oa.support ∪ oa'.support := by
  have h_support_def : ∀ x, x ∈ (oa <|> oa').support ↔
      x ∈ oa.support ∨ x ∈ oa'.support ∧ ¬ oa.neverFails := by
    induction' oa using OracleComp.inductionOn with oa i t oa' h
    · grind [supportWhen, support, neverFails_pure]
    · rw [OracleComp.orElse_distrib_query]
      simp only [support, neverFails, supportWhen_bind, supportWhen_query, Set.mem_univ,
        Set.iUnion_true, Set.mem_iUnion, neverFails_bind_iff, neverFails_query] at h ⊢
      grind
    · simp
  grind

end OracleComp
