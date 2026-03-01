/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Basic Constructions of Simulation Oracles

This file defines a number of basic simulation oracles, as well as operations to combine them.
-/

open OracleSpec OracleComp Prod Sum

universe u v w

variable {ι} {spec : OracleSpec ι} {α β γ : Type u}

namespace QueryImpl

section compose

variable {ι' : Type} {spec' : OracleSpec ι'} {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- Given an implementation of `spec` in terms of a new set of oracles `spec'`,
and an implementation of `spec'` in terms of arbitrary `m`, implement `spec` in terms of `m`. -/
def compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec')) :
    QueryImpl spec m :=
  fun t => simulateQ so' (so t)

infixl : 65 " ∘ₛ " => QueryImpl.compose

omit [LawfulMonad m] in
@[simp]
lemma apply_compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec'))
    (t : spec.Domain) : (so' ∘ₛ so) t = simulateQ so' (so t) := rfl

@[simp]
lemma simulateQ_compose (so' : QueryImpl spec' m)
    (so : QueryImpl spec (OracleComp spec'))
    (oa : OracleComp spec α) : simulateQ (so' ∘ₛ so) oa = simulateQ so' (simulateQ so oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h]

end compose

end QueryImpl

/-- Simulation oracle for replacing queries with uniform random selection, using `unifSpec`.
The resulting computation is still identical under `evalDist`.
The relevant `OracleSpec` can usually be inferred automatically, so we leave it implicit. -/
def uniformSampleImpl [∀ i, SampleableType (spec.Range i)] :
    QueryImpl spec ProbComp := fun t => $ᵗ spec.Range t

namespace uniformSampleImpl

variable {ι₀ : Type} {spec₀ : OracleSpec ι₀} [∀ i, SampleableType (spec₀.Range i)]

@[simp]
lemma evalDist_simulateQ [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) :
    evalDist (simulateQ uniformSampleImpl oa) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h, uniformSampleImpl]

@[simp]
lemma probOutput_simulateQ [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (x : α) :
    Pr[= x | simulateQ uniformSampleImpl oa] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ oa)) x

@[simp]
lemma probEvent_simulateQ [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (p : α → Prop) :
    Pr[p | simulateQ uniformSampleImpl oa] = Pr[p | oa] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_simulateQ]

@[simp]
lemma support_simulateQ [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) :
    support (simulateQ uniformSampleImpl oa) = support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h, uniformSampleImpl]

@[simp]
lemma finSupport_simulateQ [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    [DecidableEq α] (oa : OracleComp spec₀ α) :
    finSupport (simulateQ uniformSampleImpl oa) = finSupport oa := by
  simp [finSupport_eq_iff_support_eq_coe]

end uniformSampleImpl
