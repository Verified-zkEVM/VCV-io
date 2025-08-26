/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.NeverFails
import VCVio.EvalDist.OptionT
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Output Distribution of Computations

This file defines a `HasEvalDist` for `OracleComp`, assuming uniform outputs of computations.
-/

open OracleSpec Option ENNReal BigOperators

universe u v w

namespace OracleComp

variable {spec : OracleSpec} {spec' : OracleSpec} {α β γ : Type w}

instance : LawfulMonad SetM := Set.instLawfulMonad

section supportM

protected instance hasSupportM : HasSupportM (OracleComp spec) where
  toFun := fun mx => PFunctor.FreeM.mapM (fun _ => Set.univ) mx
  toFun_pure' := by simp [OracleComp.pure_def]
  toFun_bind' := by simp [OracleComp.bind_def]

lemma support_def (mx : OracleComp spec α) :
    support mx = SetM.run (PFunctor.FreeM.mapM (fun _ => Set.univ) mx) := rfl

@[simp] lemma support_query (t : spec.domain) : support (query t) = Set.univ := by
  simp [support_def, SetM.run]

@[simp] lemma support_coin : support coin = {true, false} := by
  rw [coin_def, support_query]
  simp [Set.ext_iff]

@[simp] lemma support_uniformFin (n : ℕ) : support $[0..n] = Set.univ := by
  simp [uniformFin_def]
  rw [support_query]

end supportM

section evalDist

/-- The standard evaluation distribution on `OracleComp` given by mapping queries to a uniform
output distribution. In the case of `ProbComp` this is exactly the distribution coming from
each uniform selection responding uniformly. -/
protected noncomputable instance hasEvalDist [spec.Fintype] [spec.Inhabited] :
    HasEvalDist (OracleComp spec) where
  evalDist := simulateQ fun t => OptionT.mk (some <$> PMF.uniformOfFintype (spec.range t))
  support_eq mx := by induction mx using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t my h => simp [h, Set.ext_iff]
  __ := OracleComp.hasSupportM

variable [spec.Fintype] [spec.Inhabited]

lemma evalDist_def (mx : OracleComp spec α) : evalDist mx =
    simulateQ (fun t => OptionT.mk (some <$> PMF.uniformOfFintype (spec.range t))) mx := rfl

@[simp] lemma evalDist_query (t : spec.domain) :
    evalDist (query t) = OptionT.mk (some <$> PMF.uniformOfFintype (spec.range t)) := by
  simp [evalDist_def]

end evalDist

section hasFinEvalDist

open Classical -- We need decidable equality for the `finset` binds

protected noncomputable instance hasFinEvalDist [spec.Fintype] [spec.Inhabited] :
    HasFinEvalDist (OracleComp spec) where
  finSupport mx := OracleComp.construct (fun x => {x}) (fun _ _ r => Finset.univ.biUnion r) mx
  mem_finSupport_iff mx x := by
    induction mx using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t my h => simp [h]

variable [spec.Fintype] [spec.Inhabited]

lemma finSupport_def (mx : OracleComp spec α) : finSupport mx =
    OracleComp.construct (fun x => {x}) (fun _ _ r => Finset.univ.biUnion r) mx := rfl

@[simp] lemma finSupport_query (t : spec.domain) :
    finSupport (query t) = Finset.univ := by simp [finSupport_def]

end hasFinEvalDist

end OracleComp
