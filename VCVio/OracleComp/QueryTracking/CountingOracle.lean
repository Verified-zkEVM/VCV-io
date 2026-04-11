/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.SimSemantics.WriterT
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Counting Queries Made by a Computation

This file defines a simulation oracle `countingOracle` for counting the number of queries made
while running the computation. The count is represented by a function from oracle indices to
counts, allowing each oracle to be tracked individually.

Tracking individually is not necessary, but gives tighter security bounds in some cases.
It also allows for generating things like seed values for a computation more tightly.
-/

open OracleSpec OracleComp

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

section withCost

variable {ω : Type u} [Monoid ω]

/-- Wrap an oracle implementation to accumulate cost in a `WriterT ω` layer.
The cost function `costFn` assigns a cost value to each oracle query.
Cost is accumulated before the implementation runs, so failed queries are still costed. -/
def withCost (so : QueryImpl spec m) (costFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  fun t => do tell (costFn t); so t

@[simp, grind =]
lemma withCost_apply (so : QueryImpl spec m) (costFn : spec.Domain → ω)
    (t : spec.Domain) :
    so.withCost costFn t = (do tell (costFn t); so t) := rfl

lemma fst_map_run_withCost [LawfulMonad m]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withCost costFn) mx).run = simulateQ so mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa h => simp [h]

/-- Cost-tracking preserves failure probability: for any base monad `m` with `HasEvalSPMF`,
wrapping an oracle implementation with `withCost` does not change the probability of failure. -/
lemma probFailure_run_simulateQ_withCost [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withCost costFn) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [show Pr[⊥ | (simulateQ (so.withCost costFn) mx).run] =
    Pr[⊥ | Prod.fst <$> (simulateQ (so.withCost costFn) mx).run] from
    (probFailure_map _ _).symm, fst_map_run_withCost]

lemma NeverFail_run_simulateQ_withCost_iff [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withCost costFn) mx).run ↔ NeverFail (simulateQ so mx) := by
  simp only [HasEvalSPMF.neverFail_iff, probFailure_run_simulateQ_withCost]

end withCost

/-- Wrap an oracle implementation to count queries in a `WriterT (QueryCount ι)` layer.
Counting happens before the implementation runs, so failed queries are still counted.
This is a special case of `withCost` where the cost function is `QueryCount.single`. -/
def withCounting [DecidableEq ι] (so : QueryImpl spec m) :
    QueryImpl spec (WriterT (QueryCount ι) m) :=
  so.withCost (QueryCount.single ·)

@[simp, grind =]
lemma withCounting_apply [DecidableEq ι] (so : QueryImpl spec m) (t : spec.Domain) :
    so.withCounting t = (do tell (QueryCount.single t); so t) := rfl

lemma withCounting_eq_withCost [DecidableEq ι] (so : QueryImpl spec m) :
    so.withCounting = so.withCost (QueryCount.single ·) := rfl

lemma fst_map_run_withCounting [DecidableEq ι] [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withCounting) mx).run = simulateQ so mx :=
  fst_map_run_withCost so _ mx

end QueryImpl

/-- Oracle with arbitrary cost tracking. The cost is accumulated in a `WriterT ω` layer
while preserving the original oracle behavior. -/
def costOracle {ω : Type u} [Monoid ω] (costFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCost costFn

/-- Oracle for counting the number of queries made by a computation. The count is stored as a
function from oracle indices to counts, to give finer grained information about the count. -/
def countingOracle [DecidableEq ι] :
    QueryImpl spec (WriterT (QueryCount ι) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCounting

lemma countingOracle_eq_costOracle [DecidableEq ι] :
    countingOracle (spec := spec) = costOracle (QueryCount.single ·) := rfl

namespace countingOracle

variable [DecidableEq ι]

@[simp]
lemma fst_map_run_simulateQ (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ countingOracle oa).run = oa := by
  rw [countingOracle, QueryImpl.fst_map_run_withCounting, simulateQ_ofLift_eq_self]

@[simp]
lemma run_simulateQ_bind_fst (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    ((simulateQ countingOracle oa).run >>= fun x => ob x.1) = oa >>= ob := by
  rw [← bind_map_left Prod.fst, fst_map_run_simulateQ]

/-- Specialization of `QueryImpl.probFailure_run_simulateQ_withCost` to `countingOracle`. -/
@[simp]
lemma probFailure_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type} (oa : OracleComp spec₀ α) :
    Pr[⊥ | (simulateQ (countingOracle (spec := spec₀)) oa).run] = Pr[⊥ | oa] := by
  simp only [countingOracle, QueryImpl.withCounting_eq_withCost,
    QueryImpl.probFailure_run_simulateQ_withCost, simulateQ_ofLift_eq_self]

/-- Specialization of `QueryImpl.NeverFail_run_simulateQ_withCost_iff` to `countingOracle`. -/
@[simp]
lemma NeverFail_run_simulateQ_iff {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) :
    NeverFail (simulateQ (countingOracle (spec := spec₀)) oa).run ↔ NeverFail oa := by
  simp only [countingOracle, QueryImpl.withCounting_eq_withCost,
    QueryImpl.NeverFail_run_simulateQ_withCost_iff, simulateQ_ofLift_eq_self]

@[simp]
lemma probEvent_fst_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (p : α → Prop) :
    Pr[ fun z => p z.1 | (simulateQ (countingOracle (spec := spec₀)) oa).run] = Pr[ p | oa] := by
  rw [show (fun z : α × QueryCount ι₀ => p z.1) = p ∘ Prod.fst from rfl,
    ← probEvent_map, fst_map_run_simulateQ]

@[simp]
lemma probOutput_fst_map_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [spec₀.Fintype] [spec₀.Inhabited] {α : Type}
    (oa : OracleComp spec₀ α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (countingOracle (spec := spec₀)) oa).run] =
      Pr[= x | oa] := by
  rw [fst_map_run_simulateQ]

section support

/-- Compatibility helper matching old state-style counting semantics:
simulate with zero initial count, then offset by `qc`. -/
def simulate (oa : OracleComp spec α) (qc : QueryCount ι) :
    OracleComp spec (α × QueryCount ι) :=
  Prod.map id (qc + ·) <$> (simulateQ countingOracle oa).run

lemma run_simulateT_eq_run_simulateT_zero (oa : OracleComp spec α) (qc : QueryCount ι) :
    simulate oa qc = Prod.map id (qc + ·) <$> simulate oa 0 := by
  unfold simulate
  rw [Functor.map_map]
  congr 1
  funext a
  rcases a with ⟨x, q⟩
  simp

/-- We can always reduce simulation with counting to start with `0`,
and add the initial count back at the end. -/
lemma support_simulate (oa : OracleComp spec α) (qc : QueryCount ι) :
    support (simulate oa qc) = Prod.map id (qc + ·) '' support (simulate oa 0) := by
  rw [run_simulateT_eq_run_simulateT_zero]
  simp [support_map]

/-- Reduce membership in support of simulation with counting to simulation starting from `0`. -/
lemma mem_support_simulate_iff (oa : OracleComp spec α) (qc : QueryCount ι)
    (z : α × QueryCount ι) :
    z ∈ support (simulate oa qc) ↔
      ∃ qc', (z.1, qc') ∈ support (simulate oa 0) ∧ qc + qc' = z.2 := by
  rw [support_simulate]
  simp only [Set.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨x, qc'⟩, hmem, hz⟩
    have hx : x = z.1 := by simpa using congrArg Prod.fst hz
    subst hx
    refine ⟨qc', ?_, ?_⟩
    · simpa using hmem
    · simpa using congrArg Prod.snd hz
  · rintro ⟨qc', hmem, hq⟩
    refine ⟨(z.1, qc'), ?_, ?_⟩
    · simpa using hmem
    · apply Prod.ext
      · simp
      · simpa using hq

lemma mem_support_simulate_iff_of_le (oa : OracleComp spec α) (qc : QueryCount ι)
    (z : α × QueryCount ι) (hz : qc ≤ z.2) :
    z ∈ support (simulate oa qc) ↔ (z.1, z.2 - qc) ∈ support (simulate oa 0) := by
  rw [mem_support_simulate_iff oa qc z]
  refine ⟨?_, ?_⟩
  · rintro ⟨qc', hmem, hq⟩
    convert hmem using 2
    funext i
    have hqi : qc i + qc' i = z.2 i := congrFun hq i
    simpa [Pi.sub_apply, hqi] using (Nat.add_sub_cancel_left (qc i) (qc' i))
  · intro hmem
    refine ⟨z.2 - qc, hmem, ?_⟩
    funext i
    simp [Pi.add_apply, Pi.sub_apply, Nat.add_sub_of_le (hz i)]

lemma le_of_mem_support_simulate {oa : OracleComp spec α} {qc : QueryCount ι}
    {z : α × QueryCount ι} (h : z ∈ support (simulate oa qc)) : qc ≤ z.2 := by
  rcases (mem_support_simulate_iff oa qc z).1 h with ⟨qc', _, hq⟩
  intro i
  exact le_of_le_of_eq (Nat.le_add_right _ _) (congrFun hq i)

section snd_map

lemma mem_support_snd_map_simulate_iff (oa : OracleComp spec α)
    (qc qc' : QueryCount ι) :
    qc' ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa qc) :
      OracleComp spec (QueryCount ι)) ↔
      ∃ qc'', ∃ x, (x, qc'') ∈ support (simulate oa 0) ∧ qc + qc'' = qc' := by
  simp only [support_map, Set.mem_image, Prod.exists, exists_eq_right]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    rcases (mem_support_simulate_iff oa qc (x, qc')).1 hx with ⟨qc'', hmem, hq⟩
    exact ⟨qc'', x, hmem, hq⟩
  · rintro ⟨qc'', x, hmem, hq⟩
    refine ⟨x, (mem_support_simulate_iff oa qc (x, qc')).2 ?_⟩
    exact ⟨qc'', hmem, hq⟩

lemma mem_support_snd_map_simulate_iff_of_le (oa : OracleComp spec α)
    {qc qc' : QueryCount ι} (hqc : qc ≤ qc') :
    qc' ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa qc) :
      OracleComp spec (QueryCount ι)) ↔
      qc' - qc ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa 0) :
        OracleComp spec (QueryCount ι)) := by
  rw [mem_support_snd_map_simulate_iff]
  simp only [support_map, Set.mem_image, Prod.exists, exists_eq_right]
  refine ⟨?_, ?_⟩
  · rintro ⟨qc'', x, hmem, hq⟩
    refine ⟨x, ?_⟩
    convert hmem using 2
    funext i
    have hqi : qc i + qc'' i = qc' i := congrFun hq i
    simpa [Pi.sub_apply, hqi] using (Nat.add_sub_cancel_left (qc i) (qc'' i))
  · rintro ⟨x, hx⟩
    refine ⟨qc' - qc, x, hx, ?_⟩
    funext i
    simp [Pi.add_apply, Pi.sub_apply, Nat.add_sub_of_le (hqc i)]

lemma le_of_mem_support_snd_map_simulate {oa : OracleComp spec α}
    {qc qc' : QueryCount ι}
    (h : qc' ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa qc) :
      OracleComp spec (QueryCount ι))) : qc ≤ qc' := by
  rcases (mem_support_snd_map_simulate_iff oa qc qc').1 h with ⟨qc'', _, _, hq⟩
  intro i
  exact le_of_le_of_eq (Nat.le_add_right _ _) (congrFun hq i)

lemma sub_mem_support_snd_map_simulate {oa : OracleComp spec α}
    {qc qc' : QueryCount ι}
    (h : qc' ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa qc) :
      OracleComp spec (QueryCount ι))) :
    qc' - qc ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa 0) :
      OracleComp spec (QueryCount ι)) :=
  (mem_support_snd_map_simulate_iff_of_le (oa := oa)
    (hqc := le_of_mem_support_snd_map_simulate h)).1 h

end snd_map

lemma add_mem_support_simulate {oa : OracleComp spec α} {qc : QueryCount ι}
    {z : α × QueryCount ι} (hz : z ∈ support (simulate oa qc)) (qc' : QueryCount ι) :
    (z.1, z.2 + qc') ∈ support (simulate oa (qc + qc')) := by
  rcases (mem_support_simulate_iff oa qc z).1 hz with ⟨qc1, hmem, hq⟩
  refine (mem_support_simulate_iff oa (qc + qc') (z.1, z.2 + qc')).2 ?_
  refine ⟨qc1, hmem, ?_⟩
  funext i
  have hi : qc i + qc1 i = z.2 i := by simpa [Pi.add_apply] using congrFun hq i
  calc
    ((qc + qc') + qc1) i = (qc i + qc1 i) + qc' i := by
      simp [Pi.add_apply, add_left_comm, add_comm]
    _ = z.2 i + qc' i := by simp [hi]
    _ = (z.2 + qc') i := by simp [Pi.add_apply]

@[simp]
lemma add_right_mem_support_simulate_iff (oa : OracleComp spec α)
    (qc qc' : QueryCount ι) (x : α) :
    (x, qc + qc') ∈ support (simulate oa qc) ↔ (x, qc') ∈ support (simulate oa 0) := by
  rw [mem_support_simulate_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨qc1, hmem, hq⟩
    convert hmem using 2
    funext i
    exact (Nat.add_left_cancel (congrFun hq i)).symm
  · intro hmem
    exact ⟨qc', hmem, by rfl⟩

@[simp]
lemma add_left_mem_support_simulate_iff (oa : OracleComp spec α)
    (qc qc' : QueryCount ι) (x : α) :
    (x, qc' + qc) ∈ support (simulate oa qc) ↔ (x, qc') ∈ support (simulate oa 0) := by
  rw [add_comm qc' qc]
  exact add_right_mem_support_simulate_iff oa qc qc' x

lemma mem_support_simulate_pure_iff (x : α) (qc : QueryCount ι)
    (z : α × QueryCount ι) :
    z ∈ support (simulate (pure x : OracleComp spec α) qc) ↔ z = (x, qc) := by
  simp [simulate]

lemma apply_ne_zero_of_mem_support_simulate_queryBind {t : spec.Domain}
    {oa : spec.Range t → OracleComp spec α} {qc : QueryCount ι} {z : α × QueryCount ι}
    (hz : z ∈ support (simulate ((query t : OracleComp spec _) >>= oa) qc)) :
    z.2 t ≠ 0 := by
  rcases (mem_support_simulate_iff (oa := ((query t : OracleComp spec _) >>= oa)) qc z).1 hz with
    ⟨q0, hq0mem, hqsum⟩
  rcases (by
      simpa [simulate, countingOracle, QueryImpl.withCounting_apply] using hq0mem) with
    ⟨u, b, _hb, hq0⟩
  have hqt : qc t + q0 t = z.2 t := congrFun hqsum t
  have hq0t : q0 t = QueryCount.single t t + b t := by
    simpa [Pi.add_apply] using (congrFun hq0 t).symm
  have hpos : 0 < z.2 t := by
    rw [← hqt, hq0t]
    have hsingle : 0 < QueryCount.single t t + b t := by
      simp [QueryCount.single]
    exact lt_of_lt_of_le hsingle (Nat.le_add_left _ _)
  exact Nat.ne_of_gt hpos

lemma exists_mem_support_of_mem_support_simulate_queryBind {t : spec.Domain}
    {oa : spec.Range t → OracleComp spec α} {qc : QueryCount ι} {z : α × QueryCount ι}
    (hz : z ∈ support (simulate ((query t : OracleComp spec _) >>= oa) qc)) :
    ∃ u, (z.1, Function.update z.2 t (z.2 t - 1)) ∈ support (simulate (oa u) qc) := by
  rcases (mem_support_simulate_iff (oa := ((query t : OracleComp spec _) >>= oa)) qc z).1 hz with
    ⟨q0, hq0mem, hqsum⟩
  rcases (by
      simpa [simulate, countingOracle, QueryImpl.withCounting_apply] using hq0mem) with
    ⟨u, b, hb, hq0⟩
  have hb0 : (z.1, b) ∈ support (simulate (oa u) 0) := by
    simpa [simulate] using hb
  refine ⟨u, ?_⟩
  refine (mem_support_simulate_iff (oa := oa u) qc
    (z := (z.1, Function.update z.2 t (z.2 t - 1)))).2 ?_
  refine ⟨b, hb0, ?_⟩
  funext j
  by_cases hj : j = t
  · subst j
    have hqj : qc t + q0 t = z.2 t := congrFun hqsum t
    have hq0j : q0 t = QueryCount.single t t + b t := by
      simpa [Pi.add_apply] using (congrFun hq0 t).symm
    have hcalc : qc t + b t = z.2 t - 1 := by
      rw [hq0j] at hqj
      have hsingle : QueryCount.single t t = 1 := by simp [QueryCount.single]
      rw [hsingle] at hqj
      omega
    simp [Function.update, hcalc]
  · have hqj : qc j + q0 j = z.2 j := congrFun hqsum j
    have hq0j : q0 j = QueryCount.single t j + b j := by
      simpa [Pi.add_apply] using (congrFun hq0 j).symm
    have hsingle : QueryCount.single t j = 0 := by simp [QueryCount.single, hj]
    have hcalc : qc j + b j = z.2 j := by
      rw [hq0j, hsingle] at hqj
      simpa [zero_add] using hqj
    simp [Function.update, hj, hcalc]

lemma mem_support_simulate_queryBind_iff (t : spec.Domain)
    (oa : spec.Range t → OracleComp spec α) (qc : QueryCount ι) (z : α × QueryCount ι) :
    z ∈ support (simulate ((query t : OracleComp spec _) >>= oa) qc) ↔
      z.2 t ≠ 0 ∧
      ∃ u, (z.1, Function.update z.2 t (z.2 t - 1)) ∈ support (simulate (oa u) qc) := by
  refine ⟨?_, ?_⟩
  · intro hz
    exact ⟨apply_ne_zero_of_mem_support_simulate_queryBind hz,
      exists_mem_support_of_mem_support_simulate_queryBind hz⟩
  · rintro ⟨hz0, hu⟩
    rcases hu with ⟨u, hu⟩
    rcases (mem_support_simulate_iff (oa := oa u) qc
      (z := (z.1, Function.update z.2 t (z.2 t - 1)))).1 hu with ⟨b, hb0, hbEq⟩
    have hbRun : (z.1, b) ∈ support ((simulateQ countingOracle (oa u)).run) := by
      simpa [simulate] using hb0
    have hbRun' : (z.1, b) ∈
        support ((simulateQ (QueryImpl.id' spec).withCounting (oa u)).run) := by
      simpa [countingOracle] using hbRun
    let q0 : QueryCount ι := QueryCount.single t + b
    have hq0mem : (z.1, q0) ∈ support (simulate ((query t : OracleComp spec _) >>= oa) 0) := by
      have hex :
          ∃ i a b', (a, b') ∈ support (simulateQ (QueryImpl.id' spec).withCounting (oa i)).run ∧
            (a, QueryCount.single t + b') = (z.1, q0) :=
        ⟨u, z.1, b, hbRun', by simp [q0]⟩
      simpa [simulate, countingOracle, QueryImpl.withCounting_apply] using hex
    have hqsum : qc + q0 = z.2 := by
      funext j
      by_cases hj : j = t
      · subst j
        have hbEqj : qc t + b t = (Function.update z.2 t (z.2 t - 1)) t := by
          simpa [Pi.add_apply] using congrFun hbEq t
        have hbEqj' : qc t + b t = z.2 t - 1 := by
          simpa [Function.update] using hbEqj
        have hzpos : 0 < z.2 t := Nat.pos_iff_ne_zero.mpr hz0
        have hsingle : QueryCount.single t t = 1 := by simp [QueryCount.single]
        calc
          (qc + q0) t = qc t + (QueryCount.single t t + b t) := by
            simp [q0, Pi.add_apply]
          _ = qc t + b t + 1 := by
            simp [hsingle, add_comm, add_assoc]
          _ = z.2 t := by
            omega
      · have hbEqj : qc j + b j = (Function.update z.2 t (z.2 t - 1)) j := by
          simpa [Pi.add_apply] using congrFun hbEq j
        have hbEqj' : qc j + b j = z.2 j := by
          simpa [Function.update, hj] using hbEqj
        calc
          (qc + q0) j = qc j + (QueryCount.single t j + b j) := by
            simp [q0, Pi.add_apply]
          _ = qc j + b j := by simp [QueryCount.single, hj]
          _ = z.2 j := hbEqj'
    exact (mem_support_simulate_iff (oa := ((query t : OracleComp spec _) >>= oa))
      qc z).2 ⟨q0, hq0mem, hqsum⟩

lemma exists_mem_support_of_mem_support {oa : OracleComp spec α} {x : α} (hx : x ∈ support oa)
    (qc : QueryCount ι) : ∃ qc', (x, qc') ∈ support (simulate oa qc) := by
  have hx' : x ∈ support (Prod.fst <$> (simulateQ countingOracle oa).run) := by
    simpa [fst_map_run_simulateQ] using hx
  rw [support_map] at hx'
  rcases hx' with ⟨z, hz, hzfst⟩
  have hz0 : (x, z.2) ∈ support (simulate oa 0) := by
    rw [simulate, support_map]
    refine ⟨z, hz, ?_⟩
    rcases z with ⟨x', q⟩
    simpa using hzfst
  refine ⟨qc + z.2, ?_⟩
  exact (mem_support_simulate_iff (oa := oa) qc (z := (x, qc + z.2))).2
    ⟨z.2, hz0, by rfl⟩

end support

end countingOracle
