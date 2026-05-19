/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import VCVio.ProgramLogic.Unary.SimulateQ
import Examples.CommitmentScheme.Hiding.CountBounds

open OracleSpec OracleComp ENNReal

variable {M S C : Type}
  [DecidableEq M] [DecidableEq S]
  [Fintype C] [Inhabited C]

section experiments

variable [Inhabited M] [Inhabited S]

/-- Combined query implementation for the averaged hiding experiment,
merging the left (uniform-salt) and right (commitment oracle) implementations. -/
def hidingAvgQueryImpl :
    QueryImpl (HidingAvgSpec M S C)
      (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C))) :=
  hidingAvgLeftImpl (M := M) (S := S) (C := C) +
    hidingAvgRightImpl (M := M) (S := S) (C := C)

/-- The averaged hiding computation: sample a uniform salt `s`, then run the
adversary's oracle computation for that salt. Returns `(s, b)` where `b` is the
adversary's guess bit. -/
def hidingAvgComp {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    OracleComp (HidingAvgSpec M S C) (S × Bool) := do
  let s ← (HidingAvgSpec M S C).query (Sum.inl ())
  let b ← OracleComp.liftComp (hidingOa A s) (HidingAvgSpec M S C)
  pure (s, b)

/-- Textbook-facing bounded real hiding experiment: the challenge salt is sampled once inside the
experiment, then the real hiding game for that salt is run. -/
def hidingMixedReal {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    OracleComp (HidingAvgSpec M S C) Bool := do
  let s ← (HidingAvgSpec M S C).query (Sum.inl ())
  OracleComp.liftComp (hidingReal A s) (HidingAvgSpec M S C)

/-- Textbook-facing bounded simulator experiment: sample the hidden salt internally, then run the
corresponding per-salt simulator game. -/
def hidingMixedSim {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    OracleComp (HidingAvgSpec M S C) Bool := do
  let s ← (HidingAvgSpec M S C).query (Sum.inl ())
  OracleComp.liftComp (hidingSim A s) (HidingAvgSpec M S C)

end experiments

lemma run_simulateQ_hidingAvgRightImpl_eq_liftComp {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st : HidingCountState M S C) :
    (simulateQ hidingAvgRightImpl oa).run st =
      OracleComp.liftComp ((simulateQ hidingImplCountAll oa).run st) (HidingAvgSpec M S C) := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
      simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind,
        OracleComp.liftComp_bind]
      have hstep :
          (hidingAvgRightImpl (M := M) (S := S) (C := C) t).run st =
            OracleComp.liftComp
              ((hidingImplCountAll (M := M) (S := S) (C := C) t).run st)
              (HidingAvgSpec M S C) := by
        change
          (StateT.mk (fun s =>
            OracleComp.liftComp
              ((hidingImplCountAll (M := M) (S := S) (C := C) t).run s)
              (HidingAvgSpec M S C))).run st =
            OracleComp.liftComp
              ((hidingImplCountAll (M := M) (S := S) (C := C) t).run st)
              (HidingAvgSpec M S C)
        rfl
      exact OracleComp.bind_congr' hstep (fun p => by
        simpa using ih p.1 p.2)

variable [Inhabited M] [Inhabited S] in
lemma run_simulateQ_hidingAvgComp_eq_bind {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0) =
      (liftM ((Unit →ₒ S).query ()) >>= fun s =>
        Prod.map (fun b => (s, b)) id <$>
          OracleComp.liftComp
            ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
            (HidingAvgSpec M S C)) := by
  have hleftrun :
      (simulateQ hidingAvgQueryImpl
          ((HidingAvgSpec M S C).query (Sum.inl ()) :
            OracleComp (HidingAvgSpec M S C) S)).run
          (∅, fun _ => 0) =
        (liftM ((Unit →ₒ S).query ()) >>= fun s => pure (s, (∅, fun _ => 0))) := by
    simp [hidingAvgQueryImpl, hidingAvgLeftImpl, simulateQ_query]
  rw [hidingAvgComp, simulateQ_bind, StateT.run_bind, hleftrun]
  change
    (liftM ((Unit →ₒ S).query ()) >>= fun s =>
      (simulateQ hidingAvgQueryImpl (do
          let b ← (hidingOa A s).liftComp (HidingAvgSpec M S C)
          pure (s, b))).run (∅, fun _ => 0)) = _
  refine OracleComp.bind_congr' rfl ?_
  intro s
  rw [simulateQ_bind, StateT.run_bind]
  rw [show simulateQ hidingAvgQueryImpl
      ((hidingOa A s).liftComp (HidingAvgSpec M S C)) =
        simulateQ hidingAvgRightImpl (hidingOa A s) by
        simpa [hidingAvgQueryImpl, OracleComp.liftComp_eq_liftM] using
          (QueryImpl.simulateQ_add_liftComp_right
            (impl₁' := hidingAvgLeftImpl) (impl₂' := hidingAvgRightImpl)
            (hidingOa A s))]
  rw [run_simulateQ_hidingAvgRightImpl_eq_liftComp]
  change
    ((fun a : Bool × HidingCountState M S C => ((s, a.1), a.2)) <$>
      (((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)).liftComp
        (HidingAvgSpec M S C))) =
    ((fun a : Bool × HidingCountState M S C => ((s, a.1), a.2)) <$>
      (((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)).liftComp
        (HidingAvgSpec M S C)))
  rfl

variable [Fintype S] [Inhabited M] [Inhabited S] in
/-- Averaged-mass bridge for hiding.

This packages the per-salt bad probabilities into the shared `hidingAvgComp`
run, where the salt is sampled once up front and then the shared count-all
simulation is reused for the rest of the game. -/
theorem sum_probEvent_hidingBad_eq_avg_bad_mass {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)]) =
    (Fintype.card S : ℝ≥0∞) *
      Pr[fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1 |
        (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)] := by
  classical
  let P : S → ℝ≥0∞ := fun s =>
    Pr[fun z : Bool × HidingCountState M S C => 2 ≤ z.2.2 s |
      (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)]
  have hrun := run_simulateQ_hidingAvgComp_eq_bind (M := M) (S := S) (C := C) A
  have hprob :
      Pr[fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1 |
          (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)] =
        ∑ s : S, Pr[= s | ((Unit →ₒ S).query () : OracleComp (Unit →ₒ S) S)] * P s := by
    rw [hrun, probEvent_bind_eq_tsum, tsum_fintype]
    refine Finset.sum_congr rfl ?_
    intro s hs
    have hsprob :
        Pr[= s | ((Unit →ₒ S).query () : OracleComp (Unit →ₒ S) S)] =
          (Fintype.card S : ℝ≥0∞)⁻¹ := by
      simp
    rw [probEvent_map, probEvent_liftComp, hsprob]
    congr 1
  have hcard0 : (Fintype.card S : ℝ≥0∞) ≠ 0 := by simp
  have hcard_top : (Fintype.card S : ℝ≥0∞) ≠ ∞ := by simp
  calc
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)])
        = ∑ s : S, P s := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            simpa [P] using
              probEvent_hidingBad_eq_countAll (M := M) (S := S) (C := C) A s
    _ = ∑ s : S, (Fintype.card S : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞)⁻¹ * P s) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          calc
            P s = 1 * P s := by rw [one_mul]
            _ = ((Fintype.card S : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞)⁻¹) * P s := by
                  rw [ENNReal.mul_inv_cancel hcard0 hcard_top]
            _ = (Fintype.card S : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞)⁻¹ * P s) := by
                  rw [mul_assoc]
    _ = (Fintype.card S : ℝ≥0∞) * ∑ s : S, (Fintype.card S : ℝ≥0∞)⁻¹ * P s := by
          rw [Finset.mul_sum]
    _ = (Fintype.card S : ℝ≥0∞) * ∑ s : S,
          Pr[= s | ((Unit →ₒ S).query () : OracleComp (Unit →ₒ S) S)] * P s := by
          simp_rw [probOutput_query]
    _ = (Fintype.card S : ℝ≥0∞) *
          Pr[fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1 |
            (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)] := by
          rw [hprob]

variable [Fintype S] [Inhabited M] [Inhabited S] in
lemma probEvent_hidingAvg_bad_le_wp_selectedCountPred
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    Pr[fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1 |
      (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)] ≤
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0))
      (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞)) := by
  let oa :=
    (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)
  have h :=
    OracleComp.ProgramLogic.markov_bound
      oa
      (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞))
      1
      (fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1)
      (fun z hz => by
        have hnat : (1 : ℕ) ≤ z.2.2 z.1.1 - 1 := by omega
        have hcast : (1 : ℝ≥0∞) ≤ (z.2.2 z.1.1 - 1 : ℝ≥0∞) := by
          exact_mod_cast hnat
        simpa using hcast)
  simpa [oa] using h

variable [Fintype S] [Inhabited M] [Inhabited S] in
lemma card_mul_wp_hidingAvg_selectedCountPred_eq_sum_wp_countPred
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (Fintype.card S : ℝ≥0∞) *
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0))
        (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞)) =
    ∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)) := by
  classical
  let Q : S → ℝ≥0∞ := fun s =>
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
      (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞))
  have hwp :
      OracleComp.ProgramLogic.wp
          ((simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0))
          (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞)) =
        ∑ s : S,
          Pr[= s | ((Unit →ₒ S).query () : OracleComp (Unit →ₒ S) S)] * Q s := by
    rw [run_simulateQ_hidingAvgComp_eq_bind, OracleComp.ProgramLogic.wp_bind,
      OracleComp.ProgramLogic.wp_eq_tsum, tsum_fintype]
    refine Finset.sum_congr rfl ?_
    intro s hs
    rw [OracleComp.ProgramLogic.wp_map, OracleComp.ProgramLogic.wp_liftComp]
    rfl
  have hcard0 : (Fintype.card S : ℝ≥0∞) ≠ 0 := by simp
  have hcard_top : (Fintype.card S : ℝ≥0∞) ≠ ∞ := by simp
  calc
    (Fintype.card S : ℝ≥0∞) *
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0))
          (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞))
      = (Fintype.card S : ℝ≥0∞) * ∑ s : S,
          Pr[= s | ((Unit →ₒ S).query () : OracleComp (Unit →ₒ S) S)] * Q s := by
            rw [hwp]
    _ = (Fintype.card S : ℝ≥0∞) * ∑ s : S,
          (Fintype.card S : ℝ≥0∞)⁻¹ * Q s := by
            simp_rw [probOutput_query]
    _ = ∑ s : S, (Fintype.card S : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞)⁻¹ * Q s) := by
          rw [Finset.mul_sum]
    _ = ∑ s : S, Q s := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          calc
            (Fintype.card S : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞)⁻¹ * Q s)
              = ((Fintype.card S : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞)⁻¹) * Q s := by
                  rw [mul_assoc]
            _ = 1 * Q s := by
                  rw [ENNReal.mul_inv_cancel hcard0 hcard_top]
            _ = Q s := by
                  rw [one_mul]
    _ = ∑ s : S,
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
            (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)) := by
          simp [Q]

variable [Fintype S] [Inhabited M] [Inhabited S] in
/-- Textbook outer bridge: the bad-mass sum is bounded by the per-salt
count-pred expectations from the shared counted implementation. -/
theorem sum_probEvent_hidingBad_le_sum_wp_countPred {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)]) ≤
    ∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)) := by
  calc
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)])
      =
        (Fintype.card S : ℝ≥0∞) *
          Pr[fun z : ((S × Bool) × HidingCountState M S C) => 2 ≤ z.2.2 z.1.1 |
            (simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0)] := by
              simpa using sum_probEvent_hidingBad_eq_avg_bad_mass (M := M) (S := S) (C := C) A
    _ ≤
        (Fintype.card S : ℝ≥0∞) *
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingAvgQueryImpl (hidingAvgComp A)).run (∅, fun _ => 0))
            (fun z : ((S × Bool) × HidingCountState M S C) => (z.2.2 z.1.1 - 1 : ℝ≥0∞)) := by
              exact mul_le_mul' le_rfl (probEvent_hidingAvg_bad_le_wp_selectedCountPred
                (M := M) (S := S) (C := C) A)
    _ =
        ∑ s : S,
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
            (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)) := by
              simpa using
                card_mul_wp_hidingAvg_selectedCountPred_eq_sum_wp_countPred
                  (M := M) (S := S) (C := C) A

/-- The real hiding game is `simulateQ cachingOracle` applied to the shared computation. -/
theorem hidingReal_eq {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    hidingReal A s = (simulateQ cachingOracle (hidingOa A s)).run' ∅ := by
  simp only [hidingReal, hidingOa]

/-- The real hiding game equals `simulateQ hidingImpl₁` projected to discard the counter.
This lifts cachingOracle's state by pairing it with the salt counter. -/
theorem hidingReal_eq_impl₁ {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    hidingReal A s = (simulateQ (hidingImpl₁ s) (hidingOa A s)).run' (∅, 0) := by
  rw [hidingReal_eq A s]
  exact (OracleComp.run'_simulateQ_eq_of_query_map_eq
    (hidingImpl₁ s) cachingOracle Prod.fst (fun ms st => by
      obtain ⟨cache, cnt⟩ := st
      simp only [hidingImpl₁, cachingOracle, QueryImpl.withCaching_apply,
        QueryImpl.ofLift, StateT.run_bind, StateT.run_get, pure_bind]
      cases hc : cache ms with
      | some u =>
        simp [StateT.run_pure, Prod.map]
      | none =>
        simp only [StateT.run_bind, OracleComp.liftM_run_StateT]
        simp only [monad_norm]
        simp [StateT.run_set, StateT.run_pure, Prod.map, StateT.run_modifyGet]
    ) (hidingOa A s) (∅, 0)).symm

variable [Inhabited M] [Inhabited S] in
/-- The implementations agree when `¬bad`: when the counter is less than 2,
`hidingImpl₁` and `hidingImpl₂` produce the same monadic computation.
The redirect condition `cnt ≥ 2 && salt = s` is `false` since `cnt < 2`. -/
theorem hidingImpl_agree (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) (h : ¬hidingBad st) :
    (hidingImpl₁ s ms).run st = (hidingImpl₂ s ms).run st := by
  simp only [hidingBad, ge_iff_le, not_le] at h
  obtain ⟨cache, cnt⟩ := st
  simp only at h
  simp only [hidingImpl₁, hidingImpl₂, StateT.run_bind, StateT.run_get, pure_bind]
  cases cache ms with
  | some u => rfl
  | none =>
    -- cnt < 2, so the redirect condition is false, making queryPoint = ms
    have hcnt : (if (decide (cnt ≥ 2) && (ms.2 == s)) = true then (default, default) else ms)
        = ms := by
      have : decide (cnt ≥ 2) = false := decide_eq_false (Nat.not_le.mpr h)
      simp [this]
    rw [hcnt]

omit [DecidableEq M] [DecidableEq S] [Fintype C] [Inhabited C] in
/-- `hidingBad` is upward-closed in the counter component. -/
private lemma hidingBad_of_counter_le
    {st₁ st₂ : QueryCache (CMOracle M S C) × ℕ}
    (h : hidingBad st₁) (hle : st₁.2 ≤ st₂.2) : hidingBad st₂ := by
  simp only [hidingBad] at h ⊢; omega

/-- One-step counter growth bound for `hidingImpl₁`:
the salt counter is monotone and increases by at most one. -/
theorem hidingImpl₁_counter_le_succ (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ)
    (x : C × (QueryCache (CMOracle M S C) × ℕ))
    (hx : x ∈ support ((hidingImpl₁ s ms).run st)) :
    st.2 ≤ x.2.2 ∧ x.2.2 ≤ st.2 + 1 := by
  obtain ⟨cache, cnt⟩ := st
  simp only [hidingImpl₁, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
    simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  | none =>
    simp only [hcache, StateT.run_bind] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨u, _, hx⟩ := hx
    simp only [StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    simp
    split <;> omega

/-- Bad is monotone for `hidingImpl₁`: once the counter reaches 2, it stays ≥ 2. -/
theorem hidingImpl₁_bad_mono (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) (h : hidingBad st)
    (x : C × (QueryCache (CMOracle M S C) × ℕ))
    (hx : x ∈ support ((hidingImpl₁ s ms).run st)) :
    hidingBad x.2 :=
  hidingBad_of_counter_le h (hidingImpl₁_counter_le_succ s ms st x hx).1

/-! ### Distributional agreement via `hidingImplSim`

The proof uses `hidingImplSim`, which redirects all salt-`s` cache misses to
`(default, default)`. The argument proceeds in three steps:
1. `hidingImpl₁` and `hidingImplSim` agree distributionally when `¬bad`
   (both return fresh uniform on cache miss; the query point is irrelevant
   because the underlying oracle is memoryless).
2. `hidingImplSim.run' = hidingSim` (the simulator matches the implementation).
3. `tvDist_simulateQ_le_probEvent_bad_dist` bounds the statistical distance
   by `Pr[bad]`.

The `Pr[bad] ≤ t/|S|` bound requires `s` to be uniformly random (see below). -/

variable [Inhabited M] [Inhabited S] in
/-- One-step counter growth bound for `hidingImplSim`:
the salt counter is monotone and increases by at most one. -/
theorem hidingImplSim_counter_le_succ (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ)
    (x : C × (QueryCache (CMOracle M S C) × ℕ))
    (hx : x ∈ support ((hidingImplSim s ms).run st)) :
    st.2 ≤ x.2.2 ∧ x.2.2 ≤ st.2 + 1 := by
  obtain ⟨cache, cnt⟩ := st
  simp only [hidingImplSim, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
    simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  | none =>
    simp only [hcache, StateT.run_bind] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨u, _, hx⟩ := hx
    simp only [StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    simp
    split <;> omega

variable [Inhabited M] [Inhabited S] in
/-- Bad is monotone for `hidingImplSim`: once cnt ≥ 2, it stays ≥ 2. -/
theorem hidingImplSim_bad_mono (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) (h : hidingBad st)
    (x : C × (QueryCache (CMOracle M S C) × ℕ))
    (hx : x ∈ support ((hidingImplSim s ms).run st)) :
    hidingBad x.2 :=
  hidingBad_of_counter_le h (hidingImplSim_counter_le_succ s ms st x hx).1

variable [Inhabited M] [Inhabited S] in
/-- `hidingImpl₁` and `hidingImplSim` agree **distributionally** when `¬bad`.

When `cnt < 2`, the two implementations differ only in the query point for
salt-s cache misses: `hidingImpl₁` queries at `ms`, while `hidingImplSim`
queries at `(default, default)`. Since the underlying oracle is memoryless
(`Pr[= u | query t₁] = Pr[= u | query t₂]` for all `u` when both ranges
are `C`), the returned value has the same distribution. The cache update and
counter increment are identical (both cache at `ms`, both increment when
`ms.2 = s`). Therefore every `(output, state)` pair has the same probability. -/
theorem hidingImpl_agree_dist (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) (h : ¬hidingBad st)
    (p : C × (QueryCache (CMOracle M S C) × ℕ)) :
    Pr[= p | (hidingImpl₁ s ms).run st] =
      Pr[= p | (hidingImplSim s ms).run st] := by
  obtain ⟨cache, cnt⟩ := st
  simp only [hidingBad, ge_iff_le, not_le] at h
  simp only [hidingImpl₁, hidingImplSim, StateT.run_bind, StateT.run_get, pure_bind]
  cases hcache : cache ms with
  | some u =>
    -- Cache hit: both return the same cached value, state unchanged
    simp
  | none =>
    -- Cache miss: impl₁ queries at ms, implSim queries at queryPoint.
    -- Both bind on (liftM (query _)).run st then set+return.
    -- The continuations are identical; only the query point differs.
    -- Since (liftM (query t)).run st = query t >>= pure (·, st),
    -- Pr[= (u, st') | ...] = Pr[= u | query t] · [st' = st],
    -- and Pr[= u | query t] = 1/|C| for any t, both factors match.
    simp only [StateT.run_bind]
    refine tsum_congr fun x => ?_
    congr 1

variable [Inhabited M] [Inhabited S] in
/-- The sim game equals `hidingImplSim` applied to `hidingOa`, projected to output.

This lifts `cachingOracle`'s state by pairing it with the salt counter and
shows that `hidingImplSim` acts as a state-projection of `cachingOracle` where
all salt-s queries are redirected. -/
theorem hidingSim_eq_implSim {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    hidingSim A s = (simulateQ (hidingImplSim s) (hidingOa A s)).run' (∅, 0) := by
  rfl

variable [Inhabited M] [Inhabited S] in
/-- For fixed `s`, the TV distance between real and sim games is bounded by
the probability of the bad event under `hidingImpl₁`.

The proof uses the distributional identical-until-bad lemma
(`tvDist_simulateQ_le_probEvent_bad_dist`): `hidingImpl₁` (real with counter) and
`hidingImplSim` (sim with counter) agree distributionally when `¬bad` because the
underlying oracle is memoryless. -/
theorem tvDist_hidingReal_hidingSim_le_probBad {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    tvDist (hidingReal A s) (hidingSim A s) ≤
    Pr[hidingBad ∘ Prod.snd |
        (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)].toReal := by
  rw [hidingReal_eq_impl₁ A s, hidingSim_eq_implSim A s]
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_bad_dist
    (hidingImpl₁ s) (hidingImplSim s) hidingBad (hidingOa A s) (∅, 0)
    (by simp [hidingBad])
    (fun ms st h p => hidingImpl_agree_dist s ms st h p)
    (hidingImpl₁_bad_mono s)
    (hidingImplSim_bad_mono s)

/-- Sum of `Pr[bad(s)]` over all salts is at most `t`.

The textbook (Claim cm-hiding-hit-query) samples `s` uniformly and independently
of the adversary's queries.  The per-query argument is:
- **Choose phase**: `A.choose` does not take `s` as input, so each choose-phase
  query `(m_i, s_i)` has `s_i` independent of the uniform `s`.
  Summing the indicator `[s_i = s]` over all `s ∈ S` gives exactly 1 per query.
- **Distinguish phase**: `A.distinguish aux cm` receives `cm = H(m, s)`, but under
  the caching oracle `cm` is a fresh uniform value independent of `s`.  By
  symmetry, each distinguish-phase query's salt hits any particular `s` with
  probability `1/|S|`, so the sum over all `s` is again 1 per query.
- The adversary makes at most `t` queries total, so `∑ s, Pr[bad(s)] ≤ t`.

The per-salt bound `Pr[bad(s)] ≤ t/|S|` does NOT hold for fixed `s` (a trivial
adversary always querying salt `s` gives `Pr[bad] = 1`).  The correct statement
is the sum/average version below.

**Proof strategy**: Swap the sum over `s` inside the probability, express
`∑_s Pr[bad(s)]` as `𝔼[#{adversary queries with salt = s}]`, then use linearity
of expectation and the per-query bound. -/
-- Pointwise arithmetic helper: event indicator is bounded by a natural count.
theorem indicator_le_natCast_count (P : Prop) [Decidable P] (n : ℕ)
    (h : P → 1 ≤ n) : (if P then (1 : ℝ≥0∞) else 0) ≤ n := by
  by_cases hP : P
  · simp [hP, h hP]
  · simp [hP]

omit [DecidableEq M] [DecidableEq S] in
lemma wp_finset_sum {α : Type}
    (oa : OracleComp (CMOracle M S C) α) (ss : Finset S) (f : S → α → ℝ≥0∞) :
    (ss.sum fun s => OracleComp.ProgramLogic.wp oa (f s)) =
      OracleComp.ProgramLogic.wp oa (fun z => ss.sum fun s => f s z) := by
  letI := Classical.decEq S
  refine Finset.induction_on ss ?_ ?_
  · simp
  · intro s ss hs ih
    simp [Finset.sum_insert, hs, ih, OracleComp.ProgramLogic.wp_add]

variable [Fintype S] in
lemma sum_wp_hidingOa_eq_wp_choose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    (post : S → Bool × HidingCountState M S C → ℝ≥0∞) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (post s)) =
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
      (fun qchoose : (M × AUX) × HidingCountState M S C =>
        ∑ s : S,
          OracleComp.ProgramLogic.wp
            ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
            (fun qch : C × HidingCountState M S C =>
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                (post s))) := by
  classical
  calc
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (post s))
      =
    ∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
        (fun qchoose : (M × AUX) × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
            (fun qch : C × HidingCountState M S C =>
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                (post s))) := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        simp [hidingOa, simulateQ_bind, StateT.run_bind, OracleComp.ProgramLogic.wp_bind]
    _ =
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
        (fun qchoose : (M × AUX) × HidingCountState M S C =>
          ∑ s : S,
            OracleComp.ProgramLogic.wp
              ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
              (fun qch : C × HidingCountState M S C =>
                OracleComp.ProgramLogic.wp
                  ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                  (post s))) := by
        simpa using
          (wp_finset_sum
            ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
            Finset.univ
            (fun s qchoose =>
              OracleComp.ProgramLogic.wp
                ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
                (fun qch : C × HidingCountState M S C =>
                  OracleComp.ProgramLogic.wp
                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                    (post s))))

variable [Fintype S] in
lemma sum_wp_countPred_eq_wp_choose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞))) =
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
        (fun qchoose : (M × AUX) × HidingCountState M S C =>
          ∑ s : S,
            OracleComp.ProgramLogic.wp
              ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
              (fun qch : C × HidingCountState M S C =>
                OracleComp.ProgramLogic.wp
                  ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                  (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)))) := by
  simpa using
    sum_wp_hidingOa_eq_wp_choose
      (M := M) (S := S) (C := C) A
      (fun s z => (z.2.2 s - 1 : ℝ≥0∞))

lemma wp_challenge_countPred_le_initialCount
    (m : M) (s : S) (st : HidingCountState M S C) :
    OracleComp.ProgramLogic.wp
      ((hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st)
      (fun qch : C × HidingCountState M S C => (qch.2.2 s - 1 : ℝ≥0∞)) ≤ st.2 s := by
  rw [OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' qch,
        Pr[= qch |
          (hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st] *
          (qch.2.2 s - 1 : ℝ≥0∞)
      ≤
        ∑' qch,
          Pr[= qch |
            (hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st] * st.2 s := by
            refine ENNReal.tsum_le_tsum fun qch => ?_
            by_cases hqch :
                qch ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st)
            · exact mul_le_mul'
                le_rfl
                (by
                  exact_mod_cast
                    (challenge_countPred_le_initialCount_of_mem_support_step_hidingImplCountAll
                      (M := M) (S := S) (C := C) m s st hqch))
            · rw [probOutput_eq_zero_of_not_mem_support hqch]
              simp
    _ = st.2 s := by
        rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

variable [Fintype S] in
lemma sum_wp_challenge_countPred_le_initialCount
    (m : M) (st : HidingCountState M S C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st)
        (fun qch : C × HidingCountState M S C => (qch.2.2 s - 1 : ℝ≥0∞))) ≤
      (∑ s : S, st.2 s : ℝ≥0∞) := by
  refine Finset.sum_le_sum ?_
  intro s hs
  exact wp_challenge_countPred_le_initialCount (M := M) (S := S) (C := C) m s st

variable [Fintype S] [Inhabited S] in
lemma sum_wp_distinguish_countPred_le_sum_initialPred_add_residual
    {AUX : Type} {t : ℕ} [Finite M]
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (cm : C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞))) ≤
      (∑ s : S, (qchoose.2.2 s - 1 : ℝ≥0∞)) + (t - ∑ s : S, qchoose.2.2 s) := by
  haveI := Fintype.ofFinite M
  have hsplit :=
    sum_wp_countPred_le_sum_initialPred_add_sum_wp_countIncrements
      (M := M) (S := S) (C := C)
      (oa := A.distinguish qchoose.1.2 cm)
      (st₀ := qchoose.2)
  have hbound :
      IsTotalQueryBound (A.distinguish qchoose.1.2 cm) (t - ∑ s : S, qchoose.2.2 s) :=
    hiding_distinguish_totalBound_of_choose_count_support
      (M := M) (S := S) (C := C) A hqchoose cm
  have hincr :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
          (fun z : Bool × HidingCountState M S C => (z.2.2 s - qchoose.2.2 s : ℝ≥0∞))) ≤
        (t - ∑ s : S, qchoose.2.2 s) := by
    simpa using
      (sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll
        (M := M) (S := S) (C := C)
        (oa := A.distinguish qchoose.1.2 cm)
        (n := t - ∑ s : S, qchoose.2.2 s)
        hbound qchoose.2)
  exact le_trans hsplit (by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_left hincr (∑ s : S, (qchoose.2.2 s - 1 : ℝ≥0∞)))

variable [Fintype S] in
lemma sum_wp_countPred_le_sum_initialPred_add_queryBound_of_run_hidingImplCountAll
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (st₀ : HidingCountState M S C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞))) ≤
      (∑ s : S, (st₀.2 s - 1 : ℝ≥0∞)) + n := by
  have hsplit :=
    sum_wp_countPred_le_sum_initialPred_add_sum_wp_countIncrements
      (M := M) (S := S) (C := C) oa st₀
  have hincr :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll oa).run st₀)
          (fun z : α × HidingCountState M S C => (z.2.2 s - st₀.2 s : ℝ≥0∞))) ≤ n := by
    simpa using
      (sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll
        (M := M) (S := S) (C := C) (oa := oa) (n := n) hbound st₀)
  exact le_trans hsplit (by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_left hincr (∑ s : S, (st₀.2 s - 1 : ℝ≥0∞)))

variable [Fintype S] [Inhabited S] in
lemma sum_wp_distinguish_countPred_le_queryBound_of_choose_count_support
    {AUX : Type} {t : ℕ} [Finite M]
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (cm : C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞))) ≤ t := by
  haveI := Fintype.ofFinite M
  have hsplit :=
    sum_wp_distinguish_countPred_le_sum_initialPred_add_residual
      (M := M) (S := S) (C := C) A hqchoose cm
  rcases
      exists_counting_support_of_mem_support_run_hidingImplCountAll_coord
        (M := M) (S := S) (C := C)
        (oa := A.choose)
        (st₀ := ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0))
        (z := qchoose)
        hqchoose with
    ⟨qcChoose, hqcChoose, hcoordChoose⟩
  have hchooseCounts :
      (∑ s : S, qchoose.2.2 s) ≤ t := by
    have hcoordSum :
        (∑ s : S, qchoose.2.2 s) ≤ ∑ s : S, ∑ m : M, qcChoose (m, s) := by
      refine Finset.sum_le_sum ?_
      intro s hs
      simpa using hcoordChoose s
    have htotal :
        (∑ ms : M × S, qcChoose ms) ≤ t := by
      exact IsTotalQueryBound.counting_total_le
        (spec := CMOracle M S C)
        (ι := M × S)
        (oa := A.choose)
        (n := t)
        (h := hiding_choose_totalBound (M := M) (S := S) (C := C) A)
        hqcChoose
    have hswap :
        (∑ s : S, ∑ m : M, qcChoose (m, s)) = ∑ ms : M × S, qcChoose ms := by
      calc
        (∑ s : S, ∑ m : M, qcChoose (m, s)) = ∑ m : M, ∑ s : S, qcChoose (m, s) := by
          simpa using (Finset.sum_comm : (∑ s : S, ∑ m : M, qcChoose (m, s)) =
            ∑ m : M, ∑ s : S, qcChoose (m, s))
        _ = ∑ ms : M × S, qcChoose ms := by
          symm
          simp [Fintype.sum_prod_type]
    exact le_trans hcoordSum (by simpa [hswap] using htotal)
  have hpred :
      (∑ s : S, (qchoose.2.2 s - 1 : ℝ≥0∞)) ≤ (∑ s : S, qchoose.2.2 s : ℝ≥0∞) := by
    refine Finset.sum_le_sum ?_
    intro s hs
    exact_mod_cast (Nat.sub_le (qchoose.2.2 s) 1)
  calc
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
        (fun z : Bool × HidingCountState M S C => (z.2.2 s - 1 : ℝ≥0∞)))
      ≤ (∑ s : S, (qchoose.2.2 s - 1 : ℝ≥0∞)) + (t - ∑ s : S, qchoose.2.2 s) := hsplit
    _ ≤ (∑ s : S, qchoose.2.2 s : ℝ≥0∞) + (t - ∑ s : S, qchoose.2.2 s) := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_right hpred (t - ∑ s : S, qchoose.2.2 s)
    _ = t := by
        have hcast : (∑ s : S, qchoose.2.2 s : ℝ≥0∞) ≤ t := by
          exact_mod_cast hchooseCounts
        rw [add_comm]
        rw [Nat.cast_sum]
        exact tsub_add_cancel_of_le hcast

variable [Fintype S] [Inhabited S] in
lemma sum_wp_distinguish_incrementIndicators_le_queryResidual_of_choose_count_support
    {AUX : Type} {t : ℕ} [Finite M]
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (cm : C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
        (fun z : Bool × HidingCountState M S C =>
          OracleComp.ProgramLogic.propInd (qchoose.2.2 s < z.2.2 s))) ≤
      (t - ∑ s : S, qchoose.2.2 s) := by
  haveI := Fintype.ofFinite M
  have hbound :
      IsTotalQueryBound (A.distinguish qchoose.1.2 cm) (t - ∑ s : S, qchoose.2.2 s) :=
    hiding_distinguish_totalBound_of_choose_count_support
      (M := M) (S := S) (C := C) A hqchoose cm
  have hres :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
          (fun z : Bool × HidingCountState M S C => (z.2.2 s - qchoose.2.2 s : ℝ≥0∞))) ≤
        (t - ∑ s : S, qchoose.2.2 s) := by
    simpa using
      (sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll
        (M := M) (S := S) (C := C)
        (oa := A.distinguish qchoose.1.2 cm)
        (n := t - ∑ s : S, qchoose.2.2 s)
        hbound qchoose.2)
  have hmono :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
          (fun z : Bool × HidingCountState M S C =>
            OracleComp.ProgramLogic.propInd (qchoose.2.2 s < z.2.2 s))) ≤
        (∑ s : S,
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2)
            (fun z : Bool × HidingCountState M S C => (z.2.2 s - qchoose.2.2 s : ℝ≥0∞))) := by
    refine Finset.sum_le_sum ?_
    intro s hs
    refine OracleComp.ProgramLogic.wp_mono
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qchoose.2) ?_
    intro z
    by_cases hslt : qchoose.2.2 s < z.2.2 s
    · simp only [OracleComp.ProgramLogic.propInd, if_pos hslt]
      exact_mod_cast (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hslt))
    · simp [OracleComp.ProgramLogic.propInd, hslt]
  exact le_trans hmono hres

variable [Fintype S] in
lemma sum_wp_badIndicator_eq_wp_choose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)]) =
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
      (fun qchoose : (M × AUX) × HidingCountState M S C =>
        ∑ s : S,
          OracleComp.ProgramLogic.wp
            ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
            (fun qch : C × HidingCountState M S C =>
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                (fun z : Bool × HidingCountState M S C =>
                  OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)))) := by
  classical
  calc
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)])
      =
    ∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
        (fun z : Bool × HidingCountState M S C =>
          OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)) := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        rw [probEvent_hidingBad_eq_countAll (M := M) (S := S) (C := C) A s,
          OracleComp.ProgramLogic.probEvent_eq_wp_propInd]
    _ =
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
        (fun qchoose : (M × AUX) × HidingCountState M S C =>
          ∑ s : S,
            OracleComp.ProgramLogic.wp
              ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
              (fun qch : C × HidingCountState M S C =>
                OracleComp.ProgramLogic.wp
                  ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                  (fun z : Bool × HidingCountState M S C =>
                    OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)))) := by
        simpa using
          sum_wp_hidingOa_eq_wp_choose
            (M := M) (S := S) (C := C) A
            (fun s z => OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s))

variable [Fintype S] in
lemma wp_badIndicator_le_chooseHit_add_distinguishIncrement_of_choose_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
        (fun qch : C × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)))) ≤
    ∑ s : S,
      (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.wp
          ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
          (fun qch : C × HidingCountState M S C =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s)))) := by
  refine Finset.sum_le_sum ?_
  intro s hs
  rw [OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' qch,
        Pr[= qch |
          (hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2] *
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s))
      ≤
        ∑' qch,
          Pr[= qch |
            (hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2] *
            (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                (fun z : Bool × HidingCountState M S C =>
                  OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s))) := by
            refine ENNReal.tsum_le_tsum ?_
            intro qch
            by_cases hqch :
                qch ∈ support
                  ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
            · have hinner :
                  OracleComp.ProgramLogic.wp
                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                    (fun z : Bool × HidingCountState M S C =>
                      OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s))
                  ≤
                    OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                      OracleComp.ProgramLogic.wp
                        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                        (fun z : Bool × HidingCountState M S C =>
                          OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s)) := by
                rw [OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
                calc
                  ∑' z,
                      Pr[= z |
                        (simulateQ hidingImplCountAll
                          (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                        OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)
                    ≤
                      ∑' z,
                        Pr[= z |
                          (simulateQ hidingImplCountAll
                            (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                          (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                            OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s)) := by
                              refine ENNReal.tsum_le_tsum ?_
                              intro z
                              by_cases hz :
                                  z ∈ support
                                    ((simulateQ hidingImplCountAll
                                      (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                              · exact (mul_le_mul' le_rfl
                              (bad_indicator_le_chooseHitIndicator_add_distinguishIncrementIndicator
                                (M := M) (S := S) (C := C) A hqchoose s hqch hz))
                              · rw [probOutput_eq_zero_of_not_mem_support hz]
                                simp
                  _ =
                    OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                      ∑' z,
                        Pr[= z |
                          (simulateQ hidingImplCountAll
                            (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                          OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s) := by
                            simp_rw [mul_add]
                            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
                              tsum_probOutput_of_liftM_PMF, one_mul]
              exact mul_le_mul' le_rfl hinner
            · rw [probOutput_eq_zero_of_not_mem_support hqch]
              simp
    _ =
      OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.wp
          ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
          (fun qch : C × HidingCountState M S C =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s))) := by
        rw [OracleComp.ProgramLogic.wp_eq_tsum]
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
          tsum_probOutput_of_liftM_PMF, one_mul]

variable [Fintype S] in
lemma wp_badIndicator_le_chooseHit_add_freshDistinguishIncrement_of_choose_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
        (fun qch : C × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)))) ≤
    ∑ s : S,
      (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.wp
          ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
          (fun qch : C × HidingCountState M S C =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd
                  (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))) := by
  refine Finset.sum_le_sum ?_
  intro s hs
  rw [OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' qch,
        Pr[= qch |
          (hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2] *
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s))
      ≤
        ∑' qch,
          Pr[= qch |
            (hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2] *
            (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                (fun z : Bool × HidingCountState M S C =>
                  OracleComp.ProgramLogic.propInd
                    (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))) := by
            refine ENNReal.tsum_le_tsum ?_
            intro qch
            by_cases hqch :
                qch ∈ support
                  ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
            · have hinner :
                  OracleComp.ProgramLogic.wp
                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                    (fun z : Bool × HidingCountState M S C =>
                      OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s))
                  ≤
                    OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                      OracleComp.ProgramLogic.wp
                        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                        (fun z : Bool × HidingCountState M S C =>
                          OracleComp.ProgramLogic.propInd
                            (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)) := by
                rw [OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
                calc
                  ∑' z,
                      Pr[= z |
                        (simulateQ hidingImplCountAll
                          (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                        OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s)
                    ≤
                      ∑' z,
                        Pr[= z |
                          (simulateQ hidingImplCountAll
                            (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                          (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                            OracleComp.ProgramLogic.propInd
                              (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)) := by
                              refine ENNReal.tsum_le_tsum ?_
                              intro z
                              by_cases hz :
                                  z ∈ support
                                    ((simulateQ hidingImplCountAll
                                      (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                              · exact (mul_le_mul' le_rfl
                        (bad_indicator_le_chooseHitIndicator_add_freshDistinguishIncrementIndicator
                          (M := M) (S := S) (C := C) A hqchoose s hqch hz))
                              · rw [probOutput_eq_zero_of_not_mem_support hz]
                                simp
                  _ =
                    OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                      ∑' z,
                        Pr[= z |
                          (simulateQ hidingImplCountAll
                            (A.distinguish qchoose.1.2 qch.1)).run qch.2] *
                          OracleComp.ProgramLogic.propInd
                            (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s) := by
                            simp_rw [mul_add]
                            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
                              tsum_probOutput_of_liftM_PMF, one_mul]
              exact mul_le_mul' le_rfl hinner
            · rw [probOutput_eq_zero_of_not_mem_support hqch]
              simp
    _ =
      OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.wp
          ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
          (fun qch : C × HidingCountState M S C =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd
                  (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))) := by
        rw [OracleComp.ProgramLogic.wp_eq_tsum]
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
          tsum_probOutput_of_liftM_PMF, one_mul]

omit [DecidableEq S] in
lemma sum_chooseHitIndicators_le_sumCounts [Fintype S]
    (counts : S → ℕ) :
    (∑ s : S, OracleComp.ProgramLogic.propInd (0 < counts s)) ≤
      (∑ s : S, counts s : ℝ≥0∞) := by
  refine Finset.sum_le_sum ?_
  intro s hs
  by_cases hpos : 0 < counts s
  · simp only [OracleComp.ProgramLogic.propInd, if_pos hpos]
    exact_mod_cast hpos
  · simp [OracleComp.ProgramLogic.propInd, hpos]

variable [Fintype S] in
lemma sum_wp_freshDistinguishIncrement_eq_query
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
        (fun qch : C × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd
                (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))) =
      ∑ s : S,
        OracleComp.ProgramLogic.propInd (qchoose.2.2 s = 0) *
          OracleComp.ProgramLogic.wp
            ((CMOracle M S C).query (qchoose.1.1, s) :
              OracleComp (CMOracle M S C) C)
            (fun cm =>
              OracleComp.ProgramLogic.wp
                ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run
                  (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
                    Function.update qchoose.2.2 s 1))
                (fun z : Bool × HidingCountState M S C =>
                  OracleComp.ProgramLogic.propInd (1 < z.2.2 s))) := by
  refine Finset.sum_congr rfl ?_
  intro s hs
  exact wp_freshDistinguishIncrement_eq
    (M := M) (S := S) (C := C) A hqchoose s
