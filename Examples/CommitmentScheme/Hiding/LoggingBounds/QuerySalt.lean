/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import Examples.CommitmentScheme.Hiding.LoggingBounds.Average

/-!
# Query-Salt Logging Bounds

Bounds on the probability that the adversary's salt-specific query count
exceeds a threshold, obtained via counting-oracle projections and
indicator function analysis. These feed into the averaged hiding bound.
-/

open OracleSpec OracleComp ENNReal

variable {M S C : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C]

omit [DecidableEq C] [Fintype M] [Inhabited M] in
lemma wp_choose_sumHitIndicators_le_queryBound
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
      (fun qchoose : (M × AUX) × HidingCountState M S C =>
        ∑ s : S, OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s)) ≤ t := by
  refine le_trans
    (OracleComp.ProgramLogic.wp_mono
      ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
      (fun qchoose =>
        sum_chooseHitIndicators_le_sumCounts qchoose.2.2))
    (wp_choose_sumCounts_le_queryBound (M := M) (S := S) (C := C) A)

omit [DecidableEq M] [DecidableEq S] [DecidableEq C] [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C] in
lemma run_simulateQ_loggingOracle_query_bind {α : Type}
    (t : (CMOracle M S C).Domain) (mx : (CMOracle M S C).Range t → OracleComp (CMOracle M S C) α) :
    (simulateQ loggingOracle (liftM (query t) >>= mx)).run =
      (query t : OracleComp (CMOracle M S C) _) >>= fun u =>
        (fun p : α × QueryLog (CMOracle M S C) =>
          (p.1, (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2))
          <$> (simulateQ loggingOracle (mx u)).run := by
  simp [loggingOracle, QueryImpl.withLogging, OracleQuery.cont_query,
    Prod.map, Function.id_def]

omit [DecidableEq M] [DecidableEq C] [Fintype M] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma sum_querySaltCounts_eq_length
    (log : QueryLog (CMOracle M S C)) :
    (∑ s : S,
      QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s)) = log.length := by
  classical
  induction log with
  | nil =>
      simp [QueryLog.countQ]
  | cons entry log ih =>
      have hcount : ∀ s : S,
          QueryLog.countQ (entry :: log) (fun t : (CMOracle M S C).Domain => t.2 = s) =
            (if s = entry.1.2 then 1 else 0) +
              QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s) := by
        intro s
        by_cases h : s = entry.1.2
        · simpa [h, Nat.add_comm] using
            (show
              QueryLog.countQ (entry :: log) (fun t : (CMOracle M S C).Domain => t.2 = s) =
                (QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s) + 1) by
              simp [QueryLog.countQ, QueryLog.getQ_cons, h])
        · have h' : ¬ entry.1.2 = s := by simpa [eq_comm] using h
          simp [QueryLog.countQ, QueryLog.getQ_cons, h, h']
      calc
        (∑ s : S,
          QueryLog.countQ (entry :: log) (fun t : (CMOracle M S C).Domain => t.2 = s))
            = ∑ s : S,
                ((if s = entry.1.2 then 1 else 0) +
                  QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s)) := by
                refine Finset.sum_congr rfl ?_
                intro s hs
                exact hcount s
        _ = (∑ s : S, (if s = entry.1.2 then 1 else 0)) +
              (∑ s : S, QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s)) := by
                rw [Finset.sum_add_distrib]
        _ = (1 : ℕ) + (∑ s : S,
              QueryLog.countQ log
                (fun t : (CMOracle M S C).Domain => t.2 = s)) := by
              have hsingle : (∑ s : S, (if s = entry.1.2 then 1 else 0 : ℕ)) = 1 := by
                simp
              rw [hsingle]
        _ = log.length + 1 := by rw [ih, Nat.add_comm]

omit [DecidableEq M] [DecidableEq C] [Fintype M] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma sum_querySaltIndicators_le_logLength
    (log : QueryLog (CMOracle M S C)) :
    (∑ s : S,
      OracleComp.ProgramLogic.propInd
        (0 < QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s))) ≤ log.length := by
  have hcounts :
      (∑ s : S,
        QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s) : ℝ≥0∞) = log.length := by
    exact_mod_cast sum_querySaltCounts_eq_length (M := M) (S := S) (C := C) log
  refine le_trans
    (sum_chooseHitIndicators_le_sumCounts
      (counts := fun s => QueryLog.countQ log (fun t : (CMOracle M S C).Domain => t.2 = s))) ?_
  exact le_of_eq hcounts

omit [DecidableEq C] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
lemma log_length_le_of_mem_support_counting_simulate_run_logging
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {z : (α × QueryLog (CMOracle M S C)) × QueryCount (M × S)}
    (hz : z ∈ support (countingOracle.simulate ((simulateQ loggingOracle oa).run) 0)) :
    z.1.2.length ≤ ∑ ms : M × S, z.2 ms := by
  induction oa using OracleComp.inductionOn generalizing z with
  | pure x =>
      have hz' :
          z ∈ support
            (countingOracle.simulate (spec := CMOracle M S C) (ι := M × S)
              (pure (x, ([] : QueryLog (CMOracle M S C)))) 0) := by
        simpa [simulateQ_pure] using hz
      rw [countingOracle.mem_support_simulate_pure_iff
        (spec := CMOracle M S C) (ι := M × S)] at hz'
      subst z
      simp
  | query_bind t mx ih =>
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind] at hz
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hz0, u, hz⟩ := hz
      have hmap :
          countingOracle.simulate
            (((fun p : α × QueryLog (CMOracle M S C) =>
                (p.1, (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) ::
                  p.2)) <$> (simulateQ loggingOracle (mx u)).run)) 0 =
            (fun zz : (α × QueryLog (CMOracle M S C)) × QueryCount (M × S) =>
              ((zz.1.1,
                  (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) ::
                    zz.1.2), zz.2)) <$>
              countingOracle.simulate ((simulateQ loggingOracle (mx u)).run) 0 := by
        simp [countingOracle.simulate, Prod.map, simulateQ_map]
      rw [hmap, support_map] at hz
      obtain ⟨w, hzu, hzEq⟩ := hz
      rcases w with ⟨⟨zu, logu⟩, qcu⟩
      have hz1 :
          (zu,
            (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: logu) = z.1 := by
        simpa using congrArg Prod.fst hzEq
      have hzlog :
          (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: logu = z.1.2 := by
        simpa using congrArg Prod.snd hz1
      have hzqc : qcu = Function.update z.2 t (z.2 t - 1) := by
        simpa using congrArg Prod.snd hzEq
      have hlen : logu.length ≤ ∑ ms : M × S, qcu ms :=
        ih u (z := ((zu, logu), qcu)) hzu
      have hsum :
          ∑ ms : M × S, Function.update z.2 t (z.2 t - 1) ms = (∑ ms : M × S, z.2 ms) - 1 := by
        let qpred : QueryCount (M × S) := Function.update z.2 t (z.2 t - 1)
        have hpredsucc : Function.update qpred t (qpred t + 1) = z.2 := by
          funext j
          by_cases hj : j = t
          · subst hj
            simp [qpred]
            omega
          · simp [qpred, Function.update, hj]
        have hsumsucc := sum_update_succ_count (counts := qpred) t
        rw [hpredsucc] at hsumsucc
        dsimp [qpred] at hsumsucc
        omega
      rw [hzqc, hsum] at hlen
      have hsumpos : 0 < ∑ ms : M × S, z.2 ms := by
        exact Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hz0)
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
      have hcons :
          ((⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: logu).length
            ≤ ∑ ms : M × S, z.2 ms := by
        have hlt : logu.length < ∑ ms : M × S, z.2 ms := by
          exact lt_of_le_of_lt hlen (Nat.sub_lt hsumpos (by simp))
        simpa using Nat.succ_le_of_lt hlt
      simpa [hzlog] using hcons

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] in
lemma log_length_le_of_mem_support_run_cached_logging
    [Finite M] [Finite S] [Finite C]
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (cache₀ : QueryCache (CMOracle M S C))
    {z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C)}
    (hz : z ∈ support
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)) :
    z.1.2.length ≤ n := by
  haveI : Fintype M := Fintype.ofFinite M
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fintype C := Fintype.ofFinite C
  classical
  let cost : QueryCache (CMOracle M S C) → ℕ := fun _ => 0
  have hstep :
      ∀ t : (CMOracle M S C).Domain, ∀ st : QueryCache (CMOracle M S C),
        ∀ x : (CMOracle M S C).Range t × QueryCache (CMOracle M S C),
          x ∈ support ((cachingOracle (spec := CMOracle M S C) t).run st) →
            cost x.2 ≤ cost st + 1 := by
    intro t st x hx
    simp [cost]
  rcases countingOracle.exists_mem_support_simulate_of_mem_support_run_simulateQ_le_cost
      (spec := CMOracle M S C)
      (ι := M × S)
      (impl := cachingOracle)
      cost hstep hz with ⟨qc, hqc, _⟩
  have hlen :
      z.1.2.length ≤ ∑ ms : M × S, qc ms :=
    log_length_le_of_mem_support_counting_simulate_run_logging
      (M := M) (S := S) (C := C) oa hqc
  have hboundLog :
      IsTotalQueryBound ((simulateQ loggingOracle oa).run) n :=
    (isTotalQueryBound_run_simulateQ_loggingOracle_iff
      (spec := CMOracle M S C) oa n).2 hbound
  have hqc_le : (∑ ms : M × S, qc ms) ≤ n :=
    IsTotalQueryBound.counting_total_le
      (spec := CMOracle M S C)
      (ι := M × S)
      (oa := (simulateQ loggingOracle oa).run)
      (n := n)
      hboundLog hqc
  exact le_trans hlen hqc_le

omit [DecidableEq C] [Fintype M] [Inhabited M] [Inhabited S] in
lemma sum_wp_querySaltIndicators_le_queryBound_of_run_cached_logging
    [Finite M]
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (cache₀ : QueryCache (CMOracle M S C))
    (hbound : IsTotalQueryBound oa n) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)
        (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          OracleComp.ProgramLogic.propInd
            (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))) ≤ n := by
  haveI : Fintype M := Fintype.ofFinite M
  classical
  have hsum :=
    wp_finset_sum
      (M := M) (S := S) (C := C)
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)
      Finset.univ
      (fun s z =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))
  rw [hsum, OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' z,
        Pr[= z | (simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀] *
          (∑ s : S,
            OracleComp.ProgramLogic.propInd
              (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))
      ≤
        ∑' z,
          Pr[= z | (simulateQ cachingOracle
            ((simulateQ loggingOracle oa).run)).run cache₀] * n := by
            refine ENNReal.tsum_le_tsum ?_
            intro z
            by_cases hz :
                z ∈ support
                  ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)
            · exact mul_le_mul'
                le_rfl
                (le_trans
                  (sum_querySaltIndicators_le_logLength (M := M) (S := S) (C := C) z.1.2)
                  (by
                    exact_mod_cast
                      (log_length_le_of_mem_support_run_cached_logging
                        (M := M) (S := S) (C := C)
                        (oa := oa) (n := n) hbound cache₀ hz)))
            · rw [probOutput_eq_zero_of_not_mem_support hz]
              simp
    _ = (n : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

omit [DecidableEq C] [Fintype M] [Inhabited M] in
lemma sum_wp_distinguish_incrementIndicators_le_queryResidual_of_choose_count_support_with_state
    [Finite M]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (cm : C) (qch : C × HidingCountState M S C) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qch.2)
        (fun z : Bool × HidingCountState M S C =>
          OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s))) ≤
      (t - ∑ s : S, qchoose.2.2 s) := by
  haveI : Fintype M := Fintype.ofFinite M
  have hbound :
      IsTotalQueryBound (A.distinguish qchoose.1.2 cm) (t - ∑ s : S, qchoose.2.2 s) :=
    hiding_distinguish_totalBound_of_choose_count_support
      (M := M) (S := S) (C := C) A hqchoose cm
  have hres :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qch.2)
          (fun z : Bool × HidingCountState M S C =>
            (z.2.2 s - qch.2.2 s : ℝ≥0∞))) ≤
        (t - ∑ s : S, qchoose.2.2 s) := by
    simpa using
      (sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll
        (M := M) (S := S) (C := C)
        (oa := A.distinguish qchoose.1.2 cm)
        (n := t - ∑ s : S, qchoose.2.2 s)
        hbound qch.2)
  have hmono :
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qch.2)
          (fun z : Bool × HidingCountState M S C =>
            OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s))) ≤
        (∑ s : S,
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              (z.2.2 s - qch.2.2 s : ℝ≥0∞))) := by
    refine Finset.sum_le_sum ?_
    intro s hs
    refine OracleComp.ProgramLogic.wp_mono
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run qch.2) ?_
    intro z
    by_cases hslt : qch.2.2 s < z.2.2 s
    · simp [OracleComp.ProgramLogic.propInd, hslt]
      have hsub : 1 ≤ (z.2.2 s - qch.2.2 s : ℕ) := by
        omega
      have hcast : (1 : ℝ≥0∞) ≤ (z.2.2 s - qch.2.2 s : ℝ≥0∞) := by
        exact_mod_cast hsub
      simpa using hcast
    · simp [OracleComp.ProgramLogic.propInd, hslt]
  exact le_trans hmono hres

omit [DecidableEq M] [DecidableEq C] [Fintype M] [Inhabited M] [Inhabited S] in
lemma sum_wp_querySaltIndicators_le_queryBound_of_run_logging
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ loggingOracle oa).run)
        (fun z : α × QueryLog (CMOracle M S C) =>
          OracleComp.ProgramLogic.propInd
            (0 < QueryLog.countQ z.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))) ≤ n := by
  classical
  have hsum :=
    wp_finset_sum
      (M := M) (S := S) (C := C)
      ((simulateQ loggingOracle oa).run)
      Finset.univ
      (fun s z =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))
  rw [hsum, OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' z,
        Pr[= z | (simulateQ loggingOracle oa).run] *
          (∑ s : S,
            OracleComp.ProgramLogic.propInd
              (0 < QueryLog.countQ z.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))
      ≤
        ∑' z, Pr[= z | (simulateQ loggingOracle oa).run] * n := by
          refine ENNReal.tsum_le_tsum ?_
          intro z
          by_cases hz : z ∈ support ((simulateQ loggingOracle oa).run)
          · exact mul_le_mul'
              le_rfl
              (le_trans
                (sum_querySaltIndicators_le_logLength (M := M) (S := S) (C := C) z.2)
                (by
                  exact_mod_cast
                    (log_length_le_of_mem_support_run_simulateQ
                      (spec := CMOracle M S C)
                      (oa := oa) (n := n) hbound hz)))
          · rw [probOutput_eq_zero_of_not_mem_support hz]
            simp
    _ = (n : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
theorem run_cached_logging_proj_eq_cachingOracle
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (cache₀ : QueryCache (CMOracle M S C)) :
    Prod.map Prod.fst id <$>
        (simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀ =
      (simulateQ cachingOracle oa).run cache₀ := by
  induction oa using OracleComp.inductionOn generalizing cache₀ with
  | pure x =>
      simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind]
      rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
      cases ht : cache₀ t with
      | some u =>
          simp [ht, StateT.run_bind, StateT.run_get, pure_bind]
          simpa [simulateQ_map, StateT.map, StateT.run, Function.comp_def] using ih u cache₀
      | none =>
          simp only [OracleQuery.input_query, QueryImpl.withCaching_apply,
            QueryImpl.ofLift_apply, monadLift_self, StateT.run_bind,
            StateT.run_get, pure_bind, ht, StateT.run_monadLift,
            bind_pure_comp, StateT.run_modifyGet, Functor.map_map,
            id_eq, simulateQ_map, StateT.run_map,
            bind_map_left, map_bind, Prod.map_apply]
          refine bind_congr ?_
          intro u
          simpa [simulateQ_map, StateT.map, StateT.run, Function.comp_def] using
            ih u (cache₀.cacheQuery t u)

omit [DecidableEq M] [DecidableEq S] [DecidableEq C] [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C] in
lemma queryLog_countQ_pos_of_mem
    {entry : (t : (CMOracle M S C).Domain) × (CMOracle M S C).Range t}
    {log : QueryLog (CMOracle M S C)}
    {p : (CMOracle M S C).Domain → Prop} [DecidablePred p]
    (hmem : entry ∈ log) (hp : p entry.1) :
    0 < QueryLog.countQ log p := by
  induction log with
  | nil =>
      cases hmem
  | cons hd tl ih =>
      simp only [List.mem_cons, QueryLog.countQ, QueryLog.getQ_cons] at hmem ⊢
      rcases hmem with rfl | hmem
      · simp [hp]
      · by_cases hhd : p hd.1
        · simp [hhd]
        · simp only [hhd, ↓reduceIte]
          exact ih hmem

omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
lemma fresh_incrementIndicator_le_querySaltIndicator_cached_logging
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    (hzero : qchoose.2.2 s = 0)
    (cm : C) :
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run
        (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm, Function.update qchoose.2.2 s 1))
      (fun z : Bool × HidingCountState M S C =>
        OracleComp.ProgramLogic.propInd (1 < z.2.2 s))
    ≤
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run
        (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm))
      (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))) := by
  let freshCache : QueryCache (CMOracle M S C) :=
    qchoose.2.1.cacheQuery (qchoose.1.1, s) cm
  let freshState : HidingCountState M S C :=
    (freshCache, Function.update qchoose.2.2 s 1)
  let oa := A.distinguish qchoose.1.2 cm
  let countRun := ((simulateQ hidingImplCountAll oa).run freshState)
  let cacheRun := ((simulateQ cachingOracle oa).run freshCache)
  let cachedLogRun :=
    ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run freshCache)
  let cacheEvent : Bool × QueryCache (CMOracle M S C) → Prop :=
    fun z => ∃ m : M, ∃ v : C, m ≠ qchoose.1.1 ∧ z.2 (m, s) = some v
  rw [← OracleComp.ProgramLogic.probEvent_eq_wp_propInd,
    ← OracleComp.ProgramLogic.probEvent_eq_wp_propInd]
  have hcount_to_cache :
      Pr[fun z : Bool × HidingCountState M S C => 1 < z.2.2 s | countRun] ≤
        Pr[cacheEvent | cacheRun] := by
    dsimp [countRun, cacheRun]
    rw [← run_hidingImplCountAll_proj_eq_cachingOracle
      (M := M) (S := S) (C := C) oa freshState]
    rw [probEvent_map]
    refine probEvent_mono ?_
    intro z hz hgt
    have hcount1 : (Function.update qchoose.2.2 s 1) s = 1 := by
      simp [Function.update]
    have hself1 : ∃ v : C, freshCache (qchoose.1.1, s) = some v := by
      refine ⟨cm, ?_⟩
      simp [freshCache]
    have hunique1 : ∀ m : M, m ≠ qchoose.1.1 → freshCache (m, s) = none := by
      intro m hm
      have hnone :
          qchoose.2.1 (m, s) = none :=
        cache_none_of_zero_count_of_mem_support_run_hidingChoose
          (M := M) (S := S) (C := C) A hqchoose m s hzero
      have hne : (m, s) ≠ (qchoose.1.1, s) := by
        intro hEq
        exact hm (by simpa using congrArg Prod.fst hEq)
      simpa [freshCache, QueryCache.cacheQuery_of_ne qchoose.2.1 cm hne] using hnone
    rcases exists_new_salt_cacheEntry_of_count_gt_one
        (M := M) (S := S) (C := C) (oa := oa) (m0 := qchoose.1.1) (s := s)
        (cache₀ := freshCache) (counts₀ := Function.update qchoose.2.2 s 1)
        (z := z) hcount1 hself1 hunique1 hz hgt with ⟨m, v, hmne, hcache⟩
    exact ⟨m, v, hmne, hcache⟩
  have hcache_to_log :
      Pr[cacheEvent | cacheRun] ≤
        Pr[fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s)
          | cachedLogRun] := by
    dsimp [cacheRun, cachedLogRun]
    rw [← run_cached_logging_proj_eq_cachingOracle
      (M := M) (S := S) (C := C) oa freshCache]
    rw [probEvent_map]
    refine probEvent_mono ?_
    intro z hz hcacheEv
    rcases hcacheEv with ⟨m, v, hmne, hcache⟩
    have hlog :=
      cache_entry_in_log_or_initial oa freshCache z hz (m, s) v hcache
    cases hlog with
    | inl hinit =>
        have hnone :
            qchoose.2.1 (m, s) = none :=
          cache_none_of_zero_count_of_mem_support_run_hidingChoose
            (M := M) (S := S) (C := C) A hqchoose m s hzero
        have hne : (m, s) ≠ (qchoose.1.1, s) := by
          intro hEq
          exact hmne (by simpa using congrArg Prod.fst hEq)
        have hinitnone : freshCache (m, s) = none := by
          simpa [freshCache, QueryCache.cacheQuery_of_ne qchoose.2.1 cm hne] using hnone
        have : some v = none := hinit.symm.trans hinitnone
        cases this
    | inr hentry =>
        rcases hentry with ⟨entry, hmem, hentry_eq, _⟩
        have hsalt : entry.1.2 = s := by
          simpa using congrArg Prod.snd hentry_eq
        exact queryLog_countQ_pos_of_mem
          (M := M) (S := S) (C := C) hmem (by simp [hsalt])
  exact le_trans hcount_to_cache hcache_to_log

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma cacheQuery_swap_of_ne
    (cache : QueryCache (CMOracle M S C))
    {t₀ t₁ : (CMOracle M S C).Domain}
    (u₀ u₁ : C)
    (hne : t₀ ≠ t₁) :
    (cache.cacheQuery t₀ u₀).cacheQuery t₁ u₁ =
      (cache.cacheQuery t₁ u₁).cacheQuery t₀ u₀ := by
  ext t
  by_cases ht₀ : t = t₀
  · subst ht₀
    simp [QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne, hne]
  · by_cases ht₁ : t = t₁
    · subst ht₁
      simp [QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne, hne.symm]
    · simp [QueryCache.cacheQuery_of_ne, ht₀, ht₁]

omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
lemma wp_querySaltIndicator_prepend_eq_one
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (cache : QueryCache (CMOracle M S C))
    (t : (CMOracle M S C).Domain) (u : C) (s : S)
    (hsalt : t.2 = s) :
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((fun p : α × QueryLog (CMOracle M S C) =>
            (p.1, (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
          (simulateQ loggingOracle oa).run)).run cache)
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) = 1 := by
  rw [simulateQ_map]
  change OracleComp.ProgramLogic.wp
      (((fun zz : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          ((zz.1.1,
              (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: zz.1.2),
            zz.2)) <$>
        (simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache))
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) = 1
  rw [OracleComp.ProgramLogic.wp_map]
  have hpost :
      ((fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) ∘
        fun zz : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          ((zz.1.1,
              (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: zz.1.2),
            zz.2)) =
      fun _ => (1 : ℝ≥0∞) := by
    funext z
    have hpos :
        0 <
          QueryLog.countQ
            ((⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: z.1.2)
            (fun t' : (CMOracle M S C).Domain => t'.2 = s) := by
      simp [QueryLog.countQ, QueryLog.getQ_cons, hsalt]
    simp [OracleComp.ProgramLogic.propInd, hpos]
  rw [hpost, OracleComp.ProgramLogic.wp_const]

omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
lemma wp_querySaltIndicator_prepend_eq_of_ne
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (cache : QueryCache (CMOracle M S C))
    (t : (CMOracle M S C).Domain) (u : C) (s : S)
    (hsalt : t.2 ≠ s) :
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((fun p : α × QueryLog (CMOracle M S C) =>
            (p.1, (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
          (simulateQ loggingOracle oa).run)).run cache)
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) =
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache)
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) := by
  rw [simulateQ_map]
  change OracleComp.ProgramLogic.wp
      (((fun zz : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          ((zz.1.1,
              (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: zz.1.2),
            zz.2)) <$>
        (simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache))
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) =
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache)
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s)))
  rw [OracleComp.ProgramLogic.wp_map]
  have hpost :
      ((fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) ∘
        fun zz : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
          ((zz.1.1,
              (⟨t, u⟩ : (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: zz.1.2),
            zz.2)) =
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) := by
    funext z
    simp [QueryLog.countQ, QueryLog.getQ_cons, hsalt, OracleComp.ProgramLogic.propInd]
  rw [hpost]

omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
lemma wp_querySaltIndicator_cached_logging_cacheQuery_eq_of_no_other_salt_entries
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (cache₀ : QueryCache (CMOracle M S C))
    (m : M) (s : S) (cm : C)
    (hself : cache₀ (m, s) = none)
    (hother : ∀ m' : M, m' ≠ m → cache₀ (m', s) = none) :
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run
        (cache₀.cacheQuery (m, s) cm))
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))) =
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle ((simulateQ loggingOracle oa).run)).run cache₀)
      (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))) := by
  induction oa using OracleComp.inductionOn generalizing cache₀ with
  | pure x =>
      simp [simulateQ_pure, QueryLog.countQ]
  | query_bind t mx ih =>
      change
        OracleComp.ProgramLogic.wp
          ((simulateQ cachingOracle
            ((liftM (query (spec := CMOracle M S C) t)) >>= fun u =>
              (fun p : α × QueryLog (CMOracle M S C) =>
                (p.1,
                  (⟨t, u⟩ :
                    (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
                (simulateQ loggingOracle (mx u)).run)).run
            (cache₀.cacheQuery (m, s) cm))
          (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
            OracleComp.ProgramLogic.propInd
              (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s))) =
        OracleComp.ProgramLogic.wp
          ((simulateQ cachingOracle
            ((liftM (query (spec := CMOracle M S C) t)) >>= fun u =>
              (fun p : α × QueryLog (CMOracle M S C) =>
                (p.1,
                  (⟨t, u⟩ :
                    (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
                (simulateQ loggingOracle (mx u)).run)).run cache₀)
          (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
            OracleComp.ProgramLogic.propInd
              (0 < QueryLog.countQ z.1.2 (fun t' : (CMOracle M S C).Domain => t'.2 = s)))
      simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
      rw [OracleComp.ProgramLogic.wp_bind, OracleComp.ProgramLogic.wp_bind]
      by_cases hsalt : t.2 = s
      · have hpost :
            (fun qu : C × QueryCache (CMOracle M S C) =>
              OracleComp.ProgramLogic.wp
                ((simulateQ cachingOracle
                  ((fun p : α × QueryLog (CMOracle M S C) =>
                      (p.1,
                        (⟨t, (query t).cont qu.1⟩ :
                          (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
                    (simulateQ loggingOracle (mx ((query t).cont qu.1))).run)).run qu.2)
                (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
                  OracleComp.ProgramLogic.propInd
                    (0 < QueryLog.countQ z.1.2
                      (fun t' : (CMOracle M S C).Domain => t'.2 = s)))) =
            fun _ => (1 : ℝ≥0∞) := by
          funext qu
          exact wp_querySaltIndicator_prepend_eq_one
            (M := M) (S := S) (C := C)
            (oa := mx ((query t).cont qu.1)) (cache := qu.2)
            (t := t) (u := (query t).cont qu.1) (s := s) hsalt
        rw [hpost]
        simp [OracleComp.ProgramLogic.wp_const]
      · have hpost :
            (fun qu : C × QueryCache (CMOracle M S C) =>
              OracleComp.ProgramLogic.wp
                ((simulateQ cachingOracle
                  ((fun p : α × QueryLog (CMOracle M S C) =>
                      (p.1,
                        (⟨t, (query t).cont qu.1⟩ :
                          (i : (CMOracle M S C).Domain) × (CMOracle M S C).Range i) :: p.2)) <$>
                    (simulateQ loggingOracle (mx ((query t).cont qu.1))).run)).run qu.2)
                (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
                  OracleComp.ProgramLogic.propInd
                    (0 < QueryLog.countQ z.1.2
                      (fun t' : (CMOracle M S C).Domain => t'.2 = s)))) =
            (fun qu : C × QueryCache (CMOracle M S C) =>
              OracleComp.ProgramLogic.wp
                ((simulateQ cachingOracle
                  ((simulateQ loggingOracle (mx ((query t).cont qu.1))).run)).run qu.2)
                (fun z : (α × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
                  OracleComp.ProgramLogic.propInd
                    (0 < QueryLog.countQ z.1.2
                      (fun t' : (CMOracle M S C).Domain => t'.2 = s)))) := by
          funext qu
          exact wp_querySaltIndicator_prepend_eq_of_ne
            (M := M) (S := S) (C := C)
            (oa := mx ((query t).cont qu.1)) (cache := qu.2)
            (t := t) (u := (query t).cont qu.1) (s := s) hsalt
        rw [hpost]
        have htne : t ≠ (m, s) := by
          intro hEq
          exact hsalt (by simpa using congrArg Prod.snd hEq)
        have hmst_ne_t : (m, s) ≠ t := by
          intro hEq
          exact htne hEq.symm
        have hcache_eq : (cache₀.cacheQuery (m, s) cm) t = cache₀ t := by
          simp [QueryCache.cacheQuery_of_ne cache₀ cm htne]
        cases ht : cache₀ t with
        | some u =>
            have hcache_hit : (cache₀.cacheQuery (m, s) cm) t = some u := by
              rw [hcache_eq, ht]
            have hcache_fresh_run :
                (liftM (cachingOracle (spec := CMOracle M S C) t) :
                  StateT (QueryCache (CMOracle M S C))
                    (OracleComp (CMOracle M S C)) _).run
                    (cache₀.cacheQuery (m, s) cm) =
                  pure (u, cache₀.cacheQuery (m, s) cm) := by
              simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
                StateT.run_bind, StateT.run_get, hcache_hit, pure_bind, StateT.run_pure]
            have hcache_common_run :
                (liftM (cachingOracle (spec := CMOracle M S C) t) :
                  StateT (QueryCache (CMOracle M S C))
                    (OracleComp (CMOracle M S C)) _).run cache₀ =
                  pure (u, cache₀) := by
              simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
                StateT.run_bind, StateT.run_get, ht, pure_bind, StateT.run_pure]
            rw [hcache_fresh_run, hcache_common_run]
            rw [OracleComp.ProgramLogic.wp_pure, OracleComp.ProgramLogic.wp_pure]
            simpa [OracleQuery.cont_query] using ih u cache₀ hself hother
        | none =>
            have hcache_none : (cache₀.cacheQuery (m, s) cm) t = none := by
              rw [hcache_eq, ht]
            have hmiss_fresh :
                (liftM (cachingOracle (spec := CMOracle M S C) t) :
                  StateT (QueryCache (CMOracle M S C))
                    (OracleComp (CMOracle M S C)) _).run
                    (cache₀.cacheQuery (m, s) cm) =
                  (liftM (query (spec := CMOracle M S C) t) >>= fun u =>
                    pure (u, (cache₀.cacheQuery (m, s) cm).cacheQuery t u) :
                      OracleComp (CMOracle M S C) (C × QueryCache (CMOracle M S C))) := by
              simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
                StateT.run_bind, StateT.run_get, pure_bind, hcache_none]
              change (StateT.lift
                  (PFunctor.FreeM.lift (query (spec := CMOracle M S C) t))
                  (cache₀.cacheQuery (m, s) cm) >>= _) = _
              simp only [StateT.lift, bind_assoc, pure_bind,
                modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
                StateT.modifyGet, StateT.run]
            have hmiss_common :
                (liftM (cachingOracle (spec := CMOracle M S C) t) :
                  StateT (QueryCache (CMOracle M S C))
                    (OracleComp (CMOracle M S C)) _).run cache₀ =
                  (liftM (query (spec := CMOracle M S C) t) >>= fun u =>
                    pure (u, cache₀.cacheQuery t u) :
                      OracleComp (CMOracle M S C) (C × QueryCache (CMOracle M S C))) := by
              simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
                StateT.run_bind, StateT.run_get, pure_bind, ht]
              change (StateT.lift
                (PFunctor.FreeM.lift (query (spec := CMOracle M S C) t))
                cache₀ >>= _) = _
              simp only [StateT.lift, bind_assoc, pure_bind,
                modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
                StateT.modifyGet, StateT.run]
            rw [hmiss_fresh, hmiss_common, OracleComp.ProgramLogic.wp_bind,
              OracleComp.ProgramLogic.wp_bind]
            simp_rw [OracleComp.ProgramLogic.wp_pure]
            rw [OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
            refine tsum_congr ?_
            intro u
            congr 1
            have hself' : (cache₀.cacheQuery t u) (m, s) = none := by
              simpa [QueryCache.cacheQuery_of_ne cache₀ u hmst_ne_t] using hself
            have hother' : ∀ m' : M, m' ≠ m → (cache₀.cacheQuery t u) (m', s) = none := by
              intro m' hm'
              have hne' : (m', s) ≠ t := by
                intro hEq
                exact hsalt (by simpa [eq_comm] using congrArg Prod.snd hEq)
              simpa [QueryCache.cacheQuery_of_ne cache₀ u hne'] using hother m' hm'
            simpa [OracleQuery.cont_query,
              cacheQuery_swap_of_ne (M := M) (S := S) (C := C)
              (cache := cache₀) (t₀ := (m, s)) (t₁ := t) cm u hmst_ne_t]
              using ih u (cache₀.cacheQuery t u) hself' hother'

omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
lemma wp_querySaltIndicator_cached_logging_freshCache_eq_common
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × HidingCountState M S C}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    (hzero : qchoose.2.2 s = 0)
    (cm : C) :
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run
        (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm))
      (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))) =
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run qchoose.2.1)
      (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))) := by
  refine wp_querySaltIndicator_cached_logging_cacheQuery_eq_of_no_other_salt_entries
    (M := M) (S := S) (C := C)
    (oa := A.distinguish qchoose.1.2 cm)
    (cache₀ := qchoose.2.1)
    (m := qchoose.1.1) (s := s) (cm := cm) ?_ ?_
  · exact cache_none_of_zero_count_of_mem_support_run_hidingChoose
      (M := M) (S := S) (C := C) A hqchoose qchoose.1.1 s hzero
  · intro m' hm'
    exact cache_none_of_zero_count_of_mem_support_run_hidingChoose
      (M := M) (S := S) (C := C) A hqchoose m' s hzero

omit [DecidableEq C] [Fintype M] [Inhabited M] in
lemma sum_wp_freshDistinguishIncrement_le_queryResidual_of_choose_support
    [Finite M]
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
                (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))) ≤
      (t - ∑ s : S, qchoose.2.2 s) := by
  haveI : Fintype M := Fintype.ofFinite M
  classical
  rw [sum_wp_freshDistinguishIncrement_eq_query (M := M) (S := S) (C := C) A hqchoose]
  let freshTerm : S → ℝ≥0∞ := fun s =>
    OracleComp.ProgramLogic.propInd (qchoose.2.2 s = 0) *
      OracleComp.ProgramLogic.wp
        (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
          OracleComp (CMOracle M S C) C)
        (fun cm =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run
              (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
                Function.update qchoose.2.2 s 1))
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd (1 < z.2.2 s)))
  let logTerm : S → ℝ≥0∞ := fun s =>
    OracleComp.ProgramLogic.propInd (qchoose.2.2 s = 0) *
      OracleComp.ProgramLogic.wp
        (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
          OracleComp (CMOracle M S C) C)
        (fun cm =>
          OracleComp.ProgramLogic.wp
            ((simulateQ cachingOracle
              ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run qchoose.2.1)
            (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
              OracleComp.ProgramLogic.propInd
                (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))))
  have hstep : (∑ s : S, freshTerm s) ≤ ∑ s : S, logTerm s := by
    refine Finset.sum_le_sum ?_
    intro s hs
    by_cases hzero : qchoose.2.2 s = 0
    · dsimp [freshTerm, logTerm]
      simp only [hzero, OracleComp.ProgramLogic.propInd_true, one_mul]
      refine OracleComp.ProgramLogic.wp_mono
        (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
          OracleComp (CMOracle M S C) C) ?_
      intro cm
      refine le_trans
        (fresh_incrementIndicator_le_querySaltIndicator_cached_logging
          (M := M) (S := S) (C := C) A hqchoose s hzero cm) ?_
      exact le_of_eq
        (wp_querySaltIndicator_cached_logging_freshCache_eq_common
          (M := M) (S := S) (C := C) A hqchoose s hzero cm)
    · dsimp [freshTerm, logTerm]
      simp only [hzero, OracleComp.ProgramLogic.propInd_false, zero_mul, zero_le]
  refine le_trans hstep ?_
  have hdrop :
      (∑ s : S, logTerm s)
      ≤
      (∑ s : S,
        OracleComp.ProgramLogic.wp
          (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
            OracleComp (CMOracle M S C) C)
          (fun cm =>
            OracleComp.ProgramLogic.wp
              ((simulateQ cachingOracle
                ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run qchoose.2.1)
              (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
                OracleComp.ProgramLogic.propInd
                  (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s))))) := by
    refine Finset.sum_le_sum ?_
    intro s hs
    by_cases hzero : qchoose.2.2 s = 0
    · dsimp [logTerm]
      simp only [hzero, OracleComp.ProgramLogic.propInd_true, one_mul,
        le_refl]
    · dsimp [logTerm]
      simp only [hzero, OracleComp.ProgramLogic.propInd_false, zero_mul,
        zero_le]
  refine le_trans hdrop ?_
  let G : S → C → ℝ≥0∞ := fun s cm =>
    OracleComp.ProgramLogic.wp
      ((simulateQ cachingOracle
        ((simulateQ loggingOracle (A.distinguish qchoose.1.2 cm)).run)).run qchoose.2.1)
      (fun z : (Bool × QueryLog (CMOracle M S C)) × QueryCache (CMOracle M S C) =>
        OracleComp.ProgramLogic.propInd
          (0 < QueryLog.countQ z.1.2 (fun t : (CMOracle M S C).Domain => t.2 = s)))
  calc
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
          OracleComp (CMOracle M S C) C)
        (fun cm => G s cm))
      = ∑ s : S, ∑ cm : C, (Fintype.card C : ℝ≥0∞)⁻¹ * G s cm := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [OracleComp.ProgramLogic.wp_eq_tsum, tsum_fintype]
          refine Finset.sum_congr rfl ?_
          intro cm hcm
          simp [G, probOutput_query]
    _ = ∑ cm : C, ∑ s : S, (Fintype.card C : ℝ≥0∞)⁻¹ * G s cm := by
          simpa using (Finset.sum_comm :
            (∑ s : S, ∑ cm : C, (Fintype.card C : ℝ≥0∞)⁻¹ * G s cm) =
              ∑ cm : C, ∑ s : S, (Fintype.card C : ℝ≥0∞)⁻¹ * G s cm)
    _ = ∑ cm : C, (Fintype.card C : ℝ≥0∞)⁻¹ * ∑ s : S, G s cm := by
          refine Finset.sum_congr rfl ?_
          intro cm hcm
          rw [Finset.mul_sum]
    _ ≤ ∑ cm : C, (Fintype.card C : ℝ≥0∞)⁻¹ * (t - ∑ s : S, qchoose.2.2 s) := by
          refine Finset.sum_le_sum ?_
          intro cm hcm
          exact mul_le_mul' le_rfl
            (by
              simpa [G] using
                (sum_wp_querySaltIndicators_le_queryBound_of_run_cached_logging
                  (M := M) (S := S) (C := C)
                  (cache₀ := qchoose.2.1)
                  (oa := A.distinguish qchoose.1.2 cm)
                  (n := t - ∑ s : S, qchoose.2.2 s)
                  (hiding_distinguish_totalBound_of_choose_count_support
                    (M := M) (S := S) (C := C) A hqchoose cm)))
    _ = (t - ∑ s : S, qchoose.2.2 s) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← mul_assoc]
          have hcard0 : (Fintype.card C : ℝ≥0∞) ≠ 0 := by simp
          have hcard_top : (Fintype.card C : ℝ≥0∞) ≠ ∞ := by simp
          rw [ENNReal.mul_inv_cancel hcard0 hcard_top, one_mul]

omit [DecidableEq C] [Fintype M] [Inhabited M] in
theorem sum_probEvent_hidingBad_le [Finite M] {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)]) ≤ t := by
  haveI : Fintype M := Fintype.ofFinite M
  classical
  calc
    (∑ s : S, Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)])
      =
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
          simpa using sum_wp_badIndicator_eq_wp_choose (M := M) (S := S) (C := C) A
    _ ≤
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
        (fun qchoose : (M × AUX) × HidingCountState M S C =>
          ∑ s : S,
            (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
              OracleComp.ProgramLogic.wp
                ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
                (fun qch : C × HidingCountState M S C =>
                  OracleComp.ProgramLogic.wp
                    ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                    (fun z : Bool × HidingCountState M S C =>
                      OracleComp.ProgramLogic.propInd
                        (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))))) := by
          rw [OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
          refine ENNReal.tsum_le_tsum ?_
          intro qchoose
          by_cases hqchoose : qchoose ∈ support
              ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
          · exact mul_le_mul'
              le_rfl
              (wp_badIndicator_le_chooseHit_add_freshDistinguishIncrement_of_choose_support
                (M := M) (S := S) (C := C) A hqchoose)
          · rw [probOutput_eq_zero_of_not_mem_support hqchoose]
            simp
    _ ≤ t := by
      rw [OracleComp.ProgramLogic.wp_eq_tsum]
      calc
        ∑' qchoose,
            Pr[= qchoose | (simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)] *
              (∑ s : S,
                (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                  OracleComp.ProgramLogic.wp
                    ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
                    (fun qch : C × HidingCountState M S C =>
                      OracleComp.ProgramLogic.wp
                        ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
                        (fun z : Bool × HidingCountState M S C =>
                          OracleComp.ProgramLogic.propInd
                            (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s)))))
          ≤
            ∑' qchoose,
              Pr[= qchoose | (simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)] * t := by
                refine ENNReal.tsum_le_tsum ?_
                intro qchoose
                by_cases hqchoose :
                    qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
                · refine mul_le_mul' le_rfl ?_
                  have hhit :
                      (∑ s : S, OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s)) ≤
                        (∑ s : S, qchoose.2.2 s : ℝ≥0∞) :=
                    sum_chooseHitIndicators_le_sumCounts qchoose.2.2
                  have hfresh :
                      (∑ s : S,
                        OracleComp.ProgramLogic.wp
                          ((hidingImplCountAll (M := M) (S := S) (C := C)
                            (qchoose.1.1, s)).run qchoose.2)
                          (fun qch : C × HidingCountState M S C =>
                            OracleComp.ProgramLogic.wp
                              ((simulateQ hidingImplCountAll
                                (A.distinguish qchoose.1.2 qch.1)).run
                                qch.2)
                              (fun z : Bool × HidingCountState M S C =>
                                OracleComp.ProgramLogic.propInd
                                  (qchoose.2.2 s = 0 ∧
                                    qch.2.2 s < z.2.2 s)))) ≤
                        (t - ∑ s : S, qchoose.2.2 s) :=
                    sum_wp_freshDistinguishIncrement_le_queryResidual_of_choose_support
                      (M := M) (S := S) (C := C) A hqchoose
                  have hcounts :
                      (∑ s : S, qchoose.2.2 s) ≤ t :=
                    sum_counts_le_queryBound_of_mem_support_run_hidingChoose
                      (M := M) (S := S) (C := C) A hqchoose
                  calc
                    (∑ s : S,
                      (OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
                        OracleComp.ProgramLogic.wp
                          ((hidingImplCountAll (M := M) (S := S) (C := C)
                            (qchoose.1.1, s)).run qchoose.2)
                          (fun qch : C × HidingCountState M S C =>
                            OracleComp.ProgramLogic.wp
                              ((simulateQ hidingImplCountAll
                                (A.distinguish qchoose.1.2 qch.1)).run
                                qch.2)
                              (fun z : Bool × HidingCountState M S C =>
                                OracleComp.ProgramLogic.propInd
                                  (qchoose.2.2 s = 0 ∧
                                    qch.2.2 s < z.2.2 s)))))
                      = (∑ s : S,
                          OracleComp.ProgramLogic.propInd
                            (0 < qchoose.2.2 s)) +
                          (∑ s : S,
                            OracleComp.ProgramLogic.wp
                              ((hidingImplCountAll (M := M) (S := S) (C := C)
                                (qchoose.1.1, s)).run qchoose.2)
                              (fun qch : C × HidingCountState M S C =>
                                OracleComp.ProgramLogic.wp
                                  ((simulateQ hidingImplCountAll
                                    (A.distinguish qchoose.1.2 qch.1)).run
                                    qch.2)
                                  (fun z : Bool × HidingCountState M S C =>
                                    OracleComp.ProgramLogic.propInd
                                      (qchoose.2.2 s = 0 ∧
                                        qch.2.2 s < z.2.2 s)))) := by
                          rw [Finset.sum_add_distrib]
                    _ ≤ (∑ s : S, qchoose.2.2 s : ℝ≥0∞) +
                          (t - ∑ s : S, qchoose.2.2 s) := by
                          exact add_le_add hhit hfresh
                    _ = t := by
                          have hcast : (∑ s : S, qchoose.2.2 s : ℝ≥0∞) ≤ t := by
                            exact_mod_cast hcounts
                          rw [add_comm, Nat.cast_sum]
                          exact tsub_add_cancel_of_le hcast
                · rw [probOutput_eq_zero_of_not_mem_support hqchoose]
                  simp
    _ = t := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

