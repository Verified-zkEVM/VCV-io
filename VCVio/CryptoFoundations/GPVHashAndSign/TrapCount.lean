/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.VerificationBridge

/-! # GPV Hash-and-Sign: The Counter-Augmented Trap Run

The N5 counter-augmented trap run tagging the forged point with its programming
index, and its agreement with the untagged run.
-/

public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

/-! #### N5. Counter-augmented trap run: tagging the forged point's programming index

The trapdoor-recording combined run `progGameRunImplCombinedTrap` carries an *unordered* hidden
preimage table `(Salt × M) → Option Domain`, so it does not expose the *order* in which programmed
entries were written.  To partition the trap mass by the programming index of the forged point we
augment the run with a passive `(idxTable, counter)` instrument: a running `ℕ` counter that
increments by one on every programming event (each random-oracle cache miss and each signing step —
exactly the events that write a fresh preimage-table key), and an insertion-index table
`(Salt × M) → Option ℕ` that records, at each such event, the counter value at the time the key was
first written.  The instrument is never *read* during the run, so it is distributionally passive:
projecting it away recovers `progGameRunImplCombinedTrap` exactly
(`map_run_progGameRunImplCombinedTrapCount_proj`).  The insertion-index table is written in lockstep
with the preimage table (`progGameRunImplCombinedTrapCount_idx_iff_table`), so on every trap-winning
trajectory the forged point — being in the preimage table — has a well-defined recorded insertion
index, which drives the trap-mass index partition `∑' j, g j = trap`. -/

open Classical in
/-- **N5 — the counter-augmented trapdoor-recording combined handler.** Identical to
`progGameRunImplCombinedTrap` on its first state component, but additionally threads a passive
`(idxTable, counter)` instrument: a running `ℕ` programming counter and an insertion-index table
`(Salt × M) → Option ℕ`.  At each programming event (random-oracle miss or signing step) it records
the current counter value into the index table at the freshly written key and increments the
counter; on uniform queries and random-oracle cache hits the instrument is left untouched. -/
@[expose] noncomputable def progGameRunImplCombinedTrapCount (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl (.inl q) => do
        let v ← (unifSpec.query q : ProbComp _)
        pure (v, s)
    | .inl (.inr q) =>
        match s.1.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let v ← ($ᵗ Range : ProbComp Range)
            let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
            pure (v,
              ((((s.1.1.1.1.cacheQuery q v, s.1.1.1.2), s.1.1.2),
                fun t' => if t' = q then some x else s.1.2 t'),
                ((fun t' => if t' = q then some s.2.2 else s.2.1 t'), s.2.2 + 1)))
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let v ← ($ᵗ Range : ProbComp Range)
        let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
        pure ((r, x),
          ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
            s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r),
            fun t' => if t' = (r, msg) then some x else s.1.2 t'),
            ((fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1)))

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrapCount` on a uniform query.** -/
lemma progGameRunImplCombinedTrapCount_run_inl_inl (pk : PK) (sk : SK) (q : unifSpec.Domain)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    (progGameRunImplCombinedTrapCount psf M Salt pk sk (.inl (.inl q))).run s =
      (do let v ← (unifSpec.query q : ProbComp _); pure (v, s)) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrapCount` on a random-oracle query.** -/
lemma progGameRunImplCombinedTrapCount_run_inl_inr (pk : PK) (sk : SK)
    (q : (Salt × M →ₒ Range).Domain)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    (progGameRunImplCombinedTrapCount psf M Salt pk sk (.inl (.inr q))).run s =
      (match s.1.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let v ← ($ᵗ Range : ProbComp Range)
            let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
            pure (v,
              ((((s.1.1.1.1.cacheQuery q v, s.1.1.1.2), s.1.1.2),
                fun t' => if t' = q then some x else s.1.2 t'),
                ((fun t' => if t' = q then some s.2.2 else s.2.1 t'), s.2.2 + 1)))) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrapCount` on a signing query.** -/
lemma progGameRunImplCombinedTrapCount_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    (progGameRunImplCombinedTrapCount psf M Salt pk sk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let v ← ($ᵗ Range : ProbComp Range)
        let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
        pure ((r, x),
          ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
            s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r),
            fun t' => if t' = (r, msg) then some x else s.1.2 t'),
            ((fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1)))) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 per-query projection.** Dropping the `(idxTable, counter)` instrument from one
`progGameRunImplCombinedTrapCount` query step recovers the corresponding
`progGameRunImplCombinedTrap` step.  This is the per-query hypothesis of the state-projection
transport `map_run_simulateQ_eq_of_query_map_eq`, witnessing that the instrument is passive. -/
lemma progGameRunImplCombinedTrapCount_proj (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    Prod.map id
        (Prod.fst : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
            ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) →
          (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) <$>
        (progGameRunImplCombinedTrapCount psf M Salt pk sk t).run s =
      (progGameRunImplCombinedTrap psf M Salt pk sk t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombinedTrapCount_run_inl_inl, progGameRunImplCombinedTrap_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [progGameRunImplCombinedTrapCount_run_inl_inr, progGameRunImplCombinedTrap_run_inl_inr]
          cases s.1.1.1.1 q with
          | none => simp [map_eq_bind_pure_comp, Prod.map]
          | some v => simp [Prod.map]
  | inr msg =>
      rw [progGameRunImplCombinedTrapCount_run_inr, progGameRunImplCombinedTrap_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 run-level projection (passive augmentation).** Dropping the `(idxTable, counter)`
instrument from the full simulated run of `progGameRunImplCombinedTrapCount` over `oa` recovers the
run of `progGameRunImplCombinedTrap` from the projected start state.  Transports the per-query
`progGameRunImplCombinedTrapCount_proj` through the whole computation via
`map_run_simulateQ_eq_of_query_map_eq`: the instrument is distributionally passive, so the
counter and the insertion-index table do not change the trap event mass. -/
lemma map_run_progGameRunImplCombinedTrapCount_proj (pk : PK) (sk : SK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    Prod.map id
        (Prod.fst : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
            ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) →
          (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) <$>
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s =
      (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) →
      (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (progGameRunImplCombinedTrapCount_proj psf M Salt pk sk) oa s

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 lockstep-domain invariant.** Starting from a state whose insertion-index table and hidden
preimage table agree on which keys are recorded, every state reachable in the counter-augmented run
preserves that agreement: a key has a recorded preimage iff it has a recorded insertion index.  The
two tables are written by the *same* conditional update at each programming event (random-oracle
miss or signing step) and are both untouched on uniform queries and cache hits, so the per-key
`isSome` status of the two tables stays in lockstep through the whole adaptive fold.  This is the
support-level fact that lets the trap-mass index partition over recorded insertion indices recover
the full trap mass: every trap-winning trajectory, having its forged point in the preimage table,
has a well-defined recorded forged-point insertion index. -/
lemma progGameRunImplCombinedTrapCount_idx_iff_table (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)),
      (∀ k, s.1.2 k ≠ none ↔ s.2.1 k ≠ none) →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        ∀ k, z.2.1.2 k ≠ none ↔ z.2.2.1 k ≠ none := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
  | query_bind t mx ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · -- uniform query: instrument untouched
        rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        rw [hpst] at hz
        exact ih pv s hs z hz
      · -- random-oracle query: hit keeps both tables, miss writes both keys together
        rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            rw [hpst] at hz
            exact ih pv s hs z hz
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            refine ih pv pst ?_ z hz
            intro k
            rw [hpst]
            by_cases hk : k = mc
            · subst hk; simp
            · simp only [if_neg hk]; exact hs k
      · -- signing query: writes both keys together
        rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        refine ih pv pst ?_ z hz
        intro k
        rw [hpst]
        by_cases hk : k = (r, msg)
        · subst hk; simp
        · simp only [if_neg hk]; exact hs k

/-- **Deterministic `Option ℕ`-index partition of an event.** For a computation `mx`, an event `P`,
and an `Option ℕ`-valued index `idx` that is recorded (`≠ none`) on every positive-probability `P`
outcome, the event mass partitions over the index value: `Pr[P] = ∑' j, Pr[P ∧ idx = some j]`.  The
`some j` atoms tile the event, with the index of each `P`-outcome read off the outcome itself.  This
is the abstract index partition behind the GPV Step-2 trap-mass decomposition `∑' j, g j = trap`. -/
theorem probEvent_eq_tsum_probEvent_index_aux {ι : Type} {m : Type → Type} [Monad m]
    [MonadLiftT m SPMF] (mx : m ι) (P : ι → Prop) (idx : ι → Option ℕ)
    (hidx : ∀ x, Pr[= x | mx] ≠ 0 → P x → idx x ≠ none) :
    Pr[P | mx] = ∑' j : ℕ, Pr[fun x => P x ∧ idx x = some j | mx] := by
  classical
  rw [probEvent_eq_tsum_indicator]
  have hcongr : ∀ j : ℕ,
      Pr[fun x => P x ∧ idx x = some j | mx]
        = ∑' x : ι, {x | P x ∧ idx x = some j}.indicator (Pr[= · | mx]) x := by
    intro j; rw [probEvent_eq_tsum_indicator]
  simp_rw [hcongr]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  by_cases hPx : P x
  · rcases eq_or_ne (Pr[= x | mx]) 0 with hp0 | hp0
    · rw [Set.indicator_apply, if_pos (Set.mem_ofPred_eq ▸ hPx), hp0]
      symm
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      refine ENNReal.tsum_eq_zero.mpr fun j => ?_
      by_cases hc : P x ∧ idx x = some j
      · rw [if_pos hc, hp0]
      · rw [if_neg hc]
    · obtain ⟨j₀, hj₀⟩ := Option.ne_none_iff_exists'.mp (hidx x hp0 hPx)
      rw [Set.indicator_of_mem (Set.mem_ofPred_eq ▸ hPx)]
      rw [tsum_eq_single j₀]
      · rw [Set.indicator_of_mem (Set.mem_ofPred_eq ▸ ⟨hPx, hj₀⟩)]
      · intro j hj
        rw [Set.indicator_of_notMem]
        rintro ⟨-, hjeq⟩
        exact hj (by rw [hj₀] at hjeq; exact (Option.some.inj hjeq).symm)
  · rw [Set.indicator_of_notMem (show x ∉ {x | P x} from hPx)]
    symm
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    refine ENNReal.tsum_eq_zero.mpr fun j => ?_
    rw [if_neg (fun h => hPx h.1)]

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 counter bound.** From any start state, every final state of the counter-augmented trap run
of an adversary `oa` bounded by `(qS, qH)` (signing / hash queries) has its running programming
counter at most `s.counter + qS + qH`: the counter is incremented exactly once per programming event
(random-oracle miss or signing step), each charged against the corresponding query budget; uniform
queries and random-oracle cache hits leave the counter fixed.  This is the trapCount-run dual of
`embedAtIndexImpl_run_count_le`. -/
lemma progGameRunImplCombinedTrapCount_run_count_le (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ)) (qS qH : ℕ),
      oa.IsQueryBoundP (· matches .inr _) qS →
      oa.IsQueryBoundP (· matches .inl (.inr _)) qH →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        z.2.2.2 ≤ s.2.2 + qS + qH := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s qS qH _ _ z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact le_add_right (Nat.le_add_right _ _)
  | query_bind t mx ih =>
      intro s qS qH hQS hQH z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQS hQH
      obtain ⟨hQS1, hQS2⟩ := hQS
      obtain ⟨hQH1, hQH2⟩ := hQH
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · -- uniform query: counter untouched
        rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have := ih pv pst qS qH hbS hbH z hz
        rw [hpst] at this; exact le_trans this (by omega)
      · -- random-oracle query: hit leaves the counter fixed, miss increments by one
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqH : 0 < qH := by simpa using hQH1
        rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            have := ih pv pst qS (qH - 1) hbS hbH z hz
            rw [hpst] at this; exact le_trans this (by omega)
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            have := ih pv pst qS (qH - 1) hbS hbH z hz
            have hc : pst.2.2 = s.2.2 + 1 := by rw [hpst]
            rw [hc] at this; exact le_trans this (by omega)
      · -- signing query: increments the counter
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqS : 0 < qS := by simpa using hQS1
        rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        have := ih pv pst (qS - 1) qH hbS hbH z hz
        have hc : pst.2.2 = s.2.2 + 1 := by rw [hpst]
        rw [hc] at this; exact le_trans this (by omega)

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 recorded-index range.** From a start state whose insertion-index table only records indices
strictly below the running counter, every state reachable in the counter-augmented trap run
preserves that bound: every recorded insertion index is `< counter`.  Each programming event records
the *current* counter value and then increments the counter, so the freshly recorded index is `<`
the new counter; previously recorded indices stay below the (only larger) counter; uniform queries
and cache hits leave both unchanged. -/
lemma progGameRunImplCombinedTrapCount_idx_lt_count (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ)),
      (∀ k i, s.2.1 k = some i → i < s.2.2) →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        ∀ k i, z.2.2.1 k = some i → i < z.2.2.2 := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
  | query_bind t mx ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · -- uniform query: instrument untouched
        rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        refine ih pv pst ?_ z hz
        rw [hpst]; exact hs
      · -- random-oracle query: hit unchanged, miss records `counter` and increments
        rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            refine ih pv pst ?_ z hz
            rw [hpst]; exact hs
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            refine ih pv pst ?_ z hz
            intro k i hki
            have hcnt : pst.2.2 = s.2.2 + 1 := by rw [hpst]
            have hidx : pst.2.1 = fun t' => if t' = mc then some s.2.2 else s.2.1 t' := by
              rw [hpst]
            rw [hcnt]
            rw [hidx] at hki
            by_cases hk : k = mc
            · subst hk; simp only [if_true] at hki
              rw [Option.some.injEq] at hki; omega
            · simp only [if_neg hk] at hki
              exact Nat.lt_succ_of_lt (hs k i hki)
      · -- signing query: records `counter` and increments
        rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        refine ih pv pst ?_ z hz
        intro k i hki
        have hcnt : pst.2.2 = s.2.2 + 1 := by rw [hpst]
        have hidx : pst.2.1 = fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t' := by
          rw [hpst]
        rw [hcnt]
        rw [hidx] at hki
        by_cases hk : k = (r, msg)
        · subst hk; simp only [if_true] at hki
          rw [Option.some.injEq] at hki; omega
        · simp only [if_neg hk] at hki
          exact Nat.lt_succ_of_lt (hs k i hki)

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 recorded-index budget.** From the empty/zero start state, every recorded insertion index of
the counter-augmented trap run of an adversary obeying `signHashQueryBound` is `< qSign + qHash`:
the index is `< counter` (`progGameRunImplCombinedTrapCount_idx_lt_count`) and the counter is
`≤ qSign + qHash` (`progGameRunImplCombinedTrapCount_run_count_le`).  This bounds the realized
programming index that the reservoir winner `reservoirWinnerIndex (qSign + qHash)` samples over. -/
lemma progGameRunImplCombinedTrapCount_idx_lt_budget (pk : PK) (sk : SK) (qSign qHash : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (hQ : signHashQueryBound (S' := Salt × Domain) (α := β)
      (oa := oa) (qSign := qSign) (qHash := qHash))
    {z : β × (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
      ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ))}
    (hmem : z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run
      (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
        (fun _ => none), 0)))
    {k : Salt × M} {i : ℕ} (hki : z.2.2.1 k = some i) : i < qSign + qHash := by
  have hidx := progGameRunImplCombinedTrapCount_idx_lt_count psf M Salt pk sk oa
    (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
      (fun _ => none), 0) (by intro k i hk; simp at hk) z hmem k i hki
  have hcnt := progGameRunImplCombinedTrapCount_run_count_le psf M Salt pk sk oa
    (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
      (fun _ => none), 0) qSign qHash hQ.1 hQ.2 z hmem
  simp only at hcnt
  omega

omit [DecidableEq Range] [Fintype Salt] in
/-- **N4 (scaffold) — off-slot target independence of the trap-sibling embed step.** The embedded
target `y` enters the trap-sibling handler `embedTrapImpl … j y` at *exactly one* query step: the
random-oracle **miss** whose running count equals the winner slot `j`.  Everywhere else — uniform
queries, random-oracle cache hits, off-`j` random-oracle misses (`s.2 ≠ j`), and signing steps — the
per-step run is *literally independent* of `y`, drawing and caching a fresh uniform image (or, on a
hit, returning the cached value) with no reference to `y`.

This is the structural foundation of the GPV Step-2 front-loading commute: it is what lets the
externally-averaged target `y ← $ᵗ Range` be pushed *past* every non-winner step of the
`simulateQ (embedTrapImpl … j y)` fold (each such step commutes with the front draw by
`OracleComp.DeferredSampling.evalSPMF_bind_comm`), leaving only the single count-`j` miss at which
`y` is consumed — the slot the inline trap winner draw `v⋆ ← $ᵗ Range` must be coupled to. -/
lemma embedTrapImpl_run_step_indep_of_target (pk : PK) (sk : SK) (j : ℕ) (y₁ y₂ : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ)
    (hoff : ∀ q : (Salt × M →ₒ Range).Domain, t = .inl (.inr q) → s.1 q = none → s.2 ≠ j) :
    (embedTrapImpl psf M Salt pk sk j y₁ t).run s =
      (embedTrapImpl psf M Salt pk sk j y₂ t).run s := by
  cases t with
  | inl q =>
      cases q with
      | inl q => rw [embedTrapImpl_run_inl_inl, embedTrapImpl_run_inl_inl]
      | inr q =>
          rw [embedTrapImpl_run_inl_inr, embedTrapImpl_run_inl_inr]
          cases hq : s.1 q with
          | some v => rfl
          | none => simp only [if_neg (hoff q rfl hq)]
  | inr msg => rw [embedTrapImpl_run_inr, embedTrapImpl_run_inr]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Front-draw commute past one trap-sibling embed step (the answer-irrelevant case).** A leading
independent draw `od : ProbComp ρ` feeding a continuation that runs one `embedTrapImpl … j y` step
and then consumes `od`'s value commutes past that step: the step's answer draw and `od` are
independent `ProbComp`s, so they may be drawn in either order (`evalSPMF_bind_comm`).

This is the distribution-level building block of the GPV Step-2 embed-side front-loading: it is what
lets the externally-averaged target `y ← $ᵗ Range` be pushed *past* each non-winner step of the
`simulateQ (embedTrapImpl … j y)` fold (combined with `embedTrapImpl_run_step_indep_of_target`,
which makes every off-`j` step literally independent of `y`).  It is fully generic in the step
constructor `t`, so it applies uniformly to uniform queries, random-oracle cache hits/misses, and
signing steps; the only `y`-dependent step is the single count-`j` miss at which `y` is consumed. -/
theorem embedTrapImpl_frontDraw_commute {ρ γ : Type} (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (od : ProbComp ρ)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ)
    (k : ρ → (((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t ×
      ((Salt × M →ₒ Range).QueryCache × ℕ)) → ProbComp γ) :
    𝒮[od >>= fun r =>
        (embedTrapImpl psf M Salt pk sk j y t).run s >>= fun pq => k r pq] =
      𝒮[(embedTrapImpl psf M Salt pk sk j y t).run s >>= fun pq =>
        od >>= fun r => k r pq] :=
  OracleComp.DeferredSampling.evalSPMF_bind_comm od
    ((embedTrapImpl psf M Salt pk sk j y t).run s) (fun r pq => k r pq)

/-- **Inline-fresh sibling of the trap-sibling embed handler.** Identical state `cache × ℕ`,
counter logic, and never-overwrite discipline as `embedTrapImpl`, but the count-`w` random-oracle
miss is *not* special: at *every* random-oracle miss (winner slot or not) it draws a fresh uniform
image `v ← $ᵗ Range`, caches `v`, and returns `v`.  Equivalently, this is `embedTrapImpl … w y` with
the `if st.2 = w` winner branch deleted — a plain lazy random oracle threading a passive programming
counter (with the same trapdoor-recording signing step as `embedTrapImpl`).

The point of this handler is the GPV Step-2 front-loading: averaging `embedTrapImpl … w y` over an
external target draw `y ← $ᵗ Range` *equals* this inline-fresh run distributionally
(`evalSPMF_frontDraw_embedTrapImpl_eq_embedTrapFresh`), because the count-`w` miss happens at most
once and there caching a front-loaded `y` versus an inline-fresh `v` is the same uniform draw, while
every other step is literally independent of `y` (`embedTrapImpl_run_step_indep_of_target`). -/
@[expose] noncomputable def embedTrapFreshImpl (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × ℕ) ProbComp) :=
  let State := (Salt × M →ₒ Range).QueryCache × ℕ
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          set ((st.1.cacheQuery t v, st.2 + 1) : State)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set ((st.1.cacheQuery (r, msg) c, st.2 + 1) : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshImpl` on a uniform query. -/
lemma embedTrapFreshImpl_run_inl_inl (pk : PK) (sk : SK) (q : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    (embedTrapFreshImpl psf M Salt pk sk (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshImpl` on a random-oracle query. -/
lemma embedTrapFreshImpl_run_inl_inr (pk : PK) (sk : SK) (q : (Salt × M →ₒ Range).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedTrapFreshImpl psf M Salt pk sk (.inl (.inr q))).run s :
        ProbComp (Range × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (match s.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              ((v, (s.1.cacheQuery q v, s.2 + 1)) :
                Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapFreshImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply, StateT.run_set, StateT.run_pure]
  | some v =>
      simp [embedTrapFreshImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshImpl` on a signing query. -/
lemma embedTrapFreshImpl_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedTrapFreshImpl psf M Salt pk sk (.inr msg)).run s :
        ProbComp ((Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), (s.1.cacheQuery (r, msg) c, s.2 + 1)) :
              Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapFreshImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off the winner slot the trap-sibling embed step *is* the inline-fresh step.** Away from the
count-`j` random-oracle miss — i.e. on every uniform query, every random-oracle cache hit, every
off-`j` random-oracle miss (`s.2 ≠ j`), and every signing step — `embedTrapImpl … j y` and
`embedTrapFreshImpl` run *literally identically*: the only place `embedTrapImpl`'s special winner
branch (`if st.2 = j then embed y`) fires is the count-`j` miss, and there both handlers otherwise
draw a fresh uniform and cache it.  This is the per-step bridge through which the front-loading lift
`evalSPMF_frontDraw_embedTrapImpl_eq_embedTrapFresh` commutes the front target draw past every
non-winner step. -/
lemma embedTrapImpl_run_step_eq_embedTrapFresh (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ)
    (hoff : ∀ q : (Salt × M →ₒ Range).Domain, t = .inl (.inr q) → s.1 q = none → s.2 ≠ j) :
    (embedTrapImpl psf M Salt pk sk j y t).run s =
      (embedTrapFreshImpl psf M Salt pk sk t).run s := by
  cases t with
  | inl q =>
      cases q with
      | inl q => rw [embedTrapImpl_run_inl_inl, embedTrapFreshImpl_run_inl_inl]
      | inr q =>
          rw [embedTrapImpl_run_inl_inr, embedTrapFreshImpl_run_inl_inr]
          cases hq : s.1 q with
          | some v => rfl
          | none => simp only [if_neg (hoff q rfl hq)]
  | inr msg => rw [embedTrapImpl_run_inr, embedTrapFreshImpl_run_inr]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step the trap-sibling embed counter never decreases.** Every output state of one
`embedTrapImpl … j y` query step has running counter `≥` the start counter: uniform queries and
random-oracle cache hits leave it fixed, random-oracle misses and signing steps increment it by one.
This is the monotonicity that keeps a post-winner run (`j < s.2`) forever clear of the winner slot,
so `embedTrapImpl … j y` and `embedTrapFreshImpl` coincide there. -/
lemma embedTrapImpl_run_step_count_le (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ)
    (z : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t ×
      ((Salt × M →ₒ Range).QueryCache × ℕ))
    (hz : z ∈ support ((embedTrapImpl psf M Salt pk sk j y t).run s)) :
    s.2 ≤ z.2.2 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapImpl_run_inl_inl, map_eq_bind_pure_comp] at hz
          obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
          simp only [Function.comp_apply] at hh
          subst hh
          rfl
      | inr q =>
          rw [embedTrapImpl_run_inl_inr] at hz
          cases hq : s.1 q with
          | some v =>
              rw [hq, support_pure, Set.mem_singleton_iff] at hz
              subst hz; rfl
          | none =>
              rw [hq, map_eq_bind_pure_comp] at hz
              obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
              simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hh
              subst hh; split_ifs <;> simp
  | inr msg =>
      rw [embedTrapImpl_run_inr] at hz
      obtain ⟨r, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      obtain ⟨c, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [map_eq_bind_pure_comp] at hz
      obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
      simp only [Function.comp_apply] at hh
      subst hh; simp

omit [DecidableEq Range] [Fintype Salt] in
/-- **Post-winner coincidence.** Once the running programming counter has passed the winner slot
(`j < s.2`), the trap-sibling embed handler `embedTrapImpl … j y` and its inline-fresh sibling
`embedTrapFreshImpl` produce *identical* output distributions over any adaptive computation `oa`:
the counter only increases (`embedTrapImpl_run_step_count_le`), so it never returns to `j`, hence
the winner branch never fires and every step agrees (`embedTrapImpl_run_step_eq_embedTrapFresh`).
The external target `y` is irrelevant past the winner. -/
lemma evalSPMF_run_embedTrapImpl_eq_embedTrapFresh_of_lt (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : (Salt × M →ₒ Range).QueryCache × ℕ), j < s.2 →
      𝒮[(simulateQ (embedTrapImpl psf M Salt pk sk j y) oa).run s] =
        𝒮[(simulateQ (embedTrapFreshImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _; rfl
  | query_bind t ob ih =>
      intro s hs
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      have hstep : (embedTrapImpl psf M Salt pk sk j y t).run s =
          (embedTrapFreshImpl psf M Salt pk sk t).run s :=
        embedTrapImpl_run_step_eq_embedTrapFresh psf M Salt pk sk j y t s
          (fun q _ _ => by omega)
      rw [hstep]
      refine evalSPMF_bind_congr (fun p hp => ?_)
      have hcount : s.2 ≤ p.2.2 :=
        embedTrapImpl_run_step_count_le psf M Salt pk sk j y t s p (by rw [hstep]; exact hp)
      exact ih p.1 p.2 (by omega)

omit [DecidableEq Range] [Fintype Salt] in
/-- **The GPV Step-2 front-loading lift.** Averaging the trap-sibling embed run over an *external*
target draw `y ← $ᵗ Range` (drawn before the fold) equals the inline-fresh run `embedTrapFreshImpl`
(which draws a fresh uniform at *every* random-oracle miss, including the winner slot), at any start
state `s`:

`𝒮[y ← $ᵗ Range; (simulateQ (embedTrapImpl … j y) oa).run s]`
`  = 𝒮[(simulateQ embedTrapFreshImpl oa).run s]`.

This is the distribution-level front-loading equality the one-step commute
`embedTrapImpl_frontDraw_commute` lifts across the whole adaptive fold.  Proof by induction on `oa`,
threading the start state (hence the running counter):

* **Pre-winner / off-winner step** (the step is not the count-`j` random-oracle miss — uniform
  query, cache hit, off-`j` miss, or signing): the step is literally `y`-independent and equal to
  the inline-fresh step (`embedTrapImpl_run_step_eq_embedTrapFresh`), so the front `y` draw commutes
  past it (`OracleComp.DeferredSampling.evalSPMF_bind_comm`); the inductive hypothesis rewrites the
  continuation.
* **Winner step** (count-`j` random-oracle miss): the front `y` is the immediately consumed draw —
  `embedTrapImpl … j y` caches and returns `y` while discarding its own fresh draw, so
  `y ← $ᵗ Range; (cache y; return y)` *is* the inline-fresh draw `v ← $ᵗ Range; (cache v; return v)`
  (the discarded draw collapses by `probFailure_uniformSample`).  After this step the counter is
  `j + 1 > j`, so the trap-sibling and inline-fresh continuations coincide
  (`evalSPMF_run_embedTrapImpl_eq_embedTrapFresh_of_lt`). -/
lemma evalSPMF_frontDraw_embedTrapImpl_eq_embedTrapFresh [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : (Salt × M →ₒ Range).QueryCache × ℕ),
      𝒮[(($ᵗ Range : ProbComp Range) >>= fun y =>
          (simulateQ (embedTrapImpl psf M Salt pk sk j y) oa).run s)] =
        𝒮[(simulateQ (embedTrapFreshImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s
      simp only [simulateQ_pure, StateT.run_pure]
      rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
        (probFailure_uniformSample Range)]
  | query_bind t ob ih =>
      intro s
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      -- decide whether this step is the winner (count-`j`) random-oracle miss
      by_cases hwin : ∃ q : (Salt × M →ₒ Range).Domain,
          t = .inl (.inr q) ∧ s.1 q = none ∧ s.2 = j
      · -- **Winner step.** Substitute the front `y` for the inline fresh winner draw.
        obtain ⟨q, rfl, hmiss, hcount⟩ := hwin
        -- Unfold both winner steps: `embedTrapImpl` caches/returns `y` (winner branch, `s.2 = j`),
        -- `embedTrapFreshImpl` caches/returns a fresh `v`.
        rw [show (fun y => (embedTrapImpl psf M Salt pk sk j y (.inl (.inr q))).run s >>= fun p =>
                (simulateQ (embedTrapImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (($ᵗ Range : ProbComp Range) >>= fun _ =>
                  (simulateQ (embedTrapImpl psf M Salt pk sk j y) (ob y)).run
                    (s.1.cacheQuery q y, s.2 + 1))) from by
          funext y
          rw [embedTrapImpl_run_inl_inr, hmiss, hcount]
          simp only [↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]]
        rw [show ((embedTrapFreshImpl psf M Salt pk sk (.inl (.inr q))).run s >>= fun p =>
                (simulateQ (embedTrapFreshImpl psf M Salt pk sk) (ob p.1)).run p.2)
              = (($ᵗ Range : ProbComp Range) >>= fun v =>
                  (simulateQ (embedTrapFreshImpl psf M Salt pk sk) (ob v)).run
                    (s.1.cacheQuery q v, s.2 + 1)) from by
          rw [embedTrapFreshImpl_run_inl_inr, hmiss]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]]
        -- Drop the discarded inner draw on the left, then apply post-winner coincidence per `y`.
        refine evalSPMF_bind_congr' _ (fun y => ?_)
        rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
          (probFailure_uniformSample Range)]
        exact evalSPMF_run_embedTrapImpl_eq_embedTrapFresh_of_lt psf M Salt pk sk j y (ob y)
          (s.1.cacheQuery q y, s.2 + 1) (by omega)
      · -- **Off-winner step.** The step is `y`-independent; commute the front `y` past it.
        push Not at hwin
        have hoff : ∀ q : (Salt × M →ₒ Range).Domain,
            t = .inl (.inr q) → s.1 q = none → s.2 ≠ j := by
          intro q hq hm; exact hwin q hq hm
        -- rewrite the step (for every `y`) to the inline-fresh step
        rw [show (fun y => (embedTrapImpl psf M Salt pk sk j y t).run s >>= fun p =>
                (simulateQ (embedTrapImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (embedTrapFreshImpl psf M Salt pk sk t).run s >>= fun p =>
                (simulateQ (embedTrapImpl psf M Salt pk sk j y) (ob p.1)).run p.2) from by
          funext y
          rw [embedTrapImpl_run_step_eq_embedTrapFresh psf M Salt pk sk j y t s hoff]]
        -- commute the front `y` past the now-`y`-free fresh step
        rw [OracleComp.DeferredSampling.evalSPMF_bind_comm ($ᵗ Range : ProbComp Range)
          ((embedTrapFreshImpl psf M Salt pk sk t).run s)
          (fun y p => (simulateQ (embedTrapImpl psf M Salt pk sk j y) (ob p.1)).run p.2)]
        -- the continuation is the front-loaded run; the inductive hypothesis rewrites it
        refine evalSPMF_bind_congr' _ (fun p => ?_)
        exact ih p.1 p.2

/-- **Index-augmented trap-sibling embed handler.** Identical to `embedTrapImpl … j y` on its
`cache × ℕ` state component (winner branch `if st.2 = j then embed y` included), but additionally
threads a passive insertion-index table `(Salt × M) → Option ℕ`: at each programming event
(random-oracle miss or signing step) it records the current counter value into the index table at
the freshly written key.  The index table is never *read* during the run, so it is distributionally
passive: projecting it away recovers `embedTrapImpl … j y` exactly (`embedTrapIdxImpl_proj`).

The point of the augmentation is that at the count-`j` winner random-oracle miss the cached image is
`y` *and* the recorded index is `j`: this is the run-only witness that the forged point being the
embedded winner slot (`cache(forged) = some y`) coincides with `idx(forged) = some j`. -/
@[expose] noncomputable def embedTrapIdxImpl (pk : PK) (sk : SK) (j : ℕ) (y : Range) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) ProbComp) :=
  let State := ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          if st.1.2 = j then
            set (((st.1.1.cacheQuery t y, st.1.2 + 1),
              fun t' => if t' = t then some st.1.2 else st.2 t') : State)
            pure y
          else
            set (((st.1.1.cacheQuery t v, st.1.2 + 1),
              fun t' => if t' = t then some st.1.2 else st.2 t') : State)
            pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set (((st.1.1.cacheQuery (r, msg) c, st.1.2 + 1),
        fun t' => if t' = (r, msg) then some st.1.2 else st.2 t') : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxImpl` on a uniform query. -/
lemma embedTrapIdxImpl_run_inl_inl (pk : PK) (sk : SK) (j : ℕ) (y : Range) (q : unifSpec.Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    (embedTrapIdxImpl psf M Salt pk sk j y (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxImpl` on a random-oracle query. -/
lemma embedTrapIdxImpl_run_inl_inr (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (q : (Salt × M →ₒ Range).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    ((embedTrapIdxImpl psf M Salt pk sk j y (.inl (.inr q))).run s :
        ProbComp (Range × (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))) =
      (match s.1.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              (if s.1.2 = j then
                  (y, ((s.1.1.cacheQuery q y, s.1.2 + 1),
                    fun t' => if t' = q then some s.1.2 else s.2 t'))
                else
                  (v, ((s.1.1.cacheQuery q v, s.1.2 + 1),
                    fun t' => if t' = q then some s.1.2 else s.2 t')) :
                Range × (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapIdxImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply]
      refine bind_congr fun v => ?_
      split_ifs with hb <;> simp [StateT.run_set]
  | some v =>
      simp [embedTrapIdxImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxImpl` on a signing query. -/
lemma embedTrapIdxImpl_run_inr (pk : PK) (sk : SK) (j : ℕ) (y : Range) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    ((embedTrapIdxImpl psf M Salt pk sk j y (.inr msg)).run s :
        ProbComp ((Salt × Domain) ×
          (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), ((s.1.1.cacheQuery (r, msg) c, s.1.2 + 1),
              fun t' => if t' = (r, msg) then some s.1.2 else s.2 t')) :
              Domain → (Salt × Domain) ×
                (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapIdxImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query passive projection of `embedTrapIdxImpl`.** Dropping the insertion-index table from
one `embedTrapIdxImpl` query step recovers the corresponding `embedTrapImpl … j y` step. -/
lemma embedTrapIdxImpl_proj (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
        (Salt × M →ₒ Range).QueryCache × ℕ) <$>
        (embedTrapIdxImpl psf M Salt pk sk j y t).run s =
      (embedTrapImpl psf M Salt pk sk j y t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapIdxImpl_run_inl_inl, embedTrapImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [embedTrapIdxImpl_run_inl_inr, embedTrapImpl_run_inl_inr]
          cases s.1.1 q with
          | none =>
              simp only [Functor.map_map]
              refine congrArg (fun f => f <$> ($ᵗ Range : ProbComp Range)) ?_
              funext v; split_ifs <;> rfl
          | some v => simp [Prod.map]
  | inr msg =>
      rw [embedTrapIdxImpl_run_inr, embedTrapImpl_run_inr]
      simp [Functor.map_map, Prod.map, map_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level passive projection of `embedTrapIdxImpl`.** Dropping the insertion-index table from
the full simulated run of `embedTrapIdxImpl` over `oa` recovers the run of `embedTrapImpl … j y`. -/
lemma map_run_embedTrapIdxImpl_proj (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
        (Salt × M →ₒ Range).QueryCache × ℕ) <$>
        (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s =
      (simulateQ (embedTrapImpl psf M Salt pk sk j y) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
      (Salt × M →ₒ Range).QueryCache × ℕ)
    (embedTrapIdxImpl_proj psf M Salt pk sk j y) oa s

/-- **Index-augmented inline-fresh embed handler.** Identical to `embedTrapFreshImpl` on its
`cache × ℕ` state component, but additionally threads a passive insertion-index table
`(Salt × M) → Option ℕ`: at each programming event (random-oracle miss or signing step) it records
the current counter value into the index table at the freshly written key.  The index table is
never *read* during the run, so it is distributionally passive: projecting it away recovers
`embedTrapFreshImpl` exactly (`embedTrapFreshIdxImpl_proj`).

This is the embed-side mirror of `progGameRunImplCombinedTrapCount`'s index instrument: both record,
at each fresh random-oracle miss, the running counter value into an index table keyed at the missed
point.  It is the run-only bookkeeping that replaces the `y`-reading win literal
`cache(forged) = some y` of `embedTrapImpl` by the run-only predicate `idx(forged) = some j`. -/
@[expose] noncomputable def embedTrapFreshIdxImpl (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) ProbComp) :=
  let State := ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          set (((st.1.1.cacheQuery t v, st.1.2 + 1),
            fun t' => if t' = t then some st.1.2 else st.2 t') : State)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set (((st.1.1.cacheQuery (r, msg) c, st.1.2 + 1),
        fun t' => if t' = (r, msg) then some st.1.2 else st.2 t') : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxImpl` on a uniform query. -/
lemma embedTrapFreshIdxImpl_run_inl_inl (pk : PK) (sk : SK) (q : unifSpec.Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    (embedTrapFreshIdxImpl psf M Salt pk sk (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxImpl` on a random-oracle query. -/
lemma embedTrapFreshIdxImpl_run_inl_inr (pk : PK) (sk : SK) (q : (Salt × M →ₒ Range).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    ((embedTrapFreshIdxImpl psf M Salt pk sk (.inl (.inr q))).run s :
        ProbComp (Range × (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))) =
      (match s.1.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              ((v, ((s.1.1.cacheQuery q v, s.1.2 + 1),
                fun t' => if t' = q then some s.1.2 else s.2 t')) :
                Range × (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapFreshIdxImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply, StateT.run_set, StateT.run_pure]
  | some v =>
      simp [embedTrapFreshIdxImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxImpl` on a signing query. -/
lemma embedTrapFreshIdxImpl_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    ((embedTrapFreshIdxImpl psf M Salt pk sk (.inr msg)).run s :
        ProbComp ((Salt × Domain) ×
          (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), ((s.1.1.cacheQuery (r, msg) c, s.1.2 + 1),
              fun t' => if t' = (r, msg) then some s.1.2 else s.2 t')) :
              Domain → (Salt × Domain) ×
                (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapFreshIdxImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query passive projection of `embedTrapFreshIdxImpl`.** Dropping the insertion-index table
from one `embedTrapFreshIdxImpl` query step recovers the corresponding `embedTrapFreshImpl` step:
the index table is written by a deterministic update that does not feed the answer draw or the
`cache × ℕ` update, so it is distributionally passive. -/
lemma embedTrapFreshIdxImpl_proj (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
        (Salt × M →ₒ Range).QueryCache × ℕ) <$>
        (embedTrapFreshIdxImpl psf M Salt pk sk t).run s =
      (embedTrapFreshImpl psf M Salt pk sk t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapFreshIdxImpl_run_inl_inl, embedTrapFreshImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [embedTrapFreshIdxImpl_run_inl_inr, embedTrapFreshImpl_run_inl_inr]
          cases s.1.1 q with
          | none => simp [map_eq_bind_pure_comp, Prod.map]
          | some v => simp [Prod.map]
  | inr msg =>
      rw [embedTrapFreshIdxImpl_run_inr, embedTrapFreshImpl_run_inr]
      simp [Functor.map_map, Prod.map, map_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level passive projection of `embedTrapFreshIdxImpl`.** Dropping the insertion-index table
from the full simulated run of `embedTrapFreshIdxImpl` over `oa` recovers the run of
`embedTrapFreshImpl` from the projected start state.  Transports the per-query
`embedTrapFreshIdxImpl_proj` through the whole computation via
`map_run_simulateQ_eq_of_query_map_eq`. -/
lemma map_run_embedTrapFreshIdxImpl_proj (pk : PK) (sk : SK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
        (Salt × M →ₒ Range).QueryCache × ℕ) <$>
        (simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) oa).run s =
      (simulateQ (embedTrapFreshImpl psf M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
      (Salt × M →ₒ Range).QueryCache × ℕ)
    (embedTrapFreshIdxImpl_proj psf M Salt pk sk) oa s

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off the winner slot the idx-augmented trap-sibling embed step *is* the idx-augmented
inline-fresh step.** Away from the count-`j` random-oracle miss the special winner branch never
fires, so `embedTrapIdxImpl … j y` and `embedTrapFreshIdxImpl` run identically (the idx-table update
is identical on both sides).  Idx-augmented mirror of `embedTrapImpl_run_step_eq_embedTrapFresh`. -/
lemma embedTrapIdxImpl_run_step_eq_embedTrapFreshIdx (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))
    (hoff : ∀ q : (Salt × M →ₒ Range).Domain, t = .inl (.inr q) → s.1.1 q = none → s.1.2 ≠ j) :
    (embedTrapIdxImpl psf M Salt pk sk j y t).run s =
      (embedTrapFreshIdxImpl psf M Salt pk sk t).run s := by
  cases t with
  | inl q =>
      cases q with
      | inl q => rw [embedTrapIdxImpl_run_inl_inl, embedTrapFreshIdxImpl_run_inl_inl]
      | inr q =>
          rw [embedTrapIdxImpl_run_inl_inr, embedTrapFreshIdxImpl_run_inl_inr]
          cases hq : s.1.1 q with
          | some v => rfl
          | none => simp only [if_neg (hoff q rfl hq)]
  | inr msg => rw [embedTrapIdxImpl_run_inr, embedTrapFreshIdxImpl_run_inr]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step the idx-augmented trap-sibling embed counter never decreases.** Idx-augmented mirror
of `embedTrapImpl_run_step_count_le`. -/
lemma embedTrapIdxImpl_run_step_count_le (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))
    (z : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t ×
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))
    (hz : z ∈ support ((embedTrapIdxImpl psf M Salt pk sk j y t).run s)) :
    s.1.2 ≤ z.2.1.2 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapIdxImpl_run_inl_inl, map_eq_bind_pure_comp] at hz
          obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
          simp only [Function.comp_apply] at hh
          subst hh
          rfl
      | inr q =>
          rw [embedTrapIdxImpl_run_inl_inr] at hz
          cases hq : s.1.1 q with
          | some v =>
              rw [hq, support_pure, Set.mem_singleton_iff] at hz
              subst hz; rfl
          | none =>
              rw [hq, map_eq_bind_pure_comp] at hz
              obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
              simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hh
              subst hh; split_ifs <;> simp
  | inr msg =>
      rw [embedTrapIdxImpl_run_inr] at hz
      obtain ⟨r, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      obtain ⟨c, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [map_eq_bind_pure_comp] at hz
      obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
      simp only [Function.comp_apply] at hh
      subst hh; simp

omit [DecidableEq Range] [Fintype Salt] in
/-- **Post-winner coincidence (idx-augmented).** Once the running counter has passed the winner slot
(`j < s.1.2`), `embedTrapIdxImpl … j y` and `embedTrapFreshIdxImpl` produce identical output
distributions over any `oa`.  Idx-augmented mirror of
`evalSPMF_run_embedTrapImpl_eq_embedTrapFresh_of_lt`. -/
lemma evalSPMF_run_embedTrapIdxImpl_eq_embedTrapFreshIdx_of_lt (pk : PK) (sk : SK) (j : ℕ)
    (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)), j < s.1.2 →
      𝒮[(simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s] =
        𝒮[(simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _; rfl
  | query_bind t ob ih =>
      intro s hs
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      have hstep : (embedTrapIdxImpl psf M Salt pk sk j y t).run s =
          (embedTrapFreshIdxImpl psf M Salt pk sk t).run s :=
        embedTrapIdxImpl_run_step_eq_embedTrapFreshIdx psf M Salt pk sk j y t s
          (fun q _ _ => by omega)
      rw [hstep]
      refine evalSPMF_bind_congr (fun p hp => ?_)
      have hcount : s.1.2 ≤ p.2.1.2 :=
        embedTrapIdxImpl_run_step_count_le psf M Salt pk sk j y t s p (by rw [hstep]; exact hp)
      exact ih p.1 p.2 (by omega)

omit [DecidableEq Range] [Fintype Salt] in
/-- **The idx-augmented GPV Step-2 front-loading lift.** Averaging the idx-augmented trap-sibling
embed run over an external target draw `y ← $ᵗ Range` equals the idx-augmented inline-fresh run
`embedTrapFreshIdxImpl`.  Idx-augmented mirror of
`evalSPMF_frontDraw_embedTrapImpl_eq_embedTrapFresh`: off-winner steps commute the front `y` past
`y`-independent steps; at the count-`j` winner miss the front `y` is the immediately consumed draw
(cached at the slot tagged `idx = some j`), so the front `y` *is* the inline-fresh winner draw, and
post-winner the two runs coincide (`evalSPMF_run_embedTrapIdxImpl_eq_embedTrapFreshIdx_of_lt`). -/
lemma evalSPMF_frontDraw_embedTrapIdxImpl_eq_embedTrapFreshIdx [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)),
      𝒮[(($ᵗ Range : ProbComp Range) >>= fun y =>
          (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s)] =
        𝒮[(simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s
      simp only [simulateQ_pure, StateT.run_pure]
      rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
        (probFailure_uniformSample Range)]
  | query_bind t ob ih =>
      intro s
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      by_cases hwin : ∃ q : (Salt × M →ₒ Range).Domain,
          t = .inl (.inr q) ∧ s.1.1 q = none ∧ s.1.2 = j
      · -- **Winner step.** Substitute the front `y` for the inline fresh winner draw.
        obtain ⟨q, rfl, hmiss, hcount⟩ := hwin
        rw [show (fun y => (embedTrapIdxImpl psf M Salt pk sk j y (.inl (.inr q))).run s >>=
                fun p => (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (($ᵗ Range : ProbComp Range) >>= fun _ =>
                  (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (ob y)).run
                    ((s.1.1.cacheQuery q y, s.1.2 + 1),
                      fun t' => if t' = q then some s.1.2 else s.2 t'))) from by
          funext y
          rw [embedTrapIdxImpl_run_inl_inr, hmiss, hcount]
          simp only [↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]]
        rw [show ((embedTrapFreshIdxImpl psf M Salt pk sk (.inl (.inr q))).run s >>= fun p =>
                (simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) (ob p.1)).run p.2)
              = (($ᵗ Range : ProbComp Range) >>= fun v =>
                  (simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) (ob v)).run
                    ((s.1.1.cacheQuery q v, s.1.2 + 1),
                      fun t' => if t' = q then some s.1.2 else s.2 t')) from by
          rw [embedTrapFreshIdxImpl_run_inl_inr, hmiss]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]]
        refine evalSPMF_bind_congr' _ (fun y => ?_)
        rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
          (probFailure_uniformSample Range)]
        exact evalSPMF_run_embedTrapIdxImpl_eq_embedTrapFreshIdx_of_lt psf M Salt pk sk j y (ob y)
          ((s.1.1.cacheQuery q y, s.1.2 + 1),
            fun t' => if t' = q then some s.1.2 else s.2 t') (by simp only [hcount]; omega)
      · -- **Off-winner step.** The step is `y`-independent; commute the front `y` past it.
        push Not at hwin
        have hoff : ∀ q : (Salt × M →ₒ Range).Domain,
            t = .inl (.inr q) → s.1.1 q = none → s.1.2 ≠ j := by
          intro q hq hm; exact hwin q hq hm
        rw [show (fun y => (embedTrapIdxImpl psf M Salt pk sk j y t).run s >>= fun p =>
                (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (embedTrapFreshIdxImpl psf M Salt pk sk t).run s >>= fun p =>
                (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (ob p.1)).run p.2) from by
          funext y
          rw [embedTrapIdxImpl_run_step_eq_embedTrapFreshIdx psf M Salt pk sk j y t s hoff]]
        rw [OracleComp.DeferredSampling.evalSPMF_bind_comm ($ᵗ Range : ProbComp Range)
          ((embedTrapFreshIdxImpl psf M Salt pk sk t).run s)
          (fun y p => (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (ob p.1)).run p.2)]
        refine evalSPMF_bind_congr' _ (fun p => ?_)
        exact ih p.1 p.2

open Classical in
omit [Fintype Salt] in
/-- **Index-augmented winner-slot restriction of the per-target embedding win is a lower bound.**
Running the embed game on the index-augmented handler `embedTrapIdxImpl … j y` and conjoining the
win predicate with the run-only winner-slot witness `idx(forged) = some j` can only *decrease* the
win mass relative to the un-augmented per-target win on `embedTrapImpl … j y`:

* the index table is passive, so the augmented run projects onto the un-augmented run
  (`map_run_embedTrapIdxImpl_proj`) — the win predicate and the trapdoor draw read only the shared
  output/cache components;
* the extra conjunct `idx(forged) = some j` only restricts the event (`probOutput_bind_mono`).

Averaged over the front target `y ← $ᵗ Range` this gives the winner-slot-restricted lower bound
that the trap-count run's index-tagged trap mass couples to. -/
lemma reservoir_embed_winnerIdx_le [DecidableEq Domain] [Inhabited Range] (pk : PK) (sk : SK)
    (j : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    (∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
        Pr[= true | (do
          let r ← (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (adv.main pk)).run
            (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none))
          let x ← psf.trapdoorSample pk sk ((r.2.1.1 (r.1.2.1, r.1.1)).getD y)
          pure (decide (r.1.2.2 = x) && decide (r.2.1.1 (r.1.2.1, r.1.1) = some y) &&
            decide (r.2.2 (r.1.2.1, r.1.1) = some j)) : ProbComp Bool)]) ≤
      Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk ((r.2.1 (r.1.2.1, r.1.1)).getD y)
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  rw [probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun y => ?_
  refine mul_le_mul' le_rfl ?_
  -- Rewrite the un-augmented embed run as the projection of the index-augmented run.
  rw [show (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
        ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
      = Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
          (Salt × M →ₒ Range).QueryCache × ℕ) <$>
        (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (adv.main pk)).run
          (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none)) from
    (map_run_embedTrapIdxImpl_proj psf M Salt pk sk j y (adv.main pk)
      (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none))).symm]
  rw [bind_map_left]
  -- Both sides now share the index-augmented run; compare per output `r`.
  refine probOutput_bind_mono (fun r _ => ?_)
  simp only [Prod.map, id_eq]
  -- Per output `r` the trapdoor draws agree; the augmented win adds the conjunct
  -- `idx(forged) = some j`, which can only restrict.
  refine probOutput_bind_mono (fun x _ => ?_)
  simp only [probOutput_pure]
  split_ifs with h1 h2 <;> first | rfl | simp_all

omit [DecidableEq Range] [Fintype Salt] in
/-- **Embed-side index/cache lockstep invariant.** On the index-augmented embed run
`embedTrapIdxImpl … j y`, the cache table and the insertion-index table agree on which keys are
recorded: a key has a cached random-oracle value iff it has a recorded insertion index.  Both tables
are written by the *same* conditional update at each programming event (random-oracle miss or
signing step) and are both untouched on uniform queries and cache hits, so their per-key
`isSome` status stays in lockstep through the whole adaptive fold.  In particular
`idx(forged) = some j` forces
`cache(forged) ≠ none`, which pins the trapdoor draw `trapdoorSample pk sk ((cache forged).getD y)`
to the cached image, eliminating the dependence on the front target `y`. -/
lemma embedTrapIdxImpl_idx_iff_cache (pk : PK) (sk : SK) (j : ℕ) (y : Range) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)),
      (∀ k, s.1.1 k ≠ none ↔ s.2 k ≠ none) →
      ∀ z ∈ support ((simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s),
        ∀ k, z.2.1.1 k ≠ none ↔ z.2.2 k ≠ none := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hs
  | query_bind t mx ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz2⟩
      rcases t with (n | mc) | msg
      · rw [embedTrapIdxImpl_run_inl_inl, map_eq_bind_pure_comp] at hps
        obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hh
        have hps' : pst = s := (Prod.ext_iff.mp hh).2
        refine ih pv pst ?_ z hz2
        rw [hps']; exact hs
      · rw [embedTrapIdxImpl_run_inl_inr] at hps
        cases hq : s.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            refine ih pv pst ?_ z hz2
            rw [hpst]; exact hs
        | none =>
            rw [hq, map_eq_bind_pure_comp] at hps
            obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
            simp only [Function.comp_apply] at hh
            have hps' : pst = ((if s.1.2 = j then s.1.1.cacheQuery mc y
                  else s.1.1.cacheQuery mc v, s.1.2 + 1),
                fun t' => if t' = mc then some s.1.2 else s.2 t') := by
              have h2 := (Prod.ext_iff.mp hh).2
              by_cases hb : s.1.2 = j <;> simp only [hb, if_true, if_false] at h2 ⊢ <;>
                exact h2
            refine ih pv pst ?_ z hz2
            intro k
            rw [hps']
            by_cases hk : k = mc
            · subst hk
              by_cases hb : s.1.2 = j <;> simp [hb, QueryCache.cacheQuery_self]
            · by_cases hb : s.1.2 = j <;>
                simp only [hb, if_true, if_false, if_neg hk,
                  QueryCache.cacheQuery_of_ne _ _ hk] <;> exact hs k
      · rw [embedTrapIdxImpl_run_inr] at hps
        obtain ⟨r, -, hps⟩ := (mem_support_bind_iff _ _ _).1 hps
        obtain ⟨c, -, hps⟩ := (mem_support_bind_iff _ _ _).1 hps
        rw [map_eq_bind_pure_comp] at hps
        obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hh
        have hps' : pst = ((s.1.1.cacheQuery (r, msg) c, s.1.2 + 1),
            fun t' => if t' = (r, msg) then some s.1.2 else s.2 t') := (Prod.ext_iff.mp hh).2
        refine ih pv pst ?_ z hz2
        intro k
        rw [hps']
        by_cases hk : k = (r, msg)
        · subst hk; simp [QueryCache.cacheQuery_self]
        · simp only [if_neg hk, QueryCache.cacheQuery_of_ne _ _ hk]; exact hs k

end GPVHashAndSign
