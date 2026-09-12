/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.TrapCount

/-! # GPV Hash-and-Sign: Index-Embedding Handlers

The signed-set-augmented index embed handlers realizing the pre-sampled
embed-index programming of the random oracle.
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

/-! ### Signed-set-augmented index embed handlers

The index-augmented embed handlers `embedTrapIdxImpl` / `embedTrapFreshIdxImpl` track the
insertion-index table but *not* which messages were signed.  The `…Sig` variants below additionally
thread a passive *signed-set* `Finset M`: the signing branch inserts the queried message, while
random-oracle misses and uniform queries leave it untouched.  The signed set is never *read* during
the run, so it is distributionally passive: projecting it away recovers the un-`Sig` handler exactly
(`map_run_embedTrapIdxSigImpl_proj` / `map_run_embedTrapFreshIdxSigImpl_proj`).  Its purpose is the
GPV Step-2 freshness recovery (`embedTrapIdxSigImpl_fresh_idx_cache_eq`): on a key whose message was
never signed, an `idx = some j` tag forces the cached image to be the embedded target `y`. -/

/-- **Signed-set-augmented index-augmented trap-sibling embed handler.** Identical to
`embedTrapIdxImpl … j y` on its `(cache × ℕ) × idxTable` state component (winner branch
`if st.1.2 = j then embed y` included), but additionally threads a passive signed-set `Finset M`:
the signing branch inserts the queried message; random-oracle misses and uniform queries leave the
signed set unchanged.  The signed set is never *read* during the run, so it is distributionally
passive: projecting it away recovers `embedTrapIdxImpl … j y` exactly
(`embedTrapIdxSigImpl_proj`). -/
@[expose] noncomputable def embedTrapIdxSigImpl (pk : PK) (sk : SK) (j : ℕ) (y : Range) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
        ProbComp) :=
  let State := (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1.1.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          if st.1.1.2 = j then
            set (((((st.1.1.1.cacheQuery t y, st.1.1.2 + 1),
              fun t' => if t' = t then some st.1.1.2 else st.1.2 t'), st.2)) : State)
            pure y
          else
            set (((((st.1.1.1.cacheQuery t v, st.1.1.2 + 1),
              fun t' => if t' = t then some st.1.1.2 else st.1.2 t'), st.2)) : State)
            pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set (((((st.1.1.1.cacheQuery (r, msg) c, st.1.1.2 + 1),
        fun t' => if t' = (r, msg) then some st.1.1.2 else st.1.2 t'),
        insert msg st.2)) : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxSigImpl` on a uniform query. -/
lemma embedTrapIdxSigImpl_run_inl_inl (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (q : unifSpec.Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    (embedTrapIdxSigImpl psf M Salt pk sk j y (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxSigImpl` on a random-oracle query. -/
lemma embedTrapIdxSigImpl_run_inl_inr (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (q : (Salt × M →ₒ Range).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    ((embedTrapIdxSigImpl psf M Salt pk sk j y (.inl (.inr q))).run s :
        ProbComp (Range ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))) =
      (match s.1.1.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              (if s.1.1.2 = j then
                  (y, (((s.1.1.1.cacheQuery q y, s.1.1.2 + 1),
                    fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2))
                else
                  (v, (((s.1.1.1.cacheQuery q v, s.1.1.2 + 1),
                    fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2)) :
                Range ×
                  ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1.1.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapIdxSigImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply]
      refine bind_congr fun v => ?_
      split_ifs with hb <;> simp [StateT.run_set]
  | some v =>
      simp [embedTrapIdxSigImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxSigImpl` on a signing query. -/
lemma embedTrapIdxSigImpl_run_inr (pk : PK) (sk : SK) (j : ℕ) (y : Range) (msg : M)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    ((embedTrapIdxSigImpl psf M Salt pk sk j y (.inr msg)).run s :
        ProbComp ((Salt × Domain) ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), (((s.1.1.1.cacheQuery (r, msg) c, s.1.1.2 + 1),
              fun t' => if t' = (r, msg) then some s.1.1.2 else s.1.2 t'), insert msg s.2)) :
              Domain → (Salt × Domain) ×
                ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapIdxSigImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query passive projection of `embedTrapIdxSigImpl`.** Dropping the signed set from one
`embedTrapIdxSigImpl` query step recovers the corresponding `embedTrapIdxImpl … j y` step. -/
lemma embedTrapIdxSigImpl_proj (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    Prod.map id (Prod.fst :
        (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
          ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (embedTrapIdxSigImpl psf M Salt pk sk j y t).run s =
      (embedTrapIdxImpl psf M Salt pk sk j y t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapIdxSigImpl_run_inl_inl, embedTrapIdxImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [embedTrapIdxSigImpl_run_inl_inr, embedTrapIdxImpl_run_inl_inr]
          cases s.1.1.1 q with
          | none =>
              simp only [Functor.map_map]
              refine congrArg (fun f => f <$> ($ᵗ Range : ProbComp Range)) ?_
              funext v; split_ifs <;> rfl
          | some v => simp [Prod.map]
  | inr msg =>
      rw [embedTrapIdxSigImpl_run_inr, embedTrapIdxImpl_run_inr]
      simp [Functor.map_map, Prod.map, map_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level passive projection of `embedTrapIdxSigImpl`.** Dropping the signed set from the full
simulated run of `embedTrapIdxSigImpl` over `oa` recovers the run of `embedTrapIdxImpl … j y`. -/
lemma map_run_embedTrapIdxSigImpl_proj (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    Prod.map id (Prod.fst :
        (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
          ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s =
      (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
      ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))
    (embedTrapIdxSigImpl_proj psf M Salt pk sk j y) oa s

/-- **Signed-set-augmented index-augmented inline-fresh embed handler.** Identical to
`embedTrapFreshIdxImpl` on its `(cache × ℕ) × idxTable` state component, but additionally threads a
passive signed-set `Finset M`: the signing branch inserts the queried message; random-oracle misses
and uniform queries leave the signed set unchanged.  The signed set is never *read* during the run,
so it is distributionally passive: projecting it away recovers `embedTrapFreshIdxImpl` exactly
(`embedTrapFreshIdxSigImpl_proj`). -/
@[expose] noncomputable def embedTrapFreshIdxSigImpl (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
        ProbComp) :=
  let State := (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1.1.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          set (((((st.1.1.1.cacheQuery t v, st.1.1.2 + 1),
            fun t' => if t' = t then some st.1.1.2 else st.1.2 t'), st.2)) : State)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set (((((st.1.1.1.cacheQuery (r, msg) c, st.1.1.2 + 1),
        fun t' => if t' = (r, msg) then some st.1.1.2 else st.1.2 t'),
        insert msg st.2)) : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxSigImpl` on a uniform query. -/
lemma embedTrapFreshIdxSigImpl_run_inl_inl (pk : PK) (sk : SK) (q : unifSpec.Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    (embedTrapFreshIdxSigImpl psf M Salt pk sk (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxSigImpl` on a random-oracle query. -/
lemma embedTrapFreshIdxSigImpl_run_inl_inr (pk : PK) (sk : SK) (q : (Salt × M →ₒ Range).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    ((embedTrapFreshIdxSigImpl psf M Salt pk sk (.inl (.inr q))).run s :
        ProbComp (Range ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))) =
      (match s.1.1.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              ((v, (((s.1.1.1.cacheQuery q v, s.1.1.2 + 1),
                fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2)) :
                Range ×
                  ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1.1.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapFreshIdxSigImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply, StateT.run_set, StateT.run_pure]
  | some v =>
      simp [embedTrapFreshIdxSigImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxSigImpl` on a signing query. -/
lemma embedTrapFreshIdxSigImpl_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    ((embedTrapFreshIdxSigImpl psf M Salt pk sk (.inr msg)).run s :
        ProbComp ((Salt × Domain) ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), (((s.1.1.1.cacheQuery (r, msg) c, s.1.1.2 + 1),
              fun t' => if t' = (r, msg) then some s.1.1.2 else s.1.2 t'), insert msg s.2)) :
              Domain → (Salt × Domain) ×
                ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapFreshIdxSigImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query passive projection of `embedTrapFreshIdxSigImpl`.** Dropping the signed set from one
`embedTrapFreshIdxSigImpl` query step recovers the corresponding `embedTrapFreshIdxImpl` step. -/
lemma embedTrapFreshIdxSigImpl_proj (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    Prod.map id (Prod.fst :
        (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
          ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (embedTrapFreshIdxSigImpl psf M Salt pk sk t).run s =
      (embedTrapFreshIdxImpl psf M Salt pk sk t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapFreshIdxSigImpl_run_inl_inl, embedTrapFreshIdxImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [embedTrapFreshIdxSigImpl_run_inl_inr, embedTrapFreshIdxImpl_run_inl_inr]
          cases s.1.1.1 q with
          | none => simp [map_eq_bind_pure_comp, Prod.map]
          | some v => simp [Prod.map]
  | inr msg =>
      rw [embedTrapFreshIdxSigImpl_run_inr, embedTrapFreshIdxImpl_run_inr]
      simp [Functor.map_map, Prod.map, map_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level passive projection of `embedTrapFreshIdxSigImpl`.** Dropping the signed set from the
full simulated run of `embedTrapFreshIdxSigImpl` over `oa` recovers the run of
`embedTrapFreshIdxImpl` from the projected start state. -/
lemma map_run_embedTrapFreshIdxSigImpl_proj (pk : PK) (sk : SK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    Prod.map id (Prod.fst :
        (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
          ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s =
      (simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
      ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))
    (embedTrapFreshIdxSigImpl_proj psf M Salt pk sk) oa s

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off the winner slot the signed-set-augmented trap-sibling embed step *is* the signed-set
inline-fresh step.** Away from the count-`j` random-oracle miss the special winner branch never
fires, so `embedTrapIdxSigImpl … j y` and `embedTrapFreshIdxSigImpl` run identically (the idx-table
and signed-set updates are identical on both sides).  Signed-set mirror of
`embedTrapIdxImpl_run_step_eq_embedTrapFreshIdx`. -/
lemma embedTrapIdxSigImpl_run_step_eq_embedTrapFreshIdxSig (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
    (hoff : ∀ q : (Salt × M →ₒ Range).Domain, t = .inl (.inr q) → s.1.1.1 q = none → s.1.1.2 ≠ j) :
    (embedTrapIdxSigImpl psf M Salt pk sk j y t).run s =
      (embedTrapFreshIdxSigImpl psf M Salt pk sk t).run s := by
  cases t with
  | inl q =>
      cases q with
      | inl q => rw [embedTrapIdxSigImpl_run_inl_inl, embedTrapFreshIdxSigImpl_run_inl_inl]
      | inr q =>
          rw [embedTrapIdxSigImpl_run_inl_inr, embedTrapFreshIdxSigImpl_run_inl_inr]
          cases hq : s.1.1.1 q with
          | some v => rfl
          | none => simp only [if_neg (hoff q rfl hq)]
  | inr msg => rw [embedTrapIdxSigImpl_run_inr, embedTrapFreshIdxSigImpl_run_inr]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step the signed-set-augmented trap-sibling embed counter never decreases.** Signed-set
mirror of `embedTrapIdxImpl_run_step_count_le`. -/
lemma embedTrapIdxSigImpl_run_step_count_le (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
    (z : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t ×
      ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))
    (hz : z ∈ support ((embedTrapIdxSigImpl psf M Salt pk sk j y t).run s)) :
    s.1.1.2 ≤ z.2.1.1.2 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapIdxSigImpl_run_inl_inl, map_eq_bind_pure_comp] at hz
          obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
          simp only [Function.comp_apply] at hh
          subst hh
          rfl
      | inr q =>
          rw [embedTrapIdxSigImpl_run_inl_inr] at hz
          cases hq : s.1.1.1 q with
          | some v =>
              rw [hq, support_pure, Set.mem_singleton_iff] at hz
              subst hz; rfl
          | none =>
              rw [hq, map_eq_bind_pure_comp] at hz
              obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
              simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hh
              subst hh; split_ifs <;> simp
  | inr msg =>
      rw [embedTrapIdxSigImpl_run_inr] at hz
      obtain ⟨r, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      obtain ⟨c, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [map_eq_bind_pure_comp] at hz
      obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
      simp only [Function.comp_apply] at hh
      subst hh; simp

omit [DecidableEq Range] [Fintype Salt] in
/-- **Post-winner coincidence (signed-set-augmented).** Once the running counter has passed the
winner slot (`j < s.1.1.2`), `embedTrapIdxSigImpl … j y` and `embedTrapFreshIdxSigImpl` produce
identical output distributions over any `oa`.  Signed-set mirror of
`evalSPMF_run_embedTrapIdxImpl_eq_embedTrapFreshIdx_of_lt`. -/
lemma evalSPMF_run_embedTrapIdxSigImpl_eq_embedTrapFreshIdxSig_of_lt (pk : PK) (sk : SK) (j : ℕ)
    (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
      j < s.1.1.2 →
      𝒮[(simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s] =
        𝒮[(simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _; rfl
  | query_bind t ob ih =>
      intro s hs
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      have hstep : (embedTrapIdxSigImpl psf M Salt pk sk j y t).run s =
          (embedTrapFreshIdxSigImpl psf M Salt pk sk t).run s :=
        embedTrapIdxSigImpl_run_step_eq_embedTrapFreshIdxSig psf M Salt pk sk j y t s
          (fun q _ _ => by omega)
      rw [hstep]
      refine evalSPMF_bind_congr (fun p hp => ?_)
      have hcount : s.1.1.2 ≤ p.2.1.1.2 :=
        embedTrapIdxSigImpl_run_step_count_le psf M Salt pk sk j y t s p (by rw [hstep]; exact hp)
      exact ih p.1 p.2 (by omega)

omit [DecidableEq Range] [Fintype Salt] in
/-- **The signed-set-augmented GPV Step-2 front-loading lift.** Averaging the signed-set-augmented
trap-sibling embed run over an external target draw `y ← $ᵗ Range` equals the signed-set-augmented
inline-fresh run `embedTrapFreshIdxSigImpl`.  Signed-set mirror of
`evalSPMF_frontDraw_embedTrapIdxImpl_eq_embedTrapFreshIdx`: off-winner steps commute the front `y`
past `y`-independent steps; at the count-`j` winner miss the front `y` is the immediately consumed
draw, so the front `y` *is* the inline-fresh winner draw, and post-winner the two runs coincide
(`evalSPMF_run_embedTrapIdxSigImpl_eq_embedTrapFreshIdxSig_of_lt`).  The signed set is updated
identically on both sides (signing ignores `y`) and is never read, so it rides along passively. -/
lemma evalSPMF_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
      𝒮[(($ᵗ Range : ProbComp Range) >>= fun y =>
          (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s)] =
        𝒮[(simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s] := by
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
          t = .inl (.inr q) ∧ s.1.1.1 q = none ∧ s.1.1.2 = j
      · -- **Winner step.** Substitute the front `y` for the inline fresh winner draw.
        obtain ⟨q, rfl, hmiss, hcount⟩ := hwin
        rw [show (fun y => (embedTrapIdxSigImpl psf M Salt pk sk j y (.inl (.inr q))).run s >>=
                fun p => (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (($ᵗ Range : ProbComp Range) >>= fun _ =>
                  (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (ob y)).run
                    (((s.1.1.1.cacheQuery q y, s.1.1.2 + 1),
                      fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2))) from by
          funext y
          rw [embedTrapIdxSigImpl_run_inl_inr, hmiss, hcount]
          simp only [↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]]
        rw [show ((embedTrapFreshIdxSigImpl psf M Salt pk sk (.inl (.inr q))).run s >>= fun p =>
                (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) (ob p.1)).run p.2)
              = (($ᵗ Range : ProbComp Range) >>= fun v =>
                  (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) (ob v)).run
                    (((s.1.1.1.cacheQuery q v, s.1.1.2 + 1),
                      fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2)) from by
          rw [embedTrapFreshIdxSigImpl_run_inl_inr, hmiss]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]]
        refine evalSPMF_bind_congr' _ (fun y => ?_)
        rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
          (probFailure_uniformSample Range)]
        exact evalSPMF_run_embedTrapIdxSigImpl_eq_embedTrapFreshIdxSig_of_lt psf M Salt pk sk j y
          (ob y)
          (((s.1.1.1.cacheQuery q y, s.1.1.2 + 1),
            fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2)
          (by simp only [hcount]; omega)
      · -- **Off-winner step.** The step is `y`-independent; commute the front `y` past it.
        push Not at hwin
        have hoff : ∀ q : (Salt × M →ₒ Range).Domain,
            t = .inl (.inr q) → s.1.1.1 q = none → s.1.1.2 ≠ j := by
          intro q hq hm; exact hwin q hq hm
        rw [show (fun y => (embedTrapIdxSigImpl psf M Salt pk sk j y t).run s >>= fun p =>
                (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (embedTrapFreshIdxSigImpl psf M Salt pk sk t).run s >>= fun p =>
                (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (ob p.1)).run p.2) from by
          funext y
          rw [embedTrapIdxSigImpl_run_step_eq_embedTrapFreshIdxSig psf M Salt pk sk j y t s hoff]]
        rw [OracleComp.DeferredSampling.evalSPMF_bind_comm ($ᵗ Range : ProbComp Range)
          ((embedTrapFreshIdxSigImpl psf M Salt pk sk t).run s)
          (fun y p => (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (ob p.1)).run p.2)]
        refine evalSPMF_bind_congr' _ (fun p => ?_)
        exact ih p.1 p.2

omit [DecidableEq Range] [Fintype Salt] in
/-- **Expected-functional form of the signed-set front-loading lift.**  For any nonnegative output
functional `F`, the inline-fresh run's expectation equals the front-target-averaged trap-sibling
run's expectation: `∑' w, Pr[= w | freshSig run] · F w = ∑' y, Pr[= y] · ∑' w, Pr[= w |
embedTrapIdxSig … j y run] · F w`.  Immediate from
`evalSPMF_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl` (the two `evalSPMF`s agree, so
their expectations of `F` agree) and the Tonelli rearrangement `tsum_probOutput_bind_mul`. -/
lemma tsum_probOutput_embedTrapFreshIdxSig_mul_eq_frontDraw [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
    (F : β × ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) →
      ℝ≥0∞) :
    (∑' w, Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s] * F w) =
      ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
        ∑' w, Pr[= w | (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s] * F w := by
  have hlift := evalSPMF_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl psf M Salt pk sk j
    oa s
  have hF : ∀ w, Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s] =
      Pr[= w | (($ᵗ Range : ProbComp Range) >>= fun y =>
        (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s)] :=
    fun w => by rw [probOutput, probOutput, hlift]
  simp_rw [hF]
  rw [tsum_probOutput_bind_mul]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Freshness-confined winner-slot cache invariant (state-general form).** On the
signed-set-augmented embed run `embedTrapIdxSigImpl … j y`, the following invariant is preserved
through the whole adaptive fold: for every key `k`, if its recorded insertion index is the winner
index `j` *and* its message was never signed (`k.2 ∉ signedSet`), then its cached random-oracle
image is exactly the embedded target `y`.

The invariant holds because the only programming event that can record `idx k = some j` at an
unsigned key `k` is a *random-oracle miss* at counter value `j` — and the embed handler's count-`j`
winner branch caches exactly `y` there.  The signing branch records its key `(r, msg)` but
simultaneously inserts `msg` into the signed set, so any key it touches has `k.2 ∈ signedSet`
afterwards, falling outside the invariant's unsigned hypothesis.  All other steps (uniform queries,
cache hits, off-`j` misses) either leave the state untouched or record an index `≠ j`. -/
lemma embedTrapIdxSigImpl_fresh_idx_cache_eq_general (pk : PK) (sk : SK) (j : ℕ) (y : Range) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
      (∀ k, s.1.2 k = some j → k.2 ∉ s.2 → s.1.1.1 k = some y) →
      ∀ z ∈ support ((simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s),
        ∀ k, z.2.1.2 k = some j → k.2 ∉ z.2.2 → z.2.1.1.1 k = some y := by
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
      · rw [embedTrapIdxSigImpl_run_inl_inl, map_eq_bind_pure_comp] at hps
        obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hh
        have hps' : pst = s := (Prod.ext_iff.mp hh).2
        refine ih pv pst ?_ z hz2
        rw [hps']; exact hs
      · rw [embedTrapIdxSigImpl_run_inl_inr] at hps
        cases hq : s.1.1.1 mc with
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
            have hps' : pst = (((if s.1.1.2 = j then s.1.1.1.cacheQuery mc y
                  else s.1.1.1.cacheQuery mc v, s.1.1.2 + 1),
                fun t' => if t' = mc then some s.1.1.2 else s.1.2 t'), s.2) := by
              have h2 := (Prod.ext_iff.mp hh).2
              by_cases hb : s.1.1.2 = j <;> simp only [hb, if_true, if_false] at h2 ⊢ <;>
                exact h2
            refine ih pv pst ?_ z hz2
            intro k hidx hfresh
            subst hps'
            simp only at hidx hfresh ⊢
            by_cases hk : k = mc
            · subst hk
              -- The miss at `mc` records `idx mc = some s.1.1.2`; the hypothesis forces it `= j`,
              -- so the winner branch fired and cached `y`.
              simp only [if_true, Option.some.injEq] at hidx
              subst hidx
              simp only [if_true, QueryCache.cacheQuery_self]
            · -- Off the missed key the state is the old one; apply `hs`.
              simp only [if_neg hk] at hidx
              by_cases hb : s.1.1.2 = j <;>
                simp only [hb, if_true, if_false, QueryCache.cacheQuery_of_ne _ _ hk] <;>
                exact hs k hidx hfresh
      · rw [embedTrapIdxSigImpl_run_inr] at hps
        obtain ⟨r, -, hps⟩ := (mem_support_bind_iff _ _ _).1 hps
        obtain ⟨c, -, hps⟩ := (mem_support_bind_iff _ _ _).1 hps
        rw [map_eq_bind_pure_comp] at hps
        obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hh
        have hps' : pst = (((s.1.1.1.cacheQuery (r, msg) c, s.1.1.2 + 1),
            fun t' => if t' = (r, msg) then some s.1.1.2 else s.1.2 t'),
            insert msg s.2) := (Prod.ext_iff.mp hh).2
        refine ih pv pst ?_ z hz2
        intro k hidx hfresh
        subst hps'
        simp only [Finset.mem_insert, not_or] at hfresh
        obtain ⟨hne, hfresh'⟩ := hfresh
        -- `k.2 ≠ msg` forces `k ≠ (r, msg)`, so the signing step left `idx k` and `cache k` alone.
        have hk : k ≠ (r, msg) := fun hkeq => hne (by rw [hkeq])
        simp only at hidx ⊢
        simp only [if_neg hk] at hidx
        rw [QueryCache.cacheQuery_of_ne _ _ hk]
        exact hs k hidx hfresh'

omit [DecidableEq Range] [Fintype Salt] in
/-- **Freshness-confined winner-slot cache recovery.** On the signed-set-augmented embed run
`embedTrapIdxSigImpl … j y` started from the empty state, any reachable final state `z` satisfies:
for a forged key `k` whose message was never signed (`k.2 ∉ z.signedSet`, the run-only freshness
witness) and whose recorded insertion index is the winner index `j` (`z.idxTable k = some j`), the
cached random-oracle image at `k` is exactly the embedded target `y` (`z.cache k = some y`).

This is the load-bearing freshness recovery for GPV Step-2: freshness rules out the signing branch
(which always signs its key's message), so the only programming event that could have recorded
`idx k = some j` is a count-`j` random-oracle miss, where the embed handler caches exactly `y`.  It
eliminates the free `y` from the embed win literal `cache(forged) = some y` on the winner slot,
specializing `embedTrapIdxSigImpl_fresh_idx_cache_eq_general` to the empty start (vacuous
invariant). -/
lemma embedTrapIdxSigImpl_fresh_idx_cache_eq (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (z : β × ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))
    (hz : z ∈ support ((simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run
      ((((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none)),
        (∅ : Finset M)))) :
    ∀ k, z.2.1.2 k = some j → k.2 ∉ z.2.2 → z.2.1.1.1 k = some y :=
  embedTrapIdxSigImpl_fresh_idx_cache_eq_general psf M Salt pk sk j y oa
    ((((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none)), (∅ : Finset M))
    (fun k hidx _ => by simp at hidx) z hz

omit [DecidableEq Range] [Fintype Salt] in
/-- **Write-only trapdoor-table support invariant.** On the counter-augmented trapdoor-recording run
`progGameRunImplCombinedTrapCount`, every recorded preimage is a trapdoor sample of the matching
cached random-oracle image: if `table(k) = some x` then there is a cached value `v` with
`cache(k) = some v` and `x ∈ support (trapdoorSample pk sk v)`.  Each programming event
(random-oracle miss or signing step) caches a fresh image `v` and records `trapdoorSample pk sk v`
into the table at the *same* key in lockstep; the table is never read during the run, so this
`(cache, table)`
agreement is preserved through the whole adaptive fold.  This is the support-level fact behind the
write-only-table deferral matching the trap event `table(forged) = output` to the embed event
`output = trapdoorSample (cache forged)`. -/
lemma progGameRunImplCombinedTrapCount_table_support (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)),
      (∀ k x, s.1.2 k = some x →
        ∃ v, s.1.1.1.1 k = some v ∧ x ∈ support (psf.trapdoorSample pk sk v)) →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        ∀ k x, z.2.1.2 k = some x →
          ∃ v, z.2.1.1.1.1 k = some v ∧ x ∈ support (psf.trapdoorSample pk sk v) := by
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
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        rw [hpst] at hz
        exact ih pv s hs z hz
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
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
            obtain ⟨v, hv, x, hx, -, hpst⟩ := hps
            refine ih pv pst ?_ z hz
            intro k x' hkx'
            have hcache : pst.1.1.1.1 = s.1.1.1.1.cacheQuery mc v := by rw [hpst]
            have htbl : pst.1.2 = fun t' => if t' = mc then some x else s.1.2 t' := by rw [hpst]
            rw [htbl] at hkx'
            rw [hcache]
            by_cases hk : k = mc
            · subst hk
              simp only [if_true] at hkx'
              rw [Option.some.injEq] at hkx'
              subst hkx'
              exact ⟨v, QueryCache.cacheQuery_self _ _ _, hx⟩
            · simp only [if_neg hk] at hkx'
              obtain ⟨w, hw1, hw2⟩ := hs k x' hkx'
              exact ⟨w, by rw [QueryCache.cacheQuery_of_ne _ _ hk]; exact hw1, hw2⟩
      · rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, hx, -, hpst⟩ := hps
        refine ih pv pst ?_ z hz
        intro k x' hkx'
        have hcache : pst.1.1.1.1 = s.1.1.1.1.cacheQuery (r, msg) v := by rw [hpst]
        have htbl : pst.1.2 = fun t' => if t' = (r, msg) then some x else s.1.2 t' := by rw [hpst]
        rw [htbl] at hkx'
        rw [hcache]
        by_cases hk : k = (r, msg)
        · subst hk
          simp only [if_true] at hkx'
          rw [Option.some.injEq] at hkx'
          subst hkx'
          exact ⟨v, QueryCache.cacheQuery_self _ _ _, hx⟩
        · simp only [if_neg hk] at hkx'
          obtain ⟨w, hw1, hw2⟩ := hs k x' hkx'
          exact ⟨w, by rw [QueryCache.cacheQuery_of_ne _ _ hk]; exact hw1, hw2⟩

end GPVHashAndSign
