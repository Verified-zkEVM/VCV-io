/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.EmbedIndex

/-! # GPV Hash-and-Sign: Security Bounds

The trap-count to fresh-signature projections, the reservoir extraction of the
programmed-preimage branch, the forgery dichotomy, and the headline EUF-CMA
bounds.

The headline bounds here, `euf_cma_split_bound` and `euf_cma_collision_bound`, carry the
random-oracle convention `ForgesQueriedPoint` as a hypothesis. They are the primitive forms that
the append-forgery-query compiler chains through; the public endpoints for consumers are the
all-adversaries corollaries `euf_cma_split_bound_of_queryBound` and
`euf_cma_collision_bound_of_queryBound` in `AppendQuery.lean`, whose only structural hypothesis on
the adversary is the query bound.
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

/-! ### Trap-count → fresh-sig cache/counter/idx/signedSet projection

The counter-augmented trapdoor-recording run `progGameRunImplCombinedTrapCount` and the
signed-set-augmented inline-fresh embed run `embedTrapFreshIdxSigImpl` draw their cached
random-oracle images identically: both cache a *fresh* uniform draw at every programming event (the
trap handler embeds nothing, and the fresh-sig handler has no winner branch).  They differ only in
the *extra* book-keeping the trap run carries — the freshness Bool flag and the write-only trapdoor
preimage table — both of which are distributionally passive.  Dropping them and reshaping the tuple
recovers the fresh-sig run's `(((cache × counter) × idx) × signedSet)` state exactly
(`map_run_progGameRunImplCombinedTrapCount_freshSig_proj`), at the *distribution* level: the trap
run's per-programming-event trapdoor draw `x ← trapdoorSample pk sk v` is never read by either run,
so under `NeverFail` it contributes only its (unit) mass. -/

/-- **`evalSPMF`-level state-projection transport (differing state types).** If every oracle step of
`impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec'))` becomes the corresponding `impl₂` step after
mapping the state with `proj : σ₁ → σ₂` *at the distribution level*, then the full simulated runs
agree under the same projection at the distribution level.  This is the `evalSPMF`-level relaxation
of `OracleComp.map_run_simulateQ_eq_of_query_map_eq`: the per-query hypothesis may discard a
never-failing answer-irrelevant draw (e.g. a write-only trapdoor sample) that breaks the *monadic*
equality but preserves the distribution. -/
theorem evalSPMF_map_run_simulateQ_eq_of_query_evalSPMF_map_eq
    {ι : Type} {spec : OracleSpec ι}
    {σ₁ σ₂ : Type} {α : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      𝒮[Prod.map id proj <$> (impl₁ t).run s] = 𝒮[(impl₂ t).run (proj s)])
    (oa : OracleComp spec α) (s : σ₁) :
    𝒮[Prod.map id proj <$> (simulateQ impl₁ oa).run s] =
      𝒮[(simulateQ impl₂ oa).run (proj s)] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rw [evalSPMF_bind_congr' ((impl₁ t).run s)
        (ob₂ := fun x => (simulateQ impl₂ (oa x.1)).run (proj x.2))
        (fun x => ih x.1 x.2)]
      rw [show ((impl₁ t).run s >>= fun x => (simulateQ impl₂ (oa x.1)).run (proj x.2))
            = ((Prod.map id proj <$> (impl₁ t).run s) >>= fun x =>
                (simulateQ impl₂ (oa x.1)).run x.2) from by
        rw [bind_map_left]; rfl]
      rw [evalSPMF_bind, hproj t s, ← evalSPMF_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query trap-count → fresh-sig distribution projection.** Dropping the freshness Bool flag
and the write-only trapdoor table from one `progGameRunImplCombinedTrapCount` query step — and
reshaping the remaining `(cache, signedSet, idx, counter)` components into the fresh-sig
`(((cache × counter) × idx) × signedSet)` layout — recovers the corresponding
`embedTrapFreshIdxSigImpl` step at the distribution level.  Both handlers cache a fresh uniform draw
at every programming event; the trap run's extra trapdoor sample `x ← trapdoorSample pk sk v` is
never read, so under `hNF` it is a never-failing value-irrelevant prefix that drops out. -/
lemma progGameRunImplCombinedTrapCount_freshSig_proj (pk : PK) (sk : SK)
    (hNF : ∀ c : Range, NeverFail (psf.trapdoorSample pk sk c))
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    𝒮[Prod.map id
        (fun s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
              ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) =>
          ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2) :
            (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)) <$>
        (progGameRunImplCombinedTrapCount psf M Salt pk sk t).run s] =
      𝒮[(embedTrapFreshIdxSigImpl psf M Salt pk sk t).run
        ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2))] := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombinedTrapCount_run_inl_inl, embedTrapFreshIdxSigImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [progGameRunImplCombinedTrapCount_run_inl_inr, embedTrapFreshIdxSigImpl_run_inl_inr]
          cases hq : s.1.1.1.1 q with
          | none =>
              -- RO miss: the trapdoor sample `x` is recorded write-only in the table (which the
              -- projection drops), so the projected output is `x`-independent and `x` drops out.
              simp only [map_bind, map_pure, Prod.map, id_eq]
              rw [map_eq_bind_pure_comp]
              refine evalSPMF_bind_congr' _ (fun v => ?_)
              rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails
                (psf.trapdoorSample pk sk v) (hNF v).probFailure_eq_zero _]
              rfl
          | some v => simp [Prod.map]
  | inr msg =>
      -- Signing: the trapdoor sample `x` *is* part of the output `(r, x)` on both sides, so the two
      -- signing steps draw `x ← trapdoorSample pk sk c` and output `(r, x)` identically.
      rw [progGameRunImplCombinedTrapCount_run_inr, embedTrapFreshIdxSigImpl_run_inr]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, Prod.map, id_eq, pure_bind]
      rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level trap-count → fresh-sig distribution projection.** Transports the per-query step
`progGameRunImplCombinedTrapCount_freshSig_proj` through the whole adaptive fold via
`evalSPMF_map_run_simulateQ_eq_of_query_evalSPMF_map_eq`: dropping the freshness Bool flag and the
write-only trapdoor table from the full simulated trap-count run, and reshaping to the fresh-sig
state layout, recovers the `embedTrapFreshIdxSigImpl` run distribution. -/
lemma map_run_progGameRunImplCombinedTrapCount_freshSig_proj (pk : PK) (sk : SK)
    (hNF : ∀ c : Range, NeverFail (psf.trapdoorSample pk sk c))
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    𝒮[Prod.map id
        (fun s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
              ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) =>
          ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2) :
            (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)) <$>
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] =
      𝒮[(simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run
        ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2))] := by
  exact evalSPMF_map_run_simulateQ_eq_of_query_evalSPMF_map_eq
    (progGameRunImplCombinedTrapCount psf M Salt pk sk)
    (embedTrapFreshIdxSigImpl psf M Salt pk sk)
    (fun s => ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2)))
    (progGameRunImplCombinedTrapCount_freshSig_proj psf M Salt pk sk hNF) oa s

omit [Fintype Salt] in
/-- **Step-2 embed-side reduction to the common freshness-confined deferred functional.**  The
inline-fresh-run expectation of the *freshness-confined winner-slot deferred-trapdoor* functional

  `Wf w := if forged.msg ∉ signedSet_w ∧ idx_w(forged) = some j then
              Pr[= forged.dom | trapdoorSample (cache_w forged)] else 0`

is a lower bound for the winner-slot-restricted per-target embedding win
(`reservoir_embed_winnerIdx_le`'s left side, i.e. the right side of the floor-free coupling).  The
front target average `∑' y, Pr[= y] · embedTrapIdxImpl … j y` is lifted to the signed-set-augmented
index run (`map_run_embedTrapIdxSigImpl_proj`, signed set passive) and then to the inline-fresh run
(`evalSPMF_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl`).  On the inline-fresh run the
freshness recovery (`embedTrapIdxSigImpl_fresh_idx_cache_eq`) makes the diagonal
`cache(forged) = some y` automatic on the freshness-confined winner slot, so the front `y` is
recovered as the cached image and the embed win event's literal `cache(forged) = some y` is matched;
the residual freshness restriction `forged.msg ∉ signedSet` only *decreases* the inline-fresh-run
expectation relative to the (freshness-free) embed win mass, so the bound is an inequality. -/
lemma freshSig_winnerSlot_deferred_le_embed [DecidableEq Domain] [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    (∑' w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
        Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) (adv.main pk)).run
            ((((∅, 0), fun _ => none), ∅))] *
          (if w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j then
              Pr[= w.1.2.2 | psf.trapdoorSample pk sk
                ((w.2.1.1.1 (w.1.2.1, w.1.1)).getD default)]
            else 0)) ≤
      ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
          Pr[= true | (do
            let r ← (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (adv.main pk)).run
              (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none))
            let x ← psf.trapdoorSample pk sk ((r.2.1.1 (r.1.2.1, r.1.1)).getD y)
            pure (decide (r.1.2.2 = x) && decide (r.2.1.1 (r.1.2.1, r.1.1) = some y) &&
              decide (r.2.2 (r.1.2.1, r.1.1) = some j)) : ProbComp Bool)] := by
  classical
  -- Rewrite each per-target embed win on the Sig-augmented run (signed set passive), then express
  -- the win mass as a `tsum` over the run output `r`.
  rw [tsum_probOutput_embedTrapFreshIdxSig_mul_eq_frontDraw psf M Salt pk sk j (adv.main pk)
    ((((∅, 0), fun _ => none), ∅))]
  refine ENNReal.tsum_le_tsum fun y => ?_
  refine mul_le_mul' le_rfl ?_
  -- Lift the un-augmented embed run on the RHS to the signed-set-augmented run.
  rw [show (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (adv.main pk)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none))
      = Prod.map id (Prod.fst :
          (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
            ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((((∅, 0), fun _ => none), ∅)) from
    (map_run_embedTrapIdxSigImpl_proj psf M Salt pk sk j y (adv.main pk)
      ((((∅, 0), fun _ => none), ∅))).symm]
  rw [bind_map_left]
  -- Express the win mass as a `tsum` over the Sig run output and compare termwise.
  rw [probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun w => ?_
  simp only [Prod.map, id_eq]
  -- Compare `Pr[= w | run] · Wf w ≤ Pr[= w | run] · winContinuation w`; off-support both vanish,
  -- on-support the freshness recovery aligns the literals.
  by_cases hsupp : w ∈ support ((simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y)
      (adv.main pk)).run ((((∅, 0), fun _ => none), ∅)))
  · refine mul_le_mul' le_rfl ?_
    -- The win predicate is `decide (r.dom = x) && decide (cache forged = some y) &&
    -- decide (idx forged = some j)`, with the trapdoor draw `x ← trapdoor ((cache forged).getD y)`.
    by_cases hWf : w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j
    · obtain ⟨hfresh, hidx⟩ := hWf
      -- Freshness recovery on the Sig run: `idx forged = some j` and forged unsigned force
      -- `cache forged = some y`.
      have hcache : w.2.1.1.1 (w.1.2.1, w.1.1) = some y :=
        embedTrapIdxSigImpl_fresh_idx_cache_eq psf M Salt pk sk j y (adv.main pk) w hsupp
          (w.1.2.1, w.1.1) hidx hfresh
      rw [if_pos ⟨hfresh, hidx⟩, probOutput_bind_eq_tsum]
      -- The continuation `pure (decide (dom = x) && decide (cache = some y) && decide (idx = j))`
      -- has both run-only literals `true`; it reduces to matching `dom = x`, so the `tsum` over `x`
      -- collapses to the single diagonal term at `x = dom`.
      refine le_of_eq ?_
      simp only [hcache, hidx, Option.getD_some, decide_true, Bool.and_true]
      rw [tsum_eq_single w.1.2.2 (fun x hx => by
        rw [probOutput_pure_eq_indicator]
        simp only [Set.indicator_apply, Set.mem_singleton_iff, eq_comm (a := true),
          decide_eq_true_eq, Ne.symm hx, if_false, mul_zero])]
      rw [probOutput_pure_eq_indicator]
      simp only [Set.indicator_apply, Set.mem_singleton_iff, eq_comm (a := true),
        decide_eq_true_eq, if_true, Function.const_apply, mul_one]
    · rw [if_neg hWf]; exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]; exact zero_le

omit [DecidableEq Range] [Fintype Salt] in
/-- **The signed set only grows along the trap-count run.**  Every reachable final state's signed
set contains the start signed set: signing inserts the queried message and no step removes from the
signed set. -/
lemma progGameRunImplCombinedTrapCount_signedSet_grows (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)),
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        s.1.1.1.2 ⊆ z.2.1.1.1.2 := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact subset_rfl
  | query_bind t mx ih =>
      intro s z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        have := ih pv pst z hz; rw [hpst] at this; exact this
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            have := ih pv pst z hz; rw [hpst] at this; exact this
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            have := ih pv pst z hz; rw [hpst] at this; exact this
      · rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        have hih := ih pv pst z hz
        rw [hpst] at hih
        exact (Finset.subset_insert _ _).trans hih

omit [DecidableEq Range] [Fintype Salt] in
/-- **Write-once freezing of a programmed, unsigned key on the trap-count run.**  Once a key `k₀` is
cached (`cache_s(k₀) ≠ none`) and its message stays unsigned through the run (`k₀.2 ∉ z.signedSet`
at the reachable final state `z`), both its cached image and its recorded trapdoor preimage are
frozen: `cache_z(k₀) = cache_s(k₀)` and `table_z(k₀) = table_s(k₀)`.  Random-oracle misses fire only
on cache misses, so they cannot overwrite an already-cached `k₀`; the signing branch writes at
`(r, msg)` and inserts `msg` into the signed set, so if it touched `k₀` it would sign `k₀.2`,
contradicting the final-state freshness (the signed set only grows). -/
lemma progGameRunImplCombinedTrapCount_frozen (pk : PK) (sk : SK) (k₀ : Salt × M) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)),
      s.1.1.1.1 k₀ ≠ none →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        k₀.2 ∉ z.2.1.1.1.2 →
        z.2.1.1.1.1 k₀ = s.1.1.1.1 k₀ ∧ z.2.1.2 k₀ = s.1.2 k₀ := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz hfresh
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl⟩
  | query_bind t mx ih =>
      intro s hs z hz hfresh
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        rw [hpst] at hz
        exact ih pv s hs z hz hfresh
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            rw [hpst] at hz
            exact ih pv s hs z hz hfresh
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            -- The miss is at `mc ≠ k₀` (since `cache_s(k₀) ≠ none = cache_s(mc)`), so `k₀` is
            -- untouched; apply the IH from the post-step state, which still has `cache(k₀) ≠ none`.
            have hne : k₀ ≠ mc := fun h => hs (by rw [h]; exact hq)
            obtain ⟨hcache, htbl⟩ := ih pv pst (by
              rw [hpst]; simp only [QueryCache.cacheQuery_of_ne _ _ hne]; exact hs) z hz hfresh
            rw [hcache, htbl, hpst]
            simp only [QueryCache.cacheQuery_of_ne _ _ hne, if_neg hne]
            exact ⟨trivial, trivial⟩
      · rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        -- The signing inserts `msg` into the signed set; since the post-state's signed set is
        -- contained in the final `z`'s signed set, and `k₀.2 ∉ z.signedSet`, we get `msg ≠ k₀.2`,
        -- hence `(r, msg) ≠ k₀`, so the signing step left `k₀` untouched.
        have hmsg : msg ≠ k₀.2 := by
          intro hmeq
          have hpst_sgn : k₀.2 ∈ pst.1.1.1.2 := by
            rw [hpst]; simp only [hmeq, Finset.mem_insert, true_or]
          have hgrow := progGameRunImplCombinedTrapCount_signedSet_grows psf M Salt pk sk
            (mx pv) pst z hz
          exact hfresh (hgrow hpst_sgn)
        have hk : k₀ ≠ (r, msg) := fun h => hmsg (by rw [h])
        obtain ⟨hcache, htbl⟩ := ih pv pst (by
          rw [hpst]; simp only [QueryCache.cacheQuery_of_ne _ _ hk]; exact hs) z hz hfresh
        rw [hcache, htbl, hpst]
        simp only [QueryCache.cacheQuery_of_ne _ _ hk, if_neg hk]
        exact ⟨trivial, trivial⟩

omit [DecidableEq Range] [Fintype Salt] in
/-- **Table-independence of any output/cache/idx/signedSet expectation on the trap-count run.**  The
trap handler never reads the write-only preimage table, so any output functional `F` of the output
and the projected `(cache, counter, idx, signedSet)` state has the same expectation from two start
states `s₁`, `s₂` that agree on everything except the table (`s₁.1.1 = s₂.1.1` and `s₁.2 = s₂.2`,
i.e. the cache/signed-set/bad components and the idx/counter components coincide).  Instance of the
generic state-relation transfer `tsum_probOutput_simulateQ_run_mul_of_rel`. -/
lemma progGameRunImplCombinedTrapCount_table_indep (pk : PK) (sk : SK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (F : β →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞)
    (s₁ s₂ : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ))
    (h11 : s₁.1.1 = s₂.1.1) (h2 : s₁.2 = s₂.2) :
    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s₁] *
        F z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2))) =
      ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s₂] *
        F z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) := by
  classical
  exact OracleComp.DeferredSampling.tsum_probOutput_simulateQ_run_mul_of_rel
    (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa
    (fun u₁ u₂ => u₁.1.1 = u₂.1.1 ∧ u₁.2 = u₂.2)
    (fun t a b hab K hKinv => by
      obtain ⟨hb11, hb2⟩ := hab
      rcases t with (n | mc) | msg
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl,
          progGameRunImplCombinedTrapCount_run_inl_inl]
        rw [tsum_probOutput_bind_mul,
          tsum_probOutput_bind_mul]
        refine tsum_congr fun v => ?_
        rw [tsum_probOutput_pure_mul,
          tsum_probOutput_pure_mul]
        exact congrArg _ (hKinv v a b ⟨hb11, hb2⟩)
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr,
          progGameRunImplCombinedTrapCount_run_inl_inr]
        have hcache : a.1.1.1.1 mc = b.1.1.1.1 mc := by rw [hb11]
        rw [hcache]
        cases hq : b.1.1.1.1 mc with
        | some v =>
            rw [tsum_probOutput_pure_mul,
              tsum_probOutput_pure_mul]
            exact hKinv v a b ⟨hb11, hb2⟩
        | none =>
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun v => congrArg _ ?_
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun x => congrArg _ ?_
            rw [tsum_probOutput_pure_mul,
              tsum_probOutput_pure_mul]
            refine hKinv v _ _ ⟨?_, ?_⟩
            · simp only [hb11]
            · simp only [hb2]
      · rw [progGameRunImplCombinedTrapCount_run_inr, progGameRunImplCombinedTrapCount_run_inr]
        rw [tsum_probOutput_bind_mul,
          tsum_probOutput_bind_mul]
        refine tsum_congr fun r => congrArg _ ?_
        rw [tsum_probOutput_bind_mul,
          tsum_probOutput_bind_mul]
        refine tsum_congr fun v => congrArg _ ?_
        rw [tsum_probOutput_bind_mul,
          tsum_probOutput_bind_mul]
        refine tsum_congr fun x => congrArg _ ?_
        rw [tsum_probOutput_pure_mul,
          tsum_probOutput_pure_mul]
        refine hKinv _ _ _ ⟨?_, ?_⟩
        · simp only [hb11]
        · simp only [hb2])
    (fun g st => F g ((((st.1.1.1.1, st.2.2), st.2.1), st.1.1.1.2)))
    (fun g u₁ u₂ huv => by
      obtain ⟨hu11, hu2⟩ := huv
      have hst : ((((u₁.1.1.1.1, u₁.2.2), u₁.2.1), u₁.1.1.1.2) :
            (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
          = ((((u₂.1.1.1.1, u₂.2.2), u₂.2.1), u₂.1.1.1.2)) := by
        rw [show u₁.1.1.1.1 = u₂.1.1.1.1 from by rw [hu11],
          show u₁.1.1.1.2 = u₂.1.1.1.2 from by rw [hu11],
          show u₁.2.1 = u₂.2.1 from by rw [hu2], show u₁.2.2 = u₂.2.2 from by rw [hu2]]
      rw [hst])
    s₁ s₂ ⟨h11, h2⟩

open Classical in
omit [DecidableEq Range] [Fintype Salt] in
/-- **Frozen-table expectation on the trap-count run.**  When the forged key `k₀` is already cached
at the start (`cache_s(k₀) ≠ none`) and the output functional `G` vanishes off the freshness event
`k₀.2 ∉ signedSet`, the recorded table at `k₀` is frozen on the relevant support, so the
`G · 1_{table(k₀) = some sStar}` expectation factors as the constant frozen indicator
`1_{table_s(k₀) = some sStar}` times the `G` expectation. -/
lemma progGameRunImplCombinedTrapCount_table_frozen_eq (pk : PK) (sk : SK)
    (k₀ : Salt × M) (sStar : Domain)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (G : β →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞)
    (hGfresh : ∀ b w, k₀.2 ∈ w.2 → G b w = 0)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ))
    (hs : s.1.1.1.1 k₀ ≠ none) :
    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
        (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
          (if z.2.1.2 k₀ = some sStar then 1 else 0))) =
      (if s.1.2 k₀ = some sStar then 1 else 0) *
        ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
          G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2) ) := by
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ support
      ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s)
  · by_cases hzfresh : k₀.2 ∈ z.2.1.1.1.2
    · rw [hGfresh z.1 _ (by exact hzfresh)]; ring
    · obtain ⟨-, htbl⟩ := progGameRunImplCombinedTrapCount_frozen psf M Salt pk sk k₀ oa s hs z hz
        hzfresh
      rw [htbl]; ring
  · rw [probOutput_eq_zero_of_not_mem_support hz]; ring

open Classical in
omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step deferral of one write-only trapdoor draw on the trap-count run (state-general
form).**  For a fixed key `k₀` and recorded value `sStar`, and any nonnegative output functional
`G` of the run output and the projected `(cache, counter, idx, signedSet)` state, the trap-count run
expectation of `G · 1_{table(k₀) = some sStar}` equals the run expectation of `G · D s`, where the
*deferred* value `D s z` is:

* the frozen indicator `1_{table_s(k₀) = some sStar}` if `k₀` was already programmed at the start
  state `s` (`cache_s(k₀) ≠ none`); or
* the deferred trapdoor-draw probability `Pr[= sStar | trapdoorSample (cache_z(k₀))]` if `k₀` is
  freshly programmed during the run (`cache_s(k₀) = none` and `cache_z(k₀) ≠ none`), and `0` if `k₀`
  is never programmed (`cache_z(k₀) = none`).

The recorded preimage `x ← trapdoorSample (cache k₀)` is sampled write-only at the `k₀` programming
event and never read, so its position in the adaptive fold is irrelevant: at the programming step
the inline `x`-draw is integrated against the frozen continuation (`cache(k₀)` and `table(k₀)` are
both frozen afterwards), turning `1_{table(k₀) = some sStar}` into the trapdoor-draw probability;
off the programming step the table at `k₀` is untouched, so the IH carries through.  This is the
defer-to-end twin of the front-loading lift, *keeping* the forged draw rather than dropping it. -/
lemma progGameRunImplCombinedTrapCount_table_defer (pk : PK) (sk : SK)
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (k₀ : Salt × M) (sStar : Domain)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (G : β →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞)
    (hGfresh : ∀ b w, k₀.2 ∈ w.2 → G b w = 0) :
    ∀ (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ)),
      (s.1.2 k₀ ≠ none → s.1.1.1.1 k₀ ≠ none) →
      (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
          (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
            (if z.2.1.2 k₀ = some sStar then 1 else 0))) =
        ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
          (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
            (match s.1.1.1.1 k₀ with
              | some _ => (if s.1.2 k₀ = some sStar then 1 else 0)
              | none =>
                  match z.2.1.1.1.1 k₀ with
                  | some v => Pr[= sStar | psf.trapdoorSample pk sk v]
                  | none => 0)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s htc
      simp only [simulateQ_pure, StateT.run_pure,
        tsum_probOutput_pure_mul]
      -- At `pure`, the final state is the start state, so the table at `k₀` is `s.1.2 k₀`.
      rcases hc : s.1.1.1.1 k₀ with _ | v
      · -- `k₀` unprogrammed at start (and at end): the deferred branch gives `0`; the table/cache
        -- lockstep `htc` forces `table_s(k₀) = none`, so the indicator branch is also `0`.
        have htbl : s.1.2 k₀ = none := by
          by_contra hne; exact (htc hne) hc
        rw [if_neg (by rw [htbl]; simp)]
      · rfl
  | query_bind t mx ih =>
      intro s htc
      -- **Branch A: `k₀` already programmed at the start.**  The deferred value is the constant
      -- frozen indicator; both sides factor through the frozen-table expectation lemma.
      rcases hcs : s.1.1.1.1 k₀ with _ | v₀
      · -- **Branch B: `k₀` not yet programmed at the start.**  Split the leading step from the
        -- continuation and integrate the (single) `k₀`-programming draw to the front.
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rcases t with (n | mc) | msg
        · -- Uniform query: the state is untouched, `cache(k₀)` stays `none`; apply the IH at `s`.
          rw [progGameRunImplCombinedTrapCount_run_inl_inl, bind_assoc]
          simp only [pure_bind]
          rw [tsum_probOutput_bind_mul,
            tsum_probOutput_bind_mul]
          refine tsum_congr fun v => congrArg _ ?_
          have hih := ih v s htc
          simp only [hcs] at hih
          exact hih
        · -- Random-oracle query at `mc`.
          rw [progGameRunImplCombinedTrapCount_run_inl_inr]
          cases hmcq : s.1.1.1.1 mc with
          | some v =>
              -- Cache hit: state untouched; apply the IH at `s`.
              simp only [pure_bind]
              have hih := ih v s htc
              simp only [hcs] at hih
              exact hih
          | none =>
              have htbls : s.1.2 k₀ = none := by
                by_contra hne; exact (htc hne) hcs
              simp only [bind_assoc, pure_bind]
              by_cases hmck : mc = k₀
              · -- **The forged random-oracle miss: integrate the single trapdoor draw.**
                subst hmck
                rw [tsum_probOutput_bind_mul,
                  tsum_probOutput_bind_mul]
                refine tsum_congr fun v => congrArg _ ?_
                -- Abbreviate the per-`(v, x)` `G`-expectation `Q x` from the post-state.
                set Q : Domain → ℝ≥0∞ := fun x =>
                  ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
                      (mx v)).run
                      ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                        fun t' => if t' = mc then some x else s.1.2 t'),
                        (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1)] *
                    G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) with hQ
                -- **LHS inner**, per `x`: apply the deferral IH at the post-state (where `cache mc`
                -- is `some v ≠ none`), turning `1_{table_z(mc) = sStar}` into the *frozen* value
                -- `1_{table_post(mc) = sStar} = 1_{x = sStar}`; then the constant factors out.
                have hLHS : ∀ x : Domain,
                    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
                        (mx v)).run
                        ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1)] *
                      (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
                        (if z.2.1.2 mc = some sStar then 1 else 0)))
                      = (if x = sStar then 1 else 0) * Q x := by
                  intro x
                  have hihx := ih v
                    ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                        fun t' => if t' = mc then some x else s.1.2 t'),
                        (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1) (by
                      simp only [QueryCache.cacheQuery_self]; exact fun _ => Option.some_ne_none v)
                  simp only [QueryCache.cacheQuery_self] at hihx
                  rw [hihx]
                  -- the post-state's `table mc = some x`, so the frozen indicator is `1_{x=sStar}`
                  simp only [if_true, Option.some.injEq]
                  rw [hQ]
                  simp only []
                  rw [← ENNReal.tsum_mul_left]
                  refine tsum_congr fun z => ?_; ring
                -- **RHS inner**, per `x`: the cache at `mc` is frozen to `some v`, so the deferred
                -- value is the constant `Pr[= sStar | trapdoorSample v]`; factor it out.
                have hRHS : ∀ x : Domain,
                    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
                        (mx v)).run
                        ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1)] *
                      (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
                        (match z.2.1.1.1.1 mc with
                          | some w => Pr[= sStar | psf.trapdoorSample pk sk w]
                          | none => 0)))
                      = Pr[= sStar | psf.trapdoorSample pk sk v] * Q x := by
                  intro x
                  rw [hQ]
                  simp only []
                  rw [← ENNReal.tsum_mul_left]
                  refine tsum_congr fun z => ?_
                  by_cases hz : z ∈ support
                      ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (mx v)).run
                        ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1))
                  · by_cases hzfresh : mc.2 ∈ z.2.1.1.1.2
                    · -- `mc.2` signed at `z` ⟹ `G = 0`, so the term vanishes on both sides.
                      rw [hGfresh z.1 _ (by exact hzfresh)]; ring
                    · have hpostc : ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'),
                          s.2.2 + 1).1.1.1.1 mc ≠ none := by
                        simp only [QueryCache.cacheQuery_self]; exact Option.some_ne_none v
                      obtain ⟨hzcache, -⟩ := progGameRunImplCombinedTrapCount_frozen psf M Salt pk
                        sk mc (mx v) _ hpostc z hz hzfresh
                      rw [hzcache]
                      simp only [QueryCache.cacheQuery_self]; ring
                  · rw [probOutput_eq_zero_of_not_mem_support hz]; ring
                -- **Combine.**  Per `x`, the inner sum is `Pr[= sStar | trapdoorSample v] · Q x` on
                -- the right and `1_{x = sStar} · Q x` on the left, and `Q` is table-independent
                -- (`progGameRunImplCombinedTrapCount_table_indep`), so `Q x = Q sStar`; integrating
                -- `x ← trapdoorSample v` turns the left indicator into `Pr[= sStar | trapdoor v]`.
                rw [tsum_probOutput_bind_mul,
                  tsum_probOutput_bind_mul]
                simp only [hLHS, hRHS]
                -- `Q` is independent of the table value `x`, so `Q x = Q sStar` for all `x`.
                have hQindep : ∀ x : Domain, Q x = Q sStar := fun x => by
                  rw [hQ]
                  exact progGameRunImplCombinedTrapCount_table_indep psf M Salt pk sk (mx v) _ _ _
                    rfl rfl
                simp_rw [hQindep]
                -- LHS: `∑' x, Pr[= x] · (1_{x = sStar} · Q sStar) = Pr[= sStar | trapdoor v] · Q`.
                rw [show (∑' x : Domain, Pr[= x | psf.trapdoorSample pk sk v] *
                        ((if x = sStar then 1 else 0) * Q sStar))
                      = Pr[= sStar | psf.trapdoorSample pk sk v] * Q sStar from by
                    rw [tsum_eq_single sStar (fun x hx => by rw [if_neg hx, zero_mul, mul_zero])]
                    rw [if_pos rfl, one_mul]]
                -- RHS: `∑' x, Pr[= x] · (Pr[= sStar | trapdoor v] · Q sStar) = 1 · (… · Q)`.
                rw [ENNReal.tsum_mul_right,
                  tsum_probOutput_eq_one' (hNF v).probFailure_eq_zero, one_mul]
              · -- Miss at `mc ≠ k₀`: `cache(k₀)` stays `none`; apply the IH at the post-state.
                rw [tsum_probOutput_bind_mul,
                  tsum_probOutput_bind_mul]
                refine tsum_congr fun v => congrArg _ ?_
                rw [tsum_probOutput_bind_mul,
                  tsum_probOutput_bind_mul]
                refine tsum_congr fun x => congrArg _ ?_
                -- Apply the IH at the post-state; `cache(k₀)` is unchanged (miss at `mc ≠ k₀`),
                -- so its outer deferred branch stays `none`, matching the goal.
                have hih := ih v
                  ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                      fun t' => if t' = mc then some x else s.1.2 t'),
                      (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1) (by
                    simp only [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hmck), hcs, if_neg
                      (Ne.symm hmck), htbls]
                    exact fun h => absurd rfl h)
                simp only [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hmck), hcs] at hih
                exact hih
        · -- Signing query on `msg`.
          rw [progGameRunImplCombinedTrapCount_run_inr]
          simp only [bind_assoc, pure_bind]
          have htbls : s.1.2 k₀ = none := by
            by_contra hne; exact (htc hne) hcs
          by_cases hmsg : msg = k₀.2
          · -- Signing the forged message inserts `k₀.2` into the (monotone) signed set, so every
            -- continuation has `k₀.2 ∈ signedSet` and `G = 0`; both sides vanish termwise.
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun r => congrArg _ ?_
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun v => congrArg _ ?_
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun x => congrArg _ ?_
            refine tsum_congr fun z => ?_
            by_cases hz : z ∈ support
                ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (mx (r, x))).run
                  ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
                    s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r),
                    fun t' => if t' = (r, msg) then some x else s.1.2 t'),
                    (fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1))
            · have hgrow := progGameRunImplCombinedTrapCount_signedSet_grows psf M Salt pk sk
                (mx (r, x)) _ z hz
              have hmem : k₀.2 ∈ z.2.1.1.1.2 :=
                hgrow (by simp only [hmsg, Finset.mem_insert, true_or])
              rw [hGfresh z.1 _ hmem]; ring
            · rw [probOutput_eq_zero_of_not_mem_support hz]; ring
          · -- `msg ≠ k₀.2` forces `(r, msg) ≠ k₀`, so `cache(k₀)` stays `none`; apply the IH.
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun r => congrArg _ ?_
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun v => congrArg _ ?_
            rw [tsum_probOutput_bind_mul,
              tsum_probOutput_bind_mul]
            refine tsum_congr fun x => congrArg _ ?_
            have hk : k₀ ≠ (r, msg) := fun h => hmsg (by rw [h])
            have hih := ih (r, x)
              ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
                  s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r),
                  fun t' => if t' = (r, msg) then some x else s.1.2 t'),
                  (fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1) (by
                simp only [QueryCache.cacheQuery_of_ne _ _ hk, hcs, if_neg hk, htbls]
                exact fun h => absurd rfl h)
            simp only [QueryCache.cacheQuery_of_ne _ _ hk, hcs] at hih
            exact hih
      · rw [progGameRunImplCombinedTrapCount_table_frozen_eq psf M Salt pk sk k₀ sStar _ G hGfresh s
          (by rw [hcs]; exact Option.some_ne_none v₀), ← ENNReal.tsum_mul_left]
        refine tsum_congr fun z => ?_; ring

open Classical in
omit [Fintype Salt] in
/-- **Step-2 trap-side table-defer to the common freshness-confined deferred functional.**  The
freshness-confined index-tagged trap-exact-match mass — the trap event
`forged.msg ∉ signedSet ∧ table(forged) = some forged.dom ∧ idx(forged) = some j` on the
counter-augmented trapdoor-recording run `progGameRunImplCombinedTrapCount` — is bounded by the
inline-fresh-run expectation of the freshness-confined winner-slot deferred-trapdoor functional

  `Wf w := if forged.msg ∉ signedSet_w ∧ idx_w(forged) = some j then
              Pr[= forged.dom | trapdoorSample (cache_w forged)] else 0`.

This is the genuinely-new (answer-irrelevant) content of GPV Step-2: at the freshness-confined
forged key the write-only trapdoor preimage `x ← trapdoorSample (cache forged)` recorded inline into
the
table is *never read* (an unsigned forged key is a random-oracle miss whose preimage enters only the
write-only table, never the adversary view), so it commutes to the end of the adaptive fold and
becomes a post-run independent trapdoor draw against the cached image.  Freshness is exactly what
makes this draw deferrable; a *signed* key returns `(r, x)` to the adversary, so its table draw is
not deferrable, which is why dropping freshness falsifies the bound. -/
lemma trap_freshSig_le_winnerSlot_deferred [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c)) :
    Pr[fun w : (M × (Salt × Domain)) ×
          (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
            (((Salt × M) → Option ℕ) × ℕ)) =>
          (w.1.1 ∉ w.2.1.1.1.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
            w.2.2.1 (w.1.2.1, w.1.1) = some j |
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)]
      ≤ ∑' w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
        Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) (adv.main pk)).run
            ((((∅, 0), fun _ => none), ∅))] *
          (if w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j then
              Pr[= w.1.2.2 | psf.trapdoorSample pk sk
                ((w.2.1.1.1 (w.1.2.1, w.1.1)).getD default)]
            else 0) := by
  classical
  -- Abbreviate the trap-state → fresh-sig-state projection (drop the freshness Bool flag and the
  -- write-only trapdoor table; reshape to the fresh-sig `(((cache × counter) × idx) × signedSet)`).
  set projS : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
        × (((Salt × M) → Option ℕ) × ℕ) →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M :=
    fun s => ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2)) with hprojS
  -- **Transport the RHS fresh-sig-run expectation onto the trap-count run.**  By the
  -- distribution-level projection, the fresh-sig run is the trap-count run mapped by
  -- `projS`, so the
  -- RHS expectation of `Wf` over the fresh-sig run equals its expectation over the trap-count run
  -- precomposed with `Prod.map id projS`.
  have hRHS : (∑' w, Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk)
          (adv.main pk)).run ((((∅, 0), fun _ => none), ∅))] *
        (if w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j then
            Pr[= w.1.2.2 | psf.trapdoorSample pk sk
              ((w.2.1.1.1 (w.1.2.1, w.1.1)).getD default)]
          else 0)) =
      ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)] *
        (if z.1.1 ∉ (projS z.2).2 ∧ (projS z.2).1.2 (z.1.2.1, z.1.1) = some j then
            Pr[= z.1.2.2 | psf.trapdoorSample pk sk
              (((projS z.2).1.1.1 (z.1.2.1, z.1.1)).getD default)]
          else 0) := by
    have hmap := map_run_progGameRunImplCombinedTrapCount_freshSig_proj psf M Salt pk sk hNF
      (adv.main pk)
      (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
        (fun _ => none), 0)
    simp only [hprojS] at hmap ⊢
    -- Pointwise: the fresh-sig output probability is the trap-count run mapped by `projS`.
    have hpt : ∀ w, Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk)
          (adv.main pk)).run ((((∅, 0), fun _ => none), ∅))]
        = Pr[= w | Prod.map id
            (fun s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
                ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) =>
              ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2) :
                (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)) <$>
            (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (adv.main pk)).run
              (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
                (fun _ => none), 0)] :=
      fun w => by rw [probOutput, probOutput, hmap]
    simp_rw [hpt]
    rw [tsum_probOutput_map_mul]
    refine tsum_congr fun z => ?_
    simp only [Prod.map, id_eq]
  rw [hRHS]
  -- **The per-run table-defer (the answer-irrelevant content).**  Both sides are
  -- now expectations over the *same* trap-count run; the LHS reads the recorded table at the forged
  -- point (`1_{table(forged) = some forged.dom}`), the RHS the deferred trapdoor draw against the
  -- cached image (`Pr[= forged.dom | trapdoorSample (cache forged)]`).  On the freshness-confined
  -- winner slot the recorded entry is the inline write-only draw `x ← trapdoorSample (cache
  -- forged)` sampled at the forged random-oracle miss and never read; its *expected* indicator over
  -- the run equals the deferred draw probability.
  --
  -- ⚠ This is NOT a per-final-state inequality (it FAILS pointwise: at a state whose table is
  -- already frozen to `some d₀`, the LHS indicator is `1_{d₀ = forged.dom}` while the RHS is
  -- `Pr[= forged.dom | trapdoorSample (cache forged)] < 1`).  It holds only in *expectation*: the
  -- recorded `x` is itself random (drawn at the forged miss), independent of `(output, cache)`
  -- given the run, so `E[1_{table(forged) = forged.dom}] = Pr[= forged.dom | trapdoorSample (cache
  -- forged)]`.  Mechanizing it requires *deferring* the single answer-irrelevant write-only draw
  -- `x` from its inline position at the forged miss to the end of the adaptive `simulateQ` fold (it
  -- commutes past every subsequent step because the continuation never reads `table(forged)` or the
  -- frozen `cache(forged)`), matching it to a post-run draw of `trapdoorSample (cache forged)`.
  -- The projection `map_run_progGameRunImplCombinedTrapCount_freshSig_proj` *drops* every table
  -- draw via `evalSPMF_bind_const_neverFails`; the defer-to-end induction over the trap run that
  -- keeps the deferred draw is `progGameRunImplCombinedTrapCount_table_defer`.  Below the FRESH
  -- conjunct `w.1.1 ∉ w.2.1.1.1.2` is carried throughout.
  rw [probEvent_eq_tsum_ite]
  refine le_of_eq ?_
  classical
  -- Decompose the output-dependent forged-key indicator over a fixed key/value pair `p`, swap the
  -- order of summation, and apply the (fixed-key) table-defer per `p`.  Recombining over `p` gives
  -- the deferred functional with the cache-read trapdoor probability.
  set proj2 : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
        × (((Salt × M) → Option ℕ) × ℕ) →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M :=
    fun st => ((((st.1.1.1.1, st.2.2), st.2.1), st.1.1.1.2)) with hproj2
  -- The per-pair selector functional.
  set Gp : (Salt × M) × Domain → (M × (Salt × Domain)) →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞ :=
    fun p b w => if (b.2.1, b.1) = p.1 ∧ b.2.2 = p.2 ∧ b.1 ∉ w.2 ∧ w.1.2 p.1 = some j
      then 1 else 0 with hGp
  set run := (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (adv.main pk)).run
    ((((∅, ∅), false), fun _ => none), (fun _ => none), 0) with hrun
  -- **LHS = double sum.**  The forged-key indicator collapses to the single pair
  -- `p = (forged, forged.dom)`.
  have hLHSdecomp : (∑' z, if (z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.1.2 (z.1.2.1, z.1.1) = some z.1.2.2) ∧
          z.2.2.1 (z.1.2.1, z.1.1) = some j then Pr[= z | run] else 0)
      = ∑' p : (Salt × M) × Domain, ∑' z,
          Pr[= z | run] * (Gp p z.1 (proj2 z.2) * (if z.2.1.2 p.1 = some p.2 then 1 else 0)) := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun z => ?_
    simp only [hGp, hproj2]
    rw [tsum_eq_single ((z.1.2.1, z.1.1), z.1.2.2) (fun p hp => by
      rw [show (if (z.1.2.1, z.1.1) = p.1 ∧ z.1.2.2 = p.2 ∧ z.1.1 ∉ z.2.1.1.1.2 ∧
            z.2.2.1 p.1 = some j then (1 : ℝ≥0∞) else 0) = 0 from by
        refine if_neg ?_
        rintro ⟨h1, h2, -, -⟩; exact hp (by rw [Prod.ext_iff]; exact ⟨h1.symm, h2.symm⟩),
        zero_mul, mul_zero])]
    simp only [true_and]
    by_cases hev : (z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.1.2 (z.1.2.1, z.1.1) = some z.1.2.2) ∧
        z.2.2.1 (z.1.2.1, z.1.1) = some j
    · obtain ⟨⟨hfresh, htbl⟩, hidx⟩ := hev
      rw [if_pos ⟨⟨hfresh, htbl⟩, hidx⟩, if_pos ⟨hfresh, hidx⟩, if_pos htbl]; ring
    · rw [if_neg hev]
      by_cases htbl : z.2.1.2 (z.1.2.1, z.1.1) = some z.1.2.2
      · have hcond : ¬(z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.2.1 (z.1.2.1, z.1.1) = some j) := by
          rintro ⟨hfresh, hidx⟩; exact hev ⟨⟨hfresh, htbl⟩, hidx⟩
        rw [if_pos htbl, mul_one, if_neg hcond, mul_zero]
      · rw [if_neg htbl, mul_zero, mul_zero]
  -- **Per-pair table-defer.**  Apply the fixed-key table-defer lemma at `(k₀, sStar) = p` with the
  -- selector `Gp p` (which vanishes off the freshness event, as required).
  have hbridge : ∀ p : (Salt × M) × Domain,
      (∑' z, Pr[= z | run] * (Gp p z.1 (proj2 z.2) * (if z.2.1.2 p.1 = some p.2 then 1 else 0)))
        = ∑' z, Pr[= z | run] * (Gp p z.1 (proj2 z.2) *
            (match (proj2 z.2).1.1.1 p.1 with
              | some w => Pr[= p.2 | psf.trapdoorSample pk sk w]
              | none => 0)) := by
    intro p
    have hGfreshp : ∀ b w, p.1.2 ∈ w.2 → Gp p b w = 0 := by
      intro b w hmem
      rw [hGp]; refine if_neg ?_
      rintro ⟨hbp, -, hbw, -⟩
      exact hbw (by rw [show b.1 = p.1.2 from by rw [← hbp]]; exact hmem)
    have hdefer := progGameRunImplCombinedTrapCount_table_defer psf M Salt pk sk hNF p.1 p.2
      (adv.main pk) (Gp p) hGfreshp
      (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
        (fun _ => none), 0) (by simp)
    -- the empty start has `cache p.1 = none`, so the deferred outer match reduces to the inner
    -- `match cache_z p.1`.
    simp only [hrun, hproj2] at hdefer ⊢
    refine hdefer.trans (tsum_congr fun z => congrArg _ (congrArg _ ?_))
    rcases (((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2).1.1.1 p.1 with _ | w <;> rfl
  -- **RHS = double sum.**  The deferred functional likewise collapses to the single forged pair.
  have hRHSdecomp : (∑' z, Pr[= z | run] *
          (if z.1.1 ∉ (proj2 z.2).2 ∧ (proj2 z.2).1.2 (z.1.2.1, z.1.1) = some j then
            Pr[= z.1.2.2 | psf.trapdoorSample pk sk
              (((proj2 z.2).1.1.1 (z.1.2.1, z.1.1)).getD default)]
          else 0))
      = ∑' p : (Salt × M) × Domain, ∑' z,
          Pr[= z | run] * (Gp p z.1 (proj2 z.2) *
            (match (proj2 z.2).1.1.1 p.1 with
              | some w => Pr[= p.2 | psf.trapdoorSample pk sk w]
              | none => 0)) := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun z => ?_
    simp only [hGp, hproj2]
    rw [tsum_eq_single ((z.1.2.1, z.1.1), z.1.2.2) (fun p hp => by
      rw [show (if (z.1.2.1, z.1.1) = p.1 ∧ z.1.2.2 = p.2 ∧ z.1.1 ∉ z.2.1.1.1.2 ∧
            z.2.2.1 p.1 = some j then (1 : ℝ≥0∞) else 0) = 0 from by
        refine if_neg ?_
        rintro ⟨h1, h2, -, -⟩; exact hp (by rw [Prod.ext_iff]; exact ⟨h1.symm, h2.symm⟩),
        zero_mul, mul_zero])]
    simp only [true_and]
    -- diagonal `p = (forged, dom)`: `Gp = 1_{fresh ∧ idx=j}` and the deferred value reads
    -- `cache_z(forged)`; on the run support `idx = some j` forces `cache ≠ none` (idx/table/cache
    -- lockstep), so it matches the `getD default` form.
    by_cases hz : z ∈ support run
    · by_cases hfi : z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.2.1 (z.1.2.1, z.1.1) = some j
      · obtain ⟨hfresh, hidx⟩ := hfi
        rw [if_pos ⟨hfresh, hidx⟩, if_pos ⟨hfresh, hidx⟩]
        -- recover `cache ≠ none` from `idx = some j` via the lockstep invariants
        have hzrun : z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
            (adv.main pk)).run ((((∅, ∅), false), fun _ => none), (fun _ => none), 0)) := by
          rw [← hrun]; exact hz
        have hidxne : z.2.2.1 (z.1.2.1, z.1.1) ≠ none := by rw [hidx]; exact Option.some_ne_none j
        have htblne : z.2.1.2 (z.1.2.1, z.1.1) ≠ none :=
          (progGameRunImplCombinedTrapCount_idx_iff_table psf M Salt pk sk (adv.main pk)
            ((((∅, ∅), false), fun _ => none), (fun _ => none), 0)
            (fun k => by simp) z hzrun (z.1.2.1, z.1.1)).2 hidxne
        obtain ⟨xv, htbleq⟩ := Option.ne_none_iff_exists'.1 htblne
        obtain ⟨w, hcache, -⟩ := progGameRunImplCombinedTrapCount_table_support psf M Salt pk sk
          (adv.main pk) ((((∅, ∅), false), fun _ => none), (fun _ => none), 0)
          (fun k x hx => by simp at hx) z hzrun (z.1.2.1, z.1.1) xv htbleq
        rw [hcache, Option.getD_some]; ring
      · simp only [if_neg hfi, zero_mul, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hz]; ring
  -- **Combine.**  `LHS = (hLHSdecomp) ∑∑ indicator = (hbridge) ∑∑ deferred = (hRHSdecomp) RHS`.
  rw [hLHSdecomp]
  rw [show (∑' p : (Salt × M) × Domain, ∑' z, Pr[= z | run] *
        (Gp p z.1 (proj2 z.2) * (if z.2.1.2 p.1 = some p.2 then 1 else 0)))
      = ∑' p : (Salt × M) × Domain, ∑' z, Pr[= z | run] *
        (Gp p z.1 (proj2 z.2) *
          (match (proj2 z.2).1.1.1 p.1 with
            | some w => Pr[= p.2 | psf.trapdoorSample pk sk w]
            | none => 0)) from tsum_congr fun p => hbridge p]
  rw [← hRHSdecomp]

open Classical in
omit [Fintype Salt] in
/-- **The per-slot front-loading deferred-sampling coupling (floor-free form).**

The *index-tagged* trap-exact-match mass at slot `j` — the trap event on the counter-augmented run
`progGameRunImplCombinedTrapCount` restricted to the event that the forged point was *programmed at
counter value `j`* — is bounded by the **floor-free** per-target embedding win
`S (some j) = ∑' y, Pr[= y | $ᵗ Range] · Pr[win | embedTrapImpl … j y]`, with **no** budget /
reservoir factor.  This is the genuine deferred-sampling content of GPV Step-2: at the fixed slot
`j` the trap run's inline uniform winner draw `v⋆ ← $ᵗ Range` (drawn *inside* the `simulateQ` fold
at the adaptively-determined `j`-th programming step) must be pushed to the front and re-expressed
as the embedded target `y ← $ᵗ Range` (drawn *outside* the fold), mirroring
`evalSPMF_gpvRealImpl_eq_drawList_gpvRealImplTape`; the embedded slot is then `j` and the win event
couples to the trap run's write-only `table(forged) = trapdoorSample (cache(forged))`.

The budget-scaled form `reservoir_embed_commute_winner` follows from this by the reservoir floor
arithmetic (`probOutput_reservoirWinnerIndex_eq` at `j < qSign + qHash`, the recorded-index budget
`progGameRunImplCombinedTrapCount_idx_lt_budget` clearing the `j ≥ qSign + qHash` tail). -/
lemma reservoir_embed_commute_winner_floorFree [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (_hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (_hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (_hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) (j : ℕ) :
    Pr[fun w : (M × (Salt × Domain)) ×
          (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
            (((Salt × M) → Option ℕ) × ℕ)) =>
          ((decide (w.1.1 ∉ w.2.1.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
            w.2.2.1 (w.1.2.1, w.1.1) = some j |
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)]
      ≤ ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x) &&
                decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  -- **The GPV Step-2 per-slot front-loading joint coupling.**
  --
  -- This is the deferred-sampling content.  The left mass lives on the
  -- counter-augmented trap run `progGameRunImplCombinedTrapCount`: at the *adaptively-determined*
  -- `j`-th programming step, an inline uniform winner image `v⋆ ← $ᵗ Range` is drawn *inside* the
  -- `simulateQ` fold, cached at the forged point, and the write-only trapdoor preimage
  -- `trapdoorSample (pk, sk) v⋆` is recorded.  The right mass averages the embedded target
  -- `y ← $ᵗ Range` *outside* the fold and runs `embedTrapImpl … j y`, which caches `y` at its
  -- count-`j` random-oracle miss and draws fresh uniform images everywhere else.
  --
  -- **Fold the `y`-average into a single front draw.** The right-hand `∑' y`
  -- weighted by `Pr[= y | $ᵗ Range]` is exactly the output probability of the bind that draws
  -- `y ← $ᵗ Range` first and then runs the per-target win game (`probOutput_bind_eq_tsum`).  This
  -- puts the right side in the *front-loaded* form `Pr[= true | y ← $ᵗ Range; …]`, matching the
  -- trap run's inline `v⋆ ← $ᵗ Range` up to the adaptive count-`j` position.
  rw [← probOutput_bind_eq_tsum]
  -- **The adaptive count-`j` front-loading, via the front-draw lift.**
  --
  -- The goal is now `LHS_trap ≤ Pr[= true | y ← $ᵗ Range; x ← trapdoorSample pk sk y;
  --   r ← (simulateQ (embedTrapImpl … j y) (adv.main pk)).run (∅, 0);
  --   pure (decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y))]`, i.e. both sides now carry
  -- a single `$ᵗ Range` draw: the trap run draws it *inline* at the adaptively-determined `j`-th
  -- programming step, the embed game draws it at the *front* (consumed at its count-`j` miss).
  --
  -- The adaptive PMF×PMF run coupling — pushing the trap run's inline winner draw
  -- `v⋆ ← $ᵗ Range` to the front and re-expressing it as the embedded target `y ← $ᵗ Range` across
  -- the whole adaptive fold — is
  -- `evalSPMF_frontDraw_embedTrapImpl_eq_embedTrapFresh`: averaging the trap-sibling embed run over
  -- the external target draw equals the inline-fresh run `embedTrapFreshImpl` (an all-fresh-uniform
  -- lazy random oracle with counter).  Its winner step substitutes the front `y` for the inline
  -- fresh winner draw and uses post-winner coincidence
  -- (`evalSPMF_run_embedTrapImpl_eq_embedTrapFresh_of_lt`); its off-winner steps commute the front
  -- draw past `y`-independent steps (`embedTrapImpl_run_step_eq_embedTrapFresh`,
  -- `OracleComp.DeferredSampling.evalSPMF_bind_comm`).
  --
  -- **The win-event same-randomness coupling.**
  --
  -- The lift couples the *run* (the cache/counter marginal), but the embed win event still reads
  -- the front target `y` directly — `r.2.1 (forged) = some y` and
  -- `r.1.2.2 = x ← trapdoorSample pk sk y` — so the lift cannot fire while `y` lives in the event.
  -- On the winner-slot support the cache *pins* `y`: at slot `j` the trap-sibling caches exactly
  -- `y`, so `r.2.1 (forged) = some y` forces `y = cache(forged)` and
  -- `x ← trapdoorSample pk sk (cache(forged))`.  Eliminating the explicit `y` via this cache-pin
  -- (a marginal over `y` tied to the cache value) puts the embed win in run-only form, after which
  -- the front-draw lift rewrites the run to `embedTrapFreshImpl` and the
  -- trap-count run is its trapdoor-table/index augmentation (the LHS handler
  -- `progGameRunImplCombinedTrapCount` draws the *same* fresh `v` and records
  -- `table(forged) = trapdoorSample pk sk v` with `idx(forged) = some j`).  Matching the trap event
  -- `table(forged) = trapdoorSample (cache(forged))` to the embed event `output = trapdoorSample
  -- (cache(forged))` is the final N4-style same-randomness coupling
  -- (`evalSPMF_simulateQ_run_congr` after projecting to the common
  -- `embedTrapFreshImpl` cache/counter state) and the trapdoor draw `x`.
  --
  -- **Commute the trapdoor draw `x` past the embed run.**  The trapdoor
  -- preimage `x ← trapdoorSample pk sk y` is drawn from an *independent* `ProbComp` (it does not
  -- feed the embed run `simulateQ (embedTrapImpl … j y)`, which consumes only `y`), so the two
  -- binds exchange at the distribution level (`OracleComp.DeferredSampling.evalSPMF_bind_comm`).
  -- Running the embed first and drawing `x` afterwards leaves the win event — and hence the output
  -- probability `Pr[= true | …]` — unchanged.  This re-expresses the right-hand game in the
  -- *run-first* form, in which the embed run output `r` is already available when the trapdoor draw
  -- `x` and the win predicate `decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y)` are
  -- evaluated.
  rw [show Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let x ← psf.trapdoorSample pk sk y
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)]
      = Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk y
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] from by
    refine probOutput_congr rfl ?_
    refine evalSPMF_bind_congr' _ (fun y => ?_)
    exact OracleComp.DeferredSampling.evalSPMF_bind_comm (psf.trapdoorSample pk sk y)
      ((simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run (∅, 0))
      (fun x r => pure (decide (r.1.2.2 = x) &&
        decide (r.2.1 (r.1.2.1, r.1.1) = some y)))]
  -- **Pin the trapdoor draw to the cached image at the forged point.**  The
  -- win predicate is `decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y)`; whenever its
  -- second conjunct holds the cached image at the forged point is exactly the front target,
  -- `r.2.1 (forged) = some y`, so `(r.2.1 (forged)).getD y = y` and the trapdoor preimage
  -- `x ← trapdoorSample pk sk y` equals `x ← trapdoorSample pk sk ((r.2.1 (forged)).getD y)`.
  -- When the second conjunct fails the whole `&&` is `false` regardless of `x`, so the trapdoor
  -- draw is irrelevant and either target yields the same (constant-`false`) win distribution.
  -- This pins the trapdoor draw to a *run-read* cache value — eliminating the free `y` from the
  -- trapdoor draw, leaving it only in the cache-comparison literal `some y`.
  rw [show Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk y
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)]
      = Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk ((r.2.1 (r.1.2.1, r.1.1)).getD y)
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] from by
    refine probOutput_congr rfl (evalSPMF_bind_congr' _ (fun y => ?_))
    refine evalSPMF_bind_congr' _ (fun r => ?_)
    rcases hc : r.2.1 (r.1.2.1, r.1.1) with _ | yv
    · simp only [Option.getD_none]
    · simp only [Option.getD_some]
      by_cases hy : yv = y
      · rw [hy]
      · simp only [Option.some.injEq, hy, decide_false, Bool.and_false]
        rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
            ((hNF y).probFailure_eq_zero),
          OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _
            ((hNF yv).probFailure_eq_zero)]]
  -- **Index-augment the embed run and restrict the win to the winner slot.**
  -- The win predicate `decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y)` reads only the
  -- embed run *output* `r.1.2.2` and *cache* `r.2.1`, both of which are recovered from the
  -- index-augmented run `embedTrapIdxImpl … j y` by the passive projection
  -- `map_run_embedTrapIdxImpl_proj` (the inserted insertion-index table is never read).  Hence the
  -- right-hand win mass equals the same win mass on the augmented run, which dominates its
  -- restriction to the further conjunct `idx(forged) = some j` (the run-only winner-slot witness):
  --
  --   `RHS' := ∑'y Pr[=y] · Pr[= true | embedTrapIdxImpl … j y; x ← trapdoorSample (cache forged);
  --              pure (win ∧ idx(forged) = some j)]  ≤  RHS`.
  --
  -- This is the sound monotone reduction (`probOutput` over a conjoined Bool) that re-expresses the
  -- right side on the index-augmented run with the winner-slot restriction made explicit, so that
  -- the front target `y` enters only through run-only predicates (`idx(forged) = some j`) — exactly
  -- the form the trap-count run's `idx(forged) = some j` event couples to.
  refine le_trans ?_ (reservoir_embed_winnerIdx_le psf hr M Salt pk sk j adv)
  -- **The freshness-confined winner-slot coupling.**
  --
  -- Goal here (after the winner-idx monotone step `reservoir_embed_winnerIdx_le`):
  --   ⊢ Pr[fun w => ((fresh w.1.1 ∧ verify ∧ isShort) ∧ table(forged) = some w.1.2.2)
  --        ∧ idx(forged) = some j | (simulateQ progGameRunImplCombinedTrapCount (adv.main pk)).run]
  --     ≤ ∑'y Pr[= y | $ᵗ Range] ·
  --         Pr[= true | r ← (simulateQ (embedTrapIdxImpl … j y) (adv.main pk)).run ((∅, 0), ∅idx);
  --                     x ← trapdoorSample pk sk ((r.2.1.1 (forged)).getD y);
  --                     pure (decide (r.1.2.2 = x) && decide (r.2.1.1 (forged) = some y)
  --                            && decide (r.2.2 (forged) = some j))]
  --
  -- ⚠ The FRESHNESS conjunct `w.1.1 ∉ w.2.1.1.1.2` (`forged.msg ∉ signedSet`) is LOAD-BEARING and
  -- must NOT be dropped.  Dropping it makes the bound FALSE: both the trap run's signing branch
  -- (`progGameRunImplCombinedTrapCount_run_inr`) and the embed run's signing branch
  -- (`embedTrapIdxImpl_run_inr`) increment the counter and write the insertion-index table, but the
  -- embed's signing branch caches a *fresh* `c` (it never tests `j`), not the embedded `y`.  So a
  -- replay adversary making one signing query on `m` at counter `j`, receiving `(r, x =
  -- trapdoorSample c)` and outputting the forgery `(r, m, x)`, gives trap mass
  -- `table(forged) = some x ∧ idx(forged) = some j` with probability `1`, while the embed side
  -- needs the fresh `c = y` — a `1/|Range|` coincidence (witness: the bijective PSF, `j = 0`).
  --
  -- Route (freshness collapses the joint coupling to marginal + deterministic recovery): freshness
  -- ⟹ `forged.msg` was never signed ⟹ `forged` can only have been inserted by a random-oracle miss,
  -- at counter `j` (since `idx(forged) = some j`), where the embed caches exactly `y` — so on that
  -- slot the diagonal `cache(forged) = some y` is recovered from the run state, eliminating the
  -- free `y` from the embed win literal.  The marginal lift
  -- `evalSPMF_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl` then fires; the trap-count
  -- run is matched to `embedTrapFreshIdxSigImpl` by the freshness recovery
  -- `embedTrapIdxSigImpl_fresh_idx_cache_eq` and the write-only-table support invariant
  -- `progGameRunImplCombinedTrapCount_table_support`.  The omitted embed-side signing-slot mass on
  -- the right is nonnegative, so the bound is an inequality (trap ≤ embed), not an equality.
  --
  -- **The run-marginal half.** The cache/counter/idx/signedSet marginals of
  -- the trap-count run and the inline-fresh signed-set embed run coincide *as distributions*, via
  -- the generic `evalSPMF`-level state-projection transport
  -- `evalSPMF_map_run_simulateQ_eq_of_query_evalSPMF_map_eq` (which tolerates the never-failing
  -- answer-irrelevant trapdoor draw at each RO miss) instantiated as
  -- `map_run_progGameRunImplCombinedTrapCount_freshSig_proj`.  This discharges the *run-marginal*
  -- half of the coupling: it identifies the trap-count cache/idx/signedSet law with the
  -- `embedTrapFreshIdxSigImpl` law that the front-draw lift produces from
  -- `∑'y Pr[=y] · embedTrapIdxSigImpl … j y`.
  --
  -- **The table↔trapdoor-draw joint factorization.** On the
  -- trap run the forged point's write-only table entry `table(forged) = some preimg` was sampled
  -- `x ← trapdoorSample pk sk (cache(forged))` *inline* at the adaptively-determined forged
  -- programming event, and must be front-loaded to the embed side's *post-run* trapdoor draw
  -- `x ← trapdoorSample pk sk (cache(forged))`, matching the recorded `x` to the adversary output
  -- `preimg`.  FRESHNESS is exactly what makes this draw answer-irrelevant (an unsigned forged key
  -- is an RO miss, whose `x` enters only the write-only table — never the adversary view; a
  -- *signed* key returns `(r, x)` to the adversary, so its table draw is *not* deferrable, which is
  -- why dropping FRESH falsifies the bound).  Formalizing this defer-to-end of one
  -- answer-irrelevant write-only draw across the adaptive `simulateQ` fold is the genuine joint
  -- PMF×PMF coupling: a per-final-state induction (à la
  -- `tsum_probOutput_simulateQ_run_mul_of_rel`) showing the table at
  -- an unsigned key is an independent fresh `trapdoorSample (cache key)` conditioned on the final
  -- cache/idx/signedSet state, carried out in `trap_freshSig_le_winnerSlot_deferred`.
  --
  -- **Assembly.** Drop the verify/isShort conjuncts (they only restrict; FRESH stays) by
  -- `probEvent_mono`, then chain the trap-side table-defer
  -- `trap_freshSig_le_winnerSlot_deferred` (`G_trap ≤` the freshness-confined deferred functional
  -- expectation over the inline-fresh run) with the embed-side reduction
  -- `freshSig_winnerSlot_deferred_le_embed` (that expectation `≤` the winner-slot-restricted
  -- per-target embedding win).
  refine le_trans (probEvent_mono ?_)
    (le_trans (trap_freshSig_le_winnerSlot_deferred psf hr M Salt pk sk j adv hNF)
      (freshSig_winnerSlot_deferred_le_embed psf hr M Salt pk sk j adv))
  rintro w - ⟨⟨hflag, htbl⟩, hidx⟩
  refine ⟨⟨?_, htbl⟩, hidx⟩
  -- The flag conjunct `(decide fresh && (decide verify && isShort)) = true` carries the FRESH
  -- literal `forged.msg ∉ signedSet`, which is preserved verbatim.
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hflag
  exact hflag.1

open Classical in
omit [Fintype Salt] in
/-- **The per-slot front-loading deferred-sampling coupling (budget-scaled form).**

For a fixed programmed-entry index `j`, the *index-tagged* trap-exact-match mass — the trap event on
the counter-augmented run `progGameRunImplCombinedTrapCount` further restricted to the event that
the forged random-oracle point was *programmed at counter value `j`* (its recorded insertion index
is `some j`) — is bounded by the budget-scaled reservoir winner mass
`(qSign + qHash) · Pr[= some j | reservoirWinnerIndex (qSign + qHash)] · S (some j)` at slot `j`,
where `S (some j)` is the
winner-slot-restricted per-target embedding win of `embedTrapImpl … j y` averaged over `y ← $ᵗ
Range`.

This is derived from the floor-free form `reservoir_embed_commute_winner_floorFree` by the reservoir
arithmetic: at `j < qSign + qHash` the winner mass is exactly `(qSign + qHash)⁻¹`
(`probOutput_reservoirWinnerIndex_eq`), so `(qSign + qHash) · (qSign + qHash)⁻¹ = 1` absorbs the
budget factor and the floor-free bound passes through; at `j ≥ qSign + qHash` no programmed entry
can have recorded index `j` (`progGameRunImplCombinedTrapCount_idx_lt_budget`), so the left mass is
`0`.  The multi-target factor `qSign + qHash` pays the guessing loss. -/
lemma reservoir_embed_commute_winner [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) (j : ℕ) :
    Pr[fun w : (M × (Salt × Domain)) ×
          (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
            (((Salt × M) → Option ℕ) × ℕ)) =>
          ((decide (w.1.1 ∉ w.2.1.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
            w.2.2.1 (w.1.2.1, w.1.1) = some j |
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        Pr[= some j | reservoirWinnerIndex (qSign + qHash)] *
          ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x) &&
                decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  set Q := qSign + qHash with hQdef
  set S : ENNReal := ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk y
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] with hSdef
  set LHS : ENNReal := Pr[fun w : (M × (Salt × Domain)) ×
        (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
          (((Salt × M) → Option ℕ) × ℕ)) =>
        ((decide (w.1.1 ∉ w.2.1.1.1.2) &&
            (decide (psf.eval pk w.1.2.2 =
                (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
              psf.isShort w.1.2.2)) = true ∧
          w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
          w.2.2.1 (w.1.2.1, w.1.1) = some j |
      (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
        (adv.main pk)).run
        (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
          (fun _ => none), 0)] with hLHSdef
  -- Floor-free per-slot bound (the genuine front-loading commute).
  have hfloorFree : LHS ≤ S :=
    reservoir_embed_commute_winner_floorFree psf hr M Salt domainSample pk sk qSign qHash adv
      hreg hNF hForge hQ j
  change LHS ≤ (Q : ENNReal) * Pr[= some j | reservoirWinnerIndex Q] * S
  by_cases hj : j < Q
  · -- Slot `j` is within budget: the winner mass is exactly `Q⁻¹`, so `Q · Q⁻¹ = 1` absorbs the
    -- budget factor and the floor-free bound passes through.
    have hres : Pr[= some j | reservoirWinnerIndex Q] = (Q : ℝ≥0∞)⁻¹ :=
      probOutput_reservoirWinnerIndex_eq Q j hj
    rw [hres]
    have hQne : (Q : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    have hQtop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
    rw [ENNReal.mul_inv_cancel hQne hQtop, one_mul]
    exact hfloorFree
  · -- Slot `j` is beyond budget: no programmed entry has recorded index `j`, so `LHS = 0`.
    have hLHS0 : LHS = 0 := by
      rw [hLHSdef]
      refine probEvent_eq_zero ?_
      intro w hmem hP
      have hidxlt := progGameRunImplCombinedTrapCount_idx_lt_budget psf M Salt pk sk qSign qHash
        (adv.main pk) hQ hmem hP.2
      omega
    rw [hLHS0]
    exact zero_le

open Classical in
omit [Fintype Salt] in
/-- **M3, index-restricted: the reservoir↔embedding coupling (single fold-commute core).**

This is the deferred-sampling coupling of the GPV Step-2 exact-match close, with the
winner-slot bookkeeping made explicit: the per-target embedding win on the right is *restricted* to
the event that the **forged random-oracle point is the embedded (winner) slot**, read off the embed
final state as `r.2.1 (r.1.2.1, r.1.1) = some y` — at slot `wOpt.getD (qSign + qHash)` the
trap-sibling handler `embedTrapImpl` caches exactly the external target `y` at the winner
random-oracle miss, so the forged point being the winner slot is precisely its cached image being
`y`.

`reservoir_embed_commute` (M3) follows from this restricted form by dropping the winner-slot
restriction (`probOutput` monotonicity over the conjoined Bool): the *full* per-target win is at
least the winner-slot-restricted win, so the M3 bound is implied by the present, tighter bound.
Stating the restriction here lets the reservoir arithmetic (`probOutput_reservoirWinnerIndex_ge`,
the budget `N ≤ qSign + qHash` of `embedAtIndexImpl_run_count_le_budget` /
`combined_run_table_card_le`) be carried at the index-tagged level, while the per-winner-slot
front-loading joint coupling — pushing the trap run's inline winner draw `v⋆ ← $ᵗ Range` to the
front and re-expressing it as the embedded target `y ← $ᵗ Range` (mirroring
`evalSPMF_gpvRealImpl_eq_drawList_gpvRealImplTape`), together with the realized-entry index
partition of the trap mass — is supplied by `reservoir_embed_commute_winner`.

The bound holds for the same reason as M3: after the write-only-table deferral both runs maintain an
all-uniform random-oracle cache, and *averaging* the embedded target `y` over `$ᵗ Range`
reconstitutes the trap run's inline uniform winner draw `v⋆`.  The winner-slot-equals-forged-slot
contribution, summed over the `N ≤ qSign + qHash` realized programmed entries with per-slot
reservoir mass `1 / N ≥ 1 / (qSign + qHash)` and multiplied by `qSign + qHash`, already recovers the
full trap mass.  Trap-side index bookkeeping and the per-slot fold-commute supply the remaining
content. -/
lemma reservoir_embed_commute_residual [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
          (decide (w.1.1 ∉ w.2.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
        (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk)
          (adv.main pk)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
          ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                  (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x) &&
                decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  -- Abbreviations: `Q` the multi-target budget, `S wOpt` the per-slot averaged restricted embedding
  -- win, `trap` the LHS trap-exact-match mass.
  set Q := qSign + qHash with hQdef
  set S : Option ℕ → ENNReal := fun wOpt =>
    ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk y
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk (wOpt.getD Q) y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] with hSdef
  set trap : ENNReal := Pr[fun w : (M × (Salt × Domain)) ×
        ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
        (decide (w.1.1 ∉ w.2.1.1.2) &&
            (decide (psf.eval pk w.1.2.2 =
                (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
              psf.isShort w.1.2.2)) = true ∧
          w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
      (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk)
        (adv.main pk)).run
        ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
    with htrapdef
  change trap ≤ (Q : ENNReal) * ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex Q] * S wOpt
  -- **Per-slot index partition + commute.**  The per-entry mass function `g : ℕ → ENNReal` is the
  -- index-tagged trap-exact-match mass on the counter-augmented run
  -- `progGameRunImplCombinedTrapCount`, restricted to the event that the forged point was
  -- programmed at counter value `j`.  Summing `g j` over `j` recovers the full trap mass: the
  -- instrument is passive (`map_run_progGameRunImplCombinedTrapCount_proj`), so the augmented
  -- trap-event mass equals `trap`; and on every positive-probability trap outcome the forged
  -- point — being in the preimage table — has a recorded insertion index
  -- (`progGameRunImplCombinedTrapCount_idx_iff_table`), so the deterministic-index partition
  -- (`probEvent_eq_tsum_probEvent_index_aux`) tiles the trap mass over the recorded indices.  The
  -- per-slot domination `g j ≤ Q · Pr[= some j] · S` is the per-slot front-loading commute
  -- (`reservoir_embed_commute_winner`).
  obtain ⟨g, hgsum, hgle⟩ : ∃ g : ℕ → ENNReal,
      (∑' j : ℕ, g j) = trap ∧
      ∀ j : ℕ, g j ≤ (Q : ENNReal) * Pr[= some j | reservoirWinnerIndex Q] * S (some j) := by
    -- The counter-augmented run started from the projected empty state.
    set augRun := (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
        (adv.main pk)).run
        (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
          (fun _ => none), 0) with hAugRun
    -- The trap event lifted to the augmented state (referencing only the trap-state component).
    set Paug : (M × (Salt × Domain)) ×
        (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
          (((Salt × M) → Option ℕ) × ℕ)) → Prop := fun w =>
        (decide (w.1.1 ∉ w.2.1.1.1.2) &&
            (decide (psf.eval pk w.1.2.2 =
                (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
              psf.isShort w.1.2.2)) = true ∧
          w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2 with hPaug
    -- The forged-point recorded insertion index, read off the augmented final state.
    set idx : (M × (Salt × Domain)) ×
        (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
          (((Salt × M) → Option ℕ) × ℕ)) → Option ℕ := fun w =>
        w.2.2.1 (w.1.2.1, w.1.1) with hIdx
    refine ⟨fun j => Pr[fun w => Paug w ∧ idx w = some j | augRun], ?_, ?_⟩
    · -- Partition: `∑' j, g j = trap`.
      -- The augmentation is passive, so the augmented trap-event mass equals `trap`.
      have htrap_eq : trap = Pr[Paug | augRun] := by
        rw [htrapdef, ← map_run_progGameRunImplCombinedTrapCount_proj psf M Salt pk sk
          (adv.main pk) (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
            fun _ => none), (fun _ => none), 0), probEvent_map]
        rfl
      rw [htrap_eq]
      -- Every positive-probability trap outcome has a recorded forged-point index.
      refine (probEvent_eq_tsum_probEvent_index_aux augRun Paug idx ?_).symm
      intro w hw hPw
      have hmem : w ∈ support augRun := by
        by_contra hns
        exact hw (probOutput_eq_zero_of_not_mem_support hns)
      have hinv := progGameRunImplCombinedTrapCount_idx_iff_table psf M Salt pk sk
        (adv.main pk) (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
          fun _ => none), (fun _ => none), 0) (by intro k; simp) w hmem (w.1.2.1, w.1.1)
      rw [hIdx]
      exact (hinv.mp (by rw [hPaug] at hPw; rw [hPw.2]; exact Option.some_ne_none _))
    · -- Per-slot domination: the per-slot front-loading commute.
      intro j
      exact reservoir_embed_commute_winner psf hr M Salt domainSample pk sk qSign qHash
        adv hreg hNF hForge hQ j
  -- **Reservoir arithmetic.**  Push the budget factor `Q` through the winner sum and bound
  -- the trap partition `g` by the `some j` atoms of the reservoir winner average, discarding the
  -- never-firing `none` atom (`tsum_option`, terms nonnegative).
  calc trap = ∑' j : ℕ, g j := hgsum.symm
    _ ≤ ∑' j : ℕ, (Q : ENNReal) * Pr[= some j | reservoirWinnerIndex Q] * S (some j) :=
        ENNReal.tsum_le_tsum hgle
    _ = ∑' j : ℕ, (Q : ENNReal) * (Pr[= some j | reservoirWinnerIndex Q] * S (some j)) := by
        simp_rw [mul_assoc]
    _ ≤ (Q : ENNReal) *
        ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex Q] * S wOpt := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        rw [tsum_option _ ENNReal.summable]
        exact le_add_self

open Classical in
omit [Fintype Salt] in
/-- **M3 — the GPV Step-2 reservoir↔embedding deferred-sampling coupling.**

This is the joint coupling of the GPV Step-2 exact-match close, stated as the
*bound* needed by `gpv_perKey_exactMatch_le_reservoir`.  The left-hand side is the exact-match
winning mass of the trapdoor-recording combined run `progGameRunImplCombinedTrap` — the run obtained
from the combined sign-then-hash game after the write-only-table deferral (Lemma A,
`evalSPMF_run_progGameRunImplCombinedTrap_eq`).  The right-hand side is the multi-target factor
`qSign + qHash` times the full programmed-preimage reduction win, averaged over the reservoir winner
slot `wOpt ← reservoirWinnerIndex (qSign + qHash)` and the uniform target `y ← $ᵗ Range`: for each
slot/target the reduction runs the adversary under the all-uniform-cache trap-sibling embedding
handler `embedTrapImpl … (wOpt.getD (qSign + qHash)) y`, embeds the external challenge `y` at slot
`wOpt`, and wins when its forged preimage `r.1.2.2` equals the challenger's trapdoor preimage
`x ← trapdoorSample pk sk y`.

The bound holds because, after the write-only-table deferral, both runs maintain an all-uniform
random-oracle cache, and *averaging* the embedded target `y` over `$ᵗ Range` reconstitutes the
trap run's inline uniform winner draw `v⋆ ← $ᵗ Range`; the trap run's write-only
`table(forged) = trapdoorSample (cache(forged))` is then an independent fresh preimage that couples
to the reduction's external `x ~ trapdoorSample y` exactly when the winner slot is the forged point
(`cache(forged) = v⋆ ≡ y`).  The winner-slot-equals-forged-slot contribution, summed over the `N`
realized programmed entries with per-slot reservoir mass `1 / N` and multiplied by `qSign + qHash`
(with `N ≤ qSign + qHash`, `combined_run_table_card_le`), already recovers the full trap mass; the
reduction wins on *additional* coincidence paths (the forged slot differs from the embedded slot yet
its cached image coincides with `y`), so the inequality is one-directional (`≤`), not an equality.
The form is correct at `qSign + qHash = 0` (both sides vanish: no programmed entry is recorded, so
the trap mass is zero).

This is the deferred-sampling coupling where the `y`-draw lives *outside* the
`simulateQ` fold while `v⋆` lives *inside* it at an adaptively-determined fold position; the
front-loading joint-coupling is the core content of the GPV Step-2 close. -/
lemma reservoir_embed_commute [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
          (decide (w.1.1 ∉ w.2.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
        (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk)
          (adv.main pk)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
          ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                  (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
  -- M3 from the index-restricted form: bound the trap mass by the winner-slot-restricted RHS
  -- (`reservoir_embed_commute_residual`), then drop the winner-slot restriction
  -- `&& decide (… = some y)` from every per-target win (full win ≥ the restricted win).
  refine le_trans (reservoir_embed_commute_residual psf hr M Salt domainSample pk sk qSign qHash
    adv hreg hNF hForge hQ) ?_
  gcongr ((qSign + qHash : ℕ) : ENNReal) *
    ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
      ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] * ?_ with wOpt y
  -- Per-target: dropping the conjunct `decide (r.2.1 (r.1.2.1, r.1.1) = some y)` only increases
  -- the winning mass (`probOutput` monotone over the conjoined Bool body).
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x => ?_
  gcongr
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun r => ?_
  gcongr
  rw [probOutput_pure, probOutput_pure]
  by_cases hxr : r.1.2.2 = x
  · simp only [hxr, decide_true, Bool.true_and]
    split <;> simp
  · simp [hxr]

open Classical in
omit [Fintype Salt] in
/-- **Exact-match reservoir bound (Step-2 exact-match branch).** The exact-match winning mass on the
combined verify-extended run — a verifying fresh forgery `(msg, (r, s⋆))` whose forged preimage `s⋆`
exactly reproduces the simulator's hidden programmed preimage `sHidden` recorded in the table at the
forged point — is bounded by the multi-target factor `qSign + qHash` times the exact-match
programmed preimage advantage of `programmedPreimageReduction` at `(pk, sk)`.

The programmed-preimage reduction embeds its uniform target `y` at one uniformly chosen programmed
entry (reservoir sampling over the at most `qSign + qHash` programmed random-oracle entries); when
the embedded entry is the forged point and the forgery reproduces the hidden preimage, it wins the
single-target programmed-preimage experiment, paying the explicit `qSign + qHash` guessing loss.

This is the exact-match branch of the GPV Step-2 collision extraction; the
distinct-preimage branch is discharged by `gpv_perKey_distinct_le_collision`. -/
lemma gpv_perKey_exactMatch_le_reservoir [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
            (decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2 |
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
          (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        Pr[= true | (do
          let y ← ($ᵗ Range : ProbComp Range)
          let x ← psf.trapdoorSample pk sk y
          let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
          pure (decide (x' = x)) : ProbComp Bool)] := by
  -- **Step A (verify-strip, reduction-agnostic).**  Strip the verify continuation: on the forced
  -- cache hit at the forged point the verification read is table-passive, so the verify-extended
  -- exact-match mass is bounded by the exact-match event on `adv.main pk`'s combined run alone.
  refine le_trans
    (gpv_perKey_exactMatch_verifyStrip_le psf hr M Salt domainSample pk adv hForge) ?_
  -- **Step B (target factorization).**  Expand the reduction's averaged exact-match advantage over
  -- the uniform target draw `y ← $ᵗ Range` and push the `(qSign + qHash)` factor inside the sum, so
  -- the goal becomes the verify-stripped LHS bounded by
  --   `∑' y, (qSign + qHash) * (Pr[= y | $ᵗ Range] * Pr[per-y exact-match win])`.
  rw [programmedPreimage_perKey_eq_tsum psf hr M Salt domainSample pk sk qSign qHash adv,
    ← ENNReal.tsum_mul_left]
  -- **N4 rewrite.**  Inside every per-target factor `P_y`, replace the pre-sampled-index
  -- handler `embedAtIndexImpl` by its trapdoor-uniform sibling `embedTrapImpl` (N4); after this the
  -- embed run has an all-uniform cache (modulo `y` at the winner slot), matching the cache marginal
  -- of the trapdoor-recording combined run.
  have hN4 : ∀ y : Range,
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk y
        let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
        pure (decide (x' = x)) : ProbComp Bool)]
      = Pr[= true | (do
          let x ← psf.trapdoorSample pk sk y
          let wOpt ← reservoirWinnerIndex (qSign + qHash)
          let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
              (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
          pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
    intro y
    refine probOutput_congr rfl ?_
    simp only [programmedPreimageReduction_eq_run, bind_assoc, pure_bind]
    refine evalSPMF_bind_congr fun x _ => ?_
    refine evalSPMF_bind_congr fun wOpt _ => ?_
    -- The remaining `run >>= pure ∘ decide` factor is equidistributed under N4.
    rw [evalSPMF_bind, evalSPMF_bind,
      evalSPMF_run_embedAtIndexImpl_eq_embedTrap psf M Salt domainSample pk sk
        (wOpt.getD (qSign + qHash)) y hreg hNF (adv.main pk)
        ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))]
  -- **N4 applied.**  Replace every per-target embed run by its all-uniform-cache trap
  -- sibling `embedTrapImpl`, so the goal RHS is the reservoir/target average of the *trap-sibling*
  -- embedding run, matching the cache marginal of the trapdoor-recording combined run.
  simp only [hN4]
  -- **M1 (Lemma A — write-only-table deferral).**  Push the verify-stripped LHS exact-match mass
  -- off the eval-caching combined run `progGameRunImplCombined` onto its trapdoor-recording sibling
  -- `progGameRunImplCombinedTrap`, an exact equidistribution under `hreg` with the event unchanged.
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalSPMF_run_progGameRunImplCombinedTrap_eq psf M Salt domainSample pk sk hreg (adv.main pk)
      ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none))]
  -- **M4 (assembly).**  Pull the reservoir winner draw `wOpt` to the front of each per-target win,
  -- swap the target/reservoir averages, fold in the multi-target factor, and discharge the result
  -- against the reservoir↔embedding coupling `reservoir_embed_commute` (M3).
  have hpull : ∀ i : Range,
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk i
        let wOpt ← reservoirWinnerIndex (qSign + qHash)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
            (wOpt.getD (qSign + qHash)) i) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x)) : ProbComp Bool)]
      = ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
        Pr[= true | (do
          let x ← psf.trapdoorSample pk sk i
          let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
              (wOpt.getD (qSign + qHash)) i) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
          pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
    intro i
    rw [probOutput_bind_eq_tsum]
    simp_rw [probOutput_bind_eq_tsum (reservoirWinnerIndex (qSign + qHash)),
      probOutput_bind_eq_tsum (psf.trapdoorSample pk sk i), ← ENNReal.tsum_mul_left, ← mul_assoc]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun wOpt => tsum_congr fun x => by ring
  -- Reassociate the per-target sum into the multi-target factor times the reservoir/target average
  -- that `reservoir_embed_commute` equates to the trap exact-match mass.
  have hrhs :
      (∑' i : Range, ((qSign + qHash : ℕ) : ENNReal) *
          (Pr[= i | ($ᵗ Range : ProbComp Range)] *
            ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
              Pr[= true | (do
                let x ← psf.trapdoorSample pk sk i
                let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                    (wOpt.getD (qSign + qHash)) i) (adv.main pk)).run
                  ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
                pure (decide (r.1.2.2 = x)) : ProbComp Bool)]))
        = ((qSign + qHash : ℕ) : ENNReal) *
          ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
            ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
              Pr[= true | (do
                let x ← psf.trapdoorSample pk sk y
                let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                    (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
                  ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
                pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
    rw [← ENNReal.tsum_mul_left]
    simp_rw [← ENNReal.tsum_mul_left, ← mul_assoc]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun wOpt => tsum_congr fun y => by ring
  simp_rw [hpull]
  rw [hrhs]
  exact reservoir_embed_commute psf hr M Salt domainSample pk sk qSign qHash adv hreg hNF
    hForge hQ

open Classical in
omit [Fintype Salt] in
/-- **Step 2 (collision extraction): the keygen-averaged programmed freshness verify-Bool game is
bounded by the collision and exact-match reduction advantages.**

In the programmed sign-then-hash game `progGameVerifyFresh`, every random-oracle entry was
programmed as `psf.eval pk s` for a hidden short preimage `s ← domainSample pk`.  Under `hForge` the
forgery `(msg, (r, s⋆))` lands on a programmed entry, so the verification read is a cache hit
returning `psf.eval pk sHidden` for the simulator's hidden preimage `sHidden` at `(r, msg)`; a
verifying fresh forgery therefore satisfies `psf.eval pk s⋆ = psf.eval pk sHidden` with both
preimages short (the forged one by the verifier's `isShort` check, the hidden one by `hcorrect` and
`hreg`).  This splits into:

* the **distinct-preimage branch** `sHidden ≠ s⋆`, a collision under `psf.eval` extracted by the
  collision reduction `reduction` (which records the hidden preimage at each programmed point and
  returns `(sHidden, s⋆)`), bounding that mass by `collisionFindingAdvantage (reduction …)`; and
* the **exact-match branch** `sHidden = s⋆`, where the forgery reproduces the simulator's hidden
  preimage; the programmed-preimage reduction `programmedPreimageReduction` embeds its target `y` at
  one uniformly chosen programmed entry (reservoir sampling over the at most `qSign + qHash`
  entries), winning when the embedded entry is the forged point, which costs the explicit
  multi-target factor `qSign + qHash`.

This is the Step-2 collision extraction of the GPV proof, stated pinned over the concrete
programmed forgery game and the concrete reductions. -/
theorem gpv_progGameVerifyFreshAvg_le_collisionAdv_add_preimageAdv [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[= true | (𝒮[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
        progGameVerifyFresh psf hr M Salt adv domainSample pksk.1]
      ≤ collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) := by
  classical
  -- Reduce the keygen-average to a per-key `(pk, sk)` bound via the averaging skeleton SL-A,
  -- then discharge that per-key bound (the distinct-collision transfer + the reservoir exact-match
  -- bound) — the Step-2 collision extraction.
  refine gpv_progGameVerifyFreshAvg_le_of_perKey psf hr M Salt qSign qHash adv domainSample ?_
  intro pksk hmem
  -- Lift the game success onto the combined run, split into the distinct and exact-match branches,
  -- transfer the distinct branch to the collision reduction, and hand the exact branch to the
  -- reservoir bound.
  rw [progGameVerifyFresh_eq_probEvent_combined psf hr M Salt domainSample pksk.1 adv,
    reduction_collision_eq_probEvent_combined psf hr M Salt domainSample pksk.1 adv]
  refine le_trans (probEvent_mono (fun w _ hw => ?_) :
      _ ≤ Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
          ((decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) ≠ some w.1.1.2.2) ∨
            ((decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2) | _]) ?_
  · by_cases heq : w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2
    · exact Or.inr ⟨hw, heq⟩
    · exact Or.inl ⟨hw, heq⟩
  refine le_trans (probEvent_or_le _ _ _) ?_
  gcongr
  · exact gpv_perKey_distinct_le_collision psf hr M Salt domainSample pksk.1 pksk.2
      (hcorrect pksk.1 pksk.2 hmem) (hreg pksk.1 pksk.2 hmem) adv hForge
  · exact gpv_perKey_exactMatch_le_reservoir psf hr M Salt domainSample pksk.1 pksk.2 qSign qHash
      adv (hreg pksk.1 pksk.2 hmem) (hNF pksk.1 pksk.2 hmem) hForge (hQ pksk.1)

/-- **Full split GPV game-hop**: every successful fresh forgery falls into one of two cases.

1. **Distinct-preimage branch:** the forgery differs from the simulator's hidden programmed
   preimage at the forged point, yielding a collision under `psf.eval`.
2. **Exact-match branch:** the forgery exactly reproduces the simulator's hidden programmed
   preimage at that point. To capture this branch, the reduction guesses one of the at most
   `qSign + qHash` programmed entries and turns success there into a win in the single-target
   programmed-preimage experiment.

The only additional failure mode is a salt collision, bounded by `collisionBound`.

The honest trapdoor sampler is assumed total (`hNF`): for every key pair and target the sampler
`psf.trapdoorSample` never fails (`NeverFail`).  This is the standard GPV08 well-formedness
condition that the trapdoor inversion is a genuine distribution; it is the hypothesis that keeps
probability mass during the real↔programmed sign-then-hash hop and is not implied by `hcorrect`
(which constrains only the *support* of the sampler) nor by `hreg` (which equates only the *total
masses* of the two joint distributions).

The forger is assumed to query its forgery point (`hForge`, `ForgesQueriedPoint`): the standard
ROM well-formedness condition that the forgery lands on a programmed random-oracle entry, so the
collision/exact-match extraction observes the simulator's hidden preimage at that point. -/
theorem forgery_yields_collision_or_exact_match [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    adv.advantage (runtime M Salt) ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) +
        collisionBound Salt qSign qHash := by
  refine le_trans (gpv_advantage_le_progGameVerifyFreshAvg_add_collisionBound psf hr M Salt
    qSign qHash adv domainSample hreg hNF hQ) ?_
  gcongr
  exact gpv_progGameVerifyFreshAvg_le_collisionAdv_add_preimageAdv psf hr M Salt
    hcorrect qSign qHash adv domainSample hreg hNF hForge hQ

/-- **Collision-only specialization of the GPV split bound under a PSF preimage min-entropy
bound.**  This is `forgery_yields_collision_or_exact_match` with the exact-match
(programmed-preimage) branch controlled by an explicit preimage min-entropy / one-wayness bound
`εpp`: the adversary's chance of reproducing the simulator's hidden short preimage at a programmed
point is at most `εpp` (`hMinEntropy`), so the multi-target exact-match contribution is at most
`(qSign + qHash) · εpp`.  It is *derived* from the split bound and carries no independent proof
obligation.

The exact-match term is *bounded*, not eliminated: `programmedPreimageAdvantage ≥ 1 / |Domain| > 0`
for a finite domain (reproducing a sampled preimage is always possible with nonzero probability),
so a clean collision-only bound (`εpp = 0`) is unsatisfiable.  Specializing `εpp` to a concrete PSF
preimage min-entropy bound (e.g. for Falcon) yields the quantitative collision bound. -/
theorem forgery_yields_collision [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (εpp : ℝ≥0∞)
    (hMinEntropy : programmedPreimageAdvantage (psf := psf) (hr := hr)
      (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) ≤ εpp) :
    adv.advantage (runtime M Salt) ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) * εpp +
        collisionBound Salt qSign qHash := by
  refine le_trans (forgery_yields_collision_or_exact_match psf hr M Salt hcorrect qSign qHash
    adv domainSample hreg hNF hForge hQ) ?_
  gcongr

/-- **Collision-style GPV PFDH bound in the random-oracle model, under a preimage min-entropy
bound**.

For any adversary `A` making at most `qSign` signing queries against the GPV hash-and-sign
scheme with a correct PSF and `k`-bit salts, and making at most `qHash` random-oracle queries,
there exists a collision-finding reduction `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{collision}(B) + (qSign + qHash) · εpp + (qSign + qHash)² / (2 · |Salt|)`

where `εpp` bounds the exact-match (programmed-preimage) branch: the chance that an adversary
reproduces the simulator's hidden short preimage at a programmed point is at most `εpp`
(`hMinEntropy`), the PSF preimage min-entropy / one-wayness assumption. The distinct-preimage
branch gives the collision term; the exact-match branch the `(qSign + qHash) · εpp` term. This is a
specialization of `euf_cma_split_bound` and is derived from it; the exact-match term is *bounded*,
not dropped, since `programmedPreimageAdvantage ≥ 1 / |Domain| > 0` for a finite domain.

The salt-collision term `(qSign + qHash)² / (2 · |Salt|)` is `collisionBound`, the closed birthday
form of the union sum `∑_{j < qSign} (j + qHash) / |Salt|` the telescope establishes: a fresh
signing salt colliding with any previously recorded `(salt, message)` random-oracle input (a
prior signing salt or an adversary hash query). It is the constant this theorem proves; the
`collisionBound` docstring records how it relates to the GPV08 and [FGdG+25] constants. For Falcon
with 40-byte salts (`|Salt| = 2^320`), this is `2^{-191}` even for `qSign = qHash = 2^64`.

This form carries the `ForgesQueriedPoint` convention as a hypothesis and leaves `εpp` abstract.
The endpoint for consumers is `euf_cma_collision_bound_of_queryBound`, which discharges the
convention by the append-forgery-query compiler and prices `εpp` by the trapdoor guessing
probability.

References: GPV08 Section 6; BDF+11 for the QROM extension. -/
theorem euf_cma_collision_bound [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk)
    (hreg : ∃ domainSample : PK → ProbComp Domain, ∀ (pk : PK) (sk : SK),
      (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ∀ ds : PK → ProbComp Domain, ForgesQueriedPoint psf hr M Salt adv ds)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (εpp : ℝ≥0∞)
    (hMinEntropy : ∀ ds : PK → ProbComp Domain,
      programmedPreimageAdvantage (psf := psf) (hr := hr)
        (programmedPreimageReduction psf hr M Salt adv ds qSign qHash) ≤ εpp) :
    ∃ (red : CollisionAdversary (PK := PK) (Domain := Domain)),
      adv.advantage (runtime M Salt) ≤
        collisionFindingAdvantage (psf := psf) (hr := hr) red +
        ((qSign + qHash : ℕ) : ENNReal) * εpp +
        collisionBound Salt qSign qHash := by
  obtain ⟨domainSample, h⟩ := hreg
  exact ⟨reduction psf hr M Salt adv domainSample,
    forgery_yields_collision psf hr M Salt hcorrect qSign qHash adv domainSample h hNF
      (hForge domainSample) hQ εpp (hMinEntropy domainSample)⟩

/-- **Split GPV PFDH bound in the random-oracle model**.

This theorem makes both branches of the GPV proof explicit:

- a collision term for the distinct-preimage branch,
- a programmed-preimage replay term for the exact-match branch, with the explicit
  multi-target factor `qSign + qHash`,
- and the birthday salt-collision term.

It is the most honest generic statement available from the current API, before any additional
PSF-specific min-entropy lemma collapses the exact-match branch into the collision branch.

This form carries the `ForgesQueriedPoint` convention as a hypothesis; the endpoint for consumers
is `euf_cma_split_bound_of_queryBound`, which discharges it for every adversary at one extra hash
query via the append-forgery-query compiler. -/
theorem euf_cma_split_bound [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk)
    (hreg : ∃ domainSample : PK → ProbComp Domain, ∀ (pk : PK) (sk : SK),
      (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ∀ ds : PK → ProbComp Domain, ForgesQueriedPoint psf hr M Salt adv ds)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    ∃ (collisionRed : CollisionAdversary (PK := PK) (Domain := Domain))
      (exactMatchRed : ProgrammedPreimageAdversary
        (PK := PK) (Domain := Domain) (Range := Range)),
      adv.advantage (runtime M Salt) ≤
        collisionFindingAdvantage (psf := psf) (hr := hr) collisionRed +
          ((qSign + qHash : ℕ) : ENNReal) *
            programmedPreimageAdvantage (psf := psf) (hr := hr) exactMatchRed +
          collisionBound Salt qSign qHash := by
  obtain ⟨domainSample, h⟩ := hreg
  exact ⟨reduction psf hr M Salt adv domainSample,
    programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash,
    forgery_yields_collision_or_exact_match psf hr M Salt hcorrect qSign qHash adv
      domainSample h hNF (hForge domainSample) hQ⟩

end GPVHashAndSign
