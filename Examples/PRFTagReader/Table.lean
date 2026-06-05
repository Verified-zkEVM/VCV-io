/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.PRFReductions

/-!
# PRF Tag/Reader Protocol — Composed-Handler Eager-Table Equivalence

The eager-table reformulation of the composed ideal handlers. Milestones 1-4 of the
unlinkability reduction:

* **Milestone 1**: the reader-table-iteration lemma `idealCacheMapM`.
* **Milestone 2**: composed multiple-world eager-table equivalence
  `evalDist_simulateQ_multipleIdealQueryImpl_run'_eq_tableExtending`.
* **Milestone 3**: composed single-world eager-table equivalence
  `evalDist_simulateQ_singleIdealQueryImpl_run'_eq_tableExtending`.
* **Milestone 4**: eager-form success probabilities `probOutput_*_run'_eq_tableSample`
  and the `projectTable` helper that bridges the two table types.

All declarations live inside `section EagerComposed`, whose variable block drops `K`
relative to the enclosing `UnlinkReduction` section (the PRF key type does not appear in
the eager-table reformulation).
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ### Composed-handler eager-table equivalence

The composed ideal handler `multipleIdealQueryImpl` embeds the lazy random oracle inside a
stateful handler over `UnlinkOracleSpec`. The lemma below lifts the top-level lazy-vs-eager-table
equivalence (`OracleComp.evalDist_simulateQ_randomOracle_run'_eq_tableExtending`) to this composed
handler: running `multipleIdealQueryImpl` from `(s, c)` has the same output distribution as
sampling a full random-oracle table `g`, overlaying the cache `c`, and running the *real*
multiple-session handler `multipleTableHandler` deterministically against that table.

This is the multiple-world half of the recommended eager-sampling reformulation; it does not touch
the coupled-table union bound or the two residue `sorry`s. -/

section EagerComposed

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (TagId × Nonce → Digest)]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]
  [SampleableType ((TagId × Fin sessionsPerTag) × Nonce → Digest)]

/-- Deterministic real multiple-session handler keyed directly on a random-oracle table
`g : TagId × Nonce → Digest`. This is `unlinkMultipleQueryImpl prfs k` for any PRF package whose
`evalMultiple k` is the curried table; phrasing it on the raw table lets the eager-table
equivalence be stated without a `prfs`/`k` witness. -/
noncomputable def multipleTableHandler (g : TagId × Nonce → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId) ProbComp) :=
  unlinkTagQueryImpl (Slot := TagId) (fun tag nonce => g (tag, nonce))
    (multiplePattern sessionsPerTag) +
  unlinkReaderQueryImpl (Slot := TagId) (fun tag nonce => g (tag, nonce))
    (multiplePattern sessionsPerTag)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ multipleIdealQueryImpl` of a `query_bind`, run from a state and projected to its
output bit: the per-query handler followed by the recursive simulation of the continuation.
General-codomain version of `multipleIdeal_run'_query_bind`. -/
lemma multipleIdeal_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
        (liftM (OracleSpec.query t) >>= f)).run' sM =
      (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag) t sM) >>= fun p =>
        (simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
          (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]; rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `simulateQ multipleTableHandler` of a `query_bind`, run from a state and projected to its
output: the per-query handler followed by the recursive simulation of the continuation. -/
lemma multipleTable_run'_query_bind' {α : Type} (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId) :
    (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag) g)
        (liftM (OracleSpec.query t) >>= f)).run' s =
      (multipleTableHandler (sessionsPerTag := sessionsPerTag) g t s) >>= fun p =>
        (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag) g)
          (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]; rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `multipleTableHandler` on a tag query with the slot budget exhausted: returns `none`. -/
lemma multipleTableHandler_tag_run_of_not_lt (g : TagId × Nonce → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (multipleTableHandler (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) s) =
      pure (none, s) := by
  unfold multipleTableHandler
  rw [QueryImpl.add_apply_inl]
  change (unlinkTagQueryImpl (fun tag nonce => g (tag, nonce))
    (multiplePattern sessionsPerTag) tag).run s = _
  unfold unlinkTagQueryImpl
  simp [StateT.run_bind, StateT.run_get, hslot]

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `multipleTableHandler` on a tag query with a free slot: sample a nonce, look up the table at
`(tag, nonce)`, advance the session counter. -/
lemma multipleTableHandler_tag_run_of_lt (g : TagId × Nonce → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (multipleTableHandler (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) s) =
      ($ᵗ Nonce) >>= fun nonce =>
        pure (some (⟨nonce, g (tag, nonce)⟩ : TagTranscript Nonce Digest),
          { s with sessionsUsed :=
            Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }) := by
  unfold multipleTableHandler
  rw [QueryImpl.add_apply_inl]
  change (unlinkTagQueryImpl (fun tag nonce => g (tag, nonce))
    (multiplePattern sessionsPerTag) tag).run s = _
  unfold unlinkTagQueryImpl
  simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    hslot, multiplePattern, bind_pure_comp]

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `multipleTableHandler` on a reader query: deterministic acceptance against the table, with the
state untouched. -/
lemma multipleTableHandler_reader_run (g : TagId × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    (multipleTableHandler (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript) s) =
      pure (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
        (fun tag nonce => g (tag, nonce))
        (multiplePattern sessionsPerTag) transcript), s) := by
  unfold multipleTableHandler unlinkReaderQueryImpl
  rw [QueryImpl.add_apply_inr]; rfl

omit [DecidableEq Digest] in
/-- **Cache-branch eager-table step.** A single lazy-random-oracle lookup `idealCacheStep` at a
domain point `d`, followed by sampling a full random-oracle table for the remaining computation,
has the same output distribution as directly sampling the table: the fresh on-demand draw of a
cache miss is absorbed by `OracleComp.evalDist_uniformSample_bind_update_map`.

This is the per-query workhorse for an eager-sampling reformulation of the composed ideal handler:
it reconciles the lazy cache step with the up-front table draw, generalized over an arbitrary
continuation `ψ` of the resulting full table. -/
lemma evalDist_idealCacheStep_bind_uniformTable {D : Type} [DecidableEq D] [Finite D]
    [Finite Digest] [SampleableType (D → Digest)]
    {β : Type} (c : (D →ₒ Digest).QueryCache) (d : D) (ψ : (D → Digest) → β) :
    𝒟[do let r ← idealCacheStep (Digest := Digest) c d;
          let g ← $ᵗ (D → Digest);
          pure (ψ (OracleComp.tableExtending r.2 g))] =
      𝒟[do let g ← $ᵗ (D → Digest); pure (ψ (OracleComp.tableExtending c g))] := by
  classical
  haveI : Nonempty Digest := ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  unfold idealCacheStep
  rcases hc : c d with _ | u
  · dsimp only
    rw [show (($ᵗ Digest) >>= fun u => pure (u, c.cacheQuery d u)) >>=
              (fun r => ($ᵗ (D → Digest)) >>= fun g =>
                pure (ψ (OracleComp.tableExtending r.2 g)))
          = ($ᵗ Digest) >>= fun u => ($ᵗ (D → Digest)) >>= fun g =>
              pure ((fun g' => ψ (OracleComp.tableExtending c g')) (Function.update g d u))
        from by
          rw [bind_assoc]; refine bind_congr fun u => ?_
          rw [pure_bind]; refine bind_congr fun g => ?_
          rw [OracleComp.tableExtending_cacheQuery,
            OracleComp.tableExtending_update_of_none c g hc u]]
    exact OracleComp.evalDist_uniformSample_bind_update_map (R := Digest) d
      (fun g' => ψ (OracleComp.tableExtending c g'))
  · dsimp only
    rw [pure_bind]

omit [DecidableEq Digest] in
/-- **Single-cell extraction at the bind level.** Drawing a uniform function table `g : D → R` and
then running an arbitrary continuation that depends on `g` and on the cell value `g t` is
distributionally equal to drawing the cell value `u : R` uniformly first, then drawing `g`, then
running the continuation against the `t`-update of `g` (whose `t`-cell is `u`).

This is the bind-level lift of `evalDist_uniformSample_bind_update_map`: instead of carrying a
`pure (ψ g)`-only continuation, the result is parametric over an arbitrary `ProbComp β`-valued
continuation, exposing the cell read `g t` outside the table draw. It is the reusable
cell-extraction step underlying the cell-patch coupling in the hop-A fresh tag-step branch. -/
lemma evalDist_uniformSample_bind_cell_extract {D R : Type}
    [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (t : D) {β : Type}
    (cont : (D → R) → R → ProbComp β) :
    𝒟[do let g ← $ᵗ (D → R); cont g (g t)] =
      𝒟[do let u ← $ᵗ R; let g ← $ᵗ (D → R); cont (Function.update g t u) u] := by
  classical
  -- Factor both sides through a `pure (g, g t)` / `pure (Function.update g t u, u)` pair, then
  -- apply `evalDist_uniformSample_bind_update_map` on the inner pure layer.
  have hLeq :
      (do let g ← $ᵗ (D → R); cont g (g t))
        = ((do let g ← $ᵗ (D → R); pure (g, g t)) >>= fun p : (D → R) × R => cont p.1 p.2) := by
    simp
  have hReq :
      (do let u ← $ᵗ R; let g ← $ᵗ (D → R); cont (Function.update g t u) u)
        = ((do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u, u))
            >>= fun p : (D → R) × R => cont p.1 p.2) := by
    simp
  rw [hLeq, hReq]
  have hpureEq : ∀ (g : D → R) (u : R),
      (Function.update g t u, u)
        = ((fun g' : D → R => (g', g' t)) (Function.update g t u)) := fun _ _ => by simp
  have hcore :
      𝒟[do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u, u)]
        = 𝒟[do let g ← $ᵗ (D → R); pure (g, g t)] := by
    have hrw :
        (do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u, u))
          = (do let u ← $ᵗ R; let g ← $ᵗ (D → R);
                pure ((fun g' : D → R => (g', g' t)) (Function.update g t u))) :=
      bind_congr fun u => bind_congr fun g => by rw [hpureEq g u]
    rw [hrw]
    exact OracleComp.evalDist_uniformSample_bind_update_map (R := R) t (fun g' => (g', g' t))
  -- Lift `hcore` through the outer continuation `fun p => cont p.1 p.2`.
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun p => ?_
  rw [show Pr[= p | (do let g ← $ᵗ (D → R); pure (g, g t))]
        = Pr[= p | (do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u, u))]
      from probOutput_congr rfl hcore.symm]

/-! #### Milestone 1: the reader table-iteration lemma

`idealCacheMapM` folds the lazy random-oracle lookup `idealCacheStep` over a list of cache cells —
this is exactly the reader query's behaviour under the composed ideal handler. The lemmas below lift
the single-cell eager-table absorption (`evalDist_idealCacheStep_bind_uniformTable`) to a whole
list, by induction on the cell list. The end result: folding `idealCacheStep` over a list `l` and
then sampling one full table is distributionally the same as sampling the full table up front and
reading the cells deterministically against `tableExtending`. -/

omit [DecidableEq Digest] in
/-- After one `idealCacheStep` at `d`, the resulting cache stores the produced digest at `d`. -/
lemma idealCacheStep_cache_self {D : Type} [DecidableEq D]
    (c : (D →ₒ Digest).QueryCache) (d : D)
    (r : Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheStep (Digest := Digest) c d)) :
    r.2 d = some r.1 := by
  classical
  unfold idealCacheStep at hr
  rcases hc : c d with _ | u
  · rw [hc, mem_support_bind_iff] at hr
    obtain ⟨u, _, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp [QueryCache.cacheQuery]
  · rw [hc, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact hc

omit [DecidableEq Digest] in
/-- After one `idealCacheStep` at `d`, the resulting cache's domain includes `d`. -/
lemma idealCacheStep_cache_self_dom {D : Type} [DecidableEq D]
    (c : (D →ₒ Digest).QueryCache) (d : D)
    (r : Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheStep (Digest := Digest) c d)) :
    (r.2 d).isSome := by
  rw [idealCacheStep_cache_self c d r hr]; rfl

omit [DecidableEq Digest] in
/-- One `idealCacheStep` at `d` leaves all other cells of the cache untouched. -/
lemma idealCacheStep_cache_off {D : Type} [DecidableEq D]
    (c : (D →ₒ Digest).QueryCache) (d : D)
    (r : Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheStep (Digest := Digest) c d))
    (d' : D) (hd' : d' ≠ d) :
    r.2 d' = c d' := by
  classical
  unfold idealCacheStep at hr
  rcases hc : c d with _ | u
  · rw [hc, mem_support_bind_iff] at hr
    obtain ⟨u, _, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp [QueryCache.cacheQuery_of_ne _ _ hd']
  · rw [hc, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rfl

omit [DecidableEq Digest] in
/-- One `idealCacheStep` at `e` leaves any already-cached cell `d` unchanged. -/
lemma idealCacheStep_preserves_some {D : Type} [DecidableEq D]
    (c : (D →ₒ Digest).QueryCache) (e : D)
    (r : Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheStep (Digest := Digest) c e))
    (d : D) (hd : (c d).isSome) :
    r.2 d = c d := by
  classical
  by_cases hde : d = e
  · subst hde
    unfold idealCacheStep at hr
    rcases hc : c d with _ | u
    · rw [hc] at hd; simp at hd
    · rw [hc, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hc
  · exact idealCacheStep_cache_off c e r hr d hde

omit [DecidableEq Digest] in
/-- Folding `idealCacheStep` over `l` leaves any already-cached cell `d` unchanged. -/
lemma idealCacheMapM_cache_off {D : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache)
    (r : List Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheMapM (Digest := Digest) l c))
    (d : D) (hd : (c d).isSome) :
    r.2 d = c d := by
  induction l generalizing c r with
  | nil =>
    simp only [idealCacheMapM, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  | cons e es ih =>
    simp only [idealCacheMapM, mem_support_bind_iff] at hr
    obtain ⟨step, hstep, rest, hrest, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    have hstepd : (step.2 d).isSome := by
      rw [idealCacheStep_preserves_some c e step hstep d hd]; exact hd
    rw [ih step.2 rest hrest hstepd, idealCacheStep_preserves_some c e step hstep d hd]

omit [DecidableEq Digest] in
/-- Folding `idealCacheStep` over `l` leaves any cell `d` outside `l` unchanged. -/
lemma idealCacheMapM_cache_not_mem {D : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache)
    (r : List Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheMapM (Digest := Digest) l c))
    (d : D) (hd : d ∉ l) :
    r.2 d = c d := by
  induction l generalizing c r with
  | nil =>
    simp only [idealCacheMapM, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  | cons e es ih =>
    simp only [List.mem_cons, not_or] at hd
    obtain ⟨hde, hdes⟩ := hd
    simp only [idealCacheMapM, mem_support_bind_iff] at hr
    obtain ⟨step, hstep, rest, hrest, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rw [ih step.2 rest hrest hdes, idealCacheStep_cache_off c e step hstep d hde]

omit [DecidableEq Digest] in
/-- Every result of folding `idealCacheStep` over a list `l` from cache `c` has a final cache that
caches all cells of `l` and agrees with `c` off the cells of `l`. Consequently, overlaying that
final cache on any full table reads each cell of `l` as the stored digest, so the produced read
list is `l.map (tableExtending r.2 g)`. -/
lemma idealCacheMapM_support {D : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache)
    (r : List Digest × (D →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheMapM (Digest := Digest) l c))
    (g : D → Digest) :
    r.1 = l.map (OracleComp.tableExtending r.2 g) := by
  induction l generalizing c r with
  | nil =>
    simp only [idealCacheMapM, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  | cons d ds ih =>
    simp only [idealCacheMapM, mem_support_bind_iff] at hr
    obtain ⟨step, hstep, rest, hrest, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    have hstepd : step.2 d = some step.1 :=
      idealCacheStep_cache_self c d step hstep
    have hrestd : rest.2 d = some step.1 := by
      have hoff := idealCacheMapM_cache_off ds step.2 rest hrest d
        (idealCacheStep_cache_self_dom c d step hstep)
      rw [hoff, hstepd]
    simp only [List.map_cons]
    rw [ih step.2 rest hrest]
    congr 1
    simp [OracleComp.tableExtending, hrestd]

omit [DecidableEq Digest] in
/-- **Reader table-iteration lemma (Milestone 1).** Folding the lazy random-oracle lookup
`idealCacheStep` over a list of cells `l`, then sampling one full random-oracle table for the
remaining computation, has the same output distribution as directly sampling the table: every
fresh on-demand draw of a cache miss is absorbed into the up-front table draw.

This lifts the single-cell absorption `evalDist_idealCacheStep_bind_uniformTable` to a whole list
by induction on `l`, and is the reader-query workhorse of the eager-sampling reformulation. -/
lemma evalDist_idealCacheMapM_bind_uniformTable {D : Type} [DecidableEq D] [Finite D]
    [Finite Digest] [SampleableType (D → Digest)]
    {β : Type} (l : List D) (c : (D →ₒ Digest).QueryCache) (ψ : (D → Digest) → β) :
    𝒟[do let r ← idealCacheMapM (Digest := Digest) l c;
          let g ← $ᵗ (D → Digest);
          pure (ψ (OracleComp.tableExtending r.2 g))] =
      𝒟[do let g ← $ᵗ (D → Digest); pure (ψ (OracleComp.tableExtending c g))] := by
  induction l generalizing c with
  | nil =>
    simp only [idealCacheMapM, pure_bind]
  | cons d ds ih =>
    simp only [idealCacheMapM]
    have hreassoc :
        (idealCacheStep c d >>= fun r =>
            idealCacheMapM ds r.2 >>= fun rs =>
              pure (r.1 :: rs.1, rs.2)) >>= (fun r =>
          ($ᵗ (D → Digest)) >>= fun g => pure (ψ (OracleComp.tableExtending r.2 g)))
        = idealCacheStep c d >>= fun r =>
            idealCacheMapM ds r.2 >>= fun rs =>
              ($ᵗ (D → Digest)) >>= fun g =>
                pure (ψ (OracleComp.tableExtending rs.2 g)) := by
      rw [bind_assoc]; refine bind_congr fun r => ?_
      rw [bind_assoc]; refine bind_congr fun rs => ?_
      rw [pure_bind]
    rw [hreassoc]
    refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable c d ψ)
    rw [evalDist_bind, evalDist_bind]
    refine congrArg (fun h => 𝒟[idealCacheStep c d] >>= h) ?_
    exact funext fun r => ih r.2

/-- Two probabilistic samples may be drawn in either order: the output distribution of drawing
`mx` then `my` and combining is the same as drawing `my` then `mx`. Proven at the distribution
level by `tsum` rearrangement; the underlying monads need not be commutative as terms. -/
lemma evalDist_probComp_bind_comm {α₁ α₂ β : Type}
    (mx : ProbComp α₁) (my : ProbComp α₂) (F : α₁ → α₂ → ProbComp β) :
    𝒟[mx >>= fun a => my >>= fun b => F a b] =
      𝒟[my >>= fun b => mx >>= fun a => F a b] := by
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  have hL : ∀ a, Pr[= a | mx] * Pr[= y | my >>= fun b => F a b] =
      ∑' b, Pr[= a | mx] * (Pr[= b | my] * Pr[= y | F a b]) := fun a => by
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]
  have hR : ∀ b, Pr[= b | my] * Pr[= y | mx >>= fun a => F a b] =
      ∑' a, Pr[= b | my] * (Pr[= a | mx] * Pr[= y | F a b]) := fun b => by
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]
  rw [tsum_congr hL, tsum_congr hR, ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

omit [DecidableEq Digest] in
/-- Computation-valued form of `evalDist_idealCacheStep_bind_uniformTable`: the continuation `Mψ`
returns a probabilistic computation rather than a pure value. -/
lemma evalDist_idealCacheStep_bind_uniformTable_comp {D : Type} [DecidableEq D] [Finite D]
    [Finite Digest] [SampleableType (D → Digest)]
    {β : Type} (c : (D →ₒ Digest).QueryCache) (d : D) (Mψ : (D → Digest) → ProbComp β) :
    𝒟[do let r ← idealCacheStep (Digest := Digest) c d;
          let g ← $ᵗ (D → Digest);
          Mψ (OracleComp.tableExtending r.2 g)] =
      𝒟[do let g ← $ᵗ (D → Digest); Mψ (OracleComp.tableExtending c g)] := by
  have hbase := evalDist_idealCacheStep_bind_uniformTable c d Mψ
  have hL : (idealCacheStep c d >>= fun r =>
              ($ᵗ (D → Digest)) >>= fun g => Mψ (OracleComp.tableExtending r.2 g))
      = (idealCacheStep c d >>= fun r =>
            ($ᵗ (D → Digest)) >>= fun g =>
            pure (Mψ (OracleComp.tableExtending r.2 g))) >>= id := by simp
  have hR : (($ᵗ (D → Digest)) >>= fun g => Mψ (OracleComp.tableExtending c g))
      = (($ᵗ (D → Digest)) >>= fun g =>
            pure (Mψ (OracleComp.tableExtending c g))) >>= id := by simp
  rw [hL, hR, evalDist_bind (mx := idealCacheStep c d >>= fun r =>
        ($ᵗ (D → Digest)) >>= fun g => pure (Mψ (OracleComp.tableExtending r.2 g))),
    evalDist_bind (mx := ($ᵗ (D → Digest)) >>= fun g =>
        pure (Mψ (OracleComp.tableExtending c g)))]
  exact congrArg (fun h => h >>= fun c' => 𝒟[id c']) hbase

omit [DecidableEq Digest] in
/-- Computation-valued form of `evalDist_idealCacheMapM_bind_uniformTable`. -/
lemma evalDist_idealCacheMapM_bind_uniformTable_comp {D : Type} [DecidableEq D] [Finite D]
    [Finite Digest] [SampleableType (D → Digest)]
    {β : Type} (l : List D) (c : (D →ₒ Digest).QueryCache) (Mψ : (D → Digest) → ProbComp β) :
    𝒟[do let r ← idealCacheMapM (Digest := Digest) l c;
          let g ← $ᵗ (D → Digest);
          Mψ (OracleComp.tableExtending r.2 g)] =
      𝒟[do let g ← $ᵗ (D → Digest); Mψ (OracleComp.tableExtending c g)] := by
  have hbase := evalDist_idealCacheMapM_bind_uniformTable l c Mψ
  have hL : (idealCacheMapM l c >>= fun r =>
              ($ᵗ (D → Digest)) >>= fun g => Mψ (OracleComp.tableExtending r.2 g))
      = (idealCacheMapM l c >>= fun r =>
            ($ᵗ (D → Digest)) >>= fun g =>
            pure (Mψ (OracleComp.tableExtending r.2 g))) >>= id := by simp
  have hR : (($ᵗ (D → Digest)) >>= fun g => Mψ (OracleComp.tableExtending c g))
      = (($ᵗ (D → Digest)) >>= fun g =>
            pure (Mψ (OracleComp.tableExtending c g))) >>= id := by simp
  rw [hL, hR, evalDist_bind (mx := idealCacheMapM l c >>= fun r =>
        ($ᵗ (D → Digest)) >>= fun g => pure (Mψ (OracleComp.tableExtending r.2 g))),
    evalDist_bind (mx := ($ᵗ (D → Digest)) >>= fun g =>
        pure (Mψ (OracleComp.tableExtending c g)))]
  exact congrArg (fun h => h >>= fun c' => 𝒟[id c']) hbase

/-- Distribution-level bind congruence: if two continuations agree (in distribution) on every
output in the support of the head computation, the full binds have equal distributions. -/
lemma evalDist_bind_congr_of_support {α β : Type}
    (mx : ProbComp α) (my my' : α → ProbComp β)
    (h : ∀ a ∈ support mx, 𝒟[my a] = 𝒟[my' a]) :
    𝒟[mx >>= my] = 𝒟[mx >>= my'] := by
  refine evalDist_ext fun y => ?_
  refine probOutput_bind_congr fun a ha => ?_
  rw [probOutput_def, probOutput_def, h a ha]

/-! #### Milestone 2: composed multiple-world eager-table equivalence

The composed ideal handler `multipleIdealQueryImpl` embeds the lazy random oracle. The lemma below
lifts the eager-table equivalence to the composed handler: running `multipleIdealQueryImpl` from
`(s, c)` has the same output distribution as sampling a full random-oracle table `g`, overlaying
`c`, and running the deterministic real handler `multipleTableHandler (tableExtending c g)`.

The proof is `OracleComp.inductionOn` on the adversary, generalized over the state. The tag-query
case is discharged by the single-cell absorption `evalDist_idealCacheStep_bind_uniformTable`; the
reader-query case by the list absorption `evalDist_idealCacheMapM_bind_uniformTable`. -/

omit [Nonempty TagId] in
/-- **Step A, multiple world (Milestone 2).** Running the composed multiple-session ideal handler
from state `(s, c)` has the same output distribution as sampling a full random-oracle table `g`,
overlaying the cache `c`, and running the deterministic real multiple-session table handler. -/
lemma evalDist_simulateQ_multipleIdealQueryImpl_run'_eq_tableExtending
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    𝒟[(simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag)) oa).run' (s, c)] =
      𝒟[do let g ← $ᵗ (TagId × Nonce → Digest);
            (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c g)) oa).run' s] := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [multipleIdeal_run'_query_bind']
    have hrhs : 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
          (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c g))
            (liftM (OracleSpec.query t) >>= f)).run' s]
        = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
            (multipleTableHandler (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c g) t s) >>= fun p =>
              (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g)) (f p.1)).run' p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [multipleTable_run'_query_bind']
    rw [hrhs]
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · -- tag query, slot available
        rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot]
        set adv := ({ s with sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId) with hadv
        have hlhs_reassoc :
            ((($ᵗ Nonce) >>= fun nonce => idealCacheStep c (tag, nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), adv, r.2)) >>= fun p =>
              (simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
                (f p.1)).run' p.2)
            = (($ᵗ Nonce) >>= fun nonce => idealCacheStep c (tag, nonce) >>= fun r =>
                (simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv, r.2)) := by
          rw [bind_assoc]; refine bind_congr fun nonce => ?_
          rw [bind_assoc]; refine bind_congr fun r => ?_
          rw [pure_bind]
        refine (congrArg evalDist hlhs_reassoc).trans ?_
        -- per-nonce eager equivalence under the inner idealCacheStep
        have hlhs_inner : ∀ (n : Nonce),
            𝒟[idealCacheStep c (tag, n) >>= fun r =>
              (simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
                (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv, r.2)]
            = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                  (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c g))
                    (f (some (⟨n, OracleComp.tableExtending c g (tag, n)⟩ :
                      TagTranscript Nonce Digest)))).run' adv] := by
          intro n
          set Mψ : (TagId × Nonce → Digest) → ProbComp Bool := fun g' =>
            (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag) g')
              (f (some (⟨n, g' (tag, n)⟩ : TagTranscript Nonce Digest)))).run' adv with hMψ
          refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp c (tag, n) Mψ)
          refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
          rw [ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) adv r.2]
          refine congrArg _ (congrArg _ (funext fun g => ?_))
          have hcell : OracleComp.tableExtending r.2 g (tag, n) = r.1 := by
            simp only [OracleComp.tableExtending,
              idealCacheStep_cache_self c (tag, n) r hr, Option.getD_some]
          rw [hMψ]
          simp only [hcell]
        simp only [multipleTableHandler_tag_run_of_lt _ tag s hslot]
        -- LHS: $ᵗ Nonce >>= fun n => (...)
        -- RHS: $ᵗ g >>= fun g => $ᵗ Nonce >>= fun n => (...) — swap the two samples
        have hrhs_swap :
            (($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
              (($ᵗ Nonce) >>= fun nonce =>
                pure (some (⟨nonce, OracleComp.tableExtending c g (tag, nonce)⟩ :
                  TagTranscript Nonce Digest), adv)) >>= fun p =>
                (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g)) (f p.1)).run' p.2)
            = (($ᵗ (TagId × Nonce → Digest)) >>= fun g => ($ᵗ Nonce) >>= fun n =>
                (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g))
                  (f (some (⟨n, OracleComp.tableExtending c g (tag, n)⟩ :
                    TagTranscript Nonce Digest)))).run' adv) := by
          refine bind_congr fun g => ?_
          rw [bind_assoc]; refine bind_congr fun n => ?_
          rw [pure_bind]
        refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
        rw [evalDist_probComp_bind_comm ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce)]
        refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        exact hlhs_inner n
      · -- tag query, slot exhausted
        rw [multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot]
        change 𝒟[(simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
          (f none)).run' (s, c)] = _
        rw [ih none s c]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [multipleTableHandler_tag_run_of_not_lt _ tag s hslot]
        rfl
    | inr transcript =>
      rw [multipleIdealQueryImpl_reader_run transcript s c]
      set cells := (Finset.univ : Finset TagId).toList.map
        (fun tag => (tag, transcript.nonce)) with hcells
      -- collapse the LHS bind to a single idealCacheMapM bind
      have hlhs_reassoc :
          ((idealCacheMapM cells c >>= fun rs =>
              pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2))
            >>= fun p => (simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
              (f p.1)).run' p.2)
          = (idealCacheMapM cells c >>= fun rs =>
              (simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run'
                (s, rs.2)) := by
        rw [bind_assoc]; refine bind_congr fun rs => ?_
        rw [pure_bind]
      refine (congrArg evalDist hlhs_reassoc).trans ?_
      -- eager equivalence under idealCacheMapM
      set Mψ : (TagId × Nonce → Digest) → ProbComp Bool := fun g' =>
        (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag) g')
          (f (ReaderReply.ofBool (decide (∃ d ∈ cells.map g', d = transcript.auth))))).run' s
        with hMψ
      have hstep1 :
          𝒟[idealCacheMapM cells c >>= fun rs =>
              (simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run'
                (s, rs.2)]
          = 𝒟[idealCacheMapM cells c >>= fun rs =>
              ($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                Mψ (OracleComp.tableExtending rs.2 g)] := by
        refine evalDist_bind_congr_of_support _ _ _ fun rs hrs => ?_
        rw [ih (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))) s rs.2]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hMψ]
        simp only [idealCacheMapM_support cells c rs hrs g]
      rw [hstep1, evalDist_idealCacheMapM_bind_uniformTable_comp cells c Mψ]
      -- RHS: collapse the table-handler reader query
      refine (evalDist_bind_congr_of_support _ _ _ fun g _ => ?_).symm
      rw [multipleTableHandler_reader_run _ transcript s]
      change 𝒟[(simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c g))
          (f (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
            (fun tag nonce => OracleComp.tableExtending c g (tag, nonce))
            (multiplePattern sessionsPerTag) transcript)))).run' s] = _
      rw [hMψ]
      have hAccept : decide (∃ d ∈ cells.map (OracleComp.tableExtending c g),
            d = transcript.auth)
          = unlinkReaderAccepts (Slot := TagId)
            (fun tag nonce => OracleComp.tableExtending c g (tag, nonce))
            (multiplePattern sessionsPerTag) transcript := by
        unfold unlinkReaderAccepts tagAccepts
        rw [hcells]
        simp only [List.map_map, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
          multiplePattern, decide_eq_decide, decide_eq_true_eq, Function.comp]
        constructor
        · rintro ⟨d, ⟨a, rfl⟩, hd⟩
          exact ⟨a, ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne sessionsPerTag)⟩, hd⟩⟩
        · rintro ⟨tag, _, hd⟩
          exact ⟨_, ⟨tag, rfl⟩, hd⟩
      beta_reduce
      rw [hAccept]

/-! #### Milestone 3: composed single-world eager-table equivalence

The single-world analogues of the multiple-world `EagerComposed` helpers: a deterministic real
single-session table handler `singleTableHandler` keyed on a table over
`(TagId × Fin sessionsPerTag) × Nonce`, its `query_bind` / per-query reductions, and the composed
eager-table equivalence for `singleIdealQueryImpl`. -/

/-- Deterministic real single-session handler keyed directly on a random-oracle table
`g : (TagId × Fin sessionsPerTag) × Nonce → Digest`. -/
noncomputable def singleTableHandler (g : (TagId × Fin sessionsPerTag) × Nonce → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId) ProbComp) :=
  unlinkTagQueryImpl (Slot := TagId × Fin sessionsPerTag) (fun slot nonce => g (slot, nonce))
    (singlePattern sessionsPerTag) +
  unlinkReaderQueryImpl (Slot := TagId × Fin sessionsPerTag) (fun slot nonce => g (slot, nonce))
    (singlePattern sessionsPerTag)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ singleIdealQueryImpl` of a `query_bind`, run from a state and projected to its
output: general-codomain version of `singleIdeal_run'_query_bind`. -/
lemma singleIdeal_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
        (liftM (OracleSpec.query t) >>= f)).run' sS =
      (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag) t sS) >>= fun p =>
        (simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
          (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]; rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `simulateQ singleTableHandler` of a `query_bind`, run from a state and projected to its
output. -/
lemma singleTable_run'_query_bind' {α : Type}
    (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId) :
    (simulateQ (singleTableHandler g) (liftM (OracleSpec.query t) >>= f)).run' s =
      (singleTableHandler g t s) >>= fun p =>
        (simulateQ (singleTableHandler g) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]; rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `singleTableHandler` on a tag query with the slot budget exhausted: returns `none`. -/
lemma singleTableHandler_tag_run_of_not_lt
    (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (singleTableHandler g (Sum.inl tag) s) = pure (none, s) := by
  unfold singleTableHandler
  rw [QueryImpl.add_apply_inl]
  change (unlinkTagQueryImpl (fun slot nonce => g (slot, nonce))
    (singlePattern sessionsPerTag) tag).run s = _
  unfold unlinkTagQueryImpl
  simp [StateT.run_bind, StateT.run_get, hslot]

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `singleTableHandler` on a tag query with a free slot: sample a nonce, look up the table at
`((tag, sid), nonce)`, advance the session counter. -/
lemma singleTableHandler_tag_run_of_lt
    (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (singleTableHandler g (Sum.inl tag) s) =
      ($ᵗ Nonce) >>= fun nonce =>
        pure (some (⟨nonce, g ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce)⟩ :
            TagTranscript Nonce Digest),
          { s with sessionsUsed :=
            Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }) := by
  unfold singleTableHandler
  rw [QueryImpl.add_apply_inl]
  change (unlinkTagQueryImpl (fun slot nonce => g (slot, nonce))
    (singlePattern sessionsPerTag) tag).run s = _
  unfold unlinkTagQueryImpl
  simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    hslot, singlePattern, bind_pure_comp]

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `singleTableHandler` on a reader query: deterministic acceptance against the table. -/
lemma singleTableHandler_reader_run
    (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    (singleTableHandler g (Sum.inr transcript) s) =
      pure (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
        (fun slot nonce => g (slot, nonce))
        (singlePattern sessionsPerTag) transcript), s) := by
  unfold singleTableHandler unlinkReaderQueryImpl
  rw [QueryImpl.add_apply_inr]; rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- **Step A, single world (Milestone 3).** Running the composed single-session ideal handler
from state `(s, c)` has the same output distribution as sampling a full random-oracle table `g`,
overlaying the cache `c`, and running the deterministic real single-session table handler. -/
lemma evalDist_simulateQ_singleIdealQueryImpl_run'_eq_tableExtending
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    𝒟[(simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag)) oa).run' (s, c)] =
      𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (simulateQ (singleTableHandler (OracleComp.tableExtending c g)) oa).run' s] := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [singleIdeal_run'_query_bind']
    have hrhs : 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
          (simulateQ (singleTableHandler (OracleComp.tableExtending c g))
            (liftM (OracleSpec.query t) >>= f)).run' s]
        = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (singleTableHandler (OracleComp.tableExtending c g) t s) >>= fun p =>
              (simulateQ (singleTableHandler (OracleComp.tableExtending c g))
                (f p.1)).run' p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [singleTable_run'_query_bind']
    rw [hrhs]
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · rw [singleIdealQueryImpl_tag_run_of_lt tag s c hslot]
        set adv := ({ s with sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId) with hadv
        set sid := (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) with hsid
        have hlhs_reassoc :
            ((($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), adv, r.2)) >>= fun p =>
              (simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
                (f p.1)).run' p.2)
            = (($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                (simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv, r.2)) := by
          rw [bind_assoc]; refine bind_congr fun nonce => ?_
          rw [bind_assoc]; refine bind_congr fun r => ?_
          rw [pure_bind]
        refine (congrArg evalDist hlhs_reassoc).trans ?_
        have hlhs_inner : ∀ (n : Nonce),
            𝒟[idealCacheStep c ((tag, sid), n) >>= fun r =>
              (simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
                (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv, r.2)]
            = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                  (simulateQ (singleTableHandler (OracleComp.tableExtending c g))
                    (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                      TagTranscript Nonce Digest)))).run' adv] := by
          intro n
          set Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun g' =>
            (simulateQ (singleTableHandler g')
              (f (some (⟨n, g' ((tag, sid), n)⟩ : TagTranscript Nonce Digest)))).run' adv with hMψ
          refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp c ((tag, sid), n) Mψ)
          refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
          rw [ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) adv r.2]
          refine congrArg _ (congrArg _ (funext fun g => ?_))
          have hcell : OracleComp.tableExtending r.2 g ((tag, sid), n) = r.1 := by
            simp only [OracleComp.tableExtending,
              idealCacheStep_cache_self c ((tag, sid), n) r hr, Option.getD_some]
          rw [hMψ]
          simp only [hcell]
        simp only [singleTableHandler_tag_run_of_lt _ tag s hslot]
        have hrhs_swap :
            (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
              (($ᵗ Nonce) >>= fun nonce =>
                pure (some (⟨nonce, OracleComp.tableExtending c g ((tag, sid), nonce)⟩ :
                  TagTranscript Nonce Digest), adv)) >>= fun p =>
                (simulateQ (singleTableHandler (OracleComp.tableExtending c g))
                  (f p.1)).run' p.2)
            = (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                ($ᵗ Nonce) >>= fun n =>
                (simulateQ (singleTableHandler (OracleComp.tableExtending c g))
                  (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                    TagTranscript Nonce Digest)))).run' adv) := by
          refine bind_congr fun g => ?_
          rw [bind_assoc]; refine bind_congr fun n => ?_
          rw [pure_bind]
        refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
        rw [evalDist_probComp_bind_comm ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
          ($ᵗ Nonce)]
        refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        exact hlhs_inner n
      · rw [singleIdealQueryImpl_tag_run_of_not_lt tag s c hslot]
        change 𝒟[(simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
          (f none)).run' (s, c)] = _
        rw [ih none s c]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [singleTableHandler_tag_run_of_not_lt _ tag s hslot]
        rfl
    | inr transcript =>
      rw [singleIdealQueryImpl_reader_run transcript s c]
      set cells := (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
        (fun slot => (slot, transcript.nonce)) with hcells
      have hlhs_reassoc :
          ((idealCacheMapM cells c >>= fun rs =>
              pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2))
            >>= fun p => (simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
              (f p.1)).run' p.2)
          = (idealCacheMapM cells c >>= fun rs =>
              (simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run'
                (s, rs.2)) := by
        rw [bind_assoc]; refine bind_congr fun rs => ?_
        rw [pure_bind]
      refine (congrArg evalDist hlhs_reassoc).trans ?_
      set Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun g' =>
        (simulateQ (singleTableHandler g')
          (f (ReaderReply.ofBool (decide (∃ d ∈ cells.map g', d = transcript.auth))))).run' s
        with hMψ
      have hstep1 :
          𝒟[idealCacheMapM cells c >>= fun rs =>
              (simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run'
                (s, rs.2)]
          = 𝒟[idealCacheMapM cells c >>= fun rs =>
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                Mψ (OracleComp.tableExtending rs.2 g)] := by
        refine evalDist_bind_congr_of_support _ _ _ fun rs hrs => ?_
        rw [ih (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))) s rs.2]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hMψ]
        simp only [idealCacheMapM_support cells c rs hrs g]
      rw [hstep1, evalDist_idealCacheMapM_bind_uniformTable_comp cells c Mψ]
      refine (evalDist_bind_congr_of_support _ _ _ fun g _ => ?_).symm
      rw [singleTableHandler_reader_run _ transcript s]
      change 𝒟[(simulateQ (singleTableHandler (OracleComp.tableExtending c g))
          (f (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
            (fun slot nonce => OracleComp.tableExtending c g (slot, nonce))
            (singlePattern sessionsPerTag) transcript)))).run' s] = _
      rw [hMψ]
      have hAccept : decide (∃ d ∈ cells.map (OracleComp.tableExtending c g),
            d = transcript.auth)
          = unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
            (fun slot nonce => OracleComp.tableExtending c g (slot, nonce))
            (singlePattern sessionsPerTag) transcript := by
        unfold unlinkReaderAccepts tagAccepts
        rw [hcells]
        simp only [List.map_map, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
          singlePattern, decide_eq_decide, decide_eq_true_eq, Function.comp]
        constructor
        · rintro ⟨d, ⟨slot, rfl⟩, hd⟩
          exact ⟨slot.1, ⟨slot.2, hd⟩⟩
        · rintro ⟨tag, sid, hd⟩
          exact ⟨_, ⟨(tag, sid), rfl⟩, hd⟩
      beta_reduce
      rw [hAccept]

/-! #### Milestone 4 prep: eager-form success probabilities

With both ideal worlds shown equal in distribution to deterministic table-handler runs
(Milestones 2 and 3), the two ideal-world success probabilities are exposed as
table-sampled deterministic runs from the empty cache (`tableExtending ∅ g = g`). These are the
precise eager forms on which the coupled-table union bound operates. -/

omit [Nonempty TagId] in
/-- Eager form of the multiple-session ideal success probability: sample a full random-oracle
table `g`, then run the deterministic real multiple-session table handler. -/
lemma probOutput_multipleIdeal_run'_eq_tableSample [Fintype Nonce] [Finite Digest]
    (adv : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag)) adv).run'
        (UnlinkState.init, ∅)] =
      Pr[= true | ($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
        (simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag) g) adv).run'
          UnlinkState.init] := by
  rw [probOutput_def, probOutput_def,
    evalDist_simulateQ_multipleIdealQueryImpl_run'_eq_tableExtending adv UnlinkState.init ∅]
  simp only [OracleComp.tableExtending_empty]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Eager form of the single-session ideal success probability: sample a full random-oracle
table `g`, then run the deterministic real single-session table handler. -/
lemma probOutput_singleIdeal_run'_eq_tableSample [Fintype Nonce] [Finite Digest]
    (adv : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | (simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag)) adv).run'
        (UnlinkState.init, ∅)] =
      Pr[= true | ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
        (simulateQ (singleTableHandler g) adv).run' UnlinkState.init] := by
  rw [probOutput_def, probOutput_def,
    evalDist_simulateQ_singleIdealQueryImpl_run'_eq_tableExtending adv UnlinkState.init ∅]
  simp only [OracleComp.tableExtending_empty]

/-- The reference-slot projection of a single-session random-oracle table onto a multiple-session
one: read the single-session table at the fixed reference session slot `0`. It is the table-level
coupling map underlying the eager-route comparison of the two ideal worlds. -/
def projectTable
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) : TagId × Nonce → Digest :=
  fun p => gS ((p.1, (0 : Fin sessionsPerTag)), p.2)

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] in
/-- **M4a — projecting a uniform single-session table is a uniform multiple-session table.**

Drawing a uniform single-session random-oracle table `gS` and projecting it onto the reference
session slot (`projectTable`) yields the uniform distribution on multiple-session tables. This is
the marginalization step of the coupled-table union bound: the reference-slot cells of `gS` are
themselves jointly uniform and independent of the off-slot cells. -/
lemma evalDist_projectTable_uniformSample
    [Fintype Nonce] [Finite Digest] [Nonempty Digest] :
    𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
        fun gS => pure (projectTable (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) gS)] =
      𝒟[$ᵗ (TagId × Nonce → Digest)] := by
  have he : Function.Injective
      (fun p : TagId × Nonce => ((p.1, (0 : Fin sessionsPerTag)), p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.1 h.2
  exact evalDist_uniformSample_map_comp_injective (R := Digest) he


end EagerComposed

end UnlinkReduction

end PRFTagReader
