/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.Bodies

/-!
# Ghost-layer machinery for Fiat-Shamir with aborts: GhostLayer

The ghost-layer presentation of the reprogramming bodies (`ghostSignBody`
over a two-layer cache) and the ghost-instrumented hybrid handlers
(`ghostHybridImpl` with its monotone bad flag, the ghost-blind handler, and the
run-level hybrid handlers).

Part of the hybrid signing-body development for the CMA-to-NMA reduction;
`VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.Bodies` opens the
chain and holds the overview docstring.
-/

public section

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)
variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))

/-! ## Ghost-layer presentation of the reprogramming bodies

The Prog → Trans hop (`probOutput_hybridExpAtKey_prog_le_trans`) compares two signing
bodies whose caches genuinely differ throughout the run: `progSignBody` programs every
attempt, while `transSignBody` programs only the accepted transcript. The bridge is a
two-layer presentation of the cache: a *real* layer holding the entries both games agree
on, and a *ghost* layer holding the rejected-attempt programmings that only
`progSignBody` performs. `ghostSignBody` acts on the layered state, writing the accepted
transcript to the real layer and each rejected attempt to the ghost layer.

Two projection lemmas make the deferred-sampling step of the hop precise:

* overlaying the ghost layer onto the real layer recovers `progSignBody`
  (`run_ghostSignBody_overlay`), and
* forgetting the ghost layer recovers the accepted-only programming loop of
  `transSignBody` (`run_ghostSignBody_fst`) — a programmed point that is never
  subsequently read is distributionally removable. -/

/-- Overlay a ghost cache onto a real cache; ghost entries shadow real ones. -/
@[expose] def overlayCache (re gh : (M × Commit →ₒ Chal).QueryCache) :
    (M × Commit →ₒ Chal).QueryCache :=
  fun q => (gh q).or (re q)

/-- Remove a single point from a query cache. -/
@[expose] def uncacheQuery (cache : (M × Commit →ₒ Chal).QueryCache) (q : M × Commit) :
    (M × Commit →ₒ Chal).QueryCache :=
  fun q' => if q' = q then none else cache q'

omit [SampleableType Chal] in
lemma overlayCache_cacheQuery_uncacheQuery
    (re gh : (M × Commit →ₒ Chal).QueryCache) (q : M × Commit) (c : Chal) :
    overlayCache M (re.cacheQuery q c) (uncacheQuery M gh q) =
      (overlayCache M re gh).cacheQuery q c := by
  funext q'
  by_cases hq : q' = q
  · subst hq
    simp [overlayCache, uncacheQuery]
  · simp [overlayCache, uncacheQuery, hq]

omit [SampleableType Chal] in
/-- Removing a point from a cache does not increase its live-entry count: the support set
of `uncacheQuery cache q` is a subset of that of `cache`. -/
lemma toSet_uncacheQuery_subset (cache : (M × Commit →ₒ Chal).QueryCache) (q : M × Commit) :
    (uncacheQuery M cache q).toSet ⊆ cache.toSet := by
  rintro ⟨t', u'⟩ hmem
  rw [QueryCache.mem_toSet] at hmem ⊢
  by_cases ht : t' = q
  · subst ht; simp only [uncacheQuery, if_true] at hmem; exact absurd hmem (by simp)
  · rwa [uncacheQuery, if_neg ht] at hmem

omit [SampleableType Chal] in
/-- `uncacheQuery` does not increase the `enncard` resource. -/
lemma enncard_uncacheQuery_le (cache : (M × Commit →ₒ Chal).QueryCache) (q : M × Commit) :
    QueryCache.enncard (uncacheQuery M cache q) ≤ QueryCache.enncard cache :=
  ENat.toENNReal_mono (Set.encard_le_encard (toSet_uncacheQuery_subset M cache q))

omit [SampleableType Chal] in
lemma overlayCache_cacheQuery_ghost
    (re gh : (M × Commit →ₒ Chal).QueryCache) (q : M × Commit) (c : Chal) :
    overlayCache M re (gh.cacheQuery q c) = (overlayCache M re gh).cacheQuery q c := by
  funext q'
  by_cases hq : q' = q
  · subst hq
    simp [overlayCache]
  · simp [overlayCache, hq]

omit [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma overlayCache_apply_ghost_some
    {gh : (M × Commit →ₒ Chal).QueryCache} {q : M × Commit} {v : Chal}
    (re : (M × Commit →ₒ Chal).QueryCache) (h : gh q = some v) :
    overlayCache M re gh q = some v := by
  simp [overlayCache, h]

omit [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma overlayCache_apply_ghost_none
    {gh : (M × Commit →ₒ Chal).QueryCache} {q : M × Commit}
    (re : (M × Commit →ₒ Chal).QueryCache) (h : gh q = none) :
    overlayCache M re gh q = re q := by
  simp [overlayCache, h]

omit [SampleableType Chal] in
lemma overlayCache_cacheQuery_real_of_ghost_none
    (re : (M × Commit →ₒ Chal).QueryCache) {gh : (M × Commit →ₒ Chal).QueryCache}
    {q : M × Commit} (h : gh q = none) (c : Chal) :
    overlayCache M (re.cacheQuery q c) gh = (overlayCache M re gh).cacheQuery q c := by
  funext q'
  by_cases hq : q' = q
  · subst hq
    simp [overlayCache, h]
  · simp [overlayCache, hq]

/-- Signing body on the layered cache: run the abort loop privately, recording each
rejected attempt's would-be programming in the ghost layer and programming the accepted
transcript into the real layer (clearing any stale ghost entry at that point). -/
@[expose] noncomputable def ghostSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    ℕ → StateT ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache)
      ProbComp (Option (Commit × Resp))
  | 0 => pure none
  | n + 1 => do
    let (w, st) ← liftM (ids.commit pk sk)
    let c ← (liftM (uniformSample Chal) :
      StateT ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache)
        ProbComp Chal)
    let oz ← liftM (ids.respond pk sk st c)
    match oz with
    | some z =>
        modify fun s => (s.1.cacheQuery (msg, w) c, uncacheQuery M s.2 (msg, w))
        pure (some (w, z))
    | none =>
        modify fun s => (s.1, s.2.cacheQuery (msg, w) c)
        ghostSignBody pk sk msg n

omit [SampleableType Stmt] in
/-- Overlay projection: `ghostSignBody` with the ghost layer overlaid onto the real
layer is exactly `progSignBody` on the overlaid cache. Rejected-attempt programmings
(ghost writes) and accepted programmings (real writes) both surface as ordinary cache
programmings under the overlay. -/
lemma run_ghostSignBody_overlay (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache),
      (fun zs : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
          (zs.1, overlayCache M zs.2.1 zs.2.2)) <$>
        (ghostSignBody ids M pk sk msg n).run (re, gh) =
      (progSignBody ids M pk sk msg n).run (overlayCache M re gh)
  | 0, re, gh => by
    simp [ghostSignBody, progSignBody]
  | (n + 1), re, gh => by
    simp only [ghostSignBody, progSignBody, progSignAttempt, bind_assoc, StateT.run_bind,
      OracleComp.liftM_run_StateT, map_bind, pure_bind, StateT.run_modify]
    refine congrArg (ids.commit pk sk >>= ·) (funext fun wst => ?_)
    obtain ⟨w, st⟩ := wst
    refine congrArg (uniformSample Chal >>= ·) (funext fun c => ?_)
    refine congrArg (ids.respond pk sk st c >>= ·) (funext fun oz => ?_)
    cases oz with
    | some z =>
        simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
          map_pure, overlayCache_cacheQuery_uncacheQuery]
    | none =>
        simp only [StateT.run_bind, StateT.run_modify, pure_bind,
          run_ghostSignBody_overlay pk sk msg n re (gh.cacheQuery (msg, w) c),
          overlayCache_cacheQuery_ghost]

omit [SampleableType Stmt] in
/-- Ghost-forgetting projection (deferred sampling): dropping the ghost layer from
`ghostSignBody` yields the accepted-only programming loop of `transSignBody`. The
programming of a rejected attempt lives only in the ghost layer, so removing it does not
change the joint distribution of the signing output and the real cache. -/
lemma run_ghostSignBody_fst (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache),
      (fun zs : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) => (zs.1, zs.2.1)) <$>
        (ghostSignBody ids M pk sk msg n).run (re, gh) =
      (liftM (firstSome (ids.honestExecution pk sk) n) >>= signProgramCont M msg).run re
  | 0, re, gh => by
    simp [ghostSignBody, firstSome, signProgramCont]
  | (n + 1), re, gh => by
    simp only [ghostSignBody, firstSome_succ, IdenSchemeWithAbort.honestExecution,
      bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT, map_bind, pure_bind]
    refine congrArg (ids.commit pk sk >>= ·) (funext fun wst => ?_)
    obtain ⟨w, st⟩ := wst
    refine congrArg (uniformSample Chal >>= ·) (funext fun c => ?_)
    refine congrArg (ids.respond pk sk st c >>= ·) (funext fun oz => ?_)
    cases oz with
    | some z =>
        simp only [Option.map_some, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, map_pure, signProgramCont]
    | none =>
        simp only [Option.map_none, StateT.run_bind, StateT.run_modify, pure_bind]
        rw [run_ghostSignBody_fst pk sk msg n re (gh.cacheQuery (msg, w) c)]
        simp only [IdenSchemeWithAbort.honestExecution, StateT.run_bind,
          OracleComp.liftM_run_StateT, bind_assoc, pure_bind]

omit [SampleableType Stmt] in
/-- `run_ghostSignBody_fst` at the attempt budget of the scheme: forgetting the ghost
layer of `ghostSignBody` recovers `transSignBody` on the real layer. -/
lemma run_ghostSignBody_fst_eq_transSignBody (pk : Stmt) (sk : Wit) (msg : M)
    (re gh : (M × Commit →ₒ Chal).QueryCache) :
    (fun zs : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) => (zs.1, zs.2.1)) <$>
        (ghostSignBody ids M pk sk msg maxAttempts).run (re, gh) =
      (transSignBody ids M maxAttempts pk sk msg).run re :=
  run_ghostSignBody_fst ids M pk sk msg maxAttempts re gh

omit [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma overlayCache_empty (re : (M × Commit →ₒ Chal).QueryCache) :
    overlayCache M re ∅ = re := by
  funext q
  simp [overlayCache]

/-! ## Ghost-instrumented hybrid handlers

Run-level counterpart of the ghost-layer presentation: handlers for the adversary's
oracles over the layered cache, a signed-message list, and a monotone bad flag that
fires exactly when the adversary's random-oracle query hits a point of the ghost layer.
The Prog-side handler (`ghostHybridImpl … true`) answers such a query from the ghost
layer (matching `progSignBody`'s overlaid cache), while the Trans-side handler
(`ghostHybridImpl … false`) answers it from the real layer (matching `transSignBody`'s
cache). On every other query the two handlers are literally identical, which is the
identical-until-bad shape of `tvDist_simulateQ_run_le_probEvent_output_bad`. -/

/-- One caching random-oracle step on a bare cache, as a `ProbComp`. Agrees with
`(randomOracle mc).run re` (see `randomOracle_run_eq_roStep`). -/
@[expose] noncomputable def roStep (re : (M × Commit →ₒ Chal).QueryCache) (mc : M × Commit) :
    ProbComp (Chal × (M × Commit →ₒ Chal).QueryCache) :=
  match re mc with
  | some v => pure (v, re)
  | none => do
    let c ← uniformSample Chal
    pure (c, re.cacheQuery mc c)

omit [SampleableType Stmt] in
lemma randomOracle_run_eq_roStep (re : (M × Commit →ₒ Chal).QueryCache) (mc : M × Commit) :
    ((randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) mc).run re =
      roStep M re mc := by
  rw [randomOracle.apply_eq]
  cases hre : re mc with
  | some v => simp [roStep, hre]
  | none => simp [roStep, hre, StateT.run_bind]

/-- The state of the ghost-instrumented hybrid run: layered cache, signed-message list,
and the bad flag for adversarial reads of the ghost layer. -/
abbrev GhostState (M Commit Chal : Type) : Type :=
  (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) × Bool

/-- Instrumented handler for the adversary's oracles over the layered cache.
`progSide` selects the answer at a ghost hit: the ghost value (Prog side) or a fresh
caching read of the real layer (Trans side). The bad flag fires on ghost hits and is
otherwise preserved; signing queries run `ghostSignBody` on the cache layers. -/
@[expose] noncomputable def ghostHybridImpl (progSide : Bool) (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (GhostState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      match s.1.1.2 mc with
      | some v =>
          if progSide then pure (v, (s.1, true))
          else (fun cu => (cu.1, (((cu.2, s.1.1.2), s.1.2), true))) <$> roStep M s.1.1.1 mc
      | none =>
          (fun cu => (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2))) <$> roStep M s.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1, ((alc.2, msg :: s.1.2), s.2))) <$>
        (ghostSignBody ids M pk sk msg maxAttempts).run s.1.1

omit [SampleableType Stmt] in
/-- The two ghost-instrumented handlers agree on all transitions that leave the bad flag
unset: they differ only in the answer at a ghost hit, which fires the flag on both
sides. -/
lemma ghostHybridImpl_agree_good (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M)
    (u : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t)
    (s' : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) :
    Pr[= (u, (s', false)) |
        (ghostHybridImpl ids M maxAttempts true pk sk t).run (s, false)] =
      Pr[= (u, (s', false)) |
        (ghostHybridImpl ids M maxAttempts false pk sk t).run (s, false)] := by
  rcases t with (n | mc) | msg
  · rfl
  · simp only [ghostHybridImpl, StateT.run_mk]
    cases hgh : s.1.2 mc with
    | some v =>
        simp only [↓reduceIte]
        rw [probOutput_eq_zero_of_not_mem_support (by
            intro h
            rw [support_pure] at h
            simpa using congrArg (fun z : _ × GhostState M Commit Chal => z.2.2) h),
          probOutput_eq_zero_of_not_mem_support (by
            intro h
            rw [if_neg Bool.false_ne_true, support_map] at h
            obtain ⟨cu, -, hcu⟩ := h
            simpa using congrArg (fun z : _ × GhostState M Commit Chal => z.2.2) hcu)]
    | none => rfl
  · rfl

omit [SampleableType Stmt] in
/-- The ghost-instrumented handlers never unset the bad flag. -/
lemma ghostHybridImpl_bad_mono (progSide : Bool) (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (p : GhostState M Commit Chal) (hp : p.2 = true) :
    ∀ z ∈ support ((ghostHybridImpl ids M maxAttempts progSide pk sk t).run p),
      z.2.2 = true := by
  intro z hz
  rcases t with (n | mc) | msg
  · simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hp
  · simp only [ghostHybridImpl, StateT.run_mk] at hz
    rcases hgh : p.1.1.2 mc with _ | v
    · simp only [hgh, support_map] at hz
      obtain ⟨_, _, rfl⟩ := hz
      exact hp
    · simp only [hgh] at hz
      cases progSide with
      | true =>
          simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          rfl
      | false =>
          rw [if_neg Bool.false_ne_true, support_map] at hz
          obtain ⟨_, _, rfl⟩ := hz
          rfl
  · simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hp

/-! ### Ghost-blind handler

The ghost-blind handler `ghostBlindImpl` is the eager hybrid handler `ghostHybridImpl … true`
with one change at the adversarial random-oracle read step: on a ghost-cache *hit* it still
*records* the would-hit by flipping the bad flag, but it *answers* the read from the real
cache via `roStep` — exactly as it does on a *miss* — instead of returning the ghost value.
So the ghost-key values are pure side-data: they are consulted only to set the bad flag and
never influence the run's behaviour. Structurally this is the Trans-side instrumented handler
`ghostHybridImpl … false`, whose hit branch already answers from the real layer while flipping
the flag; `ghostBlindImpl` is a named alias for that handler, isolating its ghost-blind role
in the read-bound spine from the Prog→Trans hop usage of the Trans handler. -/

/-- Ghost-blind hybrid handler: identical to `ghostHybridImpl … true` except that an
adversarial random-oracle read at a ghost-cache hit answers from the real layer (`roStep`,
the same as a miss) while still flipping the bad flag. The ghost value never influences the
run. Definitionally the Trans-side handler `ghostHybridImpl … false`
(`ghostBlindImpl_eq_ghostHybridImpl_false`). -/
@[expose] noncomputable def ghostBlindImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (GhostState M Commit Chal) ProbComp) :=
  ghostHybridImpl ids M maxAttempts false pk sk

omit [SampleableType Stmt] in
/-- The ghost-blind handler is, by definition, the Trans-side instrumented handler. -/
lemma ghostBlindImpl_eq_ghostHybridImpl_false (pk : Stmt) (sk : Wit) :
    ghostBlindImpl ids M maxAttempts pk sk =
      ghostHybridImpl ids M maxAttempts false pk sk := rfl

omit [SampleableType Stmt] in
/-- The eager (`ghostHybridImpl … true`) and ghost-blind handlers agree on every non-bad
output transition from a non-bad input state: they coincide on uniform, signing, and
ghost-*miss* read steps, and on a ghost-*hit* both flip the bad flag, so neither has any
non-bad output there. This is the `h_agree_good` premise of the exact identical-until-bad
machinery. -/
lemma ghostBlindImpl_agree_good (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M)
    (u : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t)
    (s' : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) :
    Pr[= (u, (s', false)) |
        (ghostHybridImpl ids M maxAttempts true pk sk t).run (s, false)] =
      Pr[= (u, (s', false)) |
        (ghostBlindImpl ids M maxAttempts pk sk t).run (s, false)] :=
  ghostHybridImpl_agree_good ids M maxAttempts pk sk t s u s'

omit [SampleableType Stmt] in
/-- The ghost-blind handler never unsets the bad flag (bad-input monotonicity). -/
lemma ghostBlindImpl_bad_mono (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (p : GhostState M Commit Chal) (hp : p.2 = true) :
    ∀ z ∈ support ((ghostBlindImpl ids M maxAttempts pk sk t).run p),
      z.2.2 = true :=
  ghostHybridImpl_bad_mono ids M maxAttempts false pk sk t p hp

/-! ## Hybrid run-level handlers -/

/-- Run a cache-level action inside the hybrid state (random-oracle cache plus the list
of signed messages), acting on the cache component. -/
@[expose] def onCache {α : Type}
    (action : StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp α) :
    StateT ((M × Commit →ₒ Chal).QueryCache × List M) ProbComp α :=
  fun s => (fun (a, c) => (a, (c, s.2))) <$> action.run s.1

/-- Handler for the adversary's base oracles in the hybrid games: uniform queries are
forwarded and random-oracle queries go through the caching random oracle on the cache
component of the hybrid state. -/
@[expose] noncomputable def hybridBaseImpl :
    QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache × List M) ProbComp) :=
  let base : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))
  fun t => onCache M (base t)

/-- Handler for the adversary's signing oracle in the hybrid games: record the signed
message (for the freshness check) and run the given signing body on the cache. -/
@[expose] noncomputable def hybridSignImpl
    (signBody : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp))) :
    QueryImpl (M →ₒ Option (Commit × Resp))
      (StateT ((M × Commit →ₒ Chal).QueryCache × List M) ProbComp) :=
  fun msg => do
    modify fun s => (s.1, msg :: s.2)
    onCache M (signBody msg)

end FiatShamirWithAbort
