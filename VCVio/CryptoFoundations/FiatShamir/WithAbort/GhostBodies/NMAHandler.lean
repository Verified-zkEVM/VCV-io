/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.BodyBounds

/-!
# Ghost-layer machinery for Fiat-Shamir with aborts: NMAHandler

The layered ghost-tagged NMA handler, programming accepted transcripts
into the ghost layer, with the live-read / sign-program collision event.

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

/-! ## Layered ghost-tagged NMA handler

The NMA bridge (`hybridSimRun_le_managedRun_verify`) couples the single-cache simulated
hybrid against the linked managed run.  The obstruction recorded there is that the single
hybrid cache does not, on its own, record whether a point entered by a *live RO read* or by
the *signing simulation's programming* (`signProgramCont`).  We resolve this exactly as in
the Prog → Trans hop: run the hybrid on an enriched, layered cache state
`((baseCache, ghostCache), signed)` that tags each entry as live-read (base) vs
signing-programmed (ghost).  The base oracles write live RO reads to `baseCache`; the
signing body's `signProgramCont` writes the accepted-transcript programming to `ghostCache`.

On that layered state the partition *is* a function of the state, so the overlay projection
`((base, ghost), signed) ↦ (overlayCache base ghost, signed)` back to the plain single-cache
hybrid is a per-step state projection in the sense of
`OracleComp.map_run_simulateQ_eq_of_query_map_eq`.  This section builds the layered handler
and proves that overlay projection (sub-lemma (a) of the bridge). -/

/-- Ghost-layer programming continuation: like `signProgramCont`, but the accepted
transcript's challenge is written to the *ghost* layer of a `(base, ghost)` cache pair.
An all-abort loop outcome produces no signature and no programming. -/
@[expose] noncomputable def ghostSignProgramCont (msg : M) :
    Option (Commit × Chal × Resp) →
      StateT ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache)
        ProbComp (Option (Commit × Resp))
  | some (w, c, z) => do
    modify fun s => (s.1, s.2.cacheQuery (msg, w) c)
    pure (some (w, z))
  | none => pure none

/-- Signing body of the simulated hybrid on the layered cache: run the simulator loop
privately, programming the accepted transcript into the *ghost* layer (`ghostSignProgramCont`).
The base layer is untouched. -/
@[expose] noncomputable def simGhostSignBody (pk : Stmt) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache)
      ProbComp (Option (Commit × Resp)) :=
  liftM (firstSome (sim pk) maxAttempts) >>= ghostSignProgramCont M msg

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Overlay projection of `ghostSignProgramCont`: overlaying the ghost layer onto the base
layer turns the ghost-layer programming into an ordinary cache programming, recovering
`signProgramCont` on the overlaid cache. -/
lemma run_ghostSignProgramCont_overlay (msg : M)
    (oz : Option (Commit × Chal × Resp))
    (re gh : (M × Commit →ₒ Chal).QueryCache) :
    (fun zs : Option (Commit × Resp) ×
        ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (zs.1, overlayCache M zs.2.1 zs.2.2)) <$>
      (ghostSignProgramCont M msg oz).run (re, gh) =
    (signProgramCont M msg oz).run (overlayCache M re gh) := by
  cases oz with
  | none => simp [ghostSignProgramCont, signProgramCont]
  | some wcz =>
      obtain ⟨w, c, z⟩ := wcz
      simp only [ghostSignProgramCont, signProgramCont, StateT.run_bind, StateT.run_modify,
        pure_bind, StateT.run_pure, map_pure, overlayCache_cacheQuery_ghost]

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Overlay projection of `simGhostSignBody`: overlaying the ghost layer onto the base layer
recovers `simSignBody` on the overlaid cache. The simulator loop is run identically; only
the destination layer of the accepted programming differs, which the overlay erases. -/
lemma run_simGhostSignBody_overlay (pk : Stmt) (sk : Wit) (msg : M)
    (re gh : (M × Commit →ₒ Chal).QueryCache) :
    (fun zs : Option (Commit × Resp) ×
        ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (zs.1, overlayCache M zs.2.1 zs.2.2)) <$>
      (simGhostSignBody M maxAttempts sim pk msg).run (re, gh) =
    (simSignBody M maxAttempts sim pk sk msg).run (overlayCache M re gh) := by
  simp only [simGhostSignBody, simSignBody, StateT.run_bind, OracleComp.liftM_run_StateT,
    bind_assoc, pure_bind, map_bind]
  refine congrArg (firstSome (sim pk) maxAttempts >>= ·) (funext fun oz => ?_)
  exact run_ghostSignProgramCont_overlay M msg oz re gh

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Ghost-domain support fact for `simGhostSignBody`: every ghost-layer entry of an output
state is either an entry already present in the input ghost layer, or sits at a point whose
message component equals the signed message `msg`.  The base layer is never touched. -/
lemma simGhostSignBody_support_ghost (pk : Stmt) (msg : M)
    (re gh : (M × Commit →ₒ Chal).QueryCache)
    (z : Option (Commit × Resp) ×
      ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache))
    (hz : z ∈ support ((simGhostSignBody M maxAttempts sim pk msg).run (re, gh)))
    (q : M × Commit) (hq : z.2.2 q ≠ none) : gh q ≠ none ∨ q.1 = msg := by
  simp only [simGhostSignBody, StateT.run_bind, OracleComp.liftM_run_StateT, bind_assoc,
    pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
  obtain ⟨oz, -, hz⟩ := hz
  cases oz with
  | none =>
      simp only [ghostSignProgramCont, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl hq
  | some wcz =>
      obtain ⟨w, c, z'⟩ := wcz
      simp only [ghostSignProgramCont, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp only at hq
      by_cases hqw : q = (msg, w)
      · exact Or.inr (by simp [hqw])
      · exact Or.inl (by rwa [QueryCache.cacheQuery_of_ne _ _ hqw] at hq)

/-- State of the layered ghost-tagged NMA run: a base/ghost cache pair together with the
signed-message list. (No bad flag is needed for the NMA bridge: the coupling is exact, not
identical-until-bad.) -/
abbrev NmaGhostState (M Commit Chal : Type) : Type :=
  ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M

/-- Embed a base random-oracle cache (keyed by `M × Commit`) into the outer runtime cache of
the linked managed run, which is keyed by the sum spec `unifSpec + (M × Commit →ₒ Chal)`. The
uniform-query slots are empty (the runtime forwards uniform queries through `unifFwdImpl`
without caching), and the random-oracle slots carry the base entries. This is the left
component of the linked-run projection `proj₂` for sub-lemma (b). -/
@[expose] def baseEmbed (base : (M × Commit →ₒ Chal).QueryCache) :
    (unifSpec + (M × Commit →ₒ Chal)).QueryCache
  | .inl _ => none
  | .inr mc => base mc

omit [SampleableType Stmt] [DecidableEq Commit] [DecidableEq M] [SampleableType Chal] in
@[simp] lemma baseEmbed_inr (base : (M × Commit →ₒ Chal).QueryCache) (mc : M × Commit) :
    baseEmbed M base (.inr mc) = base mc := rfl

omit [SampleableType Stmt] [DecidableEq Commit] [DecidableEq M] [SampleableType Chal] in
@[simp] lemma baseEmbed_inl (base : (M × Commit →ₒ Chal).QueryCache)
    (n : unifSpec.Domain) : baseEmbed M base (.inl n) = none := rfl

omit [SampleableType Stmt] [DecidableEq Commit] [DecidableEq M] [SampleableType Chal] in
/-- The embedding of the empty base cache is the empty outer cache. -/
@[simp] lemma baseEmbed_empty :
    baseEmbed M (∅ : (M × Commit →ₒ Chal).QueryCache) =
      (∅ : (unifSpec + (M × Commit →ₒ Chal)).QueryCache) := by
  funext t
  cases t with
  | inl n => rfl
  | inr mc => rfl

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Embedding commutes with caching a random-oracle point: `baseEmbed` of a base cache
extended at `mc` equals the outer cache extended at the `.inr mc` slot. -/
lemma baseEmbed_cacheQuery (base : (M × Commit →ₒ Chal).QueryCache)
    (mc : M × Commit) (v : Chal) :
    baseEmbed M (base.cacheQuery mc v) =
      (baseEmbed M base).cacheQuery (.inr mc) v := by
  funext t
  cases t with
  | inl n =>
      rw [QueryCache.cacheQuery_of_ne _ _ (show (Sum.inl n : (unifSpec +
        (M × Commit →ₒ Chal)).Domain) ≠ Sum.inr mc by simp), baseEmbed_inl, baseEmbed_inl]
  | inr mc' =>
      by_cases h : mc' = mc
      · subst h; simp [baseEmbed, QueryCache.cacheQuery_self]
      · rw [baseEmbed_inr, QueryCache.cacheQuery_of_ne _ _ h,
          QueryCache.cacheQuery_of_ne _ _ (show (Sum.inr mc' : (unifSpec +
            (M × Commit →ₒ Chal)).Domain) ≠ Sum.inr mc by simp [h]), baseEmbed_inr]

/-- Layered ghost-tagged handler for the simulated hybrid.  Base oracles (uniform and the
caching random oracle) write live RO reads to the *base* layer, reading through the overlay
so that signing-programmed (ghost) points are visible to the adversary; the signing oracle
records the signed message and runs `simGhostSignBody`, writing the accepted-transcript
programming to the *ghost* layer. -/
@[expose] noncomputable def ghostNmaImpl (pk : Stmt) (_sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (NmaGhostState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      match s.1.2 mc with
      | some v => pure (v, s)
      | none =>
          (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((cu.2, s.1.2), s.2))) <$> roStep M s.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (alc.1, (alc.2, msg :: s.2))) <$>
        (simGhostSignBody M maxAttempts sim pk msg).run s.1

omit [SampleableType Stmt] in
lemma ghostNmaImpl_run_unif (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : NmaGhostState M Commit Chal) :
    (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl

omit [SampleableType Stmt] in
lemma ghostNmaImpl_run_ro (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : NmaGhostState M Commit Chal) :
    (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inr mc))).run s =
      match s.1.2 mc with
      | some v => pure (v, s)
      | none =>
          (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((cu.2, s.1.2), s.2))) <$> roStep M s.1.1 mc := rfl

omit [SampleableType Stmt] in
lemma ghostNmaImpl_run_sign (pk : Stmt) (sk : Wit) (msg : M)
    (s : NmaGhostState M Commit Chal) :
    (ghostNmaImpl M maxAttempts sim pk sk (.inr msg)).run s =
      (fun alc : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (alc.1, (alc.2, msg :: s.2))) <$>
        (simGhostSignBody M maxAttempts sim pk msg).run s.1 := rfl

omit [SampleableType Stmt] in
/-- **Ghost-domain invariant for `ghostNmaImpl`.** Along any run of the layered NMA handler,
every ghost-layer entry's message component has been recorded in the signed list. This is the
NMA analogue of `ghostHybridImpl_preserves_signed_inv`: the base oracles never write the ghost
layer, and the signing oracle records the signed message before programming the ghost layer at
a point whose message component equals that signed message (`simGhostSignBody_support_ghost`).
This invariant is the gate for the linked-run coupling (sub-lemma (b)): it certifies that on a
random-oracle step a live read hits the base/outer layer, while the ghost layer only carries
signing-programmed points. -/
lemma ghostNmaImpl_preserves_signed_inv (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : NmaGhostState M Commit Chal)
    (hs : ∀ q : M × Commit, s.1.2 q ≠ none → q.1 ∈ s.2) :
    ∀ z ∈ support ((ghostNmaImpl M maxAttempts sim pk sk t).run s),
      ∀ q : M × Commit, z.2.1.2 q ≠ none → q.1 ∈ z.2.2 := by
  intro z hz
  rcases t with (n | mc) | msg
  · simp only [ghostNmaImpl, StateT.run_mk, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · simp only [ghostNmaImpl, StateT.run_mk] at hz
    cases hgh : s.1.2 mc with
    | some v =>
        simp only [hgh, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hs
    | none =>
        simp only [hgh, support_map] at hz
        obtain ⟨cu, -, rfl⟩ := hz
        exact hs
  · simp only [ghostNmaImpl, StateT.run_mk, support_map] at hz
    obtain ⟨alc, halc, rfl⟩ := hz
    intro q hq
    rcases simGhostSignBody_support_ghost M maxAttempts sim pk msg s.1.1 s.1.2 alc halc q hq
      with hgh | hmsg
    · exact List.mem_cons_of_mem _ (hs q hgh)
    · exact hmsg ▸ List.mem_cons_self

omit [SampleableType Stmt] in
/-- **Whole-run ghost-domain invariant.** Lifting `ghostNmaImpl_preserves_signed_inv` through
the full simulated run via `simulateQ_run_preserves_inv_of_query`: starting from the empty
layered state `((∅, ∅), [])`, every output state `z` in the support of the layered ghost-tagged
NMA run records each ghost-layer point's message in the signed list. This is the support fact
gating the verify-tail split (`hybridVerifyCont_cache_congr`): on a fresh forgery `msg ∉ z.2.2`
the ghost layer misses at every `(msg, w)`, so the overlay agrees with the base layer there. -/
lemma ghostNmaImpl_run_signed_inv (pk : Stmt) (sk : Wit) {β : Type}
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
      (M →ₒ Option (Commit × Resp))) β) :
    ∀ z ∈ support ((simulateQ (ghostNmaImpl M maxAttempts sim pk sk) oa).run ((∅, ∅), [])),
      ∀ q : M × Commit, z.2.1.2 q ≠ none → q.1 ∈ z.2.2 := by
  refine simulateQ_run_preserves_inv_of_query
    (ghostNmaImpl M maxAttempts sim pk sk)
    (inv := fun s => ∀ q : M × Commit, s.1.2 q ≠ none → q.1 ∈ s.2)
    (fun t s hs => ghostNmaImpl_preserves_signed_inv M maxAttempts sim pk sk t s hs)
    oa ((∅, ∅), []) ?_
  intro q hq
  exact absurd rfl hq

omit [SampleableType Stmt] in
/-- **Sub-lemma (a): overlay projection of the layered NMA handler.** Each step of the
layered ghost-tagged handler `ghostNmaImpl`, projected by overlaying the ghost layer onto the
base layer, equals the corresponding step of the plain single-cache hybrid handler
`hybridBaseImpl + hybridSignImpl simSignBody`. -/
lemma ghostNmaImpl_proj_hybrid (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : NmaGhostState M Commit Chal) :
    Prod.map id (fun g : NmaGhostState M Commit Chal =>
        (overlayCache M g.1.1 g.1.2, g.2)) <$>
        (ghostNmaImpl M maxAttempts sim pk sk t).run s =
      ((hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (simSignBody M maxAttempts sim pk sk)) t).run
        (overlayCache M s.1.1 s.1.2, s.2) := by
  rcases t with (n | mc) | msg
  · simp only [ghostNmaImpl, StateT.run_mk, QueryImpl.add_apply_inl, hybridBaseImpl,
      unifFwdImpl, QueryImpl.liftTarget_apply, Functor.map_map]
    rfl
  · refine Eq.trans ?_
      (hybridBaseImpl_run_ro M mc (overlayCache M s.1.1 s.1.2) s.2).symm
    rw [ghostNmaImpl_run_ro]
    cases hgh : s.1.2 mc with
    | some v =>
        rw [roStep_of_some M (overlayCache_apply_ghost_some (M := M) s.1.1 hgh)]
        simp
    | none =>
        cases hre : s.1.1 mc with
        | some v =>
            rw [roStep_of_some M hre, roStep_of_some M (show overlayCache M
              s.1.1 s.1.2 mc = some v by
                rw [overlayCache_apply_ghost_none (M := M) s.1.1 hgh, hre])]
            simp
        | none =>
            rw [roStep_of_none M hre, roStep_of_none M (show overlayCache M
              s.1.1 s.1.2 mc = none by
                rw [overlayCache_apply_ghost_none (M := M) s.1.1 hgh, hre])]
            simp [overlayCache_cacheQuery_real_of_ghost_none (M := M) s.1.1 hgh]
  · refine Eq.trans (b := (fun ac : Option (Commit × Resp) ×
        (M × Commit →ₒ Chal).QueryCache => (ac.1, (ac.2, msg :: s.2))) <$>
        (simSignBody M maxAttempts sim pk sk msg).run
          (overlayCache M s.1.1 s.1.2)) ?_ ?_
    · rw [ghostNmaImpl_run_sign,
        ← run_simGhostSignBody_overlay M maxAttempts sim pk sk msg s.1.1 s.1.2]
      refine (Functor.map_map _ _ _).trans (Eq.symm ?_)
      exact (Functor.map_map _ _ _).trans rfl
    · exact (hybridSignImpl_run M (simSignBody M maxAttempts sim pk sk) msg
        (overlayCache M s.1.1 s.1.2) s.2).symm

/-! ### Live-read / sign-program collision event (sub-lemma (b) reframe)

The per-step state-projection equality `hproj2_sign` is *provably impossible*: a
sign-programmed transcript point `(msg, w)` can coincide with a point already written into the
base (live-read) layer by a prior adversary random-oracle query, and the projection
`proj₂ ((base, ghost), signed) = (baseEmbed base, overlayCache base ghost)` cannot recover the
linked managed handler's separate inner/outer cache split from `(base, ghost)` alone at such a
point (a `(msg, w)` in the overlay could have arrived via a live read — present in the outer
cache — or via signing — absent from the outer cache — and the layered state records no flag
distinguishing the two).

`signLiveCollisionState` is the exact state-level event distinguishing the two runs: at the
*start of a sign step* for message `msg`, the simulator's accepted commitment `w` lands on a
point `(msg, w)` already live in the base layer. Off this event (`base (msg, w) = none` for the
drawn `w`), the sign step's projection *is* a function of the state and the per-step coupling is
exact. On this event the two runs diverge, and — because the headline bound
`hybridSimRun_le_managedRun_verify` is an *inequality* (`≤`) — the divergence may be paid on the
bad side via the commit-guessing charge `probEvent_commit_hit_le` (the base layer's live-read
count times the per-commit guessing bound `ε`), exactly the charge class already used for the
ghost-read collision in `probEvent_ghostRead_bad_le`. -/

omit [SampleableType Stmt] [SampleableType Chal] in
/-- The live-read / sign-program collision predicate at a sign step. For a base (live-read)
cache `base` and a drawn accepted commitment `w` for message `msg`, the collision fires iff the
sign-programmed point `(msg, w)` is already present in the base layer (i.e. the simulator's
commitment landed on a previously live-read random-oracle point). This is the *exact* event off
which the layered NMA run and the linked managed run agree: when `base (msg, w) = none` the
sign-step projection `proj₂` is a function of the state, so the per-step coupling is an exact
equality; when it holds the two runs diverge and the gap is charged by
`probEvent_commit_hit_le`. -/
def signLiveCollision (base : (M × Commit →ₒ Chal).QueryCache) (msg : M) (w : Commit) : Prop :=
  base (msg, w) ≠ none

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq Commit] [DecidableEq M] in
/-- The collision is decidable and its negation is exactly the no-collision hypothesis
`base (msg, w) = none` under which the sign-step projection is exact. -/
lemma not_signLiveCollision_iff (base : (M × Commit →ₒ Chal).QueryCache) (msg : M) (w : Commit) :
    ¬ signLiveCollision M base msg w ↔ base (msg, w) = none := by
  simp [signLiveCollision]

omit [SampleableType Stmt] in
/-- **Sub-lemma (a), full-run form.** The full simulated run of the layered ghost-tagged NMA
handler `ghostNmaImpl`, projected by overlaying the ghost layer onto the base layer, equals
the plain single-cache simulated hybrid run.  This lifts the per-step projection
`ghostNmaImpl_proj_hybrid` through `OracleComp.map_run_simulateQ_eq_of_query_map_eq`. -/
lemma map_run_simulateQ_ghostNmaImpl_overlay {β : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
      (M →ₒ Option (Commit × Resp))) β)
    (s : NmaGhostState M Commit Chal) :
    Prod.map id (fun g : NmaGhostState M Commit Chal =>
        (overlayCache M g.1.1 g.1.2, g.2)) <$>
        (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) oa).run s =
      (simulateQ (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (simSignBody M maxAttempts sim pk sk)) oa).run
        (overlayCache M s.1.1 s.1.2, s.2) :=
  map_run_simulateQ_eq_of_query_map_eq
    (ghostNmaImpl M maxAttempts sim pk sk)
    (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
      hybridSignImpl M (simSignBody M maxAttempts sim pk sk))
    (fun g => (overlayCache M g.1.1 g.1.2, g.2))
    (ghostNmaImpl_proj_hybrid M maxAttempts sim pk sk) oa s

omit [SampleableType Stmt] in
/-- **Sub-lemma (a) at the initial empty layered state.** Starting from the empty layered
cache `((∅, ∅), [])`, the overlay-projected layered run equals the plain single-cache hybrid
run started from `(∅, [])` (using `overlayCache _ ∅ = id` to simplify the projected initial
state). -/
lemma map_run_simulateQ_ghostNmaImpl_overlay_empty {β : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
      (M →ₒ Option (Commit × Resp))) β) :
    Prod.map id (fun g : NmaGhostState M Commit Chal =>
        (overlayCache M g.1.1 g.1.2, g.2)) <$>
        (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) oa).run ((∅, ∅), []) =
      (simulateQ (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (simSignBody M maxAttempts sim pk sk)) oa).run (∅, []) := by
  rw [map_run_simulateQ_ghostNmaImpl_overlay M maxAttempts sim pk sk oa ((∅, ∅), [])]
  simp only [overlayCache_empty]

end FiatShamirWithAbort
