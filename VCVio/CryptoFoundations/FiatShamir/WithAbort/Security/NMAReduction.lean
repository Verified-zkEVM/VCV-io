/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.HopLemmas
public import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.NMAHandler

/-!
# EUF-CMA for Fiat-Shamir with aborts: NMAReduction

The NMA reduction: the two-layer nested managed simulation
(`simulatedNmaAdv` with inner managed handler and outer runtime handler) and the
linked-run coupling identifying it with the final hybrid.

Part of the CMA-to-NMA security development for the Fiat-Shamir-with-aborts
transform; `VCVio.CryptoFoundations.FiatShamir.WithAbort.Security` assembles
the headline `euf_cma_to_nma` and holds the overview docstring.
-/

public section

universe u v

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section EUF_CMA

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

section scaffold

variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
variable (adv : SignatureAlg.unforgeableAdv
  (FiatShamirWithAbort
    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))

/-! ## The NMA reduction

### Named managed/runtime handlers for the linked-run coupling

The managed NMA run is a two-layer nested simulation: an *inner managed* handler
`nmaOuterImpl pk` (forward uniform, managed-cache RO reads, simulator-loop signing) threads
the inner cache, and an *outer runtime* handler `nmaInnerImpl` (`unifFwdImpl + randomOracle`)
re-simulates the residual live queries. Their `link`, `nmaLinkImpl pk`, is the single
combined simulation over the product cache that the per-step state-coupling projects onto.
Naming the three handlers at top level lets the coupling be stated and proved against
`nmaLinkImpl pk` one query step at a time. -/

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- **Uniform-only nested-simulation collapse.**
The simulator loop inside `sigSim`/`nmaOuterImpl` is run under the inner managed handler's
uniform branch `unifSim n = fwd (.inl n)`, which forwards each uniform draw transparently into
the sum spec without touching the managed cache. Hence simulating any `unifSpec`-only
computation `oa` under `unifSim` and running the resulting `StateT` at a cache `cache` returns
`oa` lifted into the sum spec with the cache threaded *unchanged*: `(simulateQ unifSim oa).run
cache = (·, cache) <$> liftComp oa _`. This collapses the `simulateQ unifSim (firstSome (sim
pk) maxAttempts)` nested simulation in the sign step back to the bare lifted `firstSome` loop —
the part of `hproj2_sign` that is independent of the live-read/sign collision. -/
lemma simulateQ_unifSim_run {α : Type}
    (oa : OracleComp unifSpec α)
    (cache : (unifSpec + (M × Commit →ₒ Chal)).QueryCache) :
    let spec := unifSpec + (M × Commit →ₒ Chal)
    let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
    let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
      fun n => fwd (.inl n)
    (simulateQ unifSim oa).run cache =
      (fun r => (r, cache)) <$> (liftComp oa (unifSpec + (M × Commit →ₒ Chal))) := by
  intro spec fwd unifSim
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x => simp [unifSim, fwd]
  | query_bind t k ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_query]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
      -- `unifSim t` forwards the uniform query `t` straight through into the sum spec, leaving
      -- the cache untouched.
      have hstep : (unifSim t).run cache
          = (liftComp (query t : OracleComp unifSpec _) spec) >>= fun u => pure (u, cache) := by
        simp only [unifSim, fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
        change ((liftM (query (Sum.inl t)) :
            StateT (unifSpec + (M × Commit →ₒ Chal)).QueryCache
              (OracleComp (unifSpec + (M × Commit →ₒ Chal))) _)).run cache = _
        rw [OracleComp.liftM_run_StateT]
        refine congrArg (· >>= fun u => pure (u, cache)) ?_
        rfl
      rw [hstep, liftComp_bind, map_bind, bind_assoc]
      simp only [pure_bind]
      exact bind_congr (fun u => ih u cache)

/-- The inner *managed* handler of the NMA reduction: forward uniform queries to the live
spec (`unifSim`), answer hash queries through the managed cache (`roSim`, forwarding misses
to the live oracle), and answer signing queries with the simulator loop (`sigSim`), programming
the accepted transcript's challenge into the managed cache. This is the
`(unifSim + roSim) + sigSim` handler used inside `simulatedNmaAdv`. -/
noncomputable def nmaOuterImpl (pk : Stmt) :
    QueryImpl.Stateful (unifSpec + (M × Commit →ₒ Chal))
      ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (unifSpec + (M × Commit →ₒ Chal)).QueryCache :=
  letI spec := unifSpec + (M × Commit →ₒ Chal)
  letI fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  letI unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
    fun n => fwd (.inl n)
  letI roSim : QueryImpl (M × Commit →ₒ Chal)
      (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none => do
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  letI sigSim : QueryImpl (M →ₒ Option (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun msg => do
    let r ← simulateQ unifSim (firstSome (sim pk) maxAttempts)
    match r with
    | some (w, c, z) =>
        modifyGet fun cache => (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
    | none => pure none
  (unifSim + roSim) + sigSim

/-- The outer *runtime* handler of the NMA reduction: forward uniform queries (`unifFwdImpl`)
and answer the residual live random-oracle reads through the runtime's own random oracle
(`randomOracle`), threading the outer cache. This is the
`unifFwdImpl + randomOracle` handler that re-simulates the `.run ∅` boundary in
`simulatedNmaAdv`. -/
noncomputable def nmaInnerImpl :
    QueryImpl.Stateful unifSpec (unifSpec + (M × Commit →ₒ Chal))
      ((M × Commit →ₒ Chal).QueryCache) :=
  unifFwdImpl (M × Commit →ₒ Chal) +
    (randomOracle : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))

/-- The single *linked* handler `nmaOuterImpl pk |>.link nmaInnerImpl` that collapses the
two-layer managed/runtime nesting into one simulation over the product cache
`((unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache)`.
The per-step state-coupling for the NMA bridge is stated against this handler. -/
noncomputable def nmaLinkImpl (pk : Stmt) :
    QueryImpl.Stateful unifSpec
      ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      ((unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache) :=
  (nmaOuterImpl M maxAttempts sim pk).link (nmaInnerImpl M)

/-- The linked-run projection of sub-lemma (b): map the layered ghost-tagged NMA state
`((base, ghost), signed)` onto the linked managed handler's product cache pair.

The product cache the linked handler `nmaLinkImpl` carries is
`(inner : (unifSpec + (M × Commit →ₒ Chal)).QueryCache, outer : (M × Commit →ₒ Chal).QueryCache)`,
where the **inner** managed cache accumulates *both* live random-oracle reads (`roSim` writes a
fresh value into the inner `.inr mc` slot) *and* the signing-programmed accepted transcripts
(`sigSim` writes `.inr (msg, w) ↦ c`), while the **outer** runtime cache accumulates *only* live
random-oracle reads (`sigSim` never forwards to the outer oracle).

Hence the consistent per-step projection is:

* `inner := baseEmbed (overlayCache base ghost)` — the *full* hybrid cache (live reads in the
  base layer plus signing-programmed points in the ghost layer), embedded into the sum-keyed
  inner cache; and
* `outer := base` — the live-read base layer only.

Both components are forced by the two step shapes: the random-oracle step writes a live read
into the inner cache, so the inner component must carry the overlay; the signing step writes
the programmed transcript into the inner cache and never touches the outer, so the outer
component must exclude ghost points. With `inner := baseEmbed (overlay base ghost)` and
`outer := base` both the RO step and the sign step are exact per-step equalities; the swapped
assignment `(baseEmbed base, overlayCache base ghost)` makes neither step a state function. The
signed-message list is forgotten — the linked handler carries no such list. -/
def proj2 (s : NmaGhostState M Commit Chal) :
    (unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache :=
  (baseEmbed M (overlayCache M s.1.1 s.1.2), s.1.1)

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), uniform-query step.** On a uniform query the layered ghost-tagged
handler `ghostNmaImpl`, projected by `proj2`, matches the linked managed handler `nmaLinkImpl`
applied to the projected state. The uniform query forwards straight through both handlers
(`unifSim`/`unifFwdImpl`) without touching either cache layer, so the coupling is the
straightforward forward pass. -/
lemma hproj2_unif (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : NmaGhostState M Commit Chal) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inl n))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inl n))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_unif, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
    HasQuery.toQueryImpl_apply, nmaInnerImpl, unifFwdImpl, proj2]
  rfl

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), random-oracle step — cached-read sub-case.** On a random-oracle query at a
point `mc` whose ghost layer misses (`hgm`) and whose base layer already holds a value `v`
(`hbh : s.1.1 mc = some v`), the layered ghost-tagged handler `ghostNmaImpl`, projected by
`proj2`, matches the linked managed handler `nmaLinkImpl` applied to the projected state. Both
sides read the cached value: `ghostNmaImpl` returns `roStep`'s cached branch (base hit), while
the linked `roSim` finds the same value in the inner managed cache (`baseEmbed base`, which holds
the base entry at `.inr mc`) and short-circuits, so neither cache layer is written.

The two other RO sub-cases are handled by the siblings `hproj2_ro_fresh` and
`hproj2_ro_ghost_hit`:

* **fresh live read** (`s.1.1 mc = none`, ghost miss, `hproj2_ro_fresh`): the read resamples; both
  sides write the sampled value to base/inner (`baseEmbed_cacheQuery`) and to overlay/outer
  (`overlayCache_cacheQuery_real_of_ghost_none`, via the `randomOracle_run_eq_roStep` round-trip),
  reducing to a `roStep`-on-`overlayCache` match under the inner-`roSim` / outer-`randomOracle`
  nested-simulation `.run` plumbing.
* **ghost hit** (`s.1.2 mc ≠ none`, `hproj2_ro_ghost_hit`): `ghostNmaImpl` returns the ghost value
  leaving its state untouched, whereas the linked `roSim` re-reads through the runtime
  `randomOracle`, recovering the same value from `overlayCache base ghost`. Because `proj2` places
  the *overlay* in the inner slot and only the base layer in the outer slot, the re-cached point is
  already present on the projected side, so the step is an equality without needing a
  reachable-state side condition. -/
lemma hproj2_ro (pk : Stmt) (sk : Wit) (mc : M × Commit) (v : Chal)
    (s : NmaGhostState M Commit Chal) (hgm : s.1.2 mc = none) (hbh : s.1.1 mc = some v) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inr mc))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inr mc))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_ro, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, proj2]
  rw [hgm]
  -- The inner managed cache is now `baseEmbed (overlayCache base ghost)`; since the ghost layer
  -- misses at `mc` (`hgm`), the overlay agrees with the base layer there (`= some v`), so `roSim`
  -- finds the value in the inner cache and short-circuits without touching either cache layer.
  have hov : overlayCache M s.1.1 s.1.2 mc = some v :=
    (overlayCache_apply_ghost_none (M := M) s.1.1 hgm).trans hbh
  erw [StateT.run_bind, StateT.run_get]
  simp only [pure_bind, baseEmbed_inr, hov, roStep_of_some M hbh, map_pure, nmaInnerImpl]
  erw [StateT.run_pure]
  simp only [map_pure, QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst, PFunctor.Lens.State.snd, Prod.map, id_eq, proj2]
  rfl

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), random-oracle step — ghost-hit sub-case.** On a random-oracle query at a
point `mc` whose ghost layer already holds a value `v` (`hgh : s.1.2 mc = some v`), the layered
ghost-tagged handler `ghostNmaImpl`, projected by `proj2`, matches the linked managed handler
`nmaLinkImpl` applied to the projected state. `ghostNmaImpl` returns the ghost value leaving its
state untouched; under `proj2` the inner managed cache is `baseEmbed (overlayCache base ghost)`,
which carries the ghost value at `.inr mc` (`overlayCache_apply_ghost_some`), so the linked
`roSim` finds it and short-circuits without touching either layer. Placing the overlay — rather
than the bare base layer — in the inner slot is what makes this sub-case an exact equality, with
no reachability side condition on the state. -/
lemma hproj2_ro_ghost_hit (pk : Stmt) (sk : Wit) (mc : M × Commit) (v : Chal)
    (s : NmaGhostState M Commit Chal) (hgh : s.1.2 mc = some v) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inr mc))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inr mc))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_ro, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, proj2]
  rw [hgh]
  -- The overlay holds the ghost value at `mc`, so the inner managed cache `baseEmbed (overlay
  -- base ghost)` does too; `roSim` short-circuits.
  have hov : overlayCache M s.1.1 s.1.2 mc = some v :=
    overlayCache_apply_ghost_some (M := M) s.1.1 hgh
  erw [StateT.run_bind, StateT.run_get]
  simp only [pure_bind, baseEmbed_inr, hov, map_pure, nmaInnerImpl]
  erw [StateT.run_pure]
  simp only [map_pure, QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst, PFunctor.Lens.State.snd, Prod.map, id_eq, proj2]
  rfl

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), random-oracle step — fresh-live-read sub-case.** On a random-oracle
query at a point `mc` whose ghost layer misses (`hgm`) and whose base layer also misses
(`hbm : s.1.1 mc = none`), the layered ghost-tagged handler `ghostNmaImpl`, projected by
`proj2`, matches the linked managed handler `nmaLinkImpl` applied to the projected state.
Both sides resample a fresh value `c`; `ghostNmaImpl` writes it to the base layer (`roStep`'s
miss branch), while the linked `roSim` misses the inner managed cache (`baseEmbed base`,
which has no entry at `.inr mc` since `base mc = none`) and forwards to the runtime
`randomOracle` (the `randomOracle_run_eq_roStep` round-trip), caching the result both in the
inner managed cache and the outer runtime cache. Under `proj2`, the inner write matches
`baseEmbed_cacheQuery` and the outer write matches `overlayCache_cacheQuery_real_of_ghost_none`. -/
lemma hproj2_ro_fresh (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : NmaGhostState M Commit Chal) (hgm : s.1.2 mc = none) (hbm : s.1.1 mc = none) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inr mc))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inr mc))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_ro, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, proj2]
  rw [hgm]
  -- The inner managed cache is now `baseEmbed (overlayCache base ghost)`; since both the ghost
  -- layer (`hgm`) and the base layer (`hbm`) miss at `mc`, the overlay misses there too, so
  -- `roSim`'s inner lookup misses and forwards to the outer runtime `randomOracle`.
  have hov : overlayCache M s.1.1 s.1.2 mc = none := by simp [overlayCache, hgm, hbm]
  erw [StateT.run_bind, StateT.run_get]
  simp only [pure_bind, baseEmbed_inr, hov]
  rw [QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
  -- Reduce the inner `roSim` body run to a single `query` followed by an inner-cache write,
  -- then push `simulateQ nmaInnerImpl` through it: the `.inr mc` query is answered by the
  -- runtime `randomOracle`, whose run is `roStep` on the outer cache.
  conv_rhs =>
    enter [2, 1, 2]
    change (query (Sum.inr mc) : OracleComp (unifSpec + (M × Commit →ₒ Chal)) _) >>=
      fun v => pure (v, (baseEmbed M (overlayCache M s.1.1 s.1.2)).cacheQuery (Sum.inr mc) v)
  rw [simulateQ_bind]
  simp only [simulateQ_pure]
  conv_rhs =>
    enter [2, 1, 1]
    rw [show (query (Sum.inr mc) : OracleComp (unifSpec + (M × Commit →ₒ Chal)) _) =
        liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inr mc)) from rfl,
      simulateQ_spec_query]
    simp only [nmaInnerImpl, QueryImpl.add_apply_inr]
  rw [StateT.run_bind]
  conv_rhs => enter [2, 1]; erw [randomOracle_run_eq_roStep]
  -- Both sides resample: the layered run's base layer and the linked run's outer cache (now the
  -- base layer too) both miss at `mc`.
  rw [roStep_of_none M hbm]
  -- Normalise both sides to a single resample, mapping `c` to a `(c, inner, outer)` triple.
  simp only [bind_pure_comp, StateT.run_pure]
  conv_lhs => erw [Functor.map_map, Functor.map_map]
  conv_rhs => erw [Functor.map_map, Functor.map_map]
  refine map_congr fun c => ?_
  -- Reconcile the cache writes on the two layers: the inner write matches `baseEmbed`'s
  -- `cacheQuery`, the outer write matches the overlay's `cacheQuery` (ghost misses at `mc`).
  simp only [Prod.map, id_eq, proj2, QueryImpl.Stateful.Frame.linkReshape,
    QueryImpl.Stateful.Frame.prod, PFunctor.Lens.State.fst, PFunctor.Lens.State.snd,
    PFunctor.Lens.State.put, PFunctor.Lens.State.mk]
  rw [overlayCache_cacheQuery_real_of_ghost_none (M := M) s.1.1 hgm, baseEmbed_cacheQuery]

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), signing-query step — exact per-step equality.**

On a signing query, the layered ghost-tagged handler `ghostNmaImpl`, projected by the
*redesigned* `proj2 ((base, ghost), signed) = (baseEmbed (overlayCache base ghost), base)`,
equals the linked managed handler `nmaLinkImpl` applied to the projected state — *unconditionally*
(no collision hypothesis).

The redesign is what makes this exact. The linked managed `sigSim` writes the accepted transcript
into the *inner managed cache* (`cacheQuery (.inr (msg, w)) c`) and leaves the *outer runtime
cache* untouched. The layered run writes the same transcript into the *ghost layer*, leaving the
base layer untouched. Under `proj2`, the inner managed cache is recovered as `baseEmbed`
of the *full overlay* `overlayCache base ghost`, so the ghost-layer write surfaces in `proj2`'s
*first* slot exactly where `sigSim` writes (`overlayCache_cacheQuery_ghost` then
`baseEmbed_cacheQuery`), while the outer cache is `proj2`'s *second* slot `base`, untouched on both
sides. There is no slot swap and no dependence on whether `(msg, w)` coincides with a prior live
read: `proj2`'s first component carries the full overlay, so the sign point lands in the same inner
slot regardless.

PROOF SHAPE. `link_impl_apply_run` exposes the linked RHS as the nested simulation
`simulateQ nmaInnerImpl ((nmaOuterImpl pk (.inr msg)).run outerCache)`; `simp [nmaOuterImpl]`
reduces the outer step to the `sigSim` body — a nested `simulateQ unifSim (firstSome (sim pk)
maxAttempts)` (collapsed by `simulateQ_unifSim_run`, the simulator loop touches no cache layer)
followed by inner-cache programming `cacheQuery (.inr (msg, w)) c`. The LHS is `simGhostSignBody`
(`liftM (firstSome (sim pk) maxAttempts)` then ghost-layer `cacheQuery (msg, w) c`). A
support-restricted `SPMF` bind congruence on the accepted transcript then reduces both sides to
matching pure values, closed by the overlay/`baseEmbed` cache algebra above. -/
lemma hproj2_sign (pk : Stmt) (sk : Wit) (msg : M)
    (s : NmaGhostState M Commit Chal) :
    𝒮[Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inr msg)).run s] =
      𝒮[(nmaLinkImpl M maxAttempts sim pk (.inr msg)).run (proj2 M s)] := by
  rw [ghostNmaImpl_run_sign, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  -- Reduce the linked RHS's outer step `nmaOuterImpl pk (.inr msg)` to the simulator body
  -- `sigSim msg`: a nested simulation `simulateQ unifSim (firstSome (sim pk) maxAttempts)`
  -- followed by inner-cache programming of the accepted transcript. After this the residual is
  -- the uniform-only nested-simulation collapse (i) above; the per-step equality then fails
  -- exactly on `signLiveCollision`, which the leaf's collision-accounting reframe pays on the
  -- bad side rather than discharging here.
  simp only [nmaOuterImpl, QueryImpl.add_apply_inr]
  -- Reduce the LHS to `firstSome (sim pk) maxAttempts >>= ghostSignProgramCont`.
  simp only [simGhostSignBody, StateT.run_bind, OracleComp.liftM_run_StateT, bind_assoc,
    pure_bind, map_bind]
  -- Collapse the RHS's nested `simulateQ unifSim (firstSome …)` loop via `simulateQ_unifSim_run`.
  conv_rhs => enter [1, 2, 1]; rw [simulateQ_unifSim_run]
  -- Distribute the outer `simulateQ nmaInnerImpl` and `.run` over the bind, and collapse the
  -- lifted `firstSome` loop against `nmaInnerImpl`'s uniform-forwarding branch (`roSim`).
  rw [simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map]
  rw [show nmaInnerImpl M = unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) from rfl,
    roSim.simulateQ_liftComp, unifFwdImpl.simulateQ_run]
  -- Both sides are now `firstSome … >>= (per-output programming)`; align by support-restricted
  -- bind congruence and case-split on the accepted transcript.
  simp only [map_bind, Functor.map_map, bind_map_left]
  -- Move into `SPMF` (where the map/bind laws apply cleanly, dodging the `OracleComp` `Functor`
  -- vs `Monad` map friction): both sides become `𝒮[firstSome …] >>= (per-output programming)`.
  simp only [evalSPMF_map, evalSPMF_bind]
  -- Support-restricted `SPMF` bind congruence (`evalSPMF_bind_congr` with `m := SPMF`, where
  -- `evalSPMF` is the identity): case-split on the accepted transcript, using the no-collision
  -- hypothesis on the `some` branch.
  refine evalSPMF_bind_congr (m := SPMF) (mx := 𝒮[firstSome (sim pk) maxAttempts])
    fun a _ha => ?_
  simp only [SPMF.evalSPMF_def]
  -- Case-split on the accepted transcript; under the redesigned `proj2` the `some` branch aligns
  -- the ghost-layer write with the inner-cache write unconditionally (no collision hypothesis).
  cases a with
  | none =>
      -- The all-abort outcome programs no point on either side; both reduce to `(none, proj2 s)`.
      simp only [ghostSignProgramCont, StateT.run_pure, simulateQ_pure, evalSPMF_pure, map_pure,
        proj2, QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
        PFunctor.Lens.State.fst, PFunctor.Lens.State.snd, PFunctor.Lens.State.put,
        PFunctor.Lens.State.mk, Prod.map, id_eq]
  | some wcz =>
      obtain ⟨w, c, z⟩ := wcz
      -- Reduce the LHS ghost-layer programming to a pure value.
      simp only [ghostSignProgramCont, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_pure]
      -- Reduce the RHS inner-cache programming and the trivial outer simulation to a pure value.
      conv_rhs => enter [2, 1, 1, 2]; erw [StateT.run_modifyGet]
      rw [simulateQ_pure]
      erw [StateT.run_pure]
      simp only [evalSPMF_pure, map_pure, proj2, QueryImpl.Stateful.Frame.linkReshape,
        QueryImpl.Stateful.Frame.prod, PFunctor.Lens.State.fst, PFunctor.Lens.State.snd,
        PFunctor.Lens.State.put, PFunctor.Lens.State.mk]
      simp only [proj2, Prod.map, id_eq]
      -- Off the collision (`hbase : s.1.1 (msg, w) = none`) the two pure values agree exactly under
      -- the *redesigned* `proj2 ((base, ghost), signed) = (baseEmbed (overlay base ghost), base)`.
      -- Both sides write the accepted transcript into the inner managed cache and leave the outer
      -- (live-read) cache `base` untouched:
      --   LHS = (some (w, z), baseEmbed (overlay base (ghost.cacheQuery (msg, w) c)), base)
      --   RHS = (some (w, z), (baseEmbed (overlay base ghost)).cacheQuery (.inr (msg, w)) c, base).
      -- The ghost-layer write surfaces in the inner cache (`proj2`'s *first* slot, via the overlay)
      -- exactly where the linked `sigSim` writes `.inr (msg, w) ↦ c`, and the live-read layer
      -- `base` (`proj2`'s *second* slot = the linked outer cache) is untouched on both sides — so
      -- the per-step sign equality is now exact (no slot swap). The `hbase` no-collision hypothesis
      -- is not even needed for the cache algebra under the redesigned projection: `proj2`'s first
      -- component carries the full overlay, so the sign point lands in the same inner slot whether
      -- or not it coincides with a prior live read.
      rw [overlayCache_cacheQuery_ghost, baseEmbed_cacheQuery]

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), unified per-step `evalSPMF` coupling.** For *every* oracle query `t` and
every layered state `s`, the `proj2`-projected layered NMA step has the same output/state
distribution as the linked managed step on the projected state. This bundles the four per-step
lemmas (`hproj2_unif`, `hproj2_ro`/`hproj2_ro_ghost_hit`/`hproj2_ro_fresh`, `hproj2_sign`): under
the redesigned `proj2 ((base, ghost), signed) = (baseEmbed (overlayCache base ghost), base)` each
step is an exact equality (the random-oracle and signing steps no longer depend on any reachability
or no-collision side condition), so the coupling holds unconditionally on all of `t`. This is the
per-query hypothesis for the whole-run state-projection `relTriple_simulateQ_run`. -/
lemma hproj2_evalSPMF (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : NmaGhostState M Commit Chal) :
    𝒮[Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk t).run s] =
      𝒮[(nmaLinkImpl M maxAttempts sim pk t).run (proj2 M s)] := by
  rcases t with (n | mc) | msg
  · exact congrArg _ (hproj2_unif M maxAttempts sim pk sk n s)
  · rcases hgh : s.1.2 mc with _ | v
    · rcases hbh : s.1.1 mc with _ | w
      · exact congrArg _ (hproj2_ro_fresh M maxAttempts sim pk sk mc s hgh hbh)
      · exact congrArg _ (hproj2_ro M maxAttempts sim pk sk mc w s hgh hbh)
    · exact congrArg _ (hproj2_ro_ghost_hit M maxAttempts sim pk sk mc v s hgh)
  · exact hproj2_sign M maxAttempts sim pk sk msg s

/-- **Graph coupling along a function.** If pushing `oa` forward through `F` matches `ob` in
distribution, then `oa` and `ob` are related (as a `RelTriple`) by the graph relation
`fun a b => F a = b`. This is the reverse direction of `evalSPMF_map_eq_of_relTriple`: the
witnessing coupling is the deterministic coupling `𝒮[oa] >>= fun a => pure (a, F a)`, whose first
marginal is `𝒮[oa]` and whose second marginal is `𝒮[F <$> oa] = 𝒮[ob]`, supported on the graph. -/
private lemma relTriple_graph_of_evalSPMF_map_eq
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {α' σ' : Type} (F : α' → σ')
    (oa : OracleComp spec₁ α') (ob : OracleComp spec₂ σ')
    (h : 𝒮[F <$> oa] = 𝒮[ob]) :
    OracleComp.ProgramLogic.Relational.RelTriple oa ob (fun a b => F a = b) := by
  apply (OracleComp.ProgramLogic.Relational.relTriple_iff_relWP
    (oa := oa) (ob := ob) (R := fun a b => F a = b)).2
  refine ⟨⟨𝒮[oa] >>= fun a => pure (a, F a), ?_, ?_⟩, ?_⟩
  · rw [map_bind]; simp
  · rw [← h, evalSPMF_map, map_bind]; simp
  · intro z hz
    rcases (mem_support_bind_iff
      (𝒮[oa]) (fun a => (pure (a, F a) : SPMF (α' × σ'))) z).1 hz with ⟨a, _, hz'⟩
    have hzEq : z = (a, F a) := by
      simpa [support_pure, Set.mem_singleton_iff] using hz'
    simp [hzEq]

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), whole-run state projection.** The full layered ghost-tagged NMA run
`(simulateQ ghostNmaImpl (adv.main pk)).run s`, projected by `proj2`, has the same output/state
distribution as the linked managed run `(simulateQ nmaLinkImpl (adv.main pk)).run (proj2 s)`. This
lifts the per-step coupling `hproj2_evalSPMF` through `relTriple_simulateQ_run` with the state
relation `R s' p := proj2 s' = p` (output-equal, `proj2`-related states), the per-step `RelTriple`
being recovered from the per-step `evalSPMF`-map equality by the graph coupling
`relTriple_graph_of_evalSPMF_map_eq`. -/
lemma evalSPMF_map_run_simulateQ_ghostNmaImpl_proj2 {β : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
      (M →ₒ Option (Commit × Resp))) β)
    (s : NmaGhostState M Commit Chal) :
    𝒮[Prod.map id (proj2 M) <$> (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) oa).run s] =
      𝒮[(simulateQ (nmaLinkImpl M maxAttempts sim pk) oa).run (proj2 M s)] := by
  -- State relation: `s'` and `p` are related iff `p` is the `proj2`-projection of `s'`.
  have hrel := OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run
    (impl₁ := ghostNmaImpl M maxAttempts sim pk sk)
    (impl₂ := nmaLinkImpl M maxAttempts sim pk)
    (R_state := fun (s' : NmaGhostState M Commit Chal) p => proj2 M s' = p)
    (oa := oa)
    (himpl := fun t s₁ s₂ hs => ?_)
    (s₁ := s) (s₂ := proj2 M s) rfl
  · -- The whole-run `RelTriple` carries `p₁.1 = p₂.1 ∧ proj2 p₁.2 = p₂.2`, i.e. the graph of
    -- `Prod.map id proj2`. Re-express it as a graph relation and extract the `map`-equality.
    have hrel' : OracleComp.ProgramLogic.Relational.RelTriple
        ((simulateQ (ghostNmaImpl M maxAttempts sim pk sk) oa).run s)
        ((simulateQ (nmaLinkImpl M maxAttempts sim pk) oa).run (proj2 M s))
        (fun p₁ p₂ => Prod.map id (proj2 M) p₁ = p₂) :=
      OracleComp.ProgramLogic.Relational.relTriple_post_mono hrel
        (fun p₁ p₂ ⟨h1, h2⟩ => Prod.ext h1 h2)
    have := OracleComp.ProgramLogic.Relational.evalSPMF_map_eq_of_relTriple
      (f := Prod.map id (proj2 M)) (g := id) hrel'
    simpa using this
  · -- Per-step coupling from the unified per-step `evalSPMF`-map equality, via the graph coupling.
    subst hs
    refine OracleComp.ProgramLogic.Relational.relTriple_post_mono
      (relTriple_graph_of_evalSPMF_map_eq (F := Prod.map id (proj2 M))
        ((ghostNmaImpl M maxAttempts sim pk sk t).run s₁)
        ((nmaLinkImpl M maxAttempts sim pk t).run (proj2 M s₁))
        (hproj2_evalSPMF M maxAttempts sim pk sk t s₁)) ?_
    rintro p₁ p₂ rfl
    exact ⟨rfl, rfl⟩


/-- The managed-RO NMA reduction for Fiat-Shamir with aborts: run the CMA adversary,
forwarding uniform queries, answering live hash queries through a managed cache, and
answering signing queries with the simulator loop of `simSignBody` (programming the
accepted transcript's challenge into the managed cache). Returns the forgery together
with the managed cache, in the interface of `SignatureAlg.managedRoNmaAdv`. -/
@[expose] noncomputable def simulatedNmaAdv :
    SignatureAlg.managedRoNmaAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts) where
  main pk :=
    let spec := unifSpec + (M × Commit →ₒ Chal)
    let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
    let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
      fun n => fwd (.inl n)
    let roSim : QueryImpl (M × Commit →ₒ Chal)
        (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
      let cache ← get
      match cache (.inr mc) with
      | some v => pure v
      | none => do
          let v ← fwd (.inr mc)
          modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
    let sigSim : QueryImpl (M →ₒ Option (Commit × Resp))
        (StateT spec.QueryCache (OracleComp spec)) := fun msg => do
      let r ← simulateQ unifSim (firstSome (sim pk) maxAttempts)
      match r with
      | some (w, c, z) =>
          modifyGet fun cache => (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
      | none => pure none
    -- Run the inner CMA adversary under the managed simulation, then erase the
    -- forgery's own verification point from the returned cache (Option B). The
    -- with-aborts `verify pk msg (some (w', z))` issues exactly one hash query, at
    -- `(msg, w')`; clearing that entry makes `withCacheOverlay advCache verify` miss
    -- there and fall through to the live oracle, so the managed-RO experiment agrees
    -- with the plain EUF-NMA verification on *every* forgery. In particular a replayed
    -- signed `(msg, w')` no longer wins through the programmed challenge, which is what
    -- makes the bridge to `eufNmaAdv.advantage` sound. Other programmed entries sit at
    -- different points and are never read by `verify`.
    (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅ >>= fun result =>
      let ((msg, σ), cache) := result
      let advCache : spec.QueryCache :=
        match σ with
        | some (w', _) => Function.update cache (Sum.inr (msg, w')) none
        | none => cache
      pure ((msg, σ), advCache)

omit [SampleableType Stmt] in
/-- **Nested-simulation fusion for the managed NMA run.** The managed reduction runs the
common adversary `adv.main pk` under the inner managed handler `nmaOuterImpl pk` threading the
inner cache (`StateT spec.QueryCache (OracleComp spec)`), then `.run ∅` re-simulates the
residual live queries under the outer runtime handler `nmaInnerImpl` (`unifFwdImpl +
randomOracle`) threading the outer cache. By `QueryImpl.Stateful.simulateQ_link_run` this
two-layer nesting is a single simulation of the *linked* handler `nmaLinkImpl pk =
(nmaOuterImpl pk).link nmaInnerImpl` over the product cache, up to the canonical `linkReshape`
regrouping of the final state. This collapses the explicit `.run ∅` boundary into a single
`simulateQ` whose state is the genuine `(inner managed cache, outer runtime cache)` pair the
per-step coupling projects onto. -/
lemma managedRun_eq_link_run (pk : Stmt) :
    letI spec := unifSpec + (M × Commit →ₒ Chal)
    (simulateQ (nmaLinkImpl M maxAttempts sim pk) (adv.main pk)).run (∅, ∅) =
      (QueryImpl.Stateful.Frame.prod spec.QueryCache
          ((M × Commit →ₒ Chal).QueryCache)).linkReshape (∅, ∅) <$>
        (simulateQ (nmaInnerImpl M)
          ((simulateQ (nmaOuterImpl M maxAttempts sim pk)
            (adv.main pk)).run ∅)).run ∅ := by
  exact (QueryImpl.Stateful.simulateQ_link_run _ _ (adv.main pk) ∅ ∅)

omit [SampleableType Stmt] [SampleableType Chal] in
/-- If a cache misses at the forgery's verification point `Sum.inr (msg, w')`, the overlay
verification of `FiatShamirWithAbort.verify pk msg (some (w', z))` agrees with the plain
live verification: the single query at `Sum.inr (msg, w')` misses and is forwarded live.
The `none` case is verification-free, so it is trivially overlay-insensitive. -/
lemma withCacheOverlay_verify_eq_of_miss
    (cache : (unifSpec + (M × Commit →ₒ Chal)).QueryCache) (pk : Stmt)
    (msg : M) (σ : Option (Commit × Resp))
    (hmiss : ∀ w' z, σ = some (w', z) → cache (Sum.inr (msg, w')) = none) :
    withCacheOverlay cache
        ((FiatShamirWithAbort (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
          ids hr M maxAttempts).verify pk msg σ) =
      (FiatShamirWithAbort (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts).verify pk msg σ := by
  cases σ with
  | none => simp only [FiatShamirWithAbort, withCacheOverlay_pure]
  | some wz =>
      obtain ⟨w', z⟩ := wz
      have hm : cache (Sum.inr (msg, w')) = none := hmiss w' z rfl
      change withCacheOverlay _
          ((query (Sum.inr (msg, w')) :
            OracleComp (unifSpec + (M × Commit →ₒ Chal))
              ((unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inr (msg, w')))) >>=
            fun c => pure (ids.verify pk w' c z)) =
        (query (Sum.inr (msg, w')) :
            OracleComp (unifSpec + (M × Commit →ₒ Chal))
              ((unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inr (msg, w')))) >>=
            fun c => pure (ids.verify pk w' c z)
      rw [withCacheOverlay_bind_pure, bind_pure_comp]
      congr 1
      exact withCacheOverlay_query_miss _ (Sum.inr (msg, w')) hm

omit [SampleableType Stmt] in
/-- **Verify-tail pointwise split** (the per-forgery content of the NMA bridge). On a common
ghost-tagged output state `((base, ghost), signed)` satisfying the ghost-domain invariant
(every ghost point's message is signed), the hybrid verification-and-freshness continuation
`hybridVerifyCont` on the overlay cache is bounded by the managed overlay verification on the
base cache. On `msg ∈ signed` the freshness conjunct zeroes the left
(`probOutput_true_hybridVerifyCont_of_mem`); on a fresh forgery `msg ∉ signed` the invariant
makes the ghost layer miss at every `(msg, w)`, so the overlay agrees with the base cache
(`hybridVerifyCont_cache_congr`), the Option-B post-processing makes `withCacheOverlay` miss
its own verification point (`withCacheOverlay_verify_eq_of_miss`), and the two tails coincide. -/
lemma probOutput_hybridVerifyCont_le_managed_verify (pk : Stmt)
    (ms : M × Option (Commit × Resp)) (base ghost : (M × Commit →ₒ Chal).QueryCache)
    (signed : List M)
    (hinv : ∀ q : M × Commit, ghost q ≠ none → q.1 ∈ signed) :
    Pr[= true | hybridVerifyCont ids hr M maxAttempts pk
        (ms, (overlayCache M base ghost, signed))] ≤
      Pr[= true | (fun x : Bool × _ => x.1) <$>
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          (withCacheOverlay
            (match ms.2 with
              | some (w', _) => Function.update (baseEmbed M (overlayCache M base ghost))
                  (Sum.inr (ms.1, w')) none
              | none => baseEmbed M (overlayCache M base ghost))
            ((FiatShamirWithAbort ids hr M maxAttempts).verify pk ms.1 ms.2))).run base] := by
  obtain ⟨msg, σ⟩ := ms
  by_cases hmem : msg ∈ signed
  · rw [probOutput_true_hybridVerifyCont_of_mem ids hr M maxAttempts pk (msg, σ)
      (overlayCache M base ghost) signed hmem]
    exact zero_le
  · rw [withCacheOverlay_verify_eq_of_miss ids hr M maxAttempts _ pk msg σ
        (by intro w' z hσ; simp [hσ]),
      hybridVerifyCont_cache_congr ids hr M maxAttempts pk (msg, σ)
        (overlayCache M base ghost) base signed
        (fun w => overlayCache_apply_ghost_none (M := M) base
          (by by_contra h; exact hmem (hinv (msg, w) h)))]
    refine le_of_eq ?_
    simp only [hybridVerifyCont, hmem, not_false_eq_true, decide_true, Bool.true_and,
      StateT.run', bind_pure]
    rfl

omit [SampleableType Stmt] in
/-- **State-coupling for the NMA bridge** (genuine two-layer content). At a fixed key pair
the single-cache hybrid run of `hybridExpAtKey`, *followed by its verification-and-freshness
tail* `hybridVerifyCont`, is bounded by the run-normal-form of the managed-RO NMA
experiment: the managed-cache run of `simulatedNmaAdv` (re-simulated under the runtime's
outer `randomOracle`), followed by overlay verification.

The two presentations run the *same* adversary `adv.main pk` but thread the random-oracle
cache through genuinely different layers:

* the **hybrid** (`impl₁ := hybridBaseImpl + hybridSignImpl simSignBody`) keeps a *single*
  cache `(cache, signed)`, into which both live RO reads (`randomOracle`) and the signing
  simulation's accepted-transcript programming (`simSignBody` via `signProgramCont`) write;
* the **managed reduction** (`simulatedNmaAdv.main`) keeps an *inner managed* cache threaded
  by `roSim`/`sigSim`, whose live `fwd` reads are resolved by the runtime's *separate outer*
  `randomOracle` cache. `simulateQ_compose` (`∘ₛ`) does not collapse these two layers because
  the inner `.run ∅` boundary turns `roSim`/`fwd` misses into live queries answered by the
  outer oracle.

The coupling claim is that the *overlay* of the inner managed cache onto the outer runtime
cache reproduces the single hybrid cache throughout the run (a state-projection in the sense
of `OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'`), and that the signed-message list
matches the set of points the managed simulation programmed (a cache invariant in the style
of `fsAbortSignLoop_cache_invariant`). On `msg ∈ signed` the freshness conjunct kills the
left side (`probOutput_true_hybridVerifyCont_of_mem`); on fresh forgeries the
`withCacheOverlay` verification agrees with the live verification at the verification point
(`withCacheOverlay_verify_eq_of_miss`, since the managed point at `(msg, w')` carries the
programmed challenge that equals the hybrid's cached value, while the freshness check rules
out a stale read). Hence the per-forgery success of the hybrid tail is at most that of the
overlay verification, and the bound follows. -/
lemma hybridSimRun_le_managedRun_verify (pk : Stmt) (sk : Wit) :
    Pr[= true | (simulateQ
          (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
            hybridSignImpl M (simSignBody M maxAttempts sim pk sk))
          (adv.main pk)).run (∅, []) >>= hybridVerifyCont ids hr M maxAttempts pk] ≤
      Pr[= true | (fun x : Bool × _ => x.1) <$> do
        let p ← (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pk)).run ∅
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          (withCacheOverlay p.1.2 ((FiatShamirWithAbort ids hr M maxAttempts).verify
            pk p.1.1.1 p.1.1.2))).run p.2] := by
  -- STEP 1 (the link fusion, executed by the `simp only` below): collapse the explicit `.run ∅`
  -- re-simulation boundary on the RHS. Distributing the outer `simulateQ` over
  -- `simulatedNmaAdv`'s post-processing bind (`simulateQ_bind`/`StateT.run_bind`) exposes the
  -- nested managed run
  --   `(simulateQ (unifFwd+ro) ((simulateQ ((unifSim+roSim)+sigSim) (adv.main pk)).run ∅)).run ∅`,
  -- which `managedRun_eq_link_run` rewrites to the canonical `linkReshape` of a *single* linked
  -- simulation `(simulateQ nmaLinkImpl (adv.main pk)).run (∅, ∅)` over the product cache
  -- `(inner managed cache, outer runtime cache)`. After this rewrite the RHS is a single
  -- `simulateQ` whose state is genuinely the inner/outer cache pair.
  --
  -- WHY THE COUPLING RUNS ON A LAYERED STATE. The two sides are not related by a state projection
  -- out of the plain hybrid state `(reCache, signed)`. Replaying both handlers per step, the
  -- linked caches evolve as:
  --   * `outerCache` accumulates *only live RO reads* (`roSim` forwards inner misses to `fwd`,
  --     re-simulated by the inner `randomOracle`, which writes the outer layer); signing's
  --     `sigSim` programs the *inner* layer only and never forwards to the outer oracle;
  --   * `innerCache` accumulates *both* live RO reads *and* the signing-programmed points.
  -- So `outerCache = reCache ∖ {signing-only-programmed points}` is not a function of
  -- `(reCache, signed)`: a point `(msg, w)` with `msg ∈ signed` may have entered `reCache` either
  -- by a live RO read (then it is in `outerCache`) or by `signProgramCont` (then it is absent
  -- from `outerCache`), and the plain hybrid state records no flag distinguishing the two. The
  -- proof therefore runs the adversary on an *enriched, layered* cache state that tags each entry
  -- as live-read (base layer) vs signing-programmed (ghost layer) — the same `overlayCache` /
  -- ghost-layer device used for the Prog→Trans hop in `GhostBodies` — namely `ghostNmaImpl` over
  -- `NmaGhostState = ((baseCache, ghostCache), signed)`. On that state the partition *is* a state
  -- function and both projections are per-step state projections.
  simp only [simulatedNmaAdv, simulateQ_bind, StateT.run_bind, bind_assoc]
  -- The RHS is now `(fun x => x.1) <$> do let p ← (simulateQ (unifFwd+ro)
  --   ((simulateQ ((unifSim+roSim)+sigSim) (adv.main pk)).run ∅)).run ∅; (Option-B post)…`,
  -- with the bare nested managed run exposed. `managedRun_eq_link_run` equates this nested
  -- run (modulo the canonical `linkReshape <$> _` regrouping of the final state) with the
  -- single linked simulation `(simulateQ (outer.link inner) (adv.main pk)).run (∅, ∅)`.
  --
  -- With the nested boundary exposed, the bound is the pair of state projections out of the
  -- layered ghost-tagged run, followed by the verify-tail split.
  --
  -- (a) HYBRID SIDE. `ghostNmaImpl` (`GhostBodies/NMAHandler.lean`) runs the adversary over
  -- `NmaGhostState = ((baseCache, ghostCache), signed)`, with
  -- `simGhostSignBody`/`ghostSignProgramCont` writing the accepted transcript to the ghost layer
  -- and the base oracles writing live RO reads to the base layer. Its overlay projection back to
  -- the plain single-cache hybrid is `ghostNmaImpl_proj_hybrid` (per step) and
  -- `map_run_simulateQ_ghostNmaImpl_overlay`/`_empty` (whole run), via
  -- `OracleComp.map_run_simulateQ_eq_of_query_map_eq` with
  -- `proj ((base, ghost), signed) = (overlayCache base ghost, signed)`. So the hybrid LHS equals
  -- `Pr[= true | (overlay-projected ghostNmaImpl run) >>= …]`.
  --
  -- (b) MANAGED SIDE. The *same* layered run projects onto the linked
  -- `(outerCache : spec.QueryCache, innerCache : (M × Commit →ₒ Chal).QueryCache)` pair under
  --   `proj2 ((base, ghost), signed) = (baseEmbed (overlayCache base ghost), base)`,
  -- i.e. the inner managed cache is the full hybrid overlay (live reads *and* programmed sign
  -- points) while the outer runtime cache is the live-read base layer only. Carrying the sign
  -- point in the inner slot is what makes the sign step a state function whether or not the
  -- programmed point coincides with a prior live read. This is not a primitive-query projection:
  -- by `linkWith_apply_run` each `nmaLinkImpl t` step is itself a nested
  -- `simulateQ nmaInnerImpl ((nmaOuterImpl t).run …)`, where `roSim` does an inner cache lookup
  -- and forwards a miss to `fwd` (re-simulated by the inner `randomOracle`, the
  -- `randomOracle_run_eq_roStep` round-trip) and `sigSim` runs a whole
  -- `simulateQ unifSim (firstSome (sim pk) maxAttempts)`. Against that nested form every per-step
  -- coupling is an exact unconditional equality — `hproj2_unif`, `hproj2_ro`,
  -- `hproj2_ro_ghost_hit`, `hproj2_ro_fresh`, `hproj2_sign` — bundled as `hproj2_evalSPMF` and
  -- lifted to the whole run by `evalSPMF_map_run_simulateQ_ghostNmaImpl_proj2` (via
  -- `relTriple_simulateQ_run` and the graph coupling `relTriple_graph_of_evalSPMF_map_eq`).
  -- The supporting facts are `ghostNmaImpl_preserves_signed_inv` (every ghost-layer point's msg
  -- lies in `signed`, the NMA analogue of `ghostHybridImpl_preserves_signed_inv`, backed by
  -- `simGhostSignBody_support_ghost`) and `baseEmbed`
  -- (+ `baseEmbed_inr`/`baseEmbed_inl`/`baseEmbed_cacheQuery`), the embedding of the base RO
  -- cache (keyed by `M × Commit`) into the sum-spec-keyed outer runtime cache, whose RO-step
  -- algebra is `baseEmbed (base.cacheQuery mc v) = (baseEmbed base).cacheQuery (.inr mc) v`.
  --
  -- (c) ASSEMBLY (the verify-tail split, executed below). By (a) and (b) the hybrid LHS run and
  -- the linked managed RHS run are both projections of the *same* layered ghost-tagged run
  -- `(simulateQ ghostNmaImpl (adv.main pk)).run ((∅,∅), [])`. The two verify tails are aligned on
  -- this common run by `probOutput_hybridVerifyCont_le_managed_verify` — on `msg ∈ signed` the
  -- freshness conjunct zeroes the hybrid side (`probOutput_true_hybridVerifyCont_of_mem`), and on
  -- fresh forgeries the overlay verification agrees with the live verification
  -- (`withCacheOverlay_verify_eq_of_miss`, `hybridVerifyCont_cache_congr`), gated by the whole-run
  -- ghost-domain invariant `ghostNmaImpl_run_signed_inv`. The `linkReshape` / post-processing
  -- regrouping is threaded by `managedRun_eq_link_run` + `bind_map_left`.
  --
  -- Reduce the Option-B post-processing `pure` (re-simulated under `nmaInner`) to its value, and
  -- pull the outer `(fun x => x.1) <$> _` past the head bind. The RHS is now `nestedManaged >>= K`
  -- with `K a = (fun x => x.1) <$> (simulateQ nmaInner (withCacheOverlay (advCache a)
  -- (verify pk a.1.1.1 a.1.1.2))).run a.2`.
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, map_bind]
  -- The managed verify tail, expressed as a function of the *value × linked cache pair*. By
  -- `proj2` it is the layered-run tail; by `linkReshape` it is the nested managed tail.
  set RHSverify : (M × Option (Commit × Resp)) ×
      ((unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache) →
      ProbComp Bool :=
    fun p => (fun x : Bool × _ => x.1) <$>
      (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
          (randomOracle : QueryImpl (M × Commit →ₒ Chal)
            (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
        (withCacheOverlay
          (match p.1.2 with
            | some (w', _) => Function.update p.2.1 (Sum.inr (p.1.1, w')) none
            | none => p.2.1)
          ((FiatShamirWithAbort ids hr M maxAttempts).verify pk p.1.1 p.1.2))).run p.2.2
    with hRHSverify
  -- LHS: rewrite the plain hybrid run as the overlay projection of the layered ghost run (a),
  -- and push the projection through the bind (`map_bind`).
  rw [← map_run_simulateQ_ghostNmaImpl_overlay_empty M maxAttempts sim pk sk (adv.main pk),
    bind_map_left]
  -- RHS: fold the unfolded handlers back to `nmaOuterImpl`/`nmaInnerImpl`, regroup the nested
  -- managed run by `managedRun_eq_link_run` into `linkRun`, then transport `linkRun`'s
  -- distribution back to the layered ghost run by sub-lemma (b).
  have hRHS :
      Pr[= true | (simulateQ (nmaInnerImpl M)
            ((simulateQ (nmaOuterImpl M maxAttempts sim pk) (adv.main pk)).run ∅)).run ∅ >>=
          fun a => RHSverify (a.1.1, (a.1.2, a.2))] =
        Pr[= true | (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) (adv.main pk)).run
            ((∅, ∅), []) >>= fun g => RHSverify (g.1, proj2 M g.2)] := by
    -- The ghost-side tail factors through `Prod.map id proj2`; the nested-side tail factors
    -- through `linkReshape`. Rewriting both tails as `RHSverify <$> (the projected head)` via
    -- `bind_map_left` lets sub-lemma (b) (`proj2 <$> ghostRun =𝒟 linkRun`) and the fusion
    -- (`linkRun = linkReshape <$> nested`) line the two heads up.
    have hproj2_empty : proj2 M (((∅ : (M × Commit →ₒ Chal).QueryCache),
        (∅ : (M × Commit →ₒ Chal).QueryCache)), ([] : List M)) = (∅, ∅) := by
      simp only [proj2, overlayCache_empty]
      exact congrArg (·, ∅) (baseEmbed_empty M)
    have hghost :
        (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) (adv.main pk)).run ((∅, ∅), []) >>=
            (fun g => RHSverify (g.1, proj2 M g.2)) =
          (Prod.map id (proj2 M) <$>
              (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) (adv.main pk)).run
                ((∅, ∅), [])) >>= RHSverify := by
      rw [bind_map_left]; rfl
    have hnested :
        (simulateQ (nmaInnerImpl M)
              ((simulateQ (nmaOuterImpl M maxAttempts sim pk) (adv.main pk)).run ∅)).run ∅ >>=
            (fun a => RHSverify (a.1.1, (a.1.2, a.2))) =
          ((QueryImpl.Stateful.Frame.prod (unifSpec + (M × Commit →ₒ Chal)).QueryCache
                ((M × Commit →ₒ Chal).QueryCache)).linkReshape (∅, ∅) <$>
              (simulateQ (nmaInnerImpl M)
                ((simulateQ (nmaOuterImpl M maxAttempts sim pk) (adv.main pk)).run ∅)).run ∅) >>=
            RHSverify := by
      rw [bind_map_left]; rfl
    rw [hghost, hnested]
    -- Reduce to the head-distribution equality, then bind with `RHSverify`.
    have hhead :
        𝒮[Prod.map id (proj2 M) <$>
            (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) (adv.main pk)).run ((∅, ∅), [])] =
          𝒮[(QueryImpl.Stateful.Frame.prod (unifSpec + (M × Commit →ₒ Chal)).QueryCache
                ((M × Commit →ₒ Chal).QueryCache)).linkReshape (∅, ∅) <$>
              (simulateQ (nmaInnerImpl M)
                ((simulateQ (nmaOuterImpl M maxAttempts sim pk) (adv.main pk)).run ∅)).run ∅] := by
      rw [evalSPMF_map_run_simulateQ_ghostNmaImpl_proj2 M maxAttempts sim
        pk sk (adv.main pk) ((∅, ∅), []), hproj2_empty,
        managedRun_eq_link_run ids hr M maxAttempts sim adv pk]
    refine OracleComp.probOutput_congr rfl ?_
    rw [evalSPMF_bind, evalSPMF_bind, hhead]
  -- Assemble: the goal RHS is `nestedManaged >>= K` (`= hRHS`'s LHS, defeq), so rewrite to the
  -- common ghost run, then `probOutput_bind_mono` against the pointwise verify-tail split, gated
  -- by the whole-run ghost-domain invariant.
  refine le_trans ?_ (le_of_eq hRHS.symm)
  refine probOutput_bind_mono fun a ha => ?_
  obtain ⟨av, ⟨base, ghost⟩, signed⟩ := a
  exact probOutput_hybridVerifyCont_le_managed_verify ids hr M maxAttempts pk av base ghost signed
    (fun q hq => ghostNmaImpl_run_signed_inv M maxAttempts sim pk sk (adv.main pk) _ ha q hq)

omit [SampleableType Stmt] in
/-- **Per-key cache-overlay invariant** (core of the NMA bridge): at a fixed key pair the
simulated single-cache hybrid (with the freshness check) is bounded by the run-normal-form
of the managed-RO NMA experiment — the managed-cache run of `simulatedNmaAdv` followed by
overlay verification, all under the runtime's `randomOracle` layer.

This is the genuine distributional content of `probOutput_hybridExp_sim_le_managedRoNmaExp`:
the inner managed cache threaded by `roSim`/`sigSim` together with the runtime's outer
`randomOracle` layer reproduces the single-cache hybrid run of `hybridExpAtKey`, and on
fresh forgeries the `withCacheOverlay` verification agrees with the live oracle at the
verification point (a cache invariant in the style of `fsAbortSignLoop_cache_invariant`:
every entry programmed by the signing simulation has its message recorded in the signed
list, so the freshness conjunct can only decrease the left-hand side). -/
lemma hybridExp_sim_le_managedRun_perKey
    (ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))
    (hro : ro = randomOracle) (pk : Stmt) (sk : Wit) :
    Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (simSignBody M maxAttempts sim pk sk) pk] ≤
      Pr[= true | (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
        ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pk >>= fun result =>
          withCacheOverlay result.2
            ((FiatShamirWithAbort ids hr M maxAttempts).verify
              pk result.1.1 result.1.2))).run' ∅] := by
  subst hro
  -- Put the hybrid LHS into run-normal-form (`run` of the hybrid handler on `adv.main pk`
  -- followed by the verify-and-freshness tail `hybridVerifyCont`).
  rw [hybridExpAtKey_eq_run_bind]
  -- Put the managed RHS into run-normal-form: `simulateQ_bind` distributes the outer RO
  -- simulation over the managed run and the overlay verification, and `StateT.run'`/`run`
  -- exposes the `(forgery, runtimeCache)` bind as a `ProbComp` bind whose final value is the
  -- forgery's verification bit (`pure p.1`).
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  exact hybridSimRun_le_managedRun_verify ids hr M maxAttempts sim adv pk sk

omit [SampleableType Stmt] in
/-- NMA bridge: the success probability of the simulated hybrid (averaged over key
generation, with the freshness check) is at most the success probability of
`simulatedNmaAdv` in the managed-RO NMA experiment.

Distributional content: (i) the single-cache-layer hybrid run coincides with the
managed-cache run of `simulatedNmaAdv` followed by overlay verification
(`withCacheOverlay`), and (ii) by a cache invariant in the style of
`fsAbortSignLoop_cache_invariant`, every entry programmed by the signing simulation has
its message recorded in the signed list, so on fresh forgeries the overlay agrees with
the live oracle at the verification point and the freshness conjunct can only decrease
the left-hand side. The matching hash-query-bound transfer is
`simulatedNmaAdv_nmaHashQueryBound` in `FiatShamir.WithAbort.Security`: the simulated signing
loop issues no live hash queries, so the NMA adversary keeps the CMA adversary's hash budget. -/
lemma probOutput_hybridExp_sim_le_managedRoNmaExp :
    Pr[= true | do
        let (pk, sk) ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (simSignBody M maxAttempts sim pk sk) pk] ≤
      Pr[= true | SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv)] := by
  classical
  -- Abbreviation for the runtime random-oracle simulator.
  set ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := randomOracle with hro
  -- Normal form of the managed-RO NMA experiment: the runtime's `withStateOracle`
  -- semantics unfolds to a single `simulateQ … |>.run' ∅`, and the lifted key
  -- generation pulls out as an ordinary `ProbComp` bind via `roSim.run'_liftM_bind`.
  have hRHS : Pr[= true | SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv)] =
      Pr[= true | hr.gen >>= fun pksk =>
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
          ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pksk.1 >>= fun result =>
            withCacheOverlay result.2
              ((FiatShamirWithAbort ids hr M maxAttempts).verify
                pksk.1 result.1.1 result.1.2))).run' ∅] := by
    unfold SignatureAlg.managedRoNmaExp
    -- Expose the bundled `withStateOracle` semantics as a run-normal-form ProbComp.
    change Pr[= true | 𝒮[(simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
        (do
          let (pk, _) ← (FiatShamirWithAbort ids hr M maxAttempts).keygen
          let result ← (simulatedNmaAdv ids hr M maxAttempts sim adv).main pk
          withCacheOverlay result.2
            ((FiatShamirWithAbort ids hr M maxAttempts).verify
              pk result.1.1 result.1.2))).run' ∅]] = _
    -- `keygen = monadLift hr.gen`; pull it out of the simulation.
    rw [show (FiatShamirWithAbort ids hr M maxAttempts).keygen =
      (liftM hr.gen : OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Stmt × Wit)) from rfl]
    rw [simulateQ_bind, roSim.run'_liftM_bind]
    rfl
  rw [hRHS]
  -- Reduce to a per-key statement under the shared `hr.gen` prefix.
  refine probOutput_bind_mono fun pksk _ => ?_
  -- Per-key core: the simulated hybrid (with the freshness check) is bounded by the
  -- managed-cache run of `simulatedNmaAdv` followed by overlay verification. This is the
  -- cache-overlay invariant: the inner managed cache `roSim` plus the runtime's outer
  -- `randomOracle` layer reproduces the single-cache hybrid, and on fresh forgeries the
  -- overlay agrees with the live oracle at the verification point.
  obtain ⟨pk, sk⟩ := pksk
  exact hybridExp_sim_le_managedRun_perKey ids hr M maxAttempts sim adv ro hro pk sk

end scaffold

end EUF_CMA

end FiatShamirWithAbort
