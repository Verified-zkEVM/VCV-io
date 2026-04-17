/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Std.Tactic.Do
import VCVio.ProgramLogic.Unary.StdDoBridge
import VCVio.ProgramLogic.Unary.WriterTBridge
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.SeededOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# `Std.Do` handler specifications for `OracleComp` simulators

Connects the oracle-simulation handlers (`cachingOracle`, `seededOracle`,
`loggingOracle`) to `Std.Do`'s `Triple` / `mvcgen` framework via the
`instWPOracleComp` bridge in `StdDoBridge.lean`.

## Architecture

The bridge is two-layered:

* *Per-query (leaf) specs* are proven once. Modern handlers (`cachingOracle`,
  `loggingOracle`, `cachingLoggingOracle`) are written in `do` notation
  with `get` / `match` / `query` / `modify` / `tell`, and their `_triple`
  lemmas use `mvcgen` directly to walk the body. Each `query` step is
  bridged to a support-based statement via `wpProp_iff_forall_support`;
  this is the only point where the proof leaves pure `Std.Do.Triple`
  reasoning. Older handlers (`seededOracle`) are still proved via
  `triple_stateT_iff_forall_support` because their `StateT.mk`-style body
  doesn't reduce under `mvcgen`. Specs admitting a single canonical
  postcondition are `@[spec]`-tagged.
* *Composite (program-level) reasoning* is then done by `mvcgen`. Each
  example below ends with `mvcgen [handler_triple]` (optionally `<;> grind`)
  and the tactic walks the bind tree, instantiating the leaf spec at each
  occurrence and discharging side conditions. No per-program induction is
  required from the user.

`loggingOracle` is the original `WriterT (QueryLog spec) (OracleComp spec)`
implementation in `VCVio/OracleComp/QueryTracking/LoggingOracle.lean`.
The bridge `WriterTBridge.lean` interprets the writer log `ω = QueryLog spec`
as a state component of `Std.Do`'s `(.arg ω .pure)` post-shape, so the
`mvcgen` workflow for `WriterT` and `StateT` handlers is identical.

For whole-`simulateQ` results, the structural recursion on `OracleComp` is
isolated in the single helper `simulateQ_triple_preserves_invariant`. A
direct `Triple.bind`-based proof currently triggers a typeclass-search
timeout on `WPMonad (StateT σ (OracleComp spec)) (.arg σ .pure)`; the
helper bails out to support reasoning once and downstream consumers stay in
the `Std.Do` world. See `StdDoBridge.lean`'s architectural note for the
two `mvcgen`-side issues (spurious `MonadLift OracleComp OracleComp` and
`DiscrTree` `liftM`/`MonadLift.monadLift` mismatch) that prevent a fully
spec-driven leaf proof; both are worked around there with `@[spec]`
registrations, but the underlying `WPMonad` synthesis remains expensive.

## Main results

* `triple_stateT_iff_forall_support` - bridge lemma reducing `Std.Do.Triple`
  on `StateT σ (OracleComp spec)` to support-based reasoning.
* `simulateQ_triple_preserves_invariant` - generic invariant-preservation
  for `simulateQ`; lifts per-handler invariant triples to whole-program
  triples.
* `cachingOracle_triple`, `seededOracle_triple`, `seededOracle_triple_of_cons`,
  `seededOracle_triple_of_nil`, `loggingOracle_triple`,
  `loggingOracle_triple_prefix` - per-handler specifications
  consumable by `mvcgen`.
* `simulateQ_cachingOracle_preserves_cache_le` - worked whole-program
  example lifting `cachingOracle_triple`.

## Worked `mvcgen` examples

Each handler section ends with one or more `example` blocks demonstrating
that `mvcgen` actually closes goals composed from the per-query specs:
two-, three-, and four-query bind chains for caching; a no-fallthrough
chain for seeded; an in-order log-extension chain for logging; and prefix /
replacement chains for the replay fork in
`VCVio.CryptoFoundations.ReplayForkStdDo`.

## Stacked / multi-handler examples

The `stackedHandlers` section combines two state-tracking handlers into a
single `StateT (σ₁ × σ₂) (OracleComp spec)` layer. The worked example
`cachingLoggingOracle` simultaneously caches and logs every query; its
`@[spec]` lemma asserts both invariants together, and the generic
`simulateQ_triple_preserves_invariant` lifts each component invariant
(`cache₀ ≤ cache'` and `log₀ <+: log'`) to whole-program statements.

This single-`StateT`-layer pattern is preferred over genuinely stacked
`StateT`-over-`StateT` because:

* `mvcgen` and `Triple.bind` already struggle with one `StateT` layer over
  `OracleComp` (see the `WPMonad` timeout discussion above); two layers
  amplify the issue.
* The product-state representation matches the FiatShamir / forking
  proofs already in `VCVio/CryptoFoundations`, so there is a direct path
  from these examples to research-grade proofs.

## Related

The replay-fork handler `replayOracle` lives in
`VCVio.CryptoFoundations.ReplayFork`; its `Std.Do.Triple` specifications
are in `VCVio.CryptoFoundations.ReplayForkStdDo`.

## Limitations

* `simulateQ_triple_preserves_invariant` is still proved by induction on
  the support, not by `Triple.bind` / `Triple.pure`. Two roadblocks make
  the structural proof unaffordable today:
  - `WPMonad (StateT σ (OracleComp spec)) (.arg σ .pure)` instance
    synthesis times out on `isDefEq` (verified up to 1M heartbeats with
    several proof variations). The cost appears to be in
    `(wp x).mono` reduction inside `Triple.bind` for the
    `StateT σ (OracleComp spec)` instance.
  - The `mvcgen` `DiscrTree` only matches `liftM`-headed query terms
    after our `Spec.monadLift_query` workaround in `StdDoBridge.lean`;
    the pre-workaround failure mode silently dropped applicable specs
    rather than producing a clear error, which makes diagnosing
    mvcgen-side blockers expensive.

  Both are upstream `Std.Do` issues worth filing; the support fallback
  is a one-shot escape hatch and downstream consumers stay in the
  `Std.Do` world.
* `seededOracle`'s leaf specs (`seededOracle_triple`,
  `seededOracle_triple_of_cons`, `seededOracle_triple_of_nil`) still
  bail out to support-based reasoning. The `StateT.mk`-style definition
  branches on the seed list, and rewriting it in `do` notation conflicts
  with `MonadStateOf` instance resolution. Refactoring `seededOracle` to
  use `do` with `get` / `set` / `pure` would make it `mvcgen`-friendly,
  but is non-trivial given the existing dependents.
-/

open Std.Do OracleSpec OracleComp

set_option mvcgen.warning false

namespace OracleComp.ProgramLogic.StdDo

variable {ι : Type}
variable {spec : OracleSpec.{0, 0} ι} [spec.Fintype] [spec.Inhabited]

/-- Support characterization of `Std.Do.Triple` on `StateT σ (OracleComp spec)`.

A triple `⦃P⦄ mx ⦃Q⦄` holds iff every outcome `(a, s')` in the support of
`mx.run s` satisfies the postcondition `Q.1 a s'`, whenever the starting
state `s` satisfies the precondition `P`. -/
theorem triple_stateT_iff_forall_support {σ α : Type}
    (mx : StateT σ (OracleComp spec) α)
    (P : Assertion (.arg σ .pure)) (Q : PostCond α (.arg σ .pure)) :
    Std.Do.Triple mx P Q ↔
      ∀ s : σ, (P s).down →
        ∀ a s', (a, s') ∈ support (mx.run s) → (Q.1 a s').down := by
  classical
  rw [Triple.iff]
  simp only [SPred.entails_1]
  refine forall_congr' (fun s => ?_)
  refine imp_congr_right (fun _hP => ?_)
  -- Goal: (wp⟦mx⟧ Q s).down ↔ ∀ a s', (a, s') ∈ support (mx.run s) → (Q.1 a s').down
  change wpProp (spec := spec) (mx.run s) (fun p => (Q.1 p.1 p.2).down) ↔ _
  rw [wpProp_iff_forall_support]
  constructor
  · intro h a s' hmem; exact h (a, s') hmem
  · intro h p hmem; exact h p.1 p.2 hmem

/-! ## Generic invariant-preservation for `simulateQ` -/

/-- Generic simulation triple: if every handler call `handler t` preserves an
invariant `I` on the simulation state, then `simulateQ handler oa` preserves
`I` for any `oa : OracleComp spec α`.

The invariant-only form (same `I` as pre- and post-condition, independent of
return value) is the most common case; stronger per-call specs can be derived
by instantiating `I` appropriately or composing via `Triple.and`/`Triple.mp`. -/
theorem simulateQ_triple_preserves_invariant {σ α : Type}
    (handler : QueryImpl spec (StateT σ (OracleComp spec)))
    (I : σ → Prop)
    (hhandler : ∀ t : spec.Domain, Std.Do.Triple (handler t)
      (spred(fun s => ⌜I s⌝))
      (⇓ _ s' => ⌜I s'⌝))
    (oa : OracleComp spec α) :
    Std.Do.Triple
      (simulateQ handler oa : StateT σ (OracleComp spec) α)
      (spred(fun s => ⌜I s⌝))
      (⇓ _ s' => ⌜I s'⌝) := by
  -- A pure `Std.Do`-level proof via `Triple.pure` / `Triple.bind` is the
  -- structurally right thing, but consistently times out on `isDefEq` in
  -- the `query_bind` step (verified up to 1M heartbeats with several
  -- variations: explicit `R`, explicit `Q`, stripping `liftM` via
  -- `simulateQ_bind` + `simulateQ_query` + `id_map`). The cost appears to
  -- be in `(wp x).mono` reduction inside `Triple.bind` for the
  -- `StateT σ (OracleComp spec)` instance; this is plausibly a `Std.Do`
  -- upstream issue worth reporting.
  --
  -- For now, bail out once to the support layer and induct directly on
  -- `oa`. Downstream consumers stay in the `Std.Do` world.
  rw [triple_stateT_iff_forall_support]
  intro s hs a s' hmem
  revert s s' a
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s hs a s' hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨_, hseq⟩ := hmem
    exact hseq ▸ hs
  | query_bind t oa ih =>
    intro s hs a s' hmem
    simp only [simulateQ_query_bind, OracleQuery.input_query,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hmem
    obtain ⟨⟨u, s₁⟩, hmem₁, hmem₂⟩ := hmem
    have hhand := hhandler t
    rw [triple_stateT_iff_forall_support] at hhand
    have hI₁ : I s₁ := hhand s hs u s₁ hmem₁
    exact ih u s₁ hI₁ a s' hmem₂

/-- Specialized simulation triple: combine a starting-state precondition
`s = s₀` with an invariant that holds of `s₀`. The invariant is threaded
through the entire simulation. -/
theorem simulateQ_triple_of_state_and_invariant {σ α : Type}
    (handler : QueryImpl spec (StateT σ (OracleComp spec)))
    (I : σ → Prop)
    (hhandler : ∀ t : spec.Domain, Std.Do.Triple (handler t)
      (spred(fun s => ⌜I s⌝))
      (⇓ _ s' => ⌜I s'⌝))
    (oa : OracleComp spec α) (s₀ : σ) (hI : I s₀) :
    Std.Do.Triple
      (simulateQ handler oa : StateT σ (OracleComp spec) α)
      (spred(fun s => ⌜s = s₀⌝))
      (⇓ _ s' => ⌜I s'⌝) := by
  rw [triple_stateT_iff_forall_support]
  intro s hs a s' hmem
  rw [hs] at hmem
  have hbase := simulateQ_triple_preserves_invariant handler I hhandler oa
  rw [triple_stateT_iff_forall_support] at hbase
  exact hbase s₀ hI a s' hmem

section cachingOracle

variable [DecidableEq ι]

/-- Cache-monotonicity spec for `cachingOracle t` in `Std.Do.Triple` form.

If the cache on entry is `≥ cache₀`, then after a single call to
`cachingOracle t`, the updated cache is still `≥ cache₀` and, moreover,
contains the returned value at key `t`. -/
@[spec]
theorem cachingOracle_triple (t : spec.Domain) (cache₀ : QueryCache spec) :
    Std.Do.Triple
      (cachingOracle t : StateT (QueryCache spec) (OracleComp spec) (spec.Range t))
      (spred(fun cache => ⌜cache₀ ≤ cache⌝))
      (⇓ v cache' => ⌜cache₀ ≤ cache' ∧ cache' t = some v⌝) := by
  rw [show cachingOracle t =
        (do match (← get) t with
            | Option.some u => return u
            | Option.none =>
                let u ← (OracleComp.query t : OracleComp spec _)
                modifyGet (fun cache => (u, cache.cacheQuery t u)) :
          StateT (QueryCache spec) (OracleComp spec) (spec.Range t)) from rfl]
  mvcgen
  rename_i cache hle hnone
  rw [show (liftM (OracleQuery.query t) : OracleComp spec _) = OracleComp.query t from rfl,
      wpProp_iff_forall_support]
  intro u _
  mvcgen
  exact ⟨le_trans hle (QueryCache.le_cacheQuery cache hnone),
    QueryCache.cacheQuery_self cache t u⟩

/-- `mvcgen` example: two sequential `cachingOracle` queries preserve cache
monotonicity. `mvcgen` propagates the cache prefix through both binds; the
final transitivity step is closed by `grind`. -/
example (t₁ t₂ : spec.Domain) (cache₀ : QueryCache spec) :
    Std.Do.Triple
      (do let _ ← cachingOracle t₁; cachingOracle t₂ :
        StateT (QueryCache spec) (OracleComp spec) (spec.Range t₂))
      (spred(fun cache => ⌜cache₀ ≤ cache⌝))
      (⇓ v cache' => ⌜cache₀ ≤ cache' ∧ cache' t₂ = some v⌝) := by
  mvcgen [cachingOracle_triple]
  all_goals grind

/-- `mvcgen` example: a 4-query `cachingOracle` block preserves cache
monotonicity. Demonstrates that the chain length doesn't change the proof
shape: `mvcgen` walks the bind tree and `grind` closes the transitivity
chain. -/
example (t₁ t₂ t₃ t₄ : spec.Domain) (cache₀ : QueryCache spec) :
    Std.Do.Triple
      (do
        let _ ← cachingOracle t₁
        let _ ← cachingOracle t₂
        let _ ← cachingOracle t₃
        cachingOracle t₄ :
        StateT (QueryCache spec) (OracleComp spec) (spec.Range t₄))
      (spred(fun cache => ⌜cache₀ ≤ cache⌝))
      (⇓ v cache' => ⌜cache₀ ≤ cache' ∧ cache' t₄ = some v⌝) := by
  mvcgen [cachingOracle_triple]
  all_goals grind

/-- Global cache-monotonicity for `simulateQ cachingOracle`: an arbitrary
`OracleComp` simulated under caching never shrinks the cache. Derived via the
generic `simulateQ_triple_preserves_invariant`. -/
theorem simulateQ_cachingOracle_preserves_cache_le {α : Type}
    (cache₀ : QueryCache spec) (oa : OracleComp spec α) :
    Std.Do.Triple
      (simulateQ cachingOracle oa :
        StateT (QueryCache spec) (OracleComp spec) α)
      (spred(fun cache => ⌜cache₀ ≤ cache⌝))
      (⇓ _ cache' => ⌜cache₀ ≤ cache'⌝) := by
  refine simulateQ_triple_preserves_invariant cachingOracle (fun c => cache₀ ≤ c) ?_ oa
  intro t
  have := cachingOracle_triple t cache₀
  rw [triple_stateT_iff_forall_support] at this ⊢
  intro s hs a s' hmem
  exact (this s hs a s' hmem).1

end cachingOracle

section seededOracle

variable [DecidableEq ι]

/-- Specification for `seededOracle t` in `Std.Do.Triple` form.

The call consumes at most one value at index `t`: either the seed was empty at
`t` (state unchanged, returned value fresh) or the seed started with a value
`v` at `t` that is returned and popped from the state.

`seededOracle` is defined via `StateT.mk`, so we open the structure with
`triple_stateT_iff_forall_support` to bring the `match`-on-seed under
support reasoning, then close each branch directly. The other handlers
(`cachingOracle`, `loggingOracle`, `cachingLoggingOracle`) are defined in
`do`-notation form and admit pure `mvcgen` proofs; this one follows the
same pattern only after the `StateT.mk` is unfolded. -/
@[spec]
theorem seededOracle_triple (t : spec.Domain) (seed₀ : QuerySeed spec) :
    Std.Do.Triple
      (seededOracle t : StateT (QuerySeed spec) (OracleComp spec) (spec.Range t))
      (spred(fun seed => ⌜seed = seed₀⌝))
      (⇓ v seed' =>
        ⌜(seed₀ t = [] ∧ seed' = seed₀) ∨
         (∃ us, seed₀ t = v :: us ∧ seed' = Function.update seed₀ t us)⌝) := by
  rw [triple_stateT_iff_forall_support]
  intro seed hseed v seed' hmem
  rw [hseed] at hmem
  simp only [seededOracle.apply_eq, StateT.run, StateT.mk] at hmem
  cases hst : seed₀ t with
  | nil =>
    left
    rw [hst] at hmem
    simp only [support_map, support_query, Set.image_univ, Set.mem_range,
      Prod.mk.injEq] at hmem
    obtain ⟨_, _, hseed'⟩ := hmem
    exact ⟨rfl, hseed'.symm⟩
  | cons u us =>
    right
    rw [hst] at hmem
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨hv, hseed'⟩ := hmem
    subst hv
    exact ⟨us, rfl, hseed'⟩

/-- Specialized spec: if the seed has at least one value at `t`, `seededOracle t`
deterministically pops the head and updates the state. -/
theorem seededOracle_triple_of_cons (t : spec.Domain)
    (u : spec.Range t) (us : List (spec.Range t)) (seed₀ : QuerySeed spec)
    (h : seed₀ t = u :: us) :
    Std.Do.Triple
      (seededOracle t : StateT (QuerySeed spec) (OracleComp spec) (spec.Range t))
      (spred(fun seed => ⌜seed = seed₀⌝))
      (⇓ v seed' => ⌜v = u ∧ seed' = Function.update seed₀ t us⌝) := by
  rw [triple_stateT_iff_forall_support]
  intro seed hseed v seed' hmem
  rw [hseed] at hmem
  simp only [seededOracle.apply_eq, StateT.run, StateT.mk, h, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  exact ⟨hmem.1, hmem.2⟩

/-- Specialized spec: if the seed is empty at `t`, `seededOracle t` makes a live
query and leaves the state untouched. -/
theorem seededOracle_triple_of_nil (t : spec.Domain) (seed₀ : QuerySeed spec)
    (h : seed₀ t = []) :
    Std.Do.Triple
      (seededOracle t : StateT (QuerySeed spec) (OracleComp spec) (spec.Range t))
      (spred(fun seed => ⌜seed = seed₀⌝))
      (⇓ _ seed' => ⌜seed' = seed₀⌝) := by
  rw [triple_stateT_iff_forall_support]
  intro seed hseed v seed' hmem
  rw [hseed] at hmem
  simp only [seededOracle.apply_eq, StateT.run, StateT.mk, h, support_map,
    support_query, Set.image_univ, Set.mem_range, Prod.mk.injEq] at hmem
  obtain ⟨_, _, hseed'⟩ := hmem
  exact hseed'.symm

/-- `mvcgen` example: two consecutive `seededOracle` calls from an empty seed
both fall through to live queries, leaving the seed unchanged. The two
hypotheses on the seed are deposited as side conditions by `mvcgen`. -/
example (t₁ t₂ : spec.Domain) (seed₀ : QuerySeed spec)
    (h₁ : seed₀ t₁ = []) (h₂ : seed₀ t₂ = []) :
    Std.Do.Triple
      (do let _ ← seededOracle t₁; seededOracle t₂ :
        StateT (QuerySeed spec) (OracleComp spec) (spec.Range t₂))
      (spred(fun seed => ⌜seed = seed₀⌝))
      (⇓ _ seed' => ⌜seed' = seed₀⌝) := by
  mvcgen [seededOracle_triple_of_nil]
  all_goals grind

end seededOracle

section loggingOracle

/-- Spec for `loggingOracle t` over `WriterT (QueryLog spec) (OracleComp spec)`:
the writer log accumulates the query / response pair `⟨t, v⟩`. Proved purely
with `mvcgen` plus a single bridging step to bring the residual
`wpProp (liftM (query t))` goal to support form so the universally-quantified
obligation can be discharged by a second `mvcgen`.

Note: the writer log `ω = QueryLog spec` is interpreted by
`WriterTBridge.lean` as a state component (post-shape `(.arg ω .pure)`),
so the precondition / postcondition shape is identical to that of the
`StateT`-based reformulation. -/
@[spec]
theorem loggingOracle_triple (t : spec.Domain) (log₀ : QueryLog spec) :
    Std.Do.Triple
      (loggingOracle t :
        WriterT (QueryLog spec) (OracleComp spec) (spec.Range t))
      (spred(fun log => ⌜log = log₀⌝))
      (⇓ v log' => ⌜log' = log₀ ++ [⟨t, v⟩]⌝) := by
  unfold loggingOracle QueryImpl.withLogging QueryImpl.ofLift
  mvcgen
  rename_i s _ heq
  subst heq
  rw [show (liftM (OracleQuery.query t) : OracleComp spec _) = OracleComp.query t from rfl,
      wpProp_iff_forall_support]
  intro a _
  mvcgen

/-- Log-monotonicity corollary: the log only grows (as a list-prefix). Derived
directly from `loggingOracle_triple` via `mvcgen` (no support-layer escape). -/
theorem loggingOracle_triple_prefix (t : spec.Domain) (log₀ : QueryLog spec) :
    Std.Do.Triple
      (loggingOracle t :
        WriterT (QueryLog spec) (OracleComp spec) (spec.Range t))
      (spred(fun log => ⌜log = log₀⌝))
      (⇓ _ log' => ⌜log₀ <+: log'⌝) := by
  unfold loggingOracle QueryImpl.withLogging QueryImpl.ofLift
  mvcgen
  rename_i s _ heq
  subst heq
  rw [show (liftM (OracleQuery.query t) : OracleComp spec _) = OracleComp.query t from rfl,
      wpProp_iff_forall_support]
  intro a _
  mvcgen
  exact ⟨[⟨t, a⟩], rfl⟩

/-- `mvcgen` example: two consecutive logged queries extend the log with
both entries in order. The full proof is `mvcgen [loggingOracle_triple]`
plus a `grind` to close the trivial list-append side condition. -/
example (t₁ t₂ : spec.Domain) (log₀ : QueryLog spec) :
    Std.Do.Triple
      (do let u₁ ← loggingOracle t₁; let u₂ ← loggingOracle t₂; pure (u₁, u₂) :
        WriterT (QueryLog spec) (OracleComp spec) (spec.Range t₁ × spec.Range t₂))
      (spred(fun log => ⌜log = log₀⌝))
      (⇓ p log' => ⌜log' = log₀ ++ [⟨t₁, p.1⟩, ⟨t₂, p.2⟩]⌝) := by
  mvcgen [loggingOracle_triple]
  all_goals grind

end loggingOracle

/-! ## Stacked handlers

This section demonstrates the architecture's behavior under "stacked"
handlers, where the simulation state is itself a product of two
independent sub-states. The single-`StateT`-layer pattern (with
`σ := σ₁ × σ₂`) is the most ergonomic way to combine two state-tracking
handlers, because it stays inside the `(.arg σ .pure)` postcondition
shape that our `Std.Do` bridge supports cleanly.

The worked example is `cachingLoggingOracle`, which on every query both:
* logs the query/response pair into the right component, and
* caches the response in the left component (querying the underlying
  oracle only on a cache miss).

Each per-query specification is a *conjunction* of the cache invariant
(`cache₀ ≤ cache' ∧ cache' t = some v`) and the log invariant
(`log' = log₀ ++ [⟨t, v⟩]`). `mvcgen` walks composite chains the same
way as for the single-state handlers; only the leaf spec changes shape.

Whole-program lifting via `simulateQ_triple_preserves_invariant` works
unchanged: the invariant is now `I : (QueryCache spec × QueryLog spec) → Prop`,
typically a conjunction of one cache property and one log property. -/

section stackedHandlers

variable [spec.DecidableEq]

/-- A combined caching + logging handler over a product state.

Behavior on a query `t`:
* if the cache already has a value `v` at `t`, return `v`, leave the cache
  unchanged, and append `⟨t, v⟩` to the log;
* otherwise sample `v` from the underlying oracle, install `(t, v)` into
  the cache, and append `⟨t, v⟩` to the log.

The log always grows by exactly one entry per call; the cache grows by at
most one entry per call. Defined in `do`-notation form so that `mvcgen`
walks the body directly. -/
def cachingLoggingOracle :
    QueryImpl spec (StateT (QueryCache spec × QueryLog spec) (OracleComp spec)) :=
  fun t => do
    let s ← get
    match s.1 t with
    | some v =>
        modify (fun s => (s.1, s.2 ++ [⟨t, v⟩]))
        pure v
    | none =>
        let v ← (OracleComp.query t : OracleComp spec _)
        modify (fun s => (QueryCache.cacheQuery s.1 t v, s.2 ++ [⟨t, v⟩]))
        pure v

/-- Per-call spec for `cachingLoggingOracle t`: the log is extended by exactly
one entry `⟨t, v⟩`, the cache only grows, and the returned value is now
cached at `t`. Proved purely with `mvcgen` plus a single bridging step in
the cache-miss branch (where `liftM (query t)` needs to be brought to
`OracleComp.query` form so that the support-quantified obligation can be
discharged by a second `mvcgen`). -/
@[spec]
theorem cachingLoggingOracle_triple
    (t : spec.Domain) (cache₀ : QueryCache spec) (log₀ : QueryLog spec) :
    Std.Do.Triple
      (cachingLoggingOracle t :
        StateT (QueryCache spec × QueryLog spec) (OracleComp spec) (spec.Range t))
      (spred(fun s => ⌜cache₀ ≤ s.1 ∧ s.2 = log₀⌝))
      (⇓ v s' => ⌜cache₀ ≤ s'.1 ∧ s'.1 t = some v ∧ s'.2 = log₀ ++ [⟨t, v⟩]⌝) := by
  unfold cachingLoggingOracle
  mvcgen
  · -- some-branch: cache hit
    rename_i s hcond v hsome _t
    obtain ⟨hle, hlog⟩ := hcond
    change cache₀ ≤ s.1 ∧ s.1 t = some v ∧ s.2 ++ [⟨t, v⟩] = log₀ ++ [⟨t, v⟩]
    exact ⟨hle, hsome, by rw [hlog]⟩
  · -- none-branch: cache miss, falls through to query
    rename_i s hcond hnone
    obtain ⟨hle, hlog⟩ := hcond
    rw [show (liftM (OracleQuery.query t) : OracleComp spec _) = OracleComp.query t from rfl,
        wpProp_iff_forall_support]
    intro v _
    mvcgen
    change cache₀ ≤ s.1.cacheQuery t v ∧ (s.1.cacheQuery t v) t = some v ∧
      s.2 ++ [⟨t, v⟩] = log₀ ++ [⟨t, v⟩]
    exact ⟨le_trans hle (QueryCache.le_cacheQuery _ hnone),
      QueryCache.cacheQuery_self _ t v, by rw [hlog]⟩

/-- `mvcgen` example: two consecutive `cachingLoggingOracle` calls extend the
log with both query/response entries in order, while the cache continues to
grow monotonically. Composition is fully automatic; only a final `grind` is
needed for list-append associativity. -/
example (t₁ t₂ : spec.Domain)
    (cache₀ : QueryCache spec) (log₀ : QueryLog spec) :
    Std.Do.Triple
      (do
        let v₁ ← cachingLoggingOracle t₁
        let v₂ ← cachingLoggingOracle t₂
        pure (v₁, v₂) :
        StateT (QueryCache spec × QueryLog spec) (OracleComp spec)
          (spec.Range t₁ × spec.Range t₂))
      (spred(fun s => ⌜cache₀ ≤ s.1 ∧ s.2 = log₀⌝))
      (⇓ p s' =>
        ⌜cache₀ ≤ s'.1 ∧ s'.2 = log₀ ++ [⟨t₁, p.1⟩, ⟨t₂, p.2⟩]⌝) := by
  mvcgen [cachingLoggingOracle_triple]
  all_goals grind

/-- Whole-program lift: `simulateQ cachingLoggingOracle oa` preserves cache
monotonicity for any `oa`. Derived via the generic
`simulateQ_triple_preserves_invariant`. -/
theorem simulateQ_cachingLoggingOracle_preserves_cache_le {α : Type}
    (cache₀ : QueryCache spec) (oa : OracleComp spec α) :
    Std.Do.Triple
      (simulateQ cachingLoggingOracle oa :
        StateT (QueryCache spec × QueryLog spec) (OracleComp spec) α)
      (spred(fun s => ⌜cache₀ ≤ s.1⌝))
      (⇓ _ s' => ⌜cache₀ ≤ s'.1⌝) := by
  refine simulateQ_triple_preserves_invariant cachingLoggingOracle
    (fun s => cache₀ ≤ s.1) ?_ oa
  intro t
  rw [triple_stateT_iff_forall_support]
  intro s hs a s' hmem
  have hh := cachingLoggingOracle_triple t s.1 s.2
  rw [triple_stateT_iff_forall_support] at hh
  exact (hh s ⟨le_refl _, rfl⟩ a s' hmem).1.trans' hs

/-- Whole-program lift: `simulateQ cachingLoggingOracle oa` preserves the
log-prefix invariant (the log only grows). -/
theorem simulateQ_cachingLoggingOracle_preserves_log_prefix {α : Type}
    (log₀ : QueryLog spec) (oa : OracleComp spec α) :
    Std.Do.Triple
      (simulateQ cachingLoggingOracle oa :
        StateT (QueryCache spec × QueryLog spec) (OracleComp spec) α)
      (spred(fun s => ⌜log₀ <+: s.2⌝))
      (⇓ _ s' => ⌜log₀ <+: s'.2⌝) := by
  refine simulateQ_triple_preserves_invariant cachingLoggingOracle
    (fun s => log₀ <+: s.2) ?_ oa
  intro t
  rw [triple_stateT_iff_forall_support]
  rintro s ⟨k, hk⟩ v s' hmem
  have hh := cachingLoggingOracle_triple t s.1 s.2
  rw [triple_stateT_iff_forall_support] at hh
  have hpost := hh s ⟨le_refl _, rfl⟩ v s' hmem
  exact ⟨k ++ [⟨t, v⟩], by rw [hpost.2.2, ← hk, List.append_assoc]⟩

end stackedHandlers

end OracleComp.ProgramLogic.StdDo
