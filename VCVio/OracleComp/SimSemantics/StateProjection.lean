/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import VCVio.OracleComp.SimSemantics.StateT
import VCVio.OracleComp.ProbComp

/-!
# State-Projection Lemmas for `simulateQ`

This file collects the *equational* state-projection theorems for `simulateQ` over `StateT`-valued
query implementations. They are pure equalities on distributions, with no relational, coupling, or
TV-distance content, and so live at the `SimSemantics` layer alongside `StateT.lean` rather than in
`ProgramLogic`.

## Main results

- `OracleComp.map_run_simulateQ_eq_of_query_map_eq` (and its `_inv'` variant): if every oracle
  step of `impl₁` becomes the corresponding `impl₂` step after mapping the state by `proj`, then
  the full simulation does too.
- `OracleComp.run'_simulateQ_eq_of_query_map_eq` (and variants): the `run'` (output-only)
  projection corollaries.
- `QueryImpl.StateOrnament`: a package for the recurring pattern where one
  stateful handler refines another by carrying extra bookkeeping state.
- `QueryImpl.fixSndStateT` + `OracleComp.simulateQ_run_eq_of_snd_invariant`: support-based
  decomposition for product state spaces where one component is invariant.
- `QueryImpl.extendState` + `OracleComp.extendState_run_proj_eq`: auxiliary-state lift, the
  inverse direction of `fixSndStateT`.

## Layering

This file is below `ProgramLogic` and is depended on by both `ProgramLogic/Relational/SimulateQ`
(which proves the genuinely relational corollaries) and `OracleComp/QueryTracking/*` files that
need to project away bookkeeping state from cached / programmed / seeded oracles.
-/

universe u v

open OracleSpec

namespace OracleComp

variable {α : Type u}

/-! ## State-projection: all states -/

/-- State-projection transport for `simulateQ.run`.

If each oracle call under `impl₁` becomes the corresponding `impl₂` call after mapping the state
with `proj`, then the full simulated runs agree under the same projection. -/
theorem map_run_simulateQ_eq_of_query_map_eq
    {ι : Type u} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ m))
    (impl₂ : QueryImpl spec (StateT σ₂ m))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =
      (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      calc
        ((impl₁ t).run s >>= fun x =>
            Prod.map id proj <$> (simulateQ impl₁ (oa x.1)).run x.2)
            =
            ((impl₁ t).run s >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run (proj x.2)) := by
                  refine bind_congr fun x => ?_
                  simpa using ih x.1 x.2
        _ =
            ((Prod.map id proj <$> (impl₁ t).run s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  exact
                    (bind_map_left (m := m) (Prod.map id proj)
                      ((impl₁ t).run s)
                      (fun y => (simulateQ impl₂ (oa y.1)).run y.2)).symm
        _ =
            ((impl₂ t).run (proj s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  rw [hproj t s]

/-- `run'` projection corollary of `map_run_simulateQ_eq_of_query_map_eq`. -/
theorem run'_simulateQ_eq_of_query_map_eq
    {ι : Type u} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ m))
    (impl₂ : QueryImpl spec (StateT σ₂ m))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    (simulateQ impl₁ oa).run' s = (simulateQ impl₂ oa).run' (proj s) := by
  have hrun := map_run_simulateQ_eq_of_query_map_eq impl₁ impl₂ proj hproj oa s
  have hmap := congrArg (fun p => Prod.fst <$> p) hrun
  simpa [StateT.run'] using hmap

/-! ## State-projection: invariant-gated -/

/-- Invariant-gated state-projection theorem: if `proj` commutes with each oracle
step *under* a state invariant `inv` that is preserved by every step, then it
commutes with the full simulation starting from any state satisfying `inv`. This
is the natural strengthening of `map_run_simulateQ_eq_of_query_map_eq` for
projections that only agree on a reachable subset of states. -/
theorem map_run_simulateQ_eq_of_query_map_eq_inv'
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hinv : ∀ t s, inv s →
      ∀ y ∈ support (m := OracleComp spec') ((impl₁ t).run s), inv y.2)
    (hproj : ∀ t s, inv s →
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) (hs : inv s) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =
      (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      have hbind :
          (do
              let x ← (impl₁ t).run s
              Prod.map id proj <$> (simulateQ impl₁ (oa x.1)).run x.2 :
                OracleComp spec' (α × σ₂)) =
            (do
              let x ← (impl₁ t).run s
              (simulateQ impl₂ (oa x.1)).run (proj x.2)) :=
        bind_congr_of_forall_mem_support
          (mx := ((impl₁ t).run s : OracleComp spec' (spec.Range t × σ₁)))
          (fun x hx => ih x.1 x.2 (hinv t s hs x hx))
      calc
        ((impl₁ t).run s >>= fun x =>
            Prod.map id proj <$> (simulateQ impl₁ (oa x.1)).run x.2)
            =
            ((impl₁ t).run s >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run (proj x.2)) := hbind
        _ =
            ((Prod.map id proj <$> (impl₁ t).run s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  exact
                    (bind_map_left (m := OracleComp spec') (Prod.map id proj)
                      ((impl₁ t).run s)
                      (fun y => (simulateQ impl₂ (oa y.1)).run y.2)).symm
        _ =
            ((impl₂ t).run (proj s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  rw [hproj t s hs]

/-- Query-step invariant preservation lifts to any full simulation. This is the
support-preservation half of `map_run_simulateQ_eq_of_query_map_eq_inv'`,
exposed separately for projected continuations after a simulated prefix. -/
theorem simulateQ_run_preserves_inv_of_query
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ : Type _}
    (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (inv : σ → Prop)
    (hinv : ∀ t s, inv s →
      ∀ y ∈ support (m := OracleComp spec') ((impl t).run s), inv y.2)
    (oa : OracleComp spec α) (s : σ) (hs : inv s) :
    ∀ y ∈ support (m := OracleComp spec') ((simulateQ impl oa).run s), inv y.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
      intro y hy
      have hy' : y = (x, s) := by simpa using hy
      simpa [hy'] using hs
  | query_bind t oa ih =>
      intro y hy
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hy
      rcases (mem_support_bind_iff _ _ _).1 hy with ⟨x, hx, hyx⟩
      exact ih x.1 x.2 (hinv t s hs x hx) y hyx

/-- Invariant-gated state-projection theorem for a simulated prefix followed by
a stateful continuation. -/
theorem map_run_simulateQ_bind_eq_of_query_map_eq_inv'
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ : Type _} {β : Type u}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hinv : ∀ t s, inv s →
      ∀ y ∈ support (m := OracleComp spec') ((impl₁ t).run s), inv y.2)
    (hproj : ∀ t s, inv s →
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α)
    (k₁ : α → StateT σ₁ (OracleComp spec') β)
    (k₂ : α → StateT σ₂ (OracleComp spec') β)
    (hk : ∀ x s, inv s →
      Prod.map id proj <$> (k₁ x).run s = (k₂ x).run (proj s))
    (s : σ₁) (hs : inv s) :
    Prod.map id proj <$> ((simulateQ impl₁ oa >>= k₁).run s) =
      ((simulateQ impl₂ oa >>= k₂).run (proj s)) := by
  simp only [StateT.run_bind, map_bind]
  have hpres :=
    simulateQ_run_preserves_inv_of_query impl₁ inv hinv oa s hs
  have hcont :
      ((simulateQ impl₁ oa).run s >>= fun x =>
          Prod.map id proj <$> (k₁ x.1).run x.2) =
        ((simulateQ impl₁ oa).run s >>= fun x =>
          (k₂ x.1).run (proj x.2)) :=
    bind_congr_of_forall_mem_support
      (mx := ((simulateQ impl₁ oa).run s :
        OracleComp spec' (α × σ₁)))
      (fun x hx => hk x.1 x.2 (hpres x hx))
  calc
    ((simulateQ impl₁ oa).run s >>= fun x =>
        Prod.map id proj <$> (k₁ x.1).run x.2)
        =
        ((simulateQ impl₁ oa).run s >>= fun x =>
          (k₂ x.1).run (proj x.2)) := hcont
    _ =
        ((Prod.map id proj <$> (simulateQ impl₁ oa).run s) >>= fun x =>
          (k₂ x.1).run x.2) := by
              exact
                (bind_map_left (m := OracleComp spec') (Prod.map id proj)
                  ((simulateQ impl₁ oa).run s)
                  (fun y => (k₂ y.1).run y.2)).symm
    _ =
        ((simulateQ impl₂ oa).run (proj s) >>= fun x =>
          (k₂ x.1).run x.2) := by
              rw [map_run_simulateQ_eq_of_query_map_eq_inv'
                impl₁ impl₂ inv proj hinv hproj oa s hs]

/-- `run'` projection corollary of `map_run_simulateQ_eq_of_query_map_eq_inv'`. -/
theorem run'_simulateQ_eq_of_query_map_eq_inv'
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hinv : ∀ t s, inv s →
      ∀ y ∈ support (m := OracleComp spec') ((impl₁ t).run s), inv y.2)
    (hproj : ∀ t s, inv s →
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) (hs : inv s) :
    (simulateQ impl₁ oa).run' s = (simulateQ impl₂ oa).run' (proj s) := by
  have hrun :=
    map_run_simulateQ_eq_of_query_map_eq_inv' impl₁ impl₂ inv proj hinv hproj oa s hs
  have hmap := congrArg (fun p => Prod.fst <$> p) hrun
  simpa [StateT.run'] using hmap

end OracleComp

namespace QueryImpl

/-- A state ornament packages the data needed to project a decorated stateful
query implementation onto a base implementation.

The decorated implementation may carry extra bookkeeping state. The projection
only needs to commute with each query on states satisfying `inv`, and `inv` must
be preserved by each query step. -/
structure StateOrnament
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ τ : Type _}
    (decorated : QueryImpl spec (StateT σ (OracleComp spec')))
    (base : QueryImpl spec (StateT τ (OracleComp spec'))) where
  inv : σ → Prop
  proj : σ → τ
  preserves_inv :
    ∀ t s, inv s →
      ∀ y ∈ support (m := OracleComp spec') ((decorated t).run s), inv y.2
  project_step :
    ∀ t s, inv s →
      Prod.map id proj <$> (decorated t).run s = (base t).run (proj s)

namespace StateOrnament

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
variable {σ τ : Type _}
variable {decorated : QueryImpl spec (StateT σ (OracleComp spec'))}
variable {base : QueryImpl spec (StateT τ (OracleComp spec'))}

/-- A state ornament projects full simulations of the decorated implementation
onto simulations of the base implementation. -/
theorem run_eq {α : Type}
    (orn : StateOrnament decorated base)
    (oa : OracleComp spec α) (s : σ) (hs : orn.inv s) :
    Prod.map id orn.proj <$> (simulateQ decorated oa).run s =
      (simulateQ base oa).run (orn.proj s) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    decorated base orn.inv orn.proj
    (fun t s hs => orn.preserves_inv t s hs)
    (fun t s hs => orn.project_step t s hs)
    oa s hs

/-- Output-only corollary of `QueryImpl.StateOrnament.run_eq`. -/
theorem run'_eq {α : Type}
    (orn : StateOrnament decorated base)
    (oa : OracleComp spec α) (s : σ) (hs : orn.inv s) :
    (simulateQ decorated oa).run' s =
      (simulateQ base oa).run' (orn.proj s) := by
  have h := orn.run_eq oa s hs
  have hmap := congrArg (fun p => Prod.fst <$> p) h
  simpa [StateT.run'] using hmap

end StateOrnament

end QueryImpl

/-! ## Fixing one component of a product state -/

namespace QueryImpl

/-- Given a `StateT (σ × Q) ProbComp` query implementation, fix the second state component
at `q₀` and project to `StateT σ ProbComp`. -/
def fixSndStateT {ι : Type} {spec : OracleSpec ι} {σ Q : Type}
    (impl : QueryImpl spec (StateT (σ × Q) ProbComp)) (q₀ : Q) :
    QueryImpl spec (StateT σ ProbComp) :=
  fun t => StateT.mk fun s => Prod.map id Prod.fst <$> (impl t).run (s, q₀)

end QueryImpl

namespace OracleComp

variable {α : Type}

/-- If the Q-component of product state `(σ × Q)` is invariant under all oracle queries
starting from `q₀`, then the full `simulateQ` computation decomposes: running with `(s, q₀)`
produces the same result as running the projected implementation on `s` alone, with `q₀`
appended back.

This generalizes `map_run_simulateQ_eq_of_query_map_eq` from all-states commutativity to
support-based invariance. -/
theorem simulateQ_run_eq_of_snd_invariant
    {ι : Type} {spec : OracleSpec ι} {σ Q : Type}
    (impl : QueryImpl spec (StateT (σ × Q) ProbComp))
    (q₀ : Q)
    (h_inv : ∀ (t : spec.Domain) (s : σ) (x : _ × (σ × Q)),
      x ∈ support ((impl t).run (s, q₀)) → x.2.2 = q₀)
    (oa : OracleComp spec α) (s : σ) :
    (simulateQ impl oa).run (s, q₀) =
    (fun p => (p.1, (p.2, q₀))) <$> (simulateQ (QueryImpl.fixSndStateT impl q₀) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rw [map_bind]
    conv_rhs =>
      rw [show (QueryImpl.fixSndStateT impl q₀ t).run s =
        Prod.map id Prod.fst <$> (impl t).run (s, q₀) from rfl]
    rw [bind_map_left]
    refine OracleComp.bind_congr_of_forall_mem_support _ (fun ⟨u, s', q'⟩ hx => ?_)
    have hq : q' = q₀ := h_inv t s ⟨u, s', q'⟩ hx
    subst hq
    simp only [Prod.map, id]
    exact ih u s'

/-- `run'` projection corollary of `simulateQ_run_eq_of_snd_invariant`. -/
theorem simulateQ_run'_eq_of_snd_invariant
    {ι : Type} {spec : OracleSpec ι} {σ Q : Type}
    (impl : QueryImpl spec (StateT (σ × Q) ProbComp))
    (q₀ : Q)
    (h_inv : ∀ (t : spec.Domain) (s : σ) (x : _ × (σ × Q)),
      x ∈ support ((impl t).run (s, q₀)) → x.2.2 = q₀)
    (oa : OracleComp spec α) (s : σ) :
    (simulateQ impl oa).run' (s, q₀) =
    (simulateQ (QueryImpl.fixSndStateT impl q₀) oa).run' s := by
  have hrun := simulateQ_run_eq_of_snd_invariant impl q₀ h_inv oa s
  change Prod.fst <$> (simulateQ impl oa).run (s, q₀) =
    Prod.fst <$> (simulateQ (QueryImpl.fixSndStateT impl q₀) oa).run s
  rw [hrun, Functor.map_map]

end OracleComp

/-! ## Extending state with an auxiliary component -/

namespace QueryImpl

/-- Extend a stateful query implementation with an auxiliary state component `Q`.
The base implementation runs on the `σ` component. The auxiliary update may inspect the query
input, the pre-state, the produced output, the post-state, and the old auxiliary value.

Inverse direction of `QueryImpl.fixSndStateT`: `extendState` adds a passive auxiliary, while
`fixSndStateT` projects one away. Together they witness the universal property of the product
state space. -/
def extendState
    {ι : Type u} {spec : OracleSpec ι} {σ Q : Type u} {m : Type u → Type v} [Monad m]
    (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q) :
    QueryImpl spec (StateT (σ × Q) m) :=
  fun t => StateT.mk fun s => do
    let (u, s') ← (so t).run s.1
    pure (u, (s', aux t s.1 u s' s.2))

@[simp] lemma extendState_apply
    {ι : Type u} {spec : OracleSpec ι} {σ Q : Type u} {m : Type u → Type v} [Monad m]
    (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q)
    (t : spec.Domain) (s : σ × Q) :
    (extendState so aux t).run s =
      ((so t).run s.1 >>= fun p => pure (p.1, (p.2, aux t s.1 p.1 p.2 s.2))) := rfl

/-- Extend a stateful query implementation with an auxiliary component on the
left of the product state. This is the same construction as `extendState`, but
it matches handlers whose state is ordered as `(auxiliary, baseState)`. -/
def extendStateLeft
    {ι : Type u} {spec : OracleSpec ι} {σ Q : Type u} {m : Type u → Type v} [Monad m]
    (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q) :
    QueryImpl spec (StateT (Q × σ) m) :=
  fun t => StateT.mk fun s => do
    let (u, s') ← (so t).run s.2
    pure (u, (aux t s.2 u s' s.1, s'))

@[simp] lemma extendStateLeft_apply
    {ι : Type u} {spec : OracleSpec ι} {σ Q : Type u} {m : Type u → Type v} [Monad m]
    (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q)
    (t : spec.Domain) (s : Q × σ) :
    (extendStateLeft so aux t).run s =
      ((so t).run s.2 >>= fun p => pure (p.1, (aux t s.2 p.1 p.2 s.1, p.2))) := rfl

end QueryImpl

namespace OracleComp

variable {α : Type u}

/-- Forgetting the auxiliary `Q` component commutes with the full simulation.
Running `so.extendState aux` and projecting away the `Q` component agrees with running `so`
directly on the `σ` component, irrespective of the initial `Q` value or the auxiliary update.

This is the universal-property statement: the `Q` component is genuinely *passive* in the sense
that it does not influence the `σ`-side of the simulation. -/
theorem extendState_run_proj_eq
    {ι : Type u} {spec : OracleSpec ι} {σ Q : Type u}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q)
    (oa : OracleComp spec α) (s : σ) (q : Q) :
    Prod.map id Prod.fst <$> (simulateQ (QueryImpl.extendState so aux) oa).run (s, q) =
      (simulateQ so oa).run s := by
  refine map_run_simulateQ_eq_of_query_map_eq
    (impl₁ := QueryImpl.extendState so aux) (impl₂ := so)
    (proj := Prod.fst) ?_ oa (s, q)
  intro t ⟨s', q'⟩
  change Prod.map id Prod.fst <$>
      ((so t).run s' >>= fun p => pure (p.1, (p.2, aux t s' p.1 p.2 q'))) =
      (so t).run s'
  rw [map_bind]
  conv_rhs => rw [← bind_pure ((so t).run s')]
  refine bind_congr fun ⟨u, s''⟩ => ?_
  simp

/-- `run'` projection corollary of `extendState_run_proj_eq`: dropping both the auxiliary `Q`
and the `σ` state of the extended simulation gives the same output distribution as the base
simulation. -/
theorem extendState_run'_eq
    {ι : Type u} {spec : OracleSpec ι} {σ Q : Type u}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q)
    (oa : OracleComp spec α) (s : σ) (q : Q) :
    (simulateQ (QueryImpl.extendState so aux) oa).run' (s, q) =
      (simulateQ so oa).run' s := by
  have h := extendState_run_proj_eq so aux oa s q
  have hmap := congrArg (fun p => Prod.fst <$> p) h
  simpa [StateT.run'] using hmap

/-- Forgetting the left auxiliary `Q` component commutes with the full
simulation. This is the left-product analogue of `extendState_run_proj_eq`. -/
theorem extendStateLeft_run_proj_eq
    {ι : Type u} {spec : OracleSpec ι} {σ Q : Type u}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q)
    (oa : OracleComp spec α) (s : σ) (q : Q) :
    Prod.map id Prod.snd <$> (simulateQ (QueryImpl.extendStateLeft so aux) oa).run (q, s) =
      (simulateQ so oa).run s := by
  refine map_run_simulateQ_eq_of_query_map_eq
    (impl₁ := QueryImpl.extendStateLeft so aux) (impl₂ := so)
    (proj := Prod.snd) ?_ oa (q, s)
  intro t ⟨q', s'⟩
  change Prod.map id Prod.snd <$>
      ((so t).run s' >>= fun p => pure (p.1, (aux t s' p.1 p.2 q', p.2))) =
      (so t).run s'
  rw [map_bind]
  conv_rhs => rw [← bind_pure ((so t).run s')]
  refine bind_congr fun ⟨u, s''⟩ => ?_
  simp

/-- `run'` projection corollary of `extendStateLeft_run_proj_eq`. -/
theorem extendStateLeft_run'_eq
    {ι : Type u} {spec : OracleSpec ι} {σ Q : Type u}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Q → Q)
    (oa : OracleComp spec α) (s : σ) (q : Q) :
    (simulateQ (QueryImpl.extendStateLeft so aux) oa).run' (q, s) =
      (simulateQ so oa).run' s := by
  have h := extendStateLeft_run_proj_eq so aux oa s q
  have hmap := congrArg (fun p => Prod.fst <$> p) h
  simpa [StateT.run'] using hmap

end OracleComp
