/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
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

- `OracleComp.map_run_simulateQ_eq_of_query_map_eq` (and its `'`/`_inv'` variants): if every oracle
  step of `impl₁` becomes the corresponding `impl₂` step after mapping the state by `proj`, then
  the full simulation does too.
- `OracleComp.run'_simulateQ_eq_of_query_map_eq` (and variants): the `run'` (output-only)
  projection corollaries.
- `QueryImpl.fixSndStateT` + `OracleComp.simulateQ_run_eq_of_snd_invariant`: support-based
  decomposition for product state spaces where one component is invariant.
- `QueryImpl.extendState` + `OracleComp.extendState_run_proj_eq`: passive-auxiliary lift, the
  inverse direction of `fixSndStateT`.

## Layering

This file is below `ProgramLogic` and is depended on by both `ProgramLogic/Relational/SimulateQ`
(which proves the genuinely relational corollaries) and `OracleComp/QueryTracking/*` files that
need to project away bookkeeping state from cached / programmed / seeded oracles.
-/

universe u v

open OracleSpec

namespace OracleComp

variable {α : Type}

/-! ## State-projection: all states -/

/-- State-projection transport for `simulateQ.run`.

If each oracle call under `impl₁` becomes the corresponding `impl₂` call after mapping the state
with `proj`, then the full simulated runs agree under the same projection. -/
theorem map_run_simulateQ_eq_of_query_map_eq
    {ι : Type} {spec : OracleSpec ι}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
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
                    (bind_map_left (m := ProbComp) (Prod.map id proj)
                      ((impl₁ t).run s)
                      (fun y => (simulateQ impl₂ (oa y.1)).run y.2)).symm
        _ =
            ((impl₂ t).run (proj s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  rw [hproj t s]

/-- `run'` projection corollary of `map_run_simulateQ_eq_of_query_map_eq`. -/
theorem run'_simulateQ_eq_of_query_map_eq
    {ι : Type} {spec : OracleSpec ι}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    (simulateQ impl₁ oa).run' s = (simulateQ impl₂ oa).run' (proj s) := by
  have hrun := map_run_simulateQ_eq_of_query_map_eq impl₁ impl₂ proj hproj oa s
  have hmap := congrArg (fun p => Prod.fst <$> p) hrun
  simpa [StateT.run'] using hmap

/-- Generalized state-projection theorem: if applying `proj` to the state commutes with each
oracle step, then it commutes with the full simulation. Generalizes the `ProbComp` version
to any target spec. -/
theorem map_run_simulateQ_eq_of_query_map_eq'
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =
      (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
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
                    (bind_map_left (m := OracleComp spec') (Prod.map id proj)
                      ((impl₁ t).run s)
                      (fun y => (simulateQ impl₂ (oa y.1)).run y.2)).symm
        _ =
            ((impl₂ t).run (proj s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  rw [hproj t s]

/-- `run'` projection corollary of `map_run_simulateQ_eq_of_query_map_eq'`. -/
theorem run'_simulateQ_eq_of_query_map_eq'
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    (simulateQ impl₁ oa).run' s = (simulateQ impl₂ oa).run' (proj s) := by
  have hrun := map_run_simulateQ_eq_of_query_map_eq' impl₁ impl₂ proj hproj oa s
  have hmap := congrArg (fun p => Prod.fst <$> p) hrun
  simpa [StateT.run'] using hmap

/-! ## State-projection: invariant-gated -/

/-- Invariant-gated state-projection theorem: if `proj` commutes with each oracle
step *under* a state invariant `inv` that is preserved by every step, then it
commutes with the full simulation starting from any state satisfying `inv`. This
is the natural strengthening of `map_run_simulateQ_eq_of_query_map_eq'` for
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

/-! ## Extending state with a passive auxiliary -/

namespace QueryImpl

/-- Extend a stateful query implementation with an auxiliary state component `Q`.
The base impl runs on the `σ` component; `aux t u q` updates the auxiliary `Q` after each query
based on the input `t` and the produced output `u`.

Inverse direction of `QueryImpl.fixSndStateT`: `extendState` adds a passive auxiliary, while
`fixSndStateT` projects one away. Together they witness the universal property of the product
state space. -/
def extendState
    {ι : Type} {spec : OracleSpec ι} {σ Q : Type} {m : Type → Type _} [Monad m]
    (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → spec.Range t → Q → Q) :
    QueryImpl spec (StateT (σ × Q) m) :=
  fun t => StateT.mk fun s => do
    let (u, s') ← (so t).run s.1
    pure (u, (s', aux t u s.2))

@[simp] lemma extendState_apply
    {ι : Type} {spec : OracleSpec ι} {σ Q : Type} {m : Type → Type _} [Monad m]
    (so : QueryImpl spec (StateT σ m))
    (aux : (t : spec.Domain) → spec.Range t → Q → Q)
    (t : spec.Domain) (s : σ × Q) :
    (extendState so aux t).run s =
      ((so t).run s.1 >>= fun p => pure (p.1, (p.2, aux t p.1 s.2))) := rfl

end QueryImpl

namespace OracleComp

variable {α : Type}

/-- Forgetting the auxiliary `Q` component commutes with the full simulation: running
`so.extendState aux` and projecting away the `Q` component agrees with running `so` directly
on the `σ` component, irrespective of the initial `Q` value or the `aux` update rule.

This is the universal-property statement: the `Q` component is genuinely *passive* in the sense
that it does not influence the `σ`-side of the simulation. -/
theorem extendState_run_proj_eq
    {ι : Type} {spec : OracleSpec ι} {σ Q : Type}
    (so : QueryImpl spec (StateT σ ProbComp))
    (aux : (t : spec.Domain) → spec.Range t → Q → Q)
    (oa : OracleComp spec α) (s : σ) (q : Q) :
    Prod.map id Prod.fst <$> (simulateQ (QueryImpl.extendState so aux) oa).run (s, q) =
      (simulateQ so oa).run s := by
  refine map_run_simulateQ_eq_of_query_map_eq
    (impl₁ := QueryImpl.extendState so aux) (impl₂ := so)
    (proj := Prod.fst) ?_ oa (s, q)
  intro t ⟨s', q'⟩
  change Prod.map id Prod.fst <$>
      ((so t).run s' >>= fun p => pure (p.1, (p.2, aux t p.1 q'))) =
      (so t).run s'
  rw [map_bind]
  conv_rhs => rw [← bind_pure ((so t).run s')]
  refine bind_congr fun ⟨u, s''⟩ => ?_
  rfl

/-- `run'` projection corollary of `extendState_run_proj_eq`: dropping both the auxiliary `Q`
and the `σ` state of the extended simulation gives the same output distribution as the base
simulation. -/
theorem extendState_run'_eq
    {ι : Type} {spec : OracleSpec ι} {σ Q : Type}
    (so : QueryImpl spec (StateT σ ProbComp))
    (aux : (t : spec.Domain) → spec.Range t → Q → Q)
    (oa : OracleComp spec α) (s : σ) (q : Q) :
    (simulateQ (QueryImpl.extendState so aux) oa).run' (s, q) =
      (simulateQ so oa).run' s := by
  have h := extendState_run_proj_eq so aux oa s q
  have hmap := congrArg (fun p => Prod.fst <$> p) h
  simpa [StateT.run'] using hmap

end OracleComp
