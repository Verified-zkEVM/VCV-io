/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.StateT

/-!
# Stateful query implementations

`QueryImpl.Stateful I E σ` is a thin abbreviation for handlers that implement
an export interface `E` by running `StateT σ (OracleComp I)`. It is the
unbundled stateful-handler layer used by state-separating proofs: the handler
and initial state are supplied separately instead of being bundled in a package
record.
-/

universe uᵢ uₘ uₑ vᵢ v

open OracleSpec OracleComp

open scoped OracleSpec.PrimitiveQuery

namespace QueryImpl

/-- A stateful implementation of export queries `E` using import queries `I`
and private state `σ`. -/
def Stateful
    {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    (I : OracleSpec.{uᵢ, vᵢ} ιᵢ) (E : OracleSpec.{uₑ, v} ιₑ) (σ : Type v) :
    Type _ :=
  QueryImpl E (StateT σ (OracleComp I))

namespace Stateful

variable {ιᵢ : Type uᵢ} {ιₘ : Type uₘ} {ιₑ : Type uₑ}
  {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {M : OracleSpec.{uₘ, v} ιₘ} {E : OracleSpec.{uₑ, v} ιₑ}
  {σ σ₁ σ₂ σ' : Type v}

/-! ## Basic handlers and evaluation -/

/-- The identity stateful handler forwards each query to the same interface,
threading a trivial state. -/
protected def id (E : OracleSpec.{uₑ, v} ιₑ) :
    QueryImpl.Stateful E E PUnit.{v + 1} :=
  (QueryImpl.id' E).liftTarget (StateT PUnit.{v + 1} (OracleComp E))

/-- Lift a stateless implementation into a stateful implementation with
trivial state. -/
def ofStateless (h : QueryImpl E (OracleComp I)) :
    QueryImpl.Stateful I E PUnit.{v + 1} :=
  h.liftTarget (StateT PUnit.{v + 1} (OracleComp I))

/-- Run a stateful handler from an explicit initial state, discarding the final
state. -/
def run {α : Type v} (h : QueryImpl.Stateful I E σ) (s₀ : σ) (A : OracleComp E α) :
    OracleComp I α :=
  (simulateQ h A).run' s₀

/-- Run a stateful handler from the default initial state, discarding the final
state. This is convenient for heap states, where `default = Heap.empty`, and
for product states assembled from default components. -/
def run₀ {α : Type v} [Inhabited σ] (h : QueryImpl.Stateful I E σ)
    (A : OracleComp E α) : OracleComp I α :=
  h.run default A

/-- Run a stateful handler from an explicit initial state, keeping the final
state. -/
def runState {α : Type v} (h : QueryImpl.Stateful I E σ) (s₀ : σ) (A : OracleComp E α) :
    OracleComp I (α × σ) :=
  (simulateQ h A).run s₀

/-- Run a stateful handler from the default initial state, keeping the final
state. -/
def runState₀ {α : Type v} [Inhabited σ] (h : QueryImpl.Stateful I E σ)
    (A : OracleComp E α) : OracleComp I (α × σ) :=
  h.runState default A

@[simp]
lemma runState_ofStateless {α : Type v} (h : QueryImpl E (OracleComp I))
    (A : OracleComp E α) :
    QueryImpl.Stateful.runState (ofStateless h) PUnit.unit A =
      (·, PUnit.unit) <$> simulateQ h A := by
  induction A using OracleComp.inductionOn with
  | pure x => simp [runState, simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [runState, simulateQ_query_bind, StateT.run_bind,
      OracleQuery.input_query]
    change
      (liftM (h t) : StateT PUnit.{v + 1} (OracleComp I) (E.Range t)).run PUnit.unit >>=
          (fun p => (simulateQ (ofStateless h) (k p.1)).run p.2) =
        (fun x => (x, PUnit.unit)) <$> (h t >>= fun u => simulateQ h (k u))
    rw [StateT.run_monadLift]
    simp only [bind_assoc, pure_bind, map_bind]
    refine bind_congr fun u => ?_
    exact ih u

@[simp]
lemma run_ofStateless {α : Type v} (h : QueryImpl E (OracleComp I)) (A : OracleComp E α) :
    QueryImpl.Stateful.run (ofStateless h) PUnit.unit A = simulateQ h A := by
  change (simulateQ (ofStateless h) A).run' PUnit.unit = simulateQ h A
  rw [StateT.run'_eq]
  have hrun := runState_ofStateless h A
  change (simulateQ (ofStateless h) A).run PUnit.unit =
    (fun x => (x, PUnit.unit)) <$> simulateQ h A at hrun
  rw [hrun, ← Functor.map_map]
  simp

@[simp]
lemma run_pure {α : Type v} (h : QueryImpl.Stateful I E σ) (s₀ : σ) (x : α) :
    h.run s₀ (pure x) = pure x := by
  simp [run, simulateQ_pure, StateT.run'_eq, StateT.run_pure]

@[simp]
lemma runState_pure {α : Type v} (h : QueryImpl.Stateful I E σ) (s₀ : σ) (x : α) :
    h.runState s₀ (pure x) = pure (x, s₀) := by
  simp [runState, simulateQ_pure, StateT.run_pure]

@[simp]
lemma runState_bind {α β : Type v}
    (h : QueryImpl.Stateful I E σ) (s₀ : σ) (A : OracleComp E α)
    (f : α → OracleComp E β) :
    h.runState s₀ (A >>= f) =
      h.runState s₀ A >>= fun (a, s) => (simulateQ h (f a)).run s := by
  simp [runState, simulateQ_bind, StateT.run_bind]

/-- Transport a stateful handler along a state equivalence. -/
def transportState (h : QueryImpl.Stateful I E σ) (φ : σ ≃ σ') :
    QueryImpl.Stateful I E σ' := fun t =>
  StateT.mk fun s' => Prod.map id φ <$> (h t).run (φ.symm s')

@[simp]
lemma transportState_apply_run (h : QueryImpl.Stateful I E σ) (φ : σ ≃ σ')
    (t : E.Domain) (s' : σ') :
    (h.transportState φ t).run s' = Prod.map id φ <$> (h t).run (φ.symm s') := rfl

/-! ## Sequential composition -/

/-- The product-state reshape used by linked handlers. -/
@[reducible]
def linkReshape {α : Type v} {σ₁ : Type v} {σ₂ : Type v} :
    (α × σ₁) × σ₂ → α × (σ₁ × σ₂) := fun p => (p.1.1, (p.1.2, p.2))

/-- Sequential composition of two stateful handlers. The outer handler exports
`E` and imports `M`; the inner handler exports `M` and imports `I`. -/
def link (outer : QueryImpl.Stateful M E σ₁) (inner : QueryImpl.Stateful I M σ₂) :
    QueryImpl.Stateful I E (σ₁ × σ₂) := fun t =>
  StateT.mk fun (s₁, s₂) =>
    linkReshape <$> (simulateQ inner ((outer t).run s₁)).run s₂

lemma link_impl_apply_run (outer : QueryImpl.Stateful M E σ₁)
    (inner : QueryImpl.Stateful I M σ₂) (t : E.Domain) (s₁ : σ₁) (s₂ : σ₂) :
    ((outer.link inner) t).run (s₁, s₂) =
      linkReshape <$> (simulateQ inner ((outer t).run s₁)).run s₂ := rfl

/-- Structural form of linked simulation as nested simulations. -/
theorem simulateQ_link_run {α : Type v}
    (outer : QueryImpl.Stateful M E σ₁) (inner : QueryImpl.Stateful I M σ₂)
    (A : OracleComp E α) (s₁ : σ₁) (s₂ : σ₂) :
    (simulateQ (outer.link inner) A).run (s₁, s₂) =
      linkReshape <$>
        (simulateQ inner ((simulateQ outer A).run s₁)).run s₂ := by
  induction A using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure x =>
    change (pure (x, (s₁, s₂)) : OracleComp I (α × (σ₁ × σ₂))) =
      linkReshape <$> (simulateQ inner (pure (x, s₁))).run s₂
    rw [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    have hLHS : (simulateQ (outer.link inner) (liftM (query t) >>= k)).run (s₁, s₂) =
        (simulateQ inner ((outer t).run s₁)).run s₂ >>=
          fun (p : (E.Range t × σ₁) × σ₂) =>
            (simulateQ (outer.link inner) (k p.1.1)).run (p.1.2, p.2) := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change ((outer.link inner t >>= fun a => simulateQ (outer.link inner) (k a)).run
        (s₁, s₂)) = _
      rw [StateT.run_bind, link_impl_apply_run, bind_map_left]
    have hRHS : (simulateQ inner ((simulateQ outer (liftM (query t) >>= k)).run s₁)).run s₂ =
        (simulateQ inner ((outer t).run s₁)).run s₂ >>=
          fun (p : (E.Range t × σ₁) × σ₂) =>
            (simulateQ inner ((simulateQ outer (k p.1.1)).run p.1.2)).run p.2 := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change (simulateQ inner ((outer t >>= fun a => simulateQ outer (k a)).run s₁)).run s₂ = _
      rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
    rw [hLHS, hRHS, map_bind]
    refine bind_congr fun p => ?_
    exact ih p.1.1 p.1.2 p.2

/-- Absorb a stateful outer handler and starting state into the client
computation. -/
def shiftLeft (outer : QueryImpl.Stateful M E σ₁) (s₀ : σ₁)
    {α : Type v} (A : OracleComp E α) : OracleComp M α :=
  outer.run s₀ A

@[simp]
lemma shiftLeft_pure (outer : QueryImpl.Stateful M E σ₁) (s₀ : σ₁) {α : Type v} (x : α) :
    outer.shiftLeft s₀ (pure x) = pure x := by
  simp [shiftLeft]

lemma shiftLeft_map (outer : QueryImpl.Stateful M E σ₁) (s₀ : σ₁)
    {α β : Type v} (f : α → β) (A : OracleComp E α) :
    outer.shiftLeft s₀ (f <$> A) = f <$> outer.shiftLeft s₀ A := by
  unfold shiftLeft run
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map]
  simp

/-- Program-level linked-game reduction with explicit initial states. -/
theorem run_link_eq_run_shiftLeft {α : Type v}
    (outer : QueryImpl.Stateful M E σ₁) (inner : QueryImpl.Stateful I M σ₂)
    (s₁ : σ₁) (s₂ : σ₂) (A : OracleComp E α) :
    (outer.link inner).run (s₁, s₂) A = inner.run s₂ (outer.shiftLeft s₁ A) := by
  unfold run shiftLeft
  rw [StateT.run'_eq, StateT.run'_eq, simulateQ_link_run]
  simp [run, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]

theorem run_link_left_ofStateless {α : Type v}
    (h : QueryImpl E (OracleComp M)) (inner : QueryImpl.Stateful I M σ₂)
    (s₂ : σ₂) (A : OracleComp E α) :
    ((ofStateless h).link inner).run (PUnit.unit, s₂) A = inner.run s₂ (simulateQ h A) := by
  rw [run_link_eq_run_shiftLeft]
  simp [shiftLeft]

@[simp]
theorem run_link_ofStateless {α : Type v}
    (hP : QueryImpl E (OracleComp M)) (hQ : QueryImpl M (OracleComp I))
    (A : OracleComp E α) :
    ((ofStateless hP).link (ofStateless hQ)).run (PUnit.unit, PUnit.unit) A =
      simulateQ hQ (simulateQ hP A) := by
  rw [run_link_left_ofStateless, run_ofStateless]

/-! ## Parallel composition -/

variable {ιᵢ₁ : Type uᵢ} {ιᵢ₂ : Type uᵢ} {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
  {I₁ : OracleSpec.{uᵢ, v} ιᵢ₁} {I₂ : OracleSpec.{uᵢ, v} ιᵢ₂}
  {E₁ : OracleSpec.{uₑ, v} ιₑ₁} {E₂ : OracleSpec.{uₑ, v} ιₑ₂}

/-- Parallel composition of two stateful handlers over disjoint sum interfaces. -/
def par (h₁ : QueryImpl.Stateful I₁ E₁ σ₁) (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) :
    QueryImpl.Stateful (I₁ + I₂) (E₁ + E₂) (σ₁ × σ₂)
  | .inl t => StateT.mk fun (s₁, s₂) =>
      (Prod.map id (·, s₂)) <$> liftComp ((h₁ t).run s₁) (I₁ + I₂)
  | .inr t => StateT.mk fun (s₁, s₂) =>
      (Prod.map id (s₁, ·)) <$> liftComp ((h₂ t).run s₂) (I₁ + I₂)

@[simp]
lemma par_apply_inl_run (h₁ : QueryImpl.Stateful I₁ E₁ σ₁)
    (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) (t : E₁.Domain) (s₁ : σ₁) (s₂ : σ₂) :
    ((h₁.par h₂) (Sum.inl t)).run (s₁, s₂) =
      (Prod.map id (·, s₂)) <$> liftComp ((h₁ t).run s₁) (I₁ + I₂) := rfl

@[simp]
lemma par_apply_inr_run (h₁ : QueryImpl.Stateful I₁ E₁ σ₁)
    (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) (t : E₂.Domain) (s₁ : σ₁) (s₂ : σ₂) :
    ((h₁.par h₂) (Sum.inr t)).run (s₁, s₂) =
      (Prod.map id (s₁, ·)) <$> liftComp ((h₂ t).run s₂) (I₁ + I₂) := rfl

end Stateful

end QueryImpl
