/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.StateT
import ToMathlib.PFunctor.Lens.State

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

/-- A stateful implementation of export queries `E` using import queries `I`.

`QueryImpl.Stateful I E σ` is the raw handler shape
`QueryImpl E (StateT σ (OracleComp I))`: each export query may inspect and
update private state `σ`, while making import queries in `I`.

The surrounding `QueryImpl.Stateful` namespace develops the state-separating
composition API for these handlers. Composition can use the canonical product
state, via `link` and `par`, or an explicit `Frame` that describes how two
component states are embedded as separated lawful state lenses inside a larger
state.
-/
def Stateful
    {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    (I : OracleSpec.{uᵢ, vᵢ} ιᵢ) (E : OracleSpec.{uₑ, v} ιₑ) (σ : Type v) :
    Type _ :=
  QueryImpl E (StateT σ (OracleComp I))

namespace Stateful

variable {ιᵢ : Type uᵢ} {ιₘ : Type uₘ} {ιₑ : Type uₑ}
  {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {M : OracleSpec.{uₘ, v} ιₘ} {E : OracleSpec.{uₑ, v} ιₑ}
  {σ σ₁ σ₂ σ' : Type v}

/-! ## State frames -/

/-- A frame specifying how two component states sit inside a larger state.

The component projections are state lenses in the sense of
`PFunctor.Lens.State`: each one has a getter and a putter satisfying the
standard very-well-behaved lens laws. The `separated` field says the two lenses
are non-interfering: each update leaves the other view unchanged, and the two
updates commute. Composition operators such as `linkWith` and `parSumWith` use
this explicit frame to run handlers over a larger state than the canonical
product state.
-/
structure Frame (σ σ₁ σ₂ : Type v) where
  /-- Lens selecting and updating the left component state. -/
  left : PFunctor.Lens.State σ σ₁
  /-- Lens selecting and updating the right component state. -/
  right : PFunctor.Lens.State σ σ₂
  /-- The left component lens satisfies `PutGet`, `GetPut`, and `PutPut`. -/
  [left_isVeryWellBehaved : PFunctor.Lens.State.IsVeryWellBehaved left]
  /-- The right component lens satisfies `PutGet`, `GetPut`, and `PutPut`. -/
  [right_isVeryWellBehaved : PFunctor.Lens.State.IsVeryWellBehaved right]
  /-- The two component lenses are non-interfering separated views of the source state. -/
  [separated : PFunctor.Lens.State.IsSeparated left right]

namespace Frame

/-- The canonical product-state frame. -/
def prod (σ₁ σ₂ : Type v) : Frame (σ₁ × σ₂) σ₁ σ₂ where
  left := PFunctor.Lens.State.fst σ₁ σ₂
  right := PFunctor.Lens.State.snd σ₁ σ₂

instance instLeftIsVeryWellBehaved (F : Frame σ σ₁ σ₂) :
    PFunctor.Lens.State.IsVeryWellBehaved F.left :=
  F.left_isVeryWellBehaved

instance instRightIsVeryWellBehaved (F : Frame σ σ₁ σ₂) :
    PFunctor.Lens.State.IsVeryWellBehaved F.right :=
  F.right_isVeryWellBehaved

instance instSeparated (F : Frame σ σ₁ σ₂) :
    PFunctor.Lens.State.IsSeparated F.left F.right :=
  F.separated

/-- Reshape the result of a linked handler run back into the source state
described by a frame.

The input carries an output value, the updated left component state, and the
updated right component state. The frame writes those component states back into
the original source state `s`.
-/
@[reducible]
def linkReshape {α : Type v} (F : Frame σ σ₁ σ₂) (s : σ) :
    (α × σ₁) × σ₂ → α × σ := fun p =>
  (p.1.1, F.right.put p.2 (F.left.put p.1.2 s))

end Frame

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

/-- Sequential composition of two stateful handlers using an explicit
state frame.

The frame specifies how the outer state `σ₁` and inner state `σ₂` are viewed
and updated inside the combined state `σ`. The linked handler reads both
component states from the source state, runs the usual nested simulation, then
writes back the updated outer and inner states through the frame lenses.
-/
def linkWith (F : Frame σ σ₁ σ₂)
    (outer : QueryImpl.Stateful M E σ₁) (inner : QueryImpl.Stateful I M σ₂) :
    QueryImpl.Stateful I E σ := fun t =>
  StateT.mk fun s =>
    F.linkReshape s <$>
      (simulateQ inner ((outer t).run (F.left.get s))).run (F.right.get s)

@[simp]
lemma linkWith_apply_run (F : Frame σ σ₁ σ₂)
    (outer : QueryImpl.Stateful M E σ₁) (inner : QueryImpl.Stateful I M σ₂)
    (t : E.Domain) (s : σ) :
    ((outer.linkWith F inner) t).run s =
      F.linkReshape s <$>
        (simulateQ inner ((outer t).run (F.left.get s))).run (F.right.get s) := rfl

/-- Sequential composition of two stateful handlers. The outer handler exports
`E` and imports `M`; the inner handler exports `M` and imports `I`. -/
def link (outer : QueryImpl.Stateful M E σ₁) (inner : QueryImpl.Stateful I M σ₂) :
    QueryImpl.Stateful I E (σ₁ × σ₂) :=
  outer.linkWith (Frame.prod σ₁ σ₂) inner

lemma link_impl_apply_run (outer : QueryImpl.Stateful M E σ₁)
    (inner : QueryImpl.Stateful I M σ₂) (t : E.Domain) (s₁ : σ₁) (s₂ : σ₂) :
    ((outer.link inner) t).run (s₁, s₂) =
      (Frame.prod σ₁ σ₂).linkReshape (s₁, s₂) <$>
        (simulateQ inner ((outer t).run s₁)).run s₂ := rfl

/-- Structural form of linked simulation through an explicit state frame. -/
theorem simulateQ_linkWith_run {α : Type v} (F : Frame σ σ₁ σ₂)
    (outer : QueryImpl.Stateful M E σ₁) (inner : QueryImpl.Stateful I M σ₂)
    (A : OracleComp E α) (s : σ) :
    (simulateQ (outer.linkWith F inner) A).run s =
      F.linkReshape s <$>
        (simulateQ inner ((simulateQ outer A).run (F.left.get s))).run (F.right.get s) := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure x =>
    change (pure (x, s) : OracleComp I (α × σ)) =
      F.linkReshape s <$>
        (simulateQ inner (pure (x, F.left.get s))).run (F.right.get s)
    rw [simulateQ_pure, StateT.run_pure, map_pure]
    simp [Frame.linkReshape, PFunctor.Lens.State.put_get]
  | query_bind t k ih =>
    have hLHS :
        (simulateQ (outer.linkWith F inner) (liftM (query t) >>= k)).run s =
          (simulateQ inner ((outer t).run (F.left.get s))).run (F.right.get s) >>=
            fun (p : (E.Range t × σ₁) × σ₂) =>
              (simulateQ (outer.linkWith F inner) (k p.1.1)).run
                (F.right.put p.2 (F.left.put p.1.2 s)) := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change ((outer.linkWith F inner t >>=
          fun a => simulateQ (outer.linkWith F inner) (k a)).run s) = _
      rw [StateT.run_bind, linkWith_apply_run, bind_map_left]
    have hRHS :
        (simulateQ inner
            ((simulateQ outer (liftM (query t) >>= k)).run (F.left.get s))).run
          (F.right.get s) =
          (simulateQ inner ((outer t).run (F.left.get s))).run (F.right.get s) >>=
            fun (p : (E.Range t × σ₁) × σ₂) =>
              (simulateQ inner ((simulateQ outer (k p.1.1)).run p.1.2)).run p.2 := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change (simulateQ inner
          ((outer t >>= fun a => simulateQ outer (k a)).run (F.left.get s))).run
        (F.right.get s) = _
      rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
    rw [hLHS, hRHS, map_bind]
    refine bind_congr fun p => ?_
    rw [ih p.1.1 (F.right.put p.2 (F.left.put p.1.2 s))]
    have hleft :
        F.left.get (F.right.put p.2 (F.left.put p.1.2 s)) = p.1.2 := by
      rw [PFunctor.Lens.State.left_get_put_right, PFunctor.Lens.State.get_put]
    have hright :
        F.right.get (F.right.put p.2 (F.left.put p.1.2 s)) = p.2 := by
      rw [PFunctor.Lens.State.get_put]
    have hreshape :
        (Frame.linkReshape (α := α) F (F.right.put p.2 (F.left.put p.1.2 s))) =
          Frame.linkReshape (α := α) F s := by
      funext z
      simp only [Frame.linkReshape]
      congr 1
      rw [PFunctor.Lens.State.put_comm (L := F.left) (R := F.right),
        PFunctor.Lens.State.put_put (L := F.left),
        PFunctor.Lens.State.put_put (L := F.right)]
    rw [hleft, hright, hreshape]

/-- Structural form of linked simulation as nested simulations. -/
theorem simulateQ_link_run {α : Type v}
    (outer : QueryImpl.Stateful M E σ₁) (inner : QueryImpl.Stateful I M σ₂)
    (A : OracleComp E α) (s₁ : σ₁) (s₂ : σ₂) :
    (simulateQ (outer.link inner) A).run (s₁, s₂) =
      (Frame.prod σ₁ σ₂).linkReshape (s₁, s₂) <$>
        (simulateQ inner ((simulateQ outer A).run s₁)).run s₂ := by
  exact simulateQ_linkWith_run (Frame.prod σ₁ σ₂) outer inner A (s₁, s₂)

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

/-- A typed routing of a named export interface into a binary parallel
composition.

Each external query is owned by exactly one component. The equivalence transports
between the external response type and the selected component response type. -/
structure BinaryRoute
    {ιₑ : Type uₑ} (E : OracleSpec.{uₑ, v} ιₑ)
    {ιₑ₁ : Type uₑ} (E₁ : OracleSpec.{uₑ, v} ιₑ₁)
    {ιₑ₂ : Type uₑ} (E₂ : OracleSpec.{uₑ, v} ιₑ₂) where
  route : (t : E.Domain) →
    (Σ t₁ : E₁.Domain, E.Range t ≃ E₁.Range t₁) ⊕
    (Σ t₂ : E₂.Domain, E.Range t ≃ E₂.Range t₂)

namespace BinaryRoute

/-- The canonical route for the sum of two export interfaces. -/
def sum : BinaryRoute (E₁ + E₂) E₁ E₂ where
  route
    | .inl t => .inl ⟨t, Equiv.refl _⟩
    | .inr t => .inr ⟨t, Equiv.refl _⟩

end BinaryRoute

/-- Parallel composition of two stateful handlers over a named export interface
using an explicit state frame and ambient import interface.

The frame specifies where each side's private state lives in the shared source
state. A left query updates only the left view, and a right query updates only
the right view. The frame's separation law records that these two updates are
non-interfering.
-/
def parRouteWith
    {ιᵢ : Type uᵢ} {I : OracleSpec.{uᵢ, v} ιᵢ} {ιₑ : Type uₑ}
    {E : OracleSpec.{uₑ, v} ιₑ} (F : Frame σ σ₁ σ₂)
    (R : BinaryRoute E E₁ E₂)
    [MonadLiftT (OracleQuery I₁) (OracleQuery I)]
    [MonadLiftT (OracleQuery I₂) (OracleQuery I)]
    (h₁ : QueryImpl.Stateful I₁ E₁ σ₁) (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) :
    QueryImpl.Stateful I E σ := fun t =>
  match R.route t with
  | .inl q => StateT.mk fun s =>
      (Prod.map q.2.symm fun s₁' => F.left.put s₁' s) <$>
        liftComp ((h₁ q.1).run (F.left.get s)) I
  | .inr q => StateT.mk fun s =>
      (Prod.map q.2.symm fun s₂' => F.right.put s₂' s) <$>
        liftComp ((h₂ q.1).run (F.right.get s)) I

/-- Parallel composition of two stateful handlers over a named export interface
and canonical product state. -/
def parRoute
    {ιᵢ : Type uᵢ} {I : OracleSpec.{uᵢ, v} ιᵢ} {ιₑ : Type uₑ}
    {E : OracleSpec.{uₑ, v} ιₑ} (R : BinaryRoute E E₁ E₂)
    [MonadLiftT (OracleQuery I₁) (OracleQuery I)]
    [MonadLiftT (OracleQuery I₂) (OracleQuery I)]
    (h₁ : QueryImpl.Stateful I₁ E₁ σ₁) (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) :
    QueryImpl.Stateful I E (σ₁ × σ₂) :=
  parRouteWith (Frame.prod σ₁ σ₂) R h₁ h₂

/-- Parallel composition of two stateful handlers using an explicit state
frame and ambient import interface. The export interface is the canonical sum. -/
def parWithImports
    {ιᵢ : Type uᵢ} {I : OracleSpec.{uᵢ, v} ιᵢ} (F : Frame σ σ₁ σ₂)
    [MonadLiftT (OracleQuery I₁) (OracleQuery I)]
    [MonadLiftT (OracleQuery I₂) (OracleQuery I)]
    (h₁ : QueryImpl.Stateful I₁ E₁ σ₁) (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) :
    QueryImpl.Stateful I (E₁ + E₂) σ :=
  parRouteWith F BinaryRoute.sum h₁ h₂

/-- Routed parallel composition over an ambient import interface whose two
component import embeddings are known to have disjoint query images. The
implementation is the same as `parRouteWith`; the extra hypothesis is available
to downstream proofs that need sum-like import separation. -/
def parRouteSeparatedWith
    {ιᵢ : Type uᵢ} {I : OracleSpec.{uᵢ, v} ιᵢ} {ιₑ : Type uₑ}
    {E : OracleSpec.{uₑ, v} ιₑ} (F : Frame σ σ₁ σ₂)
    (R : BinaryRoute E E₁ E₂) [I₁ ⊂ₒ I] [I₁ ˡ⊂ₒ I] [I₂ ⊂ₒ I] [I₂ ˡ⊂ₒ I]
    [OracleSpec.DisjointSubSpec I₁ I₂ I]
    (h₁ : QueryImpl.Stateful I₁ E₁ σ₁) (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) :
    QueryImpl.Stateful I E σ :=
  parRouteWith F R h₁ h₂

/-- Parallel composition of two stateful handlers using an explicit state
frame and disjoint sum import and export interfaces. -/
def parSumWith (F : Frame σ σ₁ σ₂)
    (h₁ : QueryImpl.Stateful I₁ E₁ σ₁) (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) :
    QueryImpl.Stateful (I₁ + I₂) (E₁ + E₂) σ
  | .inl t => StateT.mk fun s =>
      (Prod.map id fun s₁' => F.left.put s₁' s) <$>
        liftComp ((h₁ t).run (F.left.get s)) (I₁ + I₂)
  | .inr t => StateT.mk fun s =>
      (Prod.map id fun s₂' => F.right.put s₂' s) <$>
        liftComp ((h₂ t).run (F.right.get s)) (I₁ + I₂)

@[simp]
lemma parSumWith_apply_inl_run (F : Frame σ σ₁ σ₂)
    (h₁ : QueryImpl.Stateful I₁ E₁ σ₁) (h₂ : QueryImpl.Stateful I₂ E₂ σ₂)
    (t : E₁.Domain) (s : σ) :
    ((h₁.parSumWith F h₂) (Sum.inl t)).run s =
      (Prod.map id fun s₁' => F.left.put s₁' s) <$>
        liftComp ((h₁ t).run (F.left.get s)) (I₁ + I₂) := rfl

@[simp]
lemma parSumWith_apply_inr_run (F : Frame σ σ₁ σ₂)
    (h₁ : QueryImpl.Stateful I₁ E₁ σ₁) (h₂ : QueryImpl.Stateful I₂ E₂ σ₂)
    (t : E₂.Domain) (s : σ) :
    ((h₁.parSumWith F h₂) (Sum.inr t)).run s =
      (Prod.map id fun s₂' => F.right.put s₂' s) <$>
        liftComp ((h₂ t).run (F.right.get s)) (I₁ + I₂) := rfl

/-- Parallel composition of two stateful handlers over disjoint sum interfaces. -/
def parSum (h₁ : QueryImpl.Stateful I₁ E₁ σ₁) (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) :
    QueryImpl.Stateful (I₁ + I₂) (E₁ + E₂) (σ₁ × σ₂) :=
  h₁.parSumWith (Frame.prod σ₁ σ₂) h₂

@[simp]
lemma parSum_apply_inl_run (h₁ : QueryImpl.Stateful I₁ E₁ σ₁)
    (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) (t : E₁.Domain) (s₁ : σ₁) (s₂ : σ₂) :
    ((h₁.parSum h₂) (Sum.inl t)).run (s₁, s₂) =
      (Prod.map id (·, s₂)) <$> liftComp ((h₁ t).run s₁) (I₁ + I₂) := rfl

@[simp]
lemma parSum_apply_inr_run (h₁ : QueryImpl.Stateful I₁ E₁ σ₁)
    (h₂ : QueryImpl.Stateful I₂ E₂ σ₂) (t : E₂.Domain) (s₁ : σ₁) (s₂ : σ₂) :
    ((h₁.parSum h₂) (Sum.inr t)).run (s₁, s₂) =
      (Prod.map id (s₁, ·)) <$> liftComp ((h₂ t).run s₂) (I₁ + I₂) := rfl

end Stateful

end QueryImpl
