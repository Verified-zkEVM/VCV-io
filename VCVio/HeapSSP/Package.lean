/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ToMathlib.Data.Heap
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.SimSemantics.PreservesInv

/-!
# HeapSSP: Packages with heap-based state

A `Package I E Ident` exposes an export oracle interface `E` while internally
querying an import interface `I`, maintaining a private heap `Heap Ident` of
typed cells set up by the monadic field `init : OracleComp I (Heap Ident)`.
The handler `impl` runs a single export query inside
`StateT (Heap Ident) (OracleComp I)`.

Identifier sets are first-class: package composition combines them with `Sum`,
and `Heap.split` provides the canonical reshape between a composite heap and
its two component heaps. Stateless packages use the empty identifier set
`PEmpty`, whose heap is the unique empty function.

## Universe layout

The import and export index universes are independent. Identifier sets live in
`Type uₛ`, while cell values live in `Type v`; therefore `Heap Ident` lives in
`Type (max uₛ v)`. Since `StateT` uses the same universe for state and return
values, the export interface and interpreted computations live in that same
state universe. -/

universe uᵢ uₑ uₛ vᵢ v w

open OracleSpec OracleComp

namespace VCVio.HeapSSP

/-- A *heap-package* exposes the export interface `E` while internally
querying the import interface `I`, maintaining a private `Heap Ident` of
typed cells.

The handler `impl` interprets each export query as a stateful `OracleComp I`
computation. The field `init : OracleComp I (Heap Ident)` produces the
initial heap; it may sample or query imports, so probabilistic setup (e.g.
sampling a long-term key once at start-of-game and writing it to a cell)
is first-class data. -/
structure Package {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    (I : OracleSpec.{uᵢ, vᵢ} ιᵢ) (E : OracleSpec.{uₑ, max uₛ v} ιₑ)
    (Ident : Type uₛ) [CellSpec.{uₛ, v} Ident] where
  /-- Initial value of the package's private heap, as a (possibly
  probabilistic / query-using) computation in the import interface. -/
  init : OracleComp I (Heap Ident)
  /-- Implementation of each export query as a stateful `OracleComp I`
  computation. -/
  impl : QueryImpl E (StateT (Heap Ident) (OracleComp I))

namespace Package

variable {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
  {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {E : OracleSpec.{uₑ, max uₛ v} ιₑ}
  {Ident : Type uₛ} [CellSpec.{uₛ, v} Ident]

/-- The identity package on `E`: each export query is forwarded as the
corresponding import query, with no private state.

The empty identifier set `PEmpty.{1}` is the unit of `Sum` on identifiers;
its heap `Heap PEmpty.{1}` is a singleton (the unique empty function). -/
@[simps]
protected def id {ιₑ : Type uₑ} (E : OracleSpec.{uₑ, w} ιₑ) :
    Package E E PEmpty.{1} where
  init := pure Heap.empty
  impl t :=
    (liftM (query t : OracleComp E (E.Range t))
      : StateT (Heap PEmpty.{1}) (OracleComp E) _)

/-- A purely stateless package built from a `QueryImpl E (OracleComp I)`.
The internal heap is `Heap PEmpty.{1}` (singleton) and the handler ignores
it. -/
@[simps]
def ofStateless {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {E : OracleSpec.{uₑ, w} ιₑ}
    (h : QueryImpl E (OracleComp I)) : Package I E PEmpty.{1} where
  init := pure Heap.empty
  impl := h.liftTarget (StateT (Heap PEmpty.{1}) (OracleComp I))

/-- Run a package against a client computation `A` that queries the package's
exports.

The result is an `OracleComp I` computation in the package's import
interface. The package's final heap is discarded; use `runState` to keep
it. -/
def run {α : Type (max uₛ v)} (P : Package I E Ident) (A : OracleComp E α) :
    OracleComp I α :=
  P.init >>= fun h₀ => (simulateQ P.impl A).run' h₀

/-- Variant of `run` that keeps the package's final heap. -/
def runState {α : Type (max uₛ v)} (P : Package I E Ident) (A : OracleComp E α) :
    OracleComp I (α × Heap Ident) :=
  P.init >>= fun h₀ => (simulateQ P.impl A).run h₀

@[simp]
lemma runState_ofStateless {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {E : OracleSpec.{uₑ, w} ιₑ}
    {α : Type w} (h : QueryImpl E (OracleComp I))
    (A : OracleComp E α) :
    (Package.ofStateless h).runState A =
      (·, Heap.empty) <$> simulateQ h A := by
  unfold Package.runState
  simp only [ofStateless_init, pure_bind]
  induction A using OracleComp.inductionOn with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, ofStateless_impl,
      QueryImpl.liftTarget_apply, OracleQuery.input_query]
    have houter :
        (liftM ((liftM (h t)) : StateT (Heap PEmpty.{1}) (OracleComp I) (E.Range t))
          : StateT (Heap PEmpty.{1}) (OracleComp I) (E.Range t)) = liftM (h t) :=
      monadLift_self _
    rw [houter, StateT.run_monadLift]
    simp only [bind_assoc, pure_bind, map_bind]
    refine bind_congr fun u => ?_
    have hu : ((Package.ofStateless h).runState (k u))
        = (·, Heap.empty) <$> simulateQ h (k u) := ih u
    simp only [Package.runState, ofStateless_init, pure_bind] at hu
    exact hu

@[simp]
lemma run_ofStateless {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {E : OracleSpec.{uₑ, w} ιₑ}
    {α : Type w} (h : QueryImpl E (OracleComp I))
    (A : OracleComp E α) :
    (Package.ofStateless h).run A = simulateQ h A := by
  have : (Package.ofStateless h).run A
      = Prod.fst <$> (Package.ofStateless h).runState A := by
    simp [Package.run, Package.runState, StateT.run'_eq]
  rw [this, runState_ofStateless, ← Functor.map_map]
  simp

/-- Running a pure client computation still executes the package's init (which may
sample). Both sides evaluate to `P.init >>= fun _ => pure x`; under a
probabilistic init interpretation such as `evalDist`, this is still the
distribution of `x`, so advantages are unaffected. -/
@[simp]
lemma run_pure {α : Type (max uₛ v)} (P : Package I E Ident) (x : α) :
    P.run (pure x) = P.init >>= fun _ => pure x := by
  simp [run, simulateQ_pure, StateT.run'_eq, StateT.run_pure]

/-- `runState` on a pure client computation returns `x` paired with the freshly-
initialised heap. -/
@[simp]
lemma runState_pure {α : Type (max uₛ v)} (P : Package I E Ident) (x : α) :
    P.runState (pure x) = (fun h₀ => (x, h₀)) <$> P.init := by
  simp [runState, simulateQ_pure, StateT.run_pure, bind_pure_comp]

@[simp]
lemma runState_bind {α β : Type (max uₛ v)}
    (P : Package I E Ident) (A : OracleComp E α) (f : α → OracleComp E β) :
    P.runState (A >>= f) =
      P.runState A >>= fun (a, h) => (simulateQ P.impl (f a)).run h := by
  simp [runState, simulateQ_bind, StateT.run_bind, bind_assoc]

@[simp]
lemma run_bind {α β : Type (max uₛ v)}
    (P : Package I E Ident) (A : OracleComp E α) (f : α → OracleComp E β) :
    P.run (A >>= f) =
      P.runState A >>= fun (a, h) => (simulateQ P.impl (f a)).run' h := by
  simp [run, runState, simulateQ_bind, StateT.run_bind, bind_assoc]

/-! ### Support-level invariant preservation -/

/-- If every query handler step preserves a heap invariant `Inv`, then the
whole simulated computation preserves `Inv` on every reachable final heap. -/
theorem simulateQ_run_preservesInv
    {I' : OracleSpec.{uᵢ, max uₛ v} ιᵢ}
    {α : Type (max uₛ v)}
    (impl : QueryImpl E (StateT (Heap Ident) (OracleComp I')))
    (Inv : Heap Ident → Prop)
    (hstep : ∀ (t : E.Domain) (h : Heap Ident), Inv h →
      ∀ z ∈ support ((impl t).run h), Inv z.2)
    (A : OracleComp E α) (h : Heap Ident) (hinv : Inv h) :
    ∀ z ∈ support ((simulateQ impl A).run h), Inv z.2 := by
  revert h
  induction A using OracleComp.inductionOn with
  | pure a =>
      intro h hinv z hz
      have hz_eq : z = (a, h) := by
        simpa using (mem_support_pure_iff z (a, h)).1 hz
      simpa [hz_eq] using hinv
  | query_bind t oa ih =>
      intro h hinv z hz
      have hz' :
          z ∈ support
            (((simulateQ impl
                  (OracleSpec.query t : OracleComp E (E.Range t))).run h) >>=
              fun us => (simulateQ impl (oa us.1)).run us.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using hz
      rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
      have hq_run :
          (simulateQ impl (OracleSpec.query t : OracleComp E (E.Range t))).run h =
            (impl t).run h := by
        have hq :
            simulateQ impl (OracleSpec.query t : OracleComp E (E.Range t)) =
              impl t := by
          simp [OracleSpec.query_def, simulateQ_query]
        simp [hq]
      have hus' : us ∈ support ((impl t).run h) := by
        simpa [hq_run] using hus
      exact ih us.1 us.2 (hstep t h hinv us hus') z hzcont

/-- Cell-preservation specialization of `simulateQ_run_preservesInv`. If each
query step leaves cell `i` unchanged, then the full simulation leaves `i`
unchanged on every reachable final heap. -/
theorem simulateQ_run_preservesCell
    {I' : OracleSpec.{uᵢ, max uₛ v} ιᵢ}
    {α : Type (max uₛ v)}
    (impl : QueryImpl E (StateT (Heap Ident) (OracleComp I')))
    (i : Ident)
    (hstep : ∀ (t : E.Domain) (h : Heap Ident),
      ∀ z ∈ support ((impl t).run h), z.2.get i = h.get i)
    (A : OracleComp E α) (h : Heap Ident) :
    ∀ z ∈ support ((simulateQ impl A).run h), z.2.get i = h.get i := by
  intro z hz
  have hpres :=
    simulateQ_run_preservesInv impl (fun h' => h'.get i = h.get i)
      (fun t h' hinv z hz => by
        exact (hstep t h' z hz).trans hinv) A h rfl
  exact hpres z hz

/-- Package-level invariant preservation on `runState`: if the init support
lies in `Inv` and each handler step preserves `Inv`, then every reachable
final heap of `runState` satisfies `Inv`. -/
theorem runState_preservesInv
    {I' : OracleSpec.{uᵢ, max uₛ v} ιᵢ}
    {α : Type (max uₛ v)}
    (P : Package I' E Ident) (Inv : Heap Ident → Prop)
    (hinit : ∀ h ∈ support P.init, Inv h)
    (hstep : ∀ (t : E.Domain) (h : Heap Ident), Inv h →
      ∀ z ∈ support ((P.impl t).run h), Inv z.2)
    (A : OracleComp E α) :
    ∀ z ∈ support (P.runState A), Inv z.2 := by
  intro z hz
  unfold Package.runState at hz
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hz
  obtain ⟨h₀, hh₀, hz⟩ := hz
  exact simulateQ_run_preservesInv P.impl Inv hstep A h₀ (hinit h₀ hh₀) z hz

end Package

/-! ### Universe-polymorphism sanity checks

The examples below exercise the universe parameters of `Package`. They are
purely typechecking tests: they ensure that the import / export index
universes (`uᵢ`, `uₑ`), the import range universe `vᵢ`, and the shared
export-range / cell-value universe `v` all remain independent. -/

section UniverseTests

example {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    (I : OracleSpec.{uᵢ, vᵢ} ιᵢ) (E : OracleSpec.{uₑ, max uₛ v} ιₑ)
    (Ident : Type uₛ) [CellSpec.{uₛ, v} Ident] :
    Type _ := Package I E Ident

example {ιᵢ : Type 0} {ιₑ : Type 1} {Ident : Type 1}
    (I : OracleSpec.{0, 2} ιᵢ) (E : OracleSpec.{1, 1} ιₑ)
    [CellSpec.{1, 0} Ident] :
    Type _ := Package I E Ident

end UniverseTests

end VCVio.HeapSSP
