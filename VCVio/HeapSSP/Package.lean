/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Heap
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.SimSemantics.PreservesInv

/-!
# HeapSSP: Packages with heap-based state

A `Package I E Ident` exposes an export oracle interface `E` while internally
querying an import interface `I`, maintaining a private heap `Heap Ident` of
typed cells set up by the monadic field `init : OracleComp I (Heap Ident)`.
The handler `impl` runs a single export query inside
`StateT (Heap Ident) (OracleComp I)`.

This is the heap-based variant of `VCVio.SSP.Package`. The two frameworks
coexist for side-by-side comparison; see
`Notes/vcvio-fs-schnorr-clean-chain.md` §D.13 for the design rationale and
the migration plan.

## What changes vs `VCVio.SSP.Package`

* The state type goes from a free `σ : Type v` to a structured
  `Heap Ident : Type v` indexed by an identifier set `Ident : Type`.
* The trivial empty state (used by `Package.id`, `Package.ofStateless`)
  becomes `Heap PEmpty.{1}`, a singleton type, instead of `PUnit.{v + 1}`.
* The structural API (`run`, `runState`, `run_pure`, `runState_bind`, ...)
  is identical in shape; only the state type changes.

The crucial divergence is in `VCVio.HeapSSP.Composition`: composition of
identifier sets uses `Sum`, with `Heap.split` as the canonical reshape.
This is what the heap layer is *for*; the present file is just the basic
data type.

## Universe layout

`Ident` lives in `Type` (i.e. `Type 0`); concrete identifier types in the
intended use case are inductive types with finitely many constructors (one
per cell in a game), so the universe-0 restriction is not limiting in
practice and keeps universe inference simple.

The other parameters are independent: `uᵢ`, `uₑ` for the import / export
spec indices; `vᵢ` for the import range universe; and `v` for the export
range universe (which is also the universe of cell value types and of the
result type `α` of any computation run against the package). With
`Ident : Type` and `[CellSpec.{0, v} Ident]`, the heap `Heap Ident` lives
in `Type max 0 v = Type v`, matching the SSP state universe exactly. -/

universe uᵢ uₑ vᵢ v

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
    (I : OracleSpec.{uᵢ, vᵢ} ιᵢ) (E : OracleSpec.{uₑ, v} ιₑ)
    (Ident : Type) [CellSpec.{0, v} Ident] where
  /-- Initial value of the package's private heap, as a (possibly
  probabilistic / query-using) computation in the import interface. -/
  init : OracleComp I (Heap Ident)
  /-- Implementation of each export query as a stateful `OracleComp I`
  computation. -/
  impl : QueryImpl E (StateT (Heap Ident) (OracleComp I))

namespace Package

variable {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
  {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {E : OracleSpec.{uₑ, v} ιₑ}
  {Ident : Type} [CellSpec.{0, v} Ident]

/-- The identity package on `E`: each export query is forwarded as the
corresponding import query, with no private state.

The empty identifier set `PEmpty.{1}` is the unit of `Sum` on identifiers;
its heap `Heap PEmpty.{1}` is a singleton (the unique empty function). -/
@[simps]
protected def id (E : OracleSpec.{uₑ, v} ιₑ) : Package E E PEmpty.{1} where
  init := pure Heap.empty
  impl t :=
    (liftM (query t : OracleComp E (E.Range t))
      : StateT (Heap PEmpty.{1}) (OracleComp E) _)

/-- A purely stateless package built from a `QueryImpl E (OracleComp I)`.
The internal heap is `Heap PEmpty.{1}` (singleton) and the handler ignores
it. -/
@[simps]
def ofStateless (h : QueryImpl E (OracleComp I)) : Package I E PEmpty.{1} where
  init := pure Heap.empty
  impl := h.liftTarget (StateT (Heap PEmpty.{1}) (OracleComp I))

/-- Run a package against an "adversary" computation `A` that queries the
package's exports.

The result is an `OracleComp I` computation in the package's import
interface. The package's final heap is discarded; use `runState` to keep
it. -/
def run {α : Type v} (P : Package I E Ident) (A : OracleComp E α) :
    OracleComp I α :=
  P.init >>= fun h₀ => (simulateQ P.impl A).run' h₀

/-- Variant of `run` that keeps the package's final heap. -/
def runState {α : Type v} (P : Package I E Ident) (A : OracleComp E α) :
    OracleComp I (α × Heap Ident) :=
  P.init >>= fun h₀ => (simulateQ P.impl A).run h₀

@[simp]
lemma runState_ofStateless {α : Type v} (h : QueryImpl E (OracleComp I))
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
lemma run_ofStateless {α : Type v} (h : QueryImpl E (OracleComp I))
    (A : OracleComp E α) :
    (Package.ofStateless h).run A = simulateQ h A := by
  have : (Package.ofStateless h).run A
      = Prod.fst <$> (Package.ofStateless h).runState A := by
    simp [Package.run, Package.runState, StateT.run'_eq]
  rw [this, runState_ofStateless, ← Functor.map_map]
  simp

/-- Running a pure adversary still executes the package's init (which may
sample). Both sides evaluate to `P.init >>= fun _ => pure x`; under a
probabilistic init interpretation such as `evalDist`, this is still the
distribution of `x`, so advantages are unaffected. -/
@[simp]
lemma run_pure {α : Type v} (P : Package I E Ident) (x : α) :
    P.run (pure x) = P.init >>= fun _ => pure x := by
  simp [run, simulateQ_pure, StateT.run'_eq, StateT.run_pure]

/-- `runState` on a pure adversary returns `x` paired with the freshly-
initialised heap. -/
@[simp]
lemma runState_pure {α : Type v} (P : Package I E Ident) (x : α) :
    P.runState (pure x) = (fun h₀ => (x, h₀)) <$> P.init := by
  simp [runState, simulateQ_pure, StateT.run_pure, bind_pure_comp]

@[simp]
lemma runState_bind {α β : Type v}
    (P : Package I E Ident) (A : OracleComp E α) (f : α → OracleComp E β) :
    P.runState (A >>= f) =
      P.runState A >>= fun (a, h) => (simulateQ P.impl (f a)).run h := by
  simp [runState, simulateQ_bind, StateT.run_bind, bind_assoc]

@[simp]
lemma run_bind {α β : Type v}
    (P : Package I E Ident) (A : OracleComp E α) (f : α → OracleComp E β) :
    P.run (A >>= f) =
      P.runState A >>= fun (a, h) => (simulateQ P.impl (f a)).run' h := by
  simp [run, runState, simulateQ_bind, StateT.run_bind, bind_assoc]

/-! ### Support-level invariant preservation -/

/-- If every query handler step preserves a heap invariant `Inv`, then the
whole simulated computation preserves `Inv` on every reachable final heap. -/
theorem simulateQ_run_preservesInv
    {ιₑ' : Type} {E' : OracleSpec.{0, 0} ιₑ'}
    {Ident' : Type} [CellSpec.{0, 0} Ident'] {α : Type}
    (impl : QueryImpl E' (StateT (Heap Ident') ProbComp))
    (Inv : Heap Ident' → Prop)
    (hstep : ∀ (t : E'.Domain) (h : Heap Ident'), Inv h →
      ∀ z ∈ support ((impl t).run h), Inv z.2)
    (A : OracleComp E' α) (h : Heap Ident') (hinv : Inv h) :
    ∀ z ∈ support ((simulateQ impl A).run h), Inv z.2 := by
  intro z hz
  have himpl : QueryImpl.PreservesInv impl Inv := hstep
  exact OracleComp.simulateQ_run_preservesInv impl Inv
    (himpl := himpl) A h hinv z hz

/-- Cell-preservation specialization of `simulateQ_run_preservesInv`. If each
query step leaves cell `i` unchanged, then the full simulation leaves `i`
unchanged on every reachable final heap. -/
theorem simulateQ_run_preservesCell
    {ιₑ' : Type} {E' : OracleSpec.{0, 0} ιₑ'}
    {Ident' : Type} [CellSpec.{0, 0} Ident'] {α : Type}
    (impl : QueryImpl E' (StateT (Heap Ident') ProbComp))
    (i : Ident')
    (hstep : ∀ (t : E'.Domain) (h : Heap Ident'),
      ∀ z ∈ support ((impl t).run h), z.2.get i = h.get i)
    (A : OracleComp E' α) (h : Heap Ident') :
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
    {ιₑ' : Type} {E' : OracleSpec.{0, 0} ιₑ'}
    {Ident' : Type} [CellSpec.{0, 0} Ident'] {α : Type}
    (P : Package unifSpec E' Ident') (Inv : Heap Ident' → Prop)
    (hinit : ∀ h ∈ support P.init, Inv h)
    (hstep : ∀ (t : E'.Domain) (h : Heap Ident'), Inv h →
      ∀ z ∈ support ((P.impl t).run h), Inv z.2)
    (A : OracleComp E' α) :
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
    (I : OracleSpec.{uᵢ, vᵢ} ιᵢ) (E : OracleSpec.{uₑ, v} ιₑ)
    (Ident : Type) [CellSpec.{0, v} Ident] :
    Type _ := Package I E Ident

example {ιᵢ : Type 0} {ιₑ : Type 1}
    (I : OracleSpec.{0, 2} ιᵢ) (E : OracleSpec.{1, 0} ιₑ)
    (Ident : Type) [CellSpec.{0, 0} Ident] :
    Type _ := Package I E Ident

end UniverseTests

end VCVio.HeapSSP
