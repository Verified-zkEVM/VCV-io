/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.StateT

/-!
# State-Separating Proofs: Packages

A `Package I E σ` exposes an export oracle interface `E` while internally querying an import
interface `I`, maintaining private state of type `σ` initialized to `init`. The handler
`impl` runs a single export query inside `StateT σ (OracleComp I)`.

This is the basic data type for the SSP layer. It corresponds to SSProve's `package`, but using
VCVio's `OracleSpec` for interfaces, `OracleComp` as the underlying free monad, and a per-package
functional `StateT` instead of a shared heap. Disjointness of state between two parallel packages
is then a *structural* property of the product state `σ₁ × σ₂`.

The two basic operations live in this file:

* `Package.id` — identity package on `E`, with no internal state.
* `Package.run` — evaluate a closed package (with no imports) against an external "adversary"
  computation that queries the package's exports.

Composition of packages (sequential `link` and parallel `par`) and the bridge to probability
distributions live in sibling files `VCVio.SSP.Composition` and `VCVio.SSP.Advantage`.
-/

/-!
## Universe layout

A `Package I E σ` lets the indices `ιᵢ` and `ιₑ` of the import / export specs live in
*independent* universes (`uᵢ`, `uₑ`), and similarly the import / export ranges live in
independent universes (`vᵢ` for `I.Range`, `v` for `E.Range`). The state `σ` and the result
type `α` of any computation run against the package both live in `Type v` (i.e. the same
universe as the export ranges); this constraint is forced by `simulateQ` operating on
`StateT σ (OracleComp I) (E.Range x)`. The import range universe `vᵢ` is unconstrained: an
`OracleComp I` can produce values in `Type v` regardless of where `I.Range` lives.
-/

universe uᵢ uₑ vᵢ v

open OracleSpec OracleComp

namespace VCVio.SSP

/-- A *package* exposes the export interface `E` while internally querying the import interface
`I`, maintaining a private state of type `σ`.

The handler `impl` interprets each export query as a stateful `OracleComp I` computation. The
field `init` is the initial state.

Universe parameters: the index universes `uᵢ, uₑ` for the import and export specs are
independent, as are the range universes `vᵢ` (for `I`) and `v` (for `E`). The state `σ` lives
in the same universe `v` as the export ranges, since the handler must produce values of type
`StateT σ (OracleComp I) (E.Range x)`. -/
structure Package {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    (I : OracleSpec.{uᵢ, vᵢ} ιᵢ) (E : OracleSpec.{uₑ, v} ιₑ) (σ : Type v) where
  /-- Initial value of the package's private state. -/
  init : σ
  /-- Implementation of each export query as a stateful `OracleComp I` computation. -/
  impl : QueryImpl E (StateT σ (OracleComp I))

namespace Package

variable {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
  {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {E : OracleSpec.{uₑ, v} ιₑ}
  {σ : Type v}

/-- The identity package on `E`: each export query is forwarded as the corresponding import
query, with no private state. -/
@[simps]
def id (E : OracleSpec.{uₑ, v} ιₑ) : Package E E PUnit.{v + 1} where
  init := PUnit.unit
  impl t :=
    (liftM (query t : OracleComp E (E.Range t)) : StateT PUnit.{v + 1} (OracleComp E) _)

/-- A purely stateless package built from a `QueryImpl E (OracleComp I)`. The internal state
is `PUnit` and the handler ignores it. -/
@[simps]
def ofStateless (h : QueryImpl E (OracleComp I)) : Package I E PUnit.{v + 1} where
  init := PUnit.unit
  impl := h.liftTarget (StateT PUnit.{v + 1} (OracleComp I))

/-- Run a package against an "adversary" computation `A` that queries the package's exports.

The result is an `OracleComp I` computation in the package's import interface. Most commonly
`I` is a sampling-only spec like `unifSpec`, in which case the result is a `ProbComp` (see
`VCVio.SSP.Advantage`). The package's final state is discarded; use `runState` to keep it. -/
def run {α : Type v} (P : Package I E σ) (A : OracleComp E α) : OracleComp I α :=
  (simulateQ P.impl A).run' P.init

/-- Variant of `run` that keeps the package's final state. -/
def runState {α : Type v} (P : Package I E σ) (A : OracleComp E α) :
    OracleComp I (α × σ) :=
  (simulateQ P.impl A).run P.init

@[simp]
lemma runState_ofStateless {α : Type v} (h : QueryImpl E (OracleComp I)) (A : OracleComp E α) :
    (Package.ofStateless h).runState A = (·, PUnit.unit) <$> simulateQ h A := by
  unfold Package.runState
  generalize (Package.ofStateless h).init = s
  induction A using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, ofStateless_impl,
      QueryImpl.liftTarget_apply, OracleQuery.input_query]
    -- LHS contains `(liftM (liftM (h t))).run s`. The outer `liftM` is the StateT self-lift;
    -- collapse it, then unfold the remaining `(liftM x).run s` and clean up.
    have houter : (liftM ((liftM (h t)) : StateT PUnit.{v + 1} (OracleComp I) (E.Range t))
        : StateT PUnit.{v + 1} (OracleComp I) (E.Range t)) = liftM (h t) :=
      monadLift_self _
    rw [houter, StateT.run_monadLift]
    simp only [bind_assoc, pure_bind, map_bind]
    refine bind_congr fun u => ?_
    -- After this, the goal mentions `simulateQ` again; we need the IH for `k u`. Note that
    -- because the outer state is `PUnit`, we can drop the `s ↦ ...` quantification: the
    -- `pure (a, s)` we got back used `PUnit.unit`, which is the same as any other `s : PUnit`.
    have hu : ((Package.ofStateless h).runState (k u)) = (·, PUnit.unit) <$> simulateQ h (k u) :=
      ih u
    simp only [Package.runState] at hu
    -- `s : PUnit` is forced to `PUnit.unit`, matching `(Package.ofStateless h).init` used in `hu`.
    obtain rfl : s = PUnit.unit := Subsingleton.elim _ _
    exact hu

@[simp]
lemma run_ofStateless {α : Type v} (h : QueryImpl E (OracleComp I)) (A : OracleComp E α) :
    (Package.ofStateless h).run A = simulateQ h A := by
  rw [show (Package.ofStateless h).run A = Prod.fst <$> (Package.ofStateless h).runState A from
    rfl, runState_ofStateless, ← Functor.map_map]
  simp

@[simp]
lemma run_pure {α : Type v} (P : Package I E σ) (x : α) :
    P.run (pure x) = pure x := by
  simp [run, simulateQ_pure, StateT.run'_eq, StateT.run_pure]

@[simp]
lemma runState_pure {α : Type v} (P : Package I E σ) (x : α) :
    P.runState (pure x) = pure (x, P.init) := by
  simp [runState, simulateQ_pure, StateT.run_pure]

@[simp]
lemma runState_bind {α β : Type v}
    (P : Package I E σ) (A : OracleComp E α) (f : α → OracleComp E β) :
    P.runState (A >>= f) =
      P.runState A >>= fun (a, s) => (simulateQ P.impl (f a)).run s := by
  simp [runState, simulateQ_bind, StateT.run_bind]

end Package

/-! ### Universe-polymorphism sanity checks

The examples below exercise the four independent universe parameters of `Package`. They are
purely typechecking tests: they ensure that the import / export index universes (`uᵢ`, `uₑ`)
and the import / export range universes (`vᵢ`, `v`) all remain independent of each other. -/

section UniverseTests

example {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    (I : OracleSpec.{uᵢ, vᵢ} ιᵢ) (E : OracleSpec.{uₑ, v} ιₑ) (σ : Type v) :
    Type _ := Package I E σ

example {ιᵢ : Type 0} {ιₑ : Type 1}
    (I : OracleSpec.{0, 2} ιᵢ) (E : OracleSpec.{1, 0} ιₑ) (σ : Type) :
    Type _ := Package I E σ

end UniverseTests

end VCVio.SSP
