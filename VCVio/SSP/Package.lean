/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# State-Separating Proofs: Packages

A `Package I E σ` exposes an export oracle interface `E` while internally querying an import
interface `I`, maintaining private state of type `σ` set up by the monadic field
`init : OracleComp I σ`. The handler `impl` runs a single export query inside
`StateT σ (OracleComp I)`.

This is the basic data type for the SSP layer. It corresponds to SSProve's `package`, but using
VCVio's `OracleSpec` for interfaces, `OracleComp` as the underlying free monad, and a per-package
functional `StateT` instead of a shared heap. Disjointness of state between two parallel packages
is then a *structural* property of the product state `σ₁ × σ₂`.

Making `init` monadic is a *strict* generalization of SSProve's setup: SSProve has no `init`
field at all (per-location literal defaults on a shared heap; probabilistic setup is folded into
oracle handlers via lazy write-on-first-use). Allowing `init : OracleComp I σ` keeps the
one-time setup pattern first-class, at the cost of losing strict program equalities like
`P.run (pure x) = pure x` (the init's effects now execute on every run even when the adversary
is a pure value; see `run_pure` below).

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

Making `init` a `OracleComp I σ` (rather than a raw `σ`) constrains `σ` to live in the same
universe as `I.Range`, i.e. `σ : Type vᵢ`. Previously `σ` was free in `Type v`. For all current
use sites (and the SSP literature) this is harmless: `σ` and `I.Range` are typically both
`Type 0`, and the rest of the API still requires `σ : Type v`, so the practical constraint is
`σ : Type v` with `vᵢ = v`.
-/

universe uᵢ uₑ v

open OracleSpec OracleComp

namespace VCVio.SSP

/-- A *package* exposes the export interface `E` while internally querying the import interface
`I`, maintaining a private state of type `σ`.

The handler `impl` interprets each export query as a stateful `OracleComp I` computation. The
field `init : OracleComp I σ` produces the initial state; it may sample or query imports, so
probabilistic setup (e.g. sampling a long-term key once at start-of-game) is first-class data.

Universe parameters: the index universes `uᵢ, uₑ` for the import and export specs are
independent. The import range universe, the export range universe, and the state universe all
coincide at `v`, since `simulateQ` requires the handler to produce values of type
`StateT σ (OracleComp I) (E.Range x)` and `init` produces values of type `OracleComp I σ`. -/
structure Package {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    (I : OracleSpec.{uᵢ, v} ιᵢ) (E : OracleSpec.{uₑ, v} ιₑ) (σ : Type v) where
  /-- Initial value of the package's private state, as a (possibly probabilistic / query-using)
  computation in the import interface. -/
  init : OracleComp I σ
  /-- Implementation of each export query as a stateful `OracleComp I` computation. -/
  impl : QueryImpl E (StateT σ (OracleComp I))

namespace Package

variable {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
  {I : OracleSpec.{uᵢ, v} ιᵢ} {E : OracleSpec.{uₑ, v} ιₑ}
  {σ : Type v}

/-- The identity package on `E`: each export query is forwarded as the corresponding import
query, with no private state.

Marked `protected` to prevent this name from shadowing `_root_.id` inside `namespace Package`;
outside the namespace it is always written `Package.id`. -/
@[simps]
protected def id (E : OracleSpec.{uₑ, v} ιₑ) : Package E E PUnit.{v + 1} where
  init := pure PUnit.unit
  impl t :=
    (liftM (query t : OracleComp E (E.Range t)) : StateT PUnit.{v + 1} (OracleComp E) _)

/-- A purely stateless package built from a `QueryImpl E (OracleComp I)`. The internal state
is `PUnit` and the handler ignores it. -/
@[simps]
def ofStateless (h : QueryImpl E (OracleComp I)) : Package I E PUnit.{v + 1} where
  init := pure PUnit.unit
  impl := h.liftTarget (StateT PUnit.{v + 1} (OracleComp I))

/-- Run a package against an "adversary" computation `A` that queries the package's exports.

The result is an `OracleComp I` computation in the package's import interface. Most commonly
`I` is a sampling-only spec like `unifSpec`, in which case the result is a `ProbComp` (see
`VCVio.SSP.Advantage`). The package's final state is discarded; use `runState` to keep it.

Operationally: first run the init to obtain a starting state `s₀`, then simulate `A` through
the handler starting in state `s₀`. -/
def run {α : Type v} (P : Package I E σ) (A : OracleComp E α) : OracleComp I α :=
  P.init >>= fun s₀ => (simulateQ P.impl A).run' s₀

/-- Variant of `run` that keeps the package's final state. -/
def runState {α : Type v} (P : Package I E σ) (A : OracleComp E α) :
    OracleComp I (α × σ) :=
  P.init >>= fun s₀ => (simulateQ P.impl A).run s₀

@[simp]
lemma runState_ofStateless {α : Type v} (h : QueryImpl E (OracleComp I)) (A : OracleComp E α) :
    (Package.ofStateless h).runState A = (·, PUnit.unit) <$> simulateQ h A := by
  -- After the `pure PUnit.unit` init binds trivially, the claim reduces to a direct induction
  -- on `A`, identical in shape to the pre-monadic-init proof.
  unfold Package.runState
  simp only [ofStateless_init, pure_bind]
  -- Now the goal is
  --   (simulateQ (ofStateless h).impl A).run PUnit.unit = (·, PUnit.unit) <$> simulateQ h A
  induction A using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, ofStateless_impl,
      QueryImpl.liftTarget_apply, OracleQuery.input_query]
    have houter : (liftM ((liftM (h t)) : StateT PUnit.{v + 1} (OracleComp I) (E.Range t))
        : StateT PUnit.{v + 1} (OracleComp I) (E.Range t)) = liftM (h t) :=
      monadLift_self _
    rw [houter, StateT.run_monadLift]
    simp only [bind_assoc, pure_bind, map_bind]
    refine bind_congr fun u => ?_
    -- IH gives the result for `k u` after normalising `runState` with the trivial init bind.
    have hu : ((Package.ofStateless h).runState (k u)) = (·, PUnit.unit) <$> simulateQ h (k u) :=
      ih u
    simp only [Package.runState, ofStateless_init, pure_bind] at hu
    exact hu

@[simp]
lemma run_ofStateless {α : Type v} (h : QueryImpl E (OracleComp I)) (A : OracleComp E α) :
    (Package.ofStateless h).run A = simulateQ h A := by
  -- `run` factors through `runState` via `Prod.fst <$> _`.
  have : (Package.ofStateless h).run A
      = Prod.fst <$> (Package.ofStateless h).runState A := by
    simp [Package.run, Package.runState, StateT.run'_eq]
  rw [this, runState_ofStateless, ← Functor.map_map]
  simp

/-- Running a pure adversary still executes the package's init (which may sample). Both sides
evaluate to `P.init >>= fun _ => pure x`; under a probabilistic init interpretation such as
`evalDist`, this is still the distribution of `x`, so advantages are unaffected. -/
@[simp]
lemma run_pure {α : Type v} (P : Package I E σ) (x : α) :
    P.run (pure x) = P.init >>= fun _ => pure x := by
  simp [run, simulateQ_pure, StateT.run'_eq, StateT.run_pure]

/-- `runState` on a pure adversary returns `x` paired with the freshly-initialised state. -/
@[simp]
lemma runState_pure {α : Type v} (P : Package I E σ) (x : α) :
    P.runState (pure x) = (fun s₀ => (x, s₀)) <$> P.init := by
  simp [runState, simulateQ_pure, StateT.run_pure, bind_pure_comp]

@[simp]
lemma runState_bind {α β : Type v}
    (P : Package I E σ) (A : OracleComp E α) (f : α → OracleComp E β) :
    P.runState (A >>= f) =
      P.runState A >>= fun (a, s) => (simulateQ P.impl (f a)).run s := by
  simp [runState, simulateQ_bind, StateT.run_bind, bind_assoc]

end Package

/-! ### Universe-polymorphism sanity checks

The examples below exercise the three independent universe parameters of `Package`. They are
purely typechecking tests: they ensure that the import / export index universes (`uᵢ`, `uₑ`)
remain independent of each other and of the shared range / state universe `v`. -/

section UniverseTests

example {ιᵢ : Type uᵢ} {ιₑ : Type uₑ}
    (I : OracleSpec.{uᵢ, v} ιᵢ) (E : OracleSpec.{uₑ, v} ιₑ) (σ : Type v) :
    Type _ := Package I E σ

example {ιᵢ : Type 0} {ιₑ : Type 1}
    (I : OracleSpec.{0, 0} ιᵢ) (E : OracleSpec.{1, 0} ιₑ) (σ : Type) :
    Type _ := Package I E σ

end UniverseTests

end VCVio.SSP
