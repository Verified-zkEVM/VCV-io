/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import ToMathlib.Control.Trace
public import ToMathlib.PFunctor.Chart.Basic

/-!
# Traces of polynomial-functor events

For a polynomial functor `P`, the universal "log of `P`-events" is the free
monoid on indices `Idx P = Σ a : P.A, P.B a`.  This file packages that monoid
together with the abstract `Control.Trace` machinery from
`ToMathlib/Control/Trace.lean`.

## Main definitions

* `PFunctor.TraceList P` — the carrier `FreeMonoid (Idx P)`,
  definitionally `List (Σ a, P.B a)`.
* `PFunctor.Trace P X` — the type of `X`-indexed `P`-event traces,
  i.e. `X → TraceList P`, with monoid structure inherited pointwise.
* `PFunctor.Trace.mapPartial`, `mapChart`,
  `restrictLeft`, `restrictRight` — the standard push / filter operations
  along chart morphisms and direct-sum projections.
* `PFunctor.Trace.toMonoid` — the universal property: every valuation
  `Idx P → ω` extends uniquely to a monoid hom `TraceList P →* ω`, and so to
  a trace map `Trace P X → Control.Trace ω X`.

## Boundary-emitter intuition

Reading `Trace P X` as "for each input `x : X`, the finite, ordered list of
`P`-events that get emitted on the boundary": this is precisely the boundary
shape of a stateless effectful Mealy machine in the `List`-Writer Kleisli
category.  Stateful executors (e.g. running over an `OracleComp`) are handled
separately in `VCVio/OracleComp/QueryTracking/`.

The canonical user inside this repository is `BoundaryAction.emit` in
`VCVio/Interaction/UC/OpenProcess.lean`, where `Trace Δ.Out X` records the
list of output-port packets a node emits when the local state transitions
to `x : X`. Operations such as `mapBoundary`, `wireLeft`, `wireRight`, and
the tensor embeddings of open processes are implemented directly by
`PFunctor.Trace.mapChart` and `PFunctor.Trace.mapPartial` against
appropriate boundary morphisms.


## References

* Bonchi, Di Lavore, Romàn — *Effectful Mealy machines and Kleisli
  categories*.
* Hancock, Setzer — *Interactive programs and weakly final coalgebras in
  dependent type theory*.
* Spivak, Niu — *Polynomial Functors: A Mathematical Theory of Interaction*,
  arXiv:2202.00534.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ v w

namespace PFunctor

/--
The free monoid on `P`-events.  Definitionally `FreeMonoid (Idx P)`, which
in turn is reducibly `List (Idx P)`.  This is the universal carrier for
"finite ordered logs of `P`-events".
-/
@[reducible] def TraceList (P : PFunctor.{uA, uB}) : Type max uA uB :=
  FreeMonoid (Idx P)

/--
An `X`-indexed trace of `P`-events: for each input `x : X`, a finite ordered
list of `P`-events.  Specialisation of `Control.Trace` at
`ω = TraceList P`, inheriting a pointwise monoid structure.
-/
@[reducible] def Trace (P : PFunctor.{uA, uB}) (X : Type v) : Type max uA uB v :=
  Control.Trace (TraceList P) X

namespace Trace

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
  {R : PFunctor.{uA₃, uB₃}} {X Y : Type v}

/--
Relabel-and-filter a trace along a partial map of indices.  This is the
single primitive for moving traces between polynomial functors: total chart
pushforward and summand restriction are both specialisations of it.
-/
def mapPartial (f : Idx P → Option (Idx Q)) (t : Trace P X) : Trace Q X :=
  fun x => List.filterMap f (t x)

/-- Push a `P`-trace forward along a chart `P → Q`. -/
def mapChart (φ : Chart P Q) : Trace P X → Trace Q X :=
  mapPartial (fun i => some (Chart.mapIdx φ i))

/-- Pre-compose a `P`-trace with `f : Y → X` (input variance). -/
def precomp (f : Y → X) (t : Trace P X) : Trace P Y := Control.Trace.precomp f t

/--
The universal map into any monoid-valued trace via the free-monoid universal
property.  Every valuation `φ : Idx P → ω` extends uniquely to a monoid
homomorphism `FreeMonoid (Idx P) →* ω`; `toMonoid φ` post-composes a `P`-trace
with that hom.
-/
def toMonoid {ω : Type w} [Monoid ω] (φ : Idx P → ω) :
    Trace P X → Control.Trace ω X :=
  Control.Trace.map (FreeMonoid.lift φ)

/-! ### Pointwise behaviour -/

@[simp] theorem mapPartial_apply (f : Idx P → Option (Idx Q)) (t : Trace P X)
    (x : X) :
    mapPartial f t x = List.filterMap f (t x) := rfl

@[simp] theorem mapChart_apply (φ : Chart P Q) (t : Trace P X) (x : X) :
    mapChart φ t x = (t x).filterMap (fun i => some (Chart.mapIdx φ i)) := rfl

@[simp] theorem toMonoid_apply {ω : Type w} [Monoid ω] (φ : Idx P → ω)
    (t : Trace P X) (x : X) :
    toMonoid φ t x = FreeMonoid.lift φ (t x) := rfl

/-! ### Functoriality of `mapPartial` and `mapChart` -/

@[simp] theorem mapPartial_some (t : Trace P X) :
    mapPartial (fun i => some i) t = t := by
  funext x
  exact List.filterMap_some

theorem mapPartial_comp (g : Idx Q → Option (Idx R))
    (f : Idx P → Option (Idx Q)) (t : Trace P X) :
    mapPartial g (mapPartial f t) = mapPartial (fun i => (f i).bind g) t := by
  funext x
  exact List.filterMap_filterMap

@[simp] theorem mapChart_id (t : Trace P X) : mapChart (Chart.id P) t = t := by
  change mapPartial (fun i => some (Chart.mapIdx (Chart.id P) i)) t = t
  exact mapPartial_some t

@[simp] theorem mapChart_comp (g : Chart Q R) (f : Chart P Q) (t : Trace P X) :
    mapChart (g ∘c f) t = mapChart g (mapChart f t) := by
  change mapPartial (fun i => some (Chart.mapIdx (g ∘c f) i)) t =
    mapPartial (fun i => some (Chart.mapIdx g i))
      (mapPartial (fun i => some (Chart.mapIdx f i)) t)
  rw [mapPartial_comp]
  rfl

/-! ### Trivial-trace lemmas

The unit trace `1 : Trace P X = fun _ => []` is annihilated by all relabel /
filter operations.  These are needed downstream to reason about
boundary actions whose default emission is the empty trace. -/

@[simp] theorem mapPartial_one (f : Idx P → Option (Idx Q)) :
    mapPartial f (1 : Trace P X) = 1 := rfl

@[simp] theorem mapChart_one (φ : Chart P Q) :
    mapChart φ (1 : Trace P X) = 1 := rfl

/-! ### Naturality of `toMonoid`

Pushing a `P`-trace along a chart `φ : P → Q` and then evaluating against a
`Q`-valuation `ψ` is the same as evaluating against the precomposed
`P`-valuation `ψ ∘ Chart.mapIdx φ`.  This is exactly the free-monoid
naturality square. -/

@[simp] theorem toMonoid_mapChart {ω : Type w} [Monoid ω] (ψ : Idx Q → ω)
    (φ : Chart P Q) (t : Trace P X) :
    toMonoid ψ (mapChart φ t) = toMonoid (ψ ∘ Chart.mapIdx φ) t := by
  funext x
  change FreeMonoid.lift ψ
      (FreeMonoid.ofList ((t x).filterMap (some ∘ Chart.mapIdx φ))) =
        FreeMonoid.lift (ψ ∘ Chart.mapIdx φ) (t x)
  rw [List.filterMap_eq_map (f := Chart.mapIdx φ),
    FreeMonoid.lift_ofList, FreeMonoid.lift_apply, List.map_map]
  rfl

end Trace

/-! ### Restriction along direct-sum projections

The summand restriction operations need `P` and `Q` to share the `B` universe
so that `P + Q` typechecks. -/

namespace Trace

variable {P Q : PFunctor.{uA, uB}} {X : Type v}

/-- Restrict a trace on `P + Q` to its `P`-summand. -/
def restrictLeft : Trace (P + Q) X → Trace P X :=
  mapPartial (fun i => match i with
    | ⟨Sum.inl a, b⟩ => some ⟨a, b⟩
    | ⟨Sum.inr _, _⟩ => none)

/-- Restrict a trace on `P + Q` to its `Q`-summand. -/
def restrictRight : Trace (P + Q) X → Trace Q X :=
  mapPartial (fun i => match i with
    | ⟨Sum.inl _, _⟩ => none
    | ⟨Sum.inr a, b⟩ => some ⟨a, b⟩)

end Trace

end PFunctor
