/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
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

## Companion bridge

`Chart.mapIdx` is added here as the small helper that lifts a polynomial
chart `P → Q` to a function `Idx P → Idx Q`.  It is the `Idx`-level avatar of
`PFunctor.Chart` and underlies `Trace.mapChart`.

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

namespace Chart

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
  {R : PFunctor.{uA₃, uB₃}}

/-- Push an `Idx P` along a chart `P → Q` to an `Idx Q`. -/
def mapIdx (φ : Chart P Q) (i : Idx P) : Idx Q :=
  ⟨φ.toFunA i.1, φ.toFunB i.1 i.2⟩

@[simp] theorem mapIdx_id (i : Idx P) : mapIdx (Chart.id P) i = i := rfl

@[simp] theorem mapIdx_comp (g : Chart Q R) (f : Chart P Q) (i : Idx P) :
    mapIdx (g ∘c f) i = mapIdx g (mapIdx f i) := rfl

end Chart

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
