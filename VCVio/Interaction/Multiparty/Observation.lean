/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

/-!
# Observations: the information lattice of a single move

This file defines `Multiparty.Observation X`, the **maximally general
single-projection form** of a local view at a node whose move space is `X`,
together with its information-lattice algebra.

`Observation X = Σ Obs : Type u, X → Obs` is one quotient morphism `X → Obs`
packaged with its codomain. Three independent literature traditions converge
on this exact object:

* Halpern-Vardi epistemic logic ("Reasoning About Knowledge"): an agent's
  observation is a projection from global state to local indistinguishability
  classes;
* Goguen-Meseguer noninterference / Sabelfeld-Myers info-flow: per-level
  projection of observable outputs;
* Honda-Yoshida-Carbone multiparty session types and Cruz-Filipe-Montesi
  endpoint projection: projection of a global type / global play to one
  role's local view.

## Polynomial substrate

`Observation` is built directly on top of the polynomial-functor library
in `ToMathlib/PFunctor`, mirroring the pattern by which
`Interaction.Spec` is built from `Spec.basePFunctor`:

```
Observation X := PFunctor.Idx (Observation.basePFunctor X)
```

where `Observation.basePFunctor X : PFunctor.{u+1, u}` has positions
`Type u` (one position per observation codomain) and a child family
`Obs ↦ X → Obs` (the projections from `X` into that codomain). Thus an
observation of `X` is precisely an *element* (in `PFunctor.Idx` terms) of
this polynomial: a chosen codomain `Obs` together with a projection
`X → Obs`. The `Σ`-form `Σ Obs : Type u, X → Obs` is recovered
definitionally because `PFunctor.Idx P` unfolds to `Σ a, P.B a`. The
polynomial substrate is the truth; the `Observation` name is an
ergonomic re-skin in the spirit of `OracleSpec` / `OracleComp` and
`Spec.done` / `Spec.node`.

## Information lattice

The intended order on `Observation X` is *informativeness*, ordered low ≤ high:

* `Observation.bot X = ⟨PUnit, fun _ => PUnit.unit⟩` is the **bottom** of the
  lattice: zero information, the coarsest (one-class) partition.
* `Observation.top X = ⟨X, id⟩` is the **top**: full information, the finest
  (all-singleton) partition.
* `Observation.Refines k₁ k₂` (`k₁ ⊑ k₂`) means "`k₁` reveals no more than
  `k₂`": the projection of `k₁` factors through that of `k₂`.
* `Observation.combine k₁ k₂` is the **join** in the information lattice: the
  Σ-product of both kernels, i.e. the universal kernel that records what is
  learned by jointly observing through `k₁` and `k₂`.
* `Observation.postcomp k f` post-composes the projection of `k` with `f`,
  yielding a kernel that is automatically refined by `k` (a downgrade).

The dual meet (greatest common reduction, the coarsest kernel that both
refine) requires quotienting `X` by the joint indistinguishability relation
and is deferred until a use case requires it.

## Mathlib lattice notation

The named operations above are also exposed via Mathlib's order typeclasses
so that standard notation works on `Observation X`:

* `(⊤ : Observation X) = Observation.top X` via `Top`;
* `(⊥ : Observation X) = Observation.bot X` via `Bot`;
* `k₁ ≤ k₂` denotes `k₁.Refines k₂` via `LE` and `Preorder`;
* `bot_le` and `le_top` come from the `OrderBot` and `OrderTop` instances;
* `k₁ ⊔ k₂ = Observation.combine k₁ k₂` via `Max`.

Note that `Refines` is only a *preorder*, not a partial order: two
observations may mutually refine each other through different bijections of
their codomains (e.g. `⟨X × Y, _⟩` and `⟨Y × X, _⟩`). For that reason we do
not declare `SemilatticeSup` (which would require antisymmetry); the
join-style theorems for `combine` are stated as named lemmas instead.

A practical payoff is that `Pi`-instance lifting in Mathlib then transfers
all of this notation pointwise to per-party observation profiles
`Party → Observation X` (see `Multiparty/ObservationProfile.lean`) for free.

## Action shape

`Observation.Action k m Cont` is the maximally general local node type
associated to a kernel: it asks the participant to commit to a uniform
continuation family conditioned on the observation `o : k.1`. The four-mode
operational refinement and its `rfl`-friendly action shapes live in
`Multiparty/Core.lean` (`ViewMode`); this file only knows the universal form.
-/

universe u v

namespace Interaction
namespace Multiparty

namespace Observation

/-- The polynomial functor whose index type is `Multiparty.Observation X`:
positions are observation codomains `Type u`, and the child family at a
position `Obs : Type u` is the type of projections `X → Obs`.

Following the convention established by `Interaction.Spec.basePFunctor`,
this exposes `Observation X` as the index type
`PFunctor.Idx (basePFunctor X) = Σ Obs : Type u, X → Obs` of a specific
polynomial functor: the universal "observations of `X`" container. An
element of the polynomial is precisely a chosen codomain together with a
projection from `X` into it. -/
@[reducible]
def basePFunctor (X : Type u) : PFunctor.{u + 1, u} where
  A := Type u
  B := (X → ·)

end Observation

/--
`Observation X` is the polynomial-element form of a local view at a node
whose move space is `X`: a single quotient morphism `toObs : X → Obs`
packaged with its codomain `Obs`.

It is **definitionally** the index type of `Observation.basePFunctor X`:
`Observation X = PFunctor.Idx (basePFunctor X) = Σ Obs : Type u, X → Obs`,
mirroring the pattern by which `Interaction.Spec` is defined as
`PFunctor.FreeM Spec.basePFunctor PUnit`. The `Σ`-pair literal
`⟨Obs, π⟩` works directly as a constructor, and the projections `k.1` /
`k.2` recover the codomain and projection.

This is the maximally general "what does a participant see" primitive. It
is the carrier of the information lattice (see `Observation.top`,
`Observation.bot`, `Observation.Refines`, `Observation.combine`).

Operationally specialized observations with simpler `Action` shapes live in
`Multiparty/Core.lean` as the four-constructor `ViewMode` type; every
`ViewMode` collapses to an `Observation` via `ViewMode.toObservation`, and
every `Observation` lifts back into `ViewMode` via `Observation.toViewMode`
(equivalently, the universal `ViewMode.react` constructor).
-/
abbrev Observation (X : Type u) : Type (u + 1) :=
  PFunctor.Idx (Observation.basePFunctor X)

namespace Observation

variable {X : Type u}

/--
`Observation.top X = ⟨X, id⟩` is the **top** of the information lattice on
`X`: the identity projection, recording the entire move.

Every `Observation X` refines `Observation.top X`.
-/
protected def top (X : Type u) : Observation X := ⟨X, id⟩

/--
`Observation.bot X = ⟨PUnit, fun _ => PUnit.unit⟩` is the **bottom** of the
information lattice on `X`: the constant projection to a singleton, recording
nothing about the move.

`Observation.bot X` refines every `Observation X`.
-/
protected def bot (X : Type u) : Observation X := ⟨PUnit, fun _ => PUnit.unit⟩

/--
`Observation.Refines k₁ k₂` (read "`k₁` refines `k₂`") holds when `k₁` is no
more revealing than `k₂`: the projection of `k₁` factors through that of
`k₂`.

Equivalently, every `k₂`-indistinguishability class is a union of
`k₁`-indistinguishability classes, so observers using `k₁` learn at most what
observers using `k₂` learn. This is the natural ordering in which
`Observation.bot` is least and `Observation.top` is greatest.
-/
def Refines (k₁ k₂ : Observation X) : Prop :=
  ∃ f : k₂.1 → k₁.1, ∀ x, k₁.2 x = f (k₂.2 x)

@[refl] theorem Refines.refl (k : Observation X) : k.Refines k :=
  ⟨id, fun _ => rfl⟩

theorem Refines.trans {k₁ k₂ k₃ : Observation X}
    (h₁₂ : k₁.Refines k₂) (h₂₃ : k₂.Refines k₃) : k₁.Refines k₃ := by
  obtain ⟨f, hf⟩ := h₁₂
  obtain ⟨g, hg⟩ := h₂₃
  exact ⟨f ∘ g, fun x => (hf x).trans (congrArg f (hg x))⟩

/-- The bottom kernel refines every kernel: zero information is no more
revealing than any kernel. -/
theorem bot_refines (k : Observation X) : (Observation.bot X).Refines k :=
  ⟨fun _ => PUnit.unit, fun _ => rfl⟩

/-- Every kernel refines the top kernel: any kernel is no more revealing
than the identity projection. -/
theorem refines_top (k : Observation X) : k.Refines (Observation.top X) :=
  ⟨k.2, fun _ => rfl⟩

/--
`Observation.combine k₁ k₂` is the **join** in the information lattice: the
Σ-product of both kernels' observations.

It is the canonical way to combine two parties' views into a coalition view,
and the universal kernel that records what is learned by jointly observing
through `k₁` and `k₂`. Since `Refines` orders by informativeness,
`combine k₁ k₂` carries strictly more information than either factor.
-/
def combine (k₁ k₂ : Observation X) : Observation X :=
  ⟨k₁.1 × k₂.1, fun x => (k₁.2 x, k₂.2 x)⟩

theorem refines_combine_left (k₁ k₂ : Observation X) : k₁.Refines (combine k₁ k₂) :=
  ⟨Prod.fst, fun _ => rfl⟩

theorem refines_combine_right (k₁ k₂ : Observation X) : k₂.Refines (combine k₁ k₂) :=
  ⟨Prod.snd, fun _ => rfl⟩

/-- `combine` is the least upper bound for `Refines`: any kernel `k` that is
refined by both `k₁` and `k₂` is refined by `combine k₁ k₂`. -/
theorem combine_refines_of {k k₁ k₂ : Observation X}
    (h₁ : k₁.Refines k) (h₂ : k₂.Refines k) : (combine k₁ k₂).Refines k := by
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  refine ⟨fun y => (f₁ y, f₂ y), fun x => ?_⟩
  change (k₁.2 x, k₂.2 x) = (f₁ (k.2 x), f₂ (k.2 x))
  rw [hf₁, hf₂]

/--
`k.postcomp f` post-composes the projection of `k` with `f : k.1 → Y`,
yielding a kernel that is automatically refined by `k`.

This is the workhorse for "downgrading" an observation: if a corruption mode
strips a field from the observation type, the new kernel is `postcomp` of the
old one with the field-removal map.
-/
def postcomp (k : Observation X) {Y : Type u} (f : k.1 → Y) : Observation X :=
  ⟨Y, fun x => f (k.2 x)⟩

theorem postcomp_refines (k : Observation X) {Y : Type u} (f : k.1 → Y) :
    (k.postcomp f).Refines k :=
  ⟨f, fun _ => rfl⟩

/--
`Observation.Action k m Cont` is the maximally general local node shape
associated to a kernel `k = ⟨Obs, toObs⟩`.

It asks the participant to commit to an entire family of continuations
indexed by the observation `o : Obs`: for each observed value `o`, an
effectful map sending each move `x : X` whose observation is `o` to its
continuation `Cont x`.

Operationally specialized shapes (the simpler `Σ-of-X`, `function-from-X`,
and `function-into-Cont` patterns) live in `Multiparty/Core.lean` as
`ViewMode.Action`; this is the universal shape that they all collapse to.
-/
def Action (k : Observation X) (m : Type u → Type u) (Cont : X → Type u) : Type u :=
  (o : k.1) → m ((x : X) → k.2 x = o → Cont x)

/-! ### Mathlib lattice typeclass instances

The instances below expose the information-lattice algebra of `Observation X`
through Mathlib's standard order classes. They are non-defining: each one is
a thin wrapper over the named operations above (`Observation.top`,
`Observation.bot`, `Refines`, `combine`).

A `SemilatticeSup` instance would require antisymmetry of `Refines`, which
fails in general (mutually refining kernels related by codomain bijections),
so we expose only `Max` for the `⊔` notation; the join-style lemmas live as
named theorems above.
-/

instance : Top (Observation X) := ⟨Observation.top X⟩

instance : Bot (Observation X) := ⟨Observation.bot X⟩

instance : LE (Observation X) := ⟨Refines⟩

instance : Preorder (Observation X) where
  le_refl := Refines.refl
  le_trans _ _ _ := Refines.trans

instance : OrderTop (Observation X) where
  le_top := refines_top

instance : OrderBot (Observation X) where
  bot_le := bot_refines

instance : Max (Observation X) := ⟨combine⟩

@[simp] theorem top_def : (⊤ : Observation X) = Observation.top X := rfl

@[simp] theorem bot_def : (⊥ : Observation X) = Observation.bot X := rfl

@[simp] theorem le_def {k₁ k₂ : Observation X} : k₁ ≤ k₂ ↔ k₁.Refines k₂ := Iff.rfl

@[simp] theorem sup_def (k₁ k₂ : Observation X) : k₁ ⊔ k₂ = combine k₁ k₂ := rfl

end Observation

end Multiparty
end Interaction
