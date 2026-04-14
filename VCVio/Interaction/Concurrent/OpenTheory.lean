/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Interface

/-!
# Operations-first open composition

This module records the smallest algebraic interface currently needed for the
UC-facing "open world" direction.

The key design choice is that we do **not** yet commit to a concrete
representation of composite open systems. In particular, this file does not
introduce a quoted syntax tree, wiring graph, or runtime semantics. Instead it
isolates the boundary-indexed operations that any such representation should
support:

* `map` for structural interface adaptation,
* `par` for side-by-side composition, and
* `wire` for internalizing one shared boundary between two open systems.

It also keeps `plug` as the top-level closure operation against a matching
external context. Conceptually, `wire` is the more local composition
primitive, while `plug` is the fully closing special case that remains most
convenient for contextual comparison.

This is the operations-first "Option C2" shape from the current UC design
notes. Later layers may realize `OpenTheory` by:

* a direct family of open processes,
* a free syntax of open-system expressions,
* an explicit graph/network representation,
* or another equivalent presentation.

What matters here is the algebra of open composition, not the concrete
representation of composite worlds.
-/

universe u

namespace Interaction
namespace Concurrent

/--
`OpenTheory` is a boundary-indexed algebra of open systems.

For each directed boundary `Δ`, `Obj Δ` is the type of systems that still
expose `Δ` to an external context. The structure then specifies three
primitive composition operations:

* `map` changes how an exposed boundary is presented, without changing the
  internal system;
* `par` places two open systems side by side and exposes the tensor of their
  boundaries;
* `wire` connects one shared boundary between two open systems and leaves the
  remaining outer boundaries exposed; and
* `plug` closes an open system against a matching context on the swapped
  boundary, yielding a closed system.

This interface is intentionally smaller than a full syntax of open worlds.
Its job is to state the semantic commitment we actually care about: a notion of
open system equipped with compositional boundary operations.

The first law layer is kept intentionally modest. This file bundles:

* functoriality of `map`,
* naturality of `par` with respect to boundary tensors, and
* naturality of `wire` with respect to its still-exposed outer boundaries, and
* naturality of `plug` with respect to swapped boundary adaptation.

More ambitious coherence laws, such as associativity/unit/symmetry of open
composition, should wait until the library settles on the right notion of
boundary equivalence or open-system isomorphism.

This first interface fixes one ambient pair of universes for ports and
messages on both sides of every boundary. That keeps `PortBoundary.swap` inside
the same family of objects. A more heterogeneous universe-polymorphic version
can be added later if it becomes genuinely necessary.
-/
structure OpenTheory where
  /--
  `Obj Δ` is the type of open systems exposing boundary `Δ`.

  The boundary is directed: `Δ.In` is what the surrounding context may send
  into the system, and `Δ.Out` is what the system may emit back out.
  -/
  Obj : PortBoundary → Type u

  /--
  Adapt the exposed boundary of an open system along a structural boundary
  morphism.

  This changes only the *presentation* of the boundary. The intended reading is
  that `map φ W` is the same internal system as `W`, but viewed through the
  interface adaptation `φ`.
  -/
  map :
    {Δ₁ Δ₂ : PortBoundary} →
    PortBoundary.Hom Δ₁ Δ₂ →
    Obj Δ₁ →
    Obj Δ₂

  /--
  Place two open systems side by side.

  The resulting system exposes the tensor of the two boundaries: the outside
  world may interact independently with either side.
  -/
  par :
    {Δ₁ Δ₂ : PortBoundary} →
    Obj Δ₁ →
    Obj Δ₂ →
    Obj (PortBoundary.tensor Δ₁ Δ₂)

  /--
  Connect one shared boundary between two open systems.

  If the left system exposes boundary `Δ₁ ⊗ Γ` and the right system exposes
  boundary `swap Γ ⊗ Δ₂`, then `wire` connects the shared middle boundary `Γ`
  internally and leaves only the outer boundaries `Δ₁` and `Δ₂` exposed.

  This is the first local composition primitive beyond plain parallel
  juxtaposition. It is the right operation for assembling open systems
  incrementally without forcing immediate total closure.
  -/
  wire :
    {Δ₁ Γ Δ₂ : PortBoundary} →
    Obj (PortBoundary.tensor Δ₁ Γ) →
    Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) →
    Obj (PortBoundary.tensor Δ₁ Δ₂)

  /--
  Close an open system against a matching plug.

  If `W : Obj Δ` is an open system and `K : Obj (PortBoundary.swap Δ)` is a
  context exposing the opposite boundary, then `plug W K` is the structurally
  closed result of connecting those two boundaries together.

  This is the minimal closure operation needed for UC-style contextual
  comparison. More general partial internalization operations can be added
  later if they are genuinely needed.
  -/
  plug :
    {Δ : PortBoundary} →
    Obj Δ →
    Obj (PortBoundary.swap Δ) →
    Obj (PortBoundary.empty)

namespace OpenTheory

/--
`IsLawfulMap T` states that boundary adaptation in `T` behaves functorially.

This is the first law layer for `OpenTheory`, and the one we can state without
committing to any further monoidal/coherence structure on boundaries.
-/
class IsLawfulMap (T : _root_.Interaction.Concurrent.OpenTheory.{u}) :
    Prop where
  /--
  Adapting a system along the identity boundary morphism does nothing.
  -/
  map_id :
    ∀ {Δ : PortBoundary} (W : T.Obj Δ),
      T.map (PortBoundary.Hom.id Δ) W = W

  /--
  Adapting along a composite boundary morphism is the same as adapting in two
  successive steps.
  -/
  map_comp :
    ∀ {Δ₁ Δ₂ Δ₃ : PortBoundary}
      (g : PortBoundary.Hom Δ₂ Δ₃)
      (f : PortBoundary.Hom Δ₁ Δ₂)
      (W : T.Obj Δ₁),
        T.map (PortBoundary.Hom.comp g f) W = T.map g (T.map f W)

/--
`IsLawfulPar T` states that parallel composition in `T` is natural with
respect to boundary adaptation.

This is the first structural law for `par` that does not require introducing a
separate theory of boundary isomorphisms. Associativity and unit laws can be
added later once that boundary-equivalence vocabulary is in place.
-/
class IsLawfulPar (T : _root_.Interaction.Concurrent.OpenTheory.{u}) :
    Prop extends IsLawfulMap T where
  /--
  Mapping a side-by-side composite along a tensor boundary morphism is the same
  as mapping each side independently before composing them in parallel.
  -/
  map_par :
    ∀ {Δ₁ Δ₁' Δ₂ Δ₂' : PortBoundary}
      (f₁ : PortBoundary.Hom Δ₁ Δ₁')
      (f₂ : PortBoundary.Hom Δ₂ Δ₂')
      (W₁ : T.Obj Δ₁)
      (W₂ : T.Obj Δ₂),
        T.map (PortBoundary.Hom.tensor f₁ f₂) (T.par W₁ W₂) =
          T.par (T.map f₁ W₁) (T.map f₂ W₂)

/--
`IsLawfulWire T` states that partial wiring in `T` is natural with respect to
boundary adaptation.

This is the first law for local composition: adapting the still-exposed
left/right outer boundaries can be pushed inside a `wire`.

Transporting the shared middle boundary itself is a subtler question because
`PortBoundary.Hom.swap` is contravariant. The corresponding law should be
stated later using boundary equivalences or a more symmetric vocabulary.
-/
class IsLawfulWire (T : _root_.Interaction.Concurrent.OpenTheory.{u}) :
    Prop extends IsLawfulMap T where
  /--
  Partial wiring is natural in its still-exposed outer boundaries.

  The shared middle boundary is held fixed in this first law layer. That keeps
  the statement well aligned with the variance of `PortBoundary.Hom` while
  still capturing the most important structural behavior of `wire`.
  -/
  map_wire :
    ∀ {Δ₁ Δ₁' Γ Δ₂ Δ₂' : PortBoundary}
      (f₁ : PortBoundary.Hom Δ₁ Δ₁')
      (f₂ : PortBoundary.Hom Δ₂ Δ₂')
      (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)),
        T.map (PortBoundary.Hom.tensor f₁ f₂) (T.wire W₁ W₂) =
          T.wire
            (T.map (PortBoundary.Hom.tensor f₁ (PortBoundary.Hom.id Γ)) W₁)
            (T.map
              (PortBoundary.Hom.tensor
                (PortBoundary.Hom.id (PortBoundary.swap Γ))
                f₂)
              W₂)

/--
`IsLawfulPlug T` states that plugging in `T` is natural with respect to
boundary adaptation.

This is the first structural law for `plug`: adapting the open side before
closure is equivalent to adapting the matching plug on the swapped boundary.
-/
class IsLawfulPlug (T : _root_.Interaction.Concurrent.OpenTheory.{u}) :
    Prop extends IsLawfulMap T where
  /--
  Boundary adaptation may be pushed across a plug by swapping the same
  adaptation onto the context side.
  -/
  map_plug :
    ∀ {Δ₁ Δ₂ : PortBoundary}
      (f : PortBoundary.Hom Δ₁ Δ₂)
      (W : T.Obj Δ₁)
      (K : T.Obj (PortBoundary.swap Δ₂)),
        T.plug (T.map f W) K =
          T.plug W (T.map (PortBoundary.Hom.swap f) K)

/--
`IsLawful T` is the first bundled law package for an open-composition theory.

At this stage it only records:

* functoriality of `map`,
* naturality of `par`, and
* naturality of `wire`, and
* naturality of `plug`.

Unit, associativity, and symmetry laws for open composition should be added
later, once the library settles on the right notion of boundary equivalence.
-/
class IsLawful (T : _root_.Interaction.Concurrent.OpenTheory.{u}) :
    Prop extends IsLawfulPar T, IsLawfulWire T, IsLawfulPlug T

/--
`Closed T` is the type of closed systems in the open-composition theory `T`.

These are precisely the systems with no remaining exposed inputs or outputs.
-/
abbrev Closed
    (T : _root_.Interaction.Concurrent.OpenTheory.{u}) :
    Type u :=
  T.Obj (PortBoundary.empty)

/--
`Plug T Δ` is the type of contexts that can close a `Δ`-shaped open system in
the theory `T`.

Such a context exposes the swapped boundary: it accepts what the open system
emits, and emits what the open system accepts.
-/
abbrev Plug
    (T : _root_.Interaction.Concurrent.OpenTheory.{u})
    (Δ : PortBoundary) : Type u :=
  T.Obj (PortBoundary.swap Δ)

/--
Close an open system against a matching plug.

This is just the `plug` operation restated using the helper names `Closed` and
`Plug`, which often match the UC / contextual-equivalence reading more closely
than the raw swapped-boundary formulation.
-/
abbrev close
    (T : _root_.Interaction.Concurrent.OpenTheory.{u})
    {Δ : PortBoundary} :
    T.Obj Δ →
    T.Plug Δ →
    T.Closed :=
  T.plug

/--
Transport an open system along a boundary equivalence.

This is the equivalence-level companion to `map`: instead of an arbitrary
one-way boundary adaptation, it uses a canonical directed boundary
isomorphism. In practice this is the convenient way to reassociate, swap, or
drop empty boundary fragments once those facts have been expressed as
`PortBoundary.Equiv`s.
-/
abbrev mapEquiv
    (T : _root_.Interaction.Concurrent.OpenTheory.{u})
    {Δ₁ Δ₂ : PortBoundary} :
    PortBoundary.Equiv Δ₁ Δ₂ →
    T.Obj Δ₁ →
    T.Obj Δ₂ :=
  fun e => T.map e.toHom

section Laws

variable {T : _root_.Interaction.Concurrent.OpenTheory.{u}}

/--
Adapting along the identity boundary morphism leaves an open system unchanged.
-/
@[simp]
theorem map_id
    [IsLawfulMap T]
    {Δ : PortBoundary}
    (W : T.Obj Δ) :
    T.map (PortBoundary.Hom.id Δ) W = W :=
  IsLawfulMap.map_id W

/--
Adapting along a composite boundary morphism is the same as adapting in two
successive steps.
-/
theorem map_comp
    [IsLawfulMap T]
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (g : PortBoundary.Hom Δ₂ Δ₃)
    (f : PortBoundary.Hom Δ₁ Δ₂)
    (W : T.Obj Δ₁) :
    T.map (PortBoundary.Hom.comp g f) W = T.map g (T.map f W) :=
  IsLawfulMap.map_comp g f W

/--
Mapping along the identity boundary equivalence does nothing.
-/
@[simp]
theorem mapEquiv_refl
    [IsLawfulMap T]
    {Δ : PortBoundary}
    (W : T.Obj Δ) :
    T.mapEquiv (PortBoundary.Equiv.refl Δ) W = W :=
  map_id (T := T) (Δ := Δ) W

/--
Mapping along a composite boundary equivalence is the same as mapping in two
successive equivalence-guided steps.
-/
theorem mapEquiv_trans
    [IsLawfulMap T]
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (e₁ : PortBoundary.Equiv Δ₁ Δ₂)
    (e₂ : PortBoundary.Equiv Δ₂ Δ₃)
    (W : T.Obj Δ₁) :
    T.mapEquiv (PortBoundary.Equiv.trans e₁ e₂) W =
      T.mapEquiv e₂ (T.mapEquiv e₁ W) := by
  simpa [OpenTheory.mapEquiv, PortBoundary.Equiv.trans] using
    map_comp (T := T) e₂.toHom e₁.toHom W

/-- Parallel composition is natural with respect to boundary adaptation. -/
theorem map_par
    [IsLawfulPar T]
    {Δ₁ Δ₁' Δ₂ Δ₂' : PortBoundary}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁')
    (f₂ : PortBoundary.Hom Δ₂ Δ₂')
    (W₁ : T.Obj Δ₁)
    (W₂ : T.Obj Δ₂) :
    T.map (PortBoundary.Hom.tensor f₁ f₂) (T.par W₁ W₂) =
      T.par (T.map f₁ W₁) (T.map f₂ W₂) :=
  IsLawfulPar.map_par f₁ f₂ W₁ W₂

/--
Parallel composition is natural with respect to boundary equivalences.

This is the equivalence-guided companion to `map_par`: canonical reshaping of
the left and right boundaries may be pushed inside `par`.
-/
theorem mapEquiv_par
    [IsLawfulPar T]
    {Δ₁ Δ₁' Δ₂ Δ₂' : PortBoundary}
    (e₁ : PortBoundary.Equiv Δ₁ Δ₁')
    (e₂ : PortBoundary.Equiv Δ₂ Δ₂')
    (W₁ : T.Obj Δ₁)
    (W₂ : T.Obj Δ₂) :
    T.mapEquiv (PortBoundary.Equiv.tensorCongr e₁ e₂) (T.par W₁ W₂) =
      T.par (T.mapEquiv e₁ W₁) (T.mapEquiv e₂ W₂) := by
  simpa [OpenTheory.mapEquiv] using
    map_par (T := T) e₁.toHom e₂.toHom W₁ W₂

/--
Partial wiring is natural with respect to boundary adaptation.
-/
theorem map_wire
    [IsLawfulWire T]
    {Δ₁ Δ₁' Γ Δ₂ Δ₂' : PortBoundary}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁')
    (f₂ : PortBoundary.Hom Δ₂ Δ₂')
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    T.map (PortBoundary.Hom.tensor f₁ f₂) (T.wire W₁ W₂) =
      T.wire
        (T.map (PortBoundary.Hom.tensor f₁ (PortBoundary.Hom.id Γ)) W₁)
        (T.map
          (PortBoundary.Hom.tensor
            (PortBoundary.Hom.id (PortBoundary.swap Γ))
            f₂)
          W₂) :=
  IsLawfulWire.map_wire f₁ f₂ W₁ W₂

/--
Partial wiring is natural with respect to boundary equivalences on the still
exposed outer boundaries.

As in `map_wire`, the shared middle boundary is held fixed in this first law
layer. The point is that canonical reassociation or symmetry on the outer
interfaces can already be pushed through `wire` without enlarging the
primitive kernel of `OpenTheory`.
-/
theorem mapEquiv_wire
    [IsLawfulWire T]
    {Δ₁ Δ₁' Γ Δ₂ Δ₂' : PortBoundary}
    (e₁ : PortBoundary.Equiv Δ₁ Δ₁')
    (e₂ : PortBoundary.Equiv Δ₂ Δ₂')
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    T.mapEquiv (PortBoundary.Equiv.tensorCongr e₁ e₂) (T.wire W₁ W₂) =
      T.wire
        (T.mapEquiv
          (PortBoundary.Equiv.tensorCongr e₁ (PortBoundary.Equiv.refl Γ))
          W₁)
        (T.mapEquiv
          (PortBoundary.Equiv.tensorCongr
            (PortBoundary.Equiv.refl (PortBoundary.swap Γ))
            e₂)
          W₂) := by
  simpa [OpenTheory.mapEquiv] using
    map_wire (T := T) e₁.toHom e₂.toHom W₁ W₂

/--
Plugging is natural with respect to boundary adaptation.
-/
theorem map_plug
    [IsLawfulPlug T]
    {Δ₁ Δ₂ : PortBoundary}
    (f : PortBoundary.Hom Δ₁ Δ₂)
    (W : T.Obj Δ₁)
    (K : T.Obj (PortBoundary.swap Δ₂)) :
    T.plug (T.map f W) K =
      T.plug W (T.map (PortBoundary.Hom.swap f) K) :=
  IsLawfulPlug.map_plug f W K

/--
Plugging is natural with respect to boundary equivalence.

This is the boundary-equivalence form of `map_plug`: if the exposed side of
the open system is reshaped by a canonical directed isomorphism, the same
forward boundary adaptation can be pushed across the plug after swapping
directions.

The right-hand side is phrased with the swapped boundary `Hom` directly rather
than wrapping it back into `mapEquiv`. That is intentional: once directions
are reversed, the variance becomes clearer at the raw boundary-map level than
through a second equivalence wrapper.
-/
theorem mapEquiv_plug
    [IsLawfulPlug T]
    {Δ₁ Δ₂ : PortBoundary}
    (e : PortBoundary.Equiv Δ₁ Δ₂)
    (W : T.Obj Δ₁)
    (K : T.Obj (PortBoundary.swap Δ₂)) :
    T.plug (T.mapEquiv e W) K =
      T.plug W (T.map (PortBoundary.Hom.swap e.toHom) K) := by
  simpa [OpenTheory.mapEquiv] using
    map_plug (T := T) e.toHom W K

end Laws

end OpenTheory

end Concurrent
end Interaction
