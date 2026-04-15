/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.Interface

/-!
# Open composition algebra with monoidal coherence

This module defines `OpenTheory`, a boundary-indexed algebra of open systems,
together with a hierarchy of lawfulness classes capturing increasingly strong
equational properties.

## Operations

* `map` adapts how an exposed boundary is presented.
* `par` places two open systems side by side (tensor of boundaries).
* `wire` internalizes one shared boundary between two open systems.
* `plug` closes an open system against a matching context on the swapped
  boundary.

## Class hierarchy

* `IsLawfulMap`: functoriality of `map` (identity and composition).
* `IsLawfulPar`/`IsLawfulWire`/`IsLawfulPlug`: naturality of each combinator
  with respect to boundary adaptation.
* `IsLawful`: bundles all naturality laws.
* `Monoidal`: symmetric monoidal coherence for `par` (associativity,
  commutativity, left and right unit laws via a distinguished `unit` object).
* `CompactClosed`: compact closed structure (`idWire` as coevaluation,
  `plug` derivable from `wire`, zig-zag identity for `wire_idWire`).

Concrete realizations include the free models (`Expr.theory`, `Interp.theory`)
and the process-backed `openTheory` in `OpenProcessModel.lean`.
-/

universe u

namespace Interaction
namespace UC

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

Lawfulness is stratified into three levels via the class hierarchy
`IsLawful ≤ Monoidal ≤ CompactClosed` (see the module docstring).

Universe polymorphism: one ambient pair of universes for ports and
messages on both sides of every boundary, keeping `PortBoundary.swap` inside
the same family of objects.
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
class IsLawfulMap (T : _root_.Interaction.UC.OpenTheory.{u}) :
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
class IsLawfulPar (T : _root_.Interaction.UC.OpenTheory.{u}) :
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
class IsLawfulWire (T : _root_.Interaction.UC.OpenTheory.{u}) :
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
class IsLawfulPlug (T : _root_.Interaction.UC.OpenTheory.{u}) :
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
class IsLawful (T : _root_.Interaction.UC.OpenTheory.{u}) :
    Prop extends IsLawfulPar T, IsLawfulWire T, IsLawfulPlug T

/--
`Monoidal T` extends `IsLawful T` with the symmetric monoidal coherence
laws for `par`: a unit object, plus associativity, commutativity (braiding),
and left/right unit laws up to boundary equivalence.

Pentagon and hexagon coherence conditions are deferred: they are derivable
in the free models and hold trivially for the concrete model up to process
isomorphism.
-/
class Monoidal (T : _root_.Interaction.UC.OpenTheory.{u}) extends IsLawful T where
  unit : T.Obj PortBoundary.empty
  par_assoc :
    ∀ {Δ₁ Δ₂ Δ₃ : PortBoundary}
      (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂) (W₃ : T.Obj Δ₃),
      T.map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom
        (T.par (T.par W₁ W₂) W₃) =
      T.par W₁ (T.par W₂ W₃)
  par_comm :
    ∀ {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂),
      T.map (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom
        (T.par W₁ W₂) =
      T.par W₂ W₁
  par_leftUnit :
    ∀ {Δ : PortBoundary} (W : T.Obj Δ),
      T.map (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom
        (T.par unit W) = W
  par_rightUnit :
    ∀ {Δ : PortBoundary} (W : T.Obj Δ),
      T.map (PortBoundary.Equiv.tensorEmptyRight Δ).toHom
        (T.par W unit) = W

/--
`CompactClosed T` extends `Monoidal T` with a coevaluation morphism
(`idWire`) and laws that connect it to `wire` and `plug`.

The `idWire Γ` process relays messages on the boundary `swap Γ ⊗ Γ`. The
key property `wire_idWire` says that wiring any process against the identity
wire leaves it unchanged (zig-zag identity). Together with `plug_eq_wire`,
this characterizes the compact closed structure.
-/
class CompactClosed (T : _root_.Interaction.UC.OpenTheory.{u})
    extends Monoidal T where
  /-- The identity wire (coevaluation): a process on the boundary `swap Γ ⊗ Γ`
  that relays messages bidirectionally. -/
  idWire : ∀ (Γ : PortBoundary),
    T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Γ)
  /-- `plug` is derivable from `wire` plus boundary reshaping. -/
  plug_eq_wire :
    ∀ {Δ : PortBoundary}
      (W : T.Obj Δ) (K : T.Obj (PortBoundary.swap Δ)),
      T.plug W K =
        T.map (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
          (T.wire
            (T.map (PortBoundary.Equiv.tensorEmptyLeft Δ).symm.toHom W)
            (T.map (PortBoundary.Equiv.tensorEmptyRight
              (PortBoundary.swap Δ)).symm.toHom K))
  /-- Left zig-zag: wiring the identity wire on the left is a no-op. -/
  wire_idWire :
    ∀ (Γ : PortBoundary) {Δ₂ : PortBoundary}
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)),
      T.wire (idWire Γ) W₂ = W₂
  /-- Right zig-zag: wiring the identity wire on the right is a no-op. -/
  wire_idWire_right :
    ∀ (Γ : PortBoundary) {Δ₁ : PortBoundary}
      (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)),
      T.wire W₁ (idWire Γ) = W₁
  /-- The monoidal unit is the coevaluation at the trivial boundary. -/
  unit_eq :
    unit = T.map (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
      (idWire PortBoundary.empty)
  /-- Wire associativity: sequential wiring can be reassociated.

  Wiring `W₁` with `W₂` through `Γ₁` and then with `W₃` through `Γ₂`
  equals wiring `W₂` with `W₃` through `Γ₂` first, then with `W₁`
  through `Γ₁`. -/
  wire_assoc :
    ∀ {Δ₁ Γ₁ Γ₂ Δ₃ : PortBoundary}
      (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ₁))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ₁) Γ₂))
      (W₃ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ₂) Δ₃)),
      T.wire (T.wire W₁ W₂) W₃ = T.wire W₁ (T.wire W₂ W₃)
  /-- Wire-par superposition (left): if the left factor of a parallel
  composition does not share a boundary with the second wire argument,
  it can be factored out of the wire. This is one of the axioms of
  traced symmetric monoidal categories. -/
  wire_par_superpose :
    ∀ {Δ₁ Δ₂ Γ Δ₃ : PortBoundary}
      (W₁ : T.Obj Δ₁)
      (W₂ : T.Obj (PortBoundary.tensor Δ₂ Γ))
      (W₃ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₃)),
      T.wire
        (T.map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Γ).symm.toHom
          (T.par W₁ W₂))
        W₃ =
      T.map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom
        (T.par W₁ (T.wire W₂ W₃))
  /-- Wire commutativity: the roles of the two wire factors are
  interchangeable up to boundary reshaping. -/
  wire_comm :
    ∀ {Δ₁ Γ Δ₂ : PortBoundary}
      (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)),
      T.wire W₁ W₂ =
        T.map (PortBoundary.Equiv.tensorComm Δ₂ Δ₁).toHom
          (T.wire
            (T.map
              (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom
              W₂)
            (T.map (PortBoundary.Equiv.tensorComm Δ₁ Γ).toHom W₁))
  /-- Plug-par factorization (left): plugging a parallel composition against
  a context factors into wiring the right component into the context, then
  plugging the left component against the result.

  This is the "vanishing tensor" axiom of traced monoidal categories: a full
  contraction over a tensor boundary `Δ₁ ⊗ Δ₂` decomposes into two sequential
  contractions, first over `Δ₂` and then over `Δ₁`. -/
  plug_par_left :
    ∀ {Δ₁ Δ₂ : PortBoundary}
      (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
      (K : T.Obj (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))),
      T.plug (T.par W₁ W₂) K =
        T.plug W₁
          (T.map (PortBoundary.Equiv.tensorEmptyRight
              (PortBoundary.swap Δ₁)).toHom
            (T.wire
              (Γ := PortBoundary.swap Δ₂)
              (Δ₂ := PortBoundary.empty)
              K
              (T.map (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm.toHom
                W₂)))
  /-- Plug-wire factorization (left): closing a wired composition against
  a context factors through the left wire component.

  The right component `W₂` is wired into the context `K` through the `Δ₂`
  boundary, producing a plug for `Δ₁ ⊗ Γ`, and then `W₁` is plugged against
  the result. -/
  plug_wire_left :
    ∀ {Δ₁ Γ Δ₂ : PortBoundary}
      (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
      (K : T.Obj (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))),
      T.plug (T.wire W₁ W₂) K =
        T.plug W₁
          (T.wire
            (Δ₁ := PortBoundary.swap Δ₁)
            (Γ := PortBoundary.swap Δ₂)
            (Δ₂ := PortBoundary.swap Γ)
            K
            (T.map (PortBoundary.Equiv.tensorComm
              (PortBoundary.swap Γ) Δ₂).toHom W₂))

/--
`Closed T` is the type of closed systems in the open-composition theory `T`.

These are precisely the systems with no remaining exposed inputs or outputs.
-/
abbrev Closed
    (T : _root_.Interaction.UC.OpenTheory.{u}) :
    Type u :=
  T.Obj (PortBoundary.empty)

/--
`Plug T Δ` is the type of contexts that can close a `Δ`-shaped open system in
the theory `T`.

Such a context exposes the swapped boundary: it accepts what the open system
emits, and emits what the open system accepts.
-/
abbrev Plug
    (T : _root_.Interaction.UC.OpenTheory.{u})
    (Δ : PortBoundary) : Type u :=
  T.Obj (PortBoundary.swap Δ)

/--
Close an open system against a matching plug.

This is just the `plug` operation restated using the helper names `Closed` and
`Plug`, which often match the UC / contextual-equivalence reading more closely
than the raw swapped-boundary formulation.
-/
abbrev close
    (T : _root_.Interaction.UC.OpenTheory.{u})
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
    (T : _root_.Interaction.UC.OpenTheory.{u})
    {Δ₁ Δ₂ : PortBoundary} :
    PortBoundary.Equiv Δ₁ Δ₂ →
    T.Obj Δ₁ →
    T.Obj Δ₂ :=
  fun e => T.map e.toHom

section Laws

variable {T : _root_.Interaction.UC.OpenTheory.{u}}

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

@[simp]
theorem mapEquiv_symm_cancel
    [IsLawfulMap T]
    {Δ₁ Δ₂ : PortBoundary}
    (e : PortBoundary.Equiv Δ₁ Δ₂)
    (W : T.Obj Δ₁) :
    T.mapEquiv e.symm (T.mapEquiv e W) = W := by
  unfold OpenTheory.mapEquiv
  rw [← map_comp]
  simp [map_id]

@[simp]
theorem mapEquiv_cancel_symm
    [IsLawfulMap T]
    {Δ₁ Δ₂ : PortBoundary}
    (e : PortBoundary.Equiv Δ₁ Δ₂)
    (W : T.Obj Δ₂) :
    T.mapEquiv e (T.mapEquiv e.symm W) = W := by
  unfold OpenTheory.mapEquiv
  rw [← map_comp]
  simp [map_id]

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

/--
Reassociating a nested parallel composition of three open systems.
-/
theorem par_assoc
    [Monoidal T]
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂) (W₃ : T.Obj Δ₃) :
    T.mapEquiv (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃)
      (T.par (T.par W₁ W₂) W₃) =
    T.par W₁ (T.par W₂ W₃) :=
  Monoidal.par_assoc W₁ W₂ W₃

/--
Swapping the components of a parallel composition along the tensor
commutativity equivalence.
-/
theorem par_comm
    [Monoidal T]
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂) :
    T.mapEquiv (PortBoundary.Equiv.tensorComm Δ₁ Δ₂)
      (T.par W₁ W₂) =
    T.par W₂ W₁ :=
  Monoidal.par_comm W₁ W₂

/-- The monoidal unit is a left identity for parallel composition. -/
@[simp]
theorem par_leftUnit
    [Monoidal T]
    {Δ : PortBoundary}
    (W : T.Obj Δ) :
    T.mapEquiv (PortBoundary.Equiv.tensorEmptyLeft Δ)
      (T.par (Monoidal.unit (T := T)) W) = W :=
  Monoidal.par_leftUnit W

/-- The monoidal unit is a right identity for parallel composition. -/
@[simp]
theorem par_rightUnit
    [Monoidal T]
    {Δ : PortBoundary}
    (W : T.Obj Δ) :
    T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight Δ)
      (T.par W (Monoidal.unit (T := T))) = W :=
  Monoidal.par_rightUnit W

/-- `plug` expressed via `wire` and boundary reshaping. -/
theorem plug_eq_wire
    [CompactClosed T]
    {Δ : PortBoundary}
    (W : T.Obj Δ) (K : T.Obj (PortBoundary.swap Δ)) :
    T.plug W K =
      T.map (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
        (T.wire
          (T.map (PortBoundary.Equiv.tensorEmptyLeft Δ).symm.toHom W)
          (T.map (PortBoundary.Equiv.tensorEmptyRight
            (PortBoundary.swap Δ)).symm.toHom K)) :=
  CompactClosed.plug_eq_wire W K

/-- Left zig-zag: wiring the identity wire on the left is a no-op. -/
@[simp]
theorem wire_idWire
    [CompactClosed T]
    {Γ : PortBoundary}
    {Δ₂ : PortBoundary}
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    T.wire (CompactClosed.idWire (T := T) Γ) W₂ = W₂ :=
  CompactClosed.wire_idWire Γ W₂

/-- Right zig-zag: wiring the identity wire on the right is a no-op. -/
@[simp]
theorem wire_idWire_right
    [CompactClosed T]
    {Γ : PortBoundary}
    {Δ₁ : PortBoundary}
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)) :
    T.wire W₁ (CompactClosed.idWire (T := T) Γ) = W₁ :=
  CompactClosed.wire_idWire_right Γ W₁

/-- The monoidal unit is the coevaluation at the trivial boundary. -/
theorem unit_eq
    [CompactClosed T] :
    Monoidal.unit (T := T) =
      T.map (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
        (CompactClosed.idWire (T := T) PortBoundary.empty) :=
  CompactClosed.unit_eq

/-! ### Wire algebra -/

/-- Wire-par superposition: the left factor of a parallel composition
can be moved outside a wire when it doesn't share the contracted
boundary. -/
theorem wire_par_superpose
    [CompactClosed T]
    {Δ₁ Δ₂ Γ Δ₃ : PortBoundary}
    (W₁ : T.Obj Δ₁)
    (W₂ : T.Obj (PortBoundary.tensor Δ₂ Γ))
    (W₃ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₃)) :
    T.wire
      (T.mapEquiv (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Γ).symm
        (T.par W₁ W₂))
      W₃ =
    T.mapEquiv (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm
      (T.par W₁ (T.wire W₂ W₃)) :=
  CompactClosed.wire_par_superpose W₁ W₂ W₃

/-- Wire associativity: sequential wiring can be reassociated. -/
theorem wire_assoc
    [CompactClosed T]
    {Δ₁ Γ₁ Γ₂ Δ₃ : PortBoundary}
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ₁))
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ₁) Γ₂))
    (W₃ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ₂) Δ₃)) :
    T.wire (T.wire W₁ W₂) W₃ = T.wire W₁ (T.wire W₂ W₃) :=
  CompactClosed.wire_assoc W₁ W₂ W₃

/-- Wire commutativity: the roles of the two wire factors are
interchangeable up to boundary reshaping. -/
theorem wire_comm
    [CompactClosed T]
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    T.wire W₁ W₂ =
      T.mapEquiv (PortBoundary.Equiv.tensorComm Δ₂ Δ₁)
        (T.wire
          (T.mapEquiv
            (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂) W₂)
          (T.mapEquiv (PortBoundary.Equiv.tensorComm Δ₁ Γ) W₁)) :=
  CompactClosed.wire_comm W₁ W₂

/-- Plug-par factorization (left): plugging a parallel composition against a
context factors through the left component.

See `CompactClosed.plug_par_left` for the full docstring. -/
theorem plug_par_left
    [CompactClosed T]
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
    (K : T.Obj (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    T.plug (T.par W₁ W₂) K =
      T.plug W₁
        (T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁))
          (T.wire
            (Γ := PortBoundary.swap Δ₂)
            (Δ₂ := PortBoundary.empty)
            K
            (T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm W₂))) :=
  CompactClosed.plug_par_left W₁ W₂ K

/-- Plug-wire factorization (left): closing a wired composition against a
context factors through the left wire component.

See `CompactClosed.plug_wire_left` for the full docstring. -/
theorem plug_wire_left
    [CompactClosed T]
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : T.Obj (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    T.plug (T.wire W₁ W₂) K =
      T.plug W₁
        (T.wire
          (Δ₁ := PortBoundary.swap Δ₁)
          (Γ := PortBoundary.swap Δ₂)
          (Δ₂ := PortBoundary.swap Γ)
          K
          (T.mapEquiv (PortBoundary.Equiv.tensorComm
            (PortBoundary.swap Γ) Δ₂) W₂)) :=
  CompactClosed.plug_wire_left W₁ W₂ K

end Laws

end OpenTheory

end UC
end Interaction
