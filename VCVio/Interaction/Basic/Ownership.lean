/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.BundledMonad
import VCVio.Interaction.Basic.Syntax

/-!
# Ownership-profile local syntax builders

This module provides a small derived API for building `Spec.SyntaxOver`
objects from two ingredients:

* a `perspective` function saying whether an agent owns or observes a node;
* a participant-local `LocalView` describing what that agent stores when it
  owns the node versus when it merely observes someone else's move.

This does **not** replace `SyntaxOver` or `InteractionOver`.
It is only a structured way to construct common owner-driven interaction
patterns on top of the generic core.

In particular, this layer is useful for two-party and multiparty interaction
models where every node has one acting party and the other parties follow the
chosen move with their passive continuations.
-/

universe u a vΓ

namespace Interaction

namespace Ownership

open PFunctor

universe uA uB uA₂ uB₂ w

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
variable (l : PFunctor.Lens P Q)

/-- Whether an agent owns a node or observes another agent's move there. -/
inductive Perspective where
  | owner
  | observer

/--
`LocalView Move` describes one agent's node object shape at a node whose
runtime directions have type `Move`.
-/
structure LocalView (Move : Type uB₂) where
  own : (Move → Type w) → Type w
  other : (Move → Type w) → Type w

/-- Select the local node shape determined by an ownership perspective. -/
def LocalView.node {Move : Type uB₂} (view : LocalView.{uB₂, w} Move) :
    Perspective → (Move → Type w) → Type w
  | .owner, Cont => view.own Cont
  | .observer, Cont => view.other Cont

/-- The standard monadic owner/passive local view. -/
def LocalView.monadic (bm : BundledMonad.{w, w}) (Move : Type w) :
    LocalView.{w, w} Move where
  own Cont := bm.M ((d : Move) × Cont d)
  other Cont := (d : Move) → bm.M (Cont d)

/--
Public-coin owner/passive local view, exposing the owned sampler separately
from its continuation family.
-/
def LocalView.publicCoin (bm : BundledMonad.{w, w}) (Move : Type w) :
    LocalView.{w, w} Move where
  own Cont := bm.M Move × ((d : Move) → Cont d)
  other Cont := (d : Move) → bm.M (Cont d)

variable {Agent : Type a} {Γ : P.A → Type vΓ}

/--
Build lens-indexed local syntax from a node-local ownership profile and
participant-local views.
-/
def syntaxOver
    (perspective : {pos : P.A} → Γ pos → Agent → Perspective)
    (view :
      {pos : P.A} → (γ : Γ pos) → Agent →
        LocalView.{uB₂, w} (Q.B (l.toFunA pos))) :
    SyntaxOver l Agent Γ where
  Node agent _ γ Cont :=
    (view γ agent).node (perspective γ agent) Cont

/-- Monadic owner/passive syntax over a lens-executed tree. -/
def monadicSyntax
    (perspective : {pos : P.A} → Γ pos → Agent → Perspective)
    (monad :
      {pos : P.A} → Γ pos → Agent →
        BundledMonad.{max uB₂ w, max uB₂ w}) :
    SyntaxOver l Agent Γ where
  Node agent pos γ Cont :=
    match perspective γ agent with
    | .owner =>
      (monad γ agent).M ((d : Q.B (l.toFunA pos)) × Cont d)
    | .observer =>
      (d : Q.B (l.toFunA pos)) → (monad γ agent).M (Cont d)

end Ownership

namespace Spec
namespace Ownership

variable {Agent : Type a}
variable {Γ : Node.Context}

/-- Whether an agent owns a node or observes another agent's move there. -/
inductive Perspective where
  | owner
  | observer

/--
`LocalView X` is the local participant interface at one move space `X`.

It separates the node shape seen by an agent when that agent owns the node
from the node shape seen when someone else owns the node.

The owned shape is intentionally unconstrained here. In particular, the common
base owned-node form
`m ((x : X) × Cont x)`
is just one important specialization of `LocalView`, not a hard-coded part of
the generic syntax core.
-/
structure LocalView (X : Type u) where
  /-- The node representation used when the agent owns the current node. -/
  own : (X → Type u) → Type u
  /-- The node representation used when some other agent owns the current node. -/
  other : (X → Type u) → Type u

/-- Select the local node shape determined by an ownership perspective. -/
def LocalView.node {X : Type u} (view : LocalView X) :
    Perspective → (X → Type u) → Type u
  | .owner, Cont => view.own Cont
  | .observer, Cont => view.other Cont

/--
The standard monadic owner/passive local view.

Owners produce an effectful move and continuation. Observers react
effectfully to every possible move.
-/
def LocalView.monadic (bm : BundledMonad.{u, u}) (X : Type u) :
    LocalView X where
  own Cont := bm.M ((x : X) × Cont x)
  other Cont := (x : X) → bm.M (Cont x)

/--
Public-coin owner/passive local view.

The observing side has the same shape as in `LocalView.monadic`. The owning
side exposes the sampler separately from the continuation family, so replay can
ignore the sampler and follow a prescribed public move.
-/
def LocalView.publicCoin (bm : BundledMonad.{u, u}) (X : Type u) :
    LocalView X where
  own Cont := bm.M X × ((x : X) → Cont x)
  other Cont := (x : X) → bm.M (Cont x)

/--
`LocalRunner m V` gives the operational interpretation of a local view `V`
inside an ambient monad `m`.

It explains:
* how an owned node produces the chosen move together with the matching
  continuation;
* how a passive node follows a move chosen elsewhere.
-/
structure LocalRunner
    (m : Type u → Type u)
    {X : Type u}
    (V : LocalView X) where
  /-- Execute an owned node, producing the chosen move and continuation. -/
  runOwn :
    {Cont : X → Type u} →
    V.own Cont →
    m ((x : X) × Cont x)
  /-- Execute a passive node after the owner has chosen move `x`. -/
  runOther :
    {Cont : X → Type u} →
    V.other Cont →
    (x : X) → m (Cont x)

/--
Build a `SyntaxOver` from a node-local ownership profile and participant-local
views.

Concrete protocols should define `perspective` by pattern matching on their
node metadata and agent constructors. This keeps owner/observer node shapes in
the definitional hot path and avoids equality tests such as
`if agent = owner γ`.
-/
def syntaxOver
    (perspective : ∀ {X}, Γ X → Agent → Perspective)
    (view : ∀ {X}, (γ : Γ X) → Agent → LocalView X) :
    SyntaxOver Agent Γ where
  Node agent _ γ Cont :=
    (view γ agent).node (perspective γ agent) Cont

/-- Monadic owner/passive syntax over plain `Spec` trees. -/
def monadicSyntax
    (perspective : ∀ {X}, Γ X → Agent → Perspective)
    (monad : ∀ {X}, Γ X → Agent → BundledMonad.{u, u}) :
    SyntaxOver Agent Γ where
  Node agent X γ Cont :=
    match perspective γ agent with
    | .owner => (monad γ agent).M ((x : X) × Cont x)
    | .observer => (x : X) → (monad γ agent).M (Cont x)

end Ownership
end Spec
end Interaction
