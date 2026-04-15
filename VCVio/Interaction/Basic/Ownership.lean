/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Syntax

/-!
# Owner-based local syntax builders

This module provides a small derived API for building `Spec.SyntaxOver`
objects from two ingredients:

* an `owner` function saying which agent controls a node;
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
namespace Spec
namespace Ownership

variable {Agent : Type a}
variable {Γ : Node.Context}

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
Build a `SyntaxOver` from an owner function and participant-local views.

If `owner γ = a`, then agent `a` uses its `own` shape at context `γ`, while
every other agent uses its `other` shape there.
-/
def syntaxOver [DecidableEq Agent]
    (owner : ∀ {X}, Γ X → Agent)
    (view : ∀ {X}, (γ : Γ X) → Agent → LocalView X) :
    SyntaxOver Agent Γ where
  Node agent _ γ Cont :=
    if agent = owner γ then
      (view γ agent).own Cont
    else
      (view γ agent).other Cont

end Ownership
end Spec
end Interaction
