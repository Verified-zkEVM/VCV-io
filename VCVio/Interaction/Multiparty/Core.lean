/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Syntax

/-!
# Native local views for multiparty interactions

This file introduces the smallest common local layer for multiparty
interaction in the `Interaction` framework.

The current two-party layer distinguishes between:
* the side that chooses the next move, and
* the side that receives that chosen move.

For adversarial and multiparty interaction, this is still not the whole story.
Besides:
* choosing the move,
* observing the full move, and
* observing nothing at all,

a participant may observe only a **quotient** or **projection** of the chosen
move. For example, a party might learn that a message was delivered on a given
channel without learning the payload itself.

The definitions in this file are intentionally local and minimal.

* `LocalView X` records how one fixed participant locally sees a chosen move
  `x : X` at one node.
* `LocalView.Action` is the canonical local node shape associated to that view.
* `localSyntax` packages that local node shape as a `Spec.SyntaxOver`.
* `Strategy` is the induced whole-tree local endpoint type, obtained from
  arbitrary node-local metadata through `SyntaxOver.comap`.

Crucially, this file does **not** commit to any particular global communication
model. In particular, it does not choose between:
* broadcast / public-transcript interaction, where one party chooses and all
  others observe; or
* directed point-to-point interaction, where one party sends, one party
  receives, and the remaining parties are hidden or only partially informed.

Those models are recovered later by choosing different node decorations and
different resolvers.

Naming note:
this file does not introduce a new global multiparty protocol syntax. The
existing `Interaction.Spec` already captures the global branching structure.
The multiparty layer only describes how one fixed participant locally sees each
node of such a spec.
-/

universe u v

namespace Interaction
namespace Multiparty

/--
`LocalView X` is the local observation mode of one fixed participant at one
protocol node whose move space is `X`.

It answers the following question:

> Once a global protocol node has been fixed, how does the chosen participant
> locally experience the actual chosen move `x : X` of that node?

The possibilities are:
* `active` — this participant chooses the next move;
* `observe` — this participant is told the full chosen move and continues after
  seeing it;
* `hidden` — this participant is not told the chosen move at the node itself,
  so any future behavior depending on that move must already be prepared
  uniformly over all possible moves;
* `quotient Obs toObs` — this participant is told only the observation
  `toObs x : Obs`, not the full move `x`.

`LocalView` is intentionally local. It does not describe the global
communication discipline that produced it, nor who else sees the move.
-/
inductive LocalView (X : Type u) : Type (u + 1) where
  | active
  | observe
  | hidden
  | quotient (Obs : Type u) (toObs : X → Obs)

namespace LocalView

/--
`ObsType view` is the type of concrete observations made by a participant with
local view `view` when some actual move `x` occurs.

Reading by cases:
* for `active` and `observe`, the participant learns the full move;
* for `hidden`, the participant learns nothing (`PUnit`);
* for `quotient Obs toObs`, the participant learns only the quotient
  observation `toObs x : Obs`.

This packages the information content of a `LocalView` independently from the
more structured endpoint semantics of `LocalView.Action`.
-/
def ObsType {X : Type u} : LocalView X → Type u
  | .active => X
  | .observe => X
  | .hidden => PUnit
  | .quotient Obs _ => Obs

/--
`obsOf view x` is the concrete observation exposed by local view `view` when
the actual move was `x`.

This forgets any control or continuation structure and keeps only the
information that is revealed:
* `active` and `observe` reveal the full move;
* `hidden` reveals nothing;
* `quotient Obs toObs` reveals `toObs x`.
-/
def obsOf {X : Type u} : (view : LocalView X) → X → view.ObsType
  | .active, x => x
  | .observe, x => x
  | .hidden, _ => PUnit.unit
  | .quotient _ toObs, x => toObs x

/--
`LocalView.Action view m Cont` is the canonical local node type for a fixed
participant with local view `view` at a node whose move space is `X`.

Interpretation by cases:
* if `view = active`, the participant effectfully selects a move `x : X` and
  produces the matching continuation;
* if `view = observe`, the participant waits for the externally chosen move
  and then produces the continuation for that move;
* if `view = hidden`, the participant does not observe the chosen move at this
  node, so it must effectfully prepare an entire family of continuations, one
  for each possible move;
* if `view = quotient Obs toObs`, the participant is told only an observation
  `o : Obs`; it must then effectfully provide continuations for every move
  whose observation agrees with `o`.

This is the native multiparty analogue of `Interaction.Role.Action` from the
two-party layer, extended by hidden and partial-observation cases.
-/
def Action {X : Type u} (view : LocalView X) (m : Type u → Type u)
    (Cont : X → Type u) : Type u :=
  match view with
  | .active => m ((x : X) × Cont x)
  | .observe => (x : X) → m (Cont x)
  | .hidden => m ((x : X) → Cont x)
  | .quotient Obs toObs => (o : Obs) → m ((x : X) → toObs x = o → Cont x)

end LocalView

/--
`LocalViewContext` is the plain node context whose metadata at each node is
just one `LocalView` of that node's move space.

This is the direct multiparty local-view analogue of the two-party
`RoleContext`.
More structured multiparty models usually decorate nodes by richer metadata and
then project that metadata to `LocalView` via `SyntaxOver.comap`.
-/
abbrev LocalViewContext : Spec.Node.Context.{u, u + 1} := fun X : Type u => LocalView X

/--
`localSyntax m` is the fundamental local syntax for one fixed participant when
the node metadata already is that participant's `LocalView`.

At a node with move space `X`, view `v : LocalView X`, and continuation family
`Cont : X → Type`, the local node object is exactly `v.Action m Cont`.

This syntax uses the singleton agent type `PUnit`, because it describes the
endpoint of one fixed participant viewpoint rather than a whole participant
profile.
-/
def localSyntax (m : Type u → Type u) :
    Spec.SyntaxOver (PUnit : Type) (fun X : Type u => LocalView X) where
  Node _ _ view Cont := view.Action m Cont

/--
`Strategy m resolve spec ctxs Output` is the whole-tree local endpoint type for
one fixed participant in a multiparty interaction.

Inputs:
* `Γ` is any chosen node-local metadata context;
* `resolve : Γ → LocalView` explains how the fixed participant locally sees a
  node carrying metadata `γ : Γ X`;
* `ctxs : Spec.Decoration Γ spec` supplies that metadata across the protocol
  tree.

The endpoint type is then obtained by reusing `localSyntax m` through
`SyntaxOver.comap resolve`.

So a `Strategy` here is **not** a global profile of all participants.
It is the projected local behavior of one chosen participant viewpoint.
Different multiparty communication models are recovered by choosing different
metadata contexts `Γ`, decorations `ctxs`, and resolvers `resolve`.
-/
abbrev Strategy
    (m : Type u → Type u)
    {Γ : Spec.Node.Context.{u, v}}
    (resolve : Spec.Node.ContextHom Γ (fun X : Type u => LocalView X))
    (spec : Spec) (ctxs : Spec.Decoration Γ spec)
    (Output : Spec.Transcript spec → Type u) :=
  Spec.SyntaxOver.Family ((localSyntax m).comap resolve) PUnit.unit spec ctxs Output

end Multiparty
end Interaction
