/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Multiparty.Core

/-!
# Per-party local-view profiles for multiparty interaction

This file packages the most structured native multiparty interface built on top
of `Interaction.Multiparty.Core`.

A node of move space `X` is decorated not merely by one local view, but by a
whole profile assigning each party its own `LocalView X`. The endpoint of one
fixed party is then obtained by projecting that profile to the chosen party.

This is the most direct structured way to describe multiparty nodes with:
* one active controller of the move;
* parties that observe the full move;
* parties that observe only a quotient of the move; and
* parties that observe nothing at all.
-/

universe u

namespace Interaction
namespace Multiparty
namespace Profile

/--
`ViewProfile Party X` assigns to each party its local view of a node whose move
space is `X`.

This is the intended structured node-local metadata for adversarial and
multiparty interaction: one actual global move may give different local
observations to different parties.
-/
abbrev ViewProfile (Party : Type u) : Spec.Node.Context.{u, u + 1} :=
  fun X => Party → LocalView X

/--
A `Decoration Party spec` assigns one local-view profile to every node of
`spec`.

At a node with move space `X`, the attached profile says, for each party, how
that party locally sees the chosen move `x : X`.
-/
abbrev Decoration (Party : Type u) :=
  Spec.Decoration (ViewProfile Party)

/--
`Profile.Strategy m me spec views Output` is the local endpoint type of the
fixed party `me` under the local-view profiles recorded by `views`.

This is obtained by projecting each node's full per-party profile to the view
of `me`, then reusing the generic multiparty `Strategy`.
-/
abbrev Strategy
    (m : Type u → Type u)
    {Party : Type u}
    (me : Party)
    (spec : Spec) (views : Decoration Party spec)
    (Output : Spec.Transcript spec → Type u) :=
  Multiparty.Strategy m (resolve := fun _ profile => profile me) spec views Output

end Profile
end Multiparty
end Interaction
