/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Multiparty.Core

/-!
# Broadcast / public-transcript multiparty interaction

This file specializes `Interaction.Multiparty.Core` to the communication model
where each node has one distinguished acting party, and every other party
observes the same chosen move.

This is the natural native model for public-transcript protocols:
one party speaks at each step, and all other parties continue along the same
observed branch.

The node metadata for this model is simply the acting party itself.
A fixed participant's endpoint is then obtained by supplying a resolver from
acting parties to `LocalView`.

For concrete finite party types, resolvers are intended to be written by
pattern matching. This preserves the strongest definitional behavior of the
resulting endpoint types.
-/

universe u

namespace Interaction
namespace Multiparty
namespace Broadcast

/--
A `PartyDecoration Party spec` labels each internal node of `spec` by its
unique acting party.

The intended semantics are broadcast / public-transcript:
the labeled party chooses the next move, and every other participant observes
that same move and continues along the corresponding branch.
-/
abbrev PartyDecoration (Party : Type u) :=
  Spec.Decoration (fun _ => Party)

/--
`Broadcast.Strategy m spec parties resolve Output` is the local endpoint type
for one fixed participant in the broadcast model.

At each node, the acting party recorded by `parties` is passed to `resolve`,
which determines how the fixed participant locally sees that node.

Typical broadcast resolvers use only:
* `LocalView.active` at the participant's own nodes, and
* `LocalView.observe` at all other nodes.

But the definition itself is intentionally more general: it exposes the full
`LocalView` interface rather than hard-coding one particular resolver.
-/
abbrev Strategy
    (m : Type u → Type u)
    {Party : Type u}
    (spec : Spec) (parties : PartyDecoration Party spec)
    (resolve : ∀ {X : Type u}, Party → LocalView X)
    (Output : Spec.Transcript spec → Type u) :=
  Multiparty.Strategy m (resolve := fun X owner => resolve (X := X) owner) spec parties Output

end Broadcast
end Multiparty
end Interaction
