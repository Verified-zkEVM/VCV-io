/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Multiparty.Core

/-!
# Directed point-to-point multiparty interaction

This file specializes `Interaction.Multiparty.Core` to the communication model
where each node carries an ordered pair of parties:
an active sender and a designated receiver.

The intended semantics are:
* the sender chooses the next move;
* the designated receiver observes that chosen move;
* all remaining parties are hidden from that node unless a richer resolver says
  otherwise.

This is the native `Interaction` formulation of directed communication.
Unlike the broadcast model, only one non-sender party receives the chosen move,
and the remaining parties need not even learn which branch was taken at that
step.
-/

universe u

namespace Interaction
namespace Multiparty
namespace Directed

/--
An `EdgeDecoration Party spec` labels each internal node of `spec` by an
ordered pair `(src, dst)` of parties.

The intended semantics are directed point-to-point communication:
`src` chooses the next move, `dst` receives that move, and all other parties
are locally hidden at that node unless a richer resolver specifies a quotient
observation.
-/
abbrev EdgeDecoration (Party : Type u) :=
  Spec.Decoration (fun _ => Party × Party)

/--
`Directed.Strategy m spec edges resolve Output` is the local endpoint type for
one fixed participant in the directed communication model.

At each node, the ordered pair `(src, dst)` recorded by `edges` is passed to
`resolve`, which determines whether the fixed participant is:
* the active sender,
* the designated full observer,
* or a hidden or partially informed outsider.

For concrete finite party types, resolvers are intended to be defined by
pattern matching on `(src, dst)`. This preserves definitional reduction of the
resulting endpoint types, especially in examples and endpoint computations.
-/
abbrev Strategy
    (m : Type u → Type u)
    {Party : Type u}
    (spec : Spec) (edges : EdgeDecoration Party spec)
    (resolve : ∀ {X : Type u}, Party → Party → LocalView X)
    (Output : Spec.Transcript spec → Type u) :=
  Multiparty.Strategy m
    (resolve := fun X edge => resolve (X := X) edge.1 edge.2) spec edges Output

end Directed
end Multiparty
end Interaction
