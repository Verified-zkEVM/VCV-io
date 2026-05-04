/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Append

/-!
# Platonic chain primitive (`Spec.Telescope`)

`Telescope round step` is the *initial algebra* of the segment functor that
extends a protocol by one round whose spec depends on the current state and
then transitions to a new state determined by the round's transcript.

Given
* a state space `St : Type v`,
* a round assignment `round : St → Spec.{u}`,
* a state transition `step : (s : St) → Transcript (round s) → St`,

an inhabitant of `Telescope round step s₀` is a finite tree of `extend` steps
ending in `done`. The construction is well-founded by virtue of being an
inductive: there is no way to construct an infinite-depth instance, so
inhabitation is itself a constructive termination proof for the underlying
state machine.

## Universal property

`Telescope round step` is the carrier of the initial `(round, step)`-algebra
in the slice category over `St`: for any other `(round, step)`-algebra
`(P : St → Type _, alg)`, there is a unique structure-preserving map
`Telescope round step → P` given by structural recursion on the inductive.
`toSpec` is one such recursion, with target algebra
`(fun _ => Spec, .done, fun s cont => (round s).append cont)`.

## References

* Hancock–Setzer (2000), recursion over interaction interfaces.
* Spivak–Niu (2024), polynomial functors as the algebra of interaction.
-/

universe u v

namespace Interaction
namespace Spec

/-- Initial-algebra presentation of a state-machine telescope of `Spec`s.

At each state `s : St`, an inhabitant either terminates (`.done s`) or extends
by running the round `round s : Spec` and recursing into
`Telescope round step (step s tr)` for every transcript `tr`. As an inductive
type, every inhabitant is finite, so the existence of a `Telescope` term is a
proof that the underlying state machine terminates. -/
inductive Telescope {St : Type v}
    (round : St → Spec.{u})
    (step : (s : St) → Transcript (round s) → St) : St → Type (max u v)
  | done (s : St) : Telescope round step s
  | extend (s : St)
      (cont : (tr : Transcript (round s)) → Telescope round step (step s tr)) :
      Telescope round step s

namespace Telescope

variable {St : Type v} {round : St → Spec.{u}}
    {step : (s : St) → Transcript (round s) → St}

/-- Flatten a `Telescope` into a concrete `Spec` by iterated `Spec.append`.
Each `extend` step contributes its round spec to the head, with the tail
expanding through the recursive continuation. -/
def toSpec : {s : St} → Telescope round step s → Spec
  | _, .done _ => .done
  | _, .extend s cont => (round s).append fun tr => (cont tr).toSpec

@[simp, grind =]
theorem toSpec_done (s : St) :
    (Telescope.done (round := round) (step := step) s).toSpec = .done := rfl

@[simp, grind =]
theorem toSpec_extend (s : St)
    (cont : (tr : Transcript (round s)) → Telescope round step (step s tr)) :
    (Telescope.extend s cont).toSpec =
      (round s).append (fun tr => (cont tr).toSpec) := rfl

end Telescope
end Spec
end Interaction
