/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.Basic.Node

/-!
# Generic local syntax over interaction trees

This file introduces the most general local syntax layer in the `Interaction`
framework.

`SyntaxOver` is the base local-syntax object:
it says what kind of node object an agent has at one protocol node, as a
function of
* the agent,
* the move space at that node,
* the realized node-local context available there, and
* the continuation family after each possible move.

Crucially, `SyntaxOver` does **not** require any functorial action on
continuations. This matters because many important interaction nodes hide their
recursive continuations under outer constructors such as monads, oracle
queries, state transitions, or other effect wrappers. Such nodes are valid
local syntax, but they need not support a generic continuation map.

`ShapeOver` in `Basic/Shape` is the functorial refinement of this base
notion: it adds continuation reindexing when the local syntax really does
support it.

Role-based APIs are specializations of this pattern:
* `Spec.Node.Context` is the semantic family of node-local data;
* `Spec.Node.Schema` is the telescope-style front-end for building such
  contexts;
* `Spec.Node.ContextHom` and `SyntaxOver.comap` express contravariant
  reindexing of local syntax along context morphisms;
* `fun _ => Role` is one example of a simple node context;
* `StrategyOver` is the whole-tree local strategy induced by one-node syntax.

Naming note:
`SyntaxOver` is the base local-syntax notion. `ShapeOver` uses the same suffix
to signal that it is the functorial refinement of syntax, with continuation
reindexing available as part of the interface.
-/

universe u a vΓ vΔ vΛ w uA uB uA₂ uB₂ t

namespace Interaction

open PFunctor

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
variable {α : Type t}

/--
`SyntaxOver l Agent Γ` is local syntax over an arbitrary control polynomial
executed through a runtime lens `l`.

At control position `pos : P.A`, node metadata has type `Γ pos`, while the
local continuation family is indexed by runtime directions
`Q.B (l.toFunA pos)`. The lens maps each runtime direction back to the
abstract control branch used for recursion.
-/
structure SyntaxOver
    (l : PFunctor.Lens P Q)
    (Agent : Type a)
    (Γ : P.A → Type vΓ) where
  Node :
    (agent : Agent) →
    (pos : P.A) →
    (γ : Γ pos) →
    (Q.B (l.toFunA pos) → Type w) →
    Type w

namespace SyntaxOver

variable {l : PFunctor.Lens P Q}
variable {Agent : Type a}
variable {Γ : P.A → Type vΓ}

/--
Reindex a local syntax object contravariantly along a node metadata map.

If `f : Γ → Δ`, then any syntax over `Δ` can be viewed as syntax over `Γ` by
translating the local metadata value before passing it to the original syntax.
-/
def comap {Δ : P.A → Type vΔ}
    (f : ∀ pos, Γ pos → Δ pos) (syn : SyntaxOver l Agent Δ) :
    SyntaxOver l Agent Γ where
  Node agent pos γ Cont := syn.Node agent pos (f pos γ) Cont

@[simp]
theorem comap_id (syn : SyntaxOver l Agent Γ) :
    comap (fun _ γ => γ) syn = syn := by
  cases syn
  rfl

theorem comap_comp {Δ : P.A → Type vΔ} {Λ : P.A → Type vΛ}
    (syn : SyntaxOver l Agent Λ)
    (g : ∀ pos, Δ pos → Λ pos) (f : ∀ pos, Γ pos → Δ pos) :
    comap f (comap g syn) = comap (fun pos => g pos ∘ f pos) syn := by
  cases syn
  rfl

/--
Restrict a participant-indexed syntax to one fixed agent.

The resulting singleton-agent syntax has the same node objects as `syn` at
`agent`; the dummy `PUnit` agent argument is ignored.
-/
def forAgent (syn : SyntaxOver l Agent Γ) (agent : Agent) :
    SyntaxOver l PUnit Γ where
  Node _ pos γ Cont := syn.Node agent pos γ Cont

end SyntaxOver


namespace Spec

variable {Agent : Type a}
variable {Γ : Node.Context.{u, vΓ}}

/--
`Syntax Agent` is the specialization of generic `SyntaxOver` to plain `Spec`
trees with no node-local context.

This is the right facade when the protocol tree carries no node metadata at
all.
-/
abbrev Syntax
    (Agent : Type a) :=
  SyntaxOver (PFunctor.Lens.id Spec.basePFunctor) Agent Node.Context.empty

end Spec
end Interaction
