/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Node
import VCVio.Interaction.Basic.Decoration

/-!
# Generic local syntax over interaction trees

This file introduces the most general local syntax layer in the `Interaction`
framework.

`Spec.SyntaxOver` is the base local-syntax object:
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

`Spec.ShapeOver` in `Basic/Shape` is the functorial refinement of this base
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

universe u a vΓ w uA uB uA₂ uB₂ t

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

variable {Agent : Type a} {Γ : P.A → Type vΓ}

end SyntaxOver

variable {Agent : Type a} {Γ : P.A → Type vΓ}

/--
Whole-tree local strategy induced by lens-indexed local syntax.

At leaves it returns the output family. At a control node it presents the local
node object supplied by `syn`, whose continuation family is recursively the
strategy for the abstract branch selected by the lens.
-/
def StrategyOver {l : PFunctor.Lens P Q}
    (syn : SyntaxOver l Agent Γ) :
    (agent : Agent) →
    (spec : PFunctor.FreeM P α) →
    Decoration Γ spec →
    (PFunctor.FreeM.PathAlong l spec → Type w) →
    Type w
  | _, .pure _, _, Out => Out ⟨⟩
  | agent, .roll pos rest, ⟨γ, ctxs⟩, Out =>
      syn.Node agent pos γ (fun d =>
        StrategyOver syn agent (rest (l.toFunB pos d)) (ctxs (l.toFunB pos d))
          (fun path => Out ⟨d, path⟩))

namespace Spec

variable {Agent : Type a}
variable {Γ : Node.Context}

/--
`SyntaxOver Agent Γ` is the most general local-syntax object in the
interaction framework.

It answers the following question:

> Suppose we are standing at one protocol node whose move space is `X`.
> The node carries realized node-local context `γ : Γ X`.
> If the protocol continues with family `Cont : X → Type w`, what is the type
> of the local object that agent `a` stores at this node?

So a `SyntaxOver` does **not** describe a whole protocol tree.
It describes the type of one local node object, uniformly for every possible:
* agent,
* move space,
* realized node-local context,
* continuation family.

The whole-tree notion is obtained later by structural recursion on `Spec` via
`StrategyOver`.

This is the most general local syntax layer because:
* binary and multiparty interaction are both recovered by the choice of
  `Agent`;
* role-based interaction is recovered by choosing an appropriate context
  family `Γ`, for example `Γ := fun _ => Role`;
* richer staged metadata can be assembled via `Spec.Node.Schema` and then
  consumed through its realized context `Spec.Node.Schema.toContext`;
* the undecorated case is recovered by taking `Γ = Spec.Node.Context.empty`;
* no functoriality assumption is imposed on recursive continuations.
-/
structure SyntaxOver
    (Agent : Type a)
    (Γ : Node.Context) where
  /--
  `Node a X γ Cont` is the type of the local object held by agent `a`
  at a node with:
  * move space `X`,
  * realized node-local context `γ : Γ X`,
  * continuation family `Cont : X → Type w`.

  The continuation is indexed by the next move `x : X`, because after choosing
  `x` the protocol does not continue in one fixed type: it continues in the
  subtree corresponding to that specific move.
  -/
  Node :
    (agent : Agent) →
    (X : Type u) →
    (γ : Γ X) →
    (X → Type w) →
    Type w

/--
`Syntax Agent` is the specialization of `SyntaxOver` with no node-local
context.

This is the right facade when the protocol tree carries no node metadata at
all. Equivalently, it is `SyntaxOver Agent Spec.Node.Context.empty`.
-/
abbrev Syntax
    (Agent : Type a) :=
  SyntaxOver Agent Node.Context.empty

/--
Reindex a local syntax object contravariantly along a node-context morphism.

If `f : Γ → Δ`, then any syntax over `Δ` can be viewed as syntax over `Γ` by
first translating the local context value `γ : Γ X` into `f X γ : Δ X` and
then using the original `Δ`-syntax there.

So `SyntaxOver` is contravariant in its context parameter.
-/
def SyntaxOver.comap {Δ : Node.Context}
    (f : Node.ContextHom Γ Δ) (syn : SyntaxOver Agent Δ) :
    SyntaxOver Agent Γ where
  Node agent X γ Cont := syn.Node agent X (f X γ) Cont

/--
Reindex a local syntax object contravariantly along a schema morphism, using
the underlying realized context morphism.
-/
abbrev SyntaxOver.comapSchema
    {Δ : Node.Context} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (f : Node.Schema.SchemaMap S T) (syn : SyntaxOver Agent Δ) :
    SyntaxOver Agent Γ :=
  SyntaxOver.comap f.toContextHom syn

@[simp]
theorem SyntaxOver.comap_id
    (syn : SyntaxOver Agent Γ) :
    SyntaxOver.comap (Node.ContextHom.id Γ) syn = syn := by
  cases syn
  rfl

theorem SyntaxOver.comap_comp
    {Δ : Node.Context} {Λ : Node.Context}
    (syn : SyntaxOver Agent Λ)
    (g : Node.ContextHom Δ Λ) (f : Node.ContextHom Γ Δ) :
    SyntaxOver.comap f (SyntaxOver.comap g syn) =
      SyntaxOver.comap (Node.ContextHom.comp g f) syn := by
  cases syn
  rfl

/--
`StrategyOver syn a spec ctxs Out` is the whole-tree local strategy
for agent `a` induced by the one-node syntax `syn`.

Inputs:
* `spec` is the underlying protocol tree;
* `ctxs : Decoration Γ spec` assigns a realized node context to each node;
* `Out : Transcript spec → Type w` is the final output family at leaves.

The result is obtained by structural recursion on `spec`:
* at a leaf, the family is just the leaf output `Out`;
* at an internal node, the family is `syn.Node ...` applied to the
  recursively defined continuation family for each child subtree.

So `SyntaxOver` is local and one-step, while `StrategyOver` is the induced
whole-tree object for one agent.
-/
def StrategyOver
    (syn : SyntaxOver Agent Γ) :
    (agent : Agent) →
    (spec : Spec) →
    Decoration Γ spec →
    (Transcript spec → Type w) →
    Type w
  | _, .done, _, Out => Out ⟨⟩
  | agent, .node X next, ⟨γ, ctxs⟩, Out =>
      syn.Node agent X γ (fun x =>
        StrategyOver syn agent (next x) (ctxs x) (fun tr =>
          Out ⟨x, tr⟩))

/-- At an internal node, `StrategyOver` unfolds to the local node object
whose continuations are the recursively induced strategies for each child. -/
theorem StrategyOver.node
    (syn : SyntaxOver Agent Γ)
    {agent : Agent} {X : Type u} {next : X → Spec}
    {γ : Γ X} {ctxs : (x : X) → Decoration Γ (next x)}
    {Out : Transcript (Spec.node X next) → Type w} :
    StrategyOver syn agent (Spec.node X next) ⟨γ, ctxs⟩ Out =
      syn.Node agent X γ (fun x =>
        StrategyOver syn agent (next x) (ctxs x) (fun tr => Out ⟨x, tr⟩)) :=
  rfl

/--
Whole-tree families for `SyntaxOver.comap f syn` are exactly families for `syn`
evaluated on the mapped decoration `Decoration.map f ctxs`.
-/
theorem StrategyOver.comap {Δ : Node.Context}
    (syn : SyntaxOver Agent Δ) (f : Node.ContextHom Γ Δ) :
    {agent : Agent} → {spec : Spec} → (ctxs : Decoration Γ spec) →
    {Out : Transcript spec → Type w} →
    StrategyOver (SyntaxOver.comap f syn) agent spec ctxs Out =
      StrategyOver syn agent spec (Decoration.map f spec ctxs) Out
  | _, .done, _, _ => rfl
  | agent, .node _ next, ⟨γ, ctxs⟩, Out => by
      simp only [StrategyOver, SyntaxOver.comap, Decoration.map]
      congr 1
      funext x
      exact StrategyOver.comap syn f (agent := agent) (ctxs := ctxs x)

theorem StrategyOver.comapSchema
    {Δ : Node.Context} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (syn : SyntaxOver Agent Δ) (f : Node.Schema.SchemaMap S T) :
    {agent : Agent} → {spec : Spec} → (ctxs : Decoration Γ spec) →
    {Out : Transcript spec → Type w} →
    StrategyOver (SyntaxOver.comapSchema f syn) agent spec ctxs Out =
      StrategyOver syn agent spec (Decoration.Schema.map f spec ctxs) Out :=
  StrategyOver.comap syn f.toContextHom

end Spec
end Interaction
