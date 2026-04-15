/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Node
import VCVio.Interaction.Basic.Syntax
import VCVio.Interaction.Basic.Shape

/-!
# Generic local execution laws over interaction trees

This file introduces the execution-side counterpart to `Spec.SyntaxOver`.

`Spec.InteractionOver` is a local operational law for agent-indexed node
objects. It says how a whole profile of local objects, one for each agent, is
combined at a single protocol node in order to choose the next move and
continue the interaction. The node-local information seen by those objects is
packaged as a realized `Spec.Node.Context`.

The role-based prover/verifier runners used elsewhere in the library are
specializations of this more general notion, obtained by choosing suitable
node contexts and syntax objects.

Just as `SyntaxOver` reindexes contravariantly along node-context morphisms,
`InteractionOver.comap` transports a local execution law along the same kind
of context change.

Naming note:
`InteractionOver` keeps the suffix form for the same reason as `ShapeOver`:
it is the primary generalized execution notion, while `Interaction` is its
trivial-data specialization rather than a base value that `InteractionOver`
depends on.
-/

universe u a vΓ w

namespace Interaction
namespace Spec

variable {Agent : Type a}
variable {Γ : Node.Context}

/--
`InteractionOver Agent Γ syn m` is the most general local execution
law for agent-indexed participant objects.

It answers the following question:

> Suppose we are standing at one protocol node with move space `X`.
> Every agent `a` has a local node object of type
> `syn.Node a X γ (Cont a)`.
> How do we execute this node, choose the next move `x : X`, and continue with
> the continuation values of all agents at that `x`?

So:
* `SyntaxOver` describes the **local syntax** available to each agent;
* `InteractionOver` describes the **local operational semantics** for one
  protocol step built from that syntax.

This is the level at which the execution discipline lives:
who chooses the move, how it is sampled or observed, how the local node objects
synchronize, and how effects in `m` are used.
-/
structure InteractionOver
    (Agent : Type a)
    (Γ : Node.Context)
    (syn : SyntaxOver Agent Γ)
    (m : Type w → Type w) where
  /--
  `interact` executes one protocol node.

  Inputs:
  * a move space `X`;
  * realized node-local context `γ : Γ X`;
  * for each agent `a`, a local node object
    `syn.Node a X γ (Cont a)`;
  * a continuation `k` explaining how to proceed once a move `x : X` has been
    chosen and each agent supplies its continuation value at that `x`.

  Output:
  * one monadic step of type `m Result`.

  In other words, `interact` is the one-step execution rule for the whole
  agent profile at this node.
  -/
  interact :
    {X : Type u} →
    {γ : Γ X} →
    {Cont : Agent → X → Type w} →
    {Result : Type w} →
    ((agent : Agent) → syn.Node agent X γ (Cont agent)) →
    ((x : X) → ((agent : Agent) → Cont agent x) → m Result) →
    m Result

/--
`Interaction Agent syn m` is the specialization of `InteractionOver` with no
node-local context.

This is the right facade when the protocol tree carries no node metadata at
all. Equivalently, it is
`InteractionOver Agent Spec.Node.Context.empty syn m`.
-/
abbrev Interaction
    (Agent : Type a)
    (syn : Syntax Agent)
    (m : Type w → Type w) :=
  InteractionOver Agent Node.Context.empty syn m

/--
Reindex a local execution law contravariantly along a node-context morphism.

If `f : Γ → Δ`, then an execution law for `Δ`-contexts can be reused on
`Γ`-contexts by first viewing the local syntax through `SyntaxOver.comap f`.
At each node, the translated context value `f X γ` is what the original
execution law sees.
-/
def InteractionOver.comap {Δ : Node.Context} {syn : SyntaxOver Agent Δ}
    {m : Type w → Type w}
    (I : InteractionOver Agent Δ syn m) (f : Node.ContextHom Γ Δ) :
    InteractionOver Agent Γ (syn.comap f) m where
  interact profile k := I.interact profile k

/--
Reindex a local execution law contravariantly along a schema morphism, using
the underlying realized context morphism.
-/
abbrev InteractionOver.comapSchema
    {Δ : Node.Context} {S : Node.Schema Γ} {T : Node.Schema Δ}
    {syn : SyntaxOver Agent Δ}
    {m : Type w → Type w}
    (I : InteractionOver Agent Δ syn m) (f : Node.Schema.SchemaMap S T) :
    InteractionOver Agent Γ (SyntaxOver.comapSchema syn f) m :=
  I.comap f.toContextHom

@[simp]
theorem InteractionOver.comap_id
    {syn : SyntaxOver Agent Γ}
    {m : Type w → Type w}
    (I : InteractionOver Agent Γ syn m) :
    I.comap (Node.ContextHom.id Γ) = I := by
  cases I
  rfl

theorem InteractionOver.comap_comp
    {Δ : Node.Context} {Λ : Node.Context}
    {syn : SyntaxOver Agent Λ}
    {m : Type w → Type w}
    (I : InteractionOver Agent Λ syn m)
    (g : Node.ContextHom Δ Λ) (f : Node.ContextHom Γ Δ) :
    (I.comap g).comap f = I.comap (Node.ContextHom.comp g f) := by
  cases I
  rfl

section Run

variable {Agent : Type u}
variable {Γ : Node.Context}
variable {syn : SyntaxOver Agent Γ}
variable {m : Type u → Type u}

/--
Execute a whole protocol tree using the local one-step law `interact`.

Inputs:
* `spec` is the underlying interaction tree;
* `ctxs : Decoration Γ spec` supplies the realized node context at each node;
* `Out : Agent → Transcript spec → Type u` is the final output family for each
  agent;
* `profile` supplies, for every agent, that agent's whole-tree participant
  object induced by `syn`.

Output:
* a monadic computation producing
  * a concrete transcript `tr`, and
  * for each agent `a`, the final output `Out a tr` obtained by following that
    transcript.

So `run` is the whole-tree execution induced by the local execution law
`InteractionOver.interact`. It is the generic profile-level analogue of the
specialized two-party runners elsewhere in the library.

This first executable version is intentionally specialized to the common
single-universe setting used throughout the current interaction layer. The
underlying `SyntaxOver` and `InteractionOver` abstractions remain more general.
-/
def InteractionOver.run
    (I : InteractionOver Agent Γ syn m) [Monad m]
    {spec : Spec}
    (ctxs : Decoration Γ spec)
    {Out : Agent → Transcript spec → Type u}
    (profile :
      (agent : Agent) → SyntaxOver.Family syn agent spec ctxs (Out agent)) :
    m ((tr : Transcript spec) × ((agent : Agent) → Out agent tr)) :=
  match spec, ctxs with
  | .done, _ => pure ⟨PUnit.unit, profile⟩
  | .node _ next, ⟨γ, ctxs⟩ =>
      I.interact
        (γ := γ)
        (Cont := fun agent x =>
          SyntaxOver.Family syn agent (next x) (ctxs x)
            (fun tr => Out agent ⟨x, tr⟩))
        (fun agent => profile agent)
        (fun x conts => do
          let ⟨tr, out⟩ ← run I
            (ctxs := ctxs x)
            (Out := fun agent tr => Out agent ⟨x, tr⟩)
            conts
          pure ⟨⟨x, tr⟩, out⟩)

end Run

end Spec
end Interaction
