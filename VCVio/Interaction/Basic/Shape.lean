/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Node
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Syntax

/-!
# Functorial local syntax over interaction trees

This file introduces the functorial refinement of the local syntax core.

`Spec.SyntaxOver` in `Basic/Syntax` is the most general local syntax object: it
describes which node object an agent has at one protocol node, with no
assumption that recursive continuations can be reindexed generically.

`Spec.ShapeOver` is the functorial refinement of that base notion:
it equips a `SyntaxOver` with a continuation map. This is exactly the extra
structure needed to define generic output transport such as
`ShapeOver.mapOutput`.

Many important interaction objects are syntax without being shapes in this
sense: if recursive continuations are hidden under an opaque outer constructor,
then a generic continuation map may not exist. This is why `SyntaxOver` is the
semantic base layer, while `ShapeOver` is the stronger interface used when
continuations are exposed functorially enough.

Naming note:
`ShapeOver` keeps the suffix form because it is the primary *functorial*
refinement of syntax, with plain `Shape` recovered as the trivial-context
specialization. This differs from `Decoration.Over`, which is literally
dependent data over a fixed base decoration value.
-/

universe u a vΓ w

namespace Interaction
namespace Spec

variable {Agent : Type a}
variable {Γ : Node.Context}

/--
`ShapeOver Agent Γ` is a functorial local-syntax object over realized node
contexts `Γ`.

It answers the following question:

> Suppose we are standing at one protocol node whose move space is `X`.
> The node carries realized node-local context `γ : Γ X`.
> If the protocol continues with family `Cont : X → Type w`, what is the type
> of the local object that agent `a` stores at this node?

Unlike bare `SyntaxOver`, a `ShapeOver` also provides a generic continuation
map. So a shape is syntax that is *functorial in its recursive continuations*.

This is the right abstraction when node objects support a generic reindexing of
their continuation payload, for example when those continuations remain exposed
or are stored under constructors with a functorial action.
-/
structure ShapeOver
    (Agent : Type a)
    (Γ : Node.Context) extends SyntaxOver Agent Γ where
  /--
  `map` expresses that a node object is functorial in its continuation family.

If we know how to transform each continuation value `A x` into a
continuation value `B x`, then we can transform a local node object with
  continuation family `A` into one with continuation family `B`.

  Importantly, `map` does **not** change:
  * the agent,
  * the move space,
  * the node-local context,
  * or the move `x` that will eventually be chosen.

  It only reinterprets what happens *after* each possible move.
  This is the local ingredient needed to define the generic whole-tree
  `ShapeOver.mapOutput` below.
  -/
  map :
    {agent : Agent} →
    {X : Type u} →
    {γ : Γ X} →
    {A B : X → Type w} →
    (∀ x, A x → B x) →
    Node agent X γ A →
    Node agent X γ B

/--
`Shape Agent` is the specialization of `ShapeOver` with no node-local context.

This is the right facade when the protocol tree carries no node metadata at all.
Equivalently, it is `ShapeOver Agent Spec.Node.Context.empty`.
-/
abbrev Shape
    (Agent : Type a) :=
  ShapeOver Agent Node.Context.empty

instance : Coe (ShapeOver Agent Γ) (SyntaxOver Agent Γ) where
  coe := ShapeOver.toSyntaxOver

/--
Reindex a local syntax object contravariantly along a node-context morphism.

If `f : Γ → Δ`, then any shape over `Δ` can be viewed as a shape over `Γ` by
first viewing its underlying syntax through `SyntaxOver.comap f`.
-/
def ShapeOver.comap {Δ : Node.Context}
    (shape : ShapeOver Agent Δ) (f : Node.ContextHom Γ Δ) :
    ShapeOver Agent Γ where
  toSyntaxOver := shape.toSyntaxOver.comap f
  map h := shape.map h

/--
Reindex a local syntax object contravariantly along a schema morphism, using
the underlying realized context morphism.
-/
abbrev ShapeOver.comapSchema
    {Δ : Node.Context} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (shape : ShapeOver Agent Δ) (f : Node.Schema.SchemaMap S T) :
    ShapeOver Agent Γ :=
  shape.comap f.toContextHom

@[simp]
theorem ShapeOver.comap_id
    (shape : ShapeOver Agent Γ) :
    shape.comap (Node.ContextHom.id Γ) = shape := by
  cases shape
  rfl

theorem ShapeOver.comap_comp
    {Δ : Node.Context} {Λ : Node.Context}
    (shape : ShapeOver Agent Λ)
    (g : Node.ContextHom Δ Λ) (f : Node.ContextHom Γ Δ) :
    (shape.comap g).comap f = shape.comap (Node.ContextHom.comp g f) := by
  cases shape
  rfl

/--
Whole-tree families for a shape are inherited from the underlying
`SyntaxOver`.
-/
abbrev ShapeOver.Family
    (shape : ShapeOver Agent Γ) :
    (agent : Agent) →
    (spec : Spec) →
    Decoration Γ spec →
    (Transcript spec → Type w) →
    Type w :=
  SyntaxOver.Family shape.toSyntaxOver

/--
`ShapeOver.mapOutput` lifts a pointwise transformation of leaf outputs to a
transformation of whole-tree participant objects.

This is the recursive global form of the local `ShapeOver.map` field.
It leaves the underlying interactive structure unchanged and only rewrites the
terminal output family.
-/
def ShapeOver.mapOutput
    (shape : ShapeOver Agent Γ)
    {agent : Agent}
    {spec : Spec}
    (ctxs : Decoration Γ spec)
    :
    {A B : Transcript spec → Type w} →
    (∀ tr, A tr → B tr) →
    ShapeOver.Family shape agent spec ctxs A →
    ShapeOver.Family shape agent spec ctxs B
  :=
    match spec, ctxs with
    | .done, _ => fun f out => f ⟨⟩ out
    | .node _ _, ⟨γ, ctxsRest⟩ => fun f node =>
        shape.map
          (agent := agent)
          (γ := γ)
          (fun x =>
            mapOutput shape (ctxs := ctxsRest x) (fun tr => f ⟨x, tr⟩))
          node

/--
Whole-tree families for `shape.comap f` are exactly families for `shape`
evaluated on the mapped decoration `Decoration.map f ctxs`.
-/
theorem ShapeOver.family_comap {Δ : Node.Context}
    (shape : ShapeOver Agent Δ) (f : Node.ContextHom Γ Δ) :
    {agent : Agent} → {spec : Spec} → (ctxs : Decoration Γ spec) →
    {Out : Transcript spec → Type w} →
    ShapeOver.Family (shape.comap f) agent spec ctxs Out =
      ShapeOver.Family shape agent spec (Decoration.map f spec ctxs) Out
  := by
    intro agent spec ctxs Out
    simpa [ShapeOver.Family] using
      (SyntaxOver.family_comap shape.toSyntaxOver f
        (agent := agent) (spec := spec) (ctxs := ctxs) (Out := Out))

theorem ShapeOver.family_comapSchema
    {Δ : Node.Context} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (shape : ShapeOver Agent Δ) (f : Node.Schema.SchemaMap S T) :
    {agent : Agent} → {spec : Spec} → (ctxs : Decoration Γ spec) →
    {Out : Transcript spec → Type w} →
    ShapeOver.Family (shape.comapSchema f) agent spec ctxs Out =
      ShapeOver.Family shape agent spec (Decoration.Schema.map f spec ctxs) Out :=
  by
    intro agent spec ctxs Out
    simpa [ShapeOver.Family] using
      (SyntaxOver.family_comapSchema shape.toSyntaxOver f
        (agent := agent) (spec := spec) (ctxs := ctxs) (Out := Out))

end Spec
end Interaction
