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

`SyntaxOver` in `Basic/Syntax` is the most general local syntax object: it
describes which node object an agent has at one protocol node, with no
assumption that recursive continuations can be reindexed generically.

`ShapeOver` is the functorial refinement of that base notion:
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

universe u a vΓ vΔ vΛ w uA uB uA₂ uB₂ t

namespace Interaction

open PFunctor
open PFunctor.FreeM.Displayed (Decoration)

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
variable {α : Type t}

/--
`ShapeOver l Agent Γ` is functorial local syntax over an arbitrary control
polynomial executed through a runtime lens `l`.

It refines `SyntaxOver l Agent Γ` with a node-level continuation map. At a
control position `pos : P.A`, recursive continuations are indexed by runtime
directions `Q.B (l.toFunA pos)`, and the lens determines which control child
each runtime direction selects.
-/
structure ShapeOver
    (l : PFunctor.Lens P Q)
    (Agent : Type a)
    (Γ : P.A → Type vΓ) extends SyntaxOver l Agent Γ where
  /--
  Transform the recursive continuation payload of one local node object.
  The agent, control position, node-local context, and runtime move shape are
  unchanged.
  -/
  map :
    {agent : Agent} →
    {pos : P.A} →
    {γ : Γ pos} →
    {A B : Q.B (l.toFunA pos) → Type w} →
    (∀ d, A d → B d) →
    Node agent pos γ A →
    Node agent pos γ B

namespace ShapeOver

variable {l : PFunctor.Lens P Q}
variable {Agent : Type a} {Γ : P.A → Type vΓ}

instance : Coe (ShapeOver l Agent Γ) (SyntaxOver l Agent Γ) where
  coe := ShapeOver.toSyntaxOver

/--
View a functorial shape as a local strategy homomorphism on one agent fiber.
-/
def toStrategyHom
    (shape : ShapeOver l Agent Γ) (agent : Agent) :
    StrategyOver.Hom shape.toSyntaxOver agent shape.toSyntaxOver agent where
  mapNode f node := shape.map f node

/--
Restrict a participant-indexed shape to one fixed agent.

The resulting singleton-agent shape has the same node objects and continuation
map as `shape` at `agent`; the dummy `PUnit` agent argument is ignored.
-/
def forAgent (shape : ShapeOver l Agent Γ) (agent : Agent) :
    ShapeOver l PUnit Γ where
  toSyntaxOver := SyntaxOver.forAgent shape.toSyntaxOver agent
  map f node := shape.map (agent := agent) f node

/--
Reindex a functorial local syntax object contravariantly along a node metadata
map.
-/
def comap {Δ : P.A → Type vΔ}
    (f : ∀ pos, Γ pos → Δ pos) (shape : ShapeOver l Agent Δ) :
    ShapeOver l Agent Γ where
  toSyntaxOver := SyntaxOver.comap f shape.toSyntaxOver
  map h := shape.map h

@[simp]
theorem comap_id (shape : ShapeOver l Agent Γ) :
    comap (fun _ γ => γ) shape = shape := by
  cases shape
  rfl

theorem comap_comp {Δ : P.A → Type vΔ} {Λ : P.A → Type vΛ}
    (shape : ShapeOver l Agent Λ)
    (g : ∀ pos, Δ pos → Λ pos) (f : ∀ pos, Γ pos → Δ pos) :
    comap f (comap g shape) = comap (fun pos => g pos ∘ f pos) shape := by
  cases shape
  rfl

/--
Map leaf outputs through a whole lens-executed strategy.

This is the recursive global form of the local `ShapeOver.map` field. The
runtime path index is `PathAlong l spec`, so it applies equally to plain specs
and to control specs such as `Oracle.Spec` executed through a lens.
-/
def mapOutput
    (shape : ShapeOver l Agent Γ)
    {agent : Agent}
    {spec : PFunctor.FreeM P α}
    (ctxs : Decoration Γ spec) :
    {A B : PFunctor.FreeM.PathAlong l spec → Type w} →
    (∀ path, A path → B path) →
    StrategyOver shape.toSyntaxOver agent spec ctxs A →
    StrategyOver shape.toSyntaxOver agent spec ctxs B :=
  match spec, ctxs with
  | .pure _, _ => fun f out => f ⟨⟩ out
  | .roll pos _, ⟨γ, ctxsRest⟩ => fun f node =>
      shape.map
        (agent := agent)
        (γ := γ)
        (fun d =>
          mapOutput shape (ctxs := ctxsRest (l.toFunB pos d))
            (fun path => f ⟨d, path⟩))
        node

/--
Whole-tree families for `ShapeOver.comap f shape` are exactly families for
`shape` evaluated on the mapped decoration.
-/
theorem family_comap {Δ : P.A → Type vΔ}
    (shape : ShapeOver l Agent Δ) (f : ∀ pos, Γ pos → Δ pos) :
    {agent : Agent} →
    {spec : PFunctor.FreeM P α} →
    (ctxs : Decoration Γ spec) →
    {Out : PFunctor.FreeM.PathAlong l spec → Type w} →
    StrategyOver (ShapeOver.comap f shape).toSyntaxOver agent spec ctxs Out =
      StrategyOver shape.toSyntaxOver agent spec (Decoration.map f spec ctxs) Out := by
  intro agent spec ctxs Out
  simpa using
    (StrategyOver.comap shape.toSyntaxOver f
      (agent := agent) (spec := spec) (ctxs := ctxs) (Out := Out))

end ShapeOver

end Interaction
