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

universe u a vΓ vΔ vΛ w uA uB uA₂ uB₂ t

namespace Interaction

open PFunctor
open PFunctor.FreeM.Displayed (Decoration)

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

namespace StrategyOver

variable {Agent₁ : Type a} {Agent₂ : Type u}
variable {l : PFunctor.Lens P Q}

/--
A local homomorphism between two lens-executed `StrategyOver` fibers.

The source and target may use different local syntax objects and different
agents, while sharing the same control lens and node-context decoration.
At each node, `mapNode` translates the source node object into the target node
object after recursive continuations have already been translated.
-/
structure Hom
    (syn₁ : SyntaxOver l Agent₁ Γ) (agent₁ : Agent₁)
    (syn₂ : SyntaxOver l Agent₂ Γ) (agent₂ : Agent₂) where
  mapNode :
    {pos : P.A} →
    {γ : Γ pos} →
    {A B : Q.B (l.toFunA pos) → Type w} →
    (∀ d, A d → B d) →
    syn₁.Node agent₁ pos γ A →
    syn₂.Node agent₂ pos γ B

/--
Map a lens-executed whole-tree strategy along a local homomorphism, while also
mapping its leaf output family.

The recursion follows runtime directions through `PathAlong l spec`; the lens
maps each runtime direction back to the corresponding control branch.
-/
def map
    {syn₁ : SyntaxOver l Agent₁ Γ} {agent₁ : Agent₁}
    {syn₂ : SyntaxOver l Agent₂ Γ} {agent₂ : Agent₂}
    (η : Hom syn₁ agent₁ syn₂ agent₂) :
    {spec : PFunctor.FreeM P α} → {ctxs : Decoration Γ spec} →
    {A B : PFunctor.FreeM.PathAlong l spec → Type w} →
    (∀ path, A path → B path) →
    StrategyOver syn₁ agent₁ spec ctxs A →
    StrategyOver syn₂ agent₂ spec ctxs B
  | PFunctor.FreeM.pure _, _, _, _, f, out => f ⟨⟩ out
  | PFunctor.FreeM.roll pos _, ⟨_, ctxs⟩, _, _, f, stratNode =>
      η.mapNode
        (fun d =>
          map η (ctxs := ctxs (l.toFunB pos d))
            (fun path => f ⟨d, path⟩))
        stratNode

/--
Whole-tree families for `SyntaxOver.comap f syn` are exactly families for `syn`
evaluated on the mapped decoration.
-/
theorem comap {Δ : P.A → Type vΔ}
    (syn : SyntaxOver l Agent Δ) (f : ∀ pos, Γ pos → Δ pos) :
    {agent : Agent} →
    {spec : PFunctor.FreeM P α} →
    (ctxs : Decoration Γ spec) →
    {Out : PFunctor.FreeM.PathAlong l spec → Type w} →
    StrategyOver (SyntaxOver.comap f syn) agent spec ctxs Out =
      StrategyOver syn agent spec (Decoration.map f spec ctxs) Out
  | _, .pure _, _, _ => rfl
  | agent, .roll pos rest, ⟨γ, ctxs⟩, Out => by
      simp only [StrategyOver, SyntaxOver.comap, Decoration.map_roll]
      congr 1
      funext d
      exact comap syn f (agent := agent) (ctxs := ctxs (l.toFunB pos d))

end StrategyOver

namespace Spec

variable {Agent : Type a}
variable {Γ : Node.Context.{u, vΓ}}

/-- Plain-`Spec` local syntax, specialized from the identity-lens generic API. -/
abbrev SyntaxOver (Agent : Type a) (Γ : Node.Context.{u, vΓ}) :=
  _root_.Interaction.SyntaxOver (PFunctor.Lens.id Spec.basePFunctor) Agent Γ

/-- View generic identity-lens syntax as syntax over plain `Spec` trees. -/
abbrev SyntaxOver.ofGeneric
    (syn : Interaction.SyntaxOver (PFunctor.Lens.id Spec.basePFunctor) Agent Γ) :
    SyntaxOver Agent Γ :=
  syn

/-- View plain `Spec` syntax as generic syntax over the identity lens. -/
abbrev SyntaxOver.toGeneric
    (syn : SyntaxOver Agent Γ) :
    Interaction.SyntaxOver (PFunctor.Lens.id Spec.basePFunctor) Agent Γ :=
  syn

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
abbrev SyntaxOver.comap {Δ : Node.Context.{u, vΔ}}
    (f : Node.ContextHom Γ Δ) (syn : SyntaxOver Agent Δ) :
    SyntaxOver Agent Γ :=
  _root_.Interaction.SyntaxOver.comap f syn

/--
Reindex a local syntax object contravariantly along a schema morphism, using
the underlying realized context morphism.
-/
abbrev SyntaxOver.comapSchema
    {Δ : Node.Context.{u, vΓ}} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (f : Node.Schema.SchemaMap S T) (syn : SyntaxOver Agent Δ) :
    SyntaxOver Agent Γ :=
  SyntaxOver.comap f.toContextHom syn

@[simp]
theorem SyntaxOver.comap_id
    (syn : SyntaxOver Agent Γ) :
    SyntaxOver.comap (Node.ContextHom.id Γ) syn = syn :=
  _root_.Interaction.SyntaxOver.comap_id syn

theorem SyntaxOver.comap_comp
    {Δ : Node.Context.{u, vΔ}} {Λ : Node.Context.{u, vΛ}}
    (syn : SyntaxOver Agent Λ)
    (g : Node.ContextHom Δ Λ) (f : Node.ContextHom Γ Δ) :
    SyntaxOver.comap f (SyntaxOver.comap g syn) =
      SyntaxOver.comap (Node.ContextHom.comp g f) syn :=
  _root_.Interaction.SyntaxOver.comap_comp syn g f

/-- Whole-tree local strategy induced by plain-`Spec` identity-lens syntax. -/
abbrev StrategyOver
    (syn : SyntaxOver Agent Γ) :
    (agent : Agent) →
    (spec : Spec) →
    Decoration Γ spec →
    (Transcript spec → Type w) →
    Type w :=
  fun agent spec ctxs Out =>
    _root_.Interaction.StrategyOver
      (P := Spec.basePFunctor) (Q := Spec.basePFunctor) (α := PUnit.{u+1})
      (l := PFunctor.Lens.id Spec.basePFunctor) syn agent spec ctxs Out

namespace StrategyOver

variable {Agent₁ : Type a} {Agent₂ : Type uA}

/-- Local homomorphism between two plain-`Spec` `StrategyOver` fibers. -/
abbrev Hom
    (syn₁ : SyntaxOver Agent₁ Γ) (agent₁ : Agent₁)
    (syn₂ : SyntaxOver Agent₂ Γ) (agent₂ : Agent₂) :=
  _root_.Interaction.StrategyOver.Hom syn₁ agent₁ syn₂ agent₂

/-- Map a whole-tree strategy along a local homomorphism and output map. -/
abbrev map
    {syn₁ : SyntaxOver Agent₁ Γ} {agent₁ : Agent₁}
    {syn₂ : SyntaxOver Agent₂ Γ} {agent₂ : Agent₂}
    (η : Hom syn₁ agent₁ syn₂ agent₂) :
    {spec : Spec} → {ctxs : Decoration Γ spec} →
    {A B : Transcript spec → Type w} →
    (∀ tr, A tr → B tr) →
    StrategyOver syn₁ agent₁ spec ctxs A →
    StrategyOver syn₂ agent₂ spec ctxs B :=
  fun f strat =>
    _root_.Interaction.StrategyOver.map
      (P := Spec.basePFunctor) (Q := Spec.basePFunctor) (α := PUnit.{u+1})
      (l := PFunctor.Lens.id Spec.basePFunctor) η f strat

end StrategyOver

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
theorem StrategyOver.comap {Δ : Node.Context.{u, vΔ}}
    (syn : SyntaxOver Agent Δ) (f : Node.ContextHom Γ Δ) :
    {agent : Agent} → {spec : Spec} → (ctxs : Decoration Γ spec) →
    {Out : Transcript spec → Type w} →
    StrategyOver (SyntaxOver.comap f syn) agent spec ctxs Out =
      StrategyOver syn agent spec (Decoration.map f spec ctxs) Out
  | _, .done, _, _ => rfl
  | agent, .node _ next, ⟨γ, ctxs⟩, Out => by
      simp only [StrategyOver, _root_.Interaction.StrategyOver,
        SyntaxOver.comap, _root_.Interaction.SyntaxOver.comap, Decoration.map,
        PFunctor.FreeM.Displayed.Decoration.map_roll]
      congr 1
      funext x
      exact StrategyOver.comap syn f (agent := agent) (ctxs := ctxs x)

theorem StrategyOver.comapSchema
    {Δ : Node.Context.{u, vΓ}} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (syn : SyntaxOver Agent Δ) (f : Node.Schema.SchemaMap S T) :
    {agent : Agent} → {spec : Spec} → (ctxs : Decoration Γ spec) →
    {Out : Transcript spec → Type w} →
    StrategyOver (SyntaxOver.comapSchema f syn) agent spec ctxs Out =
      StrategyOver syn agent spec (Decoration.Schema.map f spec ctxs) Out :=
  StrategyOver.comap syn f.toContextHom

end Spec
end Interaction
