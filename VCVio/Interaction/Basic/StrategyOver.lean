/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Shape
import VCVio.Interaction.Basic.Decoration

/-!
# Whole-tree strategies over interaction syntax

This file turns local syntax into whole-tree strategy families. It sits after
`SyntaxOver` and `ShapeOver`: syntax describes one node, shape adds local
continuation reindexing, and `StrategyOver` recursively interprets that syntax
over an entire `FreeM` tree.
-/

universe u a vΓ vΔ w uA uB uA₂ uB₂ t

namespace Interaction

open PFunctor
open PFunctor.FreeM.Displayed (Decoration)

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
variable {α : Type t}

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
The whole-tree strategy induced by `SyntaxOver.forAgent syn agent` is the
`agent` fiber of the original participant-indexed whole-tree strategy.
-/
theorem forAgent
    (syn : SyntaxOver l Agent Γ) (agent : Agent) :
    {spec : PFunctor.FreeM P α} →
    (ctxs : Decoration Γ spec) →
    {Out : PFunctor.FreeM.PathAlong l spec → Type w} →
    StrategyOver (SyntaxOver.forAgent syn agent) PUnit.unit spec ctxs Out =
      StrategyOver syn agent spec ctxs Out
  | .pure _, _, _ => rfl
  | .roll pos rest, ⟨γ, ctxs⟩, Out => by
      change syn.Node agent pos γ _ = syn.Node agent pos γ _
      congr 1
      funext d
      exact forAgent syn agent
        (ctxs := ctxs (l.toFunB pos d))
        (Out := fun path => Out ⟨d, path⟩)

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

namespace ShapeOver

variable {l : PFunctor.Lens P Q}
variable {Agent : Type a} {Γ : P.A → Type vΓ}

/--
View a functorial shape as a local strategy homomorphism on one agent fiber.
-/
def toStrategyHom
    (shape : ShapeOver l Agent Γ) (agent : Agent) :
    StrategyOver.Hom shape.toSyntaxOver agent shape.toSyntaxOver agent where
  mapNode f node := shape.map f node

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
