/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Node
import VCVio.Interaction.Basic.StrategyOver

/-!
# Generic local execution laws over interaction trees

This file introduces the execution-side counterpart to `SyntaxOver`.

`InteractionOver` is a local operational law for agent-indexed node
objects. It says how a whole profile of local objects, one for each agent, is
combined at a single protocol node in order to choose the next move and
continue the interaction. The node-local information seen by those objects is
packaged as a realized node context.

Role-based prover/verifier runners are specializations of this notion, obtained
by choosing suitable node contexts and syntax objects.

Just as `SyntaxOver` reindexes contravariantly along node-context morphisms,
`InteractionOver.comap` transports a local execution law along the same kind
of context change.

Naming note:
`InteractionOver` keeps the suffix form for the same reason as `ShapeOver`:
it is the generalized execution notion over node-local data, while
`Interaction` names the plain specialization with trivial node data.
-/

universe u a vΓ vΔ vΛ w uA uB uA₂ uB₂ t

namespace Interaction

open PFunctor
open PFunctor.FreeM.Displayed (Decoration)

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
variable {α : Type t}
variable {Agent : Type a}
variable {Γ : P.A → Type vΓ}

/--
`InteractionOver l Agent Γ syn m` is a one-step operational law for a
lens-executed polynomial interaction.

At each control node, every agent supplies a local syntax object. The
interaction law chooses one runtime direction and passes each agent's matching
continuation to the recursive runner.
-/
structure InteractionOver
    (l : PFunctor.Lens P Q)
    (Agent : Type a)
    (Γ : P.A → Type vΓ)
    (syn : SyntaxOver l Agent Γ)
    (m : Type (max uB₂ a w) → Type (max uB₂ a w)) where
  interact :
    {pos : P.A} →
    {γ : Γ pos} →
    {Cont : Agent → Q.B (l.toFunA pos) → Type w} →
    {Result : Type (max uB₂ a w)} →
    ((agent : Agent) → syn.Node agent pos γ (Cont agent)) →
    ((d : Q.B (l.toFunA pos)) → ((agent : Agent) → Cont agent d) → m Result) →
    m Result

namespace InteractionOver

variable {l : PFunctor.Lens P Q} {syn : SyntaxOver l Agent Γ}

/--
Reindex a local execution law contravariantly along a node metadata map.

If `f : Γ → Δ`, then an execution law for `Δ`-metadata can be reused on
`Γ`-metadata by first viewing local syntax through `SyntaxOver.comap f`.
-/
def comap {Δ : P.A → Type vΔ} {syn : SyntaxOver l Agent Δ}
    {m : Type (max uB₂ a w) → Type (max uB₂ a w)}
    (f : ∀ pos, Γ pos → Δ pos) (I : InteractionOver l Agent Δ syn m) :
    InteractionOver l Agent Γ (SyntaxOver.comap f syn) m where
  interact profile k := I.interact profile k

@[simp]
theorem comap_id
    {m : Type (max uB₂ a w) → Type (max uB₂ a w)}
    (I : InteractionOver l Agent Γ syn m) :
    comap (fun _ γ => γ) I = I := by
  cases I
  rfl

theorem comap_comp {Δ : P.A → Type vΔ} {Λ : P.A → Type vΛ}
    {syn : SyntaxOver l Agent Λ}
    {m : Type (max uB₂ a w) → Type (max uB₂ a w)}
    (I : InteractionOver l Agent Λ syn m)
    (g : ∀ pos, Δ pos → Λ pos) (f : ∀ pos, Γ pos → Δ pos) :
    comap f (comap g I) = comap (fun pos => g pos ∘ f pos) I := by
  cases I
  rfl

/--
Run a whole lens-executed protocol from a profile of local participant
objects, producing the runtime path and an output collected from all agents at
that same path.
-/
def run
    {m : Type (max uB₂ a w) → Type (max uB₂ a w)}
    [Monad m]
    {spec : PFunctor.FreeM P α}
    (ctxs : Decoration Γ spec)
    {Out : Agent → PFunctor.FreeM.PathAlong l spec → Type w}
    {Result : PFunctor.FreeM.PathAlong l spec → Type (max a w)}
    (profile :
      (agent : Agent) → StrategyOver syn agent spec ctxs (Out agent))
    (collect :
      (path : PFunctor.FreeM.PathAlong l spec) →
        ((agent : Agent) → Out agent path) → Result path)
    (I : InteractionOver l Agent Γ syn m) :
    m ((path : PFunctor.FreeM.PathAlong l spec) × Result path) :=
  match spec, ctxs with
  | .pure _, _ => pure ⟨⟨⟩, collect ⟨⟩ profile⟩
  | .roll pos rest, ⟨γ, ctxs⟩ =>
      I.interact
        (γ := γ)
        (Cont := fun agent d =>
          StrategyOver syn agent (rest (l.toFunB pos d)) (ctxs (l.toFunB pos d))
            (fun path => Out agent ⟨d, path⟩))
        (fun agent => profile agent)
        (fun d conts => do
          let ⟨path, out⟩ ← run
            (ctxs := ctxs (l.toFunB pos d))
            (Out := fun agent path => Out agent ⟨d, path⟩)
            (Result := fun path => Result ⟨d, path⟩)
            conts
            (fun path out => collect ⟨d, path⟩ out)
            I
          pure ⟨⟨d, path⟩, out⟩)

variable {Agent : Type u}
variable {Γ : Spec.Node.Context}
variable {syn : SyntaxOver (PFunctor.Lens.id Spec.basePFunctor) Agent Γ}
variable {m : Type u → Type u}

/--
Execute a plain `Spec` tree using an identity-lens generic local one-step law.

The local execution structure is the generic `InteractionOver`; this facade only
keeps the plain-spec transcript recursion definitionally clean for computation
lemmas.
-/
def runSpec
    [Monad m]
    {spec : Spec}
    (ctxs : Decoration Γ spec)
    {Out : Agent → Spec.Transcript spec → Type u}
    {Result : Spec.Transcript spec → Type u}
    (profile :
      (agent : Agent) → StrategyOver syn agent spec ctxs (Out agent))
    (collect : (tr : Spec.Transcript spec) → ((agent : Agent) → Out agent tr) → Result tr)
    (I : InteractionOver
      (PFunctor.Lens.id Spec.basePFunctor) Agent Γ syn m) :
    m ((tr : Spec.Transcript spec) × Result tr) :=
  match spec, ctxs with
  | .done, _ => pure ⟨PUnit.unit, collect PUnit.unit profile⟩
  | .node _ next, ⟨γ, ctxs⟩ =>
      I.interact
        (γ := γ)
        (Cont := fun agent x =>
          StrategyOver syn agent (next x) (ctxs x)
            (fun tr => Out agent ⟨x, tr⟩))
        (fun agent => profile agent)
        (fun x conts => do
          let ⟨tr, out⟩ ← runSpec
            (ctxs := ctxs x)
            (Out := fun agent tr => Out agent ⟨x, tr⟩)
            (Result := fun tr => Result ⟨x, tr⟩)
            conts
            (fun tr out => collect ⟨x, tr⟩ out)
            I
          pure ⟨⟨x, tr⟩, out⟩)

end InteractionOver
end Interaction
