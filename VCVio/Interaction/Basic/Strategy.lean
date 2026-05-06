/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Interaction

/-!
# One-player strategies

`Strategy m spec Output` is the one-participant strategy induced by
`Strategy.syntax`. At every node it chooses the next move and stores the
continuation in the ambient monad `m`; at a leaf it produces the
transcript-dependent output.

This is the singleton-agent specialization of `StrategyOver` over the empty
node context. `Strategy.run` is the corresponding specialization of the
generic `StrategyOver.run` runner.

Dependent sequential composition `Strategy.comp` requires `Spec.append` from
`VCVio.Interaction.Basic.Append`.
-/

universe u

namespace Interaction
namespace Spec

variable {m : Type u → Type u}

/-- One-participant syntax for ordinary monadic strategies.

At each node the strategy chooses a move `x` and provides the continuation in
the ambient monad `m`. -/
def Strategy.syntax (m : Type u → Type u) :
    SyntaxOver.{u, u, u, u} PUnit Node.Context.empty where
  Node _ X _ Cont := (x : X) × m (Cont x)

/-- One-player strategy with monadic effects. -/
abbrev Strategy (m : Type u → Type u)
    (spec : Spec) (Output : Transcript spec → Type u) :=
  StrategyOver (Strategy.syntax m) PUnit.unit spec (Decoration.empty spec) Output

/-- Non-dependent output type `α` at every transcript. -/
abbrev Strategy' (m : Type u → Type u) (spec : Spec) (α : Type u) :=
  Strategy m spec (fun _ => α)

/-- One-step execution law for ordinary one-player strategies. -/
def Strategy.interaction (m : Type u → Type u) [Monad m] :
    Interaction PUnit (Strategy.syntax m) m where
  interact := fun {_X} {_γ} {_Cont} {_Result} profile k => do
    let node := profile PUnit.unit
    let next ← node.2
    k node.1 (fun _ => next)

/-- Run the strategy, returning the full transcript and the dependent output. -/
def Strategy.run {m : Type u → Type u} [Monad m] :
    (spec : Spec) → {Output : Transcript spec → Type u} →
    Strategy m spec Output → m ((tr : Transcript spec) × Output tr)
  | spec, Output, strat =>
      StrategyOver.run
        (Agent := PUnit)
        (Γ := Node.Context.empty)
        (syn := Strategy.syntax m)
        (m := m)
        (Strategy.interaction m)
        (spec := spec)
        (Out := fun _ => Output)
        (Result := Output)
        (Decoration.empty spec)
        (fun agent => by
          cases agent
          exact strat)
        (fun _ out => out PUnit.unit)

/-- Map the dependent output family along a natural transformation over transcripts. -/
def Strategy.mapOutput {m : Type u → Type u} [Functor m] :
    {spec : Spec} → {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) → Strategy m spec A → Strategy m spec B
  | .done, _, _, f, a => f ⟨⟩ a
  | .node _ _, _, _, f, ⟨x, cont⟩ =>
      ⟨x, (mapOutput (fun p => f ⟨x, p⟩) ·) <$> cont⟩

/-- Pointwise identity on outputs is the identity on strategies (needs a lawful functor). -/
@[simp, grind =]
theorem Strategy.mapOutput_id {m : Type u → Type u} [Functor m] [LawfulFunctor m] {spec : Spec}
    {A : Transcript spec → Type u} (σ : Strategy m spec A) :
    Strategy.mapOutput (fun _ x => x) σ = σ := by
  induction spec with
  | done => rfl
  | node X rest ih =>
    rcases σ with ⟨x, cont⟩
    simp only [Strategy.mapOutput]
    congr 1
    have hid :
        (mapOutput (fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => y) :
            Strategy m (rest x) (fun p => A ⟨x, p⟩) → Strategy m (rest x) (fun p => A ⟨x, p⟩)) =
          id := by
      funext s
      exact ih x s
    rw [hid]
    exact LawfulFunctor.id_map cont

/-- `mapOutput` respects composition of output maps (needs a lawful functor). -/
theorem Strategy.mapOutput_comp {m : Type u → Type u} [Functor m] [LawfulFunctor m] {spec : Spec}
    {A B C : Transcript spec → Type u} (g : ∀ tr, B tr → C tr) (f : ∀ tr, A tr → B tr)
    (σ : Strategy m spec A) :
    Strategy.mapOutput (fun tr x => g tr (f tr x)) σ =
      Strategy.mapOutput g (Strategy.mapOutput f σ) := by
  induction spec with
  | done => rfl
  | node X rest ih =>
    rcases σ with ⟨x, cont⟩
    simp only [Strategy.mapOutput]
    congr 1
    have hcomp :
        (@mapOutput m _ (rest x) (fun p => A ⟨x, p⟩) (fun p => C ⟨x, p⟩)
            fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => g ⟨x, p⟩ (f ⟨x, p⟩ y)) =
          (@mapOutput m _ (rest x) (fun p => B ⟨x, p⟩) (fun p => C ⟨x, p⟩)
              (fun p y => g ⟨x, p⟩ y) ∘
            @mapOutput m _ (rest x) (fun p => A ⟨x, p⟩) (fun p => B ⟨x, p⟩)
              (fun p y => f ⟨x, p⟩ y)) := by
      funext s
      exact ih x (fun p y => g ⟨x, p⟩ y) (fun p y => f ⟨x, p⟩ y) s
    rw [hcomp, LawfulFunctor.comp_map]

end Spec
end Interaction
