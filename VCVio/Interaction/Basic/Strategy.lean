/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Interaction

/-!
# One-player strategies

`Strategy.Plain m spec Output` is the one-participant strategy induced by
`Strategy.syntax`. At every node it chooses the next move and stores the
continuation in the ambient monad `m`; at a leaf it produces the
transcript-dependent output.

This is the singleton-agent specialization of `StrategyOver` over the empty
node context. `Strategy.run` is the corresponding specialization of the
generic `InteractionOver.run` runner.

Dependent sequential composition `Strategy.comp` requires `Spec.append` from
`VCVio.Interaction.Basic.Append`.
-/

universe u

namespace Interaction
open PFunctor.FreeM.Displayed (Decoration)
namespace Spec

variable {m : Type u → Type u}

/-- One-participant syntax for ordinary monadic strategies.

At each node the strategy chooses a move `x` and provides the continuation in
the ambient monad `m`. -/
def Strategy.syntax (m : Type u → Type u) :
    _root_.Interaction.SyntaxOver
      (PFunctor.Lens.id Spec.basePFunctor) PUnit.{u+1} Node.Context.empty.{u, u} where
  Node _ X _ Cont := (x : X) × m (Cont x)

/-- One-player strategy with monadic effects. -/
abbrev Strategy.Plain (m : Type u → Type u)
    (spec : Spec.{u}) (Output : Transcript spec → Type u) :=
  StrategyOver (Strategy.syntax m) (PUnit.unit : PUnit.{u+1}) spec
    (Decoration.empty.{u, u} spec) Output

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
    Strategy.Plain m spec Output → m ((tr : Transcript spec) × Output tr)
  | spec, Output, strat =>
      InteractionOver.run
        (Agent := PUnit.{u+1})
        (Γ := Node.Context.empty)
        (syn := Strategy.syntax m)
        (m := m)
        (spec := spec)
        (Out := fun _ => Output)
        (Result := Output)
        (Decoration.empty spec)
        (fun agent => by
          cases agent
          exact strat)
        (fun _ out => out PUnit.unit)
        (Strategy.interaction m)

/-- Map the dependent output family along a natural transformation over transcripts. -/
def Strategy.mapOutput {m : Type u → Type u} [Functor m] :
    {spec : Spec} → {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) → Strategy.Plain m spec A → Strategy.Plain m spec B
  | .done, _, _, f, a => f ⟨⟩ a
  | .node _ _, _, _, f, ⟨x, cont⟩ =>
      ⟨x, (mapOutput (fun p => f ⟨x, p⟩) ·) <$> cont⟩

/-- Pointwise identity on outputs is the identity on strategies (needs a lawful functor). -/
@[simp, grind =]
theorem Strategy.mapOutput_id {m : Type u → Type u} [Functor m] [LawfulFunctor m] {spec : Spec}
    {A : Transcript spec → Type u} (σ : Strategy.Plain m spec A) :
    Strategy.mapOutput (fun _ x => x) σ = σ := by
  induction spec with
  | done => rfl
  | node X rest ih =>
    rcases σ with ⟨x, cont⟩
    simp only [Strategy.mapOutput]
    congr 1
    have hid : ∀ s : Strategy.Plain m (rest x) (fun p => A ⟨x, p⟩),
        mapOutput (fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => y) s = s :=
      fun s => ih x s
    calc (mapOutput (fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => y) ·) <$> cont
        = id <$> cont := by congr 1; funext s; exact hid s
      _ = cont := LawfulFunctor.id_map cont

/-- `mapOutput` respects composition of output maps (needs a lawful functor). -/
theorem Strategy.mapOutput_comp {m : Type u → Type u} [Functor m] [LawfulFunctor m] {spec : Spec}
    {A B C : Transcript spec → Type u} (g : ∀ tr, B tr → C tr) (f : ∀ tr, A tr → B tr)
    (σ : Strategy.Plain m spec A) :
    Strategy.mapOutput (fun tr x => g tr (f tr x)) σ =
      Strategy.mapOutput g (Strategy.mapOutput f σ) := by
  induction spec with
  | done => rfl
  | node X rest ih =>
    rcases σ with ⟨x, cont⟩
    simp only [Strategy.mapOutput]
    congr 1
    have hcomp : ∀ s : Strategy.Plain m (rest x) (fun p => A ⟨x, p⟩),
        @mapOutput m _ (rest x) (fun p => A ⟨x, p⟩) (fun p => C ⟨x, p⟩)
            (fun p y => g ⟨x, p⟩ (f ⟨x, p⟩ y)) s =
          (@mapOutput m _ (rest x) (fun p => B ⟨x, p⟩) (fun p => C ⟨x, p⟩)
              (fun p y => g ⟨x, p⟩ y) ∘
            @mapOutput m _ (rest x) (fun p => A ⟨x, p⟩) (fun p => B ⟨x, p⟩)
              (fun p y => f ⟨x, p⟩ y)) s :=
      fun s => ih x (fun p y => g ⟨x, p⟩ y) (fun p y => f ⟨x, p⟩ y) s
    calc (mapOutput (fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => g ⟨x, p⟩ (f ⟨x, p⟩ y)) ·)
              <$> cont
        = ((mapOutput (fun p y => g ⟨x, p⟩ y) ·) ∘ (mapOutput (fun p y => f ⟨x, p⟩ y) ·))
              <$> cont := by congr 1; funext s; exact hcomp s
      _ = (mapOutput (fun p y => g ⟨x, p⟩ y) ·) <$>
            ((mapOutput (fun p y => f ⟨x, p⟩ y) ·) <$> cont) := by
            rw [LawfulFunctor.comp_map]

end Spec
end Interaction
