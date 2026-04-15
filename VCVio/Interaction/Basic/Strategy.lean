/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import Mathlib.Control.Lawful

/-!
# Strategies (`Spec.Strategy`)

A `Strategy m spec Output` plays through `spec`, choosing moves and interleaving effects in `m`,
producing a transcript-dependent result `Output tr`. Definitions are by structural recursion on
the spec (Hancock–Setzer), avoiding positivity issues for generic `m`.

`run` executes a strategy; `mapOutput` is functorial in the output family. Dependent sequential
composition `Strategy.comp` requires `Spec.append` from `VCVio.Interaction.Basic.Append`.
-/

universe u

namespace Interaction
namespace Spec

variable {m : Type u → Type u}

/-- One-player strategy with monadic effects: at each node, choose a move `x` and continue in
`m`. -/
def Strategy (m : Type u → Type u) :
    (spec : Spec) → (Transcript spec → Type u) → Type u
  | .done, Output => Output ⟨⟩
  | .node X rest, Output =>
      (x : X) × m (Strategy m (rest x) (fun p => Output ⟨x, p⟩))

/-- Non-dependent output type `α` at every transcript. -/
abbrev Strategy' (m : Type u → Type u) (spec : Spec) (α : Type u) :=
  Strategy m spec (fun _ => α)

/-- Run the strategy, returning the full transcript and the dependent output. -/
def Strategy.run {m : Type u → Type u} [Monad m] :
    (spec : Spec) → {Output : Transcript spec → Type u} →
    Strategy m spec Output → m ((tr : Transcript spec) × Output tr)
  | .done, _, output => pure ⟨⟨⟩, output⟩
  | .node _ rest, _, ⟨move, cont⟩ => do
      let next ← cont
      let ⟨tail, out⟩ ← run (rest move) next
      return ⟨⟨move, tail⟩, out⟩

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
  cases spec with
  | done => rfl
  | node X rest =>
    rcases σ with ⟨x, cont⟩
    simp only [Strategy.mapOutput]
    congr 1
    have hid :
        (mapOutput (fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => y) :
            Strategy m (rest x) (fun p => A ⟨x, p⟩) → Strategy m (rest x) (fun p => A ⟨x, p⟩)) =
          id := by
      funext s
      exact @mapOutput_id m _ _ (rest x) (fun p => A ⟨x, p⟩) s
    rw [hid]
    exact LawfulFunctor.id_map cont

/-- `mapOutput` respects composition of output maps (needs a lawful functor). -/
theorem Strategy.mapOutput_comp {m : Type u → Type u} [Functor m] [LawfulFunctor m] {spec : Spec}
    {A B C : Transcript spec → Type u} (g : ∀ tr, B tr → C tr) (f : ∀ tr, A tr → B tr)
    (σ : Strategy m spec A) :
    Strategy.mapOutput (fun tr x => g tr (f tr x)) σ =
      Strategy.mapOutput g (Strategy.mapOutput f σ) := by
  cases spec with
  | done => rfl
  | node X rest =>
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
      exact
        @mapOutput_comp m _ _ (rest x) (fun p => A ⟨x, p⟩) (fun p => B ⟨x, p⟩) (fun p => C ⟨x, p⟩)
          (fun p y => g ⟨x, p⟩ y) (fun p y => f ⟨x, p⟩ y) s
    rw [hcomp, LawfulFunctor.comp_map]

end Spec
end Interaction
