/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Strategy
import ToMathlib.PFunctor.Free.Displayed.Append

/-!
# Dependent append of interaction specs

Given two interactions where the second may depend on the outcome of the first,
`PFunctor.FreeM.append` fuses them into a single interaction. The file provides the full
algebra around this operation:

- **PFunctor.FreeM.Path operations**: `PFunctor.FreeM.Path.append` / `split` construct and decompose
  combined transcripts, while `PFunctor.FreeM.Path.liftAppend` lifts a two-argument type family
  to a single-argument family on the combined transcript with definitional computation.
- **Strategy composition**: `Strategy.comp` (factored output via `liftAppend`) and
  `Strategy.compFlat` (flat output via `PFunctor.FreeM.Path.append`).
- **Decoration / refinement append** and their naturality lemmas.
-/

universe u v w w₂

namespace Interaction
namespace Spec

variable {m : Type u → Type u}

/-- Monadic composition of strategies along `PFunctor.FreeM.append`.

The output type is given as a two-argument family
`F : PFunctor.FreeM.Path s₁ → PFunctor.FreeM.Path (s₂ tr₁) → Type u`, lifted to the combined spec
via `PFunctor.FreeM.Path.liftAppend`. The continuation receives the first-phase strategy's
output and produces a second-phase strategy whose output family is `F tr₁`.

This is the preferred composition form: `liftAppend` ensures the output type
reduces definitionally when combined with `PFunctor.FreeM.Path.append`, which is essential
for dependent chain composition (see `Strategy.stateChainComp`). -/
def Strategy.comp {m : Type u → Type u} [Monad m] :
    (s₁ : Spec) → (s₂ : PFunctor.FreeM.Path s₁ → Spec) →
    {Mid : PFunctor.FreeM.Path s₁ → Type u} →
    {F : (tr₁ : PFunctor.FreeM.Path s₁) → PFunctor.FreeM.Path (s₂ tr₁) → Type u} →
    Strategy.Plain m s₁ Mid →
    ((tr₁ : PFunctor.FreeM.Path s₁) → Mid tr₁ → m (Strategy.Plain m (s₂ tr₁) (F tr₁))) →
    m (Strategy.Plain m (s₁.append s₂) (PFunctor.FreeM.Path.liftAppend s₁ s₂ F))
  | .done, _, _, _, mid, f => f ⟨⟩ mid
  | .node _ rest, s₂, _, _, ⟨x, cont⟩, f => pure ⟨x, do
      let next ← cont
      comp (rest x) (fun p => s₂ ⟨x, p⟩) next
        (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩

/-- Monadic composition of strategies along `PFunctor.FreeM.append` with a single output family
`Output` on the combined transcript. The continuation indexes into `Output` via
`PFunctor.FreeM.Path.append`.

Use this when the output type is naturally expressed over the combined transcript
rather than as a two-argument family (e.g., constant output types, or when working
with `Strategy.iterate`). See also `Strategy.comp`. -/
def Strategy.compFlat {m : Type u → Type u} [Monad m] :
    (s₁ : Spec) → (s₂ : PFunctor.FreeM.Path s₁ → Spec) →
    {Mid : PFunctor.FreeM.Path s₁ → Type u} →
    {Output : PFunctor.FreeM.Path (s₁.append s₂) → Type u} →
    Strategy.Plain m s₁ Mid →
    ((tr₁ : PFunctor.FreeM.Path s₁) → Mid tr₁ →
      m (Strategy.Plain m (s₂ tr₁)
        (fun tr₂ => Output (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂)))) →
    m (Strategy.Plain m (s₁.append s₂) Output)
  | .done, _, _, _, mid, f => f ⟨⟩ mid
  | .node _ rest, s₂, _, _, ⟨x, cont⟩, f => pure ⟨x, do
      let next ← cont
      compFlat (rest x) (fun p => s₂ ⟨x, p⟩) next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩

/-- Extract the first-phase strategy from a strategy on a composed interaction.
At each first-phase transcript `tr₁`, the remainder is the second-phase strategy
with output indexed by `PFunctor.FreeM.Path.append`. -/
def Strategy.splitPrefix {m : Type u → Type u} [Functor m] :
    (s₁ : Spec) → (s₂ : PFunctor.FreeM.Path s₁ → Spec) →
    {Output : PFunctor.FreeM.Path (s₁.append s₂) → Type u} →
    Strategy.Plain m (s₁.append s₂) Output →
    Strategy.Plain m s₁ (fun tr₁ =>
      Strategy.Plain m (s₂ tr₁) (fun tr₂ => Output (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂)))
  | .done, _, _, p => p
  | .node _ rest, s₂, _, ⟨x, cont⟩ =>
      ⟨x, (splitPrefix (rest x) (fun p => s₂ ⟨x, p⟩) ·) <$> cont⟩

/-- Concatenate per-node labels along `PFunctor.FreeM.append`. -/
abbrev Decoration.append {S : Type u → Type v}
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    (d₁ : Decoration S s₁)
    (d₂ : (tr₁ : PFunctor.FreeM.Path s₁) → Decoration S (s₂ tr₁)) :
    Decoration S (s₁.append s₂) :=
  PFunctor.FreeM.Displayed.Decoration.append (P := Spec.basePFunctor)
    (α := PUnit.{u+1}) (β := PUnit.{u+1}) d₁ d₂

/-- Concatenate dependent decoration layers along `PFunctor.FreeM.append`, over appended
base decorations. -/
abbrev Decoration.Over.append {L : Type u → Type v} {F : ∀ X, L X → Type w}
    {s₁ : Spec} {s₂ : PFunctor.FreeM.Path s₁ → Spec}
    {d₁ : Decoration L s₁}
    {d₂ : (tr₁ : PFunctor.FreeM.Path s₁) → Decoration L (s₂ tr₁)}
    (r₁ : Decoration.Over F s₁ d₁)
    (r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → Decoration.Over F (s₂ tr₁) (d₂ tr₁)) :
    Decoration.Over F (s₁.append s₂) (d₁.append d₂) :=
  PFunctor.FreeM.Displayed.Decoration.Over.append (P := Spec.basePFunctor)
    (α := PUnit.{u+1}) (β := PUnit.{u+1}) r₁ r₂

/-- `Decoration.Over.map` commutes with `Over.append`. -/
theorem Decoration.Over.map_append {L : Type u → Type v} {F G : ∀ X, L X → Type w}
    (η : ∀ X l, F X l → G X l)
    (s₁ : Spec) (s₂ : PFunctor.FreeM.Path s₁ → Spec)
    (d₁ : Decoration L s₁)
    (d₂ : (tr₁ : PFunctor.FreeM.Path s₁) → Decoration L (s₂ tr₁))
    (r₁ : Decoration.Over F s₁ d₁)
    (r₂ : (tr₁ : PFunctor.FreeM.Path s₁) → Decoration.Over F (s₂ tr₁) (d₂ tr₁)) :
    Decoration.Over.map η (s₁.append s₂) (d₁.append d₂) (Over.append r₁ r₂) =
      Over.append (Over.map η s₁ d₁ r₁)
        (fun tr₁ => Over.map η (s₂ tr₁) (d₂ tr₁) (r₂ tr₁)) :=
  PFunctor.FreeM.Displayed.Decoration.Over.map_append (P := Spec.basePFunctor)
    (α := PUnit.{u+1}) (β := PUnit.{u+1}) η s₁ s₂ d₁ d₂ r₁ r₂

/-- `Decoration.map` commutes with `Decoration.append`. -/
theorem Decoration.map_append {S : Type u → Type v} {T : Type u → Type w}
    (f : ∀ X, S X → T X)
    (s₁ : Spec) (s₂ : PFunctor.FreeM.Path s₁ → Spec)
    (d₁ : Decoration S s₁)
    (d₂ : (tr₁ : PFunctor.FreeM.Path s₁) → Decoration S (s₂ tr₁)) :
    Decoration.map f (s₁.append s₂) (d₁.append d₂) =
      (Decoration.map f s₁ d₁).append (fun tr₁ => Decoration.map f (s₂ tr₁) (d₂ tr₁)) :=
  PFunctor.FreeM.Displayed.Decoration.map_append (P := Spec.basePFunctor)
    (α := PUnit.{u+1}) (β := PUnit.{u+1}) f s₁ s₂ d₁ d₂

end Spec
end Interaction
