/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.UniformOn

/-!
# Native measure semantics for polynomial free monads

This module interprets a polynomial free program directly as a Mathlib `Measure`. Each operation
is assigned a probability measure on its answer type, and `PFunctor.FreeM.denote` recursively
composes those measures with `Measure.bind`.

`Measure α` becomes a type only after `α` receives a `MeasurableSpace`, so this interpretation is
an explicit fold rather than an unrestricted Lean monad morphism. The measurable-continuation
boundary remains visible in the general laws. Discrete answer types discharge the internal
measurability obligations while leaving the result space arbitrary.

## Main definitions

* `PFunctor.IsMeasureSpec` assigns a probability measure to each operation.
* `PFunctor.IsMeasureSpec.uniformOfFintypeInhabited` assigns the native uniform measure to every
  finite, inhabited answer type.
* `PFunctor.FreeM.denote` is the measure denoted by a free program.

## Main statements

* `PFunctor.FreeM.denote_lift` identifies the denotation of one operation.
* `PFunctor.FreeM.denote_bind_of_discrete` and `PFunctor.FreeM.denote_map_of_discrete` give the
  discrete Giry composition laws.
* `PFunctor.FreeM.denote_bind_bind_prod_mk_eq_prod` identifies two independent executions with
  Mathlib's product measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe u v w uA

namespace PFunctor

/-- Per-operation answer measures for a polynomial interface.

The measurable structure on answer types is a separate parameter rather than a field, mirroring
Mathlib's separation of `MeasurableSpace` from the measures carried on it. Answer types need not
be discrete. -/
class IsMeasureSpec (P : PFunctor.{uA, u}) [∀ a, MeasurableSpace (P.B a)] where
  /-- The distribution of answers to an operation. -/
  toMeasure : (a : P.A) → Measure (P.B a)
  /-- Answering an operation is lossless. -/
  isProbabilityMeasure : ∀ a, IsProbabilityMeasure (toMeasure a)

attribute [instance] IsMeasureSpec.isProbabilityMeasure

/-- Construct native uniform measure semantics from finite, inhabited answer types.

This is deliberately not an instance: measure semantics remain an explicit choice at each use
site, and are never inferred merely from finiteness. -/
@[reducible]
noncomputable def IsMeasureSpec.uniformOfFintypeInhabited (P : PFunctor.{uA, u})
    [P.Fintype] [P.Inhabited] [∀ a, MeasurableSpace (P.B a)] : P.IsMeasureSpec where
  toMeasure _ := uniformOn Set.univ
  isProbabilityMeasure _ := inferInstance

namespace FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.IsMeasureSpec]
  {α : Type v} {β : Type w}

/-- The measure denoted by a polynomial free program: `pure` is a Dirac mass, and each
operation is the Giry bind of its answer measure with the denotation of the continuation. -/
noncomputable def denote [MeasurableSpace α] : FreeM P α → Measure α
  | .pure x => Measure.dirac x
  | .liftBind a cont => Measure.bind (IsMeasureSpec.toMeasure a) fun b => denote (cont b)

@[simp]
theorem denote_pure [MeasurableSpace α] (x : α) :
    denote (pure x : FreeM P α) = Measure.dirac x := rfl

theorem denote_liftBind [MeasurableSpace α] (a : P.A) (cont : P.B a → FreeM P α) :
    denote (FreeM.liftBind a cont)
      = Measure.bind (IsMeasureSpec.toMeasure a) fun b => denote (cont b) := rfl

/-- A one-operation program denotes its configured answer measure. -/
@[simp]
theorem denote_lift (a : P.A) :
    denote (FreeM.lift a : FreeM P (P.B a)) = IsMeasureSpec.toMeasure a := by
  change Measure.bind (IsMeasureSpec.toMeasure a) Measure.dirac = IsMeasureSpec.toMeasure a
  exact Measure.bind_dirac

/-- A one-operation program is a probability measure whenever its continuation is an
almost-everywhere measurable family of probability measures.

This is the continuous composition boundary. For discrete answer types the hypotheses are
automatic; for a genuinely continuous oracle they are precisely the obligations represented by
a Mathlib `Kernel`. -/
theorem isProbabilityMeasure_denote_liftBind [MeasurableSpace α] (a : P.A)
    (cont : P.B a → FreeM P α)
    (hMeasurable : AEMeasurable (fun b => denote (cont b)) (IsMeasureSpec.toMeasure a))
    (hProbability : ∀ᵐ b ∂IsMeasureSpec.toMeasure a,
      IsProbabilityMeasure (denote (cont b))) :
    IsProbabilityMeasure (denote (FreeM.liftBind a cont)) :=
  MeasureTheory.isProbabilityMeasure_bind hMeasurable hProbability

/-! ## Giry composition laws -/

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Every program over discrete answer types denotes a probability measure.

This theorem is deliberately not a global instance: a program with a continuous answer type
needs a measurability argument for each continuation, and typeclass search must not hide that
boundary. -/
theorem isProbabilityMeasure_denote [MeasurableSpace α] (program : FreeM P α) :
    IsProbabilityMeasure (denote program) := by
  induction program with
  | pure _ => exact ⟨by simp⟩
  | lift_bind a cont ih =>
      exact isProbabilityMeasure_denote_liftBind a cont
        Measurable.of_discrete.aemeasurable
        (Filter.Eventually.of_forall ih)

/-- `denote` preserves bind when the denoted continuation is measurable. Discrete answer types
discharge the recursive measurability obligation inside the free program. -/
theorem denote_bind [MeasurableSpace α] [MeasurableSpace β]
    (program : FreeM P α) (f : α → FreeM P β)
    (hf : Measurable fun x => denote (f x)) :
    denote (FreeM.bind program f) = Measure.bind (denote program) fun x => denote (f x) := by
  induction program with
  | pure x => simpa using (Measure.dirac_bind hf x).symm
  | lift_bind a cont ih =>
      change Measure.bind (IsMeasureSpec.toMeasure a) (fun b => denote (FreeM.bind (cont b) f))
          = Measure.bind (Measure.bind (IsMeasureSpec.toMeasure a) fun b => denote (cont b))
              fun x => denote (f x)
      rw [Measure.bind_bind (Measurable.of_discrete).aemeasurable hf.aemeasurable]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun b => ih b)

/-- `denote` preserves bind unconditionally when the program's result type is discrete. -/
theorem denote_bind_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (program : FreeM P α) (f : α → FreeM P β) :
    denote (FreeM.bind program f) = Measure.bind (denote program) fun x => denote (f x) :=
  denote_bind program f Measurable.of_discrete

/-- `denote` turns a measurable map of program outputs into the pushforward measure. -/
theorem denote_map_of_measurable [MeasurableSpace α] [MeasurableSpace β]
    (program : FreeM P α) (f : α → β) (hf : Measurable f) :
    denote (FreeM.map f program) = (denote program).map f := by
  rw [← FreeM.bind_pure_comp f program, denote_bind program (pure ∘ f)]
  · simpa only [Function.comp_apply, denote_pure] using
      Measure.bind_dirac_eq_map (denote program) hf
  · change Measurable (Measure.dirac ∘ f)
    exact Measure.measurable_dirac.comp hf

/-- `denote` preserves every output map from a discrete result type. -/
theorem denote_map_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (program : FreeM P α) (f : α → β) :
    denote (FreeM.map f program) = (denote program).map f :=
  denote_map_of_measurable program f Measurable.of_discrete

/-- Sequentially running two programs whose second execution does not depend on the first result
denotes the product of their measures. -/
theorem denote_bind_bind_prod_mk_eq_prod [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (left : FreeM P α) (right : FreeM P β) :
    denote (FreeM.bind left fun x =>
      FreeM.bind right fun y => pure (x, y)) =
        (denote left).prod (denote right) := by
  rw [denote_bind_of_discrete left, Measure.prod]
  exact Measure.bind_congr_right (Filter.Eventually.of_forall fun x => by
    change denote (FreeM.bind right fun y => pure (x, y)) =
      Measure.map (Prod.mk x) (denote right)
    rw [denote_bind right (fun y => pure (x, y))]
    · simpa only [denote_pure] using
        Measure.bind_dirac_eq_map (denote right) (by fun_prop)
    · change Measurable (Measure.dirac ∘ Prod.mk x)
      exact Measure.measurable_dirac.comp (by fun_prop))

end FreeM
end PFunctor
