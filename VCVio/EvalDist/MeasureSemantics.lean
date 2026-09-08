/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.MeasureTheory.MeasurableSpace.Except
public import ToMathlib.MeasureTheory.Measure.Option
public import VCVio.EvalDist.Kernel
public import VCVio.EvalDist.PFunctorMeasure
public import Mathlib.Control.Monad.Writer

/-!
# Measure semantics for monads and transformer stacks

`ProbabilitySemantics m` is the small lossless denotational interface used at VCVio's boundary with
Mathlib. It interprets `m α` as an ordinary `Measure α` and records that the measure has total mass
one. It intentionally does not pretend that `Measure` is a universe-polymorphic Lean monad:
measurable spaces and measurable continuations remain visible where Mathlib requires them.

The transformer operations retain effects in the denoted output:

* `OptionT` denotes a measure on `Option α`, rather than immediately discarding failure;
* `ExceptT` denotes a measure on `Except ε α`;
* `WriterT` denotes a measure on `α × ω`;
* `ReaderT` and `StateT` denote Mathlib kernels, with the required measurability proof explicit.

Observers such as `Measure.dropNone`, `Measure.map Prod.fst`, and measurable event evaluation can
then be selected by the proof that needs them. This keeps distinct effects observable and avoids
global transformer instances that silently choose an environment, initial state, or failure policy.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe u v uA

/-- A lossless measure-valued denotation for a type constructor.

The output's `MeasurableSpace` is an explicit typeclass argument because it is semantic data, not
structure carried by the Lean type itself. -/
structure ProbabilitySemantics (m : Type u → Type v) extends EvalDistSemantics m where
  /-- The denotation of a total computation has mass one. -/
  isProbabilityMeasure : ∀ {α : Type u} [MeasurableSpace α] (computation : m α),
    IsProbabilityMeasure (denote computation)

namespace ProbabilitySemantics

variable {m : Type u → Type v} {α ε ω ρ σ : Type u}

/-- The discrete `FreeM` measure denotation packaged as a reusable semantics. -/
noncomputable def freeM {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)]
    [P.IsMeasureSpec] [∀ a, DiscreteMeasurableSpace (P.B a)] :
    ProbabilitySemantics (PFunctor.FreeM P) where
  denote := PFunctor.FreeM.denote
  apply_univ_le_one := PFunctor.FreeM.denote_apply_univ_le_one
  isProbabilityMeasure := PFunctor.FreeM.isProbabilityMeasure_denote

variable (semantics : ProbabilitySemantics m)

/-! ## Effect-preserving transformer denotations -/

/-- Denote an `OptionT` computation without erasing whether it returned `none`. -/
noncomputable def optionT [MeasurableSpace α] (computation : OptionT m α) :
    Measure (Option α) :=
  semantics.denote computation.run

theorem isProbabilityMeasure_optionT [MeasurableSpace α] (computation : OptionT m α) :
    IsProbabilityMeasure (semantics.optionT computation) :=
  semantics.isProbabilityMeasure computation.run

/-- Denote an `ExceptT` computation without erasing its error value. -/
noncomputable def exceptT [MeasurableSpace ε] [MeasurableSpace α]
    (computation : ExceptT ε m α) : Measure (Except ε α) :=
  semantics.denote computation.run

theorem isProbabilityMeasure_exceptT [MeasurableSpace ε] [MeasurableSpace α]
    (computation : ExceptT ε m α) :
    IsProbabilityMeasure (semantics.exceptT computation) :=
  semantics.isProbabilityMeasure computation.run

/-- Denote a `WriterT` computation together with its final log. -/
noncomputable def writerT [MeasurableSpace ω] [MeasurableSpace α]
    (computation : WriterT ω m α) : Measure (α × ω) :=
  semantics.denote computation.run

theorem isProbabilityMeasure_writerT [MeasurableSpace ω] [MeasurableSpace α]
    (computation : WriterT ω m α) :
    IsProbabilityMeasure (semantics.writerT computation) :=
  semantics.isProbabilityMeasure computation.run

/-! ## Environment- and state-indexed kernels -/

/-- A reader computation is a kernel from environments to output distributions.

`hMeasurable` is the semantic well-formedness obligation: arbitrary Lean functions need not be
measurable. Keeping it as an argument is what permits continuous environments without making an
unsound blanket assumption. -/
noncomputable def readerTKernel [MeasurableSpace ρ] [MeasurableSpace α]
    (computation : ReaderT ρ m α)
    (hMeasurable : Measurable fun environment => semantics.denote (computation environment)) :
    Kernel ρ α :=
  ⟨fun environment => semantics.denote (computation environment), hMeasurable⟩

@[simp]
theorem readerTKernel_apply [MeasurableSpace ρ] [MeasurableSpace α]
    (computation : ReaderT ρ m α)
    (hMeasurable : Measurable fun environment => semantics.denote (computation environment))
    (environment : ρ) :
    semantics.readerTKernel computation hMeasurable environment =
      semantics.denote (computation environment) := rfl

instance isMarkovKernel_readerTKernel [MeasurableSpace ρ] [MeasurableSpace α]
    (computation : ReaderT ρ m α)
    (hMeasurable : Measurable fun environment => semantics.denote (computation environment)) :
    IsMarkovKernel (semantics.readerTKernel computation hMeasurable) where
  isProbabilityMeasure environment :=
    semantics.isProbabilityMeasure (computation environment)

/-- A state computation is a kernel from its initial state to its result and final state.

Fixing an initial state recovers the usual measure of a run, but the kernel is the compositional
object: it retains the state threaded to the next computation. -/
noncomputable def stateTKernel [MeasurableSpace σ] [MeasurableSpace α]
    (computation : StateT σ m α)
    (hMeasurable : Measurable fun state => semantics.denote (computation state)) :
    Kernel σ (α × σ) :=
  ⟨fun state => semantics.denote (computation state), hMeasurable⟩

@[simp]
theorem stateTKernel_apply [MeasurableSpace σ] [MeasurableSpace α]
    (computation : StateT σ m α)
    (hMeasurable : Measurable fun state => semantics.denote (computation state))
    (state : σ) :
    semantics.stateTKernel computation hMeasurable state =
      semantics.denote (computation state) := rfl

instance isMarkovKernel_stateTKernel [MeasurableSpace σ] [MeasurableSpace α]
    (computation : StateT σ m α)
    (hMeasurable : Measurable fun state => semantics.denote (computation state)) :
    IsMarkovKernel (semantics.stateTKernel computation hMeasurable) where
  isProbabilityMeasure state :=
    semantics.isProbabilityMeasure (computation state)

end ProbabilitySemantics
