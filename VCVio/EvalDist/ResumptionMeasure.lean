/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Resumption.Truncate
public import ToMathlib.MeasureTheory.Measure.Monotone
public import VCVio.EvalDist.MeasureSemantics

/-!
# Measure semantics of resumptions

PolyFun's `PFunctor.Resumption` represents computations that may expose infinitely many visible
queries and never return. The primitive denotational observations here follow its existing
`Resumption.truncate` surface:

* `truncateMeasure k computation` is a probability measure on `Option β`; `none` records that the
  computation did not return within `k` visible queries;
* `outputMeasure k computation` discards the `none` mass and is therefore a subprobability measure
  on returned values;
* `returnedMeasure computation` is the monotone supremum of those finite observations and records
  divergence as missing mass.

The total truncation and returned-output views are deliberately separate. A nonterminating
computation is not a failed ordinary result, and an infinite trace distribution is not determined
by pretending an arbitrary Lean continuation is measurable. A future infinite-trace semantics
should be constructed from a measurable coalgebra using Mathlib kernels and Ionescu--Tulcea; the
finite marginals here are the observable compatibility boundary such a construction must extend.
-/

@[expose] public section

open MeasureTheory

universe u uA

namespace PFunctor.Resumption

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.IsMeasureSpec]
  {β : Type u}

/-- The measure of the `k`-query truncation of a possibly nonterminating computation. -/
noncomputable def truncateMeasure [MeasurableSpace β] (k : ℕ)
    (computation : Resumption P β) : Measure (Option β) :=
  FreeM.denote (truncate k computation)

/-- The submeasure of values returned within `k` visible queries. Cutoff mass is discarded. -/
noncomputable def outputMeasure [MeasurableSpace β] (k : ℕ)
    (computation : Resumption P β) : Measure β :=
  (truncateMeasure k computation).dropNone

@[simp]
theorem truncateMeasure_pure [MeasurableSpace β] (k : ℕ) (result : β) :
    truncateMeasure k (pure (p := P) result) = Measure.dirac (some result) := by
  simp [truncateMeasure]

@[simp]
theorem truncateMeasure_query_zero [MeasurableSpace β] (position : P.A)
    (next : P.B position → Resumption P β) :
    truncateMeasure 0 (query position next) = Measure.dirac none := by
  simp [truncateMeasure]

@[simp]
theorem outputMeasure_pure [MeasurableSpace β] (k : ℕ) (result : β) :
    outputMeasure k (pure (p := P) result) = Measure.dirac result := by
  simp [outputMeasure]

@[simp]
theorem outputMeasure_query_zero [MeasurableSpace β] (position : P.A)
    (next : P.B position → Resumption P β) :
    outputMeasure 0 (query position next) = 0 := by
  simp [outputMeasure]

/-- After a visible query, successful output mass is the Giry bind of the answer measure with the
successful output mass of each continuation. -/
theorem outputMeasure_query_succ [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace β] (k : ℕ) (position : P.A)
    (next : P.B position → Resumption P β) :
    outputMeasure (k + 1) (query position next) =
      Measure.bind (IsMeasureSpec.toMeasure position) fun direction =>
        outputMeasure k (next direction) := by
  rw [outputMeasure, truncateMeasure, truncate_query_succ, FreeM.denote_liftBind]
  unfold Measure.dropNone
  rw [Measure.bind_bind Measurable.of_discrete.aemeasurable
    Measure.measurable_dropNoneKernel.aemeasurable]
  rfl

/-- Every finite truncation has total mass one when oracle responses are discrete. -/
theorem isProbabilityMeasure_truncateMeasure [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace β] (k : ℕ) (computation : Resumption P β) :
    IsProbabilityMeasure (truncateMeasure k computation) :=
  FreeM.isProbabilityMeasure_denote _

/-- Returned-output mass at finite fuel is at most one. -/
theorem outputMeasure_apply_univ_le_one [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace β] (k : ℕ) (computation : Resumption P β) :
    outputMeasure k computation Set.univ ≤ 1 := by
  calc
    outputMeasure k computation Set.univ ≤ truncateMeasure k computation Set.univ :=
      Measure.dropNone_apply_univ_le _
    _ = 1 := (isProbabilityMeasure_truncateMeasure k computation).measure_univ

/-! ## The returned-output limit -/

/-- Returned-output mass grows monotonically as more visible queries are observed. -/
theorem outputMeasure_le_succ [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace β] (k : ℕ) (computation : Resumption P β) :
    outputMeasure k computation ≤ outputMeasure (k + 1) computation := by
  induction k generalizing computation with
  | zero =>
      rcases hdest : dest computation with result | ⟨position, next⟩
      · have hcomputation : computation = pure (p := P) result :=
          eq_of_dest_eq (by simpa using hdest)
        subst computation
        simp
      · have hcomputation : computation = query position next :=
          eq_of_dest_eq (by simpa using hdest)
        subst computation
        rw [outputMeasure_query_zero]
        exact bot_le
  | succ k ih =>
      rcases hdest : dest computation with result | ⟨position, next⟩
      · have hcomputation : computation = pure (p := P) result :=
          eq_of_dest_eq (by simpa using hdest)
        subst computation
        simp
      · have hcomputation : computation = query position next :=
          eq_of_dest_eq (by simpa using hdest)
        subst computation
        rw [outputMeasure_query_succ, outputMeasure_query_succ]
        gcongr with direction
        · exact Measurable.of_discrete.aemeasurable
        · exact Measurable.of_discrete.aemeasurable
        · exact ih (next direction)

/-- The finite returned-output observations form an increasing sequence of measures. -/
theorem monotone_outputMeasure [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace β] (computation : Resumption P β) :
    Monotone fun k => outputMeasure k computation :=
  monotone_nat_of_le_succ fun k => outputMeasure_le_succ k computation

/-- The fuel-free measure of returned values. Divergence is represented by missing total mass. -/
noncomputable def returnedMeasure [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace β] (computation : Resumption P β) : Measure β :=
  ⨆ k, outputMeasure k computation

@[simp]
theorem returnedMeasure_pure [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace β] (result : β) :
    returnedMeasure (pure (p := P) result) = Measure.dirac result := by
  simp [returnedMeasure]

/-- Every finite observation is below the returned-output limit. -/
theorem outputMeasure_le_returnedMeasure [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace β] (k : ℕ) (computation : Resumption P β) :
    outputMeasure k computation ≤ returnedMeasure computation :=
  le_iSup (fun fuel => outputMeasure fuel computation) k

/-- On a measurable event, the returned-output measure is the supremum of its finite-fuel
probabilities. -/
theorem returnedMeasure_apply [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace β] (computation : Resumption P β) (event : Set β)
    (hEvent : MeasurableSet event) :
    returnedMeasure computation event = ⨆ k, outputMeasure k computation event :=
  Measure.iSup_apply_of_monotone _ (monotone_outputMeasure computation) event hEvent

/-- The fuel-free returned-output denotation is a subprobability measure. -/
theorem returnedMeasure_apply_univ_le_one [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace β] (computation : Resumption P β) :
    returnedMeasure computation Set.univ ≤ 1 := by
  rw [returnedMeasure_apply computation Set.univ MeasurableSet.univ]
  exact iSup_le fun k => outputMeasure_apply_univ_le_one k computation

end PFunctor.Resumption
