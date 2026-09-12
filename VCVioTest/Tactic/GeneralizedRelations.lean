/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.ProgramLogic.Unary.HoareTriple
public import ToMathlib.MeasureTheory.Measure.Monotone
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Tactic.GRewrite

/-!
# Generalized congruence and rewriting

Ordinary-import tests for probability, support, cost predicates, and measure bind. Terminal
examples exercise `gcongr`, `grw`, and `rel`; interactive examples pin the obligations exposed by
congruence and rewrite normalization. Dated gap pairs distinguish partial progress from closure.
The companion `GeneralizedRelationsExperiments` module isolates proposed registrations.
-/

public section

open OracleComp OracleComp.EvalDist OracleComp.ProgramLogic OracleSpec MeasureTheory
open scoped ENNReal

namespace VCVioTest.GeneralizedRelations

/-! ## Existing expectation and event rules -/

section Probability

variable {α β : Type} (mx : ProbComp α) (f g : α → ℝ≥0∞)

example (h : ∀ x, f x ≤ g x) : expectedValue mx f ≤ expectedValue mx g := by grw [h]

example (h : ∀ x ∈ support mx, f x ≤ g x) :
    expectedValue mx f ≤ expectedValue mx g := by
  -- gap(gcongr, 2026-09-08): the support-restricted hypothesis needs an explicit application.
  fail_if_success (gcongr; done)
  gcongr with x hx
  guard_hyp hx : x ∈ support mx
  guard_target = f x ≤ g x
  exact h x hx

/-- A rewrite theorem's own support premise remains a side goal. -/
example (h : ∀ x ∈ support mx, f x ≤ g x) :
    expectedValue mx f ≤ expectedValue mx g := by
  -- gap(grw, 2026-09-08): the rewrite's support premise needs an explicit closer.
  fail_if_success (grw [h]; done)
  grw [h]
  assumption

-- Support-restricted `grw` on WP and nested expectations shares the gap above.
example (h : ∀ x ∈ support mx, f x ≤ g x) : wp mx f ≤ wp mx g := by
  grw [h]
  assumption

example (h : ∀ x ∈ support mx, f x ≤ g x) :
    Std.Do'.wp mx f Lean.Order.bot ≤ Std.Do'.wp mx g Lean.Order.bot := by
  -- gap(gcongr, 2026-09-08): the raw WP head needs explicit facade normalization.
  fail_if_success gcongr
  change wp mx f ≤ wp mx g
  guard_target = wp mx f ≤ wp mx g
  gcongr with x hx
  guard_hyp hx : x ∈ support mx
  guard_target = f x ≤ g x
  exact h x hx

example (p q : α → Prop) (h : ∀ x, p x → q x) : Pr[ p | mx] ≤ Pr[ q | mx] := by
  apply_rw [h]

example (p q : α → Prop) (h : ∀ x, p x → q x) (c : ℝ≥0∞)
    (hq : Pr[ q | mx] ≤ c) : Pr[ p | mx] ≤ c := by
  apply_rw [h]
  guard_target = Pr[ q | mx] ≤ c
  exact hq

example (h : ∀ x, g x ≤ f x) : 1 - expectedValue mx f ≤ 1 - expectedValue mx g := by
  grw [h]

example (h : ∀ x, f x ≤ g x) (c : ℝ≥0∞) (hf : c ≤ expectedValue mx f) :
    c ≤ expectedValue mx g := by
  grw [h] at hf
  guard_hyp hf : c ≤ expectedValue mx g
  exact hf

example (f' g' : α → ProbComp β) (p : β → Prop)
    (h : ∀ x ∈ support mx, Pr[ p | f' x] ≤ Pr[ p | g' x]) :
    Pr[ p | mx >>= f'] ≤ Pr[ p | mx >>= g'] := by
  -- gap(gcongr, 2026-09-08): bind probability needs the expectation normal form.
  fail_if_success gcongr
  rw [probEvent_bind_eq_expectedValue, probEvent_bind_eq_expectedValue]
  grw [h]
  assumption

example (my : α → ProbComp β) (u v : α → β → ℝ≥0∞)
    (h : ∀ x ∈ support mx, ∀ y ∈ support (my x), u x y ≤ v x y) :
    expectedValue mx (fun x => expectedValue (my x) (u x)) ≤
      expectedValue mx (fun x => expectedValue (my x) (v x)) := by
  grw [h] <;> assumption

example (h : ∀ x, f x ≤ g x) :
    expectedValue mx f + expectedValue mx f ≤ expectedValue mx g + expectedValue mx f := by
  -- gap(nth_grw, 2026-09-08): occurrence abstraction does not eta-expand the function argument.
  fail_if_success nth_grw 1 [h]
  nth_grw 1 [expectedValue_mono mx h]

/-- `rel` is a finishing tactic with an explicit list of main-goal facts. -/
example (a b c d : ℝ≥0∞) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  rel [hab, hcd]

example (a b c d : ℝ≥0∞) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  fail_if_success rel [hab]
  rel [hab, hcd]

end Probability

/-! ## Support does not require probability semantics -/

example {ι α : Type} {spec : OracleSpec ι} (oa : OracleComp spec α)
    (o₁ o₂ : QueryImpl spec Set) (h : ∀ q, o₁ q ⊆ o₂ q) :
    supportWhen o₁ oa ⊆ supportWhen o₂ oa := by
  gcongr with q
  guard_target = o₁ q ⊆ o₂ q
  exact h q

/-! ## Implication through cost predicates -/

section Costs

variable {α : Type} {m : Type → Type*} [Monad m] [MonadLiftT m SetM]
variable (oa : AddWriterT ℕ m α) {a b c : ℕ}

example (h : a ≤ b) :
    AddWriterT.QueryBoundedAboveBy oa a → AddWriterT.QueryBoundedAboveBy oa b := by gcongr

example (h : a ≤ b) :
    AddWriterT.QueryBoundedAboveBy oa (a + c) →
      AddWriterT.QueryBoundedAboveBy oa (b + c) := by gcongr

-- Goal and hypothesis rewrites below pin the normalized certificate; the closer supplies it.
example (h : a ≤ b) (ha : AddWriterT.QueryBoundedAboveBy oa a) :
    AddWriterT.QueryBoundedAboveBy oa b := by
  -- gap(grw, 2026-09-08): rewriting the bound does not close from a certificate in context.
  fail_if_success (grw [← h]; done)
  grw [← h]
  guard_target = AddWriterT.QueryBoundedAboveBy oa a
  exact ha

example (h : a ≤ b) (ha : AddWriterT.QueryBoundedAboveBy oa a) :
    AddWriterT.QueryBoundedAboveBy oa b := by
  grw +useKAbstract [← h]
  guard_target = AddWriterT.QueryBoundedAboveBy oa a
  exact ha

example (h : a ≤ b) (ha : AddWriterT.QueryBoundedAboveBy oa a) :
    AddWriterT.QueryBoundedAboveBy oa b := by
  grw [h] at ha
  guard_hyp ha : AddWriterT.QueryBoundedAboveBy oa b
  exact ha

example (h : a ≤ b) (hcost : AddWriterT.QueryBoundedAboveBy oa (a + c)) :
    AddWriterT.QueryBoundedAboveBy oa (b + c) := by
  grw [← h]
  guard_target = AddWriterT.QueryBoundedAboveBy oa (a + c)
  exact hcost

/-- Bounds can be weakened, but these rules cannot strengthen them. -/
example (h : a ≤ b) (ha : AddWriterT.QueryBoundedAboveBy oa a) :
    AddWriterT.QueryBoundedAboveBy oa b := by
  fail_if_success grw [h]
  grw [← h]
  guard_target = AddWriterT.QueryBoundedAboveBy oa a
  exact ha

example {ω : Type} [AddCommMonoid ω] [PartialOrder ω]
    (oa : AddWriterT ω m α) {a b : ω} (h : a ≤ b) :
    AddWriterT.PathwiseCostAtMost oa a → AddWriterT.PathwiseCostAtMost oa b := by gcongr

example {ω : Type} [AddCommMonoid ω] [PartialOrder ω]
    (oa : AddWriterT ω m α) {a b : ω} (h : a ≤ b)
    (ha : AddWriterT.PathwiseCostAtMost oa a) : AddWriterT.PathwiseCostAtMost oa b := by
  grw [← h]
  guard_target = AddWriterT.PathwiseCostAtMost oa a
  exact ha

example {ι : Type} (oa : AddWriterT (ι → ℕ) m α) {a b : ι → ℕ}
    (h : ∀ i, a i ≤ b i) :
    AddWriterT.PathwiseCostAtMost oa a → AddWriterT.PathwiseCostAtMost oa b := by
  -- gap(gcongr, 2026-09-08): function order remains a main goal after cost descent.
  fail_if_success (gcongr; done)
  gcongr
  guard_target = a ≤ b
  exact h

example (oa : AddWriterT ℝ≥0∞ m α) (a : ℝ≥0∞) :
    AddWriterT.PathwiseCostAtMost oa a → AddWriterT.PathwiseCostAtMost oa ⊤ := by
  rel [show a ≤ ⊤ from le_top]

end Costs

/-! ## Measures and measurable kernels -/

section Measures

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) (f g : α → Measure β)

example (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (h : ∀ x, f x ≤ g x) :
    μ.bind f ≤ μ.bind g := by grw [h]

example (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (h : ∀ x, f x ≤ g x) :
    μ.bind f ≤ μ.bind g := by
  gcongr with x
  guard_target = f x ≤ g x
  exact h x

/-- Monotonicity does not silently assume measurability. -/
example (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (h : ∀ x, f x ≤ g x) :
    μ.bind f ≤ μ.bind g := by
  fail_if_success (clear hf hg; grw [h]; done)
  grw [h]

example (h : ∀ᵐ x ∂μ, f x ≤ g x) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    μ.bind f ≤ μ.bind g := by
  -- gap(gcongr, 2026-09-08): the registered pointwise rule cannot consume an AE bound.
  fail_if_success (gcongr; done)
  exact Measure.bind_mono_right hf hg h

example (κ η : ProbabilityTheory.Kernel α β) (h : ∀ x, κ x ≤ η x) :
    μ.bind κ ≤ μ.bind η := by
  -- gap(grw, 2026-09-08): bundled kernel measurability must be supplied to the discharger.
  fail_if_success (grw [h]; done)
  have hκ := κ.measurable.aemeasurable (μ := μ)
  have hη := η.measurable.aemeasurable (μ := μ)
  grw [h]

/-! Nested binds distinguish measurability of the outer continuation from measurability in
each inner source. Universal measurability hypotheses need explicit application. -/

variable {γ : Type*} [MeasurableSpace γ] (k : α → Measure β) (u v : β → Measure γ)

example (hku : AEMeasurable (fun x => (k x).bind u) μ)
    (hkv : AEMeasurable (fun x => (k x).bind v) μ)
    (hu : ∀ x, AEMeasurable u (k x)) (hv : ∀ x, AEMeasurable v (k x))
    (h : ∀ y, u y ≤ v y) :
    μ.bind (fun x => (k x).bind u) ≤ μ.bind (fun x => (k x).bind v) := by
  -- gap(grw, 2026-09-08): the discharger does not apply quantified measurability hypotheses.
  fail_if_success (grw [h]; done)
  grw [h]
  case hf x =>
    guard_target = AEMeasurable u (k x)
    exact hu x
  case hg x =>
    guard_target = AEMeasurable (fun y => v y) (k x)
    exact hv x

example (hu : AEMeasurable u (μ.bind k)) (hv : AEMeasurable v (μ.bind k))
    (h : ∀ y, u y ≤ v y) : (μ.bind k).bind u ≤ (μ.bind k).bind v := by grw [h]

example (hu : AEMeasurable u (μ.bind k)) (hv : AEMeasurable v (μ.bind k))
    (h : ∀ y, u y ≤ v y) (ν : Measure γ) (hν : ν ≤ (μ.bind k).bind u) :
    ν ≤ (μ.bind k).bind v := by
  grw [h] at hν
  guard_hyp hν : ν ≤ (μ.bind k).bind v
  exact hν

end Measures

end VCVioTest.GeneralizedRelations
