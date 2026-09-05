/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.ResumptionMeasure
public import VCVio.EvalDist.Divergence.KLDivergence
public import VCVio.EvalDist.ExpectationMeasure
public import VCVio.EvalDist.MeasureTVDist
public import VCVio.ProgramLogic.Relational.Measure
public import ToMathlib.Probability.Divergence.RenyiDiscrete
public import Mathlib.Probability.Distributions.Gaussian.Real
public import ToMathlib.MeasureTheory.DiscreteInstances
public import Examples.OneTimePad.Basic

/-!
# Canaries for the measure denotation

Two checks on `VCVio.EvalDist.PFunctorMeasure`, kept in the test library so they stay out of
the timed build.

`continuousOracle` is the capability check. It exhibits an oracle whose answers are drawn from
a continuous distribution, which `PFunctor.IsProbabilitySpec` cannot express at all: that class
carries a `Handler PMF P`, and `PMF.support_countable` makes every `PMF` countably supported,
whereas `ProbabilityTheory.gaussianReal` is not. The measure denotation gives it a meaning.

`discreteAgreement` is the compatibility check: on an interface carrying both interpretations,
the measure denotation is the measure of the `PMF` denotation, so existing probability
statements transport rather than needing reproof.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor OracleSpec OracleComp ENNReal

namespace VCVioTest.MeasureSemantics

/-! ## Optional measure kernels -/

example {α : Type*} [MeasurableSpace α] :
    Measurable (fun value : Option α => value.elim (0 : Measure α) Measure.dirac) := by
  fun_prop

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : β → Option α) (hf : Measurable f) :
    Measurable (fun b => (f b).elim (0 : Measure α) Measure.dirac) := by
  fun_prop

/-! ## A continuous oracle -/

/-- An interface with a single operation, answered by a real number. -/
@[expose, reducible] def gaussSpec : PFunctor.{0, 0} := ⟨PUnit, fun _ => ℝ⟩

/-- The operation is answered by a standard Gaussian.

There is no `PFunctor.IsProbabilitySpec gaussSpec`: its `toPMF` field would have to be a
`PMF ℝ`, and a `PMF` has countable support. -/
noncomputable instance : gaussSpec.IsMeasureSpec where
  toMeasure _ := gaussianReal 0 1
  isProbabilityMeasure _ := instIsProbabilityMeasureGaussianReal 0 1

/-- Sampling the oracle once denotes the standard Gaussian on `ℝ`.

This is the statement the conversion buys: it does not typecheck against a `PMF`-valued
semantics, because its subject is not a `PMF`. -/
theorem denote_gauss_lift :
    FreeM.denote (P := gaussSpec) (FreeM.lift PUnit.unit) = gaussianReal 0 1 := by
  change Measure.bind (gaussianReal 0 1)
      (fun b => FreeM.denote (P := gaussSpec) (Pure.pure b)) = _
  simp

/-- Primary notation selects the direct measure fold when no discrete backend exists. -/
example : 𝒟[(FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)] = gaussianReal 0 1 :=
  denote_gauss_lift

/-- The denoted measure really is a Gaussian law: its mass on a half-line is the Gaussian's,
so Mathlib's distribution API applies to the denotation directly rather than through a
translation layer. -/
example (s : Set ℝ) :
    FreeM.denote (P := gaussSpec) (FreeM.lift PUnit.unit) s = gaussianReal 0 1 s := by
  rw [denote_gauss_lift]

/-- A genuinely continuous continuation composes through the Giry bind once its measurability is
made explicit. -/
@[expose] noncomputable def shiftedGaussian : FreeM gaussSpec ℝ :=
  FreeM.liftBind PUnit.unit fun sample => pure (sample + 1)

theorem denote_shiftedGaussian :
    FreeM.denote shiftedGaussian =
      Measure.bind (gaussianReal 0 1) fun sample => Measure.dirac (sample + 1) :=
  rfl

/-- The continuous composition remains a probability measure. This proof is the canary for the
measurable-continuation boundary that a `PMF` semantics cannot state. -/
theorem isProbabilityMeasure_denote_shiftedGaussian :
    IsProbabilityMeasure (FreeM.denote shiftedGaussian) := by
  apply FreeM.isProbabilityMeasure_denote_liftBind
  · change AEMeasurable (fun sample : ℝ => Measure.dirac (sample + 1)) (gaussianReal 0 1)
    fun_prop
  · exact Filter.Eventually.of_forall fun _ => ⟨by simp⟩

/-! ## Native uniform semantics and composition laws -/

/-- A finite, inhabited interface used without a discrete probability interpretation. -/
@[expose, reducible] def nativeCoinSpec : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

instance : nativeCoinSpec.Fintype where
  fintypeB _ := inferInstance

instance : nativeCoinSpec.Inhabited where
  inhabitedB _ := inferInstance

/-- The native uniform measure interpretation is an explicit value, not a global instance. -/
@[instance_reducible]
noncomputable def nativeCoinMeasureSpec : nativeCoinSpec.IsMeasureSpec :=
  IsMeasureSpec.uniformOfFintypeInhabited _

attribute [local instance] nativeCoinMeasureSpec

/-- A native uniform operation denotes `uniformOn univ` directly. -/
theorem denote_nativeCoin_lift :
    FreeM.denote (FreeM.lift (P := nativeCoinSpec) PUnit.unit) =
      (uniformOn Set.univ : Measure Bool) := by
  rw [FreeM.denote_lift (P := nativeCoinSpec) PUnit.unit]
  rfl

/-! ## Measure-native distance and relational semantics -/

/-- Total variation is available directly on a continuous computation. -/
example : measureTVDist shiftedGaussian shiftedGaussian = 0 :=
  measureTVDist_self shiftedGaussian

/-- The diagonal construction couples a Gaussian measure with itself. -/
example : Measure.IsCoupling (Measure.Coupling.refl (gaussianReal 0 1)).joint
    (gaussianReal 0 1) (gaussianReal 0 1) :=
  (Measure.Coupling.refl (gaussianReal 0 1)).property

/-- Relational reasoning applies directly to a continuous denotation. -/
example : MeasureProgramLogic.RelWP shiftedGaussian shiftedGaussian (· = ·) :=
  MeasureProgramLogic.relWP_refl shiftedGaussian

/-! ## Agreement with the `PMF` denotation on a discrete interface -/

/-- An interface with a single operation, answered by a coin flip. -/
@[expose, reducible] def coinSpec : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

noncomputable instance : coinSpec.IsProbabilitySpec where
  toPMF _ := PMF.uniformOfFintype Bool

noncomputable instance : coinSpec.IsMeasureSpec where
  toMeasure _ := (PMF.uniformOfFintype Bool).toMeasure
  isProbabilityMeasure _ := PMF.toMeasure.isProbabilityMeasure _

/-- A nonzero, branch-sensitive lower bound rules out a vacuous quantitative semantics. -/
example : (1 : ℝ≥0∞) ≤
    MeasureProgramLogic.eRelWP (pure true : FreeM coinSpec Bool)
      (pure false : FreeM coinSpec Bool)
      (fun a b => if a && !b then 1 else 0) := by
  apply MeasureProgramLogic.le_eRelWP_pure_pure
  fun_prop

/-- On a discrete interface the two denotations agree, so a `Pr[…]` result proved against the
`PMF` semantics can be read off the measure semantics. -/
theorem denote_eq_toMeasure_coin {α : Type} [MeasurableSpace α]
    (program : FreeM coinSpec α) :
    FreeM.denote program = (program.liftM IsProbabilitySpec.toPMF).toMeasure :=
  FreeM.denote_eq_toMeasure (fun _ => rfl) program

/-- Predicate notation transports to arbitrary measurable events, not just singletons. -/
theorem denote_event_coin {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (program : FreeM coinSpec α) (event : α → Prop) :
    FreeM.denote program {x | event x} = Pr[event | program] :=
  FreeM.denote_apply_setOf (fun _ => rfl) program event MeasurableSet.of_discrete

/-- The reverse discrete adapter preserves both successful branches and missing mass. -/
example (p : SPMF Bool) :
    p.toMeasure.toSPMF (SPMF.toMeasure_apply_univ_le_one p) = p := by
  exact SPMF.toMeasure_toSPMF p

/-! ## Primary notation and the discrete compatibility surface -/

/-- The primary `𝒟[…]` notation is a subprobability measure. -/
example (program : FreeM coinSpec Bool) : 𝒟[program] Set.univ ≤ 1 :=
  evalDist_apply_univ_le_one program

/-- On a discrete `FreeM` program, primary notation agrees with the direct measure fold. -/
example (program : FreeM coinSpec Bool) : 𝒟[program] = FreeM.denote program :=
  FreeM.evalDist_eq_denote program

/-- Point notation is an explicit adapter to singleton mass in the primary measure. -/
example (program : FreeM coinSpec Bool) (x : Bool) :
    Pr[= x | program] = 𝒟[program] {x} :=
  (FreeM.evalDist_apply_singleton (fun _ => rfl) program x).symm

/-- Predicate notation is likewise an adapter to a measurable event. -/
example (program : FreeM coinSpec Bool) (event : Bool → Prop) :
    Pr[event | program] = 𝒟[program] {x | event x} :=
  (FreeM.evalDist_apply_setOf (fun _ => rfl) program event MeasurableSet.of_discrete).symm

/-- Crossing the compatibility boundary preserves perfect indistinguishability exactly. -/
example (p q : SPMF Bool) :
    Measure.tvDist p.toMeasure q.toMeasure = 0 ↔ SPMF.tvDist p q = 0 :=
  SPMF.toMeasure_tvDist_eq_zero_iff p q

/-- On the one-point observation space, the two TV distances agree numerically as well. -/
example (p q : SPMF.{0} PUnit.{1}) :
    Measure.tvDist p.toMeasure q.toMeasure = SPMF.tvDist p q :=
  SPMF.toMeasure_tvDist_punit p q

/-- Mapping a discrete program pushes its denoted measure forward. -/
example (program : FreeM coinSpec Bool) :
    FreeM.denote ((fun bit => !bit) <$> program) =
      (FreeM.denote program).map fun bit => !bit :=
  FreeM.denote_map_of_discrete program _

/-- Two answer-independent executions denote the Mathlib product measure. -/
example (first second : FreeM coinSpec Bool) :
    FreeM.denote (do
      let x ← first
      let y ← second
      pure (x, y)) = (FreeM.denote first).prod (FreeM.denote second) :=
  FreeM.denote_bind_bind_prod_mk_eq_prod first second

/-! ## Transformer stacks retain their effects -/

/-- The reusable total semantics for the discrete coin interface. -/
noncomputable def coinMeasureSemantics : ProbabilitySemantics (FreeM coinSpec) :=
  ProbabilitySemantics.freeM

/-- `OptionT` keeps `none` as an observable outcome until a proof explicitly discards it. -/
example (computation : OptionT (FreeM coinSpec) Bool) :
    IsProbabilityMeasure (coinMeasureSemantics.optionT computation) :=
  coinMeasureSemantics.isProbabilityMeasure_optionT computation

/-- `ExceptT` likewise retains the error branch as part of the total outcome space. -/
example (computation : ExceptT Bool (FreeM coinSpec) Bool) :
    IsProbabilityMeasure (coinMeasureSemantics.exceptT computation) :=
  coinMeasureSemantics.isProbabilityMeasure_exceptT computation

/-- `WriterT` retains the produced log alongside the result. -/
example (computation : WriterT Bool (FreeM coinSpec) Bool) :
    IsProbabilityMeasure (coinMeasureSemantics.writerT computation) :=
  coinMeasureSemantics.isProbabilityMeasure_writerT computation

/-- A reader computation exposes its environment as the input of a Markov kernel. -/
@[expose] def echoEnvironment : ReaderT Bool (FreeM coinSpec) Bool :=
  fun environment => pure environment

noncomputable def echoEnvironmentKernel : Kernel Bool Bool :=
  coinMeasureSemantics.readerTKernel echoEnvironment Measurable.of_discrete

example : IsMarkovKernel echoEnvironmentKernel := by
  unfold echoEnvironmentKernel
  infer_instance

example (environment : Bool) :
    echoEnvironmentKernel environment = Measure.dirac environment := rfl

/-- A stateful computation denotes a Markov kernel from initial states to result/final-state
pairs. Discreteness makes the kernel's measurability obligation immediate. -/
@[expose] def rememberState : StateT Bool (FreeM coinSpec) Bool :=
  fun state => pure (state, !state)

noncomputable def rememberStateKernel : Kernel Bool (Bool × Bool) :=
  coinMeasureSemantics.stateTKernel rememberState Measurable.of_discrete

example : IsMarkovKernel rememberStateKernel := by
  unfold rememberStateKernel
  infer_instance

example (state : Bool) :
    rememberStateKernel state = Measure.dirac (state, !state) := rfl

/-! ## Finite observations of possible nontermination -/

/-- A resumption that needs one visible query before returning. -/
@[expose] def delayedTrue : Resumption coinSpec Bool :=
  Resumption.query PUnit.unit fun _ => pure true

/-- At zero fuel the computation has no returned-output mass. -/
example : Resumption.outputMeasure 0 delayedTrue = 0 := by
  simp [delayedTrue]

/-- At one unit of fuel it has returned `true`; the cutoff marker has not been conflated with a
failure result. -/
theorem outputMeasure_one_delayedTrue :
    Resumption.outputMeasure 1 delayedTrue = Measure.dirac true := by
  change (Measure.bind (IsMeasureSpec.toMeasure (P := coinSpec) PUnit.unit)
    (fun _ => Measure.dirac (some true))).dropNone = Measure.dirac true
  rw [Measure.bind_const,
    (IsMeasureSpec.isProbabilityMeasure (P := coinSpec) PUnit.unit).measure_univ, one_smul]
  simp

/-- The fuel-free returned-output semantics sees the delayed return with total mass one. -/
example : Resumption.returnedMeasure delayedTrue Set.univ = 1 := by
  apply le_antisymm (Resumption.returnedMeasure_apply_univ_le_one delayedTrue)
  calc
    1 = Resumption.outputMeasure 1 delayedTrue Set.univ := by
      rw [outputMeasure_one_delayedTrue]
      simp
    _ ≤ Resumption.returnedMeasure delayedTrue Set.univ :=
      (Resumption.outputMeasure_le_returnedMeasure 1 delayedTrue) Set.univ

/-! ## Transporting an existing `Pr[…]` result

`unifSpec` is discrete, so it induces a measure interpretation and the singleton bridge
applies. Any probability already proved about a `ProbComp` is then a fact about its measure
denotation, with no reproof. -/

noncomputable instance : unifSpec.toPFunctor.IsMeasureSpec :=
  PFunctor.IsProbabilitySpec.toMeasureSpec _

theorem denote_probComp_apply_singleton {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (program : ProbComp α) (x : α) :
    FreeM.denote program {x} = Pr[= x | program] :=
  FreeM.denote_apply_singleton (fun _ => rfl) program x

/-- The one-time-pad ciphertext is uniform, read off the measure denotation.

The statement is about a Mathlib `Measure`; the proof is the existing `Pr[…]` result. This is
the compatibility gate: converting the semantics does not cost the crypto proofs. -/
example (sp : ℕ) (mgen : ProbComp (BitVec sp)) (σ : BitVec sp) :
    FreeM.denote ((oneTimePad sp).PerfectSecrecyCipherExp mgen) {σ}
      = (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  rw [denote_probComp_apply_singleton]
  exact oneTimePad.probOutput_cipher_uniform sp mgen σ

/-! ## Divergence

The point of denoting into `Measure` is that Mathlib's probability library then applies to
VCVio programs directly. Kullback-Leibler is the check: it does not exist anywhere in the
`SPMF` layer, and here it arrives with its data-processing inequalities already proved. -/

open InformationTheory

/-- Post-processing two computations by the same continuation cannot increase their divergence.

This is the game-hopping shape, and it is Mathlib's `klDiv_comp_right_le` — `Measure.bind` and
kernel composition are the same operation, so no transport is involved. -/
example {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (mx my : ProbComp α) (f : α → ProbComp β) :
    klDiv (FreeM.denote (mx >>= f)) (FreeM.denote (my >>= f))
      ≤ klDiv (FreeM.denote mx) (FreeM.denote my) :=
  FreeM.klDiv_denote_bind_le mx my f

/-- The same for post-processing by a function. -/
example {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (g : α → β) (mx my : ProbComp α) :
    klDiv (FreeM.denote (g <$> mx)) (FreeM.denote (g <$> my))
      ≤ klDiv (FreeM.denote mx) (FreeM.denote my) :=
  FreeM.klDiv_denote_map_le g mx my

/-- Divergence between *continuous* denotations is expressible at all.

`klDiv` here is applied to two measures on `ℝ` that no `PMF` can carry, so this statement has no
counterpart in the `SPMF` layer — not a harder proof there, but not a well-formed statement. -/
example : klDiv (FreeM.denote (P := gaussSpec) (FreeM.lift PUnit.unit))
    (FreeM.denote (P := gaussSpec) (FreeM.lift PUnit.unit)) = 0 := by
  rw [denote_gauss_lift]
  exact klDiv_self _

/-! ## Expectation as an integral

`expectedValue` keeps its `∑'` definition and every proof written against it, while the same
quantity becomes a `∫⁻` on request. Monotone convergence is the payoff: there is no `∑'`-shaped
counterpart to it in the library. -/

open OracleComp.EvalDist in
/-- The existing sum spelling is untouched. -/
example (n : ℕ) (mx : ProbComp (BitVec n)) (g : BitVec n → ℝ≥0∞) :
    expectedValue mx g = ∑' x, Pr[= x | mx] * g x := expectedValue_def mx g

open OracleComp.EvalDist in
/-- ...and is an integral against the denoted measure. -/
example (n : ℕ) (mx : ProbComp (BitVec n)) (g : BitVec n → ℝ≥0∞) :
    expectedValue mx g = ∫⁻ x, g x ∂(toMeasure mx) := expectedValue_eq_lintegral mx g

open OracleComp.EvalDist in
/-- **Monotone convergence** for a VCVio expectation, from `lintegral_iSup`. -/
example (n : ℕ) (mx : ProbComp (BitVec n)) (g : ℕ → BitVec n → ℝ≥0∞) (hg : Monotone g) :
    expectedValue mx (fun x => ⨆ k, g k x) = ⨆ k, expectedValue mx (g k) :=
  expectedValue_iSup mx g hg

/-! ## Renyi divergence, at both ends of the boundary

The measure-level Renyi MGF is stated for arbitrary measures, so it covers laws no `PMF` can
carry, and it agrees exactly with the countably supported formula where both are defined. The
discrete development is therefore a corollary rather than a parallel copy. -/

/-- Renyi between two continuous laws — no `PMF` counterpart exists. -/
example (a : ℝ) : renyiMGF a (gaussianReal 0 1) (gaussianReal 0 1) = 1 := renyiMGF_self a _

/-- `PMF.renyiMGF_map_le` is now the measure-level result, and it still carries no instances.

The carrier here is `ℝ`, which is uncountable and has no discrete measurable structure. That is
the point of the corollary being stated without a `Countable` hypothesis: a `PMF` has countable
support whatever its carrier, so the bridge must not demand countability of the carrier itself —
otherwise it could not reach `SPMF.renyiDiv_map_le`, which instantiates at `Option α'` for an
arbitrary `α'`. -/
example (a : ℝ) (ha : 1 ≤ a) (f : ℝ → ℝ) (p q : PMF ℝ) :
    (f <$> p).renyiMGF a (f <$> q) ≤ p.renyiMGF a q :=
  PMF.renyiMGF_map_le a ha f p q

/-- **The Rényi → total-variation bound**, which was `sorry` until the measure-level theory
supplied both of its halves.

`#396` calls this "the headline Rényi → eTV-distance bound". Its two ingredients — Cauchy-Schwarz
against the Hellinger affinity, and log-convexity of the Rényi MGF — both reduce to the same
Mathlib inequality, `ENNReal.lintegral_mul_norm_pow_le`. -/
example (n : ℕ) (a : ℝ) (ha : 1 < a) (p q : PMF (BitVec n)) :
    p.etvDist q ^ (2 : ℝ) ≤ 1 - (p.renyiDiv a q)⁻¹ :=
  PMF.etvDist_sq_le_of_renyiDiv a ha p q

/-- ...and it is the existing discrete formula on a finite sample type. -/
example (n : ℕ) (a : ℝ) (ha : 1 < a) (p q : PMF (BitVec n)) :
    renyiMGF a p.toMeasure q.toMeasure = PMF.renyiMGF a p q := renyiMGF_toMeasure a ha p q

end VCVioTest.MeasureSemantics
