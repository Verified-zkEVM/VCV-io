/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.DynSystem
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.EvalDist.Kernel
public import PolyFun.PFunctor.Dynamical.Game

/-!
# Probabilistic Wiring: Adversary Strategies Against Stateful Responders

`ProbResponder spec` is the challenger side of an interactive game presented as a
coalgebra: a measurable state space together with, for each query, a *joint*
subprobability kernel over the answer and the next state. It is a Mealy machine in the
Kleisli category of subprobability kernels. An optional coherent executable
presentation as a stateful handler `QueryImpl spec (StateT State SPMF)` remains
available through `ProbResponder.IsExecutable`, `ProbResponder.answer`, and
`ProbResponder.toQueryImpl`.

Wiring a responder against an adversary `OracleStrategy` is not a hand-rolled
construction: `stepAgainst` / `iterateAgainst` are PolyFun's generic eval-wired runs
`PFunctor.DynSystem.stepWith` / `iterWith` instantiated at `m := SPMF`, driven by the
responder's stateful handler. The responder state comes first in the product state,
matching the upstream handler-state-first convention and the challenger-first state of
`PFunctor.DynSystem.closedGame`; a deterministic responder (`ProbResponder.ofDet`) wires
to `pure` of the closed-game step (`stepAgainst_ofDet`). `transcriptAgainst` additionally
records the exchanged queries and answers — `QueryLog` is VCVio vocabulary, so the
transcript form lives here rather than upstream.

Memoryless oracles embed as responders with trivial (`ProbResponder.ofHandler`) or
constant (`ProbResponder.ofHandlerFamily`) state, and the wired run then collapses to
the existing memoryless runs `OracleStrategy.kleisliStep` / `kleisliIterate`
(`stepAgainst_ofHandler` and companions) — the setup-indexed family form of the upstream
stateless collapses `PFunctor.DynSystem.stepWith_lift` / `iterWith_lift`. The
per-run-sampled oracle of a one-shot security game is exactly the constant-state case.
Genuinely stateful challengers enter through `ProbResponder.ofQueryImpl` (from a
`QueryImpl` into `StateT σ SPMF`) or `ProbResponder.ofStateQueryImpl` (from a
`QueryImpl` into `StateT σ ProbComp`, via its evaluation distribution): the lazy random
oracle (`randomOracleResponder`) is the motivating instance, and cached LR encryption
oracles fit the same constructor at the `CryptoFoundations` layer. The joint
answer/state draw is essential for these — the cache entry a random oracle stores must
be the very answer it returned.

## Categorical view (Spivak–Niu)

A *deterministic* responder is a dynamical system over the internal hom `[p, y]` of
Spivak–Niu §4.5 (for `p` the interface polynomial `spec.toPFunctor`) — PolyFun's
`PFunctor.Responder`, which embeds here as the Dirac case `ProbResponder.ofDet`.
Closing an adversary against a responder is wiring along the evaluation map
`eval : [p, y] ⊗ p → y`: `stepAgainst` keeps that wiring as deterministic combinatorial
data and lets the *states* advance in the Kleisli category of the commutative monad
`SPMF` — one synchronized step of the tensor system with the evaluation wiring applied,
which is precisely the upstream `stepWith`. `ProbResponder` is strictly more general
than a Kleisli lift of an `[p, y]`-system, because the answer and the next state are
drawn jointly rather than the state first determining a handler. The UC layer's
`processSemanticsOracle` is the heavyweight sibling of this construction (multi-party,
scheduler-driven); this file is the minimal two-party core, and neither is derived from
the other.

Wired runs of machine adversaries (an `OracleMachine.runK` against a responder rather
than a memoryless handler) live in `VCVio.OracleComp.Coinductive.WiredRun`.
-/

@[expose] public section

universe u v

open OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {S : Type u}

/-! ## Probabilistic stateful responders -/

/-- A probabilistic stateful responder: the challenger side of an interactive game, as
a Mealy coalgebra in the Kleisli category of subprobability kernels. From a state, each
query yields a joint subprobability measure over the answer and the successor state.
The joint draw matters:
a lazy random oracle's stored cache entry must be the very answer it returned, which no
answer-then-state factorization expresses. -/
structure ProbResponder {ι : Type u} (spec : OracleSpec.{u, u} ι) where
  /-- The responder's internal state (the challenger's memory). -/
  State : Type u
  /-- The measurable structure on the responder's private state. -/
  instMeasurableSpaceState : MeasurableSpace State
  /-- The measurable structure on the answer to each query. -/
  instMeasurableSpaceRange : (t : spec.Domain) → MeasurableSpace (spec.Range t)
  /-- Answer a query from a state, jointly drawing the successor state. -/
  answerKernel : (t : spec.Domain) →
    letI := instMeasurableSpaceState
    letI := instMeasurableSpaceRange t
    ProbabilityTheory.Kernel State (spec.Range t × State)
  /-- Each query kernel is subprobabilistic. -/
  answerKernel_isSubprobability : ∀ t,
    letI := instMeasurableSpaceState
    letI := instMeasurableSpaceRange t
    ProbabilityTheory.IsSubprobabilityKernel (answerKernel t)

attribute [instance] ProbResponder.instMeasurableSpaceState

namespace ProbResponder

open MeasureTheory ProbabilityTheory

/-- The subprobability invariant stored by a responder, exposed as an instance. -/
instance answerKernel.instIsSubprobabilityKernel (R : ProbResponder spec)
    (t : spec.Domain) :
    letI := R.instMeasurableSpaceRange t
    IsSubprobabilityKernel (R.answerKernel t) :=
  R.answerKernel_isSubprobability t

/-- A coherent executable realization of a kernel responder. This separate typeclass
lets kernel-native responders remain genuinely measure-theoretic, while responders
built from VCVio's SPMF/ProbComp execution layer retain their original executable
program without imposing countability on abstract state or answer types. -/
class IsExecutable (R : ProbResponder spec) where
  /-- The executable answer-and-successor-state subdistribution. -/
  answerSPMF : R.State → (t : spec.Domain) → SPMF (spec.Range t × R.State)
  /-- Executable states must be point-separating in the responder's measurable structure. -/
  instMeasurableSingletonClassState :
    letI := R.instMeasurableSpaceState
    MeasurableSingletonClass R.State
  /-- Executable answers must be point-separating in the responder's measurable structure. -/
  instMeasurableSingletonClassRange : ∀ t,
    letI := R.instMeasurableSpaceRange t
    MeasurableSingletonClass (spec.Range t)
  /-- The executable realization denotes exactly the stored answer kernel. -/
  answerKernel_eq_toMeasure : ∀ s t,
    letI := R.instMeasurableSpaceRange t
    R.answerKernel t s = (answerSPMF s t).toMeasure

/-- The authoritative kernel uniquely determines an executable realization. Point-separating
measurable spaces are essential here: equality as measures can otherwise forget distinctions
between individual executable outcomes. -/
theorem IsExecutable.answerSPMF_unique (R : ProbResponder spec)
    (E₁ E₂ : R.IsExecutable) (s : R.State) (t : spec.Domain) :
    E₁.answerSPMF s t = E₂.answerSPMF s t := by
  let _ := R.instMeasurableSpaceRange t
  let _ : MeasurableSingletonClass R.State := E₁.instMeasurableSingletonClassState
  let _ : MeasurableSingletonClass (spec.Range t) :=
    E₁.instMeasurableSingletonClassRange t
  apply SPMF.toMeasure_injective
  rw [← E₁.answerKernel_eq_toMeasure s t, ← E₂.answerKernel_eq_toMeasure s t]

/-- Build a kernel responder from an executable SPMF-valued stateful handler. The
constructor equips the state and answers with local discrete measurable structures;
it does not install blanket measurable-space instances on the underlying types. -/
@[reducible] noncomputable def ofSPMF {σ : Type u}
    (impl : QueryImpl spec (StateT σ SPMF)) : ProbResponder spec where
  State := σ
  instMeasurableSpaceState := ⊤
  instMeasurableSpaceRange := fun _ => ⊤
  answerKernel t := by
    letI : MeasurableSpace σ := ⊤
    letI : MeasurableSpace (spec.Range t) := ⊤
    exact evalDistKernelOfDiscrete (fun s => impl t s)
  answerKernel_isSubprobability t := by infer_instance

instance ofSPMF.instIsExecutable {σ : Type u}
    (impl : QueryImpl spec (StateT σ SPMF)) : (ofSPMF impl).IsExecutable where
  answerSPMF s t := impl t s
  instMeasurableSingletonClassState := inferInstance
  instMeasurableSingletonClassRange _ := inferInstance
  answerKernel_eq_toMeasure _ _ := rfl

/-- A responder as a stateful query implementation in `StateT State SPMF`: the
bundled-to-unbundled direction of the Kleisli–Mealy identification, of which
`PFunctor.Responder.equivStateHandler` is the deterministic (`Id`) sibling. -/
noncomputable def toQueryImpl (R : ProbResponder spec) [R.IsExecutable] :
    QueryImpl spec (StateT R.State SPMF) :=
  fun t s => IsExecutable.answerSPMF (R := R) s t

/-- Compatibility spelling for building a responder from a stateful query implementation. -/
@[reducible]
noncomputable def ofQueryImpl {σ : Type u}
    (impl : QueryImpl spec (StateT σ SPMF)) : ProbResponder spec :=
  ofSPMF impl

@[simp] lemma toQueryImpl_ofSPMF {σ : Type u}
    (impl : QueryImpl spec (StateT σ SPMF)) : (ofSPMF impl).toQueryImpl = impl := rfl

@[simp] lemma toQueryImpl_ofQueryImpl {σ : Type u}
    (impl : QueryImpl spec (StateT σ SPMF)) : (ofQueryImpl impl).toQueryImpl = impl := rfl

@[simp] theorem answerSPMF_ofSPMF {σ : Type u}
    (impl : QueryImpl spec (StateT σ SPMF)) (s : σ) (t : spec.Domain) :
    IsExecutable.answerSPMF (R := ofSPMF impl) s t = impl t s := rfl

/-- A family of memoryless randomized oracles indexed by a fixed setup value, as a
responder whose state is the setup and never changes: the per-run-sampled oracle of a
one-shot security game (sample the setup, then answer memorylessly) is exactly this
constant-state case. -/
@[reducible] noncomputable def ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec) :
    ProbResponder spec :=
  ofSPMF fun t γ => (fun r => (r, γ)) <$> h γ t

/-- A memoryless randomized oracle as a (trivially) stateful responder. -/
@[reducible] noncomputable def ofHandler (H : ProbHandler spec) : ProbResponder spec :=
  ofHandlerFamily fun _ : PUnit => H

/-- A deterministic responder — PolyFun's `PFunctor.Responder`, a dynamical system over
the internal hom `spec.toPFunctor ⊸ X` — as a Dirac probabilistic responder: the answer
and successor state it commits to, with probability one. Wiring against it recovers the
upstream closed game (`OracleStrategy.stepAgainst_ofDet`). -/
@[reducible] noncomputable def ofDet {σ : Type u} (C : PFunctor.Responder σ spec.toPFunctor) :
    ProbResponder spec :=
  ofSPMF fun t s => pure (C.answer s t, C.next s t)

/-- Pull a responder back along an interface lens: translate each query forward through
the lens, ask the target responder, and pull its answer back through the lens, keeping
the target's state. This is the challenger side of interface wrapping — dual to
installing an adversary forward along a lens (`OracleStrategy.reduce`).

Reducible so that `(pullback w R).State` unfolds to `R.State` during unification:
statements freely mix the two spellings, and keeping them interchangeable at
reducible transparency is what lets `rw`/`simp` traverse such goals. -/
@[reducible] noncomputable def pullback {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec') :
    ProbResponder spec where
  State := R.State
  instMeasurableSpaceState := R.instMeasurableSpaceState
  instMeasurableSpaceRange := fun t =>
    MeasurableSpace.map (w.toFunB t) (R.instMeasurableSpaceRange (w.toFunA t))
  answerKernel t := by
    letI := R.instMeasurableSpaceRange (w.toFunA t)
    letI : MeasurableSpace (spec.Range t) :=
      MeasurableSpace.map (w.toFunB t) (R.instMeasurableSpaceRange (w.toFunA t))
    exact (R.answerKernel (w.toFunA t)).map fun q => (w.toFunB t q.1, q.2)
  answerKernel_isSubprobability t := by infer_instance

/-- The answer/state map used by kernel pullback is measurable for the transported
answer measurable space. -/
theorem measurable_pullback_answerMap {ι' : Type u}
    {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    (t : spec.Domain) :
    letI := R.instMeasurableSpaceRange (w.toFunA t)
    letI := (pullback w R).instMeasurableSpaceRange t
    Measurable fun q : spec'.Range (w.toFunA t) × R.State =>
      (w.toFunB t q.1, q.2) := by
  let _ := R.instMeasurableSpaceRange (w.toFunA t)
  let _ := (pullback w R).instMeasurableSpaceRange t
  have hw : Measurable (w.toFunB t) := by
    rw [measurable_iff_comap_le]
    exact MeasurableSpace.comap_map_le
  exact (hw.comp measurable_fst).prodMk measurable_snd

/-- Executability is preserved by semantic responder pullback. The executable handler
maps the same answer/state pair as the kernel, and `SPMF.toMeasure_map` proves that the
two readings still agree. -/
noncomputable instance pullback.instIsExecutable {ι' : Type u}
    {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    [R.IsExecutable]
    [∀ t, letI := (pullback w R).instMeasurableSpaceRange t
      MeasurableSingletonClass (spec.Range t)] : (pullback w R).IsExecutable where
  answerSPMF s t :=
    (fun q => (w.toFunB t q.1, q.2)) <$>
      IsExecutable.answerSPMF (R := R) s (w.toFunA t)
  instMeasurableSingletonClassState :=
    IsExecutable.instMeasurableSingletonClassState (R := R)
  instMeasurableSingletonClassRange _ := inferInstance
  answerKernel_eq_toMeasure s t := by
    let _ := R.instMeasurableSpaceRange (w.toFunA t)
    let _ := (pullback w R).instMeasurableSpaceRange t
    simp only [pullback]
    rw [Kernel.map_apply _ (measurable_pullback_answerMap w R t) s]
    rw [IsExecutable.answerKernel_eq_toMeasure]
    exact (SPMF.toMeasure_map _ _ (measurable_pullback_answerMap w R t)).symm

/-- The executable pulled-back responder's handler translates each query forward and
maps the target responder's answer back through the lens. -/
@[simp] theorem toQueryImpl_pullback {ι' : Type u}
    {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    [R.IsExecutable]
    [∀ t, letI := (pullback w R).instMeasurableSpaceRange t
      MeasurableSingletonClass (spec.Range t)]
    (t : spec.toPFunctor.A) :
    (pullback w R).toQueryImpl t =
      (fun a => w.toFunB t a) <$> R.toQueryImpl (w.toFunA t) := by
  funext s
  change (fun q => (w.toFunB t q.1, q.2)) <$>
      IsExecutable.answerSPMF (R := R) s (w.toFunA t) =
    ((fun a => w.toFunB t a) <$> R.toQueryImpl (w.toFunA t)).run s
  rw [StateT.run_map]
  rfl

/-- **`FreeM.liftM` naturality for responder pullback**: interpreting a lens-translated
program through a responder's handler is interpreting the original program through the
pulled-back responder. The handler-level content of the interface-wrapping adjunction —
machine-free, so run-level wrapping laws follow from it by pure congruence. -/
theorem liftM_mapLens_pullback {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    [R.IsExecutable]
    [∀ t, letI := (pullback w R).instMeasurableSpaceRange t
      MeasurableSingletonClass (spec.Range t)]
    {γ : Type u} : ∀ oa : OracleComp spec γ,
    PFunctor.FreeM.liftM R.toQueryImpl (PFunctor.FreeM.mapLens w oa) =
      PFunctor.FreeM.liftM (pullback w R).toQueryImpl oa
  | .pure x => rfl
  | .liftBind t rest => by
    change (R.toQueryImpl (w.toFunA t) >>= fun d =>
        PFunctor.FreeM.liftM R.toQueryImpl (PFunctor.FreeM.mapLens w (rest (w.toFunB t d)))) =
      (pullback w R).toQueryImpl t >>= fun a =>
        PFunctor.FreeM.liftM (pullback w R).toQueryImpl (rest a)
    rw [toQueryImpl_pullback]
    simp only [bind_map_left]
    exact bind_congr fun d => liftM_mapLens_pullback w R (rest (w.toFunB t d))

/-- Lift a stateful `ProbComp` query implementation to a probabilistic responder via
its evaluation distribution, pointwise in the state. This is the bridge along which
existing stateful challengers (the lazy random oracle, cached LR encryption oracles)
become responders. -/
@[reducible] noncomputable def ofStateQueryImpl {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    {σ : Type} (impl : QueryImpl spec₀ (StateT σ ProbComp)) : ProbResponder spec₀ :=
  ofSPMF fun t s => 𝒮[(impl t).run s]

/-- **The stateful-responder probability bridge**: running an adversary against the
responder built from a `StateT σ ProbComp` handler (`ofStateQueryImpl impl`) is exactly
the evaluation distribution of running it against `impl` itself — the responder's `SPMF`
program-run is `𝒮` of the `ProbComp` program-run, *jointly* in the returned value and the
final state. This is the reusable bridge every stateful-responder consumer needs to move a
game between its `ProbComp` presentation (where probability reasoning happens) and its
`ProbResponder` presentation (the dynamical-systems wiring data).

Structurally it is the naturality of `simulateQ` along the monad morphism
`𝒮 : ProbComp →ᵐ SPMF`, transported through `StateT σ` — i.e. `𝒮 ∘ simulateQ impl =
simulateQ (𝒮 ∘ impl)`. That is exactly `PFunctor.FreeM.run_liftM_mapHom` at the bundled
evaluation-distribution morphism: `simulateQ` is the universal fold
(`simulateQ_def`), `ofStateQueryImpl` post-composes each query with `𝒮` pointwise in the
state, and `StateT.mapHom` is that post-composition as a morphism, so the whole statement
is one instance of the generic law rather than an induction over `OracleComp`. -/
theorem run_simulateQ_toQueryImpl_ofStateQueryImpl {ι₀ : Type}
    {spec₀ : OracleSpec.{0, 0} ι₀} {σ α : Type}
    (impl : QueryImpl spec₀ (StateT σ ProbComp)) (oa : OracleComp spec₀ α) (s : σ) :
    (simulateQ (ofStateQueryImpl impl).toQueryImpl oa).run s =
      𝒮[(simulateQ impl oa).run s] := by
  -- `exact` rather than a term-mode `:=`: matching the generic law needs the unfoldings of
  -- `simulateQ`, `toQueryImpl`, `ofStateQueryImpl`, `StateT.mapHom`, and `𝒮`, which are
  -- definitional but not syntactic.
  exact PFunctor.FreeM.run_liftM_mapHom (MonadHom.ofLift ProbComp SPMF) impl oa s

/-- The state set of a responder built from a stateful `ProbComp` handler is that handler's
state; a `@[simp]` `rfl` bridge so `(ofStateQueryImpl impl).State` reduces to the concrete state
type in downstream goals (the responder-`State` abbrev is otherwise opaque to `simp` and blocks
`StateT` run-map / bind rewriting). -/
@[simp] theorem ofStateQueryImpl_state {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} {σ : Type}
    (impl : QueryImpl spec₀ (StateT σ ProbComp)) : (ofStateQueryImpl impl).State = σ := rfl

/-- The post-composed form of `run_simulateQ_toQueryImpl_ofStateQueryImpl`: mapping the returned
value by `f` before running commutes with the bridge, pairing `f` on the value component. The
form security games hit, where the adversary's result is wrapped in `some` before the judge sees
it. -/
theorem run_map_simulateQ_toQueryImpl_ofStateQueryImpl {ι₀ : Type}
    {spec₀ : OracleSpec.{0, 0} ι₀} {σ α γ : Type}
    (impl : QueryImpl spec₀ (StateT σ ProbComp)) (f : α → γ) (oa : OracleComp spec₀ α) (s : σ) :
    (f <$> simulateQ (ofStateQueryImpl impl).toQueryImpl oa).run s =
      (fun p => (f p.1, p.2)) <$> 𝒮[(simulateQ impl oa).run s] := by
  rw [StateT.run_map, run_simulateQ_toQueryImpl_ofStateQueryImpl]

end ProbResponder

/-- The lazy random oracle as a probabilistic responder: the state is the query cache,
and each fresh query jointly draws a uniform answer and the cache extended by it. The
canonical example of a challenger whose answer and successor state must be drawn
jointly. -/
noncomputable def randomOracleResponder {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)] :
    ProbResponder spec₀ :=
  .ofStateQueryImpl spec₀.randomOracle

namespace OracleStrategy

open MeasureTheory ProbabilityTheory

/-! ## Wired runs

`stepAgainst` / `iterateAgainst` are the upstream eval-wired runs
`PFunctor.DynSystem.stepWith` / `iterWith` at `m := SPMF`, driven by the responder's
stateful handler `ProbResponder.toQueryImpl`. The responder state comes first in the
product, mirroring the upstream handler-state-first convention (and the challenger-first
state of `PFunctor.DynSystem.closedGame`). Likewise, the memoryless Kleisli runs of
`VCVio.OracleComp.Coinductive.DynSystem` are the upstream stateless runs at `m := SPMF`:
the step identification is definitional, the iterate agrees by fuel induction (the two
equation-compiler recursions do not unify definitionally at a variable fuel). Regression
guards below keep both identifications tight. -/

example (H : ProbHandler spec) (A : OracleStrategy S spec) (s : S) :
    kleisliStep H A s = PFunctor.DynSystem.kleisliStep H A s := rfl

example (H : ProbHandler spec) (A : OracleStrategy S spec) (n : ℕ) (s : S) :
    kleisliIterate H A n s = PFunctor.DynSystem.kleisliIterate H A n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact congrArg (kleisliStep H A s >>= ·) (funext ih)

/-! ## Kernel-valued wired runs -/

/-- The one-round output measure obtained by wiring a strategy to a responder at a
particular joint state. The measurability of the answer-to-next-state map is explicit;
`stepAgainstKernel` additionally asks that this family of measures be measurable in
the joint input state. -/
noncomputable def stepAgainstMeasure [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (_hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (p : R.State × S) : Measure (R.State × S) := by
  let _ := R.instMeasurableSpaceRange (A.expose p.2)
  exact (R.answerKernel (A.expose p.2) p.1).map
    (fun q => (q.2, A.update p.2 q.1))

/-- One wired round as a subprobability kernel on the responder/strategy product
state. The two hypotheses are precisely the local deterministic-update measurability
and the joint-state measurability needed to promote the pointwise construction to a
kernel. -/
noncomputable def stepAgainstKernel [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate)) :
    Kernel (R.State × S) (R.State × S) :=
  ⟨stepAgainstMeasure A R hUpdate, hFamily⟩

@[simp] theorem stepAgainstKernel_apply [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate))
    (p : R.State × S) :
    stepAgainstKernel A R hUpdate hFamily p = stepAgainstMeasure A R hUpdate p := rfl

instance stepAgainstKernel.instIsSubprobabilityKernel [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate)) :
    IsSubprobabilityKernel (stepAgainstKernel A R hUpdate hFamily) := ⟨fun p => by
  let _ := R.instMeasurableSpaceRange (A.expose p.2)
  rw [stepAgainstKernel_apply, stepAgainstMeasure, Measure.map_apply (hUpdate p)
    MeasurableSet.univ, Set.preimage_univ]
  exact (R.answerKernel (A.expose p.2)).measure_univ_le p.1⟩

/-- The `n`-round kernel generated by `stepAgainstKernel`. Kernel powers provide the
canonical iteration/composition operation and inherit the subprobability invariant. -/
noncomputable def iterateAgainstKernel [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate)) (n : ℕ) :
    Kernel (R.State × S) (R.State × S) :=
  stepAgainstKernel A R hUpdate hFamily ^ n

instance iterateAgainstKernel.instIsSubprobabilityKernel [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec)
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate)) (n : ℕ) :
    IsSubprobabilityKernel (iterateAgainstKernel A R hUpdate hFamily n) := by
  unfold iterateAgainstKernel
  infer_instance

/-- One wired round of an adversary strategy against a stateful responder: the
responder answers the exposed query (jointly drawing its successor state), and the
adversary advances along the answer. This is the upstream stateful-handler step
`PFunctor.DynSystem.stepWith` at `m := SPMF`: the wiring itself is deterministic
interface data; only the states advance stochastically. -/
noncomputable def stepAgainst (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable] :
    R.State × S → SPMF (R.State × S) :=
  PFunctor.DynSystem.stepWith R.toQueryImpl A

@[simp] theorem stepAgainst_apply (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable]
    (p : R.State × S) :
    stepAgainst A R p =
      (fun q => (q.2, A.update p.2 q.1)) <$>
        ProbResponder.IsExecutable.answerSPMF (R := R) p.1 (A.expose p.2) := rfl

/-- The `n`-round wired run: the Markov chain on the product state space generated by
`stepAgainst` — the upstream `PFunctor.DynSystem.iterWith` at `m := SPMF`. -/
noncomputable def iterateAgainst (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable] :
    ℕ → R.State × S → SPMF (R.State × S) :=
  PFunctor.DynSystem.iterWith R.toQueryImpl A

@[simp] theorem iterateAgainst_zero (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable]
    (p : R.State × S) : iterateAgainst A R 0 p = pure p := rfl

theorem iterateAgainst_succ (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable] (n : ℕ)
    (p : R.State × S) :
    iterateAgainst A R (n + 1) p = stepAgainst A R p >>= iterateAgainst A R n := rfl

/-- The executable one-round run denotes exactly the kernel one-round semantics. -/
theorem stepAgainstKernel_eq_toMeasure [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec) [R.IsExecutable]
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate))
    (p : R.State × S) :
    stepAgainstKernel A R hUpdate hFamily p = (stepAgainst A R p).toMeasure := by
  let _ := R.instMeasurableSpaceRange (A.expose p.2)
  rw [stepAgainstKernel_apply, stepAgainstMeasure, stepAgainst_apply,
    ProbResponder.IsExecutable.answerKernel_eq_toMeasure]
  exact (SPMF.toMeasure_map _ _ (hUpdate p)).symm

/-- On countable discrete state spaces, the executable `n`-round run denotes exactly
the corresponding power of the one-round kernel. -/
theorem iterateAgainstKernel_eq_toMeasure [MeasurableSpace S]
    (A : OracleStrategy S spec) (R : ProbResponder spec) [R.IsExecutable]
    [Countable R.State] [DiscreteMeasurableSpace R.State]
    [Countable S] [DiscreteMeasurableSpace S]
    (hUpdate : ∀ p : R.State × S,
      letI := R.instMeasurableSpaceRange (A.expose p.2)
      Measurable fun q : spec.Range (A.expose p.2) × R.State =>
        (q.2, A.update p.2 q.1))
    (hFamily : Measurable (stepAgainstMeasure A R hUpdate))
    (n : ℕ) (p : R.State × S) :
    iterateAgainstKernel A R hUpdate hFamily n p =
      (iterateAgainst A R n p).toMeasure := by
  induction n generalizing p with
  | zero =>
      rw [iterateAgainstKernel, pow_zero]
      change Measure.dirac p = (iterateAgainst A R 0 p).toMeasure
      rw [iterateAgainst_zero]
      rw [SPMF.toMeasure_pure]
  | succ n ih =>
      rw [iterateAgainstKernel, Kernel.pow_add _ n 1, pow_one, Kernel.comp_apply,
        stepAgainstKernel_eq_toMeasure A R hUpdate hFamily,
        iterateAgainst_succ, SPMF.toMeasure_bind]
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall ih

/-- The joint subdistribution over the length-`n` wired transcript and the final
product state (responder state first, matching `stepAgainst`). `QueryLog` is VCVio
vocabulary, so the transcript-recording run lives here rather than upstream. -/
noncomputable def transcriptAgainst (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable] :
    R.State × S → ℕ → SPMF (QueryLog spec × (R.State × S))
  | p, 0 => pure ([], p)
  | p, n + 1 => do
      let q ← ProbResponder.IsExecutable.answerSPMF (R := R) p.1 (A.expose p.2)
      let rest ← transcriptAgainst A R (q.2, A.update p.2 q.1) n
      pure (⟨A.expose p.2, q.1⟩ :: rest.1, rest.2)

/-- The subdistribution over length-`n` wired transcripts. -/
noncomputable def transcriptDistAgainst (A : OracleStrategy S spec) (R : ProbResponder spec)
    [R.IsExecutable]
    (p : R.State × S) (n : ℕ) : SPMF (QueryLog spec) :=
  Prod.fst <$> transcriptAgainst A R p n

/-! ## Deterministic recovery

Against the Dirac lift of a deterministic responder, one wired step is `pure` of the
upstream closed-game step: the state pairs agree on the nose because both put the
responder/challenger state first. -/

/-- Wiring against a deterministic responder is the (Dirac lift of the) upstream closed
game `PFunctor.DynSystem.closedGame`. -/
@[simp] theorem stepAgainst_ofDet (A : OracleStrategy S spec) {σ : Type u}
    (C : PFunctor.Responder σ spec.toPFunctor) (p : σ × S) :
    stepAgainst A (.ofDet C) p = pure ((PFunctor.DynSystem.closedGame C A).step p) := by
  obtain ⟨r, s⟩ := p
  simp [ProbResponder.ofDet, ProbResponder.answerSPMF_ofSPMF]

/-! ## Memoryless recovery

Against a constant-state responder the wired run is the existing memoryless Kleisli
run against the selected handler, with the setup carried along unchanged — the
setup-indexed family form of the upstream `PFunctor.DynSystem.stepWith_lift` /
`iterWith_lift` collapses (the family handler is state-dependent, so it is not literally
a `StateT.lift`; the same induction applies). -/

@[simp] theorem stepAgainst_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (A : OracleStrategy S spec) (p : Γ × S) :
    stepAgainst A (ProbResponder.ofHandlerFamily h) p =
      (fun s' => (p.1, s')) <$> kleisliStep (h p.1) A p.2 := by
  rw [stepAgainst_apply, ProbResponder.answerSPMF_ofSPMF]
  simp only [ProbResponder.ofHandlerFamily, kleisliStep, Functor.map_map]

@[simp] theorem iterateAgainst_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (A : OracleStrategy S spec) (n : ℕ) (p : Γ × S) :
    iterateAgainst A (ProbResponder.ofHandlerFamily h) n p =
      (fun s' => (p.1, s')) <$> kleisliIterate (h p.1) A n p.2 := by
  induction n generalizing p with
  | zero =>
    simp only [iterateAgainst_zero, kleisliIterate, map_pure]
  | succ n ih =>
    calc iterateAgainst A (ProbResponder.ofHandlerFamily h) (n + 1) p
        = ((fun s' => (p.1, s')) <$> kleisliStep (h p.1) A p.2) >>=
            iterateAgainst A (ProbResponder.ofHandlerFamily h) n := by
          rw [iterateAgainst_succ, stepAgainst_ofHandlerFamily]
      _ = kleisliStep (h p.1) A p.2 >>= fun s' =>
            iterateAgainst A (ProbResponder.ofHandlerFamily h) n (p.1, s') := by
          rw [map_eq_bind_pure_comp, bind_assoc]
          exact congrArg (kleisliStep (h p.1) A p.2 >>= ·)
            (funext fun s' => by rw [Function.comp_apply, pure_bind])
      _ = kleisliStep (h p.1) A p.2 >>= fun s' =>
            (fun s'' => (p.1, s'')) <$> kleisliIterate (h p.1) A n s' :=
          congrArg (kleisliStep (h p.1) A p.2 >>= ·)
            (funext fun s' => ih (p.1, s'))
      _ = (fun s' => (p.1, s')) <$> kleisliIterate (h p.1) A (n + 1) p.2 := by
          rw [kleisliIterate]
          simp only [map_eq_bind_pure_comp, bind_assoc]

/-- Against a memoryless oracle the wired step is the memoryless Kleisli step. -/
@[simp] theorem stepAgainst_ofHandler (H : ProbHandler spec) (A : OracleStrategy S spec)
    (p : PUnit × S) :
    stepAgainst A (ProbResponder.ofHandler H) p =
      (fun s' => (p.1, s')) <$> kleisliStep H A p.2 :=
  stepAgainst_ofHandlerFamily (fun _ => H) A p

/-- Against a memoryless oracle the wired run is the memoryless Kleisli run. -/
@[simp] theorem iterateAgainst_ofHandler (H : ProbHandler spec) (A : OracleStrategy S spec)
    (n : ℕ) (p : PUnit × S) :
    iterateAgainst A (ProbResponder.ofHandler H) n p =
      (fun s' => (p.1, s')) <$> kleisliIterate H A n p.2 :=
  iterateAgainst_ofHandlerFamily (fun _ => H) A n p

end OracleStrategy
