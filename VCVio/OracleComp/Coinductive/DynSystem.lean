/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.QueryTracking.LoggingOracle
import PolyFun.PFunctor.Dynamical.Behavior
import PolyFun.PFunctor.Dynamical.Run
import PolyFun.PFunctor.Free.Path

/-!
# Oracle strategies: the coalgebra dual of `OracleComp`

`OracleComp spec` is the *inductive* free monad on `spec.toPFunctor`: a program that **asks**
queries and halts. This file develops the *coalgebraic* dual, following Niu–Spivak
(*Polynomial Functors*, Ch. 4): a stateful, adaptive querier is a **`spec.toPFunctor`-dynamical
system**, and a deterministic oracle is a **section** of the same polynomial functor.

```
OracleComp  (algebra / answer side, inductive)  ⟷  OracleStrategy  (coalgebra / ask side, stateful)
                          glued by a handler  (=  Section spec.toPFunctor  =  QueryImpl spec Id)
```

* `OracleStrategy spec := PFunctor.DynSystem spec.toPFunctor` — a state set with
  `expose : State → ι` (the next query to ask) and `update : State → spec.Range _ → State`
  (digest the answer, advance). This is exactly an adaptive querying strategy / adversary.
* `OracleHandler spec := PFunctor.Section spec.toPFunctor` — a deterministic oracle as a section
  (a lens `spec.toPFunctor ⟹ X`); build with `ofFn`, apply via `DFunLike` (`h t`), and coerce to the
  underlying `QueryImpl spec Id` with `toQueryImpl`.
* `OracleStrategy.runAgainst h A : PFunctor.Closed` — close the strategy off with a handler
  (PolyFun's `close`); its `Closed.iterate` is the state trajectory and `transcript` the run log.
* `OracleStrategy.reduce` / `pair` / `juxtapose` — install a strategy along a reduction
  (`⊂ₒ` lens), against a product oracle (`*`), or in parallel (`⊗`).

The probabilistic Kleisli lift, the headline `iterate = simulateQ` correspondence, and the bridge
to `OracleComp.withQueryLog` live further down this file. The inductive-to-coinductive embedding
`toITree` is in `VCVio.OracleComp.Coinductive.Bridge`.
-/

universe u v w

open OracleSpec
open scoped PFunctor

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- A stateful, adaptive querier against `spec` (an adversary / environment): a PolyFun dynamical
system whose interface is the oracle's polynomial functor `spec.toPFunctor`. The field `expose`
chooses the next query from the current state; `update` digests an oracle answer into the next
state. The whole `PFunctor.DynSystem` / `PFunctor.Lens` combinator library applies directly. -/
abbrev OracleStrategy (spec : OracleSpec ι) : Type _ := PFunctor.DynSystem spec.toPFunctor

/-- A deterministic, total oracle for `spec`, as a PolyFun **section** — a lens
`spec.toPFunctor ⟹ X` choosing a direction (answer) at every position (query). Build one from an
answer function with `OracleHandler.ofFn`, apply it as a function through the `DFunLike` coercion
(`h t : spec.Range t`), and recover the underlying `QueryImpl spec Id` with
`OracleHandler.toQueryImpl`. Being a lens, it is exactly what `PFunctor.DynSystem.wrap` closes a
strategy with (`OracleStrategy.runAgainst`), and the whole `PFunctor.Lens` algebra applies. -/
abbrev OracleHandler (spec : OracleSpec.{u, v} ι) : Type _ :=
  PFunctor.Section.{u, v, u, v} spec.toPFunctor

namespace OracleHandler

/-- Build a handler from a dependent answer function `(t : spec.Domain) → spec.Range t`. -/
def ofFn (f : (t : spec.Domain) → spec.Range t) : OracleHandler spec :=
  PFunctor.sectionLens f

/-- The answer function underlying a handler. -/
def toFn (h : OracleHandler spec) (t : spec.Domain) : spec.Range t :=
  h.toFunB t PUnit.unit

instance instDFunLike : DFunLike (OracleHandler spec) spec.Domain (fun t => spec.Range t) where
  coe := toFn
  coe_injective' _ _ heq := by
    apply PFunctor.Lens.ext _ _ (fun a => Subsingleton.elim _ _)
    intro a
    refine funext fun u => ?_
    rw [Subsingleton.elim u PUnit.unit]
    simpa using congrFun heq a

@[simp] theorem coe_ofFn (f : (t : spec.Domain) → spec.Range t) : ⇑(ofFn f) = f := rfl

@[simp] theorem ofFn_apply (f : (t : spec.Domain) → spec.Range t) (t : spec.Domain) :
    ofFn f t = f t := rfl

/-- A handler is a deterministic `QueryImpl spec Id` — its answer function. -/
def toQueryImpl (h : OracleHandler spec) : QueryImpl spec Id := ⇑h

@[simp] theorem toQueryImpl_apply (h : OracleHandler spec) (t : spec.Domain) :
    h.toQueryImpl t = h t := rfl

instance : Coe (OracleHandler spec) (QueryImpl spec Id) := ⟨toQueryImpl⟩

end OracleHandler

/-- A **randomized** oracle for `spec`: a `QueryImpl` valued in `SPMF = OptionT PMF`, i.e. each
query answered by a sub-probability distribution. This is the Kleisli-category section that closes
a strategy into a Markov chain on its states (`OracleStrategy.kleisliStep`). Single-universe because
`SPMF : Type u → Type u`. -/
abbrev ProbHandler {ι : Type u} (spec : OracleSpec.{u, u} ι) : Type u := QueryImpl spec SPMF

namespace OracleStrategy

/-! ## Deterministic run and transcript -/

/-- Closing a strategy with a deterministic handler gives an autonomous (`Closed`) system whose
pure state transition is "ask the exposed query, feed the handler's answer back". Since the handler
*is* the section lens `spec.toPFunctor ⟹ X`, this is just `wrap` along it. -/
def runAgainst (h : OracleHandler spec) (A : OracleStrategy spec) : PFunctor.Closed :=
  PFunctor.DynSystem.wrap h A

/-- One step of the closed-loop run: ask `A.expose s`, answer with `h`, advance. Definitionally
equal to `(runAgainst h A).step s`. -/
def advanceOnce (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State) : A.State :=
  A.update s (h (A.expose s))

@[simp] theorem runAgainst_step (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State) :
    (runAgainst h A).step s = advanceOnce h A s := rfl

/-- The strategy's state after `n` handler-answered steps from `s`. Definitionally the closed
system's `Closed.iterate`. -/
def stateAfter (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State) (n : ℕ) : A.State :=
  (advanceOnce h A)^[n] s

theorem stateAfter_eq_iterate (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State)
    (n : ℕ) : stateAfter h A s n = (runAgainst h A).iterate s n := rfl

@[simp] theorem stateAfter_zero (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State) :
    stateAfter h A s 0 = s := rfl

theorem stateAfter_succ (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State) (n : ℕ) :
    stateAfter h A s (n + 1) = stateAfter h A (advanceOnce h A s) n :=
  Function.iterate_succ_apply (advanceOnce h A) n s

/-- The query asked at step `n` of the run. -/
def queryStream (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State) (n : ℕ) :
    spec.Domain := A.expose (stateAfter h A s n)

/-- The answer received at step `n` of the run. -/
def answerStream (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State) (n : ℕ) :
    spec.Range (queryStream h A s n) := h (queryStream h A s n)

/-- The length-`n` transcript of the run from state `s`: the recorded sequence of
`⟨query, answer⟩` pairs, valued in `QueryLog spec`. This associates a concrete run log to the
abstract state machine. -/
def transcript (h : OracleHandler spec) (A : OracleStrategy spec) :
    A.State → ℕ → QueryLog spec
  | _, 0 => []
  | s, n + 1 => ⟨A.expose s, h (A.expose s)⟩ :: transcript h A (advanceOnce h A s) n

@[simp] theorem transcript_zero (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State) :
    transcript h A s 0 = [] := rfl

@[simp] theorem transcript_succ (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State)
    (n : ℕ) : transcript h A s (n + 1) =
      ⟨A.expose s, h (A.expose s)⟩ :: transcript h A (advanceOnce h A s) n := rfl

@[simp] theorem transcript_length (h : OracleHandler spec) (A : OracleStrategy spec) (s : A.State)
    (n : ℕ) : (transcript h A s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [ih]

/-! ## The cofree behaviour trajectory

`PFunctor.DynSystem.trajectory` gives the cofree-`p` behaviour tree of the strategy; for the closed
run its spine is the state `iterate` (`PFunctor.DynSystem.next_iterate_trajectory`). -/

/-- The behaviour trajectory of the closed-loop run: the cofree tree whose spine is the state
sequence. The `n`-fold `CofreeC.next` walks it to the state after `n` steps. -/
theorem next_iterate_trajectory_runAgainst (h : OracleHandler spec) (A : OracleStrategy spec)
    (s : A.State) (n : ℕ) :
    (PFunctor.CofreeC.next)^[n] (PFunctor.DynSystem.trajectory (runAgainst h A) s) =
      PFunctor.DynSystem.trajectory (runAgainst h A) (stateAfter h A s n) :=
  PFunctor.DynSystem.next_iterate_trajectory (runAgainst h A) s n

/-! ## Combinators: reductions, products, and parallel composition

These reuse PolyFun's `wrap` / `pairing` / `tensor`, made meaningful on the oracle side. The key
identification is **a reduction is a lens**: a sub-spec coercion `⊂ₒ` is a `PFunctor.Lens`
(`SubSpec.toLens`), and applying it to a strategy is `wrap`, with composition for free. -/

/-- Install a strategy into a larger oracle along a sub-spec inclusion `spec ⊂ₒ superSpec`. This is
`wrap` along the reduction lens `SubSpec.toLens`; it rewrites each query forward and each answer
backward, exactly a reduction of adversaries. -/
def reduce {τ : Type u} {superSpec : OracleSpec.{u, v} τ} (h : spec ⊂ₒ superSpec)
    (A : OracleStrategy spec) : OracleStrategy superSpec :=
  PFunctor.DynSystem.wrap (SubSpec.toLens h) A

@[simp] theorem reduce_state {τ : Type u} {superSpec : OracleSpec.{u, v} τ} (h : spec ⊂ₒ superSpec)
    (A : OracleStrategy spec) : (reduce h A).State = A.State := rfl

/-- Reductions compose: reducing along `h₁` then `h₂` is reducing along `h₁.trans h₂`. Free from
`PFunctor.DynSystem.wrap_comp` and `SubSpec.trans_toLens`. -/
theorem reduce_trans {τ : Type u} {superSpec : OracleSpec.{u, v} τ}
    {ρ : Type u} {superSpec' : OracleSpec.{u, v} ρ}
    (h₁ : spec ⊂ₒ superSpec) (h₂ : superSpec ⊂ₒ superSpec') (A : OracleStrategy spec) :
    reduce h₂ (reduce h₁ A) = reduce (h₁.trans h₂) A := rfl

/-- A shared-state strategy against the product oracle `spec₁ * spec₂`, built from two interface
lenses out of one self-monomial state. This is PolyFun's categorical product `pairing`, landing in
`PFunctor.prod = *` definitionally (directions are a `Sum`, matching `OracleSpec` `*`). -/
def pair {ι₁ : Type u} {spec₁ : OracleSpec.{u, v} ι₁} {ι₂ : Type u} {spec₂ : OracleSpec.{u, v} ι₂}
    {S : Type u} (l₁ : PFunctor.Lens (PFunctor.selfMonomial S) spec₁.toPFunctor)
    (l₂ : PFunctor.Lens (PFunctor.selfMonomial S) spec₂.toPFunctor) :
    OracleStrategy (spec₁ * spec₂) :=
  PFunctor.DynSystem.pairing l₁ l₂

/-- Parallel product of two independent-state strategies. This lands in the Dirichlet tensor
`spec₁.toPFunctor ⊗ spec₂.toPFunctor`, a *synchronous joint oracle* (answers both at once) whose
directions are a `Prod`. Note `⊗ ≠ *`: this interface has no standard `OracleSpec` preimage, unlike
`pair`. Kept for modeling genuinely parallel adversaries. -/
def juxtapose {ι₁ : Type u} {spec₁ : OracleSpec.{u, v} ι₁} {ι₂ : Type u}
    {spec₂ : OracleSpec.{u, v} ι₂} (A : OracleStrategy spec₁) (B : OracleStrategy spec₂) :
    PFunctor.DynSystem (spec₁.toPFunctor ⊗ spec₂.toPFunctor) :=
  A.tensor B

/-! ## Probabilistic Kleisli run

When the handler is randomized (`ProbHandler spec`), closing a strategy no longer gives a pure state
endofunction but a **Markov chain on states**: `kleisliStep` samples an answer and advances, and its
Kleisli iterate is the distribution over states (equivalently transcripts) after `n` adaptive
queries. The deterministic run embeds as the Dirac special case (`ofHandler`). -/

section Probabilistic

variable {spec : OracleSpec.{u, u} ι}

/-- One probabilistic step: sample an answer to the exposed query from the handler, then advance the
state. The result is a sub-distribution over next states. -/
noncomputable def kleisliStep (H : ProbHandler spec) (A : OracleStrategy spec) (s : A.State) :
    SPMF A.State :=
  (fun r => A.update s r) <$> H (A.expose s)

/-- The `n`-fold Kleisli iterate of `kleisliStep`: the sub-distribution over states reached after
`n` adaptive queries, starting from `s`. -/
noncomputable def kleisliIterate (H : ProbHandler spec) (A : OracleStrategy spec) :
    ℕ → A.State → SPMF A.State
  | 0, s => pure s
  | n + 1, s => kleisliStep H A s >>= kleisliIterate H A n

/-- The joint sub-distribution over the length-`n` transcript and the final state. -/
noncomputable def kleisliTranscript (H : ProbHandler spec) (A : OracleStrategy spec) :
    A.State → ℕ → SPMF (QueryLog spec × A.State)
  | s, 0 => pure ([], s)
  | s, n + 1 => do
      let r ← H (A.expose s)
      let p ← kleisliTranscript H A (A.update s r) n
      pure (⟨A.expose s, r⟩ :: p.1, p.2)

/-- The sub-distribution over length-`n` transcripts of the randomized run from `s`. -/
noncomputable def transcriptDist (H : ProbHandler spec) (A : OracleStrategy spec) (s : A.State)
    (n : ℕ) : SPMF (QueryLog spec) :=
  Prod.fst <$> kleisliTranscript H A s n

/-- A deterministic handler as a Dirac `ProbHandler`. -/
noncomputable def _root_.ProbHandler.ofHandler (h : OracleHandler spec) : ProbHandler spec :=
  fun t => (pure (h t) : SPMF (spec.Range t))

@[simp] theorem kleisliStep_ofHandler (h : OracleHandler spec) (A : OracleStrategy spec)
    (s : A.State) : kleisliStep (ProbHandler.ofHandler h) A s = pure (advanceOnce h A s) := by
  simp [kleisliStep, ProbHandler.ofHandler, advanceOnce]

@[simp] theorem kleisliIterate_ofHandler (h : OracleHandler spec) (A : OracleStrategy spec)
    (n : ℕ) (s : A.State) :
    kleisliIterate (ProbHandler.ofHandler h) A n s = pure (stateAfter h A s n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [kleisliIterate, kleisliStep_ofHandler, pure_bind, ih, stateAfter_succ]

@[simp] theorem kleisliTranscript_ofHandler (h : OracleHandler spec) (A : OracleStrategy spec)
    (n : ℕ) (s : A.State) : kleisliTranscript (ProbHandler.ofHandler h) A s n =
      pure (transcript h A s n, stateAfter h A s n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [kleisliTranscript, ProbHandler.ofHandler]
      simp only [pure_bind, ih, transcript_succ, advanceOnce, stateAfter_succ]

/-- **Dirac bridge.** The randomized transcript distribution of a deterministic handler is the Dirac
mass on the deterministic transcript: parts 1 and 3 agree. -/
@[simp] theorem transcriptDist_ofHandler (h : OracleHandler spec) (A : OracleStrategy spec)
    (s : A.State) (n : ℕ) :
    transcriptDist (ProbHandler.ofHandler h) A s n = pure (transcript h A s n) := by
  rw [transcriptDist, kleisliTranscript_ofHandler, map_pure]

end Probabilistic

end OracleStrategy

/-! ## Headline: a program *is* a state machine whose run computes `simulateQ`

`OracleComp spec` is the inductive querier; here we read it back as a coalgebra. A program becomes a
closed dynamical system on the state set `OracleComp spec α` (the remaining computation), and
iterating that system under a deterministic handler `h` for `stepsToHalt` steps lands at `pure` of
`simulateQ (ofFn h)`. The randomized version exhibits `simulateQ` as one coalgebraic Kleisli step
followed by the rest. -/

namespace OracleComp

variable {α : Type v}

/-- One handler-driven reduction step of a program viewed as its own state: answer the head query
with `h` and continue, or stay put at a `pure`. -/
def advance (h : OracleHandler spec) (oa : OracleComp spec α) : OracleComp spec α :=
  oa.casesOn (fun x => pure x) (fun t k => k (h t))

@[simp] theorem advance_pure (h : OracleHandler spec) (x : α) :
    advance h (pure x : OracleComp spec α) = pure x := rfl

@[simp] theorem advance_queryBind (h : OracleHandler spec) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) : advance h (queryBind t k) = k (h t) := rfl

/-- The number of handler-answered query steps until the program halts. -/
def stepsToHalt (h : OracleHandler spec) (oa : OracleComp spec α) : ℕ :=
  OracleComp.construct (C := fun _ => ℕ) (fun _ => 0) (fun t _ ih => ih (h t) + 1) oa

@[simp] theorem stepsToHalt_pure (h : OracleHandler spec) (x : α) :
    stepsToHalt h (pure x : OracleComp spec α) = 0 := rfl

@[simp] theorem stepsToHalt_queryBind (h : OracleHandler spec) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) :
    stepsToHalt h (queryBind t k) = stepsToHalt h (k (h t)) + 1 := rfl

@[simp] theorem evalWithAnswerFn_queryBind (f : QueryImpl spec Id) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) :
    evalWithAnswerFn f (queryBind t k) = evalWithAnswerFn f (k (f t)) := by
  change simulateQ f (queryBind t k) = simulateQ f (k (f t))
  rw [show queryBind t k = liftM (spec.query t) >>= k from rfl, simulateQ_query_bind]
  rfl

/-- **Headline correspondence.** Answering a program's head query with a deterministic handler `h`,
iterated for exactly `stepsToHalt` steps, lands at `pure` of the simulated value: the coalgebraic
state iterate *computes* `simulateQ`/`evalWithAnswerFn`. -/
theorem iterate_advance_eq_simulate (h : OracleHandler spec) (oa : OracleComp spec α) :
    (advance h)^[stepsToHalt h oa] oa = pure (evalWithAnswerFn (QueryImpl.ofFn h) oa) := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
      rw [stepsToHalt_queryBind, Function.iterate_succ_apply, advance_queryBind, ih,
        evalWithAnswerFn_queryBind, QueryImpl.ofFn_apply]

/-- The program as a closed dynamical system: the state is the remaining computation, the interface
is the unit `X`, and one step answers the head query via `h`. The system reaches a fixed point
exactly at `pure`; iterating it is `iterate_advance_eq_simulate`. -/
def evalSystem (h : OracleHandler spec) (α : Type v) : PFunctor.Closed.{u, v, max u v} where
  State := OracleComp spec α
  expose := fun _ => PUnit.unit
  update := fun oa _ => advance h oa

@[simp] theorem evalSystem_step (h : OracleHandler spec) (oa : OracleComp spec α) :
    (evalSystem h α).step oa = advance h oa := rfl

@[simp] theorem evalSystem_iterate (h : OracleHandler spec) (oa : OracleComp spec α) (n : ℕ) :
    (evalSystem h α).iterate oa n = (advance h)^[n] oa := rfl

/-- The `Closed`-system form of the headline: `Closed.iterate` of the program-system computes
`simulateQ`. -/
theorem iterate_evalSystem_eq_simulate (h : OracleHandler spec) (oa : OracleComp spec α) :
    (evalSystem h α).iterate oa (stepsToHalt h oa) =
      pure (evalWithAnswerFn (QueryImpl.ofFn h) oa) :=
  iterate_advance_eq_simulate h oa

/-- Wrapper view: the deterministic run of a program against a handler. -/
def runProgram (h : OracleHandler spec) (oa : OracleComp spec α) : OracleComp spec α :=
  (evalSystem h α).iterate oa (stepsToHalt h oa)

theorem runProgram_eq (h : OracleHandler spec) (oa : OracleComp spec α) :
    runProgram h oa = pure (evalWithAnswerFn (QueryImpl.ofFn h) oa) :=
  iterate_advance_eq_simulate h oa

/-- Cofree corollary: the behaviour trajectory of the program-system, walked `stepsToHalt` steps,
stabilizes at the trajectory of `pure (simulated value)`. The literal `trajectory ↔ simulateQ`
shadow of the correspondence. -/
theorem trajectory_evalSystem_stabilizes (h : OracleHandler spec) (oa : OracleComp spec α) :
    (PFunctor.CofreeC.next)^[stepsToHalt h oa]
        (PFunctor.DynSystem.trajectory (evalSystem h α) oa) =
      PFunctor.DynSystem.trajectory (evalSystem h α)
        (pure (evalWithAnswerFn (QueryImpl.ofFn h) oa)) := by
  rw [PFunctor.DynSystem.next_iterate_trajectory]
  exact congrArg _ (iterate_evalSystem_eq_simulate h oa)

end OracleComp

/-! ## Probabilistic headline: `simulateQ` as a coalgebraic Kleisli step -/

namespace OracleComp

section Probabilistic

variable {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- One randomized coalgebra step on programs: sample the head query's answer from `H`, exposing the
continuation; a `pure` is already the answer. -/
noncomputable def advanceK (H : ProbHandler spec) (oa : OracleComp spec α) :
    SPMF (OracleComp spec α) :=
  oa.casesOn (fun x => pure (pure x)) (fun t k => k <$> H t)

@[simp] theorem advanceK_pure (H : ProbHandler spec) (x : α) :
    advanceK H (pure x : OracleComp spec α) = pure (pure x) := rfl

@[simp] theorem advanceK_queryBind (H : ProbHandler spec) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) : advanceK H (queryBind t k) = k <$> H t := rfl

/-- **Probabilistic headline.** The `SPMF` semantics of a program is one randomized coalgebra step
followed by the semantics of the continuation — `simulateQ` unfolds coalgebraically. With the Dirac
bridge (`transcriptDist_ofHandler`) this specializes to the deterministic correspondence. -/
theorem simulateQ_eq_advanceK_bind (H : ProbHandler spec) (oa : OracleComp spec α) :
    simulateQ H oa = advanceK H oa >>= simulateQ H := by
  cases oa with
  | pure x =>
      change simulateQ H (pure x) = advanceK H (pure x) >>= simulateQ H
      simp [advanceK_pure]
  | queryBind t k =>
      rw [advanceK_queryBind]
      change simulateQ H (liftM (spec.query t) >>= k) = (k <$> H t) >>= simulateQ H
      rw [simulateQ_query_bind]
      simp [map_eq_bind_pure_comp]

end Probabilistic

/-! ## Subsumption: the program transcript *is* the logging-oracle output

The coalgebraic transcript is not a new notion: running a program against a deterministic handler
with the existing `QueryImpl.withLogging` instrumentation produces exactly `(simulated value,
transcript)`. So the new layer reuses — rather than duplicates — VCVio's `QueryLog` machinery. -/

variable {α : Type v}

/-- The transcript of running a program `oa` against a deterministic handler `h`: the `⟨query,
answer⟩` pairs in execution order. The program-side analogue of `OracleStrategy.transcript`. -/
def transcript (h : OracleHandler spec) (oa : OracleComp spec α) : QueryLog spec :=
  oa.construct (fun _ => ([] : QueryLog spec)) (fun t _k ih => ⟨t, h t⟩ :: ih (h t))

@[simp] theorem transcript_pure (h : OracleHandler spec) (x : α) :
    transcript h (pure x : OracleComp spec α) = [] := rfl

@[simp] theorem transcript_queryBind (h : OracleHandler spec) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) :
    transcript h (queryBind t k) = ⟨t, h t⟩ :: transcript h (k (h t)) := rfl

/-! ### Denotational query bounds

Because `transcript` lands in `QueryLog spec`, its length is the number of handler-answered steps
(`stepsToHalt`), and the existing `IsTotalQueryBound` becomes a *denotational* bound on the run:
a program that makes at most `n` queries has a transcript of length at most `n`. -/

/-- The transcript length is exactly the number of handler-answered query steps. -/
@[simp] theorem transcript_length (h : OracleHandler spec) (oa : OracleComp spec α) :
    (transcript h oa).length = stepsToHalt h oa := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih => simp [ih]

@[simp] theorem transcript_countQ_pure (h : OracleHandler spec) (p : ι → Prop) [DecidablePred p]
    (x : α) : (transcript h (pure x : OracleComp spec α)).countQ p = 0 := rfl

/-- `countQ` recurrence on the transcript: a query to `t` contributes one iff `p t`. -/
theorem transcript_countQ_queryBind (h : OracleHandler spec) (p : ι → Prop) [DecidablePred p]
    (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    (transcript h (queryBind t k)).countQ p =
      (if p t then 1 else 0) + (transcript h (k (h t))).countQ p := by
  simp only [transcript_queryBind, QueryLog.countQ, QueryLog.getQ_cons]
  by_cases hpt : p t <;> simp [hpt, Nat.add_comm]

/-! ### Typed transcripts via `PFunctor.FreeM.Path`

`OracleComp spec` *is* `PFunctor.FreeM spec.toPFunctor`, and a `PFunctor.FreeM.Path` is a typed
root-to-leaf branch choice — i.e. a sequence of typed oracle answers. A deterministic handler picks
the canonical such path (`handlerPath`): its leaf is the simulated value (`output_handlerPath`) and
its erasure is the flat `QueryLog` transcript (`logOfPath_handlerPath`). So the flat transcript is
the answer-erasure of the program's typed interaction path. -/

/-- The typed root-to-leaf path through a program induced by a deterministic handler: at each query
node, choose the handler's answer. This is the program's *typed* transcript. -/
def handlerPath (h : OracleHandler spec) : (oa : OracleComp spec α) → PFunctor.FreeM.Path oa
  | .pure _ => ⟨⟩
  | .roll a rest => ⟨h a, handlerPath h (rest (h a))⟩

/-- The leaf selected by the handler's typed path is exactly the simulated value. -/
theorem output_handlerPath (h : OracleHandler spec) (oa : OracleComp spec α) :
    PFunctor.FreeM.output oa (handlerPath h oa) = evalWithAnswerFn (QueryImpl.ofFn h) oa := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
      have h1 : PFunctor.FreeM.output (queryBind t k) (handlerPath h (queryBind t k))
          = PFunctor.FreeM.output (k (h t)) (handlerPath h (k (h t))) := rfl
      rw [h1, ih, evalWithAnswerFn_queryBind, QueryImpl.ofFn_apply]

/-- Erase a typed path to a flat `QueryLog`: pair each tree node's query with the answer the path
selected there. -/
def logOfPath : (oa : OracleComp spec α) → PFunctor.FreeM.Path oa → QueryLog spec
  | .pure _, _ => []
  | .roll a rest, ⟨b, path⟩ => ⟨a, b⟩ :: logOfPath (rest b) path

/-- The flat transcript is the answer-erasure of the handler's typed path. -/
theorem logOfPath_handlerPath (h : OracleHandler spec) (oa : OracleComp spec α) :
    logOfPath oa (handlerPath h oa) = transcript h oa := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
      have h1 : logOfPath (queryBind t k) (handlerPath h (queryBind t k))
          = ⟨t, h t⟩ :: logOfPath (k (h t)) (handlerPath h (k (h t))) := rfl
      rw [h1, ih, transcript_queryBind]

/-! ### Running along a reduction lens

`reduce` rewrites a strategy *forward* along a `⊂ₒ` lens; dually, a program can be *run* along that
lens, its queries answered by a super-spec handler. The runtime path it traces
(`PFunctor.FreeM.PathAlong`) has the same leaf as running directly with the pulled-back handler —
the denotational content of "a reduction is a lens". -/

section Reduction

variable {τ : Type u} {superSpec : OracleSpec.{u, v} τ}

/-- A super-spec handler pulled back along a sub-spec inclusion: translate a `spec`-query forward,
ask the super-handler, translate the answer back. -/
def _root_.OracleHandler.pullback (hs : spec ⊂ₒ superSpec) (H : OracleHandler superSpec) :
    OracleHandler spec :=
  OracleHandler.ofFn fun a => (SubSpec.toLens hs).toFunB a (H ((SubSpec.toLens hs).toFunA a))

/-- The runtime path through a `spec`-program executed along the reduction lens, answered by a
super-spec handler `H`. -/
def runAlong (hs : spec ⊂ₒ superSpec) (H : OracleHandler superSpec) :
    (oa : OracleComp spec α) → PFunctor.FreeM.PathAlong (SubSpec.toLens hs) oa
  | .pure _ => ⟨⟩
  | .roll a rest => ⟨H ((SubSpec.toLens hs).toFunA a),
      runAlong hs H (rest (OracleHandler.pullback hs H a))⟩

/-- Running a program along the reduction lens with a super-spec handler computes the same value as
running it directly with the pulled-back handler (`output_handlerPath`'s lens-relative form). -/
theorem outputAlong_runAlong (hs : spec ⊂ₒ superSpec) (H : OracleHandler superSpec)
    (oa : OracleComp spec α) :
    PFunctor.FreeM.outputAlong (SubSpec.toLens hs) oa (runAlong hs H oa) =
      evalWithAnswerFn (QueryImpl.ofFn (OracleHandler.pullback hs H)) oa := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
      have h1 : PFunctor.FreeM.outputAlong (SubSpec.toLens hs) (queryBind t k)
            (runAlong hs H (queryBind t k))
          = PFunctor.FreeM.outputAlong (SubSpec.toLens hs) (k (OracleHandler.pullback hs H t))
              (runAlong hs H (k (OracleHandler.pullback hs H t))) := rfl
      rw [h1, ih, evalWithAnswerFn_queryBind, QueryImpl.ofFn_apply]

end Reduction

section QueryBound

variable {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- A total query bound bounds the number of handler-answered steps: if `oa` makes at most `n`
queries, the run halts within `n` steps. The operational `IsTotalQueryBound` made denotational. -/
theorem stepsToHalt_le_of_isTotalQueryBound (h : OracleHandler spec) :
    ∀ {oa : OracleComp spec α} {n : ℕ}, IsTotalQueryBound oa n → stepsToHalt h oa ≤ n := by
  intro oa
  induction oa with
  | pure x => intro n _; exact Nat.zero_le n
  | queryBind t k ih =>
      intro n hb
      obtain ⟨hpos, hrest⟩ := hb
      have hle := ih (h t) (hrest (h t))
      simp only [] at hpos hle
      rw [stepsToHalt_queryBind]; omega

/-- **Denotational query bound.** A total query bound on a program bounds the length of every
handler-answered transcript: if `oa` makes at most `n` queries, `(transcript h oa).length ≤ n`. -/
theorem transcript_length_le_of_isTotalQueryBound (h : OracleHandler spec)
    {oa : OracleComp spec α} {n : ℕ} (hb : IsTotalQueryBound oa n) :
    (transcript h oa).length ≤ n := by
  rw [transcript_length]; exact stepsToHalt_le_of_isTotalQueryBound h hb

/-- **Predicate query bound.** If `oa` makes at most `n` queries matching `p`, the transcript
contains at most `n` `p`-matching entries (`QueryLog.countQ`). -/
theorem transcript_countQ_le_of_isQueryBoundP (h : OracleHandler spec) (p : ι → Prop)
    [DecidablePred p] :
    ∀ {oa : OracleComp spec α} {n : ℕ}, IsQueryBoundP oa p n →
      (transcript h oa).countQ p ≤ n := by
  intro oa
  induction oa with
  | pure x => intro n _; exact Nat.zero_le n
  | queryBind t k ih =>
      intro n hb
      obtain ⟨hp, hrest⟩ := hb
      have hle := ih (h t) (hrest (h t))
      simp only [] at hle
      rw [transcript_countQ_queryBind]
      by_cases hpt : p t
      · have hn : 0 < n := hp.resolve_left (not_not_intro hpt)
        simp only [hpt, if_true] at hle ⊢
        omega
      · simp only [hpt, if_false] at hle ⊢
        omega

/-- **Per-index query bound.** If `oa` respects a per-index budget `qb`, then for every oracle index
`t` the transcript contains at most `qb t` queries to `t`. -/
theorem transcript_countQ_le_of_isPerIndexQueryBound (h : OracleHandler spec) [DecidableEq ι]
    (t : ι) :
    ∀ {oa : OracleComp spec α} {qb : ι → ℕ}, IsPerIndexQueryBound oa qb →
      (transcript h oa).countQ (· = t) ≤ qb t := by
  intro oa
  induction oa with
  | pure x => intro qb _; exact Nat.zero_le (qb t)
  | queryBind t' k ih =>
      intro qb hb
      obtain ⟨hpos, hrest⟩ := hb
      have hle := ih (h t') (hrest (h t'))
      simp only [] at hpos hle
      rw [transcript_countQ_queryBind]
      rcases eq_or_ne t' t with rfl | htt
      · rw [Function.update_self] at hle
        split_ifs <;> omega
      · rw [Function.update_of_ne htt.symm] at hle
        simp only [if_neg htt]; omega

end QueryBound

section Subsumption

variable {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- **Subsumption bridge.** Running a program against the deterministic handler `ofFn h` through the
existing `QueryImpl.withLogging` instrumentation yields exactly the simulated value paired with the
coalgebraic `transcript`. The new transcript is the established logging-oracle output. -/
theorem run_simulateQ_ofFn_withLogging (h : OracleHandler spec) (oa : OracleComp spec α) :
    (simulateQ ((QueryImpl.ofFn h).withLogging) oa).run =
      (evalWithAnswerFn (QueryImpl.ofFn h) oa, transcript h oa) := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
      rw [transcript_queryBind, evalWithAnswerFn_queryBind, QueryImpl.ofFn_apply,
        show queryBind t k = liftM (spec.query t) >>= k from rfl, simulateQ_query_bind]
      simp only [QueryImpl.withLogging_apply, QueryImpl.ofFn_apply, OracleQuery.input_query,
        WriterT.run_bind', monadLift_self, ih]
      rfl

end Subsumption

end OracleComp

