/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.DynSystem
import VCVio.OracleComp.QueryTracking.Trace

/-!
# Dynamical systems meet oracle computations — worked examples

Concrete demonstrations of `VCVio.OracleComp.Coinductive.DynSystem`: an oracle spec is a polynomial
functor, an adaptive querier is a dynamical system (coalgebra) over it, and a deterministic oracle
is a section that closes the loop into a runnable state machine.

* `coinCounter` — a stateful querier of the coin oracle, run against a handler for a transcript.
* `prog` / the headline — a program is its own state machine whose iterate computes `simulateQ`.
* the subsumption bridge — the new transcript *is* the existing `withLogging` output.
* the Dirac bridge — a randomized handler turns the run into a Markov chain (`transcriptDist`).
* `reduce` — a reduction of strategies is a polynomial-functor lens (`⊂ₒ`).
-/

open OracleSpec OracleComp

namespace DynSystemExamples

/-! ## A stateful coin-counting adversary

`coinSpec = Unit →ₒ Bool` is the single coin oracle. A querier that repeatedly flips the coin and
counts heads is a dynamical system over `coinSpec.toPFunctor`: the state is the running count, it
always exposes the (unique) query, and it digests a `Bool` answer by incrementing on heads. -/

/-- A strategy against the coin oracle: count the heads seen so far. -/
def coinCounter : OracleStrategy coinSpec where
  State := ℕ
  expose := fun _ => ()
  update := fun n b => bif b then n + 1 else n

/-- A deterministic coin oracle that always answers heads. -/
def allHeads : OracleHandler coinSpec := OracleHandler.ofFn fun _ => true

/-- Running the counter against the all-heads oracle for three steps reaches state `3`. -/
example : OracleStrategy.stateAfter allHeads coinCounter (0 : ℕ) 3 = (3 : ℕ) := rfl

/-- ...and its transcript records three `⟨(), true⟩` query/answer pairs. -/
example : OracleStrategy.transcript allHeads coinCounter (0 : ℕ) 3 =
    [⟨(), true⟩, ⟨(), true⟩, ⟨(), true⟩] := by decide

/-! ## A program is its own state machine

A finite `OracleComp` program becomes a closed dynamical system on the state set "remaining
computation". Iterating it under a handler computes `simulateQ` (`iterate_advance_eq_simulate`). -/

/-- A two-flip program returning the conjunction of the flips. -/
def prog : OracleComp coinSpec Bool := do
  let b₁ ← coinSpec.query ()
  let b₂ ← coinSpec.query ()
  return b₁ && b₂

/-- The deterministic run of `prog` against `allHeads` yields `true`. -/
example : evalWithAnswerFn (QueryImpl.ofFn allHeads) prog = true := by decide

/-- The program halts after two handler-answered query steps. -/
example : stepsToHalt allHeads prog = 2 := by decide

/-- Iterating the program-as-system for `stepsToHalt` steps lands at `pure true`. -/
example : (advance allHeads)^[stepsToHalt allHeads prog] prog = pure true := by
  rw [iterate_advance_eq_simulate]; congr 1

/-- The program's transcript is two heads. -/
example : OracleComp.transcript allHeads prog = [⟨(), true⟩, ⟨(), true⟩] := by decide

/-! ## Subsumption: the transcript is the logging-oracle output

The new coalgebraic transcript is not a new notion — it is exactly the `QueryLog` produced by the
existing `QueryImpl.withLogging` instrumentation under the deterministic `ofFn allHeads`. -/

example :
    (simulateQ ((QueryImpl.ofFn allHeads).withLogging) prog).run =
      (true, [⟨(), true⟩, ⟨(), true⟩]) := by
  rw [run_simulateQ_ofFn_withLogging]; rfl

/-! ## A randomized handler makes the run a Markov chain

With a randomized `ProbHandler`, closing the strategy gives a sub-distribution over transcripts
(`transcriptDist`). Feeding a deterministic handler through the Dirac embedding `ofHandler` recovers
the deterministic transcript exactly. -/

example :
    OracleStrategy.transcriptDist (ProbHandler.ofHandler allHeads) coinCounter (0 : ℕ) 3 =
      pure (OracleStrategy.transcript allHeads coinCounter (0 : ℕ) 3) :=
  OracleStrategy.transcriptDist_ofHandler allHeads coinCounter (0 : ℕ) 3

/-! ## A reduction of strategies is a lens

A sub-spec coercion `coinSpec ⊂ₒ coinSpec + coinSpec` is a polynomial-functor lens; applying it to a
strategy (`reduce`) rewrites every query into the larger oracle, preserving the state. -/

/-- The coin counter, reduced into the left copy of a two-coin oracle. -/
def coinCounterLeft : OracleStrategy (coinSpec + coinSpec) :=
  OracleStrategy.reduce inferInstance coinCounter

example : coinCounterLeft.State = ℕ := rfl

/-! ## Denotational query bounds

`transcript`'s length is the number of handler-answered steps (`transcript_length`), and a total
query bound on the program bounds it — turning the operational `IsTotalQueryBound` into a length
bound on every run. -/

/-- The transcript length equals the number of handler-answered steps; here both are `2`. -/
example : (OracleComp.transcript allHeads prog).length = stepsToHalt allHeads prog :=
  OracleComp.transcript_length allHeads prog

/-- `prog` makes at most two queries. -/
example : IsTotalQueryBound prog 2 :=
  ⟨by norm_num, fun _ => ⟨by norm_num, fun _ => trivial⟩⟩

/-- Hence every handler-answered transcript of `prog` has length at most `2`. -/
example : (OracleComp.transcript allHeads prog).length ≤ 2 :=
  OracleComp.transcript_length_le_of_isTotalQueryBound allHeads
    ⟨by norm_num, fun _ => ⟨by norm_num, fun _ => trivial⟩⟩

/-- Both of `prog`'s queries go to the single coin oracle `()`. -/
example : (OracleComp.transcript allHeads prog).countQ (· = ()) = 2 := by decide

/-- A per-index budget of `2` on the coin oracle bounds that count. -/
example (hb : IsPerIndexQueryBound prog (fun _ => 2)) :
    (OracleComp.transcript allHeads prog).countQ (· = ()) ≤ 2 :=
  OracleComp.transcript_countQ_le_of_isPerIndexQueryBound allHeads () hb

/-! ## The typed transcript (`FreeM.Path`)

A program's run against a handler is a *typed* root-to-leaf path through its `FreeM` tree: its leaf
is the simulated value, and its answer-erasure is the flat `QueryLog`. -/

/-- The handler path's leaf is `prog`'s value. -/
example : PFunctor.FreeM.output prog (OracleComp.handlerPath allHeads prog) = true := by
  rw [OracleComp.output_handlerPath]; decide

/-- Erasing the typed handler path recovers the flat transcript. -/
example : OracleComp.logOfPath prog (OracleComp.handlerPath allHeads prog) =
    [⟨(), true⟩, ⟨(), true⟩] := by
  rw [OracleComp.logOfPath_handlerPath]; decide

/-! ## A handler is a PolyFun section; a log is a free-monoid trace

`OracleHandler` is now `PFunctor.Section spec.toPFunctor` (a lens). It still drops into the existing
deterministic `QueryImpl spec Id` API through its `Coe`, and `QueryLog` is unified with the generic
`PFunctor.TraceList`. -/

/-- A handler coerces straight into the deterministic `QueryImpl spec Id` API (via its `Coe`). -/
example : evalWithAnswerFn allHeads prog = true := by decide

/-- A query log is literally the free monoid on query/answer events (`PFunctor.TraceList`). -/
example : QueryLog coinSpec = PFunctor.TraceList coinSpec.toPFunctor := rfl

end DynSystemExamples
