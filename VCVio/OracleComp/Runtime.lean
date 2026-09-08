/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
public import VCVio.OracleComp.QueryTracking.LoggingOracle

/-! # Persistent oracle runtimes

A runtime initializes its state once, then interprets surface computations sequentially.
Run results keep each output together with its final state and ordered surface query log.
The carrier does not certify provenance: `OracleRuntime.GeneratedBy` records membership in
an actual runner's support. Import queries made by setup or handlers are not surface queries.
This interface uses small types, as do the sequential query-logging laws.
-/

public section

/-- An explicitly initialized, persistent interpretation of a surface oracle. -/
structure OracleRuntime {ι κ : Type} (Import : OracleSpec ι) (Surface : OracleSpec κ) where
  State : Type
  setup : OracleComp Import State
  handler : QueryImpl.Stateful Import Surface State

/-- Paired runner output. Construction is controlled by the runtime API; sampling provenance
is a separate support-membership obligation. -/
structure RunResult {ι κ : Type} {Import : OracleSpec ι} {Surface : OracleSpec κ}
    (Γ : OracleRuntime Import Surface) (α : Type) where
  private mk ::
  output : α
  state : Γ.State
  trace : OracleSpec.QueryLog Surface

/-- Run results agree when all three paired observations agree. -/
@[ext] theorem RunResult.ext {ι κ : Type} {Import : OracleSpec ι}
    {Surface : OracleSpec κ} {Γ : OracleRuntime Import Surface} {α : Type}
    {a b : RunResult Γ α} (output : a.output = b.output)
    (state : a.state = b.state) (trace : a.trace = b.trace) : a = b := by
  cases a
  cases b
  simp_all

namespace OracleRuntime

variable {ι κ : Type} {Import : OracleSpec ι} {Surface : OracleSpec κ}
    (Γ : OracleRuntime Import Surface) {α β : Type}

/-- Run from a supplied state, recording only the surface query/answer sequence. -/
def runFrom (s : Γ.State) (program : OracleComp Surface α) :
    OracleComp Import (RunResult Γ α) :=
  (fun p => RunResult.mk p.1.1 p.2 p.1.2) <$>
    Γ.handler.runState s program.withQueryLog

/-- Initialize once and retain the paired output, final state, and surface log. -/
def run (program : OracleComp Surface α) :
    OracleComp Import (RunResult Γ α) :=
  Γ.setup >>= fun s => Γ.runFrom s program

/-- Continue a completed phase from its final state, retaining the ordered accumulated log. -/
def resume (previous : RunResult Γ α) (next : α → OracleComp Surface β) :
    OracleComp Import (RunResult Γ β) :=
  (fun result => RunResult.mk result.output result.state
    (previous.trace ++ result.trace)) <$> Γ.runFrom previous.state (next previous.output)

/-- Membership in structural runner support, not positive probability for arbitrary specs. -/
def GeneratedBy (program : OracleComp Surface α) (result : RunResult Γ α) : Prop :=
  result ∈ support (Γ.run program)

/-- Initialization is performed before the first phase. -/
theorem run_eq (program : OracleComp Surface α) :
    Γ.run program = Γ.setup >>= fun s => Γ.runFrom s program := by
  simp [run]

/-- All observations are extracted together from one logged stateful execution. -/
theorem runFrom_observe (s : Γ.State) (program : OracleComp Surface α) :
    (fun a => (a.output, a.state, a.trace)) <$> Γ.runFrom s program =
      (fun p => (p.1.1, p.2, p.1.2)) <$>
        Γ.handler.runState s program.withQueryLog := by
  simp [runFrom, Functor.map_map]

/-- A pure phase returns its input without changing state or adding queries. -/
@[simp] theorem runFrom_pure (s : Γ.State) (x : α) :
    (fun a => (a.output, a.state, a.trace)) <$> Γ.runFrom s (pure x) =
      pure (x, s, []) := by
  simp [runFrom]

/-- Erasing the surface log retains the ordinary stateful execution. -/
theorem runFrom_eraseTrace (s : Γ.State) (program : OracleComp Surface α) :
    (fun a => (a.output, a.state)) <$> Γ.runFrom s program =
      Γ.handler.runState s program := by
  have erase : Prod.fst <$> program.withQueryLog = program := by
    exact loggingOracle.fst_map_run_simulateQ program
  have h := congrArg (Γ.handler.runState s) erase
  simpa [runFrom, QueryImpl.Stateful.runState, monad_norm] using h

/-- Sequential phases share state and concatenate their logs in execution order. -/
theorem runFrom_bind (s : Γ.State) (program : OracleComp Surface α)
    (next : α → OracleComp Surface β) :
    Γ.runFrom s (program >>= next) = Γ.runFrom s program >>= fun a => Γ.resume a next := by
  simp [runFrom, resume, OracleComp.withQueryLog_bind, QueryImpl.Stateful.runState,
    monad_norm]

/-- Resumption does not repeat setup. -/
theorem run_bind (program : OracleComp Surface α)
    (next : α → OracleComp Surface β) :
    Γ.run (program >>= next) =
      Γ.run program >>= fun a => Γ.resume a next := by
  simp only [run, runFrom_bind, bind_assoc]

/-- A generated result's output and surface log belong to the original logged program's
structural support. Stateful interpretation may restrict possible answers, but cannot invent a
surface execution. No probability-spec assumption is required. -/
theorem mem_support_logged_of_generatedBy (program : OracleComp Surface α)
    (result : RunResult Γ α) (generated : Γ.GeneratedBy program result) :
    (result.output, result.trace) ∈ support program.withQueryLog := by
  rw [GeneratedBy, run_eq, mem_support_bind_iff] at generated
  obtain ⟨s, _, reached⟩ := generated
  have observed : (result.output, result.state, result.trace) ∈ support
      ((fun a : RunResult Γ α => (a.output, a.state, a.trace)) <$> Γ.runFrom s program) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ reached
  rw [runFrom_observe, support_map] at observed
  obtain ⟨⟨⟨out, trace⟩, finalState⟩, hrun, heq⟩ := observed
  have hlogged : (out, trace) ∈ support program.withQueryLog := by
    apply OracleComp.support_simulateQ_run'_subset Γ.handler program.withQueryLog s
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst hrun
  have same : (out, trace) = (result.output, result.trace) := by
    simpa only [Prod.mk.injEq] using congrArg (fun p => (p.1, p.2.2)) heq
  exact same ▸ hlogged

end OracleRuntime
