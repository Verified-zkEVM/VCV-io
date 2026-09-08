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
Artifacts keep each output together with its final state and ordered surface query log.
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
structure RuntimeArtifact {ι κ : Type} {Import : OracleSpec ι} {Surface : OracleSpec κ}
    (Γ : OracleRuntime Import Surface) (α : Type) where
  private mk ::
  output : α
  state : Γ.State
  trace : OracleSpec.QueryLog Surface

/-- Artifacts agree when all three paired observations agree. -/
@[ext] theorem RuntimeArtifact.ext {ι κ : Type} {Import : OracleSpec ι}
    {Surface : OracleSpec κ} {Γ : OracleRuntime Import Surface} {α : Type}
    {a b : RuntimeArtifact Γ α} (output : a.output = b.output)
    (state : a.state = b.state) (trace : a.trace = b.trace) : a = b := by
  cases a
  cases b
  simp_all

namespace OracleRuntime

variable {ι κ : Type} {Import : OracleSpec ι} {Surface : OracleSpec κ}
    (Γ : OracleRuntime Import Surface) {α β : Type}

/-- Run from a supplied state, recording only the surface query/answer sequence. -/
def runFrom (s : Γ.State) (program : OracleComp Surface α) :
    OracleComp Import (RuntimeArtifact Γ α) :=
  (fun p => RuntimeArtifact.mk p.1.1 p.2 p.1.2) <$>
    Γ.handler.runState s program.withQueryLog

/-- Initialize once and retain the paired output, final state, and surface log. -/
def runArtifact (program : OracleComp Surface α) :
    OracleComp Import (RuntimeArtifact Γ α) :=
  Γ.setup >>= fun s => Γ.runFrom s program

/-- Continue a completed phase from its final state, retaining the ordered accumulated log. -/
def resume (previous : RuntimeArtifact Γ α) (next : α → OracleComp Surface β) :
    OracleComp Import (RuntimeArtifact Γ β) :=
  (fun result => RuntimeArtifact.mk result.output result.state
    (previous.trace ++ result.trace)) <$> Γ.runFrom previous.state (next previous.output)

/-- Membership in structural runner support, not positive probability for arbitrary specs. -/
def GeneratedBy (program : OracleComp Surface α) (result : RuntimeArtifact Γ α) : Prop :=
  result ∈ support (Γ.runArtifact program)

/-- Initialization is performed before the first phase. -/
theorem runArtifact_eq (program : OracleComp Surface α) :
    Γ.runArtifact program = Γ.setup >>= fun s => Γ.runFrom s program := by
  simp [runArtifact]

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
theorem runArtifact_bind (program : OracleComp Surface α)
    (next : α → OracleComp Surface β) :
    Γ.runArtifact (program >>= next) =
      Γ.runArtifact program >>= fun a => Γ.resume a next := by
  simp only [runArtifact, runFrom_bind, bind_assoc]

end OracleRuntime
