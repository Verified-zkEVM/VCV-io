/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.Control.Monad.Hom
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Executing Monads as Probabalistic Computations

This file defines a structure `ExecutionMethod spec m` to provide a way to specify how to
run a monadic computation as a `ProbComp` (and in particular get probability distributions on
outputs of the computation).
Definitions like `SignatureAlg` extend this to allow them to be defined over arbitrary monads.
This means that definitions like "IND-CPA secure" are always *relative* to the execution method.

`ExecutionMethod.default` handles the case where `spec := probSpec`, in which case the
"execution function" is just `id`.
-/

open OracleComp

universe u v w

/-- An `ExecutionMethod m` provides a way to map computations in the monad `m` into `ProbComp`.
In particular it allows computations in `m` -/
structure ExecutionMethod (m : Type → Type v) [Monad m] where
    SemState : Type
    execSem : m →ᵐ StateT SemState ProbComp
    initState : SemState
    exec {α : Type} : m α → ProbComp α
    exec_eq_execSem {α : Type} (mx : m α) : exec mx = (execSem mx).run' initState
    liftProbComp : ProbComp →ᵐ m
    execSem_liftProbComp :
      execSem ∘ₘ liftProbComp = MonadHom.ofLift ProbComp (StateT SemState ProbComp)

namespace ExecutionMethod

variable {m : Type → Type v} [Monad m]

@[simp] theorem exec_liftProbComp_apply
    (execMethod : _root_.ExecutionMethod m) {α : Type} (px : ProbComp α) :
    execMethod.exec (execMethod.liftProbComp px) = px := by
  rw [execMethod.exec_eq_execSem]
  change ((execMethod.execSem ∘ₘ execMethod.liftProbComp) px).run' execMethod.initState = px
  rw [execMethod.execSem_liftProbComp]
  rw [MonadHom.ofLift_apply]
  rw [StateT.run']
  rw [map_eq_bind_pure_comp]
  change (((liftM px : StateT execMethod.SemState ProbComp α).run execMethod.initState) >>=
      pure ∘ fun x => x.1) = px
  have h := congrArg (fun q => q >>= pure ∘ fun x => x.1)
    (OracleComp.liftM_run_StateT (x := px) (s := execMethod.initState))
  have h' :
      (((liftM px : StateT execMethod.SemState ProbComp α).run execMethod.initState) >>=
        pure ∘ fun x => x.1) =
      ((px >>= fun a => pure (a, execMethod.initState)) >>= pure ∘ fun x => x.1) := by
    simpa using h
  rw [h']
  simp

@[simp] theorem exec_bind_liftProbComp_apply
    (execMethod : _root_.ExecutionMethod m) {α β : Type}
    (px : ProbComp α) (f : α → m β) :
    execMethod.exec (do
      let x ← execMethod.liftProbComp px
      f x) =
    (do
      let x ← px
      execMethod.exec (f x)) := by
  rw [execMethod.exec_eq_execSem]
  rw [MonadHom.mmap_bind]
  have hlift :
      execMethod.execSem (execMethod.liftProbComp px) =
      (MonadHom.ofLift ProbComp (StateT execMethod.SemState ProbComp)) px := by
    exact congrArg (fun H => H px) execMethod.execSem_liftProbComp
  rw [hlift, MonadHom.ofLift_apply]
  change Prod.fst <$> ((liftM px >>= fun x => execMethod.execSem (f x)).run execMethod.initState) =
    (do
      let x ← px
      execMethod.exec (f x))
  rw [StateT.run_bind]
  have hrunLift :
      ((liftM px : StateT execMethod.SemState ProbComp α).run execMethod.initState) =
      px >>= fun x => pure (x, execMethod.initState) := by
    simpa using OracleComp.liftM_run_StateT (x := px) (s := execMethod.initState)
  rw [hrunLift]
  simp [execMethod.exec_eq_execSem, map_bind]

@[simp] theorem exec_map_apply
    (execMethod : _root_.ExecutionMethod m) [LawfulMonad m]
    {α β : Type} (f : α → β) (mx : m α) :
    execMethod.exec (f <$> mx) = f <$> execMethod.exec mx := by
  rw [execMethod.exec_eq_execSem, execMethod.exec_eq_execSem]
  simp [MonadHom.mmap_map, StateT.run'_eq, map_eq_bind_pure_comp]

/-- In a public-randomness plus state-oracle world, lifted `ProbComp` computations ignore the
oracle state even before the initial state is chosen. -/
theorem execSem_liftProbComp_withStateOracle
    {ι : Type} {stateSpec : OracleSpec ι} {σ : Type}
    (stateImpl : QueryImpl stateSpec (StateT σ ProbComp))
    {α : Type} (c : ProbComp α) :
    simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + stateImpl)
      (monadLift c) =
        (MonadHom.ofLift ProbComp (StateT σ ProbComp)) c := by
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp)
  funext s
  rw [show simulateQ (idImpl + stateImpl) (monadLift c) = simulateQ idImpl c by
    simpa [MonadLift.monadLift] using
      (QueryImpl.simulateQ_add_liftComp_left (impl₁' := idImpl) (impl₂' := stateImpl) c)]
  change (simulateQ idImpl c).run s = ((MonadHom.ofLift ProbComp (StateT σ ProbComp)) c).run s
  have hrun :
      ∀ {β : Type} (oa : ProbComp β) (s : σ),
        (simulateQ idImpl oa).run s = (fun x => (x, s)) <$> oa := by
    intro β oa
    induction oa using OracleComp.inductionOn with
    | pure x =>
        intro s
        simp
    | query_bind t oa ih =>
        intro s
        change
          (do
            let a ← (liftM (query t) : ProbComp (unifSpec.Range t))
            (simulateQ idImpl (oa a)).run s) =
            (do
              let a ← liftM (query t)
              (fun x => (x, s)) <$> oa a)
        have hfun :
            (fun a => (simulateQ idImpl (oa a)).run s) =
              (fun a => (fun x => (x, s)) <$> oa a) := by
          funext a
          exact ih a s
        simp [hfun]
  rw [hrun c s]
  simpa using (OracleComp.liftM_run_StateT (x := c) (s := s))

/-- Execute a computation in `ProbComp` via `ProbComp`, by using the identity function. -/
@[simp] protected def default : ExecutionMethod ProbComp where
  SemState := PUnit
  execSem := MonadHom.ofLift ProbComp (StateT PUnit ProbComp)
  initState := PUnit.unit
  exec := fun mx => mx
  exec_eq_execSem := by
    intro α mx
    rw [MonadHom.ofLift_apply]
    rw [StateT.run']
    rw [map_eq_bind_pure_comp]
    change mx = (((liftM mx : StateT PUnit ProbComp α).run PUnit.unit) >>= pure ∘ fun x => x.1)
    have h := congrArg (fun q => q >>= pure ∘ fun x => x.1)
      (OracleComp.liftM_run_StateT (x := mx) (s := PUnit.unit))
    have h' :
        (((liftM mx : StateT PUnit ProbComp α).run PUnit.unit) >>= pure ∘ fun x => x.1) =
          ((mx >>= fun a => pure (a, PUnit.unit)) >>= pure ∘ fun x => x.1) := by
      simpa using h
    rw [h']
    simp
  liftProbComp := MonadHom.id ProbComp
  execSem_liftProbComp := by
    ext α x
    simp [MonadHom.ofLift]

end ExecutionMethod
