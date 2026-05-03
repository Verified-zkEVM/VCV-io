/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.SimulateQ
import ToMathlib.Control.OptionT

/-!
# Simulation Semantics through `OptionT` Handlers

Distributivity lemmas for `simulateQ` over `OptionT`-shaped operations
(`Option.elim`, `Option.elimM`, `OptionT.bind`, `OptionT.lift`).

These lemmas appeal to the central `simulateQ` theory in
`VCVio.OracleComp.SimSemantics.SimulateQ`; the file is grouped under
`SimSemantics/OptionT/` to mirror the per-transformer organization used for
`StateT`, `WriterT`, and `ReaderT`.
-/

open OracleComp Prod

universe u v w

variable {α β γ : Type u}

variable {ι} {spec : OracleSpec ι} {r n : Type u → Type*}
    [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)

omit [LawfulMonad n] in
@[simp] lemma simulateQ_option_elim (x : Option α) (my : OracleComp spec β)
    (my' : α → OracleComp spec β) : simulateQ impl (x.elim my my') =
    x.elim (simulateQ impl my) (fun x => simulateQ impl (my' x)) := by
  cases x <;> simp

@[simp] lemma simulateQ_option_elimM (mx : OracleComp spec (Option α))
    (my : OracleComp spec β) (my' : α → OracleComp spec β) :
    simulateQ impl (Option.elimM mx my my') =
    Option.elimM (simulateQ impl mx) (simulateQ impl my) (fun x => simulateQ impl (my' x)) := by
  unfold Option.elimM
  rw [simulateQ_bind]
  exact bind_congr fun x => simulateQ_option_elim impl x my my'

/-- `simulateQ` distributes through `OptionT.bind`, stated via `OptionT.run`. -/
lemma simulateQ_optionT_bind'
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
    simulateQ impl (mx >>= f).run =
    (simulateQ impl mx.run >>= fun a => simulateQ impl (f a).run : OptionT n β) := by
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind]
  refine bind_congr fun x => ?_
  induction x <;> simp only [Option.elim_none, Option.elim_some, simulateQ_pure]

/-- `simulateQ` distributes through `OptionT.bind`, stated via `Option.elimM`. -/
lemma simulateQ_optionT_bind''
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
    simulateQ impl (mx >>= f).run =
    Option.elimM (simulateQ impl mx.run) (pure none) (fun a => simulateQ impl (f a).run) := by
  simp

/-- `simulateQ` distributes through `OptionT.bind`: the simulated OptionT-bind is the
    OptionT-bind of the simulated pieces. -/
lemma simulateQ_optionT_bind
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
    simulateQ impl (mx >>= f : OptionT (OracleComp spec) β) =
    (simulateQ impl mx >>= fun a => simulateQ impl (f a) : OptionT n β) := by
  apply simulateQ_optionT_bind'

/-- `simulateQ` commutes with `OptionT.lift`. -/
@[simp] lemma simulateQ_optionT_lift
    (comp : OracleComp spec α) :
    simulateQ impl (OptionT.lift comp : OptionT (OracleComp spec) α) =
      (OptionT.lift (simulateQ impl comp) : OptionT n α) := by
  simp only [OptionT.lift, OptionT.mk, simulateQ_bind, simulateQ_pure]
