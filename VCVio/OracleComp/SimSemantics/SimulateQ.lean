/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
import VCVio.Prelude
import ToMathlib.Control.OptionT

/-!
# Simulation Semantics for Oracles in a Computation

-/

open OracleComp Prod

universe u v w

variable {α β γ : Type u}

section simulateQ

/-- Given an implementation of `spec` in the monad `r`, convert an `OracleComp spec α` to a
implementation in `r α` by substituting `impl t` for `query t` throughout. -/
def simulateQ {ι} {spec : OracleSpec ι} {r : Type u → Type _} [Monad r]
    (impl : QueryImpl spec r) {α : Type u} (mx : OracleComp spec α) : r α :=
  PFunctor.FreeM.mapM impl mx

variable {ι} {spec : OracleSpec ι} {r m n : Type u → Type*}
    [Monad r] (impl : QueryImpl spec r)

@[simp, grind =, game_rule]
lemma simulateQ_pure (x : α) :
    simulateQ impl (pure x : OracleComp spec α) = pure x := rfl

@[simp, grind =, game_rule]
lemma simulateQ_bind [LawfulMonad r] (mx : OracleComp spec α) (my : α → OracleComp spec β) :
    simulateQ impl (mx >>= my) = simulateQ impl mx >>= fun x => simulateQ impl (my x) := by
  unfold simulateQ; exact PFunctor.FreeM.mapM_bind' impl mx my

/-- Version of `simulateQ` that bundles into a monad hom. -/
@[reducible]
def simulateQ' [LawfulMonad r] (impl : QueryImpl spec r) : OracleComp spec →ᵐ r where
  toFun {_α} mx := simulateQ impl mx
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

@[simp, grind =, game_rule]
lemma simulateQ_query [LawfulMonad r] (q : OracleQuery spec α) :
    simulateQ impl (liftM q) = q.cont <$> (impl q.input) := by
  unfold simulateQ; simp [OracleComp.liftM_def]

/-- Specialized form of `simulateQ_query` for the canonical `spec.query t`
constructor: `simulateQ impl (liftM (spec.query t)) = impl t`.

The general `simulateQ_query` rewrite leaves an `id <$>` artifact when applied
to `spec.query t` (because `(spec.query t).cont = id`). That artifact is
harmless when `spec.Range t` is concrete (it disappears under definitional
reduction), but in *parametric* sum-spec contexts (`(E₁ + E₂).Range (Sum.inl t)`
vs `E₁.Range t`, both abstract atoms) the type annotations diverge and
`id_map` no longer fires under `simp only`. This lemma sidesteps the artifact
entirely and is the canonical entry point for simplifying `simulateQ` over an
explicit `spec.query t`. -/
@[simp, grind =]
lemma simulateQ_spec_query [LawfulMonad r] (t : spec.Domain) :
    simulateQ impl (liftM (spec.query t)) = impl t := by
  rw [simulateQ_query]; simp

@[simp]
lemma simulateQ_query_bind [LawfulMonad r] (q : OracleQuery spec α)
    (ou : α → OracleComp spec β) : simulateQ impl (liftM q >>= ou) =
      liftM (impl q.input) >>= fun u => simulateQ impl (ou (q.cont u)) := by aesop

@[simp, grind =]
lemma simulateQ_map [LawfulMonad r] (mx : OracleComp spec α) (f : α → β) :
    simulateQ impl (f <$> mx) = f <$> simulateQ impl mx := by
  simp [monad_norm]

@[simp]
lemma simulateQ_seq [LawfulMonad r] (og : OracleComp spec (α → β)) (mx : OracleComp spec α) :
    simulateQ impl (og <*> mx) = simulateQ impl og <*> simulateQ impl mx := by
  simp [monad_norm]

@[simp]
lemma simulateQ_seqLeft [LawfulMonad r] (mx : OracleComp spec α) (my : OracleComp spec β) :
    simulateQ impl (mx <* my) = simulateQ impl mx <* simulateQ impl my := by
  simp [seqLeft_eq_bind]

@[simp]
lemma simulateQ_seqRight [LawfulMonad r] (mx : OracleComp spec α) (my : OracleComp spec β) :
    simulateQ impl (mx *> my) = simulateQ impl mx *> simulateQ impl my := by
  simp [seqRight_eq_bind]

@[simp]
lemma simulateQ_ite (p : Prop) [Decidable p] (mx mx' : OracleComp spec α) :
    simulateQ impl (ite p mx mx') = ite p (simulateQ impl mx) (simulateQ impl mx') := by
  split_ifs <;> rfl

@[simp]
lemma simulateQ_liftTarget {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    (impl : QueryImpl spec m) (comp : OracleComp spec α) :
    simulateQ (impl.liftTarget n) comp = liftM (simulateQ impl comp) := by
  induction comp using OracleComp.inductionOn with
  | pure x => simp [liftM_pure]
  | query_bind t k ih => simp [ih, liftM_bind]

end simulateQ

variable {ι} {spec : OracleSpec ι} {n : Type u → Type v}
  [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)

lemma simulateQ_def (impl : QueryImpl spec n) (mx : OracleComp spec α) :
    simulateQ impl mx = PFunctor.FreeM.mapMHom impl mx := rfl

/-- `QueryImpl.id'` is an identity for `simulateQ` with implementaiton in `OracleComp spec`. -/
@[simp, grind =]
lemma simulateQ_id' (mx : OracleComp spec α) :
    simulateQ (QueryImpl.id' spec) mx = mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h]

/-- Lifting queries to their original implementation has no effect on a computation. -/
lemma simulateQ_ofLift_eq_self {α} (mx : OracleComp spec α) :
    simulateQ (QueryImpl.ofLift spec (OracleComp spec)) mx = mx := by simp

section tests

variable {ι₁ ι₂ ι₃ ι₄}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄}

example (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₂))) :
    OptionT (OracleComp spec₂) α :=
  simulateQ impl₂ <|
    simulateQ impl₁ mx

example (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₃)))
    (impl₃ : QueryImpl spec₃ (OptionT (OracleComp spec₄))) :
    OptionT (OptionT (OracleComp spec₄)) α :=
  simulateQ impl₃ <| simulateQ impl₂ <| simulateQ impl₁ mx

example (mx : OptionT (OracleComp spec₁) α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OracleComp spec₃)) :
    OptionT (OracleComp spec₃) α :=
  simulateQ impl₂ <| simulateQ impl₁ <| mx

end tests

section OptionT

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

end OptionT
