/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp
import ToMathlib.Control.StateT

/-!
# Simulation Semantics for Oracles in a Computation

-/

open OracleComp Prod

universe u v w

variable {α β γ : Type u} {spec : OracleSpec}
    {m : Type u → Type v} {n : Type u → Type w}

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulateQ` gives a method for applying a simulation oracle to a specific computation. -/
def QueryImpl (spec : OracleSpec) (m : Type u → Type v) :=
  (x : spec.domain) → m (spec.range x)

namespace QueryImpl

instance [spec.Inhabited] [Pure m] :
  Inhabited (QueryImpl spec m) := ⟨fun _ => pure default⟩

/-- Two query implementations are the same if they are the same on all query inputs. -/
@[ext] lemma ext {so so' : QueryImpl spec m}
    (h : ∀ x : spec.domain, so x = so' x) : so = so' := funext h

-- instance [MonadLift m n] : Coe (QueryImpl spec m) (QueryImpl spec n) where
--   coe impl := fun x => liftM (impl x)

/-- Gadget for auto-adding a lift to the end of a query implementation.
Useful when chaining simulations with different monad transformers. -/
def liftTarget {spec : OracleSpec} {m : Type u → Type v}
    {n : Type u → Type w} [MonadLiftT m n]
    (impl : QueryImpl spec m) : QueryImpl spec n :=
  fun t : spec.domain => liftM (impl t)

/-- Given that queries in `spec` lift to the monad `m` we get an implementation via lifting. -/
def ofLift (spec : OracleSpec) (m : Type u → Type v)
    [MonadLiftT (OracleQuery spec) m] : QueryImpl spec m :=
  fun t : spec.domain => liftM (query t)

@[simp] lemma ofLift_apply (spec : OracleSpec) (m : Type u → Type v)
    [MonadLiftT (OracleQuery spec) m] (t : spec.domain) :
    ofLift spec m t = liftM (query t) := rfl

/-- Implement the oracles by returning default values.  -/
def ofDefault (spec : OracleSpec) [spec.Inhabited] (m : Type u → Type v) [Pure m] :
    QueryImpl spec m := fun _ => pure default

@[simp] lemma ofDefault_apply (spec : OracleSpec) [spec.Inhabited] (m : Type u → Type v) [Pure m]
    (t : spec.domain) : QueryImpl.ofDefault spec m t = pure default := rfl

end QueryImpl

/-- `HasSimulateQ spec m n` means that `OracleQuery spec` can lift into `m`,
and a `MonadHom` `simulateQ` that lifts an implementation of queries to a
map between the two monads. -/
class HasSimulateQ (spec : OracleSpec)
    (m : outParam (Type u → Type v)) (n : Type u → Type w)
    [Monad m] [MonadLiftT (OracleQuery spec) m] [Monad n] where
  simulateQ (impl : QueryImpl spec n) : m →ᵐ n
  simulateQ_liftM (impl : QueryImpl spec n) {α : Type u} (q : OracleQuery spec α) :
    simulateQ impl (q : m α) = q.2 <$> impl q.1

export HasSimulateQ (simulateQ simulateQ_liftM)

attribute [simp] simulateQ_liftM

section simulateQ

variable [Monad m] [MonadLiftT (OracleQuery spec) m] [Monad n]
    [HasSimulateQ spec m n] (impl : QueryImpl spec n)

@[simp] lemma simulateQ_query [LawfulMonad n] (t : spec.domain) :
    simulateQ impl (query t : m _) = impl t := by
  simp [query_def, HasSimulateQ.simulateQ_liftM (m := m)]

@[simp] lemma simulateQ_query_bind [LawfulMonad n] (t : spec.domain) (ou : spec.range t → m β) :
    simulateQ impl ((query t : m _) >>= ou) =
      impl t >>= fun u => simulateQ impl (ou u) := by aesop

lemma simulateQ_pure (x : α) : simulateQ impl (pure x : m α) = pure x := by simp

lemma simulateQ_bind [LawfulMonad n] (mx : m α) (my : α → m β) :
    simulateQ impl (mx >>= my) = simulateQ impl mx >>= fun u => simulateQ impl (my u) := by simp

lemma simulateQ_map [LawfulMonad m] [LawfulMonad n] (mx : m α) (f : α → β) :
    simulateQ impl (f <$> mx) = f <$> simulateQ impl mx := by simp

lemma simulateQ_seq [LawfulMonad m] [LawfulMonad n] (og : m (α → β)) (mx : m α) :
    simulateQ impl (og <*> mx) = simulateQ impl og <*> simulateQ impl mx := by simp

lemma simulateQ_seqLeft [LawfulMonad m] [LawfulMonad n] (mx : m α) (my : m β) :
    simulateQ impl (mx <* my) = simulateQ impl mx <* simulateQ impl my := by simp

lemma simulateQ_seqRight [LawfulMonad m] [LawfulMonad n] (mx : m α) (my : m β) :
    simulateQ impl (mx *> my) = simulateQ impl mx *> simulateQ impl my := by simp

@[simp] lemma simulateQ_ite (p : Prop) [Decidable p] (mx oa' : m α) :
    simulateQ impl (ite p mx oa') = ite p (simulateQ impl mx) (simulateQ impl oa') := by
  split_ifs <;> rfl

end simulateQ

namespace OracleComp

/-- Canonical lifting of a function `NatOracleQuery spec α → m α`
to a morphism `OracleComp spec →ᵐ m` by preserving `bind`, `pure` -/
instance {spec : OracleSpec} {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    HasSimulateQ spec (OracleComp spec) n where
  simulateQ impl := PFunctor.FreeM.mapMHom impl
  simulateQ_liftM impl q := by simp [PFunctor.FreeM.mapM]

variable [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)

lemma simulateQ_def (impl : QueryImpl spec n) :
    (simulateQ impl : OracleComp spec →ᵐ n) = PFunctor.FreeM.mapMHom impl := rfl

@[simp] lemma simulateQ_ofLift_eq_self (mx : OracleComp spec α) :
    simulateQ (QueryImpl.ofLift spec (OracleComp spec)) mx = mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h]

end OracleComp

/-- Simulate with an `OptionT` failure chance in any `AlternativeMonad`,
sending the additional value to `failure`. -/
instance [Monad m] [MonadLiftT (OracleQuery spec) m]
    {n : Type u → Type w} [AlternativeMonad n] [LawfulMonad n]
    [LawfulAlternative n] [h : HasSimulateQ spec m n] :
    HasSimulateQ spec (OptionT m) n where
  simulateQ impl := OptionT.mapM' (h.simulateQ impl)
  simulateQ_liftM impl q := by
    simp [OptionT.mapM', liftM, monadLift, MonadLift.monadLift, h.simulateQ_liftM]

-- /-- Simulate under an optional transformer-/
-- instance [Monad m] [MonadLiftT (OracleQuery spec) m] [Monad n]
--     [HasSimulateQ spec m n] :
--     HasSimulateQ spec (OptionT m) (OptionT n) where
--   simulateQ impl := {
--     toFun mx := by
--       have : n (Option α) := simulateQ impl (OptionT.run mx)
--       sorry
--     toFun_pure' := _
--     toFun_bind' := _
--   }
--   simulateQ_liftM impl q := sorry

/-- Simulate under a state transformer. -/
instance [Monad m] [MonadLiftT (OracleQuery spec) m] [Monad n]
    [HasSimulateQ spec m n] (σ : Type u) :
    HasSimulateQ spec (StateT σ m) (StateT σ n) where
  simulateQ impl := {
    toFun {α} mx σ := by
      specialize mx σ
      stop
      refine StateT.map _
      sorry
    toFun_pure' := sorry
    toFun_bind' := sorry
  }
  simulateQ_liftM impl q := sorry

/-- Simulate underneath both state and option transformers.
NOTE: `OptionT` behaves weird with type-classes because it is marked `expose`. -/
instance [Monad m] [MonadLiftT (OracleQuery spec) m] [Monad n]
    [HasSimulateQ spec m n] (σ : Type u) :
    HasSimulateQ spec (StateT σ (OptionT m)) (StateT σ (OptionT n)) where
  simulateQ impl := sorry
  simulateQ_liftM impl q := sorry

section tests

-- Note that keeping `OptionT` "inside" helps with inference

example {spec₁ spec₂ : OracleSpec} (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₂))) :
    OptionT (OracleComp spec₂) α :=
  simulateQ impl₂ <| simulateQ impl₁ mx

example {spec₁ spec₂ spec₃ : OracleSpec} (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OptionT (OracleComp spec₂)))
    (impl₂ : QueryImpl spec₂ (StateT β (OptionT (OracleComp spec₃)))) :
    StateT β (OptionT (OracleComp spec₃)) α :=
  simulateQ impl₂ <| simulateQ impl₁ mx

example {spec₁ spec₂ spec₃ : OracleSpec} (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (StateT β (OracleComp spec₂)))
    (impl₂ : QueryImpl spec₂ (StateT β (OptionT (OracleComp spec₃)))) :
    StateT β (OptionT (OracleComp spec₃)) α :=
  simulateQ impl₂ <| simulateQ impl₁ mx

example {spec₁ spec₂ spec₃ : OracleSpec} (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OptionT (OracleComp spec₂)))
    (impl₃ : QueryImpl spec₂ (StateT β (OracleComp spec₃)))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₂)))
    (impl₄ : QueryImpl spec₃ (StateT β (OracleComp spec₁))) :
    StateT β (OptionT (OracleComp spec₁)) α :=
  simulateQ impl₄.liftTarget <|
    simulateQ impl₃.liftTarget <|
    simulateQ impl₂.liftTarget <|
    liftM (simulateQ impl₁ mx)

example {spec₁ spec₂ spec₃ : OracleSpec} (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OptionT (OracleComp spec₂)))
    (impl₂ : QueryImpl spec₂ (StateT β (OracleComp spec₃))) :
    StateT β (OptionT (OracleComp spec₃)) α :=
  simulateQ impl₂.liftTarget <|
    liftM (simulateQ impl₁ mx)

example {spec₁ spec₂ spec₃ : OracleSpec} (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (StateT β (OracleComp spec₂)))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₃))) :
    (StateT β (OptionT (OracleComp spec₃))) α :=
  simulateQ impl₂.liftTarget <| -- Need `liftTarget`
    liftM <| simulateQ impl₁ mx

end tests
