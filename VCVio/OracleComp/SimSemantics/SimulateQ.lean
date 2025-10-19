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

variable {α β γ : Type u}

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulateQ` gives a method for applying a simulation oracle to a specific computation. -/
@[reducible] def QueryImpl (spec : OracleSpec) (m : Type u → Type v) :=
  (x : spec.domain) → m (spec.range x)

namespace QueryImpl

variable {spec : OracleSpec} {m : Type u → Type v} {n : Type u → Type w}

instance [spec.Inhabited] [Pure m] : Inhabited (QueryImpl spec m) := ⟨fun _ => pure default⟩

/-- Two query implementations are the same if they are the same on all query inputs. -/
@[ext] lemma ext {so so' : QueryImpl spec m}
    (h : ∀ x : spec.domain, so x = so' x) : so = so' := funext h

/-- Gadget for auto-adding a lift to the end of a query implementation. -/
def liftTarget (n : Type u → Type*) [MonadLiftT m n]
    (impl : QueryImpl spec m) : QueryImpl spec n :=
  fun t : spec.domain => liftM (impl t)

@[simp] lemma liftTarget_apply (n : Type u → Type*) [MonadLiftT m n]
    (impl : QueryImpl spec m) (t : spec.domain) : impl.liftTarget n t = liftM (impl t) := rfl

@[simp] lemma liftTarget_self (impl : QueryImpl spec m) :
    impl.liftTarget m = impl := rfl

/-- Given that queries in `spec` lift to the monad `m` we get an implementation via lifting. -/
def ofLift (spec : OracleSpec) (m : Type u → Type v)
    [MonadLiftT (OracleQuery spec) m] : QueryImpl spec m :=
  fun t : spec.domain => liftM (query t)

@[simp] lemma ofLift_apply (spec : OracleSpec) (m : Type u → Type v)
    [MonadLiftT (OracleQuery spec) m] (t : spec.domain) : ofLift spec m t = liftM (query t) := rfl

/-- View a function from oracle inputs to outputs as an implementation in the `Id` monad.
Can be used to run a computation to get a specific value. -/
def ofFn (spec : OracleSpec) (f : (t : spec.domain) → spec.range t) :
    QueryImpl spec Id := f

/-- Version of `ofFn` that allows queries to fail to return a value. -/
def ofFn? (spec : OracleSpec) (f : (t : spec.domain) → Option (spec.range t)) :
    QueryImpl spec Option := f

end QueryImpl

/-- `HasSimulateQ spec r m n` means that an implementation of `OracleQuery spec` in terms of
a computation in `r` results in a implementation of computations in `m` in terms of `n`.
This implementation is given by a bundled monad hom `simulateQ`. We also require that queries
can be lifted into `m`, and that `simulateQ` behaves naturally with this lift.

The standard example is `HasSimulateQ spec r (OracleComp spec) r` which takes an implementation of
queries to `spec` in `r` and recursively substitutes that implementation in an `OracleComp spec`
computation, to get a value in the new spec `r`.
For example taking `r` to be `PMF` lets you asign output distributions to queries and
get an output distribution for the whole computaiton. -/
class HasSimulateQ (spec : OracleSpec) (r : Type u → Type*)
    (m : outParam (Type u → Type v)) [Monad m] [MonadLiftT (OracleQuery spec) m]
    (n : outParam (Type u → Type w)) [Monad n] [MonadLiftT r n] where
  simulateQ (impl : QueryImpl spec r) : m →ᵐ n
  simulateQ_liftM (impl : QueryImpl spec r) {α : Type u} (q : OracleQuery spec α) :
    (simulateQ impl).toFun (liftM q : m α) = q.2 <$> liftM (impl q.1)

export HasSimulateQ (simulateQ simulateQ_liftM)

attribute [simp] simulateQ_liftM

section simulateQ

variable {spec : OracleSpec} {r m n : Type u → Type*}
    [Monad m] [MonadLiftT (OracleQuery spec) m] [Monad n]
    [MonadLiftT r n] [HasSimulateQ spec r m n] (impl : QueryImpl spec r)

@[simp] lemma simulateQ_query [LawfulMonad n] (t : spec.domain) :
    simulateQ impl (query t : m (spec.range t)) = liftM (impl t) := by
  simp [query_def, HasSimulateQ.simulateQ_liftM (m := m)]

@[simp] lemma simulateQ_query_bind [LawfulMonad n] (t : spec.domain) (ou : spec.range t → m β) :
    simulateQ impl ((query t : m _) >>= ou) =
      liftM (impl t) >>= fun u => simulateQ impl (ou u) := by aesop

lemma simulateQ_pure (x : α) : simulateQ impl (pure x : m α) = (pure x : n α) := by simp

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

namespace OracleQuery

variable {spec spec' : OracleSpec}

/-- Given a map from queries in `spec` to queries in `spec'` we get a map on `OracleComp` as well
by substituting each query for the new implementation in `spec'`. -/
instance {spec spec' : OracleSpec} :
    HasSimulateQ spec (OracleQuery spec') (OracleComp spec) (OracleComp spec') where
  simulateQ impl := PFunctor.FreeM.mapMHom fun x => PFunctor.FreeM.lift (impl x)
  simulateQ_liftM _ _ _ := rfl

lemma simulateQ_def (impl : QueryImpl spec (OracleQuery spec')) :
    (simulateQ impl : OracleComp spec →ᵐ OracleComp spec') =
      PFunctor.FreeM.mapMHom fun x => liftM (impl x) := rfl

end OracleQuery

namespace OracleComp

/-- Given a `QueryImpl` of `spec` in terms of `n` we map any computation in
`OracleComp spec` to `n` by replacing queries with the corresponding implementation.
Taking `n` to be `PMF`, `Set`, etc. makes it possible to substitute each query for some denotation
like an output distribution and get the corresponding value for the entire computation.  -/
instance {spec : OracleSpec} {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    HasSimulateQ spec n (OracleComp spec) n where
  simulateQ impl := PFunctor.FreeM.mapMHom impl
  simulateQ_liftM impl q := by simp [PFunctor.FreeM.mapM]

variable {spec : OracleSpec} {n : Type u → Type v}
  [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)

lemma simulateQ_def (impl : QueryImpl spec n) :
    (simulateQ impl : OracleComp spec →ᵐ n) = PFunctor.FreeM.mapMHom impl := rfl

/-- Replacing queries with themselves has no effect. -/
@[simp] lemma simulateQ_ofLift_eq_self (mx : OracleComp spec α) :
    simulateQ (QueryImpl.ofLift spec (OracleComp spec)) mx = mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h]

end OracleComp

section OptionT

variable {spec : OracleSpec} {r m n : Type u → Type*}

/-- Apply `simulateQ` "underneath" an `OptionT` transformer. -/
instance t [Monad r] [Monad m] [MonadLiftT (OracleQuery spec) m]
    [Monad n] [LawfulMonad n] [MonadLiftT r n]
    [HasSimulateQ spec r m n] : HasSimulateQ spec r (OptionT m) (OptionT n) where
  simulateQ impl := by
    have : m →ᵐ n := simulateQ impl
    refine OptionT.mapM' ?_
    refine MonadHom.comp ?_ this
    refine MonadHom.ofLift n (OptionT n)
  simulateQ_liftM impl α q := by
    refine OptionT.ext ?_
    simp
    have : (liftM q : OptionT m α) = OptionT.lift (liftM q) := rfl
    simp [OptionT.mapM']
    simp [OptionT.run]
    rw [this]
    simp [OptionT.lift, OptionT.mk]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    rfl

end OptionT

section ErrorT


end ErrorT

section StateT


end StateT

section tests

example {spec₁ spec₂ : OracleSpec} (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₂))) :
    OptionT (OracleComp spec₂) α :=
  simulateQ impl₂ <|
    simulateQ impl₁ mx

example {spec₁ spec₂ spec₃ spec₄ : OracleSpec} (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₃)))
    (impl₃ : QueryImpl spec₃ (OptionT (OracleComp spec₄))) :
    OptionT (OptionT (OracleComp spec₄)) α :=
  simulateQ impl₃ <| simulateQ impl₂ <| simulateQ impl₁ mx

end tests

instance (priority := high) {spec : OracleSpec} :
    MonadLiftT (OracleComp []ₒ) (OracleComp spec) where
  monadLift mx :=
    let impl : QueryImpl []ₒ (OracleQuery spec) := fun t => PEmpty.elim t
    simulateQ impl mx
