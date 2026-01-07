/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.QueryImpl
import ToMathlib.Control.OptionT

/-!
# Simulation Semantics for Oracles in a Computation

-/

open OracleComp Prod

universe u v w

variable {α β γ : Type u}

-- class HasSimulateQuery {ι} (spec : OracleSpec ι) (r : Type u → Type _)
--     (m : outParam (Type u → Type v)) [Monad m] [MonadLiftT (OracleQuery spec) m]
--     (n : outParam (Type u → Type w)) [Monad n] [MonadLiftT r n] where
--   simulateQ (impl : QueryImpl spec r) {α : Type u}

/-- `HasSimulateQ spec r m n` means that an implementation of `OracleQuery spec` in terms of
a computation in `r` results in a implementation of computations in `m` in terms of `n`.
This implementation is given by a bundled monad hom `simulateQ`. We also require that queries
can be lifted into `m`, and that `simulateQ` behaves naturally with this lift.

The standard example is `HasSimulateQ spec r (OracleComp spec) r` which takes an implementation of
queries to `spec` in `r` and recursively substitutes that implementation in an `OracleComp spec`
computation, to get a value in the new spec `r`.
For example taking `r` to be `PMF` lets you asign output distributions to queries and
get an output distribution for the whole computaiton. -/
class HasSimulateQ {ι} (spec : OracleSpec ι) (r : Type u → Type*)
    (m : outParam (Type u → Type v)) [Monad m] [MonadLiftT (OracleQuery spec) m]
    (n : outParam (Type u → Type w)) [Monad n] [MonadLiftT r n] where
  /-- The mapping from `m` to `n` induced by implementing `spec` in terms of `r`. -/
  simulateQ (impl : QueryImpl spec r) : m →ᵐ n
  /-- Simulating a query is the same as applying the implementation to the query input. -/
  simulateQ_liftM (impl : QueryImpl spec r) {α : Type u} (q : OracleQuery spec α) :
    (simulateQ impl) (liftM q : m α) = q.cont <$> liftM (impl q.input)

export HasSimulateQ (simulateQ simulateQ_liftM)

attribute [simp] simulateQ_liftM

section simulateQ

variable {ι} {spec : OracleSpec ι} {r m n : Type u → Type*}
    [Monad m] [MonadLiftT (OracleQuery spec) m] [Monad n]
    [MonadLiftT r n] [HasSimulateQ spec r m n] (impl : QueryImpl spec r)

@[simp] lemma simulateQ_query [LawfulMonad n] (t : spec.Domain) :
    simulateQ impl (query t : m (spec.Range t)) = liftM (impl t) := by
  simp [query_def, HasSimulateQ.simulateQ_liftM (m := m)]

@[simp] lemma simulateQ_query_bind [LawfulMonad n] (t : spec.Domain) (ou : spec.Range t → m β) :
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

@[simp] lemma simulateQ_ite (p : Prop) [Decidable p] (mx mx' : m α) :
    simulateQ impl (ite p mx mx') = ite p (simulateQ impl mx) (simulateQ impl mx') := by
  split_ifs <;> rfl

end simulateQ

namespace OracleQuery

variable {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

/-- Given a map from queries in `spec` to queries in `spec'`, lift to a map on `OracleComp`
by substituting each query for the new implementation in `spec'`. -/
instance {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'} :
    HasSimulateQ spec (OracleQuery spec') (OracleComp spec) (OracleComp spec') where
  simulateQ impl := PFunctor.FreeM.mapMHom fun x => PFunctor.FreeM.lift (impl x)
  simulateQ_liftM _ _ _ := rfl

lemma simulateQ_def (impl : QueryImpl spec (OracleQuery spec')) :
    (simulateQ impl : OracleComp spec →ᵐ OracleComp spec') =
      PFunctor.FreeM.mapMHom fun x => liftM (impl x) := rfl

/-- `QueryImpl.id` is an identity for `simulateQ` with implementaiton in `OracleQuery spec`. -/
@[simp] lemma simulateQ_id (mx : OracleComp spec α) :
    simulateQ (QueryImpl.id spec) mx = mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h]

/-- Lifting queries to their original implementation has no effect on a computation. -/
lemma simulateQ_ofLift_eq_self {α} (mx : OracleComp spec α) :
    simulateQ (QueryImpl.ofLift spec (OracleQuery spec)) mx = mx := by simp

end OracleQuery

namespace OracleComp

/-- Given a `QueryImpl` of `spec` in terms of `n` we map any computation in
`OracleComp spec` to `n` by replacing queries with the corresponding implementation.
Taking `n` to be `PMF`, `Set`, etc. makes it possible to substitute each query for some denotation
like an output distribution and get the corresponding value for the entire computation.  -/
instance {ι} {spec : OracleSpec ι} {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    HasSimulateQ spec n (OracleComp spec) n where
  simulateQ impl := PFunctor.FreeM.mapMHom impl
  simulateQ_liftM impl q := by simp [PFunctor.FreeM.mapM]; intro q'; rfl

variable {ι} {spec : OracleSpec ι} {n : Type u → Type v}
  [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)

lemma simulateQ_def (impl : QueryImpl spec n) :
    (simulateQ impl : OracleComp spec →ᵐ n) = PFunctor.FreeM.mapMHom impl := rfl

/-- `QueryImpl.id'` is an identity for `simulateQ` with implementaiton in `OracleComp spec`. -/
@[simp] lemma simulateQ_id' (mx : OracleComp spec α) :
    simulateQ (QueryImpl.id' spec) mx = mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h]

/-- Lifting queries to their original implementation has no effect on a computation. -/
lemma simulateQ_ofLift_eq_self {α} (mx : OracleComp spec α) :
    simulateQ (QueryImpl.ofLift spec (OracleComp spec)) mx = mx := by simp

end OracleComp

section OptionT

variable {ι} {spec : OracleSpec ι} {r m n : Type u → Type*}

/-- Apply `simulateQ` "underneath" an `OptionT` transformer. -/
instance [Monad r] [Monad m] [MonadLiftT (OracleQuery spec) m]
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

-- TODO

end ErrorT

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

end tests

-- handled by sub-spec stuff
-- /-- A computation with no oracles naturally lifts to one with any number of oracles. -/
-- instance (priority := high) {ι} {spec : OracleSpec ι} :
--     MonadLiftT (OracleComp []ₒ) (OracleComp spec) where
--   monadLift mx :=
--     let impl : QueryImpl []ₒ (OracleQuery spec) := fun t => PEmpty.elim t
--     simulateQ impl mx
