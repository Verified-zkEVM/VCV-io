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

/- `HasSimulateQ spec r m n` means that an implementation of `OracleQuery spec` in terms of
a computation in `r` results in a implementation of computations in `m` in terms of `n`.
This implementation is given by a bundled monad hom `simulateQ`. We also require that queries
can be lifted into `m`, and that `simulateQ` behaves naturally with this lift.

The standard example is `HasSimulateQ spec r (OracleComp spec) r` which takes an implementation of
queries to `spec` in `r` and recursively substitutes that implementation in an `OracleComp spec`
computation, to get a value in the new spec `r`.
For example taking `r` to be `PMF` lets you asign output distributions to queries and
get an output distribution for the whole computaiton. -/
-- class HasSimulateQ {ι} (spec : OracleSpec ι) (r : Type u → Type*)
--     (m : (Type u → Type v)) [Monad m] [MonadLiftT (OracleQuery spec) m]
--     (n : outParam (Type u → Type w)) [Monad n] [MonadLiftT r n] where
--   /-- The mapping from `m` to `n` induced by implementing `spec` in terms of `r`. -/
--   simulateQ (impl : QueryImpl spec r) {α : Type u} : m α → n α
--   /-- `simulateQ` respects the underyling `pure` operation. -/
--   simulateQ_pure (impl : QueryImpl spec r) {α : Type u} (x : α) :
--       simulateQ impl (pure x : m α) = (pure x : n α)
--   /-- `simulateQ` respects the underlying `bind` operation. -/
--   simulateQ_bind (impl : QueryImpl spec r) {α β : Type u} (mx : m α) (my : α → m β) :
--       simulateQ impl (mx >>= my) = simulateQ impl mx >>= fun x => simulateQ impl (my x)
--   /-- Simulating a query is the same as applying the implementation to the query input. -/
--   simulateQ_liftM (impl : QueryImpl spec r) {α : Type u} (q : OracleQuery spec α) :
--     (simulateQ impl) (liftM q : m α) = q.cont <$> liftM (impl q.input)

-- export HasSimulateQ (simulateQ simulateQ_pure simulateQ_bind simulateQ_liftM)

-- attribute [simp, grind =] simulateQ_liftM simulateQ_pure simulateQ_bind

section simulateQ

/-- Given an implementation of `spec` in the monad `r`, convert an `OracleComp spec α` to a
implementation in `r α` by substituting `impl t` for `query t` throughout. -/
def simulateQ {ι} {spec : OracleSpec ι} {r : Type u → Type _} [Monad r]
    (impl : QueryImpl spec r) {α : Type u} (mx : OracleComp spec α) : r α :=
  PFunctor.FreeM.mapM impl mx

variable {ι} {spec : OracleSpec ι} {r m n : Type u → Type*}
    [Monad r] (impl : QueryImpl spec r)

@[simp, grind =]
lemma simulateQ_pure (x : α) :
    simulateQ impl (pure x : OracleComp spec α) = pure x := rfl

@[simp, grind =]
lemma simulateQ_bind [LawfulMonad r] (mx : OracleComp spec α) (my : α → OracleComp spec β) :
    simulateQ impl (mx >>= my) = simulateQ impl mx >>= fun x => simulateQ impl (my x) := by
  simp [simulateQ]

/-- Version of `simulateQ` that bundles into a monad hom. -/
@[reducible]
def simulateQ' [LawfulMonad r] (impl : QueryImpl spec r) : OracleComp spec →ᵐ r where
  toFun {_α} mx := simulateQ impl mx
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

@[simp, grind =]
lemma simulateQ_query [LawfulMonad r] (q : OracleQuery spec α) :
    simulateQ impl (liftM q) = q.cont <$> (impl q.input) := by
  simp [simulateQ, PFunctor.FreeM.mapM.eq_def]

@[simp]
lemma simulateQ_query_bind [LawfulMonad r] (q : OracleQuery spec α)
    (ou : α → OracleComp spec β) : simulateQ impl (liftM q >>= ou) =
      liftM (impl q.input) >>= fun u => simulateQ impl (ou (q.cont u)) := by aesop

@[simp, grind =]
lemma simulateQ_map [LawfulMonad r] (mx : OracleComp spec α) (f : α → β) :
    simulateQ impl (f <$> mx) = f <$> simulateQ impl mx := by
  simp [map_eq_bind_pure_comp]

@[simp]
lemma simulateQ_seq [LawfulMonad r] (og : OracleComp spec (α → β)) (mx : OracleComp spec α) :
    simulateQ impl (og <*> mx) = simulateQ impl og <*> simulateQ impl mx := by
  simp [seq_eq_bind_map]

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

end simulateQ

-- namespace OracleQuery

-- variable {ι} {ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

-- /-- Given a map from queries in `spec` to queries in `spec'`, lift to a map on `OracleComp`
-- by substituting each query for the new implementation in `spec'`. -/
-- instance {ι} {ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'} :
--     HasSimulateQ spec (OracleQuery spec') (OracleComp spec) (OracleComp spec') where
--   simulateQ impl α mx := PFunctor.FreeM.mapM (QueryImpl.liftTarget _ impl) mx
--   simulateQ_pure _ _ _ := by simp
--   simulateQ_bind _ _ _ _ := by simp
--   simulateQ_liftM _ _ _ := rfl

-- @[grind =]
-- lemma simulateQ_def (impl : QueryImpl spec (OracleQuery spec'))
--     (mx : OracleComp spec α) : (simulateQ impl mx) =
--     PFunctor.FreeM.mapMHom (fun x => liftM (impl x)) mx := rfl

-- /-- `QueryImpl.id` is an identity for `simulateQ` with implementaiton in `OracleQuery spec`. -/
-- @[simp] lemma simulateQ_id (mx : OracleComp spec α) :
--     simulateQ (QueryImpl.id spec) mx = mx := by
--   induction mx using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind t mx h => simp [h]

-- /-- Lifting queries to their original implementation has no effect on a computation. -/
-- lemma simulateQ_ofLift_eq_self {α} (mx : OracleComp spec α) :
--     simulateQ (QueryImpl.ofLift spec (OracleQuery spec)) mx = mx := by simp

-- end OracleQuery

-- namespace OracleComp

-- /-- Given a `QueryImpl` of `spec` in terms of `n` we map any computation in
-- `OracleComp spec` to `n` by replacing queries with the corresponding implementation.
-- Taking `n` to be `PMF`, `Set`, etc. makes it possible to substitute each query for some denotation
-- like an output distribution and get the corresponding value for the entire computation.  -/
-- instance {ι} {spec : OracleSpec ι} {n : Type u → Type w} [Monad n] [LawfulMonad n] :
--     HasSimulateQ spec n (OracleComp spec) n where
--   simulateQ impl {α} mx := PFunctor.FreeM.mapM impl mx
--   simulateQ_pure _ _ := by simp
--   simulateQ_bind _ _ _ := by simp
--   simulateQ_liftM _ _ := by simp [PFunctor.FreeM.mapM]

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

-- end OracleComp

-- section OptionT

-- variable {ι} {spec : OracleSpec ι} {r m n : Type u → Type*}

-- /-- Apply `simulateQ` "underneath" an `OptionT` transformer. -/
-- instance [Monad m] [MonadLiftT (OracleQuery spec) m]
--     [Monad n] [LawfulMonad n] [MonadLiftT r n]
--     [HasSimulateQ spec r m n] : HasSimulateQ spec r (OptionT m) (OptionT n) where
--   simulateQ impl α mx := OptionT.mk (simulateQ impl (OptionT.run mx))
--   simulateQ_pure := sorry
--   simulateQ_bind := sorry
--     -- have : m →ᵐ n := simulateQ impl
--     -- refine OptionT.mapM' ?_
--     -- refine MonadHom.comp ?_ this
--     -- refine MonadHom.ofLift n (OptionT n)
--   simulateQ_liftM impl α q := by
--     stop
--     refine OptionT.ext ?_
--     simp
--     have : (liftM q : OptionT m α) = OptionT.lift (liftM q) := rfl
--     simp [OptionT.mapM']
--     simp [OptionT.run]
--     rw [this]
--     simp [OptionT.lift, OptionT.mk]
--     simp only [map_eq_bind_pure_comp, Function.comp_def]
--     rfl

-- -- lemma simulateQ_def

-- @[simp, grind =]
-- lemma simulateQ_id' (mx : OptionT (OracleComp spec) α) :
--     simulateQ (QueryImpl.id' spec) mx = mx := by

--   sorry

-- end OptionT

-- section ErrorT

-- -- TODO

-- end ErrorT

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

-- handled by sub-spec stuff
-- /-- A computation with no oracles naturally lifts to one with any number of oracles. -/
-- instance (priority := high) {ι} {spec : OracleSpec ι} :
--     MonadLiftT (OracleComp []ₒ) (OracleComp spec) where
--   monadLift mx :=
--     let impl : QueryImpl []ₒ (OracleQuery spec) := fun t => PEmpty.elim t
--     simulateQ impl mx
