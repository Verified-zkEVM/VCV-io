/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp
import ToMathlib.Control.StateT

/-!
# Simulation Semantics for Oracles in a Computation

This file defines a type `SimOracle spec specₜ σ` to represent a way to simulate
oracles in `spec` using the oracles in `specₜ`, maintaining some state of type `σ`.
We then define a function `simulate so oa s` to simulate the computation `oa`
using `so` to answer oracle queries, with initial state `s`.

We mark lemmas regarding simulating specific computations as `@[simp low]`,
so that lemmas specific to certain simulation oracles get applied firts.
For example `idOracle` has no effect upon simulation, and we should apply that fact first.
-/

open OracleSpec Prod

universe u v w

variable {ι ι' ιₜ : Type*} {spec : OracleSpec}
    {spec' : OracleSpec} {specₜ : OracleSpec}
    {m : Type u → Type v} {α β γ σ : Type u}

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulateQ` gives a method for applying a simulation oracle to a specific computation. -/
def QueryImpl (spec : OracleSpec) (m : Type u → Type v) :=
  (x : spec.domain) → m (spec.range x)

instance QueryImpl.Inhabited [spec.Inhabited] [Pure m] :
  Inhabited (QueryImpl spec m) := ⟨fun _ => pure default⟩

/-- Two query implementations are the same if they are the same on all query inputs. -/
@[ext] lemma QueryImpl.ext {so so' : QueryImpl spec m}
    (h : ∀ x : spec.domain, so x = so' x) : so = so' := funext h

namespace OracleComp

/-- Canonical lifting of a function `OracleQuery spec α → m α`
to a new function `OracleComp spec α` by preserving `bind`, `pure`, and `failure`.
NOTE: could change the output type to `OracleComp spec →ᵐ m`, makes some stuff below free -/
def simulateQ [Monad m] [LawfulMonad m] (so : QueryImpl spec m) :
    OracleComp spec →ᵐ m := PFunctor.FreeM.mapMHom so

lemma simulateQ_def [Monad m] [LawfulMonad m] (so : QueryImpl spec m) :
    simulateQ so = PFunctor.FreeM.mapMHom so := rfl

variable [Monad m] [LawfulMonad m] (so : QueryImpl spec m)

@[simp] lemma simulateQ_query (t : spec.domain) : simulateQ so (query t) = so t := by
  simp [simulateQ_def, query_eq_lift]

@[simp] lemma simulateQ_liftM (q : spec α) :
    simulateQ so (liftM q) = q.2 <$> so q.1 := by simp [simulateQ_def]

@[simp] lemma simulateQ_lift (q : spec α) :
    simulateQ so (PFunctor.FreeM.lift q) = q.2 <$> so q.1 := by simp [simulateQ_def]

@[simp] lemma simulateQ_liftA (t : spec.domain) :
    simulateQ so (PFunctor.FreeM.liftA t) = so t := by simp [simulateQ_def]

@[simp] lemma simulateQ_pure (x : α) : simulateQ so (pure x) = pure x := by
  simp [simulateQ_def]

@[simp] lemma simulateQ_query_bind (t : spec.domain) (ou : spec.range t → OracleComp spec β) :
    simulateQ so (query t >>= ou) = so t >>= fun u => simulateQ so (ou u) := by
  simp [simulateQ_def, query_eq_lift]

@[simp] lemma simulateQ_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    simulateQ so (oa >>= ob) = simulateQ so oa >>= fun u => simulateQ so (ob u) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa h => simp [h]

@[simp] lemma simulateQ_map (oa : OracleComp spec α) (f : α → β) :
    simulateQ so (f <$> oa) = f <$> simulateQ so oa := by simp [map_eq_bind_pure_comp]

@[simp] lemma simulateQ_seq (og : OracleComp spec (α → β)) (oa : OracleComp spec α) :
    simulateQ so (og <*> oa) = simulateQ so og <*> simulateQ so oa := by simp [seq_eq_bind]

@[simp] lemma simulateQ_seqLeft (oa : OracleComp spec α) (ob : OracleComp spec β) :
    simulateQ so (oa <* ob) = simulateQ so oa <* simulateQ so ob := by simp [seqLeft_eq]

@[simp] lemma simulateQ_seqRight (oa : OracleComp spec α) (ob : OracleComp spec β) :
    simulateQ so (oa *> ob) = simulateQ so oa *> simulateQ so ob := by simp [seqRight_eq]

@[simp] lemma simulateQ_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    simulateQ so (ite p oa oa') = ite p (simulateQ so oa) (simulateQ so oa') := by
  split_ifs <;> rfl

-- dtumad: I don't think this is true in general
-- @[simp] lemma simulateQ_orElse (oa oa' : OracleComp spec α) :
--     simulateQ so (oa <|> oa') = (simulateQ so oa <|> simulateQ so oa') := by
--   simp only [simulateQ, Option.getM]
--   simp [OracleComp.orElse_def, OptionT.run]

end OracleComp

open OracleComp

/-- Simulate a computation using the original oracles by "replacing" queries with queries.
This operates as an actual identity for `simulate'`, in that we get an exact equality
between the new and original computation.
This can be useful especially with `SimOracle.append`, in order to simulate a single oracle
in a larger set of oracles, leaving the behavior of other oracles unchanged.
The relevant spec can usually be inferred automatically, so we leave it implicit. -/
def idOracle : QueryImpl spec (OracleComp spec) := query

namespace idOracle

@[simp] lemma apply_eq (t : spec.domain) : idOracle t = query t := rfl

@[simp] lemma simulateQ_eq (oa : OracleComp spec α) :
    simulateQ idOracle oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t oa hoa => simp [hoa]

@[simp] lemma toFun_simulateQ_eq_id :
    (simulateQ idOracle).toFun = fun oa : OracleComp spec α => oa :=
  funext fun oa => by simp

end idOracle

/-- Simulate a computation by having each oracle return the default value of the query output type
for all queries. This gives a way to run arbitrary computations to get *some* output.
Mostly useful in some existence proofs, not usually used in an actual implementation. -/
def defaultOracle [spec.Inhabited] : QueryImpl spec Id := fun _ => default

-- namespace defaultOracle

-- @[simp] lemma apply_eq [spec.FiniteRange] (q : OracleQuery spec α) :
--     defaultOracle.impl q = return q.defaultOutput := rfl

-- @[simp] lemma simulateQ_eq_getM_defaultResult [spec.FiniteRange] :
--     @simulateQ ι spec _ α _ defaultOracle = Option.getM ∘ defaultResult := by
--   sorry
--   -- refine funext fun oa => by induction oa using OracleComp.inductionOn with
--   -- | pure x => simp [defaultResult, Option.getM]
--   -- | query_bind i t oa hoa => simp [hoa]; rfl

-- lemma simulateQ_eq [spec.FiniteRange] (oa : OracleComp spec α) :
--     simulateQ defaultOracle oa = oa.defaultResult.getM := by simp

-- end defaultOracle
