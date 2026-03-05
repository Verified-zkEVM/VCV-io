/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.EvalDist
import ToMathlib.General

/-!
# Coercions Between Computations With Additional Oracles

This file defines a `isSubSpec` relation for pairs of `oracleSpec` where one can be
thought of as an extension of the other with additional oracles.
The definition consists is a thin wrapper around a `MonadLift` instance on `OracleQuery`,
which extends to a lifting operation on `OracleComp`.

We use the notation `spec ⊂ₒ spec'` to represent that one set of oracles is a subset of another,
where the non-inclusive subset symbol reflects that the relation is not defined
to be reflexive by default (a reflexive instance is provided separately).
-/

open OracleSpec OracleComp BigOperators ENNReal

universe u u' v v' w w'

variable {ι : Type u} {τ : Type v}
  {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α β γ : Type w}

namespace OracleSpec

/-- Relation defining an inclusion of one set of oracles into another, where the mapping
doesn't affect the underlying probability distribution of the computation.
Informally, `spec ⊂ₒ superSpec` means that for any query to an oracle of `sub_spec`,
it can be perfectly simulated by a computation using the oracles of `superSpec`.

We avoid implementing this via the built-in subset notation as we care about the actual data
of the mapping rather than just its existence, which is needed when defining type coercions. -/
class SubSpec (spec : OracleSpec.{u,w} ι) (superSpec : OracleSpec.{v,w} τ)
    extends MonadLift (OracleQuery spec) (OracleQuery superSpec) where
  liftM_map {α β : Type _} (q : OracleQuery spec α) (f : α → β) :
      liftM (n := OracleQuery superSpec) (f <$> q) = f <$> liftM q

infix : 50 " ⊂ₒ " => SubSpec

namespace SubSpec

variable {κ : Type w'} {spec₃ : OracleSpec κ}

/-- Transitivity for `SubSpec`: if `spec₁ ⊂ₒ spec₂` and `spec₂ ⊂ₒ spec₃`,
then `spec₁ ⊂ₒ spec₃`. -/
def trans (h₁ : spec ⊂ₒ superSpec) (h₂ : superSpec ⊂ₒ spec₃) : spec ⊂ₒ spec₃ where
  monadLift q := h₂.monadLift (h₁.monadLift q)
  liftM_map q f := by
    have h₁map := h₁.liftM_map (q := q) (f := f)
    have h₁map' := congrArg h₂.monadLift h₁map
    calc
      h₂.monadLift (h₁.monadLift (f <$> q))
          = h₂.monadLift (f <$> h₁.monadLift q) := h₁map'
      _ = f <$> h₂.monadLift (h₁.monadLift q) := by
          simpa using (h₂.liftM_map (q := h₁.monadLift q) (f := f))

end SubSpec

/-- `LawfulSubSpec` extends `SubSpec` with the requirement that lifting preserves
distributions. The axiom requires that the continuation of each lifted query is a
bijection from the super-range to the sub-range, which guarantees that the uniform
distribution is preserved under the mapping. -/
class LawfulSubSpec (spec : OracleSpec.{u,w} ι) (superSpec : OracleSpec.{v,w} τ)
    [h : SubSpec spec superSpec] : Prop where
  cont_bijective (t : spec.Domain) :
    Function.Bijective (h.toMonadLift.monadLift (query (spec := spec) t)).snd

namespace LawfulSubSpec

variable {ι : Type u} {τ : Type v} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [h : spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec]

lemma evalDist_liftM_query [superSpec.Fintype] [superSpec.Inhabited]
    [spec.Fintype] [spec.Inhabited] (t : spec.Domain) :
    (PMF.uniformOfFintype (superSpec.Range
      (h.toMonadLift.monadLift (query (spec := spec) t)).fst)).map
      (h.toMonadLift.monadLift (query (spec := spec) t)).snd =
      PMF.uniformOfFintype (spec.Range t) :=
  PMF.uniformOfFintype_map_of_bijective _ (cont_bijective t)

end LawfulSubSpec

end OracleSpec


namespace OracleComp

section liftComp

/-- Lift a computation from `spec` to `superSpec` using a `SubSpec` instance on queries.
Usually `liftM` should be preferred but this can allow more explicit annotation. -/
def liftComp (mx : OracleComp spec α) (superSpec : OracleSpec τ)
      [h : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] :
      OracleComp superSpec α :=
    simulateQ (fun t => liftM (query (spec := spec) t)) mx

variable (superSpec : OracleSpec τ)
    [h : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]

@[grind =, aesop unsafe norm]
lemma liftComp_def (mx : OracleComp spec α) : liftComp mx superSpec =
    simulateQ (fun t => liftM (query (spec := spec) t)) mx := rfl

@[simp]
lemma liftComp_pure (x : α) : liftComp (pure x : OracleComp spec α) superSpec = pure x := rfl

@[simp]
lemma liftComp_query (q : OracleQuery spec α) :
    liftComp (q : OracleComp spec _) superSpec =
      q.cont <$> (liftM (query (spec := spec) q.input) : OracleComp superSpec _) := by
  simp [liftComp]

@[simp]
lemma liftComp_bind (mx : OracleComp spec α) (ob : α → OracleComp spec β) :
    liftComp (mx >>= ob) superSpec =
      liftComp mx superSpec >>= λ x ↦ liftComp (ob x) superSpec := by
  grind

@[simp]
lemma liftComp_map (mx : OracleComp spec α) (f : α → β) :
    liftComp (f <$> mx) superSpec = f <$> liftComp mx superSpec := by
  simp [liftComp]

@[simp]
lemma liftComp_seq (og : OracleComp spec (α → β)) (mx : OracleComp spec α) :
    liftComp (og <*> mx) superSpec = liftComp og superSpec <*> liftComp mx superSpec := by
  simp [liftComp, seq_eq_bind_map]

-- NOTE: `liftComp_failure` cannot be stated for `OracleComp spec` because `failure` only exists
-- in `OptionT (OracleComp spec)`, not in `OracleComp spec` itself. `OracleComp` is
-- `PFunctor.FreeM` which has no `Alternative` instance. Use `liftM_failure` in the OptionT
-- section below for the analogous result.

end liftComp

section liftComp_evalDist

variable {ι : Type u} {τ : Type v}
  {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α : Type w}
variable [spec.Fintype] [spec.Inhabited] [superSpec.Fintype] [superSpec.Inhabited]
    [h : spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec]

@[simp] lemma evalDist_liftComp (mx : OracleComp spec α) :
    evalDist (liftComp mx superSpec) = evalDist mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query]
    rw [evalDist_bind, evalDist_bind]; simp_rw [ih]
    congr 1
    simp only [evalDist_eq_simulateQ (spec := superSpec), evalDist_eq_simulateQ (spec := spec),
      simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    congr 1
    simp only [simulateQ, PFunctor.FreeM.mapM.eq_def, bind_pure_comp, PMF.monad_map_eq_map]
    exact PMF.uniformOfFintype_map_of_bijective _
      (LawfulSubSpec.cont_bijective (spec := spec) (superSpec := superSpec) t)

@[simp] lemma probOutput_liftComp (mx : OracleComp spec α) (x : α) :
    Pr[= x | liftComp mx superSpec] = Pr[= x | mx] :=
  congrFun (congrArg DFunLike.coe (evalDist_liftComp mx)) x

@[simp] lemma probEvent_liftComp (mx : OracleComp spec α) (p : α → Prop) :
    Pr[p | liftComp mx superSpec] = Pr[p | mx] := by
  simp only [probEvent_eq_tsum_indicator]
  congr 1; funext x
  simp only [probOutput_liftComp]

end liftComp_evalDist

/-- Extend a lifting on `OracleQuery` to a lifting on `OracleComp`. -/
instance [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLiftT (OracleComp spec) (OracleComp superSpec) where
  monadLift mx := liftComp mx superSpec

/-- We choose to actively rewrite `liftComp` as `liftM` to enable `LawfulMonadLift` lemmas. -/
@[simp, aesop safe norm]
lemma liftComp_eq_liftM [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : OracleComp spec α) : liftComp mx superSpec = (liftM mx : OracleComp superSpec α) := rfl

instance [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] :
    LawfulMonadLiftT (OracleComp spec) (OracleComp superSpec) where
  monadLift_pure x := liftComp_pure superSpec x
  monadLift_bind mx my := liftComp_bind superSpec mx my

-- NOTE: With constant universal levels it is fairly easy to abstract the below in a class
-- Getting a similar level of generality as the manual instances below would be useful,
--    might require some more general framework about monad transformers.

section OptionT

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (OptionT (OracleComp spec)) (OptionT (OracleComp superSpec)) where
  monadLift mx := OptionT.mk (simulateQ (fun t => liftM (query t)) (OptionT.run mx))

@[simp]
lemma liftM_OptionT_eq [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : OptionT (OracleComp spec) α) : (liftM mx : OptionT (OracleComp superSpec) α) =
      let impl : QueryImpl spec (OracleComp superSpec) := fun t => liftM (query t)
      simulateQ impl mx := rfl

@[simp]
lemma liftM_failure [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    (liftM (failure : OptionT (OracleComp spec) α) : OptionT (OracleComp superSpec) α) = failure := by
  rw [OracleComp.failure_def, liftM_OptionT_eq, OptionT.fail]
  simp only [OptionT.mk, simulateQ_pure]
  rfl

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    LawfulMonadLift (OptionT (OracleComp spec)) (OptionT (OracleComp superSpec)) where
  monadLift_pure _ := by
    simp [MonadLift.monadLift]
    rfl
  monadLift_bind mx my := by
    apply OptionT.ext
    simp [MonadLift.monadLift, OptionT.run_bind, Option.elimM, simulateQ_bind]
    refine bind_congr ?_
    intro x
    cases x <;> simp

end OptionT

section StateT

instance {σ : Type _} [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (StateT σ (OracleComp spec)) (StateT σ (OracleComp superSpec)) where
  monadLift mx := StateT.mk fun s => liftComp (StateT.run mx s) superSpec

@[simp]
lemma liftM_StateT_eq {σ : Type _} [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : StateT σ (OracleComp spec) α) : (liftM mx : StateT σ (OracleComp superSpec) α) =
      StateT.mk fun s => liftM (StateT.run mx s) := by rfl

end StateT

end OracleComp
