/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.ProbComp

/-!
# Coercions Between Computations With Additional Oracles

This file defines a `isSubSpec` relation for pairs of `oracleSpec` where one can be
thought of as an extension of the other with additional oracles.
The definition consists is a thin wrapper around a `MonadLift` instance on `OracleQuery`,
which extends to a lifting operation on `OracleComp`.

We use the notation `spec ⊂ₒ spec'` to represent that one set of oracles is a subset of another,
where the non-inclusive subset symbol reflects that we avoid defining this instance reflexively.
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

-- TODO: the following SubSpec convenience lemmas were removed during remediation.
-- They restate generic query lemmas for the SubSpec monad lift. Restore when SubSpec API stabilises.

-- @[simp] lemma support_toFun (q : OracleQuery spec α) :
--     support (h.monadLift q : OracleComp superSpec α) = Set.univ := by
--   rw [support_query]

-- @[simp] lemma probOutput_toFun [superSpec.FiniteRange] [Fintype α]
--     (q : OracleQuery spec α) (u : α) :
--     [= u | (h.monadLift q : OracleComp superSpec α)] =
--       (↑(Fintype.card α) : ℝ≥0∞)⁻¹ := by
--   rw [probOutput_liftM]

-- @[simp] lemma probEvent_toFun [superSpec.FiniteRange] [Fintype α]
--     (q : OracleQuery spec α) (p : α → Prop) [DecidablePred p] :
--     [p | (h.monadLift q : OracleComp superSpec α)] =
--       (Finset.univ.filter p).card / Fintype.card α := by
--   rw [probEvent_liftM_eq_div]

-- /-- The empty set of oracles is a subspec of any other oracle set.
-- We require `ι` to be inhabited to prevent the reflexive case. -/
-- instance [Inhabited ι] : []ₒ ⊂ₒ spec where
--   monadLift | query i _ => i.elim

end SubSpec

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

-- TODO: the following liftComp lemmas were removed during remediation.
-- They show that `liftComp` preserves distributions and related properties.
-- Needed by `CryptoFoundations/Fork.lean`. Restore when `evalDist_liftComp` is proved.

-- @[simp] lemma liftComp_failure :
--     liftComp (failure : OracleComp spec α) superSpec = failure := rfl

-- /-- Lifting a computation to a different set of oracles doesn't change the output distribution,
-- since `evalDist` assumes uniformly random queries. -/
-- @[simp] lemma evalDist_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
--     (mx : OracleComp spec α) : evalDist (liftComp mx superSpec) = evalDist mx := by
--   sorry

-- @[simp] lemma support_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
--     (mx : OracleComp spec α) : (liftComp mx superSpec).support = mx.support := by
--   sorry

-- @[simp] lemma finSupport_liftComp [spec.DecidableEq] [superSpec.DecidableEq] [DecidableEq α]
--     [spec.FiniteRange] [superSpec.FiniteRange]
--     (mx : OracleComp spec α) : (liftComp mx superSpec).finSupport = mx.finSupport := by
--   sorry

-- @[simp] lemma probOutput_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
--     (mx : OracleComp spec α) (x : α) : [= x | liftComp mx superSpec] = [= x | mx] := by
--   sorry

-- @[simp] lemma probEvent_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
--     (mx : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
--     [p | liftComp mx superSpec] = [p | mx] := by
--   sorry

-- @[simp] lemma NeverFail_lift_comp_iff (mx : OracleComp spec α) :
--     (liftComp mx superSpec).NeverFail ↔ mx.NeverFail := by
--   sorry

end liftComp

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
