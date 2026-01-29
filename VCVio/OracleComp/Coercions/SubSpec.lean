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

infix : 50 " ⊂ₒ " => SubSpec

namespace SubSpec

variable [h : MonadLift (OracleQuery spec) (OracleQuery superSpec)]

-- -- TODO: this may be a good simp lemma for normalization in general?
-- -- Guessing the rhs is almost always easier to prove things about
-- @[simp] lemma liftM_query_eq_liftM_liftM (q : spec α) :
--     (q : superSpec α) = ((q : superSpec α) : OracleComp superSpec α) := rfl

-- TODO: Nameing
-- lemma evalDist_lift_query [superSpec.Fintype] [superSpec.Inhabited]
--     [Fintype α] [Nonempty α]
--     (q : OracleQuery spec α) :
--     evalDist ((q : OracleQuery superSpec α) : OracleComp superSpec α) =
--       OptionT.lift (PMF.uniformOfFintype α) := by
--   sorry

-- @[simp] lemma evalDist_liftM [superSpec.Fintype] [Fintype α] [Nonempty α]
--     (q : OracleQuery spec α) :
--     evalDist (q : OracleComp superSpec α) =
--       OptionT.lift (PMF.uniformOfFintype α) := by
--   rw [liftM_query_eq_liftM_liftM, OracleComp.evalDist_liftM]

-- @[simp] lemma supportWhen_monadLift (q : OracleQuery spec α)
--     (poss : {α : Type w} → OracleQuery superSpec α → Set α) :
--     supportWhen (q : OracleComp superSpec α) poss = poss q := by
--   rw [liftM_query_eq_liftM_liftM]
--   simp only [supportWhen_query]

-- @[simp]
-- lemma support_toFun (q : OracleQuery spec α) :
--     support (h.monadLift q : OracleComp superSpec α) = Set.univ := by
--   rw [support_query]

-- @[simp]
-- lemma finSupport_toFun [spec.DecidableEq] [superSpec.DecidableEq] [superSpec.FiniteRange]
--     [DecidableEq α] [Fintype α] (q : OracleQuery spec α) :
--     finSupport (h.monadLift q : OracleComp superSpec α) = Finset.univ := by
--   sorry

-- @[simp]
-- lemma probOutput_toFun [superSpec.FiniteRange] [Fintype α]
--     (q : OracleQuery spec α) (u : α) :
--     [= u | (h.monadLift q : OracleComp superSpec α)] =
--       (↑(Fintype.card α) : ℝ≥0∞)⁻¹ := by
--   rw [probOutput_liftM]

-- @[simp]
-- lemma probEvent_toFun [superSpec.FiniteRange] [Fintype α]
--     (q : OracleQuery spec α) (p : α → Prop) [DecidablePred p] :
--     [p | (h.monadLift q : OracleComp superSpec α)] =
--       (Finset.univ.filter p).card / Fintype.card α := by
--   rw [probEvent_liftM_eq_div]

-- /-- The empty set of oracles is a subspec of any other oracle set.
-- We require `ι` to be inhabited to prevent the reflexive case.  -/
-- instance [Inhabited ι] : []ₒ ⊂ₒ spec where
--   monadLift | query i _ => i.elim

end SubSpec

end OracleSpec


namespace OracleComp

section liftComp

/-- Lift a computation from `spec` to `superSpec` using a `SubSpec` instance on queries.
Usually `liftM` should be preferred but this can allow more explicit annotation. -/
def liftComp (mx : OracleComp spec α) (superSpec : OracleSpec τ)
      [h : MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
      OracleComp superSpec α :=
    simulateQ (r := OracleQuery superSpec) (fun t => liftM (query (spec := spec) t)) mx

variable (superSpec : OracleSpec τ) [h : MonadLift (OracleQuery spec) (OracleQuery superSpec)]

@[grind =, aesop unsafe norm]
lemma liftComp_def (mx : OracleComp spec α) : liftComp mx superSpec =
    simulateQ (r := OracleQuery superSpec) (fun t => liftM (query (spec := spec) t)) mx := rfl

@[simp]
lemma liftComp_pure (x : α) : liftComp (pure x : OracleComp spec α) superSpec = pure x := rfl

@[simp]
lemma liftComp_query (q : OracleQuery spec α) :
    liftComp (q : OracleComp spec _) superSpec = liftM q := by
  sorry

@[simp]
lemma liftComp_bind (mx : OracleComp spec α) (ob : α → OracleComp spec β) :
    liftComp (mx >>= ob) superSpec =
      liftComp mx superSpec >>= λ x ↦ liftComp (ob x) superSpec := by
  grind

-- @[simp]
-- lemma liftComp_failure : liftComp (failure : OracleComp spec α) superSpec = failure := rfl

@[simp]
lemma liftComp_map (mx : OracleComp spec α) (f : α → β) :
    liftComp (f <$> mx) superSpec = f <$> liftComp mx superSpec := by
  simp [liftComp]

@[simp]
lemma liftComp_seq (og : OracleComp spec (α → β)) (mx : OracleComp spec α) :
    liftComp (og <*> mx) superSpec = liftComp og superSpec <*> liftComp mx superSpec := by
  simp [liftComp, seq_eq_bind, Function.comp_def]

-- /-- Lifting a computation to a different set of oracles doesn't change the output distribution,
-- since `evalDist` assumes uniformly random queries. -/
-- @[simp]
-- lemma evalDist_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
--     (mx : OracleComp spec α) : evalDist (liftComp mx superSpec) = evalDist mx := by
--   induction mx using OracleComp.inductionOn with
--   | pure x => simp [liftComp_pure]
--   | query_bind i t mx hmx =>
--       simp only [liftComp, simulateQ_bind, simulateQ_query, StateT.run'_eq, StateT.run_bind,
--         StateT.run_monadLift, SubSpec.liftM_query_eq_liftM_liftM, bind_pure_comp,
--         Function.comp_apply, bind_map_left, map_bind, evalDist_bind, OracleComp.evalDist_liftM]
--       refine congr_arg (_ >>= ·) (funext λ u ↦ ?_)
--       simpa [StateT.run, liftComp] using hmx u
--   | failure => simp

-- @[simp] -- NOTE: shouldn't actually need finiteness here.
-- lemma support_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
--     (mx : OracleComp spec α) : (liftComp mx superSpec).support = mx.support :=
--   Set.ext (mem_support_iff_of_evalDist_eq <| evalDist_liftComp _ mx)

-- @[simp]
-- lemma finSupport_liftComp [spec.DecidableEq] [superSpec.DecidableEq] [DecidableEq α]
--     [spec.FiniteRange] [superSpec.FiniteRange]
--     (mx : OracleComp spec α) : (liftComp mx superSpec).finSupport = mx.finSupport :=
--   Finset.ext (mem_finSupport_iff_of_evalDist_eq <| evalDist_liftComp _ mx)

-- @[simp]
-- lemma probOutput_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
--     (mx : OracleComp spec α) (x : α) : [= x | liftComp mx superSpec] = [= x | mx] := by
--   simp only [probOutput_def, evalDist_liftComp]

-- @[simp]
-- lemma probEvent_liftComp [spec.FiniteRange] [superSpec.FiniteRange]
--     (mx : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
--     [p | liftComp mx superSpec] = [p | mx] := by
--   simp only [probEvent_def, evalDist_liftComp]

-- @[simp] lemma NeverFail_lift_comp_iff (mx : OracleComp spec α) :
--     (liftComp mx superSpec).NeverFail ↔ mx.NeverFail := by
--   simp [liftComp]
--   sorry

end liftComp

/-- Extend a lifting on `OracleQuery` to a lifting on `OracleComp`. -/
instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (OracleComp spec) (OracleComp superSpec) where
  monadLift mx := liftComp mx superSpec

/-- We choose to actively rewrite `liftComp` as `liftM` to enable `LawfulMonadLift` lemmas. -/
@[simp, aesop safe norm]
lemma liftComp_eq_liftM [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : OracleComp spec α) : liftComp mx superSpec = (liftM mx : OracleComp superSpec α) := rfl

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    LawfulMonadLift (OracleComp spec) (OracleComp superSpec) where
  monadLift_pure x := liftComp_pure superSpec x
  monadLift_bind mx my := liftComp_bind superSpec mx my

-- NOTE: With constant universal levels it is fairly easy to abstract the below in a class
-- Getting a similar level of generality as the manual instances below would be useful,
--    might require some more general framework about monad transformers.

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (OptionT (OracleComp spec)) (OptionT (OracleComp superSpec)) where
  monadLift mx := by
    let impl : QueryImpl spec (OracleQuery superSpec) := fun t => liftM (query t)
    let := simulateQ (m := OptionT (OracleComp spec)) impl mx
    exact this
    -- OptionT.mk (liftComp mx.run superSpec)

@[simp]
lemma liftM_OptionT_eq [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : OptionT (OracleComp spec) α) : (liftM mx : OptionT (OracleComp superSpec) α) =
      let impl : QueryImpl spec (OracleQuery superSpec) := fun t => liftM (query t)
      simulateQ impl mx := rfl

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    LawfulMonadLift (OptionT (OracleComp spec)) (OptionT (OracleComp superSpec)) where
  monadLift_pure _ := by simp [MonadLift.monadLift]
  monadLift_bind mx my := by simp [MonadLift.monadLift]

instance {σ : Type _} [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (StateT σ (OracleComp spec)) (StateT σ (OracleComp superSpec)) where
  monadLift mx := StateT.mk fun s => liftComp (StateT.run mx s) superSpec

@[simp]
lemma liftM_StateT_eq {σ : Type _} [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : StateT σ (OracleComp spec) α) : (liftM mx : StateT σ (OracleComp superSpec) α) =
      StateT.mk fun s => liftM (StateT.run mx s) := by rfl

end OracleComp
