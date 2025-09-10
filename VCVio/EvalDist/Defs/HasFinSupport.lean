/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, František Silváši
-/
import VCVio.EvalDist.Defs.HasEvalDist
import VCVio.OracleComp.OracleComp

/-!
# Finite Distribution Semantics for Monadic Computation

This file defines a typeclass `HasFinSupport` extending the base class
with the fact that the support is finite.

While this could just extend `HasSupport`, this leads to diamond issues,
and we generally only use it to simplify `probOutput` type calculations by
reducing to finite sums, so generally isn't really needed.

-/

open ENNReal

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

/-- Strengthening of HasSupport that equips each computation with a finite witness of its support. -/
class HasFinSupport (m : Type u → Type v) [Monad m]
    extends HasSupport m where
  finSupport {α : Type u} (mx : m α) : Finset α
  mem_finSupport_iff {α : Type u} (mx : m α) (x : α) :
    x ∈ finSupport mx ↔ x ∈ support mx

export HasFinSupport (finSupport mem_finSupport_iff)
attribute [simp] mem_finSupport_iff

variable {spec : OracleSpec}

-- /-- The support of a computation is finite if oracles have finite ranges. -/
-- instance supportWhen_finite [spec.Fintype] (oa : OracleComp spec α) :
--     Finite ↥(oa.supportWhen poss) := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => exact Set.finite_singleton x
--   | query_bind i t oa hoa =>
--       simpa using Finite.Set.finite_biUnion'' _ fun x => (oa x).supportWhen poss
--   | failure => exact Set.toFinite ∅


-- /-- The support of a computation is finite when viewed as a type. -/
-- instance support_finite [spec.Fintype] (oa : OracleComp spec α) :
--     Finite ↥(oa.support) := supportWhen_finite _ oa

-- /-- With a `DecidableEq` instance we can show that the support is actually a `Fintype`,
-- rather than just `Finite` as in `support_finite`. -/
-- instance support_fintype [spec.Fintype] [DecidableEq α] (oa : OracleComp spec α) :
--     Fintype ↥oa.support := by
--   induction oa using OracleComp.construct with
--   | pure x => exact Fintype.subtypeEq x
--   | query_bind q oa hoa => have := q.rangeFintype; simpa using Set.fintypeiUnion _
--   | failure => exact Set.fintypeEmpty


-- end basic

-- section coe

-- /-- `finSupport` when viewed as a `Set` gives the regular `support` of the computation.  -/
-- @[simp]
-- lemma coe_finSupport [spec.Fintype] [DecidableEq α]
--     (oa : OracleComp spec α) : ↑oa.finSupport = oa.support := by
--   induction oa using OracleComp.induction with
--   | pure x => apply Finset.coe_singleton
--   | query_bind i t oa hoa => simp [hoa]
--   | failure => apply Finset.coe_empty

-- variable [spec.Fintype] [DecidableEq α] (oa : OracleComp spec α) (s : Finset α)

-- lemma finSupport_eq_iff_support_eq_coe : oa.finSupport = s ↔ oa.support = ↑s :=
--   Finset.coe_inj.symm.trans (by rw [coe_finSupport])
-- lemma eq_finSupport_iff_coe_eq_support : s = oa.finSupport ↔ ↑s = oa.support :=
--   Finset.coe_inj.symm.trans (by rw [coe_finSupport])

-- lemma finSupport_subset_iff_support_subset_coe : oa.finSupport ⊆ s ↔ oa.support ⊆ ↑s :=
--   Finset.coe_subset.symm.trans (by rw [coe_finSupport])
-- lemma subset_finSupport_iff_coe_subset_support : s ⊆ oa.finSupport ↔ ↑s ⊆ oa.support :=
--   Finset.coe_subset.symm.trans (by rw [coe_finSupport])

-- lemma mem_finSupport_iff_mem_support (x : α) : x ∈ oa.finSupport ↔ x ∈ oa.support := by
--   rw [← Finset.mem_coe, coe_finSupport]

-- lemma mem_finSupport_of_mem_support {x : α} (hx : x ∈ oa.support) : x ∈ oa.finSupport :=
--   (mem_finSupport_iff_mem_support oa x).2 hx
-- lemma mem_support_of_mem_finSupport {x : α} (hx : x ∈ oa.finSupport) : x ∈ oa.support :=
--   (mem_finSupport_iff_mem_support oa x).1 hx

-- end coe
