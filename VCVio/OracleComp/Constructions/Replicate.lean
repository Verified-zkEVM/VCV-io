/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.EvalDist
import Init.Data.Vector.Lemmas

/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a list of length `n`.

Note that while the executions are independent, they may no longer be after calling `simulate`.
-/

open OracleSpec

universe u v w

namespace OracleComp

/-- Run the computation `oa` repeatedly `n` times to get a vector of `n` results. -/
def replicate {spec : OracleSpec} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicate n ()).mapM fun () => oa

def replicateTR {spec : OracleSpec} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicateTR n ()).mapM fun () => oa

variable {spec : OracleSpec} {α β : Type v}
  (oa : OracleComp spec α) (n : ℕ)

@[simp]
lemma replicate_zero : replicate 0 oa = return [] := rfl

@[simp]
lemma replicateTR_zero : replicate 0 oa = return [] := rfl

@[simp]
lemma replicate_succ : replicate (n + 1) oa = List.cons <$> oa <*> replicate n oa := by
  rw [replicate, List.replicate_succ, List.mapM_cons, seq_eq_bind, bind_map_left]; rfl

@[simp]
lemma replicate_pure (x : α) :
    (pure x : OracleComp spec α).replicate n = pure (List.replicate n x) := by
  induction n with
  | zero => rfl
  | succ n hn => simp [hn, List.replicate]

-- @[simp]
-- lemma probFailure_replicate [spec.FiniteRange] :
--     [⊥ | oa.replicate n] = 1 - (1 - [⊥ | oa]) ^ n := by
--   rw [replicate, probFailure_list_mapM, List.map_replicate, List.prod_replicate]

-- /-- The probability of getting a vector from `replicate` is the product of the chances of
-- getting each of the individual elements. -/
-- @[simp]
-- lemma probOutput_replicate [spec.FiniteRange] (xs : List α) :
--     [= xs | oa.replicate n] = if xs.length = n then (xs.map ([= · | oa])).prod else 0 := by
--   rw [replicate, probOutput_list_mapM, List.length_replicate]
--   split_ifs with hxs
--   · exact congr_arg List.prod <| List.ext_getElem (by simp [hxs]) (by simp)
--   · rfl

-- lemma probEvent_replicate_of_probEvent_cons [spec.FiniteRange]
--     (p : List α → Prop) (hp : p []) (q : α → Prop) (hq : ∀ x xs, p (x :: xs) ↔ q x ∧ p xs) :
--     [p | oa.replicate n] = [q | oa] ^ n := by
--   induction n with
--   | zero => simpa using hp
--   | succ n hn =>
--       simp_rw [replicate_succ, probEvent_seq_map_eq_probEvent, hq, pow_succ, ← hn,
--         probEvent_seq_map_prod_mk_eq_mul, mul_comm [q | oa]]

-- @[simp]
-- lemma probEvent_all_replicate [spec.FiniteRange] (oa : OracleComp spec α) (n : ℕ) (p : α → Bool) :
--     [λ xs ↦ List.all xs p | oa.replicate n] = [λ x ↦ p x | oa] ^ n := by
--   apply probEvent_replicate_of_probEvent_cons
--   · rfl
--   · simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true, implies_true]

-- lemma support_eq_setOf_probOutput_eq_zero [spec.FiniteRange] (oa : OracleComp spec α) :
--     oa.support = {x | [= x | oa] ≠ 0} := by
--   simp only [ne_eq, probOutput_eq_zero_iff, not_not, Set.setOf_mem_eq]

-- /-- Possible ouptuts of `replicate n oa` are lists of length `n` where
-- ecah element in the list is a possible output of `oa`. -/
-- @[simp]
-- lemma support_replicate [spec.FiniteRange] (oa : OracleComp spec α) (n : ℕ) :
--     (oa.replicate n).support = {xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ oa.support} := by
--   rw [support_eq_setOf_probOutput_eq_zero]; simp

-- /-- Version of `support_replicate` using `List.all` instead of quantifiers.
-- Requires decidable equality on the output type of the computation. -/
-- lemma support_replicate' [spec.FiniteRange] [DecidableEq α] (oa : OracleComp spec α) (n : ℕ) :
--     (oa.replicate n).support = {xs | xs.length = n ∧ xs.all (· ∈ oa.support)} := by
--   simp only [support_replicate, List.all_eq_true, decide_eq_true_eq]

-- @[simp]
-- lemma mem_finSupport_replicate [spec.FiniteRange] [spec.DecidableEq] [DecidableEq α]
--     (oa : OracleComp spec α) (n : ℕ)
--     (xs : List α) : xs ∈ (oa.replicate n).finSupport ↔
--       xs.length = n ∧ xs.all (· ∈ oa.finSupport) := by
--   simp [mem_finSupport_iff_mem_support]

-- section SampleableTypeVector

-- /-- Vectors can be selected uniformly if the underlying type can be.
-- Note: this isn't very efficient as an actual implementation in practice. -/
-- instance (α : Type) [SampleableType α] (n : ℕ) :
--     SampleableType (Vector α n) where
--   selectElem := ($ᵗ α).replicate n
--   mem_support_selectElem xs := by simp
--   probOutput_selectElem_eq xs ys := by simp
--   probFailure_selectElem := by simp

-- end SampleableTypeVector

end OracleComp
