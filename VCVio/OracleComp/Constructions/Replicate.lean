/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.EvalDist.List
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
def replicate {ι} {spec : OracleSpec ι} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicate n ()).mapM fun () => oa

def replicateTR {ι} {spec : OracleSpec ι} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicateTR n ()).mapM fun () => oa

variable {ι} {spec : OracleSpec ι} {α β : Type v}
  (oa : OracleComp spec α) (n : ℕ)

@[simp]
lemma replicate_zero : replicate 0 oa = return [] := rfl

@[simp]
lemma replicateTR_zero : replicate 0 oa = return [] := rfl

@[simp]
lemma replicate_succ : replicate (n + 1) oa = List.cons <$> oa <*> replicate n oa := by
  rw [replicate, List.replicate_succ, List.mapM_cons, seq_eq_bind_map, bind_map_left]; rfl

@[simp]
lemma replicate_pure (x : α) :
    (pure x : OracleComp spec α).replicate n = pure (List.replicate n x) := by
  induction n with
  | zero => rfl
  | succ n hn => simp [hn, List.replicate]

variable [spec.Fintype] [spec.Inhabited]

lemma probFailure_replicate :
    Pr[⊥ | oa.replicate n] = 1 - (1 - Pr[⊥ | oa]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [replicate_succ]

/-- The probability of getting a list from `replicate` is the product of the chances of
getting each of the individual elements. -/
@[simp]
lemma probOutput_replicate (xs : List α) :
    Pr[= xs | oa.replicate n] = if xs.length = n then (xs.map (Pr[= · | oa])).prod else 0 := by
  have : DecidableEq α := Classical.decEq α
  induction n generalizing xs with
  | zero =>
    simp only [replicate_zero]
    by_cases hxs : xs = []
    · subst hxs; simp
    · have : xs.length ≠ 0 := fun h => hxs (List.eq_nil_of_length_eq_zero h)
      simp [this, probOutput_eq_zero_of_not_mem_support, hxs]
  | succ n ih =>
    rw [replicate_succ]
    by_cases hxs : xs = []
    · subst hxs; simp
    · obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hxs
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.map_cons, List.prod_cons]
      rw [probOutput_cons_seq_map_cons_eq_mul oa (replicate n oa) y ys, ih]
      simp

-- TODO: restore when `probEvent_seq_map` infrastructure is available
-- lemma probEvent_replicate_of_probEvent_cons
--     (p : List α → Prop) (hp : p []) (q : α → Prop) (hq : ∀ x xs, p (x :: xs) ↔ q x ∧ p xs) :
--     Pr[p | oa.replicate n] = Pr[q | oa] ^ n := by
--   sorry

/-- Possible outputs of `replicate n oa` are lists of length `n` where
each element in the list is a possible output of `oa`. -/
@[simp]
lemma support_replicate :
    support (oa.replicate n) = {xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} := by
  apply Set.ext; intro xs
  simp only [Set.mem_setOf_eq, mem_support_iff, probOutput_replicate, ne_eq]
  constructor
  · intro h
    split_ifs at h with hlen
    · refine ⟨hlen, fun x hx hzero => ?_⟩
      exact h (List.prod_eq_zero (List.mem_map.mpr ⟨x, hx, hzero⟩))
    · exact absurd rfl h
  · intro ⟨hlen, hmem⟩
    rw [if_pos hlen]
    refine List.prod_ne_zero ?_
    intro hzero
    rw [List.mem_map] at hzero
    exact hzero.elim fun x ⟨hx, hxa⟩ => hmem x hx hxa

@[simp]
lemma mem_finSupport_replicate [spec.DecidableEq] [DecidableEq α]
    (xs : List α) : xs ∈ finSupport (oa.replicate n) ↔
      xs.length = n ∧ ∀ x ∈ xs, x ∈ finSupport oa := by
  simp [mem_finSupport_iff_mem_support]

end OracleComp
