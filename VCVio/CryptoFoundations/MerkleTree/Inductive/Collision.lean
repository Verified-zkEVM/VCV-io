/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
import VCVio.OracleComp.QueryTracking.Birthday

/-!
# Merkle Tree Oracle Collision

Defines a predicate `collisionIn` for two distinct hash-oracle log entries with equal
responses, and a birthday-style bound on its probability that bridges to the
`LogHasCollision` infrastructure in `VCVio.OracleComp.QueryTracking.Birthday`.
-/

open scoped NNReal OracleComp

namespace InductiveMerkleTree

open OracleSpec OracleComp List

variable {α : Type}

/-- A log has a collision in the sense used by the SNARGs-book Merkle-tree
extractor: two distinct entries with `BEq`-equal responses. -/
def collisionIn {α : Type} [DecidableEq α]
    (log : (spec α).QueryLog) : Prop :=
  ∃ q1 q2, (q1 ≠ q2) ∧
    q1 ∈ log ∧ q2 ∈ log ∧
    q1.2 == q2.2

/-!
### Bridge to `OracleComp.LogHasCollision`

Two distinct log entries with equal responses must have distinct *inputs* (otherwise
they would be equal as sigma values), so `collisionIn` implies the index/HEq-flavoured
`LogHasCollision` predicate from VCVio.
-/

lemma collisionIn_inputs_ne {α : Type} [DecidableEq α]
    {log : (spec α).QueryLog}
    (h : collisionIn log) :
    ∃ q1 q2, (q1.1 ≠ q2.1) ∧ q1 ∈ log ∧ q2 ∈ log ∧ q1.2 == q2.2 := by
  obtain ⟨q1, q2, hne, hm1, hm2, hresp⟩ := h
  refine ⟨q1, q2, ?_, hm1, hm2, hresp⟩
  intro heq
  apply hne
  rcases q1 with ⟨i1, v1⟩; rcases q2 with ⟨i2, v2⟩
  simp only [Sigma.mk.inj_iff] at *
  exact ⟨heq, by subst heq; exact heq_of_eq (eq_of_beq hresp)⟩

lemma collisionIn_imp_logHasCollision {α : Type} [DecidableEq α]
    {log : (spec α).QueryLog}
    (h : collisionIn log) :
    OracleComp.LogHasCollision log := by
  obtain ⟨q1, q2, hne_input, hm1, hm2, hresp⟩ := collisionIn_inputs_ne h
  rw [List.mem_iff_getElem] at hm1 hm2
  obtain ⟨i, hi, hget1⟩ := hm1
  obtain ⟨j, hj, hget2⟩ := hm2
  have hlog_i : log[(⟨i, hi⟩ : Fin log.length)] = q1 := hget1
  have hlog_j : log[(⟨j, hj⟩ : Fin log.length)] = q2 := hget2
  refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ?_, ?_, ?_⟩
  · intro heq_idx
    apply hne_input
    have hq : q1 = q2 := by
      rw [← hlog_i, ← hlog_j]
      exact congrArg (log[·]) heq_idx
    exact congr_arg Sigma.fst hq
  · rw [hlog_i, hlog_j]; exact hne_input
  · rw [hlog_i, hlog_j]; exact heq_of_eq (eq_of_beq hresp)

/--
Birthday bound for oracle collisions in a Merkle-tree hash-oracle log: the probability
that the combined query log of a computation contains a collision (two distinct entries
with equal responses) is at most `n² / (2 · |α|)`, where `n` is a *total* query bound.

Derived from `OracleComp.probEvent_logCollision_le_birthday_total` by bridging
`collisionIn` to `OracleComp.LogHasCollision`. The slight `n²` vs. `n·(n-1)` slack
relative to the textbook `C(n, 2) / |α|` form comes from the union-bound step in the
underlying birthday lemma.
-/
theorem collision_probability_bound
    {β : Type} [DecidableEq α] [Inhabited α]
    [(spec α).Fintype] [(spec α).Inhabited]
    (oa : OracleComp (spec α) β) (n : ℕ)
    (h : IsTotalQueryBound oa n) :
    Pr[fun z => collisionIn z.2 | (oa.withQueryLog)] ≤
      (n ^ 2 : ENNReal) / (2 * Fintype.card ((spec α).Range default)) := by
  refine le_trans (probEvent_mono fun z _ => collisionIn_imp_logHasCollision) ?_
  refine OracleComp.probEvent_logCollision_le_birthday_total (spec := spec α) oa n h
    Fintype.card_pos (fun t => ?_)
  have heq : (spec α).Range default = (spec α).Range t := rfl
  exact (Fintype.card_congr (Equiv.cast heq)).le

end InductiveMerkleTree
