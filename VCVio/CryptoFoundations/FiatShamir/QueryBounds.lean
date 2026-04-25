/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.Coercions.Add

/-!
# Query-count bounds for Fiat-Shamir adversaries

Structural `IsQueryBound` predicates used by both the Σ-protocol and
with-aborts instances of Fiat-Shamir, plus the reciprocal challenge-space size
that appears in the quantitative bounds.

The two non-aborting EUF-CMA variants use exactly the same predicates, so they
live here in the shared `FiatShamir` namespace. With-aborts call sites
reference them via their fully qualified name.
-/

universe u v

open OracleComp OracleSpec

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section bounds

variable (M : Type)

/-- Structural bound that counts only random-oracle queries in a Fiat-Shamir
EUF-CMA adversary. Uniform-sampling and signing-oracle queries are unrestricted.

Defined as the generic predicate-targeted query bound `IsQueryBoundP` with the predicate
selecting the nested `.inl (.inr _)` (random-oracle) component of the index sum. -/
def hashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ S')) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP oa
    (fun t =>
      (match t with
        | .inl (.inr _) => true
        | _ => false) = true) Q

/-- Structural query bound for Fiat-Shamir EUF-CMA adversaries that tracks both
signing-oracle queries (`qS`) and random-oracle queries (`qH`).
Uniform-sampling queries are unrestricted. -/
def signHashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ S')) α)
    (qS qH : ℕ) : Prop :=
  OracleComp.IsQueryBound oa (qS, qH)
    (fun t b => match t, b with
      | .inl (.inl _), _ => True
      | .inl (.inr _), (_, qH') => 0 < qH'
      | .inr _, (qS', _) => 0 < qS')
    (fun t b => match t, b with
      | .inl (.inl _), b' => b'
      | .inl (.inr _), (qS', qH') => (qS', qH' - 1)
      | .inr _, (qS', qH') => (qS' - 1, qH'))

/-- Structural bound on random-oracle queries for an NMA adversary (no signing oracle).
Uniform-sampling queries are unrestricted.

Defined as the generic predicate-targeted query bound `IsQueryBoundP` with the predicate
selecting the right (random-oracle) component of the index sum. -/
def nmaHashQueryBound {α : Type}
    (oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP oa (fun t => Sum.isRight t = true) Q

@[simp]
lemma nmaHashQueryBound_query_bind_iff {α : Type}
    (t : (unifSpec + (M × Commit →ₒ Chal)).Domain)
    (oa : (unifSpec + (M × Commit →ₒ Chal)).Range t →
      OracleComp (unifSpec + (M × Commit →ₒ Chal)) α)
    (Q : ℕ) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := liftM ((unifSpec + (M × Commit →ₒ Chal)).query t) >>= oa) Q ↔
      (match t with
      | .inl _ => True
      | .inr _ => 0 < Q) ∧
      ∀ u,
        nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := oa u) (match t with
            | .inl _ => Q
            | .inr _ => Q - 1) := by
  simp only [nmaHashQueryBound, OracleComp.isQueryBoundP_query_bind_iff]
  cases t <;> simp

@[simp]
lemma nmaHashQueryBound_query_iff
    (t : (unifSpec + (M × Commit →ₒ Chal)).Domain) (Q : ℕ) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := liftM ((unifSpec + (M × Commit →ₒ Chal)).query t)) Q ↔
      match t with
      | .inl _ => True
      | .inr _ => 0 < Q := by
  simp only [nmaHashQueryBound, OracleComp.isQueryBoundP_query_iff]
  cases t <;> simp

lemma nmaHashQueryBound_mono {α : Type}
    {oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α} {Q₁ Q₂ : ℕ}
    (h : nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁)
    (hQ : Q₁ ≤ Q₂) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₂ :=
  OracleComp.IsQueryBoundP.mono h hQ

lemma nmaHashQueryBound_bind {α β : Type}
    {oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α}
    {ob : α → OracleComp (unifSpec + (M × Commit →ₒ Chal)) β}
    {Q₁ Q₂ : ℕ}
    (h1 : nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁)
    (h2 : ∀ x,
      nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := ob x) Q₂) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := oa >>= ob) (Q₁ + Q₂) :=
  OracleComp.isQueryBoundP_bind h1 (fun x _ => h2 x)

lemma nmaHashQueryBound_liftComp_zero {α : Type}
    (oa : ProbComp α) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := OracleComp.liftComp oa (unifSpec + (M × Commit →ₒ Chal))) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      trivial
  | query_bind t mx ih =>
      rw [OracleComp.liftComp_bind]
      refine nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
        (oa := OracleComp.liftComp
          ($[0..t])
          (unifSpec + (M × Commit →ₒ Chal)))
        (ob := fun u => OracleComp.liftComp (mx u) (unifSpec + (M × Commit →ₒ Chal)))
        (Q₁ := 0) (Q₂ := 0) ?_ ?_
      · simpa using
          (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
            (.inl t) 0).2 trivial
      · intro u
        exact ih u

/-- Reciprocal of the finite challenge-space size. -/
noncomputable def challengeSpaceInv (challenge : Type) [Fintype challenge] : ENNReal :=
  (Fintype.card challenge : ENNReal)⁻¹

end bounds

end FiatShamir
