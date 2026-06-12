/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.EvalDist.List
import VCVio.OracleComp.Constructions.SampleableType
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

/-- Run the computation `oa` repeatedly `n` times to get a list of `n` results. -/
def replicate {ι} {spec : OracleSpec ι} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
      let x ← oa
      let xs ← replicate n oa
      pure (x :: xs)

def replicateTR {ι} {spec : OracleSpec ι} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicateTR n ()).mapM fun () => oa

variable {ι} {spec : OracleSpec ι} {α β : Type v}
  (oa : OracleComp spec α) (n : ℕ)

@[simp]
lemma replicate_zero : replicate 0 oa = return [] := rfl

@[simp]
lemma replicateTR_zero : replicate 0 oa = return [] := rfl

/-- Bind-style unfolding of `replicate`, convenient for program-logic proofs. -/
@[simp]
lemma replicate_succ_bind :
    replicate (n + 1) oa = (do
      let x ← oa
      let xs ← replicate n oa
      pure (x :: xs)) := rfl

/-- The tail-recursive `replicateTR` agrees with the recursive `replicate`. The
`@[simp]` annotation lets every later proof about `replicateTR` reduce to the
recursive form automatically. -/
@[simp]
lemma replicateTR_eq_replicate : replicateTR n oa = replicate n oa := by
  change (List.replicateTR n ()).mapM (fun _ => oa) = replicate n oa
  rw [show List.replicateTR n () = List.replicate n () from
    congrFun (congrFun (congrFun List.replicate_eq_replicateTR.symm Unit) n) ()]
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, List.mapM_cons, ih]

lemma replicate_succ : replicate (n + 1) oa = List.cons <$> oa <*> replicate n oa := by
  simp [replicate_succ_bind, monad_norm, Function.comp]

@[simp]
lemma replicate_pure (x : α) :
    (pure x : OracleComp spec α).replicate n = pure (List.replicate n x) := by
  induction n with
  | zero => rfl
  | succ n hn => simp [hn, List.replicate]

variable [IsUniformSpec spec]

lemma probFailure_replicate :
    Pr[⊥ | oa.replicate n] = 1 - (1 - Pr[⊥ | oa]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp

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

lemma probEvent_replicate_of_probEvent_cons
    (p : List α → Prop) (hp : p []) (q : α → Prop) (hq : ∀ x xs, p (x :: xs) ↔ q x ∧ p xs) :
    Pr[ p | oa.replicate n] = Pr[ q | oa] ^ n := by
  induction n with
  | zero => simp [hp]
  | succ n ih =>
    rw [replicate_succ,
      probEvent_seq_map_eq_mul oa (replicate n oa) List.cons p q p
        (fun x _ xs _ => hq x xs),
      ih, pow_succ, mul_comm]

omit [IsUniformSpec spec] in
/-- Possible outputs of `replicate n oa` are lists of length `n` where
each element in the list is a possible output of `oa`. -/
@[simp]
lemma support_replicate :
    support (oa.replicate n) = {xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} := by
  induction n with
  | zero =>
    ext xs
    simp only [replicate_zero, support_pure, Set.mem_singleton_iff, Set.mem_setOf_eq,
      List.length_eq_zero_iff]
    refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
    intro x hx; subst h; exact (List.not_mem_nil hx).elim
  | succ n ih =>
    rw [replicate_succ]
    ext xs
    cases xs with
    | nil =>
      rw [support_seq_map_eq_image2]
      simp only [Set.mem_image2, Set.mem_setOf_eq, List.length_nil]
      refine ⟨?_, fun ⟨h, _⟩ => absurd h (Nat.succ_ne_zero n).symm⟩
      rintro ⟨_, _, _, _, ⟨⟩⟩
    | cons x xs =>
      rw [cons_mem_support_seq_map_cons_iff, ih]
      simp only [Set.mem_setOf_eq, List.length_cons, Nat.add_right_cancel_iff, List.mem_cons,
        forall_eq_or_imp]
      tauto

@[simp]
lemma mem_finSupport_replicate [spec.DecidableEq] [DecidableEq α]
    (xs : List α) : xs ∈ finSupport (oa.replicate n) ↔
      xs.length = n ∧ ∀ x ∈ xs, x ∈ finSupport oa := by
  simp [mem_finSupport_iff_mem_support]

lemma probOutput_replicate_uniformSample {α : Type} [Fintype α] [SampleableType α]
    {n : ℕ} {xs : List α} (hlen : xs.length = n) :
    Pr[= xs | replicate n ($ᵗ α)] = (↑(Fintype.card α ^ n) : ENNReal)⁻¹ := by
  simp only [probOutput_replicate, hlen, ite_true, probOutput_uniformSample]
  rw [List.prod_map_const, hlen]
  simpa [Nat.cast_pow] using
    (ENNReal.inv_pow (a := (Fintype.card α : ENNReal)) (n := n)).symm

/-! ## SimulateQ distributivity -/

section SimulateQ

variable {ι'} {spec' : OracleSpec ι'} {r : Type v → Type*}
  [Monad r] [LawfulMonad r] (impl : QueryImpl spec r)

omit [IsUniformSpec spec] in
/-- `simulateQ` distributes over `replicate`: simulating a replicated computation
equals running the simulated body `n` times via monadic recursion. -/
lemma simulateQ_replicate :
    simulateQ impl (replicate n oa) =
      (List.replicate n ()).mapM (fun _ => simulateQ impl oa) := by
  induction n with
  | zero => simp [replicate_zero, List.replicate, List.mapM_nil]
  | succ n ih =>
    simp only [replicate_succ_bind, simulateQ_bind, simulateQ_pure,
      List.replicate, List.mapM_cons]
    congr 1; funext x
    simp only [ih]

end SimulateQ

section VectorMapM

/-- Index-extraction for `(Vector.ofFn id).mapM` over an `OracleComp`: any element in the
support of the monadic `mapM` has each component lying in the support of the corresponding
inner computation. -/
lemma support_ofFn_mapM_index
    {ι α : Type} {spec : OracleSpec ι} {L : ℕ}
    (f : Fin L → OracleComp spec α)
    {v : Vector α L}
    (hv : v ∈ support ((Vector.ofFn (fun i : Fin L => i)).mapM f))
    (i : Fin L) : v[i] ∈ support (f i) := by
  simpa using
    Vector.support_mapM_index (Vector.ofFn (fun i : Fin L => i)) f hv i

end VectorMapM

end OracleComp
