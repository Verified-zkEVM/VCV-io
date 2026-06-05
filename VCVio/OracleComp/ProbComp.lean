/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.EvalDist
import Batteries.Control.OptionT

/-!
# Computations with Uniform Selection Oracles

This file defines a type `ProbComp α` for the case of `OracleComp` with access to a
uniform selection oracle, specified by `unifSpec`, as well as common operations for this type.

We define `$[0..n]` as uniform selection starting from zero for any `n : ℕ` (`uniformFin`)
as well as a version `$[n⋯m]` that tries to synthesize an instance of `n < m` (`uniformRange`).
This allows us to avoid needing an `OptionT` wrapper to handle empty ranges.

We also define typeclasses `HasUniformSelect β cont` and `HasUniformSelect! β cont` to allow for
`$ xs` and `$! xs` notation for uniform sampling from a container.
These don't really enforce any semantics, so any new definition will need to prove
lemmas about the behavior of the operation.
TODO: we could introduce a mixin typeclass at least to handle this?

`SampleableType α` on the other hand allows for `$ᵗ α` notation for uniform type sampleing,
and *does* enforce the uniformity of outputs.
Encapsulating the thing you want to select in a `SampleableType` can therefore give more
useful lemmas out of the box, in particular when using subtypes.

TODO: Some lemmas here don't exist at the `PMF`/`SPMF` levels.
-/


open OracleComp BigOperators ENNReal

universe u v w

/-- Simplified notation for computations with no oracles besides random inputs.
This specific case can be used with `#eval` to run a random program, see `OracleComp.runIO`.
NOTE: Need to decide if this should be more opaque than `abbrev`, seems like no as of now.. -/
abbrev ProbComp : Type → Type := OracleComp unifSpec

namespace ProbComp

/-- Independently sample `k` values from `samp`, returning them as a `Fin k → α`. -/
def sampleIID {α : Type} (k : ℕ) (samp : ProbComp α) : ProbComp (Fin k → α) :=
  Fin.mOfFn k fun _ => samp

section uniformFin

/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range. -/
def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) :=
  unifSpec.query n

notation "$[0.." n "]" => uniformFin n

@[grind =]
lemma uniformFin_def (n : ℕ) : $[0..n] = unifSpec.query n := rfl

@[simp]
lemma support_uniformFin (n : ℕ) :
    support (do $[0..n]) = Set.univ := by grind

@[simp]
lemma finSupport_uniformFin (n : ℕ) :
    finSupport (do $[0..n]) = Finset.univ := by grind

@[grind =]
lemma probOutput_uniformFin_eq_div (n : ℕ) (m : Fin (n + 1)) :
    Pr[= m | do $[0..n]] = 1 / (n + 1) := by simp [uniformFin_def]

@[simp, grind =]
lemma probOutput_uniformFin (n : ℕ) (m : Fin (n + 1)) :
    Pr[= m | do $[0..n]] = (n + 1 : ℝ≥0∞)⁻¹ := by simp [uniformFin_def]

@[simp, grind =]
lemma probEvent_uniformFin (n : ℕ) (p : Fin (n + 1) → Prop) [DecidablePred p] :
    Pr[ p | do $[0..n]] = (Fin.countP fun i => p i) / ↑(n + 1) := by
  simp [uniformFin_def, Fin.card_eq_countP_mem]

lemma probFailure_uniformFin (n : ℕ) :
    Pr[⊥ | do $[0..n]] = 0 := by aesop

/-- Nicer induction rule for `ProbComp` that uses monad notation.
Allows inductive definitions on computations by considering the two cases:
* `return x` / `pure x` for any `x`
* `do let u ← $[0..n]; oa u` (with inductive results for `oa u`)
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.
If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected def inductionOn {α} {C : ProbComp α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (n : ℕ) → (mx : Fin (n + 1) → ProbComp α) → (∀ m, C (mx m)) → C ($[0..n] >>= mx))
    (oa : ProbComp α) : C oa :=
  PFunctor.FreeM.inductionOn pure query_bind oa

end uniformFin

section uniformRange

/-- Select uniformly from a non-empty range. The notation attempts to derive `h` automatically. -/
def uniformRange (n m : ℕ) (h : n < m) :
    ProbComp (Fin (m + 1)) :=
  (fun ⟨x, hx⟩ => ⟨x + n, by omega⟩) <$> $[0..(m - n)]

/-- Tactic to attempt to prove `uniformRange` decreasing bound, similar to array indexing. -/
syntax "uniform_range_tactic" : tactic
macro "uniform_range_tactic" : tactic => `(tactic | trivial)
macro "uniform_range_tactic" : tactic => `(tactic | get_elem_tactic)

/-- Select uniformly from a range of numbers. Attempts to use `get-/
notation "$[" n "⋯" m "]" => uniformRange n m (by uniform_range_tactic)

lemma uniformRange_def (n m : ℕ) (h : n < m) : $[n⋯m] = uniformRange n m h := rfl

example {m n : ℕ} (h : m < n) : ProbComp ℕ := do
  let x ← $[314⋯31415]; let y ← $[0⋯10] -- Prove by trivial reduction
  let z ← $[m⋯n] -- Use value from hypothesis
  return x + 2 * y

@[simp, grind =]
lemma uniformRange_eq_uniformFin (n : ℕ) (hn : 0 < n) : $[0⋯n] = $[0..n] := rfl

@[simp, grind =]
lemma probOutput_uniformRange (n m : ℕ) (k : Fin (m + 1)) (h : n < m) :
    Pr[= k | uniformRange n m h] = if n ≤ k then (m - n + 1 : ℝ≥0∞)⁻¹ else 0 := by
  simp only [uniformRange, probOutput_map_eq_sum_finSupport_ite, finSupport_uniformFin, Fin.ext_iff,
    probOutput_uniformFin, natCast_sub, Finset.sum_boole', nsmul_eq_mul]
  by_cases hn : n ≤ k
  · simp only [hn, ↓reduceIte]
    refine trans ?_ (one_mul _)
    congr 2
    rw [Nat.cast_eq_one, Finset.card_eq_one]
    use ⟨k - n, by fin_omega⟩
    ext i
    simp [Fin.ext_iff]
    omega
  · simp only [hn, ↓reduceIte, mul_eq_zero, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, Finset.mem_univ, forall_const, ENNReal.inv_eq_zero, add_eq_top,
      sub_eq_top_iff, natCast_ne_top, ne_eq, not_false_eq_true, and_true, one_ne_top, or_self,
      or_false]
    fin_omega

@[simp, grind =]
lemma support_uniformRange (n m : ℕ) (h : n < m) :
    support (uniformRange n m h) =
      Set.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  ext k
  rw [mem_support_iff, probOutput_uniformRange, Set.mem_Icc, Fin.ofNat_Icc_iff h]
  constructor
  · intro hne
    by_cases hk : n ≤ ↑k
    · exact hk
    · simp [hk] at hne
  · intro hk
    simp only [hk, ↓reduceIte]
    exact ENNReal.inv_ne_zero.mpr (ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top m, one_ne_top⟩)
      (by gcongr; exact tsub_le_self))

@[simp]
lemma finSupport_uniformRange (n m : ℕ) (h : n < m) :
    finSupport (do uniformRange n m h) =
      Finset.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  apply finSupport_eq_of_support_eq_coe
  simp [support_uniformRange n m h]

@[simp, grind =]
lemma probEvent_uniformRange (n m : ℕ)
    (p : Fin (m + 1) → Prop) [DecidablePred p] (h : n < m) :
    Pr[ p | uniformRange n m h] = Finset.card {x : Fin (m + 1) | n ≤ x ∧ p x} / (m - n + 1) := by
  rw [probEvent_eq_sum_filter_finSupport, finSupport_uniformRange]
  simp_rw [probOutput_uniformRange]
  have hsum :
      (∑ x ∈ Finset.filter p (Finset.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m)),
          if n ≤ ↑x then (m - n + 1 : ℝ≥0∞)⁻¹ else 0) =
      (∑ x ∈ Finset.filter p (Finset.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m)),
          (m - n + 1 : ℝ≥0∞)⁻¹) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hx' : n ≤ ↑x := by
      have := (Finset.mem_filter.mp hx).1
      rw [Finset.mem_Icc, Fin.ofNat_Icc_iff h] at this; exact this
    simp [hx']
  rw [hsum, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  congr 1; norm_cast; congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Fin.ofNat_Icc_iff h,
    Finset.mem_univ, true_and]

lemma probFailure_uniformRange (n m : ℕ) (h : n < m) :
    Pr[⊥ | uniformRange n m h] = 0 := by aesop

end uniformRange

section uniformSelect

/-- Typeclass to implement the notation `$ xs` for selecting an object uniformly from a collection.
The container type is given by `cont` with the resulting type given by `β`.
`β` is marked as an `outParam` so that Lean will first pick the output type before synthesizing.
NOTE: This current implementation doesn't impose any "correctness" conditions,
it purely exists to provide the notation, could revisit that in the future. -/
class HasUniformSelect (cont : Type u) (β : outParam Type) where
  uniformSelect : cont → OptionT ProbComp β

/-- Version of `HasUniformSelect` that doesn't allow for failure.
Useful for things like `Vector` that can be shown nonempty at the type level. -/
class HasUniformSelect! (cont : Type u) (β : outParam Type) where
  uniformSelect! : cont → ProbComp β

export HasUniformSelect (uniformSelect)
export HasUniformSelect! (uniformSelect!)

prefix : 75 "$" => uniformSelect
prefix : 75 "$!" => uniformSelect!

variable {cont : Type u} {β : Type}

/-- Given a non-failing uniform selection operation we also have a potentially failing one,
using `OptionT.lift` -/
instance hasUniformSelect_of_hasUniformSelect!
    [h : HasUniformSelect! cont β] : HasUniformSelect cont β where
  uniformSelect cont := OptionT.lift ($! cont)

/-- Compatibility of the `$! xs` operation with `$ xs` given the inferred instance.
TODO: I think we probably want to `simp` in the other direction when possible? -/
@[simp, grind =] lemma liftM_uniformSelect! [HasUniformSelect! cont β]
    (xs : cont) : (liftM ($! xs) : OptionT ProbComp β) = $ xs := by
  simp [OptionT.liftM_def]; rfl

lemma uniformSelect_eq_liftM_uniformSelect! [HasUniformSelect! cont β]
    (xs : cont) : ($ xs : OptionT ProbComp β) = liftM ($! xs) := by grind

end uniformSelect

section uniformSelectList

/-- Select a random element from a list by indexing into it with a uniform value.
If the list is empty we instead just fail rather than choose a default value.
This means selecting from a vector is often preferable, as we can prove at the type level
that there is an element in the list, avoiding the defualt case of empty lists. -/
instance hasUniformSelectList (α : Type) :
    HasUniformSelect (List α) α where
  uniformSelect
    | [] => failure
    | x :: xs => ((x :: xs)[·]) <$> $[0..xs.length]

variable {α : Type} (xs : List α)

lemma uniformSelectList_def : $ xs = match xs with
  | [] => failure
  | x :: xs => ((x :: xs)[·]) <$> $[0..xs.length] := rfl

@[simp, grind =]
lemma uniformSelectList_nil : $ ([] : List α) = failure := rfl

@[grind =]
lemma uniformSelectList_cons (x : α) (xs : List α) :
    $ (x :: xs) = ((x :: xs)[·]) <$> $[0..xs.length] := rfl

@[simp, grind =]
lemma support_uniformSelectList (xs : List α) :
    support ($ xs) = {x | x ∈ xs} := match xs with
  | [] => by simp
  | x :: xs => by simp [uniformSelectList_cons, Set.ext_iff, Fin.exists_iff,
      - List.mem_cons, List.mem_iff_getElem]

@[simp, grind =]
lemma finSupport_uniformSelectList [DecidableEq α] (xs : List α) :
    finSupport ($ xs) = xs.toFinset := match xs with
  | [] => by simp
  | x :: xs => by
      apply finSupport_eq_of_support_eq_coe
      simp [Set.ext_iff]

@[simp, grind =]
lemma probOutput_uniformSelectList [DecidableEq α] (xs : List α) (x : α) :
    Pr[= x | $ xs] = (xs.count x : ℝ≥0∞) / xs.length := match xs with
  | [] => by simp
  | y :: ys => by
    rw [List.count, ← List.countP_eq_sum_fin_ite]
    simp [uniformSelectList_cons, probOutput_map_eq_sum_fintype_ite, div_eq_mul_inv, @eq_comm _ x]

@[simp, grind =] lemma probFailure_uniformSelectList (xs : List α) :
    Pr[⊥ | $ xs] = if xs.isEmpty then 1 else 0 := match xs with
  | [] => by simp
  | y :: ys => by simp [uniformSelectList_cons]

@[simp, grind =] lemma probEvent_uniformSelectList
    (xs : List α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ xs] = (xs.countP p : ℝ≥0∞) / xs.length := match xs with
  | [] => by simp
  | y :: ys => by
    simp only [uniformSelectList_cons, Fin.getElem_fin, liftM_map, probEvent_map,
      OptionT.probEvent_liftM, probEvent_uniformFin, Function.comp_apply,
      Fin.countP_eq_countP_map_finRange, Nat.cast_add, Nat.cast_one, List.length_cons]
    congr 2
    exact List.countP_finRange_getElem (y :: ys) (fun b => decide (p b))

end uniformSelectList

section uniformSelectVector

/-- Select a random element from a vector by indexing into it with a uniform value.
TODO: different types of vectors in mathlib now -/
instance hasUniformSelectVector (α : Type) (n : ℕ) :
    HasUniformSelect! (Vector α (n + 1)) α where
  uniformSelect! xs := (xs[·]) <$> $[0..n]

variable {α : Type} {n : ℕ} (xs : Vector α (n + 1))

lemma uniformSelectVector_def : $! xs = (xs[·]) <$> $[0..n] := rfl

@[simp, grind =]
lemma support_uniformSelectVector : support ($! xs) = {x | x ∈ xs.toList} := by
  ext x
  simp only [uniformSelectVector_def, Fin.getElem_fin, support_map, support_uniformFin,
    Set.image_univ, Set.mem_range, Vector.mem_toList_iff, Set.mem_setOf_eq]
  rw [← Vector.mem_toList_iff]
  simpa [Fin.exists_iff, Vector.getElem_toList] using
    (List.mem_iff_getElem (a := x) (l := xs.toList)).symm

@[simp, grind =]
lemma finSupport_uniformSelectVector [DecidableEq α] :
    finSupport ($ xs) = xs.toList.toFinset := by
  rw [uniformSelect_eq_liftM_uniformSelect!, OptionT.finSupport_liftM]
  apply finSupport_eq_of_support_eq_coe
  simp [support_uniformSelectVector]

@[simp, grind =]
lemma probOutput_uniformSelectVector [DecidableEq α] (x : α) :
    Pr[= x | $! xs] = xs.count x / (n + 1) := by
  simp only [uniformSelectVector_def, Fin.getElem_fin]
  rw [probOutput_map_eq_sum_finSupport_ite]
  simp [div_eq_mul_inv]
  congr 2
  simpa [eq_comm] using (Vector.card_eq_count xs x)

@[simp, grind =]
lemma probEvent_uniformSelectVector (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ xs] = xs.toList.countP p / (n + 1) := by
  rw [uniformSelect_eq_liftM_uniformSelect!]
  simp only [uniformSelectVector_def, Fin.getElem_fin, liftM_map, probEvent_map,
    probEvent_eq_sum_fintype_ite, Function.comp_apply, OptionT.probOutput_liftM,
    probOutput_uniformFin, Finset.sum_boole', nsmul_eq_mul, Vector.countP_toList]
  rw [div_eq_mul_inv]
  congr 1
  simpa [eq_comm] using (Vector.card_eq_countP xs p)

end uniformSelectVector

section uniformSelectListVector

instance hasUniformSelectListVector (α : Type) (n : ℕ) :
    HasUniformSelect! (List.Vector α (n + 1)) α where
  uniformSelect! xs := (xs[·]) <$> $[0..n]

variable {α : Type} {n : ℕ} (xs : List.Vector α (n + 1))

lemma uniformSelectListVector_def : $! xs = (xs[·]) <$> $[0..n] := rfl

@[simp, grind =]
lemma probOutput_uniformSelectListVector [DecidableEq α] (x : α) :
    Pr[= x | $! xs] = xs.toList.count x / (n + 1) := by
  simp only [uniformSelectListVector_def, Fin.getElem_fin, Vector.getElem_eq_get, Fin.eta]
  rw [probOutput_map_eq_sum_finSupport_ite]
  simp [div_eq_mul_inv]
  congr 2
  simpa [eq_comm] using (List.Vector.card_eq_count xs x)

@[simp, grind =]
lemma probEvent_uniformSelectListVector (p : α → Prop) [DecidablePred p] :
    Pr[ p | $! xs] = xs.toList.countP p / (n + 1) := by
  simp only [uniformSelectListVector_def, Fin.getElem_fin, Vector.getElem_eq_get, Fin.eta,
    probEvent_map, probEvent_eq_sum_fintype_ite, Function.comp_apply, probOutput_uniformFin,
    Finset.sum_boole', nsmul_eq_mul]
  rw [div_eq_mul_inv]
  congr 1
  simpa [eq_comm] using (List.Vector.card_eq_countP xs p)

end uniformSelectListVector

section uniformSelectFinset

/-- Choose a random element from a finite set, by converting to a list and choosing from that.
This is noncomputable as we don't have a canoncial ordering for the resulting list,
so generally this should be avoided when possible. -/
noncomputable instance hasUniformSelectFinset (α : Type) :
    HasUniformSelect (Finset α) α where
  uniformSelect s := $ s.toList

variable {α : Type} (s : Finset α)

lemma uniformSelectFinset_def : $ s = $ s.toList := rfl

@[simp, grind =]
lemma support_uniformSelectFinset :
    support ($ s) = if s.Nonempty then ↑s else ∅ := by
  aesop (add norm uniformSelectFinset_def)

@[simp, grind =]
lemma finSupport_uniformSelectFinset [DecidableEq α] :
    finSupport ($ s) = if s.Nonempty then s else ∅ := by
  aesop (add norm uniformSelectFinset_def)

@[simp, grind =]
lemma probOutput_uniformSelectFinset [DecidableEq α] (x : α) :
    Pr[= x | $ s] = if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  aesop (add norm uniformSelectFinset_def)

@[simp, grind =]
lemma probEvent_uniformSelectFinset (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ s] = {x ∈ s | p x}.card / s.card := by
  classical
  haveI : DecidableEq α := Classical.decEq α
  simp only [uniformSelectFinset_def, probEvent_uniformSelectList, List.countP_eq_length_filter,
    Finset.length_toList]
  congr 2
  rw [← List.toFinset_card_of_nodup (l := s.toList.filter fun x => decide (p x))]
  · simp [List.toFinset_filter]
  · exact s.nodup_toList.filter _

@[simp, grind =]
lemma probFailure_uniformSelectFinset :
    Pr[⊥ | $ s] = if s.Nonempty then 0 else 1 := by
  aesop (add norm uniformSelectFinset_def)

end uniformSelectFinset

section uniformSelectArray

instance hasUniformSelectArray (α : Type _) : HasUniformSelect (Array α) α where
  uniformSelect xs := if h : xs.size = 0 then failure else do
    let u ← $[0..xs.size-1]
    return xs[u] -- Note the in-index bound here relies on `h`.

variable {α : Type} (xs : Array α)

lemma uniformSelectArray_def :
    ($ xs : OptionT ProbComp α) =
      if h : xs.size = 0 then failure else do
        let u ← $[0..xs.size-1]
        return xs[u] := rfl

@[simp, grind =]
lemma uniformSelectArray_empty : ($ (#[] : Array α) : OptionT ProbComp α) = failure := rfl

@[simp, grind =]
lemma support_uniformSelectArray : support ($ xs) = {x | x ∈ xs} := by
  by_cases h : xs.size = 0
  · have hxs : xs = #[] := Array.size_eq_zero_iff.mp h
    subst hxs; ext x; simp
  · have hsucc : xs.size - 1 + 1 = xs.size := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h)
    rw [uniformSelectArray_def, dif_neg h]
    ext x
    simp only [support_bind, OptionT.support_liftM, support_uniformFin,
      Set.mem_iUnion, Set.mem_setOf_eq, support_pure, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, _, hx⟩
      have hi : i.val < xs.size := Nat.lt_of_lt_of_eq i.isLt hsucc
      rw [hx]
      exact Array.getElem_mem hi
    · intro hmem
      obtain ⟨i, hi, hxs⟩ := Array.mem_iff_getElem.mp hmem
      exact ⟨⟨i, Nat.lt_of_lt_of_eq hi hsucc.symm⟩, Set.mem_univ _, hxs.symm⟩

@[simp, grind =]
lemma finSupport_uniformSelectArray [DecidableEq α] :
    finSupport ($ xs) = xs.toList.toFinset := by
  apply finSupport_eq_of_support_eq_coe
  rw [support_uniformSelectArray]
  ext x
  simp only [List.coe_toFinset, Set.mem_setOf_eq]
  constructor
  · intro hmem
    obtain ⟨i, hi, hxs⟩ := Array.mem_iff_getElem.mp hmem
    rw [List.mem_iff_getElem]
    refine ⟨i, by rwa [Array.length_toList], ?_⟩
    rw [Array.getElem_toList]; exact hxs
  · intro hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hi, hxs⟩ := hmem
    rw [Array.length_toList] at hi
    rw [Array.mem_iff_getElem]
    exact ⟨i, hi, by rw [← Array.getElem_toList (h := hi)]; exact hxs⟩

@[simp, grind =]
lemma probFailure_uniformSelectArray : Pr[⊥ | $ xs] = if xs.size = 0 then 1 else 0 := by
  by_cases h : xs.size = 0
  · have hxs : xs = #[] := Array.size_eq_zero_iff.mp h
    subst hxs; simp
  · rw [uniformSelectArray_def, dif_neg h]
    simp [h]

-- TODO: `probOutput_uniformSelectArray` and `probEvent_uniformSelectArray` analogous to the
-- `List` API. These need a careful `Fin (xs.size - 1 + 1) ≃ Fin xs.size` reindexing that
-- the present helpers don't cleanly factor. Bridging through `xs.toList` once a clean
-- `($ xs : OptionT ProbComp α) = $ xs.toList` lemma lands is probably the right path.

end uniformSelectArray

section uniformSelectMultiset

/-- Choose a random element from a multiset, by converting to a list and choosing from that.
This is noncomputable as the underlying list is only canonical up to permutation; for any
fixed `Multiset.toList` representative each element is sampled with weight equal to its
multiplicity. -/
noncomputable instance hasUniformSelectMultiset (α : Type) :
    HasUniformSelect (Multiset α) α where
  uniformSelect s := $ s.toList

variable {α : Type} (s : Multiset α)

lemma uniformSelectMultiset_def : ($ s : OptionT ProbComp α) = $ s.toList := rfl

@[simp, grind =]
lemma support_uniformSelectMultiset :
    support ($ s) = {x | x ∈ s} := by
  ext x; simp [uniformSelectMultiset_def, Multiset.mem_toList]

@[simp, grind =]
lemma finSupport_uniformSelectMultiset [DecidableEq α] :
    finSupport ($ s) = s.toFinset := by
  apply finSupport_eq_of_support_eq_coe
  ext x
  simp [Multiset.mem_toFinset]

@[simp, grind =]
lemma probOutput_uniformSelectMultiset [DecidableEq α] (x : α) :
    Pr[= x | $ s] = (s.count x : ℝ≥0∞) / Multiset.card s := by
  simp only [uniformSelectMultiset_def, probOutput_uniformSelectList,
    Multiset.length_toList]
  congr 2
  exact (Multiset.coe_count x s.toList).symm.trans (by rw [Multiset.coe_toList])

@[simp, grind =]
lemma probEvent_uniformSelectMultiset (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ s] = (Multiset.countP p s : ℝ≥0∞) / Multiset.card s := by
  classical
  simp only [uniformSelectMultiset_def, probEvent_uniformSelectList,
    Multiset.length_toList]
  congr 2
  exact (Multiset.coe_countP p s.toList).symm.trans (by rw [Multiset.coe_toList])

@[simp, grind =]
lemma probFailure_uniformSelectMultiset :
    Pr[⊥ | $ s] = if 0 < Multiset.card s then 0 else 1 := by
  rw [uniformSelectMultiset_def, probFailure_uniformSelectList]
  by_cases h : Multiset.card s = 0
  · have hs : s = 0 := Multiset.card_eq_zero.mp h
    subst hs
    simp
  · have hne : s ≠ 0 := fun hs => h (by rw [hs]; rfl)
    have hempty_false : s.toList.isEmpty = false := by
      rw [Bool.eq_false_iff, ne_eq, List.isEmpty_iff, Multiset.toList_eq_nil]
      exact hne
    have hpos : 0 < Multiset.card s := Nat.pos_of_ne_zero h
    rw [hempty_false, if_pos hpos]
    rfl

end uniformSelectMultiset

end ProbComp

section coinSpec
-- NOTE: This treats `coin` as essentially part of `ProbComp`, but it is more general.
-- In particular we can have a seperate theory of bounded uniform selection using only coins.

@[simp, grind =]
lemma support_coin : support coin = {true, false} := by aesop

@[simp, grind =]
lemma finSupport_coin : finSupport coin = {true, false} := by aesop

@[simp, grind =]
lemma probOutput_coin (b : Bool) : Pr[= b | coin] = 2⁻¹ := by aesop

@[simp, grind =]
lemma probEvent_coin (p : Bool → Prop) [DecidablePred p] :
    Pr[ p | coin] = if p true then
      (if p false then 1 else 2⁻¹) else
      (if p false then 2⁻¹ else 0) := by
  have : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by simp [← one_div]
  rw [probEvent_eq_sum_fintype_ite, Fintype.sum_bool]
  aesop

@[simp, grind =]
lemma probFailure_coin : Pr[⊥ | coin] = 0 := by grind

end coinSpec
