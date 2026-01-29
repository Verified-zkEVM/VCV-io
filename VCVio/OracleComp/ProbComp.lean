/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
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

lemma Fin.card_eq_countP_mem {n : ℕ} (s : Finset (Fin n)) :
    s.card = Fin.countP (· ∈ s) := by
  sorry

/-- Simplified notation for computations with no oracles besides random inputs.
This specific case can be used with `#eval` to run a random program, see `OracleComp.runIO`.
NOTE: Need to decide if this should be more opaque than `abbrev`, seems like no as of now.. -/
abbrev ProbComp : Type → Type := OracleComp unifSpec

namespace ProbComp

section uniformFin

/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range. -/
def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) :=
  query (spec := unifSpec) n

notation "$[0.." n "]" => uniformFin n

@[grind =]
lemma uniformFin_def (n : ℕ) : $[0..n] = query (spec := unifSpec) n := rfl

@[simp]
lemma support_uniformFin (n : ℕ) :
    support (do $[0..n]) = Set.univ := by grind

@[simp]
lemma finSupport_uniformFin (n : ℕ) :
    finSupport (do $[0..n]) = Finset.univ := by grind

@[simp, grind =]
lemma probOutput_uniformFin_eq_div (n : ℕ) (m : Fin (n + 1)) :
    Pr[= m | do $[0..n]] = 1 / (n + 1) := by simp [uniformFin_def]

@[simp, grind =]
lemma probOutput_uniformFin (n : ℕ) (m : Fin (n + 1)) :
    Pr[= m | do $[0..n]] = (n + 1 : ℝ≥0∞)⁻¹ := by simp

@[simp, grind =]
lemma probEvent_uniformFin (n : ℕ) (p : Fin (n + 1) → Prop) [DecidablePred p] :
    Pr[p | do $[0..n]] = (Fin.countP fun i => p i) / ↑(n + 1) := by
  simp [uniformFin_def, Fin.card_eq_countP_mem]

lemma probFailure_uniformFin (n : ℕ) :
    Pr[⊥ | do $[0..n]] = 0 := by aesop

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
lemma support_uniformRange (n m : ℕ) (h : n < m) :
    support (uniformRange n m h) =
      Set.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  ext k
  simp [uniformRange]
  stop
  refine ⟨fun h => by fin_omega, fun h => ?_⟩
  refine ⟨⟨k - n, by fin_omega⟩, by fin_omega⟩

@[simp]
lemma finSupport_uniformRange (n m : ℕ) (h : n < m) :
    finSupport (do uniformRange n m h) =
      Finset.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  aesop

@[simp, grind =]
lemma probOutput_uniformRange (n m : ℕ) (k : Fin (m + 1)) (h : n < m) :
    Pr[= k | uniformRange n m h] = if n ≤ k then (m - n + 1 : ℝ≥0∞)⁻¹ else 0 := by
  simp[uniformRange, probOutput_map_eq_sum_finSupport_ite, Fin.ext_iff]
  by_cases hn : n ≤ k
  · simp only [hn, ↓reduceIte]
    refine trans ?_ (one_mul _)
    congr 2
    rw [Nat.cast_eq_one, Finset.card_eq_one]
    use ⟨k - n, by fin_omega⟩
    ext i
    simp [Fin.ext_iff]
    omega
  · simp [hn]
    fin_omega

@[simp, grind =]
lemma probEvent_uniformRange (n m : ℕ)
    (p : Fin (m + 1) → Prop) [DecidablePred p] (h : n < m) :
    Pr[p | uniformRange n m h] = Finset.card {x : Fin (m + 1) | n ≤ x ∧ p x} / (m - n + 1) := by
  sorry

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
using `OptionT.lift`  -/
instance hasUniformSelect_of_hasUniformSelect!
    [h : HasUniformSelect! cont β] : HasUniformSelect cont β where
  uniformSelect cont := OptionT.lift ($! cont)

/-- Compatibility of the `$! xs` operation with `$ xs` given the inferred instance. -/
@[simp, grind =] lemma liftM_uniformSelect! [HasUniformSelect! cont β]
    (xs : cont) : (liftM ($! xs) : OptionT ProbComp β) = $ xs := by
  simp [hasUniformSelect_of_hasUniformSelect!, OptionT.liftM_def]

lemma uniformSelect_eq_liftM_uniformSelect! [HasUniformSelect! cont β]
    (xs : cont) : ($ xs : OptionT ProbComp β) = liftM ($! xs) := by grind

end uniformSelect

section uniformSelectList

/-- Select a random element from a list by indexing into it with a uniform value.
If the list is empty we instead just fail rather than choose a default value.
This means selecting from a vector is often preferable, as we can prove at the type level
that there is an element in the list, avoiding the defualt case of empty lists. -/
instance hasUniformSelectList (α : Type) [Inhabited α] :
    HasUniformSelect (List α) α where
  uniformSelect xs := do Option.getM (← (xs[·]?) <$> $[0..xs.length])

variable {α : Type} [Inhabited α]

lemma uniformSelectList_def (xs : List α) :
    $ xs = (do Option.getM (← (xs[·]?) <$> $[0..xs.length])) := rfl

@[simp] lemma uniformSelectList_nil :
    $ ([] : List α) = liftM $[0..0] *> failure := by
  simp [hasUniformSelectList, seqRight_eq_bind]

lemma uniformSelectList_cons (x : α) (xs : List α) :
    $ (x :: xs) = ((x :: xs)[·]) <$> $[0..xs.length] := by
  simp [hasUniformSelectList]
  simp [map_eq_bind_pure_comp]
  sorry

-- @[simp] lemma run_uniformSelectList (xs : List α) :
--     OptionT.run ($ xs) = (xs[·]?) <$> $[0..xs.length] := by
--   induction xs with
--   | nil =>
--     simp


--   | cons x xs h =>
--     simp [uniformSelectList_cons]
--     simp [getElem?_def]
--     sorry


-- @[simp] lemma evalDist_uniformSelectList (xs : List α) :
--     evalDist ($ xs) = match xs with
--     | [] => failure
--     | x :: xs => (PMF.uniformSample (Fin xs.length.succ)).map (some (x :: xs)[·]) :=
--   match xs with
--   | [] => by simp only [uniformSelectList_nil, evalDist_failure]; rfl
--   | x :: xs => by
--     apply OptionT.ext
--     simp only [uniformSelectList_cons, Fin.getElem_fin, evalDist_map, evalDist_liftM,
--       OptionT.run_map, OptionT.run_lift, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
--       Nat.succ_eq_add_one]
--     simp [OptionT.run, PMF.monad_map_eq_map, PMF.map, Function.comp_def]

-- @[simp] lemma support_uniformSelectList (xs : List α) :
--     ($ xs).support = if xs.isEmpty then ∅ else {y | y ∈ (xs)} :=
--   match xs with
--   | [] => rfl
--   | x :: xs => by simp only [uniformSelectList_cons, Fin.getElem_fin, support_map,
--       support_uniformFin, Set.image_univ, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
--       List.mem_iff_get, List.length_cons, List.get_eq_getElem, Set.ext_iff, Set.mem_range,
--       Set.mem_setOf_eq, implies_true]

-- @[simp] lemma finSupport_uniformSelectList [DecidableEq α] (xs : List α) :
--     ($ xs).finSupport = if xs.isEmpty then ∅ else xs.toFinset :=
--   match xs with
--   | [] => rfl
--   | x :: xs => by
--       simp only [finSupport_eq_iff_support_eq_coe, support_uniformSelectList,
--         List.isEmpty_cons, Bool.false_eq_true, if_false]
--       refine Set.ext (λ y ↦ by simp)

-- @[simp] lemma probOutput_uniformSelectList [DecidableEq α] (xs : List α) (x : α) :
--     [= x | $ xs] = if xs.isEmpty then 0 else (xs.count x : ℝ≥0∞) / xs.length := match xs with
--   | [] => by simp
--   | y :: ys => by
--     rw [List.count, ← List.countP_eq_sum_fin_ite]
--     simp [uniformSelectList_cons, probOutput_map_eq_sum_fintype_ite, div_eq_mul_inv, @eq_comm _ x]

-- @[simp] lemma probFailure_uniformSelectList (xs : List α) :
--     [⊥ | $ xs] = if xs.isEmpty then 1 else 0 := match xs with
--   | [] => by simp
--   | y :: ys => by simp [uniformSelectList_cons]

-- @[simp] lemma probEvent_uniformSelectList (xs : List α) (p : α → Prop) [DecidablePred p] :
--     [p | $ xs] = if xs.isEmpty then 0 else (xs.countP p : ℝ≥0∞) / xs.length := match xs with
--   | [] => by simp
--   | y :: ys => by simp [← List.countP_eq_sum_fin_ite, uniformSelectList_cons,
--       probOutput_map_eq_sum_fintype_ite, div_eq_mul_inv, Function.comp_def]

end uniformSelectList

section uniformSelectVector

/-- Select a random element from a vector by indexing into it with a uniform value.
TODO: different types of vectors in mathlib now -/
instance hasUniformSelectVector (α : Type) (n : ℕ) :
    HasUniformSelect! (Vector α (n + 1)) α where
  uniformSelect! xs := (xs[·]) <$> $[0..n]

instance hasUniformSelectListVector (α : Type) (n : ℕ) :
    HasUniformSelect! (List.Vector α (n + 1)) α where
  uniformSelect! xs := (xs[·]) <$> $[0..n]

-- lemma uniformSelectVector_def {α : Type} {n : ℕ} (xs : Vector α (n + 1)) :
--     ($ xs) = ($ xs.toList) := rfl

-- variable {α : Type} {n : ℕ}

-- -- /-- Uniform selection from a vector is as uniform selection from the underlying list,
-- -- given some `Inhabited` instance on the output type. -/
-- -- lemma uniformSelectVector_eq_uniformSelectList (xs : Mathlib.Vector α (n + 1)) :
-- --     ($ xs) = ($ xs.toList : ProbComp α) :=
-- --   match xs with
-- --   | ⟨x :: xs, h⟩ => by
-- --     have hxs : n = List.length xs := by simpa using symm h
-- --     cases hxs
-- --     simp only [uniformSelectVector_def, Fin.getElem_fin, Vector.getElem_eq_get, Vector.get,
-- --       List.length_cons, Fin.eta, Fin.cast_eq_self, List.get_eq_getElem, map_eq_bind_pure_comp,
-- --       Function.comp, Vector.toList_mk, uniformSelectList_cons]
-- --     sorry

-- @[simp]
-- lemma evalDist_uniformSelectVector (xs : Vector α (n + 1)) :
--     evalDist ($ xs) = (PMF.uniformSample (Fin (n + 1))).map (xs[·]) := by
--   simp [uniformSelectVector_def]
--   sorry

-- @[simp]
-- lemma support_uniformSelectVector (xs : Vector α (n + 1)) :
--     ($ xs).support = {x | x ∈ xs.toList} := by sorry
--   -- simp only [uniformSelectVector_eq_uniformSelectList, support_uniformSelectList,
--   --   Vector.empty_toList_eq_ff, Bool.false_eq_true, ↓reduceIte]

-- @[simp]
-- lemma finSupport_uniformSelectVector [DecidableEq α] (xs : Vector α (n + 1)) :
--     ($ xs).finSupport = xs.toList.toFinset := by sorry
--   -- simp only [uniformSelectVector_eq_uniformSelectList, finSupport_uniformSelectList,
--   --   Vector.empty_toList_eq_ff, Bool.false_eq_true, ↓reduceIte]

-- @[simp]
-- lemma probOutput_uniformSelectVector [DecidableEq α] (xs : Vector α (n + 1)) (x : α) :
--     [= x | $ xs] = xs.toList.count x / (n + 1) := by sorry
--   -- simp only [uniformSelectVector_eq_uniformSelectList, probOutput_uniformSelectList,
--   --   Vector.empty_toList_eq_ff, Bool.false_eq_true, ↓reduceIte, Vector.toList_length,
    --Nat.cast_add, --   Nat.cast_one]

-- @[simp]
-- lemma probEvent_uniformSelectVector (xs : Vector α (n + 1)) (p : α → Prop)
--     [DecidablePred p] : [p | $ xs] = xs.toList.countP p / (n + 1) := by sorry
--   -- simp only [uniformSelectVector_eq_uniformSelectList, probEvent_uniformSelectList,
--   --   Vector.empty_toList_eq_ff, Bool.false_eq_true, ↓reduceIte, Vector.toList_length,
      -- Nat.cast_add,
--   --   Nat.cast_one]

end uniformSelectVector

section uniformSelectFinset

/-- Choose a random element from a finite set, by converting to a list and choosing from that.
This is noncomputable as we don't have a canoncial ordering for the resulting list,
so generally this should be avoided when possible. -/
noncomputable instance hasUniformSelectFinset (α : Type) [Inhabited α] :
    HasUniformSelect (Finset α) α where
  uniformSelect s := $ s.toList

-- lemma uniformSelectFinset_def {α : Type} [DecidableEq α] (s : Finset α) :
--     ($ s) = ($ s.toList) := rfl

-- variable {α : Type}

-- @[simp] lemma support_uniformSelectFinset [DecidableEq α] (s : Finset α) :
--     ($ s).support = if s.Nonempty then ↑s else ∅ := by
--   simp only [Finset.nonempty_iff_ne_empty, ne_eq, ite_not]
--   split_ifs with hs <;> simp [hs, uniformSelectFinset_def]

-- @[simp] lemma finSupport_uniformSelectFinset [DecidableEq α] (s : Finset α) :
--     ($ s).finSupport = if s.Nonempty then s else ∅ := by
--   split_ifs with hs <;> simp only [hs, finSupport_eq_iff_support_eq_coe,
--     support_uniformSelectFinset, if_true, if_false, Finset.coe_singleton, Finset.coe_empty]

-- @[simp] lemma probOutput_uniformSelectFinset [DecidableEq α] (s : Finset α) (x : α) :
--     [= x | $ s] = if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
--   rw [uniformSelectFinset_def, probOutput_uniformSelectList]
--   by_cases hx : x ∈ s
--   · have : s.toList.isEmpty = false :=
--       List.isEmpty_eq_false_iff_exists_mem.2 ⟨x, Finset.mem_toList.2 hx⟩
--     simp [this, hx]
--   · simp [hx]

-- @[simp] lemma probFailure_uniformSelectFinset [DecidableEq α] (s : Finset α) :
--     [⊥ | $ s] = if s.Nonempty then 0 else 1 := by
--   simp_rw [Finset.nonempty_iff_ne_empty]
--   split_ifs with hs
--   · simp [hs, uniformSelectFinset_def]
--   · simp [hs, uniformSelectFinset_def]

-- @[simp] lemma evalDist_uniformSelectFinset [DecidableEq α] (s : Finset α) :
--     evalDist ($ s) = if hs : s.Nonempty then
--       OptionT.lift (PMF.uniformOfFinset s hs) else failure := by
--   refine PMF.ext λ x ↦ ?_
--   by_cases hs : s.Nonempty
--   · cases x with
--     | none =>
--         refine (probFailure_uniformSelectFinset _).trans ?_
--         simp [hs, OptionT.lift, OptionT.mk]
--     | some x =>
--         simp only [hs, ↓reduceDIte]
--         refine (probOutput_uniformSelectFinset _ _).trans ?_
--         simp only [OptionT.lift, OptionT.mk, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
--           PMF.bind_apply, PMF.uniformOfFinset_apply, PMF.pure_apply, Option.some.injEq, mul_ite,
--           mul_one, mul_zero]
--         refine symm <| (tsum_eq_single x ?_).trans ?_
--         · simp only [ne_eq, @eq_comm _ x, ite_eq_right_iff, ENNReal.inv_eq_zero,
--             natCast_ne_top, imp_false]
--           intros
--           tauto
--         · simp only [↓reduceIte, ite_eq_ite]
--   · simp only [Finset.not_nonempty_iff_eq_empty] at hs
--     simp [hs, uniformSelectFinset_def]

end uniformSelectFinset

end ProbComp
