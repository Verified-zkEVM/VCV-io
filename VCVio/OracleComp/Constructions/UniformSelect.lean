/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.EvalDist
import Batteries.Control.OptionT

/-!
# Selecting Uniformly From a Collection

This file defines some computations for selecting uniformly at random from a number
of different collections, using `unifSpec` to make the random choices.

TODO: A lot of lemmas here could exist at the `PMF` level instead.
Probably even a lot of the uniform constructions themselves (like `uniformOfList`)
-/

open BigOperators ENNReal

universe u v w

namespace OracleComp

section uniformSelect

/-- Typeclass to implement the notation `$ xs` for selecting an object uniformly from a collection.
The container type is given by `cont` with the resulting type given by `β`.
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

prefix : 50 "$" => uniformSelect
prefix : 50 "$!" => uniformSelect!

instance {cont β : Type} [h : HasUniformSelect! cont β] :
    HasUniformSelect cont β where
  uniformSelect cont := OptionT.mk (some <$> ($! cont))


end uniformSelect

section uniformSelectList

#check Option.getM

/-- Select a random element from a list by indexing into it with a uniform value.
If the list is empty we instead just fail rather than choose a default value.
This means selecting from a vector is often preferable, as we can prove at the type level
that there is an element in the list, avoiding the defualt case of empty lists. -/
instance hasUniformSelectList (α : Type) [Inhabited α] :
    HasUniformSelect (List α) α where
  uniformSelect xs := do Option.getM (← (xs[·]?) <$> $[0..xs.length])

variable {α : Type} [Inhabited α]

@[simp] lemma uniformSelectList_nil :
    ($ ([] : List α) : OptionT ProbComp α) = liftM $[0..0] *> failure := by
  simp [hasUniformSelectList]
  rfl

-- lemma uniformSelectList_cons (x : α) (xs : List α) :
--     ($ (x :: xs)) = ((x :: xs)[·]) <$> $[0..xs.length] := rfl

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
--     | x :: xs => (PMF.uniformOfFintype (Fin xs.length.succ)).map (some (x :: xs)[·]) :=
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
--     evalDist ($ xs) = (PMF.uniformOfFintype (Fin (n + 1))).map (xs[·]) := by
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

section SampleableType

/-- A `SampleableType β` instance means that `β` is a finite inhabited type,
with a computation `selectElem` that selects uniformly at random from the type.
This generally requires choosing some "canonical" ordering for the type,
so we include this to get a computable version of selection.
We also require that each element has the same probability of being chosen from by `selectElem`,
see `SampleableType.probOutput_selectElem` for the reduction when `α` has a fintype instance.
NOTE: universe polymorphism of `β` is hard. -/
class SampleableType (β : Type) where
  selectElem : ProbComp β
  mem_support_selectElem (x : β) : x ∈ support selectElem
  probOutput_selectElem_eq (x y : β) : Pr[= x | selectElem] = Pr[= y | selectElem]
  probFailure_selectElem : Pr[⊥ | selectElem] = 0

/-- Select uniformly from the type `β` using a type-class provided definition.
NOTE: naming is somewhat strange now that `Fintype` isn't explicitly required. -/
def uniformOfFintype (β : Type) [h : SampleableType β] :
    ProbComp β := h.selectElem

prefix : 90 "$ᵗ" => uniformOfFintype

variable (α : Type) [hα : SampleableType α]

@[simp] lemma probOutput_uniformOfFintype [Fintype α] (x : α) :
    Pr[= x | $ᵗ α] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  have : (Fintype.card α : ℝ≥0∞) = ∑ y : α, 1 :=
    by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  simp_rw [this, Finset.mul_sum, mul_one]
  stop
  rw [← sum_probOutput_eq_one ($ᵗ α) SampleableType.probFailure_selectElem]
  exact Finset.sum_congr rfl λ y _ ↦ SampleableType.probOutput_selectElem_eq x y

@[simp] lemma probFailure_uniformOfFintype : Pr[⊥ | $ᵗ α] = 0 :=
  SampleableType.probFailure_selectElem

@[simp] instance : HasSPMF.NeverFail ($ᵗ α) := inferInstance

@[simp] lemma evalDist_uniformOfFintype [Fintype α] [Inhabited α] :
    evalDist ($ᵗ α) = OptionT.lift (PMF.uniformOfFintype α) := by
  refine OptionT.ext ?_
  simp
  stop
  refine PMF.ext λ x ↦ match x with
  | none => by simp
  | some x => by
      simp [evalDist_apply_some]
      refine symm ((tsum_eq_single x ?_).trans ?_)
      · simp [@eq_comm _ x]
      · simp

@[simp] lemma support_uniformOfFintype : support ($ᵗ α) = Set.univ := by
  simp only [Set.ext_iff, Set.mem_univ, iff_true]
  apply SampleableType.mem_support_selectElem

@[simp] lemma finSupport_uniformOfFintype [Fintype α] [DecidableEq α] :
    finSupport ($ᵗ α) = Finset.univ := by
  stop
  simp only [finSupport_eq_iff_support_eq_coe, support_uniformOfFintype, Finset.coe_univ]

@[simp] lemma probEvent_uniformOfFintype [Fintype α] (p : α → Prop) [DecidablePred p] :
    Pr[p | $ᵗ α] = (Finset.univ.filter p).card / Fintype.card α := by
  stop
  simp only [probEvent_eq_sum_filter_univ, probOutput_uniformOfFintype, Finset.sum_const,
    nsmul_eq_mul, div_eq_mul_inv]

section instances

instance (α : Type) [Unique α] : SampleableType α where
  selectElem := return default
  mem_support_selectElem x := Unique.eq_default x ▸ rfl
  probOutput_selectElem_eq x y := by rw [Unique.eq_default x, Unique.eq_default y]
  probFailure_selectElem := sorry --probFailure_pure default

instance : SampleableType Bool where
  selectElem := $! #v[true, false]
  mem_support_selectElem x := by sorry --simp
  probOutput_selectElem_eq x y := by sorry --simp
  probFailure_selectElem := by sorry --simp

/-- Select a uniform element from `α × β` by independently selecting from `α` and `β`. -/
instance (α β : Type) [Fintype α] [Fintype β] [Inhabited α] [Inhabited β]
    [SampleableType α] [SampleableType β] : SampleableType (α × β) where
  selectElem := (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)
  mem_support_selectElem x := by sorry --simp
  probOutput_selectElem_eq := by
    stop
    simp only [Prod.forall, probOutput_seq_map_prod_mk_eq_mul,
      probOutput_uniformOfFintype, forall_const, implies_true]
  probFailure_selectElem := by sorry --simp [probFailure_seq]

/-- Nonempty `Fin` types can be selected from, using implicit casting of `Fin (n - 1 + 1)`. -/
instance (n : ℕ) : SampleableType (Fin (n + 1)) where
  selectElem := $[0..n]
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by sorry --simp only [probOutput_uniformFin, implies_true]
  probFailure_selectElem := by sorry-- simp

/-- Version of `Fin` selection using the `NeZero` typeclass, avoiding the need for `n + 1`. -/
instance (n : ℕ) [hn : NeZero n] : SampleableType (Fin n) where
  selectElem := congr_arg Fin (Nat.succ_pred (NeZero.ne n)).symm ▸ $ᵗ (Fin (n - 1 + 1))
  mem_support_selectElem x := by sorry --rw [mem_support_eqRec_iff]; simp
  probOutput_selectElem_eq x y := by sorry --simp [probOutput_eqRec]
  probFailure_selectElem := by sorry --simp

/-- Select a uniform element from `Vector α n` by independently selecting `α` at each index. -/
instance (α : Type) (n : ℕ) [SampleableType α] : SampleableType (Vector α n) where
  selectElem := by induction n with
  | zero => exact pure #v[]
  | succ m ih => exact Vector.push <$> ih <*> ($ᵗ α)
  mem_support_selectElem x := by induction n with
  | zero => simp
  | succ m ih =>
    stop
    simp [ih]
    use x.pop, x.back
    apply Vector.push_pop_back
  probOutput_selectElem_eq x y := by induction n with
  | zero =>
    have : x=y := by
      apply Vector.ext
      rintro i hi
      linarith
    simp [this]
    -- have : Subsingleton (Vector α 0) := by
    --   apply Vector.ext
    --   rintro i hi
    --   linarith
    -- Subsingleton
    -- simp [this]
  | succ m ih =>
    stop
    rw [← Vector.push_pop_back x, ← Vector.push_pop_back y]
    simp [probOutput_seq_map_vec_push_eq_mul, -Vector.push_pop_back]
    unfold uniformOfFintype
    rw [SampleableType.probOutput_selectElem_eq x.back y.back]
    exact congrFun (congrArg HMul.hMul (ih x.pop y.pop)) Pr[= y.back | SampleableType.selectElem]
  probFailure_selectElem := by
    stop
    induction n with
    | zero => simp
    | succ m ih => simp [ih, probFailure_seq]

/-- Select a uniform element from `Matrix α n` by independently selecting `α` at each index. -/
instance (α : Type) (n m : ℕ) [SampleableType α] : SampleableType (Matrix (Fin n) (Fin m) α) where
  -- selectElem := (fun x ↦ (fun i j ↦ x)) <$> ($ᵗ α)
  selectElem := by induction n with
  | zero => exact pure (Matrix.of ![])
  | succ n ihn => exact do
    let top ← $ᵗ Vector α m
    let bot ← ihn
    -- return Matrix.of (Fin.snoc top bot.get)
    return Fin.cons top.get bot
    -- return (Matrix.of (fun i j ↦ if h : i ≠ Fin.last n then top (Fin.castPred i h) j else bot[j]))
  mem_support_selectElem x := by induction n with
  | zero =>
    apply Matrix.ext
    rintro i j
    exact False.elim (IsEmpty.false i)
  | succ p ih =>
    simp at *
    use Vector.ofFn (x 0), (Fin.tail x); constructor
    simp [ih]
    have : (Vector.ofFn (x 0)).get = x 0 := by
      ext i
      simp [Vector.get]
    simp [Fin.cons_self_tail, this]
  probOutput_selectElem_eq x y := by induction n with
  | zero =>
    simp
    sorry
  | succ m ih =>
    sorry
  probFailure_selectElem := by
    stop
    induction n with
    | zero => simp
    | succ m ih =>
      simp [ih, probFailure_seq, probFailure_pure, probFailure_ite]
      sorry

end instances

section bool

-- TODO: generalize this lemma
/--
Given an independent probabilistic computation `ob : ProbComp Bool`, the probability that its
output `b'` differs from a uniformly chosen boolean `b` is the same as the probability that they
are equal. In other words, `P(b ≠ b') = P(b = b')` where `b` is uniform.
-/
lemma probOutput_uniformBool_not_decide_eq_decide {ob : ProbComp Bool} :
    Pr[= true | do let b ←$ᵗ Bool; let b' ← ob; return !decide (b = b')] =
      Pr[= true | do let b ←$ᵗ Bool; let b' ← ob; return decide (b = b')] := by
  stop
  simp [probOutput_bind_eq_sum_fintype, add_comm]

end bool

end SampleableType

end OracleComp
