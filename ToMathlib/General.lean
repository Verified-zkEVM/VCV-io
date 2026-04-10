/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Vector.Defs
public import Mathlib.Probability.Distributions.Uniform

/-!
# Lemmas to be Ported to Mathlib

This file gives a centralized location to add lemmas that belong better
in general mathlib than in the project itself.
-/

@[expose] public section

universe u v w

namespace ENNReal

lemma one_sub_one_sub_mul_one_sub {x y : ℝ≥0∞} (hx : x ≤ 1) (hy : y ≤ 1) :
    1 - (1 - x) * (1 - y) = x + y - x * y := by
  have hxy : x * y ≤ x + y := by
    have hxy_le_x : x * y ≤ x := mul_le_of_le_one_right' hy
    have hxy_le_y : x * y ≤ y := by
      apply mul_le_of_le_one_left (by positivity) hx;
    exact le_trans hxy_le_x ( le_add_of_nonneg_right <| by positivity )
  have hxy' : (1 - x) * (1 - y) ≤ 1 := by
    calc (1 - x) * (1 - y) ≤ 1 * 1 :=
          mul_le_mul' (tsub_le_self) (tsub_le_self)
        _ = 1 := one_mul 1
  rw [← ENNReal.toReal_eq_toReal_iff' (by aesop) (by aesop),
    ENNReal.toReal_sub_of_le, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le,
    ENNReal.toReal_sub_of_le, ENNReal.toReal_sub_of_le, ENNReal.toReal_add, ENNReal.toReal_mul]
  · simp
    linarith
  all_goals try aesop

lemma list_prod_natCast_ne_top {ι : Type*} (f : ι → ℕ) (js : List ι) :
    (js.map (fun j => (f j : ℝ≥0∞))).prod ≠ ⊤ := by
  have h : (js.map (fun j => (f j : ℝ≥0∞))).prod = ↑((js.map f).prod) := by
    induction js with
    | nil => simp
    | cons j js ih => simp [ih, Nat.cast_mul]
  rw [h]; exact natCast_ne_top _

/-- Real bridge for truncated `ENNReal` subtraction:
`(a - b).toReal` is bounded by `|a.toReal - b.toReal|`. -/
lemma toReal_sub_le_abs_toReal_sub (a b : ℝ≥0∞) :
    (a - b).toReal ≤ |a.toReal - b.toReal| := by
  by_cases ha : a = ⊤
  · by_cases hb : b = ⊤
    · simp [ha, hb]
    · simp [ha, hb]
  · by_cases h : b ≤ a
    · rw [ENNReal.toReal_sub_of_le h ha]
      exact le_abs_self _
    · have h' : a ≤ b := le_of_not_ge h
      rw [tsub_eq_zero_of_le h']
      exact abs_nonneg _

open Finset in
/-- The Gauss sum `∑_{k=0}^{n-1} k/N ≤ n²/(2N)`, the arithmetic core of the birthday bound. -/
lemma gauss_sum_inv_le (n : ℕ) (N : ℝ≥0∞) (_hN : 0 < N) :
    ∑ k ∈ range n, ((k : ℕ) : ℝ≥0∞) * N⁻¹ ≤
      (n ^ 2 : ℝ≥0∞) / (2 * N) := by
  rw [← Finset.sum_mul]
  have hnat : 2 * (∑ k ∈ range n, k) ≤ n ^ 2 := by
    have := Finset.sum_range_id_mul_two n; nlinarith [Nat.sub_le n 1]
  have henn : 2 * (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 := by
    have hcast : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((∑ k ∈ range n, k : ℕ) : ℝ≥0∞) := by
      simp [Nat.cast_sum]
    rw [hcast, show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_num,
      show (n : ℝ≥0∞) ^ 2 = ((n ^ 2 : ℕ) : ℝ≥0∞) from by push_cast; ring,
      ← Nat.cast_mul]
    exact_mod_cast hnat
  have hle : (∑ k ∈ range n, (k : ℝ≥0∞)) ≤ (n : ℝ≥0∞) ^ 2 / 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
    rwa [mul_comm]
  calc (∑ k ∈ range n, (k : ℝ≥0∞)) * N⁻¹
      ≤ ((n : ℝ≥0∞) ^ 2 / 2) * N⁻¹ := mul_le_mul_left hle N⁻¹
    _ = (n : ℝ≥0∞) ^ 2 / (2 * N) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
            (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
        ring

open Finset in
/-- Tight Gauss sum: `∑_{k=0}^{n-1} k/N = n*(n-1)/(2N)`. -/
lemma gauss_sum_inv_eq (n : ℕ) (N : ℝ≥0∞) :
    ∑ k ∈ range n, ((k : ℕ) : ℝ≥0∞) * N⁻¹ =
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * N) := by
  rw [← Finset.sum_mul]
  have hnat : (∑ k ∈ range n, k) * 2 = n * (n - 1) :=
    Finset.sum_range_id_mul_two n
  have henn : 2 * (∑ k ∈ range n, (k : ℝ≥0∞)) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    have hcast : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((∑ k ∈ range n, k : ℕ) : ℝ≥0∞) := by
      simp [Nat.cast_sum]
    rw [hcast, show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_num, ← Nat.cast_mul]
    congr 1; omega
  have heq : (∑ k ∈ range n, (k : ℝ≥0∞)) = ((n * (n - 1) : ℕ) : ℝ≥0∞) / 2 := by
    rw [ENNReal.eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    exact henn
  calc (∑ k ∈ range n, (k : ℝ≥0∞)) * N⁻¹
      = ((n * (n - 1) : ℕ) : ℝ≥0∞) / 2 * N⁻¹ := by rw [heq]
    _ = ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * N) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
            (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))]
        ring

/-- `a/(2N) + b/N = (a + 2b)/(2N)` for natural-number casts to `ℝ≥0∞`. -/
lemma add_div_two_mul_nat (a b N : ℕ) :
    ((a : ℕ) : ℝ≥0∞) / (2 * N) +
      ((b : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ =
    ((a + 2 * b : ℕ) : ℝ≥0∞) / (2 * N) := by
  set D := (2 * (N : ℝ≥0∞))
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [mul_comm (((b : ℕ) : ℝ≥0∞)) ((N : ℝ≥0∞)⁻¹)]
  have hD_inv : (N : ℝ≥0∞)⁻¹ = D⁻¹ * 2 := by
    simp only [D]
    rw [ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)),
      mul_comm (2 : ℝ≥0∞)⁻¹ _, mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), mul_one]
  rw [hD_inv, mul_assoc, ← mul_add]
  congr 1
  push_cast
  ring

end ENNReal

open Finset in
/-- Updating one coordinate by `+1` increases the total sum by exactly one. -/
lemma sum_update_succ_count {ι : Type} [Fintype ι] [DecidableEq ι]
    (counts : ι → ℕ) (i : ι) :
    ∑ j : ι, Function.update counts i (counts i + 1) j =
      (∑ j : ι, counts j) + 1 := by
  classical
  calc
    ∑ j : ι, Function.update counts i (counts i + 1) j =
        Function.update counts i (counts i + 1) i +
          Finset.sum (Finset.univ.erase i)
            (fun j : ι => Function.update counts i (counts i + 1) j) := by
          symm
          exact Finset.univ.add_sum_erase
            (f := fun j : ι => Function.update counts i (counts i + 1) j) (Finset.mem_univ i)
    _ = counts i + 1 + Finset.sum (Finset.univ.erase i) (fun j : ι => counts j) := by
          simp only [Function.update_self]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    _ = counts i + Finset.sum (Finset.univ.erase i) (fun j : ι => counts j) + 1 := by
          omega
    _ = (∑ j : ι, counts j) + 1 := by
          rw [← Finset.univ.add_sum_erase (f := fun j : ι => counts j) (Finset.mem_univ i)]

@[simp, grind =]
lemma fst_map_prod_map {m : Type u → Type v} [Functor m] [LawfulFunctor m] {α β γ δ : Type u}
    (mx : m (α × β)) (f : α → γ) (g : β → δ) :
    Prod.fst <$> Prod.map f g <$> mx = (f ∘ Prod.fst) <$> mx := by
  simp [Functor.map_map]; rfl

@[simp, grind =]
lemma snd_map_prod_map {m : Type u → Type v} [Functor m] [LawfulFunctor m] {α β γ δ : Type u}
    (mx : m (α × β)) (f : α → γ) (g : β → δ) :
    Prod.snd <$> Prod.map f g <$> mx = (g ∘ Prod.snd) <$> mx := by
  simp [Functor.map_map]; rfl

@[simp]
lemma List.prod_map_const {α M : Type*} [CommMonoid M] (xs : List α) (c : M) :
    (xs.map (fun _ => c)).prod = c ^ xs.length := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.prod_cons, ih,
      List.length_cons, pow_succ, mul_comm]

section sum_thing

open Filter Finset Function Topology SummationFilter

@[to_additive (attr := simp)]
theorem tprod_ite_eq' {α β} [CommMonoid α] [TopologicalSpace α]
    (b : β) [DecidablePred (b = ·)] (a : α)
    (L := unconditional β) [L.LeAtTop] :
    ∏'[L] b', (if b = b' then a else 1) = a := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb', @eq_comm _ b]

@[to_additive (attr := simp)]
theorem tprod_ite_eq_apply {α β} [CommMonoid α] [TopologicalSpace α]
    (b : β) [DecidablePred (· = b)] (f : β → α)
    (L := unconditional β) [L.LeAtTop] :
    ∏'[L] b', (if b' = b then f b' else 1) = f b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive (attr := simp)]
theorem tprod_ite_eq_apply' {α β} [CommMonoid α] [TopologicalSpace α]
    (b : β) [DecidablePred (b = ·)] (f : β → α)
    (L := unconditional β) [L.LeAtTop] :
    ∏'[L] b', (if b = b' then f b' else 1) = f b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb', @eq_comm _ b]

end sum_thing

lemma Fin.ofNat_Icc_iff {n m : ℕ} (h : n < m) (x : Fin (m + 1)) :
    (Fin.ofNat (m + 1) n ≤ x ∧ x ≤ Fin.ofNat (m + 1) m) ↔ n ≤ x.val := by
  constructor
  · intro ⟨h1, _⟩
    have h1' : (Fin.ofNat (m + 1) n).val ≤ x.val := h1
    simp only [Fin.val_ofNat, Nat.mod_eq_of_lt (show n < m + 1 by omega)] at h1'
    exact h1'
  · intro hx
    exact ⟨show (Fin.ofNat (m + 1) n).val ≤ x.val by
              simp only [Fin.val_ofNat, Nat.mod_eq_of_lt (show n < m + 1 by omega)]; exact hx,
           show x.val ≤ (Fin.ofNat (m + 1) m).val by
              simp only [Fin.val_ofNat, Nat.mod_eq_of_lt (show m < m + 1 by omega)]; omega⟩

lemma PMF.apply_eq_one_sub_tsum_ite {α} [DecidableEq α] (p : PMF α) (x : α) :
    p x = 1 - (∑' y, if y = x then 0 else p y) := by
  rw [← p.tsum_coe]
  rw [Summable.tsum_eq_add_tsum_ite' x ENNReal.summable]
  refine ENNReal.eq_sub_of_add_eq' ?_ rfl
  simp only [ne_eq, ENNReal.add_eq_top, apply_ne_top, false_or]
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  refine le_trans ?_ (le_of_eq p.tsum_coe)
  refine ENNReal.tsum_le_tsum fun x => ?_
  aesop

open Classical in
/-- Two `PMF` that agree on all but one point are actually equal. -/
lemma PMF.ext_forall_ne {α} {p q : PMF α} (x : α)
    (h : ∀ y ≠ x, p y = q y) : p = q := by
  refine PMF.ext fun y => ?_
  by_cases hy : y = x
  · rw [p.apply_eq_one_sub_tsum_ite, q.apply_eq_one_sub_tsum_ite]
    subst hy
    simp_all only [ne_eq, not_false_eq_true]
  · refine h y hy

section abs

variable {G : Type*} [CommRing G] [LinearOrder G] [IsStrictOrderedRing G] {a b : G}

lemma mul_abs_of_nonneg (h : 0 ≤ a) : a * |b| = |a * b| := by
  rw [abs_mul, abs_of_nonneg h]

lemma abs_mul_of_nonneg (h : 0 ≤ b) : |a| * b = |a * b| := by
  rw [abs_mul, abs_of_nonneg h]

lemma mul_abs_of_nonpos (h : a < 0) : a * |b| = - |a * b| := by
  rw (occs := [1]) [← sign_mul_abs a]
  rw [abs_mul, neg_eq_neg_one_mul, mul_assoc]
  congr; simp [h]

lemma abs_mul_of_nonpos (h : b < 0) : |a| * b = - |a * b| := by
  rw (occs := [1]) [← sign_mul_abs b]
  rw [abs_mul, neg_eq_neg_one_mul, ← mul_assoc, mul_comm |a| _, mul_assoc]
  congr; simp [h]

end abs

open BigOperators ENNReal

lemma Fintype.sum_inv_card (α : Type*) [Fintype α] [Nonempty α] :
  Finset.sum Finset.univ (fun _ ↦ (Fintype.card α)⁻¹ : α → ℝ≥0∞) = 1 := by
  rw [Finset.sum_eq_card_nsmul (fun _ _ ↦ rfl), Finset.card_univ,
    nsmul_eq_mul, ENNReal.mul_inv_cancel] <;> simp

section List.Vector

open List (Vector)

@[simp] -- mathlib?
lemma vector_eq_nil {α : Type*} (xs : List.Vector α 0) : xs = Vector.nil :=
  List.Vector.ext (IsEmpty.forall_iff.2 True.intro)

lemma List.injective2_cons {α : Type*} : Function.Injective2 (List.cons (α := α)) := by
  simp [Function.Injective2]

lemma Vector.injective2_cons {α : Type*} {n : ℕ} :
    Function.Injective2 (Vector.cons : α → List.Vector α n → List.Vector α (n + 1)) := by
  simp [Function.Injective2, Vector.eq_cons_iff]

@[simp]
lemma Vector.getElem_eq_get {α n} (xs : List.Vector α n) (i : ℕ) (h : i < n) :
  xs[i]'h = xs.get ⟨i, h⟩ := rfl

lemma List.Vector.toList_eq_ofFn_get {α : Type} {n : ℕ}
    (xs : List.Vector α n) : xs.toList = List.ofFn xs.get := by
  apply List.ext_getElem
  · simp [List.Vector.toList_length]
  · intro i hi1 hi2
    rw [show xs.toList[i] = xs.get ⟨i, by simpa [List.Vector.toList_length] using hi1⟩ by
        simpa using (List.Vector.get_eq_get_toList xs
          ⟨i, by simpa [List.Vector.toList_length] using hi1⟩).symm]
    simp [List.getElem_ofFn (f := xs.get) (i := i) hi2]

end List.Vector

lemma Prod.mk.injective2 {α β : Type*} :
    Function.Injective2 (Prod.mk : α → β → α × β) := by
  simp [Function.Injective2]

lemma Function.injective2_swap_iff {α β γ : Type*} (f : α → β → γ) :
    (Function.swap f).Injective2 ↔ f.Injective2 :=
  ⟨fun h _ _ _ _ h' ↦ and_comm.1 (h h'), fun h _ _ _ _ h' ↦ and_comm.1 (h h')⟩

@[simp] theorem Finset.image_const_univ {α β} [DecidableEq β] [Fintype α]
    [Nonempty α] (b : β) : (Finset.univ.image fun _ : α => b) = singleton b :=
  Finset.univ.image_const Finset.univ_nonempty b

/-- Summing `1` over list indices that satisfy a predicate is just `countP` applied to `p`. -/
lemma List.countP_eq_sum_fin_ite {α : Type*} (xs : List α) (p : α → Bool) :
    (∑ i : Fin xs.length, if p xs[i] then 1 else 0) = xs.countP p := by
  induction xs with
  | nil => {
    simp only [length_nil, Finset.univ_eq_empty, Finset.sum_boole, Fin.getElem_fin,
      Finset.filter_empty, Finset.card_empty, CharP.cast_eq_zero, countP_nil]
  }
  | cons x xs h => {
    rw [List.countP_cons, ← h]
    refine (Fin.sum_univ_succ _).trans ((add_comm _ _).trans ?_)
    simp
  }

lemma List.card_filter_getElem_eq {α : Type*} [DecidableEq α]
    (xs : List α) (x : α) :
    (Finset.filter (fun i : Fin (xs.length) ↦ xs[i] = x) Finset.univ).card =
      xs.count x := by
  rw [List.count, ← List.countP_eq_sum_fin_ite]
  simp only [Fin.getElem_fin, beq_iff_eq, Finset.sum_boole, Nat.cast_id]

lemma List.countP_finRange_getElem {α : Type} (l : List α) (p : α → Bool) :
    (List.finRange l.length).countP (fun i => p l[↑i]) = l.countP p := by
  conv_rhs => rw [← List.map_getElem_finRange l]
  rw [List.countP_map]; rfl

lemma Fin.card_eq_countP_mem {n : ℕ} (s : Finset (Fin n)) :
    s.card = Fin.countP (· ∈ s) := by
  simp [Fin.countP_eq_countP_map_finRange, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]

lemma Array.card_eq_countP {α : Type} (as : Array α)
    (p : α → Prop) [DecidablePred p] :
    ({i : Fin as.size | p as[↑i]} : Finset (Fin as.size)).card =
      as.countP (fun a => decide (p a)) := by
  rw [← Array.countP_toList]
  rw [← List.map_getElem_finRange as.toList, List.countP_map]
  have hcard := Fin.card_eq_countP_mem ({i : Fin as.size | p as[↑i]} : Finset (Fin as.size))
  rw [Fin.countP_eq_countP_map_finRange] at hcard
  simpa [Function.comp, Array.length_toList] using hcard

section VectorCounting

variable {α : Type}

lemma _root_.Vector.card_eq_countP {n : ℕ}
    (xs : Vector α n) (p : α → Prop) [DecidablePred p] :
    ({i : Fin n | p xs[↑i]} : Finset (Fin n)).card =
      xs.countP (fun a => decide (p a)) := by
  rcases xs with ⟨as, hs⟩
  calc
    ({i : Fin n | p as[↑i]} : Finset (Fin n)).card =
        ({i : Fin as.size | p as[↑i]} : Finset (Fin as.size)).card := by
          refine Finset.card_nbij (i := Fin.cast hs.symm) ?hi ?hinj ?hsurj
          · intro i hi
            simp at hi ⊢
            simpa [Fin.cast_val_eq_self] using hi
          · intro i hi j hj hij
            exact Fin.cast_injective hs.symm hij
          · intro j hj
            refine ⟨Fin.cast hs j, ?_, ?_⟩
            · simp at hj ⊢
              simpa [Fin.cast_cast] using hj
            · simp
    _ = as.countP (fun a => decide (p a)) := Array.card_eq_countP as p
    _ = (Vector.mk as hs).countP (fun a => decide (p a)) := by simp [Vector.countP_mk]

lemma _root_.Vector.card_eq_count [DecidableEq α] {n : ℕ}
    (xs : Vector α n) (x : α) :
    ({i : Fin n | x = xs[↑i]} : Finset (Fin n)).card = xs.count x := by
  rw [Vector.count_eq_countP]
  have hbeq : (fun y : α => y == x) = fun y => decide (x = y) := by
    funext y
    simp [beq_eq_decide, eq_comm]
  rw [hbeq]
  simpa using (Vector.card_eq_countP xs (p := fun y => x = y))

end VectorCounting

section ListVectorCounting

lemma List.Vector.card_eq_countP {α : Type} {n : ℕ}
    (xs : List.Vector α n) (p : α → Prop) [DecidablePred p] :
    ({i : Fin n | p (xs.get i)} : Finset (Fin n)).card =
      xs.toList.countP (fun a => decide (p a)) := by
  let ys : _root_.Vector α n := _root_.Vector.ofFn xs.get
  have hcard : ({i : Fin n | p (xs.get i)} : Finset (Fin n)).card =
      ({i : Fin n | p ys[↑i]} : Finset (Fin n)).card := by
    simp [ys, _root_.Vector.getElem_ofFn]
  have hcount : ys.countP (fun a => decide (p a)) =
      xs.toList.countP (fun a => decide (p a)) := by
    rw [← _root_.Vector.countP_toList]
    simp [ys, _root_.Vector.toList_ofFn, List.Vector.toList_eq_ofFn_get]
  calc
    ({i : Fin n | p (xs.get i)} : Finset (Fin n)).card =
        ({i : Fin n | p ys[↑i]} : Finset (Fin n)).card := hcard
    _ = ys.countP (fun a => decide (p a)) := _root_.Vector.card_eq_countP ys p
    _ = xs.toList.countP (fun a => decide (p a)) := hcount

lemma List.Vector.card_eq_count {α : Type} [DecidableEq α] {n : ℕ}
    (xs : List.Vector α n) (x : α) :
    ({i : Fin n | x = xs.get i} : Finset (Fin n)).card = xs.toList.count x := by
  have h := List.Vector.card_eq_countP xs (p := fun a => x = a)
  have hcount : xs.toList.count x = xs.toList.countP (fun a => decide (x = a)) := by
    rw [List.count_eq_countP]
    congr 1
    funext y
    simp [BEq.beq, eq_comm]
  exact h.trans hcount.symm

end ListVectorCounting

@[simp] lemma Finset.sum_boole' {ι β : Type*} [AddCommMonoid β] (r : β)
    (p) [DecidablePred p] (s : Finset ι) :
    (∑ x ∈ s, if p x then r else 0 : β) = (s.filter p).card • r :=
calc (∑ x ∈ s, if p x then r else 0 : β) = (∑ x ∈ s, if p x then 1 else 0 : ℕ) • r :=
    by simp only [← Finset.sum_nsmul_assoc, ite_smul, one_smul, zero_smul]
  _ = (s.filter p).card • r := by simp only [sum_boole, Nat.cast_id]

@[simp]
lemma Finset.count_toList {α} [DecidableEq α] (x : α) (s : Finset α) :
    s.toList.count x = if x ∈ s then 1 else 0 := by
  by_cases hx : x ∈ s
  · simp only [hx, ↓reduceIte]
    refine List.count_eq_one_of_mem ?_ ?_
    · exact nodup_toList s
    · simp [hx]
  · simp only [hx, ↓reduceIte]
    refine List.count_eq_zero_of_not_mem ?_
    simp [hx]

lemma BitVec.toFin_bijective (n : ℕ) :
    Function.Bijective (BitVec.toFin : BitVec n → Fin (2 ^ n)) := by
  refine ⟨?_, ?_⟩
  · intro i j h
    cases i
    cases j
    simp at h
    simp [h]
  · intro i
    simp only [exists_apply_eq_apply]

instance (n : ℕ) : Fintype (BitVec n) := by
  refine Fintype.ofBijective (α := Fin (2 ^ n)) ?_ ?_
  · refine fun x ↦ ?_
    refine BitVec.ofFin x
  · refine ⟨?_, ?_⟩
    · intro i j
      simp only [BitVec.ofFin.injEq, imp_self]
    · intro i
      simp only [exists_apply_eq_apply]

@[simp]
lemma card_bitVec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n :=
  (Fintype.card_of_bijective (BitVec.toFin_bijective _)).trans <| Fintype.card_fin (2 ^ n)

@[simp]
lemma BitVec.xor_self_xor {n : ℕ} (x y : BitVec n) : x ^^^ (x ^^^ y) = y := by
  rw [← BitVec.xor_assoc, xor_self, zero_xor]

instance (α : Type) [Inhabited α] : Inhabited {f : α → α // f.Bijective} :=
  ⟨id, Function.bijective_id⟩


namespace Vector

@[simp]
lemma heq_of_toArray_eq_of_size_eq {α} {m n : ℕ} {a : Vector α m} {b : Vector α n}
    (h : a.toArray = b.toArray) (h' : m = n) : HEq a b := by
  subst h'
  simp_all only [Vector.toArray_inj, heq_eq_eq]

-- Induction principles for vectors

def cases {α} {motive : {n : ℕ} → Vector α n → Sort*} (v_empty : motive #v[])
  (v_insert : {n : ℕ} → (hd : α) → (tl : Vector α n) → motive (tl.insertIdx 0 hd)) {m : ℕ} :
    (v : Vector α m) → motive v := match hm : m with
  | 0 => fun v => match v with | ⟨⟨[]⟩, rfl⟩ => v_empty
  | n + 1 => fun v => match hv : v with
    | ⟨⟨hd :: tl⟩, hSize⟩ => by
      simpa [Vector.insertIdx] using v_insert hd ⟨⟨tl⟩, by simpa using hSize⟩

@[elab_as_elim]
def induction {α} {motive : {n : ℕ} → Vector α n → Sort*} (v_empty : motive #v[])
  (v_insert : {n : ℕ} → (hd : α) → (tl : Vector α n) → motive tl → motive (tl.insertIdx 0 hd))
    {m : ℕ} : (v : Vector α m) → motive v := by induction m with
  | zero => exact fun v => match v with | ⟨⟨[]⟩, rfl⟩ => v_empty
  | succ n ih => exact fun v => match v with
    | ⟨⟨hd :: tl⟩, hSize⟩ => by
      simpa [Vector.insertIdx] using
        v_insert hd ⟨⟨tl⟩, by simpa using hSize⟩ (ih ⟨⟨tl⟩, by simpa using hSize⟩)

def cases₂ {α β} {motive : {n : ℕ} → Vector α n → Vector β n → Sort*}
  (v_empty : motive #v[] #v[])
  (v_insert : {n : ℕ} → (hd : α) → (tl : Vector α n) → (hd' : β) → (tl' : Vector β n) →
    motive (tl.insertIdx 0 hd) (tl'.insertIdx 0 hd')) {m : ℕ} :
    (v : Vector α m) → (v' : Vector β m) → motive v v' := match hm : m with
  | 0 => fun v v' => match v, v' with | ⟨⟨[]⟩, rfl⟩, ⟨⟨[]⟩, rfl⟩ => v_empty
  | n + 1 => fun v v' => match hv : v, hv' : v' with
    | ⟨⟨hd :: tl⟩, hSize⟩, ⟨⟨hd' :: tl'⟩, hSize'⟩ => by
      simpa [Vector.insertIdx] using
        v_insert hd ⟨⟨tl⟩, by simpa using hSize⟩ hd' ⟨⟨tl'⟩, by simpa using hSize'⟩

@[elab_as_elim]
def induction₂ {α β} {motive : {n : ℕ} → Vector α n → Vector β n → Sort*}
  (v_empty : motive #v[] #v[])
  (v_insert : {n : ℕ} → (hd : α) → (tl : Vector α n) → (hd' : β) → (tl' : Vector β n) →
    motive tl tl' → motive (tl.insertIdx 0 hd) (tl'.insertIdx 0 hd')) {m : ℕ} :
    (v : Vector α m) → (v' : Vector β m) → motive v v' := by induction m with
  | zero => exact fun v v' => match v, v' with | ⟨⟨[]⟩, rfl⟩, ⟨⟨[]⟩, rfl⟩ => v_empty
  | succ n ih => exact fun v v' => match hv : v, hv' : v' with
    | ⟨⟨hd :: tl⟩, hSize⟩, ⟨⟨hd' :: tl'⟩, hSize'⟩ => by
      simpa [Vector.insertIdx] using
        v_insert hd ⟨⟨tl⟩, by simpa using hSize⟩ hd' ⟨⟨tl'⟩, by simpa using hSize'⟩
        (ih ⟨⟨tl⟩, by simpa using hSize⟩ ⟨⟨tl'⟩, by simpa using hSize'⟩)


section add
-- Define vector addition more generally

instance {α : Type} {n : ℕ} [Add α] : Add (Vector α n) where
  add v1 v2 := Vector.ofFn (v1.get + v2.get)

instance {α : Type} {n : ℕ} [Zero α] : Zero (Vector α n) where
  zero := Vector.ofFn (0)

@[simp]
theorem vectorofFn_get {α : Type} {n : ℕ} (v : Fin n → α) : (Vector.ofFn v).get = v := by
  ext i
  apply Vector.getElem_ofFn

@[simp]
theorem vectorAdd_get {α : Type} {n : ℕ} [Add α] [Zero α]
 (vx : Vector α n) (vy : Vector α n)
 : (vx + vy).get = vx.get + vy.get := by
  change (Vector.ofFn (vx.get + vy.get)).get = vx.get + vy.get
  simp

end add

end Vector

open Classical in
lemma tsum_option {α β : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] [T2Space α]
    (f : Option β → α) (hf : Summable (Function.update f none 0)) :
    ∑' x : Option β, f x = f none + ∑' x : β, f (some x) := by
  refine (Summable.tsum_eq_add_tsum_ite' none hf).trans ?_
  refine congr_arg (f none + ·) ?_
  refine tsum_eq_tsum_of_ne_zero_bij (fun x ↦ some x.1) ?_ ?_ ?_
  · intro x y
    simp [SetCoe.ext_iff]
  · intro x
    cases x <;> simp
  · simp

@[simp]
lemma PMF.monad_pure_eq_pure {α : Type u} (x : α) :
    (Pure.pure x : PMF α) = PMF.pure x := rfl

@[simp]
lemma PMF.monad_bind_eq_bind {α β : Type u}
      (p : PMF α) (q : α → PMF β) : p >>= q = p.bind q := rfl

theorem PMF.bind_eq_zero {α β : Type _} {p : PMF α} {f : α → PMF β} {b : β} :
    (p >>= f) b = 0 ↔ ∀ a, p a = 0 ∨ f a b = 0 := by simp

theorem PMF.heq_iff {α β : Type u} {pa : PMF α} {pb : PMF β} (h : α = β) :
    HEq pa pb ↔ ∀ x, pa x = pb (cast h x) := by
  subst h; simp only [heq_eq_eq, cast_eq]; constructor <;> intro h'
  · intro x; rw [h']
  · ext x; rw [h' x]

theorem Option.cast_eq_some_iff {α β : Type u} {x : Option α} {b : β} (h : α = β) :
    cast (congrArg Option h) x = some b ↔ x = some (cast h.symm b) := by
  subst h; simp only [cast_eq]

theorem PMF.uniformOfFintype_cast (α β : Type _) [ha : Fintype α] [Nonempty α]
    [hb : Fintype β] [Nonempty β] (h : α = β) :
      cast (congrArg PMF h) (PMF.uniformOfFintype α) = @PMF.uniformOfFintype β _ _ := by
  subst h
  ext x
  simp only [cast_eq, uniformOfFintype_apply, inv_inj, Nat.cast_inj]
  exact @Fintype.card_congr α α ha hb (Equiv.refl α)

open Classical in
lemma PMF.uniformOfFintype_map_of_bijective {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → β) (hf : Function.Bijective f) :
    (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  have heq := Fintype.card_congr (Equiv.ofBijective f hf)
  ext x; obtain ⟨a, rfl⟩ := hf.2 x
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, heq, hf.1.eq_iff, eq_comm (a := a)]
  convert tsum_ite_eq a (fun _ : α => ((Fintype.card β : ENNReal)⁻¹))

open Classical in
/-- This doesn't get applied properly without `Classical` so add with high priority. -/
@[simp high] lemma PMF.some_map_apply_some {α} (p : PMF α) (x : α) :
    (p.map Option.some) (some x) = p x := by simp

theorem tsum_cast {α β : Type u} {f : α → ENNReal} {g : β → ENNReal}
    (h : α = β) (h' : ∀ a, f a = g (cast h a)) :
      (∑' (a : α), f a) = (∑' (b : β), g b) := by
  subst h; simp [h']

/-- Monadic analog of `Fin.ofFn`: given `f : Fin n → m α`, runs each computation
in order and collects the results as a function `Fin n → α`. This is the
`Fin n → α` counterpart of Mathlib's `Vector.mOfFn`. -/
def Fin.mOfFn {m : Type u → Type v} [Monad m] {α : Type u} :
    (n : ℕ) → (Fin n → m α) → m (Fin n → α)
  | 0, _ => return Fin.elim0
  | n + 1, f => do
    let a ← f 0
    let rest ← Fin.mOfFn n (fun i => f i.succ)
    return Fin.cons a rest

@[simp]
lemma List.foldlM_range {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {s : Type u} (n : ℕ) (f : s → Fin n → m s) (init : s) :
    List.foldlM f init (List.finRange n) =
      Fin.foldlM n f init := by
  revert init
  induction n with
  | zero => simp
  | succ n hn =>
      intro init
      simp only [List.finRange_succ, List.foldlM_cons, Fin.foldlM_succ]
      refine congr_arg (_ >>= ·) (funext fun x ↦ ?_)
      rw [← hn, List.foldlM_map]

lemma list_mapM_loop_eq {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α : Type w} {β : Type u} (xs : List α) (f : α → m β) (ys : List β) :
    List.mapM.loop f xs ys = (ys.reverse ++ ·) <$> List.mapM.loop f xs [] := by
  revert ys
  induction xs with
  | nil => simp [List.mapM.loop]
  | cons x xs h =>
      intro ys
      simp only [List.mapM.loop, map_bind]
      refine congr_arg (f x >>= ·) (funext fun x ↦ ?_)
      simp [h (x :: ys), h [x]]

/-! ### `forIn` / `foldlM` bridge for imperative-style loops

Lean's `for`/`let mut` syntax desugars to `List.forIn` with `MProd` state and
`ForInStep.yield` continuations, while functional-style code uses `List.foldlM`
with `Prod` state. The lemmas below bridge these two representations.

For a single mutable variable (no `MProd` wrapper), use Mathlib's
`List.forIn_yield_eq_foldlM` directly. -/

/-- A `for`/`let mut` loop with two mutable variables (desugared to `forIn` over
`MProd` state with `ForInStep.yield` in every branch) is equivalent to `foldlM`
with `Prod` state. This bridges two impedance mismatches at once:

1. `forIn` with yield-only body ↔ `foldlM`
2. `MProd` state from `let mut` desugaring ↔ `Prod` state -/
theorem List.forIn_mprod_yield_eq_foldlM
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α : Type w} {β γ : Type u} (l : List α) (b₀ : β) (c₀ : γ)
    (f : α → MProd β γ → m (ForInStep (MProd β γ)))
    (g : β × γ → α → m (β × γ))
    (hfg : ∀ a b c, f a ⟨b, c⟩ = do
      let r ← g (b, c) a; pure (.yield ⟨r.1, r.2⟩)) :
    (do let r ← forIn l ⟨b₀, c₀⟩ f; pure (r.fst, r.snd)) =
    l.foldlM g (b₀, c₀) := by
  suffices ∀ (b : β) (c : γ),
    (do let r ← forIn l ⟨b, c⟩ f; pure (r.fst, r.snd)) = l.foldlM g (b, c) from
    this b₀ c₀
  intro b c
  induction l generalizing b c with
  | nil => simp [List.forIn_nil, List.foldlM_nil]
  | cons x xs ih =>
    rw [List.forIn_cons, List.foldlM_cons, hfg]
    simp only [bind_assoc, pure_bind]
    congr 1; funext ⟨b', c'⟩
    exact ih b' c'
