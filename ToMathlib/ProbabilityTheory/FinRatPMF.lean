/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.FinEnum
public import Mathlib.Data.NNRat.BigOperators
public import Std.Data.HashMap.Lemmas
public import ToMathlib.Control.Monad.Hom

/-!
# Probability mass functions with finite support and non-negative rational weights

This is a special case of `PMF` that suffices for denotational semantics of `OracleComp` with finite
oracle specifications.

## Design

We use a two-layer approach:

* `FinRatPMF.Raw α` is an array-based representation storing pairs `(a, p)` of outcomes and
  probabilities. It has a computable `Monad` and `LawfulMonad` instance but non-canonical equality:
  two values representing the same distribution may differ in array order or duplicate entries.

* `FinRatPMF α` is the quotient of `FinRatPMF.Raw α` by distributional equality (`SameDist`).
  It has canonical equality (two values are equal iff they define the same distribution) and a
  `LawfulMonad` instance (necessarily `noncomputable` since `bind` must extract from the quotient).

For computation, use `FinRatPMF.Raw`. For reasoning about distributional equality, use `FinRatPMF`.
Both connect to Mathlib's `PMF` via `toPMF`.
-/

@[expose] public section

universe u

namespace FinRatPMF

/-! ## Raw representation -/

/-- Raw probability mass function with finite support and non-negative rational weights.

Stores an array of `(outcome, weight)` pairs whose weights sum to `1`. This representation is
computable but not canonical: many different `FinRatPMF.Raw` values can represent the same
probability distribution. -/
structure Raw (α : Type u) : Type u where
  data : Array (α × ℚ≥0)
  sum_eq_one : (data.toList.map Prod.snd).sum = 1

namespace Raw

variable {α β γ : Type u}

/-- View the raw array representation as a list, which is convenient for proofs. -/
def toList (p : Raw α) : List (α × ℚ≥0) := p.data.toList

def probOfList [DecidableEq α] (l : List (α × ℚ≥0)) (x : α) : ℚ≥0 :=
  (l.filter (fun a => a.1 = x) |>.map Prod.snd).sum

def supportOfList [DecidableEq α] (l : List (α × ℚ≥0)) : Finset α :=
  (l.filter (fun a => a.2 ≠ 0)).map Prod.fst |>.toFinset

private lemma sum_eq_zero_of_forall_eq_zero (l : List ℚ≥0)
    (h : ∀ q ∈ l, q = 0) : l.sum = 0 := by
  induction l with
  | nil => simp
  | cons q qs ih =>
    simp [h q (by simp), ih (by
      intro r hr
      exact h r (by simp [hr]))]

private lemma probOfList_ne_zero_of_mem [DecidableEq α] {l : List (α × ℚ≥0)} {x : α} {q : ℚ≥0}
    (hmem : (x, q) ∈ l) (hq : q ≠ 0) : probOfList l x ≠ 0 := by
  have hqmem : q ∈ (l.filter (fun a => a.1 = x)).map Prod.snd := by
    apply List.mem_map.2
    refine ⟨(x, q), ?_, rfl⟩
    simpa using hmem
  have hle : q ≤ probOfList l x := by
    simpa [probOfList] using
      (List.single_le_sum (fun _ _ => by exact zero_le _) q hqmem)
  exact (lt_of_lt_of_le (show 0 < q from pos_iff_ne_zero.mpr hq) hle).ne'

private lemma probOfList_eq_zero_of_not_mem_supportOfList [DecidableEq α]
    (l : List (α × ℚ≥0)) {x : α} (hx : x ∉ supportOfList l) : probOfList l x = 0 := by
  simp only [supportOfList, List.mem_toFinset, List.mem_map, List.mem_filter] at hx
  unfold probOfList
  apply sum_eq_zero_of_forall_eq_zero
  intro q hq
  rcases List.mem_map.1 hq with ⟨a, ha, rfl⟩
  have ha' : a ∈ l.filter (fun b => b.1 = x) := ha
  simp only [List.mem_filter] at ha'
  have hzero : a.2 = 0 := by
    by_contra hne
    exact hx ⟨a, ⟨ha'.1, by simpa using hne⟩, by simpa using ha'.2⟩
  exact hzero

private lemma mem_supportOfList_iff [DecidableEq α] (l : List (α × ℚ≥0)) (x : α) :
    x ∈ supportOfList l ↔ probOfList l x ≠ 0 := by
  constructor
  · intro hx
    rcases List.mem_toFinset.1 hx with hx
    rcases List.mem_map.1 hx with ⟨a, ha, hax⟩
    rcases List.mem_filter.1 ha with ⟨ha, hne⟩
    subst x
    exact probOfList_ne_zero_of_mem ha (by simpa using hne)
  · intro hx
    by_contra hnot
    exact hx (probOfList_eq_zero_of_not_mem_supportOfList l hnot)

private lemma supportOfList_eq_keys [DecidableEq α] {l : List (α × ℚ≥0)}
    (h : ∀ a ∈ l, a.2 ≠ 0) :
    supportOfList l = (l.map Prod.fst).toFinset := by
  ext x
  constructor
  · intro hx
    rcases List.mem_toFinset.1 hx with hx
    rcases List.mem_map.1 hx with ⟨a, ha, hax⟩
    rcases List.mem_filter.1 ha with ⟨ha, _⟩
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, ha, hax⟩)
  · intro hx
    rcases List.mem_toFinset.1 hx with hx
    rcases List.mem_map.1 hx with ⟨a, ha, hax⟩
    subst x
    exact List.mem_toFinset.2
      (List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, by simpa using h a ha⟩, rfl⟩)

@[ext] lemma ext {p q : Raw α} (h : p.data = q.data) : p = q := by
  cases p
  cases q
  cases h
  simp

lemma ext_toList {p q : Raw α} (h : p.toList = q.toList) : p = q := by
  apply ext
  simpa [Raw.toList] using congrArg List.toArray h

/-! ### Bind sum auxiliary lemma -/

private lemma bind_sum_aux (l : List (α × ℚ≥0)) (g : α → Raw β) :
    ((l.flatMap (fun (a, p) => (g a).toList.map (fun (b, q) => (b, p * q)))).map Prod.snd).sum
    = (l.map (fun (a, p) => p * ((g a).toList.map Prod.snd).sum)).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_map, Function.comp_def]
    rw [List.sum_map_mul_left]
    congr 1

/-! ### Monad operations -/

protected def pure (a : α) : Raw α := ⟨#[(a, 1)], by simp⟩

instance [Inhabited α] : Inhabited (Raw α) where
  default := Raw.pure default

instance [Repr α] : Repr (Raw α) where
  reprPrec p _ := repr (p.toList.map fun (a, q) => (reprStr a, (q : ℚ)))

instance [Repr α] : ToString (Raw α) where
  toString p := reprStr (p.toList.map fun (a, q) => (reprStr a, (q : ℚ)))

protected def bind (f : Raw α) (g : α → Raw β) : Raw β :=
  ⟨(f.toList.flatMap (fun (a, p) => (g a).toList.map (fun (b, q) => (b, p * q)))).toArray, by
    change ((f.toList.flatMap (fun (a, p) => (g a).toList.map (fun (b, q) => (b, p * q)))).map
      Prod.snd).sum = 1
    rw [bind_sum_aux]
    simp only [Raw.toList]
    simp_rw [Raw.sum_eq_one, mul_one]
    exact f.sum_eq_one⟩

instance : Monad Raw where
  pure := Raw.pure
  bind := Raw.bind

@[simp] lemma pure_toList (a : α) :
    (Pure.pure a : Raw α).toList = [(a, 1)] := by
  rfl

@[simp] lemma bind_toList (f : Raw α) (g : α → Raw β) :
    (f >>= g).toList =
      f.toList.flatMap (fun (a, p) => (g a).toList.map (fun (b, q) => (b, p * q))) := by
  change
    ((f.toList.flatMap (fun (a, p) => (g a).toList.map (fun (b, q) => (b, p * q)))).toArray).toList
      = _
  rw [List.toList_toArray]

instance : LawfulMonad Raw := LawfulMonad.mk'
  (id_map := fun x => by
    apply ext_toList
    simp [Functor.map, Raw.bind, Raw.pure, Raw.toList])
  (pure_bind := fun x f => by
    apply ext_toList
    simp)
  (bind_assoc := fun m f g => by
    apply ext_toList
    simp [List.flatMap_assoc, List.map_flatMap, List.flatMap_map, List.map_map,
      Function.comp_def, mul_assoc])
  (bind_pure_comp := fun f x => by
    cases x
    rfl)

private lemma sum_replicate_inv_length_eq_one (n : ℕ) (hn : n ≠ 0) :
    (List.replicate n ((n : ℚ≥0)⁻¹)).sum = 1 := by
  rw [List.sum_replicate, nsmul_eq_mul, mul_inv_cancel₀]
  exact_mod_cast hn

/-- Uniform distribution over a nonempty list, treating repeated entries as repeated tickets. -/
protected def uniformList (l : List α) (hl : l ≠ []) : Raw α :=
  let w : ℚ≥0 := (l.length : ℚ≥0)⁻¹
  ⟨(l.map fun a => (a, w)).toArray, by
    have hlen : l.length ≠ 0 := by
      intro hlen
      exact hl (List.eq_nil_iff_length_eq_zero.2 hlen)
    have hmap : List.map Prod.snd (List.map (fun a => (a, w)) l) = List.replicate l.length w := by
      simp [Function.comp_def]
    rw [show (((l.map (fun a => (a, w))).toArray.toList.map Prod.snd).sum) =
        (List.map Prod.snd (List.map (fun a => (a, w)) l)).sum by rw [List.toList_toArray],
      hmap]
    simpa [w] using sum_replicate_inv_length_eq_one l.length hlen⟩

/-- Uniform distribution over a finite inhabited type. -/
protected def uniform [FinEnum α] [Inhabited α] : Raw α :=
  Raw.uniformList (FinEnum.toList α) <| by
    intro hnil
    have hmem : default ∈ FinEnum.toList α := FinEnum.mem_toList default
    simp [hnil] at hmem

/-- Fair coin. -/
protected def coin : Raw Bool :=
  Raw.uniformList [true, false] (by simp)

/-- Bernoulli distribution with probability `p` of `true`. -/
protected def bernoulli (p : ℚ≥0) (hp : p ≤ 1) : Raw Bool :=
  ⟨#[(true, p), (false, 1 - p)], by
    simp [add_tsub_cancel_of_le hp]⟩

/-! ### Probability and support -/

/-- The probability assigned to `x` by the raw PMF: sum of weights for all entries with key `x`. -/
def prob [DecidableEq α] (p : Raw α) (x : α) : ℚ≥0 :=
  probOfList p.toList x

/-- `prob` is independent of the `DecidableEq` instance, since `decide (a = b)` gives the same
`Bool` for any `Decidable` instance on the same `Prop`. -/
lemma prob_eq_prob (inst1 inst2 : DecidableEq α) (p : Raw α) (x : α) :
    @prob _ inst1 p x = @prob _ inst2 p x := by
  unfold prob probOfList
  have hpred :
      (fun a : α × ℚ≥0 => @decide (a.1 = x) (inst1 a.1 x)) =
      fun a : α × ℚ≥0 => @decide (a.1 = x) (inst2 a.1 x) := by
    funext a
    cases inst1 a.1 x <;> cases inst2 a.1 x <;> simp_all
  simp [hpred]

/-- The finite support: the set of outcomes appearing in the array. -/
def support [DecidableEq α] (p : Raw α) : Finset α :=
  supportOfList p.toList

lemma prob_eq_zero_of_not_mem_support [DecidableEq α] (p : Raw α) {x : α}
    (hx : x ∉ p.support) : p.prob x = 0 := by
  simpa [prob, support] using probOfList_eq_zero_of_not_mem_supportOfList p.toList hx

lemma mem_support_iff [DecidableEq α] (p : Raw α) (x : α) :
    x ∈ p.support ↔ p.prob x ≠ 0 := by
  simpa [prob, support] using mem_supportOfList_iff p.toList x

private lemma filter_cons_sum [DecidableEq α] (hd : α × ℚ≥0) (tl : List (α × ℚ≥0)) (x : α) :
    ((hd :: tl).filter (fun a => a.1 = x) |>.map Prod.snd).sum =
    (if hd.1 = x then hd.2 else 0) +
    (tl.filter (fun a => a.1 = x) |>.map Prod.snd).sum := by
  simp only [List.filter_cons, decide_eq_true_eq]
  split <;> simp_all [List.map_cons, List.sum_cons]

private lemma list_prob_eq_zero [DecidableEq α] {l : List (α × ℚ≥0)} {x : α}
    (hx : x ∉ (l.map Prod.fst).toFinset) :
    (l.filter (fun a => a.1 = x) |>.map Prod.snd).sum = 0 := by
  suffices l.filter (fun a => a.1 = x) = [] by simp [this]
  rw [List.filter_eq_nil_iff]
  simp only [List.mem_toFinset, List.mem_map] at hx
  exact fun a ha => by simp; intro heq; exact hx ⟨a, ha, heq ▸ rfl⟩

private lemma list_sum_prob_eq [DecidableEq α] (l : List (α × ℚ≥0)) :
    (l.map Prod.fst |>.toFinset).sum
      (fun x => (l.filter (fun a => a.1 = x) |>.map Prod.snd).sum) =
    (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.toFinset_cons, List.sum_cons]
    simp_rw [filter_cons_sum, Finset.sum_add_distrib]
    congr 1
    · simp
    · by_cases hm : hd.1 ∈ (tl.map Prod.fst).toFinset
      · rw [Finset.insert_eq_of_mem hm]; exact ih
      · rw [Finset.sum_insert hm, list_prob_eq_zero hm, zero_add]; exact ih

/-- Sum of `prob` over the support recovers the total weight. -/
lemma sum_prob_eq_sum [DecidableEq α] (p : Raw α) :
    p.support.sum p.prob = (p.toList.map Prod.snd).sum := by
  let s : Finset α := p.toList.map Prod.fst |>.toFinset
  have hs : p.support ⊆ s := by
    intro x hx
    rcases List.mem_toFinset.1 hx with hx
    rcases List.mem_map.1 hx with ⟨a, ha, hax⟩
    rcases List.mem_filter.1 ha with ⟨ha, _⟩
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, ha, hax⟩)
  calc
    p.support.sum p.prob = s.sum p.prob := by
      exact Finset.sum_subset hs (by
        intro x _ hx
        exact prob_eq_zero_of_not_mem_support p hx)
    _ = (p.toList.map Prod.snd).sum := by
      simpa [s, prob, probOfList] using list_sum_prob_eq p.toList

lemma sum_prob_eq_one [DecidableEq α] (p : Raw α) : p.support.sum p.prob = 1 := by
  rw [sum_prob_eq_sum]
  simpa [Raw.toList] using p.sum_eq_one

@[simp] lemma prob_pure [DecidableEq α] (a x : α) :
    (Raw.pure a).prob x = if x = a then 1 else 0 := by
  unfold Raw.prob probOfList Raw.toList Raw.pure
  by_cases h : x = a
  · simp [h]
  · have h' : ¬ a = x := by simpa [eq_comm] using h
    simp [h, h']

@[simp] lemma support_pure [DecidableEq α] (a : α) :
    (Raw.pure a).support = {a} := by
  ext x
  by_cases h : x = a
  · subst h
    simp [mem_support_iff]
  · simp [mem_support_iff, prob_pure, h]

private lemma probOfList_map_const_eq_length_filter [DecidableEq α]
    (l : List α) (w : ℚ≥0) (x : α) :
    probOfList (l.map fun a => (a, w)) x = ((l.filter fun a => a = x).length : ℚ≥0) * w := by
  induction l with
  | nil => simp [probOfList]
  | cons a tl ih =>
    by_cases h : a = x
    · subst h
      rw [show probOfList (List.map (fun b => (b, w)) (a :: tl)) a =
          w + probOfList (List.map (fun b => (b, w)) tl) a by
            unfold probOfList
            simp]
      rw [ih]
      simp [add_mul, add_comm]
    · rw [show probOfList (List.map (fun b => (b, w)) (a :: tl)) x =
          probOfList (List.map (fun b => (b, w)) tl) x by
            unfold probOfList
            simp [h]]
      rw [ih]
      simp [h]

private lemma filter_eq_singleton_of_nodup [DecidableEq α] {l : List α} (hnd : l.Nodup)
    {x : α} (hx : x ∈ l) : l.filter (fun a => a = x) = [x] := by
  induction l with
  | nil => cases hx
  | cons a tl ih =>
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨hatl, hndtl⟩
    by_cases hax : a = x
    · subst hax
      have hnot : a ∉ tl := by
        simpa using hatl
      have hnil : tl.filter (fun y => y = a) = [] := by
        apply List.filter_eq_nil_iff.2
        intro y hy
        simp only [decide_eq_true_eq]
        intro hya
        exact hnot (hya.symm ▸ hy)
      simp [hnil]
    · have hx' : x ∈ tl := by
        cases hx with
        | head => exact False.elim (hax rfl)
        | tail _ hx' => exact hx'
      simp [hax]
      exact ih hndtl hx'

/-- Point probabilities for `uniformList` on a duplicate-free list. -/
lemma prob_uniformList_of_nodup [DecidableEq α] {l : List α} (hl : l ≠ []) (hnd : l.Nodup)
    (x : α) :
    (Raw.uniformList l hl).prob x = if x ∈ l then (l.length : ℚ≥0)⁻¹ else 0 := by
  have htoList :
      (Raw.uniformList l hl).toList = l.map fun a => (a, ((l.length : ℚ≥0)⁻¹)) := by
    simp [Raw.uniformList, Raw.toList]
  rw [Raw.prob, htoList, probOfList_map_const_eq_length_filter]
  by_cases hx : x ∈ l
  · rw [if_pos hx, filter_eq_singleton_of_nodup hnd hx]
    simp
  · rw [if_neg hx]
    have hnil : l.filter (fun a => a = x) = [] := by
      apply List.filter_eq_nil_iff.2
      intro y hy
      simp only [decide_eq_true_eq]
      intro hyx
      exact hx (hyx ▸ hy)
    simp [hnil]

/-- Uniform distributions over duplicate-free lists have support exactly the listed elements. -/
lemma support_uniformList_of_nodup [DecidableEq α] {l : List α} (hl : l ≠ []) (hnd : l.Nodup) :
    (Raw.uniformList l hl).support = l.toFinset := by
  ext x
  rw [Raw.mem_support_iff, prob_uniformList_of_nodup hl hnd]
  by_cases hx : x ∈ l
  · simp [hx, hl]
  · simp [hx]

/-- Point probabilities of `Raw.uniform`. -/
@[simp] lemma prob_uniform [FinEnum α] [Inhabited α] (x : α) :
    (Raw.uniform (α := α)).prob x = (Fintype.card α : ℚ≥0)⁻¹ := by
  simpa [Raw.uniform, FinEnum.card_eq_fintypeCard] using
    prob_uniformList_of_nodup
      (α := α)
      (l := FinEnum.toList α)
      (by
        intro hnil
        have hmem : default ∈ FinEnum.toList α := FinEnum.mem_toList default
        simp [hnil] at hmem)
      FinEnum.nodup_toList
      x

/-- `Raw.uniform` has full finite support. -/
@[simp] lemma support_uniform [DecidableEq α] [FinEnum α] [Inhabited α] :
    (Raw.uniform (α := α)).support = Finset.univ := by
  classical
  ext x
  simp only [Finset.mem_univ, iff_true, Raw.mem_support_iff]
  have hcard : (Fintype.card α : ℚ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  have hprob : (Raw.uniform (α := α)).prob x = (Fintype.card α : ℚ≥0)⁻¹ := by
    calc
      (Raw.uniform (α := α)).prob x
          = @Raw.prob _ (FinEnum.decEq) (Raw.uniform (α := α)) x := by
              exact Raw.prob_eq_prob inferInstance (FinEnum.decEq) (Raw.uniform (α := α)) x
      _ = (Fintype.card α : ℚ≥0)⁻¹ := prob_uniform (α := α) x
  simp [hprob]

/-- Point probabilities of `Raw.coin`. -/
@[simp] lemma prob_coin (b : Bool) : Raw.coin.prob b = 2⁻¹ := by
  simpa [Raw.coin] using
    prob_uniformList_of_nodup (α := Bool) (l := [true, false]) (by simp)
      (by simp) b

@[simp] lemma support_coin : Raw.coin.support = {true, false} := by
  simpa [Raw.coin] using
    support_uniformList_of_nodup (α := Bool) (l := [true, false]) (by simp) (by simp)

@[simp] lemma prob_bernoulli_true (p : ℚ≥0) (hp : p ≤ 1) :
    (Raw.bernoulli p hp).prob true = p := by
  unfold Raw.bernoulli Raw.prob probOfList Raw.toList
  simp

@[simp] lemma prob_bernoulli_false (p : ℚ≥0) (hp : p ≤ 1) :
    (Raw.bernoulli p hp).prob false = 1 - p := by
  unfold Raw.bernoulli Raw.prob probOfList Raw.toList
  simp

lemma prob_le_one [DecidableEq α] (p : Raw α) (x : α) : p.prob x ≤ 1 := by
  by_cases hx : x ∈ p.support
  · calc
      p.prob x ≤ p.support.sum p.prob := Finset.single_le_sum (fun _ _ => by exact zero_le _ ) hx
      _ = 1 := sum_prob_eq_one p
  · simp [prob_eq_zero_of_not_mem_support p hx]

private lemma probOfList_append [DecidableEq α] (l₁ l₂ : List (α × ℚ≥0)) (x : α) :
    probOfList (l₁ ++ l₂) x = probOfList l₁ x + probOfList l₂ x := by
  unfold probOfList
  rw [List.filter_append, List.map_append, List.sum_append]

private lemma filter_map_mul_eq [DecidableEq α] (l : List (α × ℚ≥0)) (p : ℚ≥0) (x : α) :
    (l.map (fun (a, q) => (a, p * q))).filter (fun a => a.1 = x) =
      (l.filter (fun a => a.1 = x)).map (fun (a, q) => (a, p * q)) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    by_cases h : hd.1 = x <;> simp [h, ih]

private lemma probOfList_map_mul [DecidableEq α] (l : List (α × ℚ≥0)) (p : ℚ≥0) (x : α) :
    probOfList (l.map fun (a, q) => (a, p * q)) x = p * probOfList l x := by
  unfold probOfList
  rw [filter_map_mul_eq]
  rw [List.map_map]
  simp only [Function.comp_def]
  simpa using List.sum_map_mul_left ((l.filter fun a => a.1 = x).map Prod.snd) id p

private lemma list_sum_prob_mul_eq [DecidableEq α] (l : List (α × ℚ≥0)) (w : α → ℚ≥0) :
    (l.map Prod.fst |>.toFinset).sum (fun x => probOfList l x * w x) =
    (l.map (fun (a, p) => p * w a)).sum := by
  induction l with
  | nil => simp [probOfList]
  | cons hd tl ih =>
    let s : Finset α := (tl.map Prod.fst).toFinset
    simp only [List.map_cons, List.toFinset_cons, List.sum_cons]
    calc
      (insert hd.1 s).sum (fun x => probOfList (hd :: tl) x * w x)
          = (insert hd.1 s).sum
              (fun x => (((if hd.1 = x then hd.2 else 0) + probOfList tl x) * w x)) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                have hprob :
                    probOfList (hd :: tl) x = (if hd.1 = x then hd.2 else 0) + probOfList tl x := by
                  simpa [probOfList] using filter_cons_sum hd tl x
                exact congrArg (fun q => q * w x) hprob
      _ = (insert hd.1 s).sum (fun x => (if hd.1 = x then hd.2 else 0) * w x) +
            (insert hd.1 s).sum (fun x => probOfList tl x * w x) := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
      _ = hd.2 * w hd.1 + (List.map (fun x => x.2 * w x.1) tl).sum := by
        congr 1
        · calc
            (insert hd.1 s).sum (fun x => (if hd.1 = x then hd.2 else 0) * w x)
                = ∑ x ∈ insert hd.1 s, if hd.1 = x then hd.2 * w x else 0 := by
                    simp_rw [ite_mul, zero_mul]
            _ = hd.2 * w hd.1 := by simp
        · by_cases hm : hd.1 ∈ s
          · rw [Finset.insert_eq_of_mem hm]
            exact ih
          · have hzero : probOfList tl hd.1 = 0 := by
              simpa [probOfList] using list_prob_eq_zero hm
            rw [Finset.sum_insert hm, hzero, zero_mul, zero_add]
            exact ih

private lemma probOfList_bind_eq_sum [DecidableEq α] [DecidableEq β]
    (l : List (α × ℚ≥0)) (g : α → Raw β) (y : β) :
    probOfList (l.flatMap (fun (a, p) => (g a).toList.map (fun (b, q) => (b, p * q)))) y =
      (l.map (fun (a, p) => p * (g a).prob y)).sum := by
  induction l with
  | nil => simp [probOfList]
  | cons hd tl ih =>
    rw [List.flatMap_cons, probOfList_append, ih, probOfList_map_mul]
    simp [Raw.prob, Raw.toList]

@[simp] lemma prob_bind [DecidableEq α] [DecidableEq β] (m : Raw α) (f : α → Raw β) (y : β) :
    (m >>= f).prob y = m.support.sum (fun a => m.prob a * (f a).prob y) := by
  let s : Finset α := m.toList.map Prod.fst |>.toFinset
  have hs : m.support ⊆ s := by
    intro x hx
    rcases List.mem_toFinset.1 hx with hx
    rcases List.mem_map.1 hx with ⟨a, ha, hax⟩
    rcases List.mem_filter.1 ha with ⟨ha, _⟩
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, ha, hax⟩)
  calc
    (m >>= f).prob y = (m.toList.map (fun (a, p) => p * (f a).prob y)).sum := by
      rw [Raw.prob, bind_toList, probOfList_bind_eq_sum]
    _ = s.sum (fun a => m.prob a * (f a).prob y) := by
      symm
      simpa [s, Raw.prob, Raw.toList] using
        list_sum_prob_mul_eq m.toList (fun a => (f a).prob y)
    _ = m.support.sum (fun a => m.prob a * (f a).prob y) := by
      symm
      exact Finset.sum_subset hs (by
        intro x _ hx
        simp [prob_eq_zero_of_not_mem_support m hx])

lemma mem_support_bind_iff [DecidableEq α] [DecidableEq β] (m : Raw α) (f : α → Raw β) (y : β) :
    y ∈ (m >>= f).support ↔ ∃ x ∈ m.support, y ∈ (f x).support := by
  rw [mem_support_iff, prob_bind]
  constructor
  · intro hy
    have hpos : 0 < ∑ x ∈ m.support, m.prob x * (f x).prob y := pos_iff_ne_zero.mpr hy
    rcases Finset.sum_pos_iff.mp hpos with ⟨x, hx, hxpos⟩
    have hfy : (f x).prob y ≠ 0 := by
      by_contra hzero
      rw [hzero, mul_zero] at hxpos
      exact lt_irrefl _ hxpos
    exact ⟨x, hx, (mem_support_iff (f x) y).2 hfy⟩
  · rintro ⟨x, hx, hy⟩
    have hmx : m.prob x ≠ 0 := (mem_support_iff m x).1 hx
    have hfy : (f x).prob y ≠ 0 := (mem_support_iff (f x) y).1 hy
    have hpos : 0 < m.prob x * (f x).prob y := by
      exact mul_pos (pos_iff_ne_zero.mpr hmx) (pos_iff_ne_zero.mpr hfy)
    have hle :
        m.prob x * (f x).prob y ≤ ∑ a ∈ m.support, m.prob a * (f a).prob y := by
      exact Finset.single_le_sum
        (f := fun a => m.prob a * (f a).prob y) (fun _ _ => by exact zero_le _) hx
    exact pos_iff_ne_zero.mp (lt_of_lt_of_le hpos hle)

@[simp] lemma support_bind [DecidableEq α] [DecidableEq β] (m : Raw α) (f : α → Raw β) :
    (m >>= f).support = m.support.biUnion (fun x => (f x).support) := by
  ext y
  simp [mem_support_bind_iff]

def addWeight [BEq α] [Hashable α] (m : Std.HashMap α ℚ≥0) (a : α × ℚ≥0) :
    Std.HashMap α ℚ≥0 :=
  m.insert a.1 (m.getD a.1 0 + a.2)

def accumulateWeights [BEq α] [Hashable α] (xs : Array (α × ℚ≥0)) :
    Std.HashMap α ℚ≥0 :=
  xs.foldl addWeight {}

private lemma getD_foldl_addWeight_eq_probOfList [DecidableEq α] [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (l : List (α × ℚ≥0)) (m : Std.HashMap α ℚ≥0) (x : α) :
    (l.foldl addWeight m).getD x 0 = m.getD x 0 + probOfList l x := by
  induction l generalizing m with
  | nil => simp [probOfList]
  | cons hd tl ih =>
    rw [List.foldl_cons, ih]
    unfold addWeight
    by_cases h : hd.1 = x
    · have hbeq : (hd.1 == x) = true := by simp [h]
      rw [Std.HashMap.getD_insert]
      simp [probOfList, h, add_assoc, add_left_comm, add_comm]
    · have hbeq : (hd.1 == x) = false := by simp [h]
      rw [Std.HashMap.getD_insert]
      simp [probOfList, h, hbeq]

private lemma getD_accumulateWeights_eq_prob [DecidableEq α] [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (xs : Array (α × ℚ≥0)) (x : α) :
    (accumulateWeights xs).getD x 0 = probOfList xs.toList x := by
  unfold accumulateWeights
  rw [← Array.foldl_toList (f := addWeight) (init := ({} : Std.HashMap α ℚ≥0)) (xs := xs)]
  simpa using getD_foldl_addWeight_eq_probOfList xs.toList ({} : Std.HashMap α ℚ≥0) x

private lemma pairwise_ne_keys_toList [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (m : Std.HashMap α ℚ≥0) :
    m.toList.Pairwise (fun a b => a.1 ≠ b.1) := by
  refine (Std.HashMap.distinct_keys_toList (m := m)).imp ?_
  intro a b hab hEq
  simp [hEq] at hab

private lemma probOfList_eq_find?_getD [DecidableEq α] [BEq α] [LawfulBEq α]
    (l : List (α × ℚ≥0)) (x : α)
    (hpair : l.Pairwise (fun a b => a.1 ≠ b.1)) :
    probOfList l x = ((l.find? (fun a => a.1 == x)).map Prod.snd).getD 0 := by
  induction l with
  | nil => simp [probOfList]
  | cons a tl ih =>
    rw [List.pairwise_cons] at hpair
    rcases hpair with ⟨ha, hpair⟩
    by_cases h : a.1 = x
    · have hnil : tl.filter (fun b => b.1 = x) = [] := by
        apply List.filter_eq_nil_iff.2
        intro b hb
        simp only [decide_eq_true_eq]
        intro hb'
        exact ha _ hb (h.trans hb'.symm)
      have hbeq : (a.1 == x) = true := by simp [h]
      simp [probOfList, h, hnil]
    · have hbeq : (a.1 == x) = false := by simp [h]
      simpa [probOfList, h, hbeq] using ih hpair

private lemma probOfList_toList_eq_getD [DecidableEq α] [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (m : Std.HashMap α ℚ≥0) (x : α) :
    probOfList m.toList x = m.getD x 0 := by
  rw [probOfList_eq_find?_getD m.toList x (pairwise_ne_keys_toList m),
    Std.HashMap.getD_eq_getD_getElem?]
  cases hopt : m[x]? with
  | none =>
    have hnot : x ∉ m := by
      rw [Std.HashMap.mem_iff_isSome_getElem?]
      simp [hopt]
    have hfind : m.toList.find? (fun a => a.1 == x) = none := by
      exact (Std.HashMap.find?_toList_eq_none_iff_not_mem (m := m) (k := x)).2 hnot
    simp [hfind]
  | some q =>
    have hxmem : x ∈ m := by
      rw [Std.HashMap.mem_iff_isSome_getElem?]
      simp [hopt]
    have hkey : m.getKey? x = some x := Std.HashMap.getKey?_eq_some (m := m) hxmem
    have hfind : m.toList.find? (fun a => a.1 == x) = some (x, q) := by
      exact (Std.HashMap.find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some
        (m := m) (k := x) (k' := x) (v := q)).2 ⟨hkey, hopt⟩
    simp [hfind]

def normalizeMap [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] (p : Raw α) :
    Std.HashMap α ℚ≥0 :=
  (accumulateWeights p.data).filter (fun _ q => q ≠ 0)

private lemma probOfNormalizeMap_eq_prob [DecidableEq α] [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (p : Raw α) (x : α) :
    probOfList (normalizeMap p).toList x = p.prob x := by
  rw [probOfList_toList_eq_getD]
  unfold normalizeMap
  rw [Std.HashMap.getD_filter']
  have hacc : (accumulateWeights p.data).getD x 0 = p.prob x := by
    simpa [Raw.prob, Raw.toList] using getD_accumulateWeights_eq_prob p.data x
  rw [Std.HashMap.getD_eq_getD_getElem?] at hacc
  cases hopt : (accumulateWeights p.data)[x]? with
  | none =>
    simp [hopt] at hacc
    simp [hacc]
  | some q =>
    have hacc' : q = p.prob x := by simpa [hopt] using hacc
    by_cases hq : q = 0
    · have hprob : p.prob x = 0 := by simpa [hacc'] using hq
      simpa [hq] using hprob.symm
    · have hprob : p.prob x ≠ 0 := by simpa [hacc'] using hq
      calc
        (Option.filter (fun q => decide (q ≠ 0)) (some q)).getD 0 = q := by
          rw [Option.filter_some]
          have hpred : decide (q ≠ 0) = true := by simp [hq]
          simp [hpred]
        _ = p.prob x := hacc'

private lemma snd_ne_zero_of_mem_normalizeMap_toList [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (p : Raw α) {a : α × ℚ≥0}
    (ha : a ∈ (normalizeMap p).toList) : a.2 ≠ 0 := by
  have hsome : (normalizeMap p)[a.1]? = some a.2 := by
    exact (Std.HashMap.mem_toList_iff_getElem?_eq_some (m := normalizeMap p)
      (k := a.1) (v := a.2)).1 ha
  unfold normalizeMap at hsome
  rw [Std.HashMap.getElem?_filter'] at hsome
  cases hacc : (accumulateWeights p.data)[a.1]? with
  | none => simp [hacc] at hsome
  | some q =>
    by_cases hq : q = 0
    · simp [hacc, hq] at hsome
      exact False.elim (hsome.2 hsome.1.symm)
    · simp [hacc] at hsome
      exact hsome.2

private lemma normalizeMap_keys_eq_support [DecidableEq α] [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (p : Raw α) :
    ((normalizeMap p).toList.map Prod.fst).toFinset = p.support := by
  rw [← supportOfList_eq_keys (l := (normalizeMap p).toList)]
  · ext x
    rw [mem_supportOfList_iff, mem_support_iff, probOfNormalizeMap_eq_prob]
  · intro a ha
    exact snd_ne_zero_of_mem_normalizeMap_toList p ha

/-- Merge duplicate outcomes and discard zero-weight entries. This implementation is linear in the
number of raw entries up to hash-map operations, so it avoids the repeated `support/prob` rescans
that would make normalization quadratic. -/
protected def normalize [DecidableEq α] [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (p : Raw α) : Raw α :=
  ⟨(normalizeMap p).toList.toArray, by
    have hkeys : ((normalizeMap p).toList.map Prod.fst).toFinset = p.support :=
      normalizeMap_keys_eq_support p
    calc
      (((normalizeMap p).toList.map Prod.snd).sum) =
          (((normalizeMap p).toList.map Prod.fst).toFinset.sum (probOfList (normalizeMap p).toList)) := by
        symm
        exact list_sum_prob_eq (normalizeMap p).toList
      _ = p.support.sum p.prob := by
        rw [hkeys]
        refine Finset.sum_congr rfl ?_
        intro x _
        exact probOfNormalizeMap_eq_prob p x
      _ = 1 := sum_prob_eq_one p⟩

@[simp] lemma normalize_toList [DecidableEq α] [BEq α] [Hashable α] [LawfulBEq α]
    [LawfulHashable α] (p : Raw α) :
    p.normalize.toList = (normalizeMap p).toList := by
  unfold Raw.normalize
  simp [Raw.toList]

@[simp] lemma prob_normalize [DecidableEq α] [BEq α] [Hashable α] [LawfulBEq α]
    [LawfulHashable α] (p : Raw α) (x : α) :
    p.normalize.prob x = p.prob x := by
  unfold Raw.prob
  rw [normalize_toList]
  exact probOfNormalizeMap_eq_prob p x

@[simp] lemma support_normalize [DecidableEq α] [BEq α] [Hashable α] [LawfulBEq α]
    [LawfulHashable α] (p : Raw α) :
    p.normalize.support = p.support := by
  ext x
  rw [mem_support_iff, mem_support_iff, prob_normalize]

/-- Convert to a `PMF` by mapping weights through `ℚ≥0 → ℝ≥0 → ℝ≥0∞`. -/
noncomputable def toPMF [DecidableEq α] (p : Raw α) : PMF α :=
  PMF.ofFinset (fun x => ((p.prob x : NNReal) : ENNReal)) p.support
    (by
      have hsum : p.support.sum p.prob = (1 : ℚ≥0) := by
        rw [sum_prob_eq_sum]
        simpa [Raw.toList] using p.sum_eq_one
      rw [← ENNReal.coe_finset_sum, ← NNRat.cast_sum (K := NNReal)]
      change (((p.support.sum p.prob : ℚ≥0) : NNReal) : ENNReal) = 1
      simpa using congrArg (fun q : ℚ≥0 => ((q : NNReal) : ENNReal)) hsum)
    (fun a ha => by simp [prob_eq_zero_of_not_mem_support p ha])

@[simp] lemma toPMF_apply [DecidableEq α] (p : Raw α) (x : α) :
    p.toPMF x = ((p.prob x : NNReal) : ENNReal) := rfl

@[simp] lemma toPMF_pure [DecidableEq α] (a : α) :
    (Raw.pure a).toPMF = PMF.pure a := by
  ext x
  rw [toPMF_apply, PMF.pure_apply, prob_pure]
  split_ifs <;> simp [*]

@[simp] lemma toPMF_uniform [FinEnum α] [Inhabited α] :
    (Raw.uniform (α := α)).toPMF = PMF.uniformOfFintype α := by
  ext x
  rw [toPMF_apply, PMF.uniformOfFintype_apply, prob_uniform]
  simp [NNRat.cast_inv]

@[simp] lemma toPMF_coin : Raw.coin.toPMF = PMF.uniformOfFintype Bool := by
  ext b
  rw [toPMF_apply, PMF.uniformOfFintype_apply, prob_coin]
  simp [NNRat.cast_inv]

@[simp] lemma toPMF_bind [DecidableEq α] [DecidableEq β] (m : Raw α) (f : α → Raw β) :
    (m >>= f).toPMF = m.toPMF >>= fun a => (f a).toPMF := by
  ext y
  rw [toPMF_apply]
  change (((m >>= f).prob y : NNReal) : ENNReal) =
      ∑' a, m.toPMF a * (f a).toPMF y
  rw [tsum_eq_sum (s := m.support)]
  · simp_rw [Raw.toPMF_apply, ← ENNReal.coe_mul, ← NNRat.cast_mul]
    rw [← ENNReal.coe_finset_sum, ← NNRat.cast_sum (K := NNReal), Raw.prob_bind]
  · intro x hx
    simp [Raw.toPMF_apply, prob_eq_zero_of_not_mem_support m hx]

noncomputable def toPMFHom : Raw →ᵐ PMF where
  toFun _ p := @Raw.toPMF _ (Classical.decEq _) p
  toFun_pure' := by
    intro α x
    letI := Classical.decEq α
    exact Raw.toPMF_pure (α := α) x
  toFun_bind' := by
    intro α β x y
    letI := Classical.decEq α
    letI := Classical.decEq β
    exact Raw.toPMF_bind (α := α) (β := β) x y

end Raw

/-! ## Distributional equality and quotient -/

variable {α β γ : Type u}

/-- Two raw PMFs represent the same distribution if they assign the same probability to every
outcome. Uses classical decidable equality since this is a `Prop`. -/
def SameDist (p q : Raw α) : Prop :=
  ∀ x : α, @Raw.prob _ (Classical.decEq _) p x =
            @Raw.prob _ (Classical.decEq _) q x

lemma SameDist.refl (p : Raw α) : SameDist p p := fun _ => rfl

lemma SameDist.symm {p q : Raw α} (h : SameDist p q) : SameDist q p :=
  fun x => (h x).symm

lemma SameDist.trans {p q r : Raw α} (hpq : SameDist p q) (hqr : SameDist q r) :
    SameDist p r :=
  fun x => (hpq x).trans (hqr x)

lemma SameDist.prob_eq [DecidableEq α] {p q : Raw α} (h : SameDist p q) (x : α) :
    p.prob x = q.prob x := by
  simpa [Raw.prob_eq_prob (Classical.decEq _) inferInstance p x,
    Raw.prob_eq_prob (Classical.decEq _) inferInstance q x] using h x

lemma SameDist.support_eq [DecidableEq α] {p q : Raw α} (h : SameDist p q) :
    p.support = q.support := by
  ext x
  rw [Raw.mem_support_iff, Raw.mem_support_iff, h.prob_eq x]

lemma SameDist.bind_congr [DecidableEq α] [DecidableEq β] {p q : Raw α}
    {f g : α → Raw β} (hpq : SameDist p q) (hfg : ∀ x, SameDist (f x) (g x)) :
    SameDist (p >>= f) (q >>= g) := by
  intro y
  rw [show @Raw.prob _ (Classical.decEq β) (p >>= f) y =
      (@Raw.support _ (Classical.decEq α) p).sum
        (fun x => @Raw.prob _ (Classical.decEq α) p x *
          @Raw.prob _ (Classical.decEq β) (f x) y) by
        exact @Raw.prob_bind _ _ (Classical.decEq α) (Classical.decEq β) p f y]
  rw [show @Raw.prob _ (Classical.decEq β) (q >>= g) y =
      (@Raw.support _ (Classical.decEq α) q).sum
        (fun x => @Raw.prob _ (Classical.decEq α) q x *
          @Raw.prob _ (Classical.decEq β) (g x) y) by
        exact @Raw.prob_bind _ _ (Classical.decEq α) (Classical.decEq β) q g y]
  rw [show @Raw.support _ (Classical.decEq α) p = @Raw.support _ (Classical.decEq α) q by
        exact @SameDist.support_eq _ (Classical.decEq α) p q hpq]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [hpq x, hfg x y]

lemma SameDist.map_congr [DecidableEq α] [DecidableEq β] {p q : Raw α}
    (hpq : SameDist p q) (f : α → β) :
    SameDist (f <$> p) (f <$> q) := by
  simpa [Functor.map] using
    (SameDist.bind_congr (β := β) hpq fun x => SameDist.refl (Raw.pure (f x)))

instance : IsEquiv (Raw α) SameDist where
  refl := SameDist.refl
  symm := @SameDist.symm _
  trans := @SameDist.trans _

instance Raw.instSetoid : Setoid (Raw α) where
  r := SameDist
  iseqv := ⟨SameDist.refl, SameDist.symm, SameDist.trans⟩

namespace Raw

lemma sameDist_normalize [DecidableEq α] [BEq α] [Hashable α] [LawfulBEq α]
    [LawfulHashable α] (p : Raw α) : SameDist p p.normalize := by
  intro x
  rw [Raw.prob_eq_prob (Classical.decEq _) inferInstance p x,
    Raw.prob_eq_prob (Classical.decEq _) inferInstance p.normalize x,
    prob_normalize]

lemma sameDist_normalize_normalize [DecidableEq α] [BEq α] [Hashable α] [LawfulBEq α]
    [LawfulHashable α] (p : Raw α) : SameDist p.normalize.normalize p.normalize := by
  intro x
  rw [Raw.prob_eq_prob (Classical.decEq _) inferInstance p.normalize.normalize x,
    Raw.prob_eq_prob (Classical.decEq _) inferInstance p.normalize x,
    prob_normalize]

end Raw

end FinRatPMF

/-- Probability mass function with finite support and rational weights, with canonical equality.

Defined as the quotient of `FinRatPMF.Raw` by distributional equality. Two values are equal iff
they assign the same probability to every outcome. -/
def FinRatPMF (α : Type u) : Type u := Quotient (α := FinRatPMF.Raw α) inferInstance

namespace FinRatPMF

variable {α β γ : Type u}

/-- Construct from a raw PMF. -/
def mk (p : Raw α) : FinRatPMF α := Quotient.mk _ p

/-- `FinRatPMF` equality is distributional equality. -/
lemma eq_iff {p q : Raw α} : mk p = mk q ↔ SameDist p q :=
  Quotient.eq

/-! ### Monad operations -/

/-- `bind` lifts `Raw.bind` across the quotient in the first argument. The codomain remains
noncomputable because the Kleisli function returns quotient values, so we still choose a raw
representative for each branch. -/
noncomputable instance : Monad FinRatPMF where
  pure a := mk (Raw.pure a)
  bind ma f := Quotient.liftOn ma
    (fun p => mk (Raw.bind p (fun a => Quotient.out (f a))))
    (by
      classical
      intro p q hpq
      apply Quotient.sound
      refine SameDist.bind_congr hpq ?_
      intro a
      exact SameDist.refl (Quotient.out (f a))
    )

lemma bind_eq_out (ma : FinRatPMF α) (f : α → FinRatPMF β) :
    ma >>= f = mk (Raw.bind (Quotient.out ma) (fun a => Quotient.out (f a))) := by
  classical
  refine Quotient.inductionOn ma ?_
  intro p
  apply Quotient.sound
  refine SameDist.bind_congr ?_ ?_
  · exact SameDist.symm <| Quotient.exact (Quotient.out_eq (mk p : FinRatPMF α))
  · intro a
    exact SameDist.refl (Quotient.out (f a))

@[simp] lemma bind_mk (p : Raw α) (f : α → FinRatPMF β) :
    (mk p >>= f) = mk (Raw.bind p (fun a => Quotient.out (f a))) := by
  classical
  trans mk (Raw.bind (Quotient.out (mk p : FinRatPMF α)) (fun a => Quotient.out (f a)))
  · exact bind_eq_out (mk p) f
  · apply Quotient.sound
    refine SameDist.bind_congr ?_ ?_
    · exact Quotient.exact (Quotient.out_eq (mk p : FinRatPMF α))
    · intro a
      exact SameDist.refl (Quotient.out (f a))

private lemma out_bind_sameDist (ma : FinRatPMF α) (f : α → FinRatPMF β) :
    SameDist (Quotient.out (ma >>= f))
      (Raw.bind (Quotient.out ma) (fun a => Quotient.out (f a))) := by
  exact Quotient.exact ((Quotient.out_eq (ma >>= f)).trans (bind_eq_out ma f))

/-! ### Connection to `PMF` -/

/-- Convert a `FinRatPMF` to a `PMF`. Well-defined since `SameDist` implies equal `toPMF`. -/
noncomputable def toPMF (p : FinRatPMF α) : PMF α := by
  classical
  refine Quotient.lift (fun raw => @Raw.toPMF _ (Classical.decEq _) raw) ?_ p
  intro a b hab
  refine PMF.ext fun x => ?_
  rw [Raw.toPMF_apply, Raw.toPMF_apply]
  exact congrArg (fun q : ℚ≥0 => ((q : NNReal) : ENNReal)) (hab x)

@[simp] lemma toPMF_mk (p : Raw α) : toPMF (mk p) = @Raw.toPMF _ (Classical.decEq _) p := by
  classical
  unfold toPMF mk
  rw [Quotient.lift_mk]

@[simp] lemma toPMF_pure (a : α) : toPMF (pure a : FinRatPMF α) = PMF.pure a := by
  classical
  rw [show (pure a : FinRatPMF α) = mk (Raw.pure a) by rfl, toPMF_mk, Raw.toPMF_pure]

lemma toPMF_out (p : FinRatPMF α) : toPMF p = @Raw.toPMF _ (Classical.decEq _) (Quotient.out p) := by
  classical
  refine Quotient.inductionOn p ?_
  intro q
  refine PMF.ext fun x => ?_
  change (toPMF (mk q : FinRatPMF α)) x =
    ((@Raw.toPMF _ (Classical.decEq _) (Quotient.out (mk q : FinRatPMF α)) : PMF α) x)
  rw [toPMF_mk, Raw.toPMF_apply, Raw.toPMF_apply]
  exact congrArg (fun r : ℚ≥0 => ((r : NNReal) : ENNReal))
    ((SameDist.symm <| Quotient.exact (Quotient.out_eq (mk q : FinRatPMF α))) x)

@[simp] lemma toPMF_bind (ma : FinRatPMF α) (f : α → FinRatPMF β) :
    toPMF (ma >>= f) = toPMF ma >>= fun a => toPMF (f a) := by
  classical
  calc
    toPMF (ma >>= f)
        = @Raw.toPMF _ (Classical.decEq _)
            (Raw.bind (Quotient.out ma) (fun a => Quotient.out (f a))) := by
              rw [bind_eq_out, toPMF_mk]
    _ = @Raw.toPMF _ (Classical.decEq _) (Quotient.out ma) >>=
          fun a => @Raw.toPMF _ (Classical.decEq _) (Quotient.out (f a)) := by
            exact Raw.toPMF_bind _ _
    _ = toPMF ma >>= fun a => toPMF (f a) := by
          rw [← toPMF_out ma]
          congr 1
          funext a
          rw [← toPMF_out (f a)]

noncomputable def toPMFHom : FinRatPMF →ᵐ PMF where
  toFun _ p := toPMF p
  toFun_pure' := by
    intro α x
    exact toPMF_pure x
  toFun_bind' := by
    intro α β x y
    exact toPMF_bind x y

lemma toPMF_injective : Function.Injective (toPMF (α := α)) := by
  classical
  intro p q hpq
  revert hpq
  refine Quotient.inductionOn₂ p q ?_
  intro a b hpq
  change toPMF (mk a) = toPMF (mk b) at hpq
  rw [toPMF_mk, toPMF_mk] at hpq
  rw [Quotient.eq]
  intro x
  have hfun :
      (@Raw.toPMF _ (Classical.decEq _) a : PMF α) x =
      (@Raw.toPMF _ (Classical.decEq _) b : PMF α) x := by
    exact congrFun (congrArg DFunLike.coe hpq) x
  rw [Raw.toPMF_apply, Raw.toPMF_apply] at hfun
  have key' :
      ((@Raw.prob _ (Classical.decEq _) a x : ℚ≥0) : NNReal) =
      ((@Raw.prob _ (Classical.decEq _) b x : ℚ≥0) : NNReal) := by
    exact congrArg ENNReal.toNNReal hfun
  calc @Raw.prob _ (Classical.decEq _) a x
      = a.prob x := Raw.prob_eq_prob _ _ _ _
    _ = b.prob x := by exact_mod_cast key'
    _ = @Raw.prob _ (Classical.decEq _) b x :=
        (Raw.prob_eq_prob _ _ _ _).symm

noncomputable instance : LawfulMonad FinRatPMF := LawfulMonad.mk'
  (id_map := fun x => by
    apply toPMF_injective
    calc
      toPMF (id <$> x) = toPMF x >>= fun a => PMF.pure a := by
        rw [show id <$> x = x >>= fun a => pure (id a) by rfl, toPMF_bind]
        simp
      _ = toPMF x := by
            change toPMF x >>= pure = toPMF x
            exact bind_pure (x := toPMF x))
  (pure_bind := fun x f => by
    apply toPMF_injective
    calc
      toPMF (pure x >>= f) = PMF.pure x >>= fun a => toPMF (f a) := by
        rw [toPMF_bind, toPMF_pure]
      _ = toPMF (f x) := by
            exact pure_bind (m := PMF) x (fun a => toPMF (f a)))
  (bind_assoc := fun m f g => by
    apply toPMF_injective
    calc
      toPMF ((m >>= f) >>= g)
          = (toPMF m >>= fun a => toPMF (f a)) >>= fun b => toPMF (g b) := by
              rw [toPMF_bind, toPMF_bind]
      _ = toPMF m >>= fun a => toPMF (f a) >>= fun b => toPMF (g b) := by simp [bind_assoc]
      _ = toPMF (m >>= fun a => f a >>= g) := by
            rw [toPMF_bind]
            congr 1
            ext a
            rw [toPMF_bind])
  (bind_pure_comp := fun f x => by
    apply toPMF_injective
    calc
      toPMF (x >>= fun a => pure (f a))
          = toPMF x >>= fun a => PMF.pure (f a) := by
              rw [toPMF_bind]
              simp
      _ = f <$> toPMF x := by
            exact bind_pure_comp (m := PMF) f (toPMF x)
      _ = toPMF (f <$> x) := by
            rw [show f <$> x = x >>= fun a => pure (f a) by rfl, toPMF_bind]
            simp [map_eq_bind_pure_comp]
            rfl)

instance instDecidableSameDist [DecidableEq α] (p q : Raw α) : Decidable (SameDist p q) := by
  let s := p.support ∪ q.support
  classical
  by_cases hs : ∀ x ∈ s, p.prob x = q.prob x
  · refine isTrue ?_
    intro x
    by_cases hx : x ∈ s
    · simpa [Raw.prob_eq_prob (Classical.decEq _) inferInstance p x,
        Raw.prob_eq_prob (Classical.decEq _) inferInstance q x] using hs x hx
    · have hpx : p.prob x = 0 := Raw.prob_eq_zero_of_not_mem_support p (by
        intro hxp
        exact hx (Finset.mem_union.2 <| Or.inl hxp))
      have hqx : q.prob x = 0 := Raw.prob_eq_zero_of_not_mem_support q (by
        intro hxq
        exact hx (Finset.mem_union.2 <| Or.inr hxq))
      rw [Raw.prob_eq_prob (Classical.decEq _) inferInstance p x,
        Raw.prob_eq_prob (Classical.decEq _) inferInstance q x, hpx, hqx]
  · refine isFalse ?_
    intro hpq
    apply hs
    intro x hx
    exact SameDist.prob_eq hpq x

instance [DecidableEq α] : BEq (Raw α) where
  beq p q := decide (SameDist p q)

@[simp] lemma beq_iff_sameDist [DecidableEq α] (p q : Raw α) :
    (p == q) = true ↔ SameDist p q := by
  show decide (SameDist p q) = true ↔ SameDist p q
  simp

end FinRatPMF
