/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import ToMathlib.General
import VCVio.EvalDist.Defs.NeverFails

/-!
# Distribution Semantics for Computations with Lists and Vectors

This file contains lemmas for `probEvent` and `probOutput` of computations involving `List`.
We also include `Vector` as a related case.

All lemmas are generic over any monad `m` with `[MonadLiftT m SPMF]`.
-/

universe u v w

variable {α β γ : Type v}
    {m : Type _ → Type _} [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

open List

section cons_append

omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistCompatible m] in
lemma cons_mem_support_seq_map_cons_iff [LawfulMonad m]
    (mx : m α) (my : m (List α)) (x : α) (xs : List α) :
    x :: xs ∈ support (cons <$> mx <*> my) ↔ x ∈ support mx ∧ xs ∈ support my := by
  rw [support_seq_map_eq_image2, Set.mem_image2_iff injective2_cons]

omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistCompatible m] in
lemma cons_mem_finSupport_seq_map_cons_iff [LawfulMonad m] [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (my : m (List α)) (x : α) (xs : List α) :
    x :: xs ∈ finSupport (cons <$> mx <*> my) ↔
      x ∈ finSupport mx ∧ xs ∈ finSupport my := by
  simpa only [mem_finSupport_iff_mem_support] using cons_mem_support_seq_map_cons_iff mx my x xs

omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] in
lemma probOutput_cons_seq_map_cons_eq_mul [LawfulMonad m]
    (mx : m α) (my : m (List α)) (x : α) (xs : List α) :
    Pr[= x :: xs | cons <$> mx <*> my] = Pr[= x | mx] * Pr[= xs | my] :=
  probOutput_seq_map_eq_mul_of_injective2 mx my cons injective2_cons x xs

omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] in
lemma probOutput_cons_seq_map_cons_eq_mul' [LawfulMonad m]
    (mx : m α) (my : m (List α)) (x : α) (xs : List α) :
    Pr[= x :: xs | (fun xs x => x :: xs) <$> my <*> mx] =
      Pr[= x | mx] * Pr[= xs | my] :=
  (probOutput_seq_map_swap mx my cons (x :: xs)).trans
    (probOutput_cons_seq_map_cons_eq_mul mx my x xs)

omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] in
@[simp]
lemma probOutput_map_append_left [LawfulMonad m] [DecidableEq α]
    (xs : List α) (mx : m (List α)) (ys : List α) :
    Pr[= ys | (xs ++ ·) <$> mx] = if ys.take xs.length = xs
      then Pr[= ys.drop xs.length | mx] else 0 := by
  split_ifs with h
  · have heq : ys = xs ++ ys.drop xs.length := by
      conv_lhs => rw [← List.take_append_drop xs.length ys, h]
    rw [probOutput_map_eq_tsum_ite]
    refine (tsum_eq_single (ys.drop xs.length) fun zs hzs =>
      if_neg fun h' => hzs ?_).trans (if_pos heq)
    exact (List.append_cancel_left (heq.symm.trans h')).symm
  · rw [probOutput_map_eq_tsum_ite]
    exact ENNReal.tsum_eq_zero.mpr fun zs =>
      if_neg fun h' => h (by simp [h'])

end cons_append

section mapM

omit [LawfulMonadLiftT m SetM] in
lemma probFailure_list_mapM_loop (xs : List α) (f : α → m β) (ys : List β) :
    Pr[⊥ | List.mapM.loop f xs ys] = 1 - (xs.map (1 - Pr[⊥ | f ·])).prod := by
  induction xs generalizing ys with
  | nil => simp [List.mapM.loop]
  | cons x xs h =>
    simp only [List.mapM.loop, List.map_cons, List.prod_cons]
    rw [probFailure_bind_eq_sub_mul _ _ (1 - (List.map (fun x ↦ 1 - Pr[⊥ | f x]) xs).prod)]
    · rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top
        ((List.prod_le_pow_card _ 1 (by simp)).trans (one_pow _).le)]
    · simp
    · simp [h]

omit [LawfulMonadLiftT m SetM] in
@[simp, grind =]
lemma probFailure_list_mapM (xs : List α) (f : α → m β) :
    Pr[⊥ | xs.mapM f] = 1 - (xs.map (1 - Pr[⊥ | f ·])).prod := by
  rw [mapM, probFailure_list_mapM_loop]

private lemma take_eq_reverse_of_take_succ_aux {δ : Type*} {zs ys : List δ} {y : δ}
    (h : zs.take (ys.length + 1) = ys.reverse ++ [y]) : zs.take ys.length = ys.reverse := by
  have := congrArg (List.take ys.length) h
  rwa [List.take_take, Nat.min_eq_left (by omega), List.take_left' (by simp)] at this

private lemma take_drop_succ_aux {δ : Type*} {zs ys : List δ} (hlt : ys.length < zs.length)
    (htake : zs.take ys.length = ys.reverse) :
    ∃ z, zs.take (ys.length + 1) = ys.reverse ++ [z] ∧
      zs.drop ys.length = z :: zs.drop (ys.length + 1) := by
  have hne : zs.drop ys.length ≠ [] := fun hd => absurd (List.drop_eq_nil_iff.mp hd) (by omega)
  refine ⟨_, ?_, (List.cons_head_tail hne).symm.trans (by rw [List.tail_drop])⟩
  conv_lhs => rw [← List.take_append_drop ys.length zs, htake]
  rw [List.take_append, List.length_reverse]
  simp [List.take_one, List.head?_eq_some_head hne]

omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] in
@[simp]
lemma probOutput_list_mapM_loop [DecidableEq β]
    (xs : List α) (f : α → m β) (ys : List β)
    (zs : List β) : Pr[= zs | List.mapM.loop f xs ys] =
      if zs.length = xs.length + ys.length ∧ zs.take ys.length = ys.reverse
      then (List.zipWith (fun x z => Pr[= z | f x]) xs (zs.drop ys.length)).prod else 0 := by
  revert ys zs
  induction xs with
  | nil =>
    intro ys zs
    simp only [List.mapM.loop, List.length_nil, Nat.zero_add,
      List.zipWith_nil_left, List.prod_nil]
    by_cases h : zs.length = ys.length ∧ zs.take ys.length = ys.reverse
    · obtain ⟨hlen, htake⟩ := h
      rw [show ys.length = zs.length from hlen.symm, List.take_length] at htake
      subst htake
      simp
    · rw [if_neg h, probOutput_pure, if_neg]
      rintro rfl
      exact h ⟨by simp, by simp⟩
  | cons x xs ih =>
    intro ys zs
    simp only [List.mapM.loop]
    rw [probOutput_bind_eq_tsum]
    simp_rw [ih, List.length_cons, List.reverse_cons]
    by_cases hcond : zs.length = xs.length + 1 + ys.length ∧ zs.take ys.length = ys.reverse
    · rw [if_pos hcond]
      obtain ⟨hlen, htake⟩ := hcond
      obtain ⟨z₀, htake_succ, hdrop_eq⟩ := take_drop_succ_aux (by omega) htake
      rw [tsum_eq_single z₀ ?_, if_pos ⟨by omega, htake_succ⟩, hdrop_eq,
        List.zipWith_cons_cons, List.prod_cons]
      intro y hy
      rw [if_neg fun ⟨_, h⟩ => hy <| by
        simpa using (List.append_cancel_left (htake_succ.symm.trans h)).symm, mul_zero]
    · rw [if_neg hcond]
      refine ENNReal.tsum_eq_zero.mpr fun y => ?_
      rw [if_neg fun ⟨_, ht⟩ => hcond ⟨by omega, take_eq_reverse_of_take_succ_aux ht⟩,
        mul_zero]

omit [LawfulMonadLiftT m SetM] in
lemma probOutput_bind_eq_mul {mx : m α} {my : α → m β} {y : β} (x : α)
    (h : ∀ x' ∈ support mx, y ∈ support (my x') → x' = x) :
    Pr[= y | mx >>= my] = Pr[= x | mx] * Pr[= y | my x] := by
  rw [probOutput_bind_eq_tsum]
  exact tsum_eq_single x <| by grind [= mul_eq_zero]

@[simp]
lemma probOutput_cons_map [LawfulMonad m] (mx : m (List α)) (x : α) (xs : List α) :
    Pr[= xs | cons x <$> mx] =
      if hxs : xs = [] then 0 else Pr[= xs.head hxs | (pure x : m α)] * Pr[= xs.tail | mx] := by
  classical
  rcases xs with _ | ⟨y, ys⟩
  · simp [probOutput_eq_zero_of_not_mem_support, support_map]
  · rcases eq_or_ne y x with rfl | hyx
    · grind [List.cons_injective]
    · simp [hyx, hyx.symm, probOutput_eq_zero_of_not_mem_support, support_map]

@[simp]
lemma probOutput_list_mapM [LawfulMonad m] (xs : List α) (f : α → m β) (ys : List β) :
    Pr[= ys | xs.mapM f] = if ys.length = xs.length
      then (List.zipWith (Pr[= · | f ·]) ys xs).prod else 0 := by
  have : DecidableEq β := Classical.decEq β
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    split_ifs with hys
    · simp only [length_cons] at hys
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hys
      simp only [mapM_cons, bind_pure_comp, zipWith_cons_cons, prod_cons]
      rw [probOutput_bind_eq_mul y]
      · simp only [probOutput_cons_map, reduceCtorEq, ↓reduceDIte, head_cons, probOutput_pure,
          ↓reduceIte, tail_cons, ih, mul_ite, one_mul, mul_zero, ite_eq_left_iff, zero_eq_mul,
          probOutput_eq_zero_iff, prod_eq_zero_iff]
        simp_all
      · simp
    · refine probOutput_eq_zero_of_not_mem_support ?_
      simp only [mapM_cons, support_bind, Set.mem_iUnion, not_exists]
      intro y _ zs hzs
      rw [support_pure, Set.mem_singleton_iff]
      intro heq; subst heq
      have : zs.length = xs.length := by
        by_contra h
        exact probOutput_ne_zero_of_mem_support hzs ((ih zs).trans (if_neg h))
      simp_all

@[simp]
lemma probOutput_list_mapM' [LawfulMonad m] (xs : List α) (f : α → m β) (ys : List β) :
    Pr[= ys | xs.mapM' f] = if ys.length = xs.length
      then (List.zipWith (Pr[= · | f ·]) ys xs).prod else 0 := by
  have : DecidableEq β := Classical.decEq β
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    split_ifs with hys
    · simp only [length_cons] at hys
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hys
      simp only [mapM'_cons, bind_pure_comp, zipWith_cons_cons, prod_cons]
      rw [probOutput_bind_eq_mul y]
      · simp only [probOutput_cons_map, reduceCtorEq, ↓reduceDIte, head_cons, probOutput_pure,
          ↓reduceIte, tail_cons, ih, mul_ite, one_mul, mul_zero, ite_eq_left_iff, zero_eq_mul,
          probOutput_eq_zero_iff, prod_eq_zero_iff]
        simp_all
      · simp
    · refine probOutput_eq_zero_of_not_mem_support ?_
      simp only [mapM'_cons, support_bind, Set.mem_iUnion, not_exists]
      intro y _ zs hzs
      rw [support_pure, Set.mem_singleton_iff]
      intro heq; subst heq
      have : zs.length = xs.length := by
        by_contra h
        exact probOutput_ne_zero_of_mem_support hzs ((ih zs).trans (if_neg h))
      simp_all

end mapM

section ListVector

variable {n : ℕ} (mx : m α) (my : m (List.Vector α n))

omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistCompatible m] in
@[simp]
lemma support_seq_map_vector_cons [LawfulMonad m] :
    support ((· ::ᵥ ·) <$> mx <*> my) =
    {xs | xs.head ∈ support mx ∧ xs.tail ∈ support my} := by
  ext xs
  simp only [support_seq_map_eq_image2, Set.mem_image2, Set.mem_setOf_eq]
  exact ⟨fun ⟨a, ha, b, hb, h⟩ => h ▸ ⟨by simpa using ha, by simpa using hb⟩,
    fun ⟨hh, ht⟩ => ⟨xs.head, hh, xs.tail, ht, xs.cons_head_tail⟩⟩

omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] in
@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul [LawfulMonad m] (xs : List.Vector α (n + 1)) :
    Pr[= xs | (· ::ᵥ ·) <$> mx <*> my] = Pr[= xs.head | mx] * Pr[= xs.tail | my] := by
  rw [← xs.cons_head_tail]
  exact probOutput_seq_map_eq_mul_of_injective2 mx my _ Vector.injective2_cons xs.head xs.tail

omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] in
@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul' [LawfulMonad m] (xs : List.Vector α (n + 1)) :
    Pr[= xs | (fun xs x => x ::ᵥ xs) <$> my <*> mx] =
    Pr[= xs.head | mx] * Pr[= xs.tail | my] :=
  (probOutput_seq_map_swap mx my (· ::ᵥ ·) xs).trans
    (probOutput_seq_map_vector_cons_eq_mul mx my xs)

@[simp]
lemma probOutput_vector_toList [LawfulMonad m] (mx' : m (List.Vector α n))
    (xs : List α) : Pr[= xs | List.Vector.toList <$> mx'] =
      if h : xs.length = n then Pr[= (⟨xs, h⟩ : List.Vector α n) | mx'] else 0 := by
  split_ifs with h
  · exact probOutput_map_eq_single (⟨xs, h⟩ : List.Vector α n)
      (fun _ _ h' => Subtype.ext h') rfl
  · apply probOutput_eq_zero_of_not_mem_support
    simp only [support_map, Set.mem_image]
    rintro ⟨ys, _, rfl⟩
    exact h ys.toList_length

end ListVector

section ListVectorMmap

variable {n : ℕ}

omit [LawfulMonadLiftT m SetM] in
@[simp]
lemma neverFail_list_vector_mmap {f : α → m β} {as : List.Vector α n}
    (h : ∀ x ∈ as.toList, NeverFail (f x)) : NeverFail (List.Vector.mmap f as) := by
  induction as using List.Vector.inductionOn with
  | nil => simp
  | @cons n x xs ih =>
    simp only [List.Vector.mmap_cons, neverFail_bind_iff]
    exact ⟨h x (by simp), fun _ _ =>
      ⟨ih (fun x' hx' => h x' (by simp [hx'])), fun _ _ => inferInstance⟩⟩

end ListVectorMmap

-- An `Array.mapM` analogue of `neverFail_list_mapM` is absent because `Array.mapM` has no
-- clean reduction to `List.mapM` in the current Lean/Mathlib version: it would require a
-- bridge lemma like `Array.mapM_eq_mapM_toList`.

-- `Std.Vector` analogues of `mem_support_vector_mapM` / `neverFail_vector_mapM` are absent
-- because `Vector.mapM` (Std/Batteries) uses `MonadSatisfying` internally and does not
-- reduce cleanly for generic `[MonadLiftT m SPMF]` monads.

/-! ## NeverFail lemmas for list monadic operations -/

section NeverFail

variable {α β : Type*} {m : Type _ → Type _} [Monad m] [LawfulMonad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

omit [LawfulMonadLiftT m SetM] in
@[simp]
lemma neverFail_list_mapM {f : α → m β} {as : List α}
    (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (as.mapM f) := by
  induction as <;> grind

omit [LawfulMonadLiftT m SetM] in
omit [LawfulMonad m] in
@[simp]
lemma neverFail_list_mapM' {f : α → m β} {as : List α}
    (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (as.mapM' f) := by
  induction as <;> simp_all

omit [LawfulMonadLiftT m SetM] in
@[simp]
lemma neverFail_list_flatMapM {f : α → m (List β)} {as : List α}
    (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (as.flatMapM f) := by
  induction as <;> grind

omit [LawfulMonadLiftT m SetM] in
@[simp]
lemma neverFail_list_filterMapM {f : α → m (Option β)} {as : List α}
    (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (as.filterMapM f) := by
  induction as <;> grind

variable {s : Type*}

omit [LawfulMonadLiftT m SetM] in
omit [LawfulMonad m] in
@[simp]
lemma neverFail_list_foldlM {f : s → α → m s} {init : s} {as : List α}
    (h : ∀ i, ∀ x ∈ as, NeverFail (f i x)) : NeverFail (as.foldlM f init) := by
  induction as generalizing init <;> grind

omit [LawfulMonadLiftT m SetM] in
@[simp]
lemma neverFail_list_foldrM {f : α → s → m s} {init : s} {as : List α}
    (h : ∀ i, ∀ x ∈ as, NeverFail (f x i)) : NeverFail (as.foldrM f init) := by
  induction as generalizing init <;> grind

end NeverFail

section VectorMapM

/-- Index-extraction for `Vector.mapM`: any component of a vector in the support of
the sequenced computation lies in the support of the corresponding component computation. -/
lemma Vector.support_mapM_index
    {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {α β : Type} {L : ℕ} (xs : _root_.Vector β L) (f : β → m α)
    {v : _root_.Vector α L} (hv : v ∈ support (xs.mapM f)) (i : Fin L) :
    v[i] ∈ support (f xs[i]) := by
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
      obtain ⟨xs0, x, hxs⟩ := Vector.exists_push (xs := xs)
      obtain ⟨v0, y, hv0⟩ := Vector.exists_push (xs := v)
      subst hxs
      subst hv0
      have hpush : (xs0.push x).mapM f =
          (xs0.mapM f >>= (fun ys ↦ f x >>= fun last ↦ pure (ys.push last))) := by
        have hsingle : (#v[x]).mapM f = (fun last ↦ #v[last]) <$> f x := by
          apply Vector.map_toArray_inj.mp
          simp
        rw [← Vector.append_singleton, Vector.mapM_append, hsingle]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
        rfl
      rw [hpush, mem_support_bind_iff] at hv
      obtain ⟨ys, hys, hv⟩ := hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨last, hlast, hpush_eq⟩ := hv
      rw [mem_support_pure_iff] at hpush_eq
      have hparts := Vector.push_eq_push.mp hpush_eq.symm
      by_cases hi : (i : ℕ) < L
      · change (v0.push y)[(i : ℕ)] ∈ support (f ((xs0.push x)[(i : ℕ)]))
        rw [Vector.getElem_push_lt hi, Vector.getElem_push_lt hi, ← hparts.2]
        exact ih xs0 hys ⟨i, hi⟩
      · have hilast : (i : ℕ) = L := by omega
        have hi_eq : i = ⟨L, Nat.lt_succ_self L⟩ := Fin.ext hilast
        subst i
        simpa [← hparts.1] using hlast

end VectorMapM
