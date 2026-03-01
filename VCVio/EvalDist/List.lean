/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.EvalDist.Defs.NeverFails
import ToMathlib.General

/-!
# Distribution Semantics for Computations with Lists and Vectors

This file contains lemmas for `probEvent` and `probOutput` of computations involving `List`.
We also include `Vector` as a related case.

All lemmas are generic over any monad `m` with `[HasEvalSPMF m]`.
-/

universe u v w

variable {α β γ : Type v}
    {m : Type _ → Type _} [Monad m] [HasEvalSPMF m]

open List

section cons_append

lemma cons_mem_support_seq_map_cons_iff [LawfulMonad m]
    (mx : m α) (my : m (List α)) (x : α) (xs : List α) :
    x :: xs ∈ support (cons <$> mx <*> my) ↔ x ∈ support mx ∧ xs ∈ support my := by
  rw [support_seq_map_eq_image2]
  exact Set.mem_image2_iff injective2_cons

lemma cons_mem_finSupport_seq_map_cons_iff [LawfulMonad m] [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (my : m (List α)) (x : α) (xs : List α) :
    x :: xs ∈ finSupport (cons <$> mx <*> my) ↔
      x ∈ finSupport mx ∧ xs ∈ finSupport my := by
  simp_rw [mem_finSupport_iff_mem_support]
  exact cons_mem_support_seq_map_cons_iff mx my x xs

lemma probOutput_cons_seq_map_cons_eq_mul [LawfulMonad m] [DecidableEq α]
    (mx : m α) (my : m (List α)) (x : α) (xs : List α) :
    Pr[= x :: xs | cons <$> mx <*> my] = Pr[= x | mx] * Pr[= xs | my] :=
  probOutput_seq_map_eq_mul_of_injective2 mx my cons injective2_cons x xs

lemma probOutput_cons_seq_map_cons_eq_mul' [LawfulMonad m] [DecidableEq α]
    (mx : m α) (my : m (List α)) (x : α) (xs : List α) :
    Pr[= x :: xs | (fun xs x => x :: xs) <$> my <*> mx] =
      Pr[= x | mx] * Pr[= xs | my] :=
  (probOutput_seq_map_swap mx my cons (x :: xs)).trans
    (probOutput_cons_seq_map_cons_eq_mul mx my x xs)

@[simp]
lemma probOutput_map_append_left [LawfulMonad m] [DecidableEq α]
    (xs : List α) (mx : m (List α)) (ys : List α) :
    Pr[= ys | (xs ++ ·) <$> mx] = if ys.take xs.length = xs
      then Pr[= ys.drop xs.length | mx] else 0 := by
  split_ifs with h
  · have heq : ys = xs ++ ys.drop xs.length := by
      have h1 := (List.take_append_drop xs.length ys).symm
      rwa [h] at h1
    rw [probOutput_map_eq_tsum_ite]
    refine (tsum_eq_single (ys.drop xs.length) fun zs hzs =>
      if_neg fun h' => hzs ?_).trans (if_pos heq)
    exact (List.append_cancel_left (heq.symm.trans h')).symm
  · rw [probOutput_map_eq_tsum_ite]
    exact ENNReal.tsum_eq_zero.mpr fun zs =>
      if_neg fun h' => h (by rw [h']; exact List.take_left)

end cons_append

section mapM

lemma probFailure_list_mapM_loop (xs : List α) (f : α → m β) (ys : List β) :
    Pr[⊥ | List.mapM.loop f xs ys] = 1 - (xs.map (1 - Pr[⊥ | f ·])).prod := by
  revert ys
  induction xs with
  | nil => simp [List.mapM.loop]
  | cons x xs h =>
      intros ys
      simp only [List.mapM.loop, List.map_cons, List.prod_cons]
      rw [probFailure_bind_eq_sub_mul _ _ (1 - (List.map (fun x ↦ 1 - Pr[⊥|f x]) xs).prod)]
      · congr 2
        rw [AddLECancellable.tsub_tsub_cancel_of_le]
        simp only [ENNReal.addLECancellable_iff_ne, ne_eq, ENNReal.sub_eq_top_iff,
          ENNReal.one_ne_top, false_and, not_false_eq_true]
        refine (List.prod_le_pow_card _ 1 <| by simp).trans (le_of_eq <| one_pow _)
      · simp
      · simp [h]

@[simp, grind =]
lemma probFailure_list_mapM (xs : List α) (f : α → m β) :
    Pr[⊥ | xs.mapM f] = 1 - (xs.map (1 - Pr[⊥ | f ·])).prod := by
  rw [mapM, probFailure_list_mapM_loop]

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
    · rw [if_pos h]
      obtain ⟨hlen, htake⟩ := h
      have : zs = ys.reverse := by
        rwa [show ys.length = zs.length from hlen.symm, List.take_length] at htake
      subst this; simp
    · rw [if_neg h, probOutput_pure, if_neg]
      rintro rfl; exact h ⟨by simp, by simp⟩
  | cons x xs ih =>
    intro ys zs
    simp only [List.mapM.loop]
    rw [probOutput_bind_eq_tsum]
    simp_rw [ih, List.length_cons, List.reverse_cons]
    have take_mono : ∀ y, zs.take (ys.length + 1) = ys.reverse ++ [y] →
        zs.take ys.length = ys.reverse := by
      intro y htk
      have h1 : zs.take ys.length = (zs.take (ys.length + 1)).take ys.length := by
        rw [List.take_take]; congr 1; omega
      rw [h1, htk, List.take_append_of_le_length (by simp)]
      simp [List.length_reverse]
    by_cases hcond : zs.length = xs.length + 1 + ys.length ∧ zs.take ys.length = ys.reverse
    · rw [if_pos hcond]
      obtain ⟨hlen, htake⟩ := hcond
      have hlt : ys.length < zs.length := by omega
      have hdrop_ne : (zs.drop ys.length) ≠ [] := by
        intro hd; exact absurd (List.drop_eq_nil_iff.mp hd) (by omega)
      set z₀ := (zs.drop ys.length).head hdrop_ne
      have hdrop_eq : zs.drop ys.length = z₀ :: zs.drop (ys.length + 1) := by
        conv_lhs => rw [← List.cons_head_tail hdrop_ne]
        rw [List.tail_drop]
      have htake_succ : zs.take (ys.length + 1) = ys.reverse ++ [z₀] := by
        conv_lhs => rw [← List.take_append_drop ys.length zs]
        rw [htake, hdrop_eq, List.take_append]
        simp [List.length_reverse]
      have hinner : ∀ y, (zs.length = xs.length + (ys.length + 1) ∧
          zs.take (ys.length + 1) = ys.reverse ++ [y]) ↔ y = z₀ := by
        intro y
        refine ⟨fun ⟨_, h⟩ => ?_, fun h => ⟨by omega, h ▸ htake_succ⟩⟩
        have := List.append_cancel_left (htake_succ.symm.trans h)
        simpa using this.symm
      simp_rw [hinner]
      rw [tsum_eq_single z₀ (by intro y hy; simp [hy]), if_pos rfl,
        hdrop_eq, List.zipWith_cons_cons, List.prod_cons]
    · rw [if_neg hcond]
      suffices hzero : ∀ y, Pr[= y | f x] *
          (if zs.length = xs.length + (ys.length + 1) ∧
              zs.take (ys.length + 1) = ys.reverse ++ [y]
            then (List.zipWith (fun a z => Pr[= z | f a]) xs (zs.drop (ys.length + 1))).prod
            else 0) = 0 by
        simp_rw [hzero]; exact tsum_zero
      intro y
      rw [if_neg (fun ⟨hl, ht⟩ => hcond ⟨by omega, take_mono y ht⟩), mul_zero]

lemma probOutput_bind_eq_mul {mx : m α} {my : α → m β} {y : β} (x : α)
    (h : ∀ x' ∈ support mx, y ∈ support (my x') → x' = x) :
    Pr[= y | mx >>= my] = Pr[= x | mx] * Pr[= y | my x] := by
  rw [probOutput_bind_eq_tsum]
  refine (tsum_eq_single x ?_)
  grind [= mul_eq_zero]

@[simp]
lemma probOutput_cons_map [LawfulMonad m] [DecidableEq α]
    (mx : m (List α)) (x : α) (xs : List α) :
    Pr[= xs | cons x <$> mx] =
      if hxs : xs = [] then 0 else Pr[= xs.head hxs | (pure x : m α)] * Pr[= xs.tail | mx] := by
  split
  case isTrue h =>
    subst h
    apply probOutput_eq_zero_of_not_mem_support
    simp [support_map]
  case isFalse h =>
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil h
    simp only [List.head_cons, List.tail_cons]
    by_cases hyx : y = x
    · subst hyx
      rw [probOutput_map_injective mx (List.cons_injective (a := y)), probOutput_pure_self, one_mul]
    · simp only [hyx, probOutput_pure, ↓reduceIte, zero_mul]
      apply probOutput_eq_zero_of_not_mem_support
      simp only [support_map, Set.mem_image, not_exists, not_and]
      exact fun _ _ h' => hyx (List.cons.inj h').1.symm

@[simp]
lemma probOutput_list_mapM [LawfulMonad m] (xs : List α) (f : α → m β) (ys : List β) :
    Pr[= ys | xs.mapM f] = if ys.length = xs.length
      then (List.zipWith (Pr[= · | f ·]) ys xs).prod else 0 := by
  have : DecidableEq β := Classical.decEq β
  revert ys
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro ys
      split_ifs with hys
      · simp at hys
        obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hys
        simp
        rw [probOutput_bind_eq_mul y]
        simp [ih]
        clear *- hys
        aesop
        simp
      · refine probOutput_eq_zero_of_not_mem_support ?_
        simp only [mapM_cons, support_bind, Set.mem_iUnion, not_exists]
        intro y _ zs hzs
        rw [support_pure, Set.mem_singleton_iff]
        intro heq; subst heq
        have : zs.length = xs.length := by
          by_contra h
          have h1 := ih zs
          rw [if_neg h] at h1
          exact absurd h1 (probOutput_ne_zero_of_mem_support hzs)
        simp_all

@[simp]
lemma probOutput_list_mapM' [LawfulMonad m] (xs : List α) (f : α → m β) (ys : List β) :
    Pr[= ys | xs.mapM' f] = if ys.length = xs.length
      then (List.zipWith (Pr[= · | f ·]) ys xs).prod else 0 := by
  have : DecidableEq β := Classical.decEq β
  revert ys
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro ys
      split_ifs with hys
      · simp at hys
        obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hys
        simp
        rw [probOutput_bind_eq_mul y]
        simp [ih]
        clear *- hys
        aesop
        simp
      · refine probOutput_eq_zero_of_not_mem_support ?_
        simp only [List.mapM'_cons, support_bind, Set.mem_iUnion, not_exists]
        intro y _ zs hzs
        rw [support_pure, Set.mem_singleton_iff]
        intro heq; subst heq
        have : zs.length = xs.length := by
          by_contra h
          have h1 := ih zs
          rw [if_neg h] at h1
          exact absurd h1 (probOutput_ne_zero_of_mem_support hzs)
        simp_all



end mapM


section ListVector

variable {n : ℕ} (mx : m α) (my : m (List.Vector α n))

@[simp]
lemma support_seq_map_vector_cons [LawfulMonad m] :
    support ((· ::ᵥ ·) <$> mx <*> my) =
    {xs | xs.head ∈ support mx ∧ xs.tail ∈ support my} := by
  ext xs
  simp only [support_seq_map_eq_image2, Set.mem_image2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, v, hv, rfl⟩
    exact ⟨by simpa using ha, by simpa using hv⟩
  · rintro ⟨hh, ht⟩
    exact ⟨xs.head, hh, xs.tail, ht, List.Vector.cons_head_tail xs⟩

@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul [LawfulMonad m] [DecidableEq α]
    (xs : List.Vector α (n + 1)) :
    Pr[= xs | (· ::ᵥ ·) <$> mx <*> my] = Pr[= xs.head | mx] * Pr[= xs.tail | my] := by
  rw [← probOutput_seq_map_eq_mul_of_injective2 mx my _ Vector.injective2_cons,
    List.Vector.cons_head_tail]

@[simp]
lemma probOutput_seq_map_vector_cons_eq_mul' [LawfulMonad m] [DecidableEq α]
    (xs : List.Vector α (n + 1)) :
    Pr[= xs | (fun xs x => x ::ᵥ xs) <$> my <*> mx] =
    Pr[= xs.head | mx] * Pr[= xs.tail | my] :=
  (probOutput_seq_map_swap mx my (· ::ᵥ ·) xs).trans
    (probOutput_seq_map_vector_cons_eq_mul mx my xs)

@[simp]
lemma probOutput_vector_toList [LawfulMonad m] [DecidableEq α]
    (mx' : m (List.Vector α n))
    (xs : List α) : Pr[= xs | List.Vector.toList <$> mx'] =
      if h : xs.length = n then Pr[= (⟨xs, h⟩ : List.Vector α n) | mx'] else 0 := by
  split_ifs with h
  · exact probOutput_map_eq_single (⟨xs, h⟩ : List.Vector α n) (fun _ _ h' => Subtype.ext h') rfl
  · apply probOutput_eq_zero_of_not_mem_support
    simp only [support_map, Set.mem_image]
    rintro ⟨ys, _, rfl⟩
    exact h ys.toList_length

end ListVector

section ListVectorMmap

variable {n : ℕ}

@[simp]
lemma neverFail_list_vector_mmap {f : α → m β} {as : List.Vector α n}
    (h : ∀ x ∈ as.toList, NeverFail (f x)) : NeverFail (List.Vector.mmap f as) := by
  induction as using List.Vector.inductionOn with
  | nil => simp [List.Vector.mmap]
  | @cons n x xs ih =>
    simp only [List.Vector.mmap_cons, HasEvalSPMF.neverFail_bind_iff]
    exact ⟨h x (by simp), fun _ _ =>
      ⟨ih (fun x' hx' => h x' (by simp [hx'])), fun _ _ => inferInstance⟩⟩

end ListVectorMmap

-- TODO: neverFail_array_mapM — Array.mapM doesn't have a clean reduction to
-- List.mapM in the current Lean/Mathlib version. A bridge lemma like
-- `Array.mapM_eq_mapM_toList` would be needed.

-- TODO: mem_support_vector_mapM and neverFail_vector_mapM for Std.Vector —
-- Vector.mapM (Std/Batteries) uses MonadSatisfying internally and doesn't
-- reduce cleanly for generic HasEvalSPMF monads.

/-! ## NeverFail lemmas for list monadic operations -/

section NeverFail

variable {α β : Type*} {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HasEvalSPMF m]

@[simp]
lemma neverFail_list_mapM {f : α → m β} {as : List α}
    (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (as.mapM f) := by
  induction as with
  | nil => rw [List.mapM_nil]; infer_instance
  | cons a as ih =>
    simp only [List.mapM_cons, HasEvalSPMF.neverFail_bind_iff]
    exact ⟨h a (.head ..), fun _ _ =>
      ⟨ih (fun x hx => h x (.tail _ hx)), fun _ _ => inferInstance⟩⟩

omit [LawfulMonad m] in
@[simp]
lemma neverFail_list_mapM' {f : α → m β} {as : List α}
    (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (as.mapM' f) := by
  induction as with
  | nil => rw [List.mapM'_nil]; infer_instance
  | cons a as ih =>
    simp only [List.mapM'_cons, HasEvalSPMF.neverFail_bind_iff]
    exact ⟨h a (.head ..), fun _ _ =>
      ⟨ih (fun x hx => h x (.tail _ hx)), fun _ _ => inferInstance⟩⟩

@[simp]
lemma neverFail_list_flatMapM {f : α → m (List β)} {as : List α}
    (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (as.flatMapM f) := by
  induction as with
  | nil => simp only [List.flatMapM_nil]; infer_instance
  | cons a as ih =>
    simp only [List.flatMapM_cons, bind_pure_comp,
      HasEvalSPMF.neverFail_bind_iff, HasEvalSPMF.neverFail_map_iff]
    exact ⟨h a (.head ..), fun _ _ => ih (fun x hx => h x (.tail _ hx))⟩

@[simp]
lemma neverFail_list_filterMapM {f : α → m (Option β)} {as : List α}
    (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (as.filterMapM f) := by
  induction as with
  | nil => simp only [List.filterMapM_nil]; infer_instance
  | cons a as ih =>
    simp only [List.filterMapM_cons, HasEvalSPMF.neverFail_bind_iff]
    refine ⟨h a (.head ..), fun y _ => ?_⟩
    have h_tail := ih (fun x hx => h x (.tail _ hx))
    cases y with
    | none => exact h_tail
    | some b =>
      simp only [HasEvalSPMF.neverFail_bind_iff]
      exact ⟨h_tail, fun _ _ => inferInstance⟩

variable {s : Type*}

omit [LawfulMonad m] in
@[simp]
lemma neverFail_list_foldlM {f : s → α → m s} {init : s} {as : List α}
    (h : ∀ i, ∀ x ∈ as, NeverFail (f i x)) : NeverFail (as.foldlM f init) := by
  induction as generalizing init with
  | nil => rw [List.foldlM_nil]; infer_instance
  | cons b bs ih =>
    simp only [List.foldlM_cons, HasEvalSPMF.neverFail_bind_iff]
    exact ⟨h init b (.head ..), fun _ _ => ih (fun i x hx => h i x (.tail _ hx))⟩

@[simp]
lemma neverFail_list_foldrM {f : α → s → m s} {init : s} {as : List α}
    (h : ∀ i, ∀ x ∈ as, NeverFail (f x i)) : NeverFail (as.foldrM f init) := by
  induction as generalizing init with
  | nil => rw [List.foldrM_nil]; infer_instance
  | cons b bs ih =>
    simp only [List.foldrM_cons, HasEvalSPMF.neverFail_bind_iff]
    exact ⟨ih (fun i x hx => h i x (.tail _ hx)), fun y _ => h y b (.head ..)⟩

end NeverFail
