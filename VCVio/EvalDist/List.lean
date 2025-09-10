/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation Distributions of Computations with `Prod`

File for lemmas about `evalDist` and `support` involving `Prod`.
-/

-- section List

-- open List

-- variable (oa : OracleComp spec α) (ob : OracleComp spec (List α))

-- lemma mem_support_seq_map_cons_iff' (xs : List α) : xs ∈ (List.cons <$> oa <*> ob).support ↔
--     xs.recOn False (λ x xs _ ↦ x ∈ oa.support ∧ xs ∈ ob.support) := by
--   cases xs <;> simp

-- lemma mem_support_seq_map_cons_iff (xs : List α) (h : xs ≠ []) :
--     xs ∈ (List.cons <$> oa <*> ob).support ↔
--       xs.head h ∈ oa.support ∧ xs.tail ∈ ob.support := by
--   obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
--   simp [h]

-- lemma cons_mem_support_seq_map_cons_iff (x : α) (xs : List α) :
--     x :: xs ∈ (cons <$> oa <*> ob).support ↔ x ∈ oa.support ∧ xs ∈ ob.support := by
--   simp only [support_seq_map_eq_image2, Set.mem_image2, List.cons.injEq, exists_eq_right_right]

-- lemma mem_finSupport_seq_map_cons_iff' [spec.FiniteRange] [spec.DecidableEq] [DecidableEq α]
--     (xs : List α) : xs ∈ (cons <$> oa <*> ob).finSupport ↔
--       xs.recOn False (λ x xs _ ↦ x ∈ oa.finSupport ∧ xs ∈ ob.finSupport) := by
--   simp_rw [mem_finSupport_iff_mem_support, mem_support_seq_map_cons_iff' oa ob xs]

-- lemma mem_finSupport_seq_map_cons_iff [spec.FiniteRange] [spec.DecidableEq] [DecidableEq α]
--     (xs : List α) (h : xs ≠ []) : xs ∈ (cons <$> oa <*> ob).finSupport ↔
--       xs.head h ∈ oa.finSupport ∧ xs.tail ∈ ob.finSupport := by
--   simp_rw [mem_finSupport_iff_mem_support, mem_support_seq_map_cons_iff oa ob xs h]

-- lemma cons_mem_finSupport_seq_map_cons_iff [spec.FiniteRange] [spec.DecidableEq] [DecidableEq α]
--     (x : α) (xs : List α) : x :: xs ∈ (cons <$> oa <*> ob).finSupport ↔
--       x ∈ oa.finSupport ∧ xs ∈ ob.finSupport := by
--   simp only [finSupport_seq_map_eq_image2, Finset.mem_image₂, List.cons.injEq,
--     exists_eq_right_right]

-- lemma probOutput_cons_seq_map_cons_eq_mul [spec.FiniteRange] [spec.DecidableEq] (x : α)
--     (xs : List α) : [= x :: xs | cons <$> oa <*> ob] = [= x | oa] * [= xs | ob] :=
--   probOutput_seq_map_eq_mul_of_injective2 oa ob List.cons List.injective2_cons x xs

-- lemma probOutput_cons_seq_map_cons_eq_mul' [spec.FiniteRange] [spec.DecidableEq] (x : α)
--     (xs : List α) : [= x :: xs | (λ xs x ↦ x :: xs) <$> ob <*> oa] = [= x | oa] * [= xs | ob] :=
--   (probOutput_seq_map_swap oa ob cons (x :: xs)).trans
--     (probOutput_cons_seq_map_cons_eq_mul oa ob x xs)

-- @[simp]
-- lemma probOutput_seq_map_cons_eq_mul [spec.FiniteRange] [spec.DecidableEq] (xs : List α) :
--     [= xs | cons <$> oa <*> ob] = if h : xs.isEmpty then 0 else
--       [= xs.head (h ∘ List.isEmpty_iff.2) | oa] * [= xs.tail | ob] :=
--   match xs with
--   | [] => by simp
--   | x :: xs => probOutput_cons_seq_map_cons_eq_mul oa ob x xs

-- section append

-- @[simp]
-- lemma probOutput_map_append_left [DecidableEq α] [spec.FiniteRange] (xs : List α)
--     (oa : OracleComp spec (List α)) (ys : List α) :
--     [= ys | (xs ++ ·) <$> oa] = if ys.take xs.length = xs
--       then [= ys.drop xs.length | oa] else 0 := by
--   split_ifs with h
--   · rw [probOutput_map_eq_tsum]
--     refine (tsum_eq_single (drop xs.length ys) ?_).trans ?_
--     · intro zs hzs
--       simp
--       intro h'
--       rw [← h] at h'
--       have := append_inj ((List.take_append_drop xs.length ys).trans h') rfl
--       refine (hzs this.2.symm).elim
--     · simp
--       intro h'
--       refine (h' ?_).elim
--       refine ((List.take_append_drop xs.length ys)).symm.trans ?_
--       refine congr_arg (· ++ _) h
--   · simp
--     intro x hx
--     refine λ h' ↦ h ?_
--     simp [← h', take_left']

-- end append

-- section mapM

-- -- @[simp]
-- -- lemma mem_support_list_mapM {f : α → OracleComp spec β} {as : List α}
-- --     (x : List β) : x ∈ (List.mapM f as).support ↔ ∀ i : Fin x.length, x[i] ∈ (f (as[i]'(by simp))).support := by
-- --   induction as with
-- --   | nil => simp [NeverFail_pure]
-- --   | cons a as ih =>
-- --     simp [List.mapM_cons, bind_pure_comp, NeverFail_bind_iff, NeverFail_map_iff, Vector.insertIdx]

-- @[simp]
-- lemma probFailure_list_mapM_loop {α β : Type*} [spec.FiniteRange]
--     (xs : List α) (f : α → OracleComp spec β) (ys : List β) :
--     [⊥ | List.mapM.loop f xs ys] = 1 - (xs.map (1 - [⊥ | f ·])).prod := by
--   revert ys
--   induction xs with
--   | nil => {
--     simp [List.mapM.loop]
--   }
--   | cons x xs h => {
--     intros ys
--     simp only [List.mapM.loop, List.map_cons, List.prod_cons]
--     rw [probFailure_bind_eq_sub_mul (1 - (List.map (fun x ↦ 1 - [⊥|f x]) xs).prod)]
--     · congr 2
--       refine ENNReal.sub_sub_cancel ENNReal.one_ne_top ?_
--       refine le_of_le_of_eq ?_ (one_pow (List.map (fun x ↦ 1 - [⊥|f x]) xs).length)
--       exact List.prod_le_pow_card _ _ (by simp)
--     · simp [h]
--   }

-- @[simp]
-- lemma probFailure_list_mapM {α β : Type*} [spec.FiniteRange] (xs : List α)
--     (f : α → OracleComp spec β) : [⊥ | xs.mapM f] = 1 - (xs.map (1 - [⊥ | f ·])).prod := by
--   rw [mapM, probFailure_list_mapM_loop]

-- -- @[simp]
-- -- lemma probOutput_list_mapM_loop' {α β : Type*} [DecidableEq β] [spec.FiniteRange]
-- --     (xs : List α) (f : α → OracleComp spec β) (ys : List β)
-- --     (zs : List β) : [= zs | List.mapM.loop f xs ys] =

-- @[simp]
-- lemma probOutput_list_mapM_loop {α β : Type*} [DecidableEq β] [spec.FiniteRange]
--     (xs : List α) (f : α → OracleComp spec β) (ys : List β)
--     (zs : List β) : [= zs | List.mapM.loop f xs ys] =
--       if zs.length = xs.length + ys.length ∧ zs.take ys.length = ys.reverse
--       then (List.zipWith (λ x z ↦ [= z | f x]) xs (zs.drop ys.length)).prod else 0 := by
--   rw [list_mapM_loop_eq]
--   rw [probOutput_map_append_left]
--   by_cases h : take ys.length zs = ys.reverse
--   · simp only [length_reverse, h, ↓reduceIte, and_true]
--     induction zs using List.reverseRecOn with
--     | nil => {
--       simp at h
--       simp [h]
--       cases xs with
--       | nil => {
--         simp [mapM.loop]
--       }
--       | cons x xs => {
--         simp [mapM.loop]
--         intro _ _
--         rw [list_mapM_loop_eq]
--         simp
--       }
--     }
--     | append_singleton zs z hzs => {
--       cases xs with
--       | nil => {
--         suffices zs.length + 1 ≤ ys.length ↔ zs.length + 1 = ys.length
--         by simp [mapM.loop, this]
--         refine LE.le.le_iff_eq ?_
--         simpa using congr_arg length h
--       }
--       | cons x xs => {
--         simp [Nat.succ_add, mapM.loop]
--         sorry
--       }
--     }
--   · simp [h]

-- @[simp]
-- lemma probOutput_list_mapM {α β : Type*} [spec.FiniteRange] (xs : List α)
--     (f : α → OracleComp spec β) (ys : List β) : [= ys | xs.mapM f] = if ys.length = xs.length
--       then (List.zipWith (fun x y => [= y | f x]) xs ys).prod else 0 := by
--   have : DecidableEq β := Classical.decEq β
--   simp [List.mapM]

-- end mapM

-- section NeverFail

-- /-- If each element of a list is mapped to a computation that never fails, then the computation
--   obtained by monadic mapping over the list also never fails. -/
-- @[simp] lemma NeverFail_list_mapM {f : α → OracleComp spec β} {as : List α}
--     (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (mapM f as) := by
--   induction as with
--   | nil => simp only [mapM, mapM.loop, reverse_nil, NeverFail_pure]
--   | cons a as ih =>
--     simp [mapM_cons, h]
--     exact fun _ _ => ih (by simp at h; exact h.2)

-- @[simp] lemma NeverFail_list_mapM' {f : α → OracleComp spec β} {as : List α}
--     (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (mapM' f as) := by
--   rw [mapM'_eq_mapM]
--   exact NeverFail_list_mapM h

-- @[simp] lemma NeverFail_list_flatMapM {f : α → OracleComp spec (List β)} {as : List α}
--     (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (flatMapM f as) := by
--   induction as with
--   | nil => simp only [flatMapM_nil, NeverFail_pure]
--   | cons a as ih =>
--     simp only [flatMapM_cons, bind_pure_comp, NeverFail_bind_iff, NeverFail_map_iff]
--     exact ⟨h a (by simp), fun y hy => ih (fun x hx => h x (by simp [hx]))⟩

-- @[simp] lemma NeverFail_list_filterMapM {f : α → OracleComp spec (Option β)} {as : List α}
--     (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (filterMapM f as) := by
--   induction as with
--   | nil => simp only [filterMapM_nil, NeverFail_pure]
--   | cons a as ih =>
--     simp only [filterMapM_cons, bind_pure_comp, NeverFail_bind_iff, NeverFail_map_iff]
--     refine ⟨h a (by simp), fun y hy => ?_⟩
--     rcases y with _ | y <;> simp <;> exact ih (fun x hx => h x (by simp [hx]))

-- variable {s : Type v}

-- @[simp] lemma NeverFail_list_foldlM {f : s → α → OracleComp spec s} {init : s} {as : List α}
--     (h : ∀ i, ∀ x ∈ as, NeverFail (f i x)) : NeverFail (foldlM f init as) := by
--   induction as generalizing init with
--   | nil => simp only [foldlM, reverse_nil, NeverFail_pure]
--   | cons b bs ih =>
--       simp only [foldlM_cons, NeverFail_bind_iff, mem_cons, true_or, h, true_and]
--       exact fun _ _ => ih (fun i x hx' => h i x (by simp [hx']))

-- @[simp] lemma NeverFail_list_foldrM {f : α → s → OracleComp spec s} {init : s} {as : List α}
--     (h : ∀ i, ∀ x ∈ as, NeverFail (f x i)) : NeverFail (foldrM f init as) := by
--   induction as generalizing init with
--   | nil => simp only [foldrM, reverse_nil, foldlM_nil, NeverFail_pure]
--   | cons b bs ih =>
--       simp only [foldrM_cons, NeverFail_bind_iff]
--       exact ⟨ih (fun i x hx => h i x (by simp [hx])), fun y _ => h y b (by simp)⟩

-- end NeverFail

-- end List

-- section List.Vector

-- variable {n : ℕ} (oa : OracleComp spec α) (ob : OracleComp spec (List.Vector α n))

-- @[simp]
-- lemma support_seq_map_vector_cons : ((· ::ᵥ ·) <$> oa <*> ob).support =
--     {xs | xs.head ∈ oa.support ∧ xs.tail ∈ ob.support} := by
--   refine Set.ext (λ xs ↦ ?_)
--   simp [Set.ext_iff, @eq_comm _ _ xs, List.Vector.eq_cons_iff]

-- @[simp]
-- lemma probOutput_seq_map_vector_cons_eq_mul [spec.FiniteRange] [spec.DecidableEq]
--     (xs : List.Vector α (n + 1)) :
--     [= xs | (· ::ᵥ ·) <$> oa <*> ob] = [= xs.head | oa] * [= xs.tail | ob] := by
--   rw [← probOutput_seq_map_eq_mul_of_injective2 oa ob _ Vector.injective2_cons,
--     List.Vector.cons_head_tail]

-- @[simp]
-- lemma probOutput_seq_map_vector_cons_eq_mul' [spec.FiniteRange] [spec.DecidableEq]
--     (xs : List.Vector α (n + 1)) :
--     [= xs | (λ xs x ↦ x ::ᵥ xs) <$> ob <*> oa] = [= xs.head | oa] * [= xs.tail | ob] :=
--   (probOutput_seq_map_swap oa ob (· ::ᵥ ·) (xs)).trans
--     (probOutput_seq_map_vector_cons_eq_mul oa ob xs)

-- @[simp]
-- lemma probOutput_vector_toList [spec.FiniteRange] [spec.DecidableEq]
--     {n : ℕ} (oa : OracleComp spec (List.Vector α n))
--     (xs : List α) : [= xs | List.Vector.toList <$> oa] =
--       if h : xs.length = n then [= ⟨xs, h⟩ | oa] else 0 := by
--   split_ifs with h
--   · refine probOutput_map_eq_single _ (λ _ _ h' ↦ List.Vector.eq ⟨xs, h⟩ _ h') rfl
--   · simp only [probOutput_eq_zero_iff, support_map, Set.mem_image, not_exists, not_and]
--     exact λ ys _ h' ↦ h (h' ▸ ys.toList_length)

-- end List.Vector

-- section List.Vector -- TODO: seperate file for vectors?

-- variable {n : ℕ}

-- @[simp] lemma NeverFail_list_vector_mmap {f : α → OracleComp spec β} {as : List.Vector α n}
--     (h : ∀ x ∈ as.toList, NeverFail (f x)) : NeverFail (List.Vector.mmap f as) := by
--   induction as with
--   | nil => simp only [List.Vector.mmap, NeverFail_pure]
--   | @cons n x xs ih =>
--     simp only [List.Vector.mmap_cons, bind_pure_comp, NeverFail_bind_iff, NeverFail_map_iff]
--     exact ⟨h x (by simp), fun y hy => ih (fun x' hx' => h x' (by simp [hx']))⟩

-- end List.Vector

-- section Array -- TODO: seperate file for arrays

-- open Array

-- @[simp] lemma NeverFail_array_mapM {f : α → OracleComp spec β} {as : Array α}
--     (h : ∀ x ∈ as, NeverFail (f x)) : NeverFail (mapM f as) := by
--   induction ha : as.toList generalizing as with
--   | nil => simp_all [h, Array.mapM, mapM.map, NeverFail_pure]
--   | cons x xs ih =>
--     rw [mapM_eq_mapM_toList, NeverFail_map_iff]

--     simp_rw [mapM_eq_mapM_toList, ha] at ih ⊢
--     simp at ih ⊢
--     specialize ih h
--     -- boring case analysis
--     sorry

-- end Array

-- section Vector -- TODO: seperate file for vectors

-- lemma mem_support_vector_mapM {n} {f : α → OracleComp spec β} {as : Vector α n} {x : Vector β n} :
--     x ∈ (Vector.mapM f as).support ↔ ∀ i : Fin n, x[i] ∈ (f as[i]).support := by
--   induction as using Vector.induction with
--   | v_empty => simp [NeverFail_pure]
--   | v_insert hd tl ih =>
--     simp [Vector.mapM_append, bind_pure_comp, NeverFail_bind_iff, NeverFail_map_iff, Vector.insertIdx]
--     sorry

-- @[simp] lemma NeverFail_vector_mapM {n} {f : α → OracleComp spec β} {as : Vector α n}
--     (h : ∀ x ∈ as.toList, NeverFail (f x)) : NeverFail (Vector.mapM f as) := by
--   induction as using Vector.induction with
--   | v_empty => simp [NeverFail_pure]
--   | v_insert hd tl ih =>
--     simp_all [Vector.mapM_append, bind_pure_comp, NeverFail_bind_iff, NeverFail_map_iff, Vector.insertIdx]
--     suffices hnew : (Vector.mapM f (#v[hd] ++ tl)).NeverFail by
--       simp only [HAppend.hAppend, Append.append, Vector.append] at hnew
--       convert hnew using 2
--       · exact Nat.add_comm _ _
--       · exact Nat.add_comm _ _
--       · rename_i h1 h2; exact Vector.heq_of_toArray_eq_of_size_eq rfl (Nat.add_comm _ _)
--     rw [Vector.mapM_append]
--     simp
--     exact ⟨by simpa [Vector.mapM, Vector.mapM.go] using h.1, fun _ _ => ih⟩

-- end Vector

-- end OracleComp
