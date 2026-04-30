/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Loom.Tactic.Attr

public import Loom.Triple.Basic
import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Range.Polymorphic
import Init.Data.Slice.Array
public import Std.Do.Triple.SpecLemmas

-- This public import is a workaround for #10652.
-- Without it, adding the `spec` attribute for `instMonadLiftTOfMonadLift` will fail.
public import Init.Data.Iterators.Lemmas.Combinators.FilterMap
public import Init.Data.Range
import Init.Data.Iterators.Lemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Range
import Init.Data.List.TakeDrop
import Init.Data.Nat.Mod
import Init.Data.Slice.Lemmas
import Init.Omega
public import Init.Data.String.Defs
public import Init.Data.String.Iterate
import Init.Data.String.Lemmas.Splits
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Iterate

set_option linter.missingDocs true

@[expose] public section

/-!
# Hoare triple specifications for select functions

This module contains Hoare triple specifications for some functions in Core.
-/

-- namespace Std.Legacy.Range

-- -- /--
-- -- Converts a range to the list of all numbers in the range.
-- -- -/
-- -- abbrev toList (r : Std.Legacy.Range) : List Nat :=
-- --   List.range' r.start ((r.stop - r.start + r.step - 1) / r.step) r.step

-- end Std.Legacy.Range

-- namespace List

-- /--
-- A pointer at a specific location in a list. List cursors are used in loop invariants for the
-- `mvcgen` tactic.

-- Moving the cursor to the left or right takes time linear in the current position of the cursor, so
-- this data structure is not appropriate for run-time code.
-- -/
-- @[ext]
-- structure Cursor {α : Type u} (l : List α) : Type u where
--   /--
--   The elements before to the current position in the list.
--   -/
--   «prefix» : List α
--   /--
--   The elements starting at the current position. If the position is after the last element of the
--   list, then the suffix is empty; otherwise, the first element of the suffix is the current element
--   that the cursor points to.
--   -/
--   suffix : List α
--   /-- Appending the prefix to the suffix yields the original list. -/
--   property : «prefix» ++ suffix = l

-- /--
-- Creates a cursor at position `n` in the list `l`.
-- The prefix contains the first `n` elements, and the suffix contains the remaining elements.
-- If `n` is larger than the length of the list, the cursor is positioned at the end of the list.
-- -/
-- def Cursor.at (l : List α) (n : Nat) : Cursor l := ⟨l.take n, l.drop n, by simp⟩

-- /--
-- Creates a cursor at the beginning of the list (position 0).
-- The prefix is empty and the suffix is the entire list.
-- -/
-- abbrev Cursor.begin (l : List α) : Cursor l := .at l 0

-- /--
-- Creates a cursor at the end of the list.
-- The prefix is the entire list and the suffix is empty.
-- -/
-- abbrev Cursor.end (l : List α) : Cursor l := .at l l.length

-- /--
-- Returns the element at the current cursor position.

-- Requires that is a current element: the suffix must be non-empty, so the cursor is not at the end of
-- the list.
-- -/
-- def Cursor.current {α} {l : List α} (c : Cursor l) (h : 0 < c.suffix.length := by get_elem_tactic) : α :=
--   c.suffix[0]'(by simp [h])

-- /--
-- Advances the cursor by one position, moving the current element from the suffix to the prefix.

-- Requires that the cursor is not already at the end of the list.
-- -/
-- def Cursor.tail (s : Cursor l) (h : 0 < s.suffix.length := by get_elem_tactic) : Cursor l :=
--   { «prefix» := s.prefix ++ [s.current]
--   , suffix := s.suffix.tail
--   , property := by
--       have : s.suffix ≠ [] := by simp only [List.ne_nil_iff_length_pos, h]
--       simp [current, ←List.head_eq_getElem this, s.property] }

-- @[simp, grind =] theorem Cursor.prefix_at (l : List α) : (Cursor.at l n).prefix = l.take n := rfl
-- @[simp, grind =] theorem Cursor.suffix_at (l : List α) : (Cursor.at l n).suffix = l.drop n := rfl
-- @[simp, grind =] theorem Cursor.current_at (l : List α) (h : n < l.length) :
--     (Cursor.at l n).current  (by simpa using Nat.sub_lt_sub_right (Nat.le_refl n) h) = l[n] := by
--   induction n with simp_all [Cursor.current]
-- @[simp, grind =] theorem Cursor.tail_at (l : List α) (h : n < l.length) :
--     (Cursor.at l n).tail (by simpa using Nat.sub_lt_sub_right (Nat.le_refl n) h) = Cursor.at l (n + 1) := by
--   simp [Cursor.tail, Cursor.at, Cursor.current]

-- /--
-- The position of the cursor in the list.
-- It's a shortcut for the number of elements in the prefix.
-- -/
-- abbrev Cursor.pos (c : Cursor l) : Nat := c.prefix.length

-- @[simp, grind =]
-- theorem Cursor.pos_at {l : List α} {n : Nat} (h : n < l.length) :
--     (Cursor.at l n).pos = n := by simp only [pos, «at», length_take]; omega

-- @[simp]
-- theorem Cursor.pos_mk {l pre suff : List α} (h : pre ++ suff = l) :
--     (Cursor.mk pre suff h).pos = pre.length := rfl

-- @[grind →]
-- theorem eq_of_range'_eq_append_cons (h : range' s n step = xs ++ cur :: ys) :
--     cur = s + step * xs.length := by
--   rw [range'_eq_append_iff] at h
--   obtain ⟨k, hk, hxs, hcur⟩ := h
--   have h := (range'_eq_cons_iff.mp hcur.symm).1.symm
--   have hk : k = xs.length := by simp_all [length_range']
--   simp only [h, hk, Nat.add_left_cancel_iff]
--   apply Nat.mul_comm

-- @[grind →]
-- theorem length_of_range'_eq_append_cons (h : range' s n step = xs ++ cur :: ys) :
--     n = xs.length + ys.length + 1 := by
--   have : n = (range' s n step).length := by simp
--   simpa [h] using this

-- @[grind →]
-- theorem mem_of_range'_eq_append_cons (h : range' s n step = xs ++ i :: ys) :
--     i ∈ range' s n step := by simp [h]

-- @[grind →]
-- theorem gt_of_range'_eq_append_cons (h : range' s n step = xs ++ i :: ys) (hstep : 0 < step) (hj : j ∈ xs) :
--     j < i := by
--   obtain ⟨nxs, _, rfl, htail⟩ := range'_eq_append_iff.mp h
--   obtain ⟨rfl, _⟩ := range'_eq_cons_iff.mp htail.symm
--   simp only [mem_range'] at hj
--   obtain ⟨i, _, rfl⟩ := hj
--   apply Nat.add_lt_add_left
--   simp [Nat.mul_comm, *]

-- @[grind →]
-- theorem lt_of_range'_eq_append_cons (h : range' s n step = xs ++ i :: ys) (hstep : 0 < step) (hj : j ∈ ys) :
--     i < j := by
--   obtain ⟨k, hk, rfl, htail⟩ := range'_eq_append_iff.mp h
--   obtain ⟨rfl, _, _, _⟩ := range'_eq_cons_iff.mp htail.symm
--   simp only [mem_range'] at hj
--   omega

-- end List


namespace Std.Do'

open Lean.Order

universe u v
variable {m : Type u → Type v} {Pred : Type u} {EPred : Type u}

/-! # `Monad` -/

variable [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]

theorem Spec.pure' (a : α) (h : pre ⊑ post a) :
    Triple pre (Pure.pure (f := m) a) post epost :=
  Triple.pure a h

@[lspec]
theorem Spec.pure (a : α) :
    Triple (post a) (Pure.pure (f := m) a) post epost :=
  Spec.pure' a PartialOrder.rel_refl

theorem Spec.bind' (x : m α) (f : α → m β)
    (h : Triple pre x (fun a => wp (f a) post epost) epost) :
    Triple pre (x >>= f) post epost :=
  Triple.bind x f (fun a => wp (f a) post epost) h (fun _ => Triple.iff.mpr PartialOrder.rel_refl)

@[lspec]
theorem Spec.bind (x : m α) (f : α → m β) :
    Triple (wp x (fun a => wp (f a) post epost) epost) (x >>= f) post epost :=
  Spec.bind' x f (Triple.iff.mpr PartialOrder.rel_refl)


theorem Spec.map' (f : α → β) (x : m α)
    (h : Triple pre x (fun a => post (f a)) epost) :
    Triple pre (f <$> x) post epost :=
  Triple.iff.mpr (PartialOrder.rel_trans (Triple.iff.mp h) (WP.wp_map f x post epost))

@[lspec]
theorem Spec.map (f : α → β) (x : m α) :
    Triple (wp x (fun a => post (f a)) epost) (f <$> x) post epost :=
  Spec.map' f x (Triple.iff.mpr PartialOrder.rel_refl)

theorem Spec.seq' (x : m (α → β)) (y : m α)
    (h : Triple pre x (fun f => wp y (fun a => post (f a)) epost) epost) :
    Triple pre (x <*> y) post epost :=
  Triple.iff.mpr (PartialOrder.rel_trans (Triple.iff.mp h) (WP.wp_seq x y post epost))

@[lspec]
theorem Spec.seq (x : m (α → β)) (y : m α) :
    Triple (wp x (fun f => wp y (fun a => post (f a)) epost) epost) (x <*> y) post epost :=
  Spec.seq' x y (Triple.iff.mpr PartialOrder.rel_refl)

/-! # `MonadLift` -/

@[lspec]
theorem Spec.monadLift_StateT (x : m α) (post : α → σ → Pred) :
    Triple (fun s => wp x (fun a => post a s) epost) (MonadLift.monadLift x : StateT σ m α) post epost :=
  Triple.iff.mpr (WP.monadLift_StateT_wp x post)

@[lspec]
theorem Spec.monadLift_ReaderT (x : m α) (post : α → ρ → Pred) :
    Triple (fun r => wp x (fun a => post a r) epost) (MonadLift.monadLift x : ReaderT ρ m α) post epost :=
  Triple.iff.mpr (by rw [WP.monadLift_ReaderT_wp]; rfl)

@[lspec]
theorem Spec.monadLift_ExceptT (x : m α) (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp x post epost.tail) (MonadLift.monadLift x : ExceptT ε m α) post epost :=
  Triple.iff.mpr (WP.monadLift_ExceptT_wp x post epost)

@[lspec]
theorem Spec.monadLift_OptionT (x : m α) (post : α → Pred) (epost : EPost.cons Pred EPred) :
    Triple (wp x post epost.tail) (MonadLift.monadLift x : OptionT m α) post epost :=
  Triple.iff.mpr (WP.monadLift_OptionT_wp x)

/-! # `MonadFunctor` -/

attribute [refl] PartialOrder.rel_refl

@[lspec]
theorem Spec.monadMap_StateT
    (f : ∀{β}, m β → m β) {α} (x : StateT σ m α) (post : α → σ → Pred) :
    Triple (fun s => wp (f (x.run s)) (fun (a, s') => post a s') epost)
      (MonadFunctor.monadMap (m := m) f x : StateT σ m α) post epost :=
  Triple.iff.mpr (by rw [WP.monadMap_StateT_wp]; rfl)

@[lspec]
theorem Spec.monadMap_ReaderT
    (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (post : α → ρ → Pred) :
    Triple (fun r => wp (f (x.run r)) (fun a => post a r) epost)
      (MonadFunctor.monadMap (m := m) f x : ReaderT ρ m α) post epost :=
  Triple.iff.mpr (by rw [WP.monadMap_ReaderT_wp]; rfl)

@[lspec]
theorem Spec.monadMap_ExceptT
    (f : ∀{β}, m β → m β) {α} (x : ExceptT ε m α) (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (f x.run) (epost.pushExcept post) epost.tail)
      (MonadFunctor.monadMap (m := m) f x : ExceptT ε m α) post epost :=
  Triple.iff.mpr (by rw [WP.monadMap_ExceptT_wp])

@[lspec]
theorem Spec.monadMap_OptionT
    (f : ∀{β}, m β → m β) {α} (x : OptionT m α) (post : α → Pred) (epost : EPost.cons Pred EPred) :
    Triple (wp (f x.run) (epost.pushOption post) epost.tail)
      (MonadFunctor.monadMap (m := m) f x : OptionT m α) post epost :=
  Triple.iff.mpr (by rw [WP.monadMap_OptionT_wp])


@[lspec]
theorem Spec.monadMap_refl (x : m α) :
    Triple (wp (f x : m α) post epost)
      (MonadFunctorT.monadMap f x : m α) post epost :=
  Triple.iff.mpr (by rw [WP.monadMap_refl_wp])

/-! # `MonadControl` -/

@[lspec]
theorem Spec.liftWith_StateT
    (f : (∀{β}, StateT σ m β → m (β × σ)) → m α) (post : α → σ → Pred) :
    Triple (fun s => wp (f (fun x => x.run s)) (fun a => post a s) epost)
      (MonadControl.liftWith (m:=m) f : StateT σ m α) post epost :=
  Triple.iff.mpr (by intro s; simp [WP.liftWith_StateT_wp f]; apply WP.wp_map'; ext; rfl)

@[lspec]
theorem Spec.liftWith_ReaderT
    (f : (∀{β}, ReaderT ρ m β → m β) → m α) (post : α → ρ → Pred) :
    Triple (fun r => wp (f (fun x => x.run r)) (fun a => post a r) epost)
      (MonadControl.liftWith (m:=m) f : ReaderT ρ m α) post epost :=
  Triple.iff.mpr (by intro r; simp [WP.liftWith_ReaderT_wp f]; rfl)

@[lspec]
theorem Spec.liftWith_ExceptT
    (f : (∀{β}, ExceptT ε m β → m (Except ε β)) → m α) (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (f (fun x => x.run)) post epost.tail)
      (MonadControl.liftWith (m:=m) f : ExceptT ε m α) post epost :=
  Triple.iff.mpr (by simp [WP.liftWith_ExceptT_wp f]; apply WP.wp_map'; ext; rfl)

@[lspec]
theorem Spec.liftWith_OptionT
    (f : (∀{β}, OptionT m β → m (Option β)) → m α) (post : α → Pred) (epost : EPost.cons Pred EPred) :
    Triple (wp (f (fun x => x.run)) post epost.tail)
      (MonadControl.liftWith (m:=m) f : OptionT m α) post epost :=
  Triple.iff.mpr (WP.liftWith_OptionT_wp f)

@[lspec]
theorem Spec.restoreM_StateT (x : m (α × σ)) (post : α → σ → Pred) :
    Triple (fun _ => wp x (fun (a, s) => post a s) epost)
      (MonadControl.restoreM (m:=m) x : StateT σ m α) post epost :=
  Triple.iff.mpr (WP.restoreM_StateT_wp x)

@[lspec]
theorem Spec.restoreM_ReaderT (x : m α) (post : α → ρ → Pred) :
    Triple (fun r => wp x (fun a => post a r) epost)
      (MonadControl.restoreM (m:=m) x : ReaderT ρ m α) post epost :=
  Triple.iff.mpr (by rw [WP.restoreM_ReaderT_wp]; rfl)

@[lspec]
theorem Spec.restoreM_ExceptT (x : m (@Except.{u, u} ε α)) (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp x (epost.pushExcept post) epost.tail)
      (MonadControl.restoreM (m:=m) x : ExceptT ε m α) post epost :=
  Triple.iff.mpr (by rw [WP.restoreM_ExceptT_wp])

@[lspec]
theorem Spec.restoreM_OptionT (x : m (Option α)) (post : α → Pred) (epost : EPost.cons Pred EPred) :
    Triple (wp x (epost.pushOption post) epost.tail)
      (MonadControl.restoreM (m:=m) x : OptionT m α) post epost :=
  Triple.iff.mpr (by rw [WP.restoreM_OptionT_wp])

/-! # `MonadControlT` -/


@[lspec]
theorem Spec.liftWith_refl
    (f : (∀{β}, m β → m β) → m α) :
    Triple (wp (f (fun x => x) : m α) post epost)
      (MonadControlT.liftWith (m:=m) f : m α) post epost :=
  Triple.iff.mpr (by rw [WP.liftWith_refl_wp])


@[lspec]
theorem Spec.restoreM_refl (x : stM m m α) :
    Triple (wp (Pure.pure x : m α) post epost)
      (MonadControlT.restoreM (m:=m) x : m α) post epost :=
  Triple.iff.mpr (by rw [WP.restoreM_refl_wp])

/-! # `ReaderT` -/

@[lspec]
theorem Spec.read_ReaderT (post : ρ → ρ → Pred) :
    Triple (fun r => post r r)
      (MonadReaderOf.read : ReaderT ρ m ρ) post epost :=
  Triple.iff.mpr (by intro r; simpa [MonadReaderOf.read] using
    (WP.wp_pure (m := m) (x := r) (post := fun a => post a r) (epost := epost)))
@[lspec]
theorem Spec.withReader_ReaderT (f : ρ → ρ) (x : ReaderT ρ m α) (post : α → ρ → Pred) :
    Triple (fun r => wp x (fun a _ => post a r) epost (f r))
      (MonadWithReaderOf.withReader f x : ReaderT ρ m α) post epost :=
  Triple.iff.mpr (by rw [WP.withReader_ReaderT_wp]; rfl)

@[lspec]
theorem Spec.adapt_ReaderT (f : ρ → ρ') (x : ReaderT ρ' m α) (post : α → ρ → Pred) :
    Triple (fun r => wp x (fun a _ => post a r) epost (f r))
      (ReaderT.adapt f x : ReaderT ρ m α) post epost :=
  Triple.iff.mpr (by rw [WP.adapt_ReaderT_wp]; rfl)

/-! # `StateT` -/

@[lspec]
theorem Spec.get_StateT (post : σ → σ → Pred) :
    Triple (fun s => post s s)
      (MonadStateOf.get : StateT σ m σ) post epost :=
  Triple.iff.mpr (by intro s; simpa [get_StateT] using
    (WP.wp_pure (m := m) (x := (s, s))
      (post := fun x => post x.fst x.snd) (epost := epost)))

@[lspec]
theorem Spec.set_StateT (s : σ) (post : PUnit → σ → Pred) :
    Triple (fun _ => post ⟨⟩ s)
      (set s : StateT σ m PUnit) post epost :=
  Triple.iff.mpr (by intro _; simpa [MonadStateOf.set] using
    (WP.wp_pure (m := m) (x := (PUnit.unit, s))
      (post := fun x => post x.fst x.snd) (epost := epost)))

@[lspec]
theorem Spec.modifyGet_StateT (f : σ → α × σ) (post : α → σ → Pred) :
    Triple (fun s => post (f s).1 (f s).2)
      (MonadStateOf.modifyGet f : StateT σ m α) post epost :=
  Triple.iff.mpr (by intro s; simpa [MonadStateOf.modifyGet] using
    (WP.wp_pure (m := m) (x := f s)
      (post := fun x => post x.fst x.snd) (epost := epost)))

/-! # `ExceptT` -/

@[lspec]
theorem Spec.run_ExceptT (x : ExceptT ε m α) (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp x post epost)
      (x.run : m (@Except.{u, u} ε α))
      (epost.pushExcept post)
      epost.tail :=
  Triple.iff.mpr (by simp [PartialOrder.rel_refl])

@[lspec]
theorem Spec.throw_ExceptT (err : ε) (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (epost.head err) (MonadExceptOf.throw err : ExceptT ε m α) post epost :=
  Triple.iff.mpr (by simpa [EPost.cons.pushExcept] using
    (WP.wp_pure (m := m) (x := Except.error err)
      (post := epost.pushExcept post)
      (epost := epost.tail)))

@[lspec]
theorem Spec.tryCatch_ExceptT (x : ExceptT ε m α) (h : ε → ExceptT ε m α) (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp x post ⟨fun e => wp (h e) post epost, epost.tail⟩)
      (MonadExceptOf.tryCatch x h : ExceptT ε m α) post epost :=
  Triple.iff.mpr (WP.tryCatch_ExceptT_wp x h)

@[lspec]
theorem Spec.orElse_ExceptT (x : ExceptT ε m α) (h : Unit → ExceptT ε m α) (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp x post ⟨fun _ => wp (h ()) post epost, epost.tail⟩)
      (OrElse.orElse x h : ExceptT ε m α) post epost :=
  Triple.iff.mpr (WP.orElse_ExceptT_wp x h)

@[lspec]
theorem Spec.adapt_ExceptT (f : ε → ε') (x : ExceptT ε m α) (post : α → Pred) (epost : EPost.cons (ε' → Pred) EPred) :
    Triple (wp x post ⟨fun e => epost.head (f e), epost.tail⟩)
      (ExceptT.adapt f x : ExceptT ε' m α) post epost :=
  Triple.iff.mpr (WP.adapt_ExceptT_wp f x)

/-! # `Except` -/

@[lspec]
theorem Spec.throw_Except (err : ε) :
    Triple (epost.head err) (MonadExceptOf.throw err : Except ε α) post epost :=
  Triple.iff.mpr (by rw [WP.throw_Except_wp]; rfl)

@[lspec]
theorem Spec.tryCatch_Except (x : Except ε α) (h : ε → Except ε α) :
    Triple (wp x post epost⟨fun e => wp (h e) post epost⟩)
      (MonadExceptOf.tryCatch x h : Except ε α) post epost :=
  Triple.iff.mpr (by rw [WP.tryCatch_Except_wp]; rfl)

@[lspec]
theorem Spec.orElse_Except (x : Except ε α) (h : Unit → Except ε α) :
    Triple (wp x post epost⟨fun (_ : ε) => wp (h ()) post epost⟩)
      (OrElse.orElse x h : Except ε α) post epost :=
  Triple.iff.mpr (by simp only [wp, WP.wpTrans, OrElse.orElse, MonadExcept.orElse]; cases x <;> rfl)

/-! # `OptionT` -/

@[lspec]
theorem Spec.run_OptionT (x : OptionT m α) (post : α → Pred) (epost : EPost.cons Pred EPred) :
    Triple (wp x post epost)
      (x.run : m (Option α))
      (epost.pushOption post)
      epost.tail :=
  Triple.iff.mpr (by rw [← OptionT.apply_wp])

@[lspec]
theorem Spec.throw_OptionT (err : PUnit) (post : α → Pred) (epost : EPost.cons Pred EPred) :
    Triple epost.head (MonadExceptOf.throw err : OptionT m α) post epost :=
  Triple.iff.mpr (WP.throw_OptionT_wp err)

@[lspec]
theorem Spec.tryCatch_OptionT (x : OptionT m α) (h : PUnit → OptionT m α) (post : α → Pred) (epost : EPost.cons Pred EPred) :
    Triple (wp x post ⟨wp (h ⟨⟩) post epost, epost.tail⟩)
      (MonadExceptOf.tryCatch x h : OptionT m α) post epost :=
  Triple.iff.mpr (WP.tryCatch_OptionT_wp x h)

@[lspec]
theorem Spec.orElse_OptionT (x : OptionT m α) (h : Unit → OptionT m α) (post : α → Pred) (epost : EPost.cons Pred EPred) :
    Triple (wp x post ⟨wp (h ()) post epost, epost.tail⟩)
      (OrElse.orElse x h : OptionT m α) post epost :=
  Triple.iff.mpr (WP.orElse_OptionT_wp x h)

/-! # `Option` -/

@[lspec]
theorem Spec.throw_Option (err : PUnit) :
    Triple epost (MonadExceptOf.throw err : Option α) post epost :=
  Triple.iff.mpr (by rw [WP.throw_Option_wp]; rfl)

@[lspec]
theorem Spec.tryCatch_Option (x : Option α) (h : PUnit → Option α) :
    Triple (wp x post (wp (h ⟨⟩) post epost))
      (MonadExceptOf.tryCatch x h : Option α) post epost :=
  Triple.iff.mpr (by rw [WP.tryCatch_Option_wp]; rfl)

@[lspec]
theorem Spec.orElse_Option (x : Option α) (h : Unit → Option α) (post : α → Prop) (epost : Prop) :
    Triple (wp x post (wp (h ()) post epost))
      (OrElse.orElse x h : Option α) post epost :=
  Triple.iff.mpr (by rw [WP.orElse_Option_wp]; rfl)

/-! # `EStateM` -/

@[lspec]
theorem Spec.get_EStateM (post : σ → σ → Prop) (epost : ε → σ → Prop) :
    Triple (fun s => post s s)
      (MonadStateOf.get : EStateM ε σ σ) post epost :=
  Triple.iff.mpr (by rw [WP.get_EStateM_wp]; rfl)

@[lspec]
theorem Spec.set_EStateM (s : σ) (post : PUnit → σ → Prop) (epost : ε → σ → Prop) :
    Triple (fun _ => post ⟨⟩ s)
      (MonadStateOf.set s : EStateM ε σ PUnit) post epost :=
  Triple.iff.mpr (by rw [WP.set_EStateM_wp]; rfl)

@[lspec]
theorem Spec.modifyGet_EStateM (f : σ → α × σ) (post : α → σ → Prop) (epost : ε → σ → Prop) :
    Triple (fun s => post (f s).1 (f s).2)
      (MonadStateOf.modifyGet f : EStateM ε σ α) post epost :=
  Triple.iff.mpr (by rw [WP.modifyGet_EStateM_wp]; rfl)

@[lspec]
theorem Spec.throw_EStateM (err : ε) (post : α → σ → Prop) (epost : ε → σ → Prop) :
    Triple (epost err) (MonadExceptOf.throw err : EStateM ε σ α) post epost :=
  Triple.iff.mpr (by rw [WP.throw_EStateM_wp]; rfl)

@[lspec]
theorem Spec.tryCatch_EStateM (x : EStateM ε σ α) (h : ε → EStateM ε σ α)
    (post : α → σ → Prop) (epost : ε → σ → Prop) :
    Triple (fun s => wp x post (fun e s' => wp (h e) post epost s') s)
      (MonadExceptOf.tryCatch x h : EStateM ε σ α) post epost :=
  Triple.iff.mpr (by rw [WP.tryCatch_EStateM_wp]; rfl)

@[lspec]
theorem Spec.orElse_EStateM (x : EStateM ε σ α) (h : Unit → EStateM ε σ α)
    (post : α → σ → Prop) (epost : ε → σ → Prop) :
    Triple (fun s => wp x post (fun _ s' => wp (h ()) post epost s') s)
      (OrElse.orElse x h : EStateM ε σ α) post epost :=
  Triple.iff.mpr (by rw [WP.orElse_EStateM_wp]; rfl)

@[lspec]
theorem Spec.adaptExcept_EStateM (f : ε → ε') (x : EStateM ε σ α)
    (post : α → σ → Prop) (epost : ε' → σ → Prop) :
    Triple (wp x post (fun e => epost (f e)))
      (EStateM.adaptExcept f x : EStateM ε' σ α) post epost :=
  Triple.iff.mpr (by rw [WP.adaptExcept_EStateM_wp]; rfl)

/-! # Lifting `MonadExceptOf` -/


@[lspec]
theorem Spec.throw_MonadExcept [MonadExceptOf ε m] (err : ε) :
    Triple (wp (MonadExceptOf.throw err : m α) post epost)
      (throw err : m α) post epost :=
  Triple.iff.mpr (by simp [throw, PartialOrder.rel_refl])


@[lspec]
theorem Spec.tryCatch_MonadExcept [MonadExceptOf ε m] (x : m α) (h : ε → m α) :
    Triple (wp (MonadExceptOf.tryCatch x h : m α) post epost)
      (tryCatch x h : m α) post epost :=
  Triple.iff.mpr (by rw [WP.tryCatch_MonadExcept_wp])

@[lspec]
theorem Spec.throw_ReaderT [MonadExceptOf ε m] (err : ε) (post : α → ρ → Pred) :
    Triple (wp (MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) err : m α) : ReaderT ρ m α) post epost)
      (MonadExceptOf.throw (ε:=ε) err : ReaderT ρ m α) post epost :=
  Triple.iff.mpr (by rw [WP.throw_ReaderT_lift_wp]; rfl)

@[lspec]
theorem Spec.throw_StateT [MonadExceptOf ε m] (err : ε) (post : α → σ → Pred) :
    Triple (wp (MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) err : m α) : StateT σ m α) post epost)
      (MonadExceptOf.throw (ε:=ε) err : StateT σ m α) post epost :=
  Triple.iff.mpr (by rw [WP.throw_StateT_lift_wp]; rfl)

@[lspec]
theorem Spec.throw_ExceptT_lift [MonadExceptOf ε m] (err : ε) (post : α → Pred) (epost : EPost.cons (ε' → Pred) EPred) :
    Triple (wp (MonadExceptOf.throw (ε:=ε) err : m (@Except.{u, u} ε' α))
        (fun r => match r with | .ok a => post a | .error e => epost.head e) epost.tail)
      (MonadExceptOf.throw (ε:=ε) err : ExceptT ε' m α) post epost :=
  Triple.iff.mpr (by rw [WP.throw_lift_ExceptT_wp]; apply WP.wp_consequence; intro r; cases r <;> rfl)

@[lspec]
theorem Spec.throw_Option_lift [MonadExceptOf ε m] (err : ε) (post : α → Pred) (epost : EPost.cons Pred EPred) :
    Triple (wp (MonadExceptOf.throw (ε:=ε) err : m (Option α))
        (epost.pushOption post) epost.tail)
      (MonadExceptOf.throw (ε:=ε) err : OptionT m α) post epost :=
  Triple.iff.mpr (by rw [WP.throw_lift_OptionT_wp])

@[lspec]
theorem Spec.tryCatch_ReaderT [MonadExceptOf ε m] (x : ReaderT ρ m α) (h : ε → ReaderT ρ m α)
    (post : α → ρ → Pred) :
    Triple (fun r => wp (MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α)
        (fun a => post a r) epost)
      (MonadExceptOf.tryCatch (ε:=ε) x h : ReaderT ρ m α) post epost :=
  Triple.iff.mpr (by rw [WP.tryCatch_ReaderT_lift_wp]; rfl)

@[lspec]
theorem Spec.tryCatch_StateT [MonadExceptOf ε m] (x : StateT σ m α) (h : ε → StateT σ m α)
    (post : α → σ → Pred) :
    Triple (fun s => wp (MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ))
        (fun (a, s') => post a s') epost)
      (MonadExceptOf.tryCatch (ε:=ε) x h : StateT σ m α) post epost :=
  Triple.iff.mpr (by rw [WP.tryCatch_StateT_lift_wp]; rfl)

@[lspec]
theorem Spec.tryCatch_ExceptT_lift [MonadExceptOf ε m] (x : ExceptT ε' m α) (h : ε → ExceptT ε' m α)
    (post : α → Pred) (epost : EPost.cons (ε' → Pred) EPred) :
    Triple (wp (MonadExceptOf.tryCatch (ε:=ε) x h : m (@Except.{u, u} ε' α))
        (fun | .ok a => post a | .error e => epost.head e) epost.tail)
      (MonadExceptOf.tryCatch (ε:=ε) x h : ExceptT ε' m α) post epost :=
  Triple.iff.mpr (by rw [WP.tryCatch_lift_ExceptT_wp]; apply WP.wp_consequence; intro r; cases r <;> rfl)

@[lspec]
theorem Spec.tryCatch_OptionT_lift [MonadExceptOf ε m] (x : OptionT m α) (h : ε → OptionT m α)
    (post : α → Pred) (epost : EPost.cons Pred EPred) :
    Triple (wp (MonadExceptOf.tryCatch (ε:=ε) x h : m (Option α))
        (epost.pushOption post) epost.tail)
      (MonadExceptOf.tryCatch (ε:=ε) x h : OptionT m α) post epost :=
  Triple.iff.mpr (by rw [WP.tryCatch_lift_OptionT_wp])

-- /-! # `MonadFunctorT` / `MonadControlT` transitivity -/


@[lspec]
theorem Spec.monadMap_trans
    {n₁ : Type u → Type v} {n₂ : Type u → Type v}
    [MonadFunctor n₁ m] [MonadFunctorT n₂ n₁]
    {f : ∀{β}, n₂ β → n₂ β}
    (x : m α) :
    Triple (wp (MonadFunctor.monadMap (m:=n₁) (MonadFunctorT.monadMap (m:=n₂) f) x : m α) post epost)
      (MonadFunctorT.monadMap (m:=n₂) f x : m α) post epost :=
  Triple.iff.mpr (by rw [WP.monadMap_trans_wp])


@[lspec]
theorem Spec.liftWith_trans
    {n₁ : Type u → Type v} {n₂ : Type u → Type v}
    [MonadControl n₁ m] [MonadControlT n₂ n₁]
    (f : (∀{β}, m β → n₂ (stM n₂ m β)) → n₂ α) :
    Triple (wp (MonadControl.liftWith (m:=n₁) fun x₂ => MonadControlT.liftWith fun x₁ => f (x₁ ∘ x₂) : m α) post epost)
      (MonadControlT.liftWith (m:=n₂) f : m α) post epost :=
  Triple.iff.mpr (by rw [WP.liftWith_trans_wp])


end Std.Do'

-- /-! # `ForIn` -/

namespace Std.Do'

universe u₁ u₂ v

variable {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v} {Pred : Type (max u₁ u₂)} {EPred : Type (max u₁ u₂)}
variable [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]

/--
The type of loop invariants used by the specifications of `for ... in ...` loops.
A loop invariant is a pair of:
* A function `List.Cursor xs × β → l` mapping the iteration cursor and state to a lattice element.
* An exception postcondition `e`.
-/
abbrev Invariant {α : Type u₁} (xs : List α) (β : Type u₂)
    (Pred : Type (max u₁ u₂)) :=
  (List.Cursor xs × β → Pred)

set_option linter.missingDocs false in
abbrev eInvariant (EPred : Type u) := EPred

@[lspec]
theorem Spec.forIn'_list
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [h]) b)
        (fun r => match r with
                 | .yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
                 | .done b' => inv (⟨xs, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs, [], by simp⟩, b))
      eInv := by
  suffices h : ∀ c,
      Triple
        (inv (c, init))
        (forIn' (m:=m) c.suffix init (fun a ha => f a (by simp [←c.property, ha])))
        (fun b => inv (⟨xs, [], by simp⟩, b))
        eInv
    from h ⟨[], xs, rfl⟩
  rintro ⟨pref, suff, h⟩
  induction suff generalizing pref init
  case nil => apply Triple.pure; simp [←h]; rfl
  case cons x suff ih =>
    simp only [List.forIn'_cons]
    apply Triple.bind
    case hx => exact step _ _ _ h.symm init
    case hf =>
      intro r
      split
      next b => -- .yield case
        simp
        have := @ih b (pref ++ [x]) (by simp [h])
        simp at this
        exact this
      next => -- .done case
        apply Triple.pure; rfl

@[lspec]
theorem Spec.forIn'_list_const_inv
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    {inv : (β → Pred)}
    {eInv : EPred}
    (step : ∀ x (hx : x ∈ xs) b,
      Triple
        (inv b)
        (f x hx b)
        (fun r => match r with | .yield b' => inv b' | .done b' => inv b')
        eInv) :
    Triple (inv init) (forIn' xs init f) inv eInv :=
  Spec.forIn'_list (fun p => inv p.2) eInv
    (fun _p c _s h b => step c (by rw [h]; exact List.mem_append_right _ (List.Mem.head _)) b)


@[lspec]
theorem Spec.forIn_list
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | .yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv (⟨xs, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs, [], by simp⟩, b))
      eInv := by
  simp only [← forIn'_eq_forIn]
  exact Spec.forIn'_list inv eInv step


@[lspec]
theorem Spec.forIn_list_const_inv
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    {inv : (β → Pred)}
    {eInv : EPred}
    (step : ∀ hd b,
      Triple
        (inv b)
        (f hd b)
        (fun r => match r with | .yield b' => inv b' | .done b' => inv b')
        eInv) :
    Triple (inv init) (forIn xs init f) inv eInv :=
  Spec.forIn_list (fun p => inv p.2) eInv (fun _p c _s _h b => step c b)

@[lspec]
theorem Spec.foldlM_list [LawfulMonad m]
    {xs : List α} {init : β} {f : β → α → m β}
    (inv : Invariant xs β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f b cur)
        (fun b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs, rfl⟩, init))
      (List.foldlM f init xs)
      (fun b => inv (⟨xs, [], by simp⟩, b))
      eInv := by
  have : xs.foldlM f init = forIn xs init (fun a b => ForInStep.yield <$> f b a) := by
    simp [List.forIn_yield_eq_foldlM, id_map']
  rw [this]
  apply Spec.forIn_list inv eInv
  intros
  apply Spec.map'
  apply step <;> assumption

@[lspec]
theorem Spec.foldlM_list_const_inv [LawfulMonad m]
    {xs : List α} {init : β} {f : β → α → m β}
    {inv : (β → Pred)}
    {eInv : EPred}
    (step : ∀ hd b,
      Triple
        (inv b)
        (f b hd)
        (fun b' => inv b')
        eInv) :
    Triple (inv init) (List.foldlM f init xs) inv eInv :=
    Spec.foldlM_list (fun p => inv p.2) eInv (fun _p c _s _h b => step c b)

@[lspec]
theorem Spec.forIn'_range {β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {xs : Std.Legacy.Range} {init : β} {f : (a : Nat) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [Std.Legacy.Range.mem_of_mem_range', h]) b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size, Std.Legacy.Range.size.eq_1]
  exact Spec.forIn'_list inv eInv (fun c hcur b => step c hcur b)

@[lspec]
theorem Spec.forIn_range {β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {xs : Std.Legacy.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  exact Spec.forIn_list inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn'_rcc {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {xs : Rcc α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [← Rcc.mem_toList_iff_mem, h]) b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Rcc.forIn'_eq_forIn'_toList]
  exact Spec.forIn'_list inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn_rcc {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {xs : Rcc α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [forIn]
  exact Spec.forIn'_rcc inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn'_rco {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    {xs : Rco α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [← Rco.mem_toList_iff_mem, h]) b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Rco.forIn'_eq_forIn'_toList]
  exact Spec.forIn'_list inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn_rco {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    {xs : Rco α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [forIn]
  exact Spec.forIn'_rco inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn'_rci {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LE α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {xs : Rci α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [← Rci.mem_toList_iff_mem, h]) b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Rci.forIn'_eq_forIn'_toList]
  exact Spec.forIn'_list inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn_rci {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LE α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {xs : Rci α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [forIn]
  exact Spec.forIn'_rci inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn'_roc {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LE α] [DecidableLE α] [LT α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    {xs : Roc α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [← Roc.mem_toList_iff_mem, h]) b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Roc.forIn'_eq_forIn'_toList]
  exact Spec.forIn'_list inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn_roc {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LE α] [DecidableLE α] [LT α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    {xs : Roc α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [forIn]
  exact Spec.forIn'_roc inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn'_roo {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {xs : Roo α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [← Roo.mem_toList_iff_mem, h]) b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Roo.forIn'_eq_forIn'_toList]
  exact Spec.forIn'_list inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn_roo {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {xs : Roo α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [forIn]
  exact Spec.forIn'_roo inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn'_roi {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {xs : Roi α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [← Roi.mem_toList_iff_mem, h]) b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Roi.forIn'_eq_forIn'_toList]
  exact Spec.forIn'_list inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn_roi {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {xs : Roi α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [forIn]
  exact Spec.forIn'_roi inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn'_ric {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLE α]
    {xs : Ric α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [← Ric.mem_toList_iff_mem, h]) b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Ric.forIn'_eq_forIn'_toList]
  exact Spec.forIn'_list inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn_ric {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLE α]
    {xs : Ric α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [forIn]
  exact Spec.forIn'_ric inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn'_rio {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLT α]
    {xs : Rio α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [← Rio.mem_toList_iff_mem, h]) b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Rio.forIn'_eq_forIn'_toList]
  exact Spec.forIn'_list inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn_rio {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLT α]
    {xs : Rio α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [forIn]
  exact Spec.forIn'_rio inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn'_rii {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [Least? α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    {xs : Rii α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [Rii.mem]) b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [Rii.forIn'_eq_forIn'_toList]
  exact Spec.forIn'_list inv eInv step

open Std Std.PRange in
@[lspec]
theorem Spec.forIn_rii {α β : Type u} {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [Least? α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    {xs : Rii α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | ForInStep.yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | ForInStep.done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  simp only [forIn]
  exact Spec.forIn'_rii inv eInv step

open Std Std.Iterators in
@[lspec]
theorem Spec.forIn_slice {δ : Type u} {m : Type u → Type w} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    {γ : Type u'} {α β : Type u}
    [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m]
    [Finite α Id]
    {init : δ} {f : β → δ → m (ForInStep δ)}
    {xs : Slice γ}
    (inv : Invariant xs.toList δ Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | .yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple (inv (⟨[], xs.toList, rfl⟩, init)) (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b)) eInv := by
  simp only [← Slice.forIn_toList]
  exact Spec.forIn_list inv eInv step

section Iterators
open Std Std.Iterators

@[lspec]
theorem Spec.forIn_iter {α β γ : Type u} {m : Type u → Type w} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {init : γ} {f : β → γ → m (ForInStep γ)}
    {it : Iter (α := α) β}
    (inv : Invariant it.toList γ Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : it.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | .yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv (⟨it.toList, [], by simp⟩, b'))
        eInv) :
    Triple (inv (⟨[], it.toList, rfl⟩, init)) (forIn it init f)
      (fun b => inv (⟨it.toList, [], by simp⟩, b)) eInv := by
  simp only [← Iter.forIn_toList]
  exact Spec.forIn_list inv eInv step

@[lspec]
theorem Spec.forIn_iterM_id {α β γ : Type u} {m : Type u → Type w} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {init : γ} {f : β → γ → m (ForInStep γ)}
    {it : IterM (α := α) Id β}
    (inv : Invariant it.toList.run γ Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : it.toList.run = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | .yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv (⟨it.toList.run, [], by simp⟩, b'))
        eInv) :
    Triple (inv (⟨[], it.toList.run, rfl⟩, init)) (forIn it init f)
      (fun b => inv (⟨it.toList.run, [], by simp⟩, b)) eInv := by
  conv in forIn it init f =>
    rw [← Iter.toIterM_toIter (it := it), ← Iter.forIn_eq_forIn_toIterM, ← Iter.forIn_toList,
      IterM.toList_toIter]
  exact Spec.forIn_list inv eInv step

@[lspec]
theorem Spec.foldM_iter {α β γ : Type u} {m : Type u → Type w} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β}
    {init : γ} {f : γ → β → m γ}
    (inv : Invariant it.toList γ Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : it.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f b cur)
        (fun b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b'))
        eInv) :
    Triple (inv (⟨[], it.toList, rfl⟩, init)) (it.foldM f init)
      (fun b => inv (⟨it.toList, [], by simp⟩, b)) eInv := by
  rw [← Iter.foldlM_toList]
  exact Spec.foldlM_list inv eInv step

@[lspec]
theorem Spec.foldM_iterM_id {α β γ : Type u} {m : Type u → Type w} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred] [LawfulMonad m]
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : IterM (α := α) Id β}
    {init : γ} {f : γ → β → m γ}
    (inv : Invariant it.toList.run γ Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : it.toList.run = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f b cur)
        (fun b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b'))
        eInv) :
    Triple (inv (⟨[], it.toList.run, rfl⟩, init)) (it.foldM f init)
      (fun b => inv (⟨it.toList.run, [], by simp⟩, b)) eInv := by
  rw [← IterM.foldlM_toList]
  exact Spec.foldlM_list inv eInv step

@[lspec]
theorem Spec.IterM.forIn_filterMapWithPostcondition {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n (Option β₂)} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple P (forIn (m := o) it init (fun out acc => do
          match ← (f out).run with
          | some c => g c acc
          | none => return .yield acc)) Q eQ) :
    Triple P (forIn (it.filterMapWithPostcondition f) init g) Q eQ := by
  rwa [Std.IterM.forIn_filterMapWithPostcondition]

@[lspec]
theorem Spec.IterM.forIn_filterMapM {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n (Option β₂)} {init : γ} {g : β₂ → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple P (forIn (m := o) it init (fun out acc => do
          match ← f out with
          | some c => g c acc
          | none => return .yield acc)) Q eQ) :
    Triple P (forIn (it.filterMapM f) init g) Q eQ := by
  rwa [Std.IterM.forIn_filterMapM]

@[lspec]
theorem Spec.IterM.forIn_filterMap {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → Option β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn it init (fun out acc => do
          match f out with
          | some c => g c acc
          | none => return .yield acc)) Q eQ) :
    Triple P (forIn (it.filterMap f) init g) Q eQ := by
  rwa [Std.IterM.forIn_filterMap]

@[lspec]
theorem Spec.IterM.forIn_mapWithPostcondition {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n β₂} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple P (forIn (m := o) it init (fun out acc => do g (← (f out).run) acc)) Q eQ) :
    Triple P (forIn (it.mapWithPostcondition f) init g) Q eQ := by
  rwa [Std.IterM.forIn_mapWithPostcondition]

@[lspec]
theorem Spec.IterM.forIn_mapM {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n β₂} {init : γ} {g : β₂ → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple P (forIn (m := o) it init (fun out acc => do g (← f out) acc)) Q eQ) :
    Triple P (forIn (it.mapM f) init g) Q eQ := by
  rwa [Std.IterM.forIn_mapM]

@[lspec]
theorem Spec.IterM.forIn_map {α β β₂ γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn it init (fun out acc => do g (f out) acc)) Q eQ) :
    Triple P (forIn (it.map f) init g) Q eQ := by
  rwa [Std.IterM.forIn_map]

@[lspec]
theorem Spec.IterM.forIn_filterWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n (ULift Bool)} {init : γ}
    {g : β → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple P (forIn (m := o) it init (fun out acc => do if (← (f out).run).down then g out acc else return .yield acc)) Q eQ) :
    Triple P (forIn (it.filterWithPostcondition f) init g) Q eQ := by
  rwa [Std.IterM.forIn_filterWithPostcondition]

@[lspec]
theorem Spec.IterM.forIn_filterM {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {init : γ} {g : β → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple P (forIn (m := o) it init (fun out acc => do if (← f out).down then g out acc else return .yield acc)) Q eQ) :
    Triple P (forIn (it.filterM f) init g) Q eQ := by
  rwa [Std.IterM.forIn_filterM]

@[lspec]
theorem Spec.IterM.forIn_filter {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → Bool} {init : γ} {g : β → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn (m := n) it init (fun out acc => do if f out then g out acc else return .yield acc)) Q eQ) :
    Triple P (forIn (it.filter f) init g) Q eQ := by
  rwa [Std.IterM.forIn_filter]

@[lspec]
theorem Spec.IterM.foldM_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple P (it.foldM (n := o) (init := init) (fun d b => do
          let some c ← (f b).run | Pure.pure d
          g d c)) Q eQ) :
    Triple P ((it.filterMapWithPostcondition f).foldM (init := init) g) Q eQ := by
  rwa [Std.IterM.foldM_filterMapWithPostcondition]

@[lspec]
theorem Spec.IterM.foldM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple P (it.foldM (n := o) (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          g d c)) Q eQ) :
    Triple P ((it.filterMapM f).foldM (init := init) g) Q eQ := by
  rwa [Std.IterM.foldM_filterMapM]

@[lspec]
theorem Spec.IterM.foldM_mapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n γ} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple P (it.foldM (n := o) (init := init) (fun d b => do let c ← (f b).run; g d c)) Q eQ) :
    Triple P ((it.mapWithPostcondition f).foldM (init := init) g) Q eQ := by
  rwa [Std.IterM.foldM_mapWithPostcondition]

@[lspec]
theorem Spec.IterM.foldM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n γ} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple P (it.foldM (n := o) (init := init) (fun d b => do let c ← f b; g d c)) Q eQ) :
    Triple P ((it.mapM f).foldM (init := init) g) Q eQ := by
  rwa [Std.IterM.foldM_mapM]

@[lspec]
theorem Spec.IterM.foldM_filterWithPostcondition {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple P (it.foldM (n := o) (init := init) (fun d b => do if (← (f b).run).down then g d b else Pure.pure d)) Q eQ) :
    Triple P ((it.filterWithPostcondition f).foldM (init := init) g) Q eQ := by
  rwa [Std.IterM.foldM_filterWithPostcondition]

@[lspec]
theorem Spec.IterM.foldM_filterM {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple P (it.foldM (n := o) (init := init) (fun d b => do if (← f b).down then g d b else Pure.pure d)) Q eQ) :
    Triple P ((it.filterM f).foldM (init := init) g) Q eQ := by
  rwa [Std.IterM.foldM_filterM]

@[lspec]
theorem Spec.IterM.foldM_filterMap {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α m n]
    [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → Option γ} {g : δ → γ → n δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (n := n) (init := init) (fun d b => do
          let some c := f b | Pure.pure d
          g d c)) Q eQ) :
    Triple P ((it.filterMap f).foldM (init := init) g) Q eQ := by
  rwa [Std.IterM.foldM_filterMap]

@[lspec]
theorem Spec.IterM.foldM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → γ} {g : δ → γ → n δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => do g d (f b))) Q eQ) :
    Triple P ((it.map f).foldM (init := init) g) Q eQ := by
  rwa [Std.IterM.foldM_map]

@[lspec]
theorem Spec.IterM.foldM_filter {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α m n]
    [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → Bool} {g : δ → β → n δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => if f b then g d b else Pure.pure d)) Q eQ) :
    Triple P ((it.filter f).foldM (init := init) g) Q eQ := by
  rwa [Std.IterM.foldM_filter]

@[lspec]
theorem Spec.IterM.fold_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (n := n) (init := init) (fun d b => do
          let some c ← (f b).run | Pure.pure d
          return g d c)) Q eQ) :
    Triple P ((it.filterMapWithPostcondition f).fold (init := init) g) Q eQ := by
  rwa [Std.IterM.fold_filterMapWithPostcondition]

@[lspec]
theorem Spec.IterM.fold_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (Option γ)} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          return g d c)) Q eQ) :
    Triple P ((it.filterMapM f).fold (init := init) g) Q eQ := by
  rwa [Std.IterM.fold_filterMapM]

@[lspec]
theorem Spec.IterM.fold_mapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => do let c ← (f b).run; return g d c)) Q eQ) :
    Triple P ((it.mapWithPostcondition f).fold (init := init) g) Q eQ := by
  rwa [Std.IterM.fold_mapWithPostcondition]

@[lspec]
theorem Spec.IterM.fold_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => do let c ← f b; return g d c)) Q eQ) :
    Triple P ((it.mapM f).fold (init := init) g) Q eQ := by
  rwa [Std.IterM.fold_mapM]

@[lspec]
theorem Spec.IterM.fold_filterWithPostcondition {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => return if (← (f b).run).down then g d b else d)) Q eQ) :
    Triple P ((it.filterWithPostcondition f).fold (init := init) g) Q eQ := by
  rwa [Std.IterM.fold_filterWithPostcondition]

@[lspec]
theorem Spec.IterM.fold_filterM {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => return if (← f b).down then g d b else d)) Q eQ) :
    Triple P ((it.filterM f).fold (init := init) g) Q eQ := by
  rwa [Std.IterM.fold_filterM]

@[lspec]
theorem Spec.IterM.fold_filterMap {α β γ δ : Type w}
    {m : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → Option γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.fold (init := init) (fun d b =>
          match f b with
          | some c => g d c
          | _ => d)) Q eQ) :
    Triple P ((it.filterMap f).fold (init := init) g) Q eQ := by
  rwa [Std.IterM.fold_filterMap]

@[lspec]
theorem Spec.IterM.fold_map {α β γ δ : Type w}
    {m : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.fold (init := init) (fun d b => g d (f b))) Q eQ) :
    Triple P ((it.map f).fold (init := init) g) Q eQ := by
  rwa [Std.IterM.fold_map]

@[lspec]
theorem Spec.IterM.fold_filter {α β δ : Type w}
    {m : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → Bool} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.fold (init := init) (fun d b => if f b then g d b else d)) Q eQ) :
    Triple P ((it.filter f).fold (init := init) g) Q eQ := by
  rwa [Std.IterM.fold_filter]

@[lspec]
theorem Spec.Iter.forIn_filterMapWithPostcondition {α β β₂ γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n (Option β₂)} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn (m := o) it init (fun out acc => do
        match ← (f out).run with
        | some c => g c acc
        | none => return .yield acc)) Q eQ) :
    Triple P (forIn (it.filterMapWithPostcondition f) init g) Q eQ := by
  rwa [Std.Iter.forIn_filterMapWithPostcondition]

@[lspec]
theorem Spec.Iter.forIn_filterMapM {α β β₂ γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id] [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n (Option β₂)} {init : γ} {g : β₂ → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn (m := o) it init (fun out acc => do
        match ← f out with
        | some c => g c acc
        | none => return .yield acc)) Q eQ) :
    Triple P (forIn (it.filterMapM f) init g) Q eQ := by
  rwa [Std.Iter.forIn_filterMapM]

@[lspec]
theorem Spec.Iter.forIn_filterMap {α β β₂ γ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred] [Finite α Id]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → Option β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn it init (fun out acc => do
        match f out with
        | some c => g c acc
        | none => return .yield acc)) Q eQ) :
    Triple P (forIn (it.filterMap f) init g) Q eQ := by
  rwa [Std.Iter.forIn_filterMap]

@[lspec]
theorem Spec.Iter.forIn_mapWithPostcondition {α β β₂ γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n β₂} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn (m := o) it init (fun out acc => do g (← (f out).run) acc)) Q eQ) :
    Triple P (forIn (it.mapWithPostcondition f) init g) Q eQ := by
  rwa [Std.Iter.forIn_mapWithPostcondition]

@[lspec]
theorem Spec.Iter.forIn_mapM {α β β₂ γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n β₂} {init : γ} {g : β₂ → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn (m := o) it init (fun out acc => do g (← f out) acc)) Q eQ) :
    Triple P (forIn (it.mapM f) init g) Q eQ := by
  rwa [Std.Iter.forIn_mapM]

@[lspec]
theorem Spec.Iter.forIn_map {α β β₂ γ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn it init (fun out acc => do g (f out) acc)) Q eQ) :
    Triple P (forIn (it.map f) init g) Q eQ := by
  rwa [Std.Iter.forIn_map]

@[lspec]
theorem Spec.Iter.forIn_filterWithPostcondition {α β γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id] [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n (ULift Bool)} {init : γ}
    {g : β → γ → o (ForInStep γ)} {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn (m := o) it init (fun out acc => do if (← (f out).run).down then g out acc else return .yield acc)) Q eQ) :
    Triple P (forIn (it.filterWithPostcondition f) init g) Q eQ := by
  rwa [Std.Iter.forIn_filterWithPostcondition]

@[lspec]
theorem Spec.Iter.forIn_filterM {α β γ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n (ULift Bool)} {init : γ} {g : β → γ → o (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn (m := o) it init (fun out acc => do if (← f out).down then g out acc else return .yield acc)) Q eQ) :
    Triple P (forIn (it.filterM f) init g) Q eQ := by
  rwa [Std.Iter.forIn_filterM]

@[lspec]
theorem Spec.Iter.forIn_filter {α β γ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β]
    [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → Bool} {init : γ} {g : β → γ → n (ForInStep γ)}
    {P : Pred} {Q : γ → Pred} {eQ : EPred}
    (h : Triple P (forIn it init (fun out acc => do if f out then g out acc else return .yield acc)) Q eQ) :
    Triple P (forIn (it.filter f) init g) Q eQ := by
  rwa [Std.Iter.forIn_filter]

@[lspec]
theorem Spec.Iter.foldM_filterMapWithPostcondition {α β γ δ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Monad o] [LawfulMonad n] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (m := o) (init := init) (fun d b => do
          let some c ← (f b).run | Pure.pure d
          g d c)) Q eQ) :
    Triple P ((it.filterMapWithPostcondition f).foldM (init := init) g) Q eQ := by
  rwa [Std.Iter.foldM_filterMapWithPostcondition]

@[lspec]
theorem Spec.Iter.foldM_filterMapM {α β γ δ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (m := o) (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          g d c)) Q eQ) :
    Triple P ((it.filterMapM f).foldM (init := init) g) Q eQ := by
  rwa [Std.Iter.foldM_filterMapM]

@[lspec]
theorem Spec.Iter.foldM_mapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'''} {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n γ} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (m := o) (init := init) (fun d b => do let c ← (f b).run; g d c)) Q eQ) :
    Triple P ((it.mapWithPostcondition f).foldM (init := init) g) Q eQ := by
  rwa [Std.Iter.foldM_mapWithPostcondition (m := m)]

@[lspec]
theorem Spec.Iter.foldM_mapM {α β γ δ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n γ} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (m := o) (init := init) (fun d b => do let c ← f b; g d c)) Q eQ) :
    Triple P ((it.mapM f).foldM (init := init) g) Q eQ := by
  rwa [Std.Iter.foldM_mapM]

@[lspec]
theorem Spec.Iter.foldM_filterWithPostcondition {α β δ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Monad o] [LawfulMonad n] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (m := o) (init := init) (fun d b => do if (← (f b).run).down then g d b else Pure.pure d)) Q eQ) :
    Triple P ((it.filterWithPostcondition f).foldM (init := init) g) Q eQ := by
  rwa [Std.Iter.foldM_filterWithPostcondition]

@[lspec]
theorem Spec.Iter.foldM_filterM {α β δ : Type w}
    {n : Type w → Type w'} {o : Type w → Type w''}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [Assertion Pred] [Assertion EPred] [WP o Pred EPred]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (m := o) (init := init) (fun d b => do if (← f b).down then g d b else Pure.pure d)) Q eQ) :
    Triple P ((it.filterM f).foldM (init := init) g) Q eQ := by
  rwa [Std.Iter.foldM_filterM]

@[lspec]
theorem Spec.Iter.foldM_filterMap {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id] [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α Id n]
    [LawfulIteratorLoop α Id n]
    {f : β → Option γ} {g : δ → γ → n δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => do
          let some c := f b | Pure.pure d
          g d c)) Q eQ) :
    Triple P ((it.filterMap f).foldM (init := init) g) Q eQ := by
  rwa [Std.Iter.foldM_filterMap]

@[lspec]
theorem Spec.Iter.foldM_map {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id] [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → γ} {g : δ → γ → n δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => do g d (f b))) Q eQ) :
    Triple P ((it.map f).foldM (init := init) g) Q eQ := by
  rwa [Std.Iter.foldM_map]

@[lspec]
theorem Spec.Iter.foldM_filter {α β δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id] [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → Bool} {g : δ → β → n δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => if f b then g d b else Pure.pure d)) Q eQ) :
    Triple P ((it.filter f).foldM (init := init) g) Q eQ := by
  rwa [Std.Iter.foldM_filter]

@[lspec]
theorem Spec.Iter.fold_filterMapWithPostcondition {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => do
          let some c ← (f b).run | Pure.pure d
          return g d c)) Q eQ) :
    Triple P ((it.filterMapWithPostcondition f).fold (init := init) g) Q eQ := by
  rwa [Std.Iter.fold_filterMapWithPostcondition]

@[lspec]
theorem Spec.Iter.fold_filterMapM {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n (Option γ)} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          return g d c)) Q eQ) :
    Triple P ((it.filterMapM f).fold (init := init) g) Q eQ := by
  rwa [Std.Iter.fold_filterMapM]

@[lspec]
theorem Spec.Iter.fold_mapWithPostcondition {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => do let c ← (f b).run; return g d c)) Q eQ) :
    Triple P ((it.mapWithPostcondition f).fold (init := init) g) Q eQ := by
  rwa [Std.Iter.fold_mapWithPostcondition]

@[lspec]
theorem Spec.Iter.fold_mapM {α β γ δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => do let c ← f b; return g d c)) Q eQ) :
    Triple P ((it.mapM f).fold (init := init) g) Q eQ := by
  rwa [Std.Iter.fold_mapM]

@[lspec]
theorem Spec.Iter.fold_filterWithPostcondition {α β δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [LawfulMonad n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => return if (← (f b).run).down then g d b else d)) Q eQ) :
    Triple P ((it.filterWithPostcondition f).fold (init := init) g) Q eQ := by
  rwa [Std.Iter.fold_filterWithPostcondition]

@[lspec]
theorem Spec.Iter.fold_filterM {α β δ : Type w}
    {n : Type w → Type w'}
    {Pred : Type w} {EPred : Type w}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [Assertion Pred] [Assertion EPred] [WP n Pred EPred]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : Iter (α := α) β}
    {P : Pred} {Q : δ → Pred} {eQ : EPred}
    (h : Triple P (it.foldM (init := init) (fun d b => return if (← f b).down then g d b else d)) Q eQ) :
    Triple P ((it.filterM f).fold (init := init) g) Q eQ := by
  rwa [Std.Iter.fold_filterM]

end Iterators


@[lspec]
theorem Spec.forIn'_array {xs : Array α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur (by simp [←Array.mem_toList_iff, h]) b)
        (fun r => match r with
          | .yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn' xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  cases xs; simp; apply Spec.forIn'_list inv eInv step

@[lspec]
theorem Spec.forIn_array {xs : Array α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f cur b)
        (fun r => match r with
          | .yield b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv (⟨xs.toList, [], by simp⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (forIn xs init f)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  cases xs; simp; apply Spec.forIn_list inv eInv step

@[lspec]
theorem Spec.foldlM_array [LawfulMonad m]
    {xs : Array α} {init : β} {f : β → α → m β}
    (inv : Invariant xs.toList β Pred)
    (eInv : EPred)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (inv (⟨pref, cur::suff, h.symm⟩, b))
        (f b cur)
        (fun b' => inv (⟨pref ++ [cur], suff, by simp [h]⟩, b'))
        eInv) :
    Triple
      (inv (⟨[], xs.toList, rfl⟩, init))
      (Array.foldlM f init xs)
      (fun b => inv (⟨xs.toList, [], by simp⟩, b))
      eInv := by
  cases xs; simp; apply Spec.foldlM_list inv eInv step

end Std.Do'
