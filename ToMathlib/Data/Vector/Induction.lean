/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Data.Vector.Defs

/-!
# Eliminators for core `Vector`

`cases`/`induction` (and their two-vector forms) for `Vector α n`, which core does not
supply, plus heterogeneous equality through `toArray`.
-/

public section

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

end Vector
