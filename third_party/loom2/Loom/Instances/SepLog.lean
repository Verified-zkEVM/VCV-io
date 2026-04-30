import Std.Data.HashMap
import Loom.Triple.Basic

open Lean.Order Loom

abbrev Loc := Nat
abbrev Val := Int

instance : EquivBEq Loc := inferInstance
instance : LawfulHashable Loc := inferInstance

def Heap := Std.HashMap Loc Val

inductive HeapException : Type where
  | notFound (x : Loc)

abbrev HeapM := StateT Heap (Except HeapException)

instance : EmptyCollection Heap := ⟨.emptyWithCapacity⟩

abbrev hProp := Heap → Prop
abbrev eProp := HeapException → Prop

def Heap.Disjoint (h₁ h₂ : Heap) : Prop :=
  ∀ x y, h₁.contains x → h₂.contains y → x ≠ y

def Heap.single (x : Loc) (v : Val) : Heap := (∅ : Heap).insert x v

-- TODO: Std.HashMap.ext is private; these need it or a representation change
theorem Heap.empty_union (h : Heap) : (∅ : Heap).union h = h := by
  sorry

theorem Heap.union_empty (h : Heap) : h.union (∅ : Heap) = h := by
  sorry

theorem Heap.Disjoint.empty_left (h : Heap) : Heap.Disjoint ∅ h := by
  intro x _ hx _
  exact absurd hx Std.HashMap.not_mem_empty

theorem Heap.Disjoint.empty_right (h : Heap) : Heap.Disjoint h ∅ := by
  intro _ y _ hy
  exact absurd hy Std.HashMap.not_mem_empty

-- TODO: needs Std.HashMap.ext / union API
theorem Heap.union_assoc (a b c : Heap) : (a.union b).union c = a.union (b.union c) := by sorry

@[simp] theorem Heap.contains_union (h₁ h₂ : Heap) (x : Loc) :
    (h₁.union h₂).contains x = (h₁.contains x || h₂.contains x) := by
  exact Std.HashMap.contains_union

theorem Heap.Disjoint.assoc_left {h₁ h₂ h₃ : Heap}
    (h₁₂ : Heap.Disjoint h₁ h₂) (h₁₂_₃ : Heap.Disjoint (h₁.union h₂) h₃) :
    Heap.Disjoint h₁ (h₂.union h₃) ∧ Heap.Disjoint h₂ h₃ := by
  constructor
  · intro x y hx hy
    rw [Heap.contains_union] at hy; simp only [Bool.or_eq_true] at hy
    cases hy with
    | inl h₂y => exact h₁₂ x y hx h₂y
    | inr h₃y =>
      exact h₁₂_₃ x y (by rw [Heap.contains_union]; simp [hx]) h₃y
  · intro x y hx hy
    exact h₁₂_₃ x y (by rw [Heap.contains_union]; simp [hx]) hy

theorem Heap.Disjoint.assoc_right {h₁ h₂ h₃ : Heap}
    (h₁_₂₃ : Heap.Disjoint h₁ (h₂.union h₃)) (h₂₃ : Heap.Disjoint h₂ h₃) :
    Heap.Disjoint h₁ h₂ ∧ Heap.Disjoint (h₁.union h₂) h₃ := by
  constructor
  · intro x y hx hy
    exact h₁_₂₃ x y hx (by rw [Heap.contains_union]; simp [hy])
  · intro x y hx hy
    rw [Heap.contains_union] at hx; simp only [Bool.or_eq_true] at hx
    cases hx with
    | inl h₁x =>
      exact h₁_₂₃ x y h₁x (by rw [Heap.contains_union]; simp [hy])
    | inr h₂x => exact h₂₃ x y h₂x hy

inductive hStar' (H₁ : hProp) (H₂ : hProp) (h : Heap) : Prop where
  | intro (h₁ h₂ : Heap) (Hh₁ : H₁ h₁) (Hh₂ : H₂ h₂)
    (h_union : h₁.union h₂ = h)
    (h_disjoint : h₁.Disjoint h₂) :
    hStar' H₁ H₂ h

def hStar (H₁ : hProp) (H₂ : hProp) : hProp := hStar' H₁ H₂

infix:65 " ∗ " => hStar

inductive hExists' (P : α → hProp) (h : Heap) : Prop where
  | intro (a : α) (Ha : P a h) : hExists' P h

def hExists (P : α → hProp) : hProp := hExists' P

notation:50 "∃ʰ " x ", " P => hExists (fun x => P)

def hForall' (P : α → hProp) (h : Heap) : Prop := ∀ a, P a h

def hForall (P : α → hProp) : hProp := hForall' P

notation:50 "∀ʰ " x ", " P => hForall (fun x => P)

inductive hPure' (P : Prop) : Heap -> Prop where
  | intro (HP : P) : hPure' P ∅

def hPure (P : Prop) : hProp := hPure' P

notation:68 "⌜" P "⌝ʰ" => hPure P

def hWand (H₁ : hProp) (H₂ : hProp) : hProp := ∃ʰ H, H ∗ hPure (H₁ ∗ H ⊑ H₂)

infix:60 " -∗ " => hWand

inductive hSingle' (x : Loc) (v : Val) : Heap → Prop where
  | intro : hSingle' x v ((∅ : Heap).insert x v)

def hSingle (x : Loc) (v : Val) : hProp := hSingle' x v

notation:70 x " ↦ " v => hSingle x v

def hEmpty : hProp := (· = ∅)

instance : EmptyCollection hProp := ⟨hEmpty⟩

/-! ## Abstract lemmas about hProp connectives -/

theorem hForall_elim {P : α → hProp} (a : α) :
  P a ⊑ Q →
  hForall P ⊑ Q :=
  fun himp _ hall =>
    himp _ (hall a)

theorem hForall_star_elim {P : α → hProp} (a : α) :
  H ∗ P a ⊑ Q →
  H ∗ hForall P ⊑ Q := by
  intro hle h ⟨h₁, h₂, hH, hP, hunion, hdisj⟩
  exact hle h (hStar'.intro h₁ h₂ hH (hP a) hunion hdisj)

theorem hForall_intro {P : α → hProp} {Q : hProp}
    (h : ∀ a, Q ⊑ P a) : Q ⊑ hForall P :=
  fun heap hQ a => h a heap hQ

theorem hStar_hPure_true_left {Q : hProp} : hPure True ∗ Q ⊑ Q := by
  intro h ⟨_, h₂, hpure, hQ, hunion, _⟩
  cases hpure with
  | intro _ =>
    rw [Heap.empty_union] at hunion
    exact hunion ▸ hQ

theorem hWand_hPure_true_elim {Q : hProp} : hWand (hPure True) Q ⊑ Q := by
  intro h ⟨H', ⟨h₁, _, hH', hpure, hunion, _⟩⟩
  cases hpure with
  | intro hent =>
    rw [Heap.union_empty] at hunion
    subst hunion
    exact hent h₁ (hStar'.intro ∅ h₁ (hPure'.intro trivial) hH'
      (Heap.empty_union h₁) (Heap.Disjoint.empty_left h₁))

theorem entails_hWand {H₁ H₂ Q : hProp} (hle : H₁ ∗ H₂ ⊑ Q) :
    H₂ ⊑ hWand H₁ Q := by
  intro h hH₂
  exact hExists'.intro H₂ (hStar'.intro h ∅ hH₂ (hPure'.intro hle)
    (Heap.union_empty h) (Heap.Disjoint.empty_right h))

theorem hWand_mono :
  P ⊑ Q →
  H -∗ P ⊑ H -∗ Q := by
  intro hle h ⟨H', ⟨h₁, h₂, hH', hpure, hunion, hdisj⟩⟩
  cases hpure with
  | intro hent =>
    exact hExists'.intro H' (hStar'.intro h₁ ∅ hH' (hPure'.intro (PartialOrder.rel_trans hent hle))
      hunion hdisj)

theorem hStar_mono :
  P ⊑ Q →
  H ∗ P ⊑ H ∗ Q := by
  intro hle h ⟨h₁, h₂, hH, hP, hunion, hdisj⟩
  exact hStar'.intro h₁ h₂ hH (hle h₂ hP) hunion hdisj

theorem hWand_elim {H Q : hProp} : H ∗ (H -∗ Q) ⊑ Q := by
  intro h ⟨h₁, h₂, hH, ⟨H', ⟨h₃, h₄, hH', hpure, hunion₂, hdisj₂⟩⟩, hunion, hdisj⟩
  cases hpure with
  | intro hent =>
    rw [Heap.union_empty] at hunion₂
    subst hunion₂
    exact hent h (hStar'.intro h₁ h₃ hH hH' hunion hdisj)

theorem hStar_assoc_l {A B C : hProp} : (A ∗ B) ∗ C ⊑ A ∗ (B ∗ C) := by
  intro h ⟨h₁₂, h₃, ⟨h₁, h₂, hA, hB, hunion₁₂, hdisj₁₂⟩, hC, hunion, hdisj⟩
  have ⟨hdisj₁, hdisj₂⟩ := Heap.Disjoint.assoc_left hdisj₁₂ (hunion₁₂ ▸ hdisj)
  exact hStar'.intro h₁ (h₂.union h₃) hA (hStar'.intro h₂ h₃ hB hC rfl hdisj₂)
    (by rw [← Heap.union_assoc, hunion₁₂, hunion]) hdisj₁

theorem hStar_assoc_r {A B C : hProp} : A ∗ (B ∗ C) ⊑ (A ∗ B) ∗ C := by
  intro h ⟨h₁, h₂₃, hA, ⟨h₂, h₃, hB, hC, hunion₂₃, hdisj₂₃⟩, hunion, hdisj⟩
  have ⟨hdisj₁, hdisj₂⟩ := Heap.Disjoint.assoc_right (hunion₂₃ ▸ hdisj) hdisj₂₃
  exact hStar'.intro (h₁.union h₂) h₃ (hStar'.intro h₁ h₂ hA hB rfl hdisj₁) hC
    (by rw [Heap.union_assoc, hunion₂₃, hunion]) hdisj₂

/-! ## WP instance -/


/-! ## HashMap helper lemmas -/

@[simp] theorem Heap.get?_union (h₁ h₂ : Heap) (x : Loc) :
    (h₁.union h₂).get? x = (h₂.get? x).or (h₁.get? x) := by
  exact Std.HashMap.getElem?_union

@[simp] theorem Heap.get?_insert_self (h : Heap) (x : Loc) (v : Val) :
    (h.insert x v).get? x = some v := by
  unfold Std.HashMap.get? Std.HashMap.insert; simp

@[simp] theorem Heap.get?_empty (x : Loc) :
    (∅ : Heap).get? x = none := by
  change Std.DHashMap.Const.get? _ _ = none
  exact Std.DHashMap.Const.get?_empty

@[simp] theorem Heap.contains_insert (h : Heap) (x y : Loc) (v : Val) :
    (h.insert x v).contains y = (x == y || h.contains y) := by
  exact Std.HashMap.contains_insert

@[simp] theorem Heap.contains_empty (x : Loc) :
    (∅ : Heap).contains x = false := by
  exact Std.HashMap.contains_empty

-- Needed for assign: updating a value in a union
theorem Heap.union_insert_eq (h : Heap) (x : Loc) (u v : Val)
    (hdisj : ¬ h.contains x) :
    (h.union ((∅ : Heap).insert x u)).insert x v = h.union ((∅ : Heap).insert x v) := by
  sorry -- needs HashMap.ext

-- Needed for alloc: inserting a fresh key = union with singleton
theorem Heap.insert_eq_union_single (h : Heap) (x : Loc) (v : Val)
    (hnot : ¬ h.contains x) :
    h.insert x v = h.union ((∅ : Heap).insert x v) := by
  sorry -- needs HashMap.ext

theorem Heap.Disjoint.not_contains_left {h₁ h₂ : Heap} {x : Loc}
    (hdisj : Heap.Disjoint h₁ h₂) (hx : h₂.contains x) : ¬ h₁.contains x := by
  intro h₁x; exact absurd rfl (hdisj x x h₁x hx)

theorem Heap.Disjoint.insert_val {h : Heap} {x : Loc} {u v : Val}
    (hdisj : Heap.Disjoint h ((∅ : Heap).insert x u)) :
    Heap.Disjoint h ((∅ : Heap).insert x v) := by
  intro a b ha hb
  have hbu : ((∅ : Heap).insert x u).contains b := by
    simp [Heap.contains_empty] at hb ⊢; exact hb
  exact hdisj a b ha hbu

theorem Heap.Disjoint.single_of_not_contains {h : Heap} {x : Loc} {v : Val}
    (hnot : ¬ h.contains x) : Heap.Disjoint h ((∅ : Heap).insert x v) := by
  intro a b ha hb
  simp [Heap.contains_empty] at hb
  subst hb; intro heq; subst heq; exact hnot ha

/-! ## Heap operations -/

def HeapM.assign (x : Loc) (v : Val) : HeapM Unit := do
  if (← get).contains x then do
    modify (·.insert x v)
  else throw (.notFound x)

def HeapM.read (x : Loc) : HeapM Val := do
  match (← get).get? x with
  | some v => pure v
  | none => throw (.notFound x)

def Heap.maxKey (h : Heap) : Loc :=
  h.keys.foldl max 0

theorem Heap.maxKey_not_mem (h : Heap) (x : Loc) :
  x > h.maxKey →
  ¬ h.contains x := by
  sorry

def HeapM.alloc (v : Val) : HeapM Loc := do
  let newKey := (← get).maxKey + 1
  modify fun h : Heap => h.insert newKey v
  return newKey

/-! ## Layer 1: HeapM computation lemmas -/

@[simp] private theorem HeapM.bind_apply (x : HeapM α) (f : α → HeapM β) (s : Heap) :
    (x >>= f) s = x s >>= fun (a, s') => f a s' := rfl

@[simp] private theorem HeapM.get_apply (s : Heap) :
    (get : HeapM Heap) s = .ok (s, s) := rfl

@[simp] private theorem HeapM.pure_apply (a : α) (s : Heap) :
    (pure a : HeapM α) s = .ok (a, s) := rfl

@[simp] private theorem HeapM.throw_apply (e : HeapException) (s : Heap) :
    (throw e : HeapM α) s = .error e := rfl

@[simp] private theorem HeapM.modify_apply (f : Heap → Heap) (s : Heap) :
    (modify f : HeapM PUnit) s = .ok ((), f s) := rfl

@[simp] private theorem HeapM.map_apply (f : α → β) (x : HeapM α) (s : Heap) :
    (f <$> x) s = x s >>= fun (a, s') => .ok (f a, s') := rfl

private theorem HeapM.wp_ok {x : HeapM α} {s s' : Heap} {a : α}
    (h : x s = .ok (a, s')) :
    @wp HeapM _ _ _ _ StateT.instWP α x post epost s = post a s' := by
  simp only [wp]; rw [h]

/-! ## Layer 2: Inner specs with frame -/

theorem HeapM.read_inner (x : Loc) (v : Val) (H : hProp) (epost : PUnit × eProp) :
    Triple
      (H ∗ (x ↦ v)) (read x) (fun r => H ∗ (⌜r = v⌝ʰ ∗ x ↦ v)) epost := by
  rw [Triple.iff]
  intro s ⟨h₁, h₂, hH, hSingle, hunion, hdisj⟩
  cases hSingle; subst hunion
  simp only [wp, HeapM.read, bind, Except.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Heap.get?_union, Heap.get?_insert_self, Option.or]
  exact hStar'.intro h₁ ((∅ : Heap).insert x v) hH
    (hStar'.intro ∅ ((∅ : Heap).insert x v) (hPure'.intro ⟨⟩) hSingle'.intro
      (Heap.empty_union _) (Heap.Disjoint.empty_left _))
    rfl hdisj

theorem HeapM.assign_inner (x : Loc) (v u : Val) (H : hProp) (epost : PUnit × eProp) :
    Triple
      (H ∗ (x ↦ u)) (HeapM.assign x v) (fun _ => H ∗ (x ↦ v)) epost := by
  rw [Triple.iff]
  intro s ⟨h₁, h₂, hH, hSingle, hunion, hdisj⟩
  cases hSingle; subst hunion
  have hcontains : (h₁.union ((∅ : Heap).insert x u)).contains x = true := by
    rw [Heap.contains_union]; simp
  simp only [wp, HeapM.assign, Except.bind,
    hcontains, ite_true, HeapM.modify_apply, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, Except.pure]
  rw [Heap.union_insert_eq h₁ x u v (hdisj.not_contains_left (by simp))]
  exact hStar'.intro h₁ ((∅ : Heap).insert x v) hH hSingle'.intro rfl (hdisj.insert_val)

theorem HeapM.alloc_inner (v : Val) (H : hProp) (epost : PUnit × eProp) :
    Triple
      (H ∗ ∅) (HeapM.alloc v) (fun loc => H ∗ (loc ↦ v)) epost := by
  rw [Triple.iff]
  intro s ⟨h₁, h₂, hH, hempty, hunion, hdisj⟩
  change h₂ = ∅ at hempty; subst hempty
  rw [Heap.union_empty] at hunion; subst hunion
  simp only [wp, HeapM.alloc, HeapM.modify_apply, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, Except.pure, Except.bind, StateT.pure]
  have hnot : ¬ h₁.contains (h₁.maxKey + 1) :=
    Heap.maxKey_not_mem h₁ _ (by simp)
  rw [Heap.insert_eq_union_single h₁ _ v hnot]
  exact hStar'.intro h₁ ((∅ : Heap).insert _ v) hH hSingle'.intro rfl
    (Heap.Disjoint.single_of_not_contains hnot)

/-! ## Layer 3: Outer separation logic specs -/

instance : WP HeapM hProp (PUnit × eProp) where
  wp x post epost := ∀ʰ H, H -∗ wp x (fun x => H ∗ post x) epost
  wp_pure x post epost := by
    simp [WP.wp_pure]
    apply PartialOrder.rel_antisymm
    { exact PartialOrder.rel_trans (by apply hForall_elim; rfl)
        (PartialOrder.rel_trans hWand_hPure_true_elim hStar_hPure_true_left) }
    { exact hForall_intro (fun H => entails_hWand PartialOrder.rel_refl) }
  wp_bind x f post epost := by
    simp
    apply hForall_intro; intro H
    apply hForall_elim H (Q := H -∗ _)
    apply hWand_mono
    apply PartialOrder.rel_trans; rotate_left; apply WP.wp_bind
    apply WP.wp_consequence; intro x; simp
    apply hForall_star_elim H (Q := wp _ _ _)
    exact hWand_elim
  wp_consequence x post post' epost h := by
    apply hForall_intro; intro H
    apply hForall_elim H (Q := H -∗ _)
    apply hWand_mono; apply WP.wp_consequence; intro x; simp
    apply hStar_mono; apply h

def HeapM.frame (H pre : hProp) (post : α → hProp) (epost : PUnit × eProp) (x : HeapM α) :
  Triple pre x post epost →
  Triple (H ∗ pre) x (fun x => H ∗ post x) epost := by
  simp [Triple.iff]; rw [wp]; simp [instWPHeapMHPropProdPUnitEProp]; intro hwp
  apply hForall_intro; intro K
  apply entails_hWand
  -- Goal: K ∗ (H ∗ pre) ⊑ wp x (fun a => K ∗ (H ∗ post a)) epost
  have hwp' := PartialOrder.rel_trans hwp (hForall_elim (K ∗ H) PartialOrder.rel_refl)
  have step1 := PartialOrder.rel_trans (hStar_mono hwp') hWand_elim
  have step2 := @WP.wp_consequence HeapM _ _ _ _ StateT.instWP _ x
    (fun a => (K ∗ H) ∗ post a) (fun a => K ∗ (H ∗ post a)) epost (fun a => hStar_assoc_l)
  intro heap hKHpre
  exact step2 heap (step1 heap (hStar_assoc_r heap hKHpre))


theorem HeapM.read_spec (x : Loc) (v : Val) :
  Triple (x ↦ v) (read x) (⌜· = v⌝ʰ ∗ x ↦ v) epost := by
  simp [Triple.iff]; apply hForall_intro; intro H
  apply entails_hWand
  simp [<-Triple.iff]
  apply read_inner


theorem HeapM.assign_spec (x : Loc) (v u : Val) :
  Triple (x ↦ u) (assign x v) (fun _ => x ↦ v) epost := by
  simp [Triple.iff]; apply hForall_intro; intro H
  apply entails_hWand
  simp [<-Triple.iff]
  apply assign_inner

theorem HeapM.alloc_spec (v : Val) :
  Triple ∅ (alloc v) (· ↦ v) epost := by
  simp [Triple.iff]; apply hForall_intro; intro H
  apply entails_hWand
  simp [<-Triple.iff]
  apply alloc_inner
