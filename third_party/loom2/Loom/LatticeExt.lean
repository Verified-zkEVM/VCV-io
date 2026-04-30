/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Init.Internal.Order
universe u v w
@[expose] public section

set_option linter.missingDocs true

namespace Lean.Order

/-!
# Additional Complete Lattice Operations

Extensions to `Lean.Order.CompleteLattice` providing additional operations
needed for program verification.
-/

section LatticeExtensions

attribute [refl] PartialOrder.rel_refl

variable {α : Type u} [CompleteLattice α]

/-- Top element of a complete lattice (supremum of all elements) -/
noncomputable def latticeTop : α := CompleteLattice.sup (fun _ => True)

@[inherit_doc latticeTop]
scoped notation "⊤" => latticeTop

theorem le_top (x : α) : x ⊑ ⊤ := by
  apply le_sup
  trivial

/-- Bottom element of a complete lattice (infimum of all elements) -/
noncomputable def latticeBot : α := inf (fun _ => True)

theorem latticeBot_le (x : α) : latticeBot ⊑ x := by
  apply inf_le
  trivial

/-- Binary meet (infimum) -/
noncomputable def meet (x y : α) : α := inf (fun z => z = x ∨ z = y)

@[inherit_doc meet]
scoped infixl:70 " ⊓ " => meet

theorem meet_le_left (x y : α) : x ⊓ y ⊑ x := by
  apply inf_le
  left; rfl

theorem meet_le_right (x y : α) : x ⊓ y ⊑ y := by
  apply inf_le
  right; rfl

theorem le_meet (x y z : α) : x ⊑ y → x ⊑ z → x ⊑ y ⊓ z := by
  intro hxy hxz
  apply le_inf
  intro w hw
  cases hw with
  | inl h => rw [h]; exact hxy
  | inr h => rw [h]; exact hxz

/-- Binary join (supremum) -/
noncomputable def join (x y : α) : α := CompleteLattice.sup (fun z => z = x ∨ z = y)

@[inherit_doc join]
scoped infixl:65 " ⊔ " => join

theorem left_le_join (x y : α) : x ⊑ x ⊔ y := by
  apply le_sup
  left; rfl

theorem right_le_join (x y : α) : y ⊑ x ⊔ y := by
  apply le_sup
  right; rfl

theorem join_le (x y z : α) : x ⊑ z → y ⊑ z → x ⊔ y ⊑ z := by
  intro hxz hyz
  apply sup_le
  intro w hw
  cases hw with
  | inl h => rw [h]; exact hxz
  | inr h => rw [h]; exact hyz

/-- Indexed infimum -/
noncomputable def iInf {ι : Type v} (f : ι → α) : α := inf (fun x => ∃ i, f i = x)

theorem iInf_le {ι : Type v} (f : ι → α) (i : ι) : iInf f ⊑ f i := by
  apply inf_le
  exact ⟨i, rfl⟩

theorem le_iInf {ι : Type v} (f : ι → α) (x : α) : (∀ i, x ⊑ f i) → x ⊑ iInf f := by
  intro h
  apply le_inf
  intro y ⟨i, hi⟩
  rw [← hi]
  exact h i

/-- Pointwise characterization of indexed infimum on function lattices. -/
@[simp] theorem iInf_fun_apply
    {ι : Type v} {σ : Type w} {β : Type u} [CompleteLattice β]
    (f : ι → σ → β) (s : σ) :
    (iInf f) s = iInf (fun i => f i s) := by
  apply PartialOrder.rel_antisymm
  ·
    apply le_iInf
    intro i
    exact (iInf_le f i) s
  ·
    let g : σ → β := fun t => iInf (fun i => f i t)
    have hg : g ⊑ iInf f := by
      apply le_iInf
      intro i t
      exact iInf_le (fun j => f j t) i
    simpa [g] using hg s

/-- Indexed supremum -/
noncomputable def iSup {ι : Type v} (f : ι → α) : α := CompleteLattice.sup (fun x => ∃ i, f i = x)

theorem le_iSup {ι : Type v} (f : ι → α) (i : ι) : f i ⊑ iSup f := by
  apply le_sup
  exact ⟨i, rfl⟩

theorem iSup_le {ι : Type v} (f : ι → α) (x : α) : (∀ i, f i ⊑ x) → iSup f ⊑ x := by
  intro h
  apply sup_le
  intro y ⟨i, hi⟩
  rw [← hi]
  exact h i

/-- Pointwise characterization of `CompleteLattice.sup` on function lattices:
`(sup c) s = sup (fun y => ∃ f, c f ∧ f s = y)`. -/
theorem sup_fun_apply
    {σ : Type v} {β : Type w} [CompleteLattice β]
    (c : (σ → β) → Prop) (s : σ) :
    CompleteLattice.sup c s = CompleteLattice.sup (fun y => ∃ f, c f ∧ f s = y) := by
  apply PartialOrder.rel_antisymm
  · -- sup c s ⊑ sup {y | ∃ f ∈ c, f s = y}
    let g : σ → β := fun t => CompleteLattice.sup (fun y => ∃ f, c f ∧ f t = y)
    have hg : CompleteLattice.sup c ⊑ g := by
      apply sup_le
      intro f hf t
      apply le_sup
      exact ⟨f, hf, rfl⟩
    exact hg s
  · -- sup {y | ∃ f ∈ c, f s = y} ⊑ sup c s
    apply sup_le
    intro y ⟨f, hf, hfs⟩
    rw [← hfs]
    exact (le_sup (c := c) hf) s

/-- Pointwise characterization of binary meet on function lattices. -/
@[simp] theorem meet_fun_apply
    {σ : Type v} {β : Type w} [CompleteLattice β]
    (a b : σ → β) (s : σ) :
    (a ⊓ b) s = a s ⊓ b s := by
  apply PartialOrder.rel_antisymm
  · apply le_meet
    · exact (meet_le_left a b) s
    · exact (meet_le_right a b) s
  · classical
    let f : σ → β := fun t => if t = s then a t ⊓ b t else latticeBot
    have hf_left : f ⊑ a := by
      intro t
      rcases Classical.propDecidable (t = s) with (h|h)
      · simp [f, h, latticeBot_le]
      · simp [f, h, meet_le_left]
    have hf_right : f ⊑ b := by
      intro t
      rcases Classical.propDecidable (t = s) with (h|h)
      · simp [f, h, latticeBot_le]
      · simp [f, h, meet_le_right]
    have hf_meet : f ⊑ a ⊓ b := le_meet f a b hf_left hf_right
    have hs : f s = a s ⊓ b s := by simp [f]
    exact hs ▸ hf_meet s

/-- Pointwise characterization of binary join on function lattices. -/
@[simp] theorem join_fun_apply
    {σ : Type v} {β : Type w} [CompleteLattice β]
    (a b : σ → β) (s : σ) :
    (a ⊔ b) s = a s ⊔ b s := by
  apply PartialOrder.rel_antisymm
  ·
    have hfun : a ⊔ b ⊑ fun t => a t ⊔ b t :=
      join_le a b (fun t => a t ⊔ b t)
        (fun t => left_le_join (a t) (b t))
        (fun t => right_le_join (a t) (b t))
    exact hfun s
  ·
    apply join_le
    · exact (left_le_join a b) s
    · exact (right_le_join a b) s

end LatticeExtensions

/-!
# Prop Embedding into Partial Order

Embedding propositions into a partial order with top and bottom.
-/

attribute [local instance] Classical.propDecidable in
/-- Pure embedding of propositions into a complete lattice. -/
noncomputable def CompleteLattice.pure {l : Type u} [CompleteLattice l] : Prop → l := fun p =>
  if p then ⊤ else latticeBot

@[inherit_doc CompleteLattice.pure]
scoped notation "⌜" p "⌝" => CompleteLattice.pure p

attribute [local instance] Classical.propDecidable in
@[simp]
theorem trueE (l : Type v) [CompleteLattice l] : ⌜True⌝ = (⊤ : l) := by
  simp [CompleteLattice.pure]

attribute [local instance] Classical.propDecidable in
@[simp]
theorem falseE (l : Type v) [CompleteLattice l] : ⌜False⌝ = (latticeBot : l) := by
  simp [CompleteLattice.pure]

attribute [local instance] Classical.propDecidable in
theorem LE.pure_imp {l : Type u} [CompleteLattice l]
  (p₁ p₂ : Prop) : (p₁ → p₂) → ⌜p₁⌝ ⊑ (⌜p₂⌝ : l) := by
  simp only [CompleteLattice.pure]
  intro h
  split
  case isTrue hp1 =>
    split
    case isTrue => exact PartialOrder.rel_refl
    case isFalse hp2 => exact absurd (h hp1) hp2
  case isFalse =>
    exact latticeBot_le _

attribute [local instance] Classical.propDecidable in
@[simp]
theorem LE.pure_intro {l : Type u} [CompleteLattice l]
  (p : Prop) (h : l) : (⌜p⌝ ⊑ h) = (p → ⊤ ⊑ h) := by
  simp only [CompleteLattice.pure]
  apply propext
  constructor
  · intro hle hp
    simp only [hp, ↓reduceIte] at hle
    exact hle
  · intro himp
    split
    next hp => exact himp hp
    next => exact latticeBot_le _

attribute [local instance] Classical.propDecidable in
/-- Proving `pre ⊑ ⌜p⌝` reduces to proving `p`. -/
theorem le_pure {l : Type u} [CompleteLattice l] (x : l) (p : Prop) : p → x ⊑ ⌜p⌝ :=
  fun hp => by simp [CompleteLattice.pure, hp]; exact le_top x

attribute [local instance] Classical.propDecidable in
/-- Pointwise characterization of `⌜p⌝` on function lattices: `(⌜p⌝ : σ → β) s = (⌜p⌝ : β)`. -/
theorem top_fun_apply {σ : Type v} {β : Type w} [CompleteLattice β] (s : σ) :
    (⊤ : σ → β) s = (⊤ : β) :=
  PartialOrder.rel_antisymm (le_top _) (le_top (α := σ → β) (fun _ => ⊤) s)

theorem bot_fun_apply {σ : Type v} {β : Type w} [CompleteLattice β] (s : σ) :
    (latticeBot : σ → β) s = (latticeBot : β) :=
  PartialOrder.rel_antisymm (latticeBot_le (α := σ → β) (fun _ => latticeBot) s) (latticeBot_le _)

attribute [local instance] Classical.propDecidable in
@[simp] theorem pure_fun_apply
    {σ : Type v} {β : Type w} [CompleteLattice β]
    (p : Prop) (s : σ) :
    (⌜p⌝ : σ → β) s = (⌜p⌝ : β) := by
  unfold CompleteLattice.pure
  split <;> simp [top_fun_apply, bot_fun_apply]

attribute [local instance] Classical.propDecidable in
@[simp]
theorem pure_intro_l {l : Type u} [CompleteLattice l] (p : Prop) (x y : l) :
  (x ⊓ ⌜ p ⌝ ⊑ y) = (p → x ⊑ y) := by
  apply propext
  constructor
  · intro h hp
    have hxy : x ⊓ ⊤ ⊑ y := by simp only [CompleteLattice.pure, hp, ↓reduceIte] at h; exact h
    have hx_le_meet : x ⊑ x ⊓ ⊤ := le_meet x x ⊤ PartialOrder.rel_refl (le_top x)
    exact PartialOrder.rel_trans hx_le_meet hxy
  · intro h
    simp only [CompleteLattice.pure]
    split
    next hp => exact PartialOrder.rel_trans (meet_le_left x ⊤) (h hp)
    next => exact PartialOrder.rel_trans (meet_le_right x latticeBot) (latticeBot_le _)

attribute [local instance] Classical.propDecidable in
@[simp]
theorem pure_intro_r {l : Type u} [CompleteLattice l] (p : Prop) (x y : l) :
  (⌜ p ⌝ ⊓ x ⊑ y) = (p → x ⊑ y) := by
  apply propext
  constructor
  · intro h hp
    have hxy : ⊤ ⊓ x ⊑ y := by simp only [CompleteLattice.pure, hp, ↓reduceIte] at h; exact h
    have hx_le_meet : x ⊑ ⊤ ⊓ x := le_meet x ⊤ x (le_top x) PartialOrder.rel_refl
    exact PartialOrder.rel_trans hx_le_meet hxy
  · intro h
    simp only [CompleteLattice.pure]
    split
    next hp => exact PartialOrder.rel_trans (meet_le_right ⊤ x) (h hp)
    next => exact PartialOrder.rel_trans (meet_le_left latticeBot x) (latticeBot_le _)

/-!
# CompleteLattice instance for Prop

We define a CompleteLattice structure on Prop where:
- rel is implication (→)
- sup is existential quantification over the predicate
-/

instance : PartialOrder Prop where
  rel p q := p → q
  rel_refl := id
  rel_trans := fun h1 h2 x => h2 (h1 x)
  rel_antisymm := fun h1 h2 => propext ⟨h1, h2⟩

/-- Supremum for Prop: true iff some element of the set is true -/
def propSup (c : Prop → Prop) : Prop := ∃ p, c p ∧ p

theorem propSup_is_sup (c : Prop → Prop) : is_sup c (propSup c) := by
  intro y
  constructor
  · intro hsup z hcz hz
    apply hsup
    exact Exists.intro z (And.intro hcz hz)
  · intro h ⟨z, hcz, hz⟩
    exact h z hcz hz

instance : CompleteLattice Prop where
  has_sup c := ⟨propSup c, propSup_is_sup c⟩

theorem prop_pre_intro (x y : Prop) : (x → True ⊑ y) → x ⊑ y :=
  fun h hx => h hx trivial

theorem prop_pre_elim (x : Prop) : x → True ⊑ x :=
  fun hx _ => hx

/-- Intro the left component of a meet precondition: `a ⊓ b ⊑ c` becomes `a → b ⊑ c`. -/
theorem meet_pre_intro (a b c : Prop) : (a → b ⊑ c) → a ⊓ b ⊑ c :=
  fun h hab => h ((meet_le_left a b) hab) ((meet_le_right a b) hab)

/-- Intro the right component of a meet precondition: `a ⊓ b ⊑ c` becomes `a → b ⊑ c`. -/
theorem meet_pre_intro' (a b c : Prop) : (b → a ⊑ c) → a ⊓ b ⊑ c :=
  sorry


/-- Eliminate `True` from the left of a meet precondition. -/
theorem true_meet_pre_elim (b c : Prop) : b ⊑ c → True ⊓ b ⊑ c :=
  fun h hab => h ((meet_le_right True b) hab)

@[simp] theorem iInf_prop_eq_forall {ι : Type u} (f : ι → Prop) :
    (iInf f : Prop) = (∀ i, f i) := by
  apply propext
  constructor
  · intro hf i
    exact (iInf_le f i) hf
  · intro hall
    exact (le_iInf f (x := ∀ i, f i) (fun i h => h i)) hall

@[simp] theorem meet_prop_eq_and (a b : Prop) : (a ⊓ b : Prop) = (a ∧ b) := by
  apply propext
  constructor
  · intro hab
    exact ⟨(meet_le_left a b) hab, (meet_le_right a b) hab⟩
  · intro hab
    exact (le_meet (a ∧ b) a b (fun h => h.left) (fun h => h.right)) hab

@[simp] theorem join_prop_eq_or (a b : Prop) : (a ⊔ b : Prop) = (a ∨ b) := by
  apply propext
  constructor
  · intro hab
    exact (join_le a b (a ∨ b) (fun ha => Or.inl ha) (fun hb => Or.inr hb)) hab
  · intro hab
    cases hab with
    | inl ha => exact (left_le_join a b) ha
    | inr hb => exact (right_le_join a b) hb

end Lean.Order
