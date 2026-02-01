/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Init
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ToMathlib.Control.Monad.Transformer
import Batteries.Control.AlternativeMonad

/-!
# Coupling for probability distributions

-/

universe u

noncomputable section

namespace PMF

variable {α β : Type*}

class IsCoupling (c : PMF (α × β)) (p : PMF α) (q : PMF β) where
  map_fst : c.map Prod.fst = p
  map_snd : c.map Prod.snd = q

def Coupling (p : PMF α) (q : PMF β) :=
  { c : PMF (α × β) // IsCoupling c p q }

end PMF

/-- Subprobability distribution. -/
-- @[reducible]
abbrev SPMF : Type u → Type u := OptionT PMF

namespace SPMF

variable {α β : Type u}

-- @[reducible] protected def mk (m : PMF (Option α)) : SPMF α := OptionT.mk m

-- @[reducible] protected def run (m : SPMF α) : PMF (Option α) := OptionT.run m

-- instance : AlternativeMonad SPMF := inferInstance

-- instance : LawfulAlternative SPMF := inferInstance

instance : FunLike (SPMF α) (Option α) ENNReal :=
  inferInstanceAs (FunLike (PMF (Option α)) (Option α) ENNReal)

-- instance : MonadLift PMF SPMF := inferInstance

-- instance : LawfulMonadLift PMF SPMF := inferInstance

theorem pure_eq_pmf_pure {a : α} : (pure a : SPMF α) = PMF.pure a := by
  simp [pure, liftM, OptionT.pure, monadLift, MonadLift.monadLift, OptionT.lift, PMF.instMonad]

theorem bind_eq_pmf_bind {p : SPMF α} {f : α → SPMF β} :
    (p >>= f) = PMF.bind p (fun a => match a with | some a' => f a' | none => PMF.pure none) := by
  simp only [bind, OptionT.bind, OptionT.mk, PMF.instMonad, PMF.bind_const, PMF.bind_pure]
  rfl

@[simp] lemma map_some_apply_some (p : PMF α) (x : α) : p.map some (some x) = p x := by
  rw [PMF.map_apply, tsum_eq_single x] <;> grind

@[simp] lemma PMF.map_some_apply_some (p : PMF α) (x : α) : (some <$> p) (some x) = p x :=
  SPMF.map_some_apply_some p x

@[ext]
class IsCoupling (c : SPMF (α × β)) (p : SPMF α) (q : SPMF β) : Prop where
  map_fst : Prod.fst <$> c = p
  map_snd : Prod.snd <$> c = q

def Coupling (p : SPMF α) (q : SPMF β) :=
  { c : SPMF (α × β) // IsCoupling c p q }

-- Interaction between `Coupling` and `pure` / `bind`

example (f g : α → β) (h : f = g) : ∀ x, f x = g x := congrFun h

/-- Helper lemma: `p.map f = pure y` iff `f` maps every element in `p`'s support to `y`. -/
theorem PMF.map_eq_pure_iff {α β : Type*} (p : PMF α) (f : α → β) (y : β) :
    p.map f = pure y ↔ ∀ x ∈ p.support, f x = y := by
  simp only [PMF.ext_iff, PMF.map_apply, PMF.support]
  constructor
  · intro h x hx
    by_contra hne
    have hfx := h (f x)
    simp only [PMF.pure_apply, hne, ↓reduceIte, Pure.pure] at hfx
    exact hx (by simpa using ENNReal.tsum_eq_zero.mp hfx x)
  · intro hf x
    by_cases hx : x = y
    all_goals simp only [Function.mem_support, ne_eq, Pure.pure, PMF.pure_apply, ↓reduceIte, *] at *
    · exact (tsum_congr fun a ↦ by grind).trans p.tsum_coe
    · simp only [ENNReal.tsum_eq_zero, ite_eq_right_iff]
      grind

/-
Helper lemma: `p` is `pure x` iff its support is contained in `{x}`.
-/
theorem PMF.support_subset_singleton {α : Type*} (p : PMF α) (x : α) :
    p.support ⊆ {x} ↔ p = pure x := by
  constructor
  · intro hsupport
    have heq := p.support_nonempty.subset_singleton_iff.mp hsupport
    ext y
    simp only [Pure.pure, PMF.pure_apply]
    split_ifs with hy
    · exact hy ▸ (PMF.apply_eq_one_iff p x).mpr heq
    · exact (PMF.apply_eq_zero_iff p y).mpr (heq ▸ hy)
  · intro rfl
    exact (PMF.support_pure x).subset

/-- Helper lemma: `Option.map f x = some y` iff `x = some a` and `f a = y`. -/
theorem Option.map_eq_some_iff {α β : Type*} (f : α → β) (x : Option α) (y : β) :
    x.map f = some y ↔ ∃ a, x = some a ∧ f a = y :=
  _root_.Option.map_eq_some_iff

theorem pure_eq_pure_some {α : Type*} (a : α) : (pure a : SPMF α) = PMF.pure (some a) := rfl

/-- Helper lemma: `f <$> p = pure y` in `SPMF` iff for all `x` in `p`'s support, `x` is `some a`
with `f a = y`. -/
theorem map_eq_pure_iff {α β : Type u} (p : SPMF α) (f : α → β) (y : β) :
    f <$> p = pure y ↔ ∀ x ∈ p.support, ∃ a, x = some a ∧ f a = y := by
  rw [pure_eq_pure_some]
  have fmap_eq : f <$> p = PMF.map (Option.map f) p := by ext x; simp only [OptionT.run_map]; rfl
  rw [fmap_eq]
  change PMF.map (Option.map f) p = pure (some y) ↔ _
  simp only [PMF.map_eq_pure_iff, Option.map_eq_some_iff]

/- The coupling of two pure values must be the pure pair of those values -/
theorem IsCoupling.pure_iff {α β : Type u} {a : α} {b : β} {c : SPMF (α × β)} :
    IsCoupling c (pure a) (pure b) ↔ c = pure (a, b) := by
  constructor
  · intro ⟨h1, h2⟩
    apply (PMF.support_subset_singleton ..).mp
    intro x hx
    rw [map_eq_pure_iff] at h1 h2
    obtain ⟨z, rfl, hz⟩ := h1 x hx
    obtain ⟨z', hz', hz''⟩ := h2 _ hx
    grind
  · rintro rfl; constructor <;> simp

theorem IsCoupling.none_iff {α β : Type u} {c : SPMF (α × β)} :
    IsCoupling c (failure : SPMF α) (failure : SPMF β) ↔ c = failure := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have h_support : ∀ x ∈ c.support, x = none := by
      intro x hx
      replace h₁ := congr_arg PMF.support h₁
      replace h₂ := congr_arg PMF.support h₂
      simp_all [PMF.support, Function.support, Set.ext_iff]
      cases x <;> simp_all
      specialize h₁ (Option.some (‹α × β›.1))
      specialize h₂ (Option.some (‹α × β›.2))
      simp_all [Alternative.failure, OptionT.fail, OptionT.mk, Pure.pure, Functor.map,
        OptionT.bind, OptionT.pure]
      simp_all [Bind.bind]
      cases h₁ (Option.some ‹_›) <;> cases h₂ (Option.some ‹_›) <;> simp_all
    exact (PMF.support_subset_singleton c none).mp fun x hx ↦ h_support x hx
  · rintro rfl
    exact ⟨map_failure _, map_failure _⟩

/-- Main theorem about coupling and bind operations -/
theorem IsCoupling.bind {α₁ α₂ β₁ β₂ : Type u}
    {p : SPMF α₁} {q : SPMF α₂} {f : α₁ → SPMF β₁} {g : α₂ → SPMF β₂}
    (c : Coupling p q) (d : (a₁ : α₁) → (a₂ : α₂) → SPMF (β₁ × β₂))
    (h : ∀ (a₁ : α₁) (a₂ : α₂), c.1.1 (some (a₁, a₂)) ≠ 0 → IsCoupling (d a₁ a₂) (f a₁) (g a₂)) :
    IsCoupling (c.1 >>= λ (p : α₁ × α₂) => d p.1 p.2) (p >>= f) (q >>= g) := by
  obtain ⟨hc₁, hc₂⟩ := c.2
  constructor
  · simp [← hc₁]; congr; funext ⟨a₁, a₂⟩; have := h a₁ a₂; sorry
  · simp [← hc₂]; sorry

/-- Existential version of `IsCoupling.bind` -/
theorem IsCoupling.exists_bind {α₁ α₂ β₁ β₂ : Type u}
    {p : SPMF α₁} {q : SPMF α₂} {f : α₁ → SPMF β₁} {g : α₂ → SPMF β₂}
    (c : Coupling p q)
    (h : ∀ (a₁ : α₁) (a₂ : α₂), ∃ (d : SPMF (β₁ × β₂)), IsCoupling d (f a₁) (g a₂)) :
    ∃ (d : SPMF (β₁ × β₂)), IsCoupling d (p >>= f) (q >>= g) :=
  let d := fun a₁ a₂ ↦ (h a₁ a₂).choose
  let hd := fun a₁ a₂ _ ↦ (h a₁ a₂).choose_spec
  ⟨c.1 >>= fun (a, b) ↦ d a b, .bind c d hd⟩

end SPMF

end
