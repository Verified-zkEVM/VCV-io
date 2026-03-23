/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import ToMathlib.Control.Monad.Transformer
public import Batteries.Control.AlternativeMonad
public import ToMathlib.ProbabilityTheory.SPMF

/-!
# Coupling for probability distributions

-/

@[expose] public section

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

namespace SPMF

variable {α β : Type u}

@[ext]
class IsCoupling (c : SPMF (α × β)) (p : SPMF α) (q : SPMF β) : Prop where
  map_fst : Prod.fst <$> c = p
  map_snd : Prod.snd <$> c = q

def Coupling (p : SPMF α) (q : SPMF β) :=
  { c : SPMF (α × β) // IsCoupling c p q }

-- Interaction between `Coupling` and `pure` / `bind`

example (f g : α → β) (h : f = g) : ∀ x, f x = g x := by exact fun x ↦ congrFun h x

/-- The coupling of two pure values must be the pure pair of those values -/
theorem IsCoupling.pure_iff {α β : Type u} {a : α} {b : β} {c : SPMF (α × β)} :
    IsCoupling c (pure a) (pure b) ↔ c = pure (a, b) := by
  constructor
  · intro ⟨h1, h2⟩
    rw [SPMF.fmap_eq_map] at h1 h2
    change PMF.map (Option.map Prod.fst) c = PMF.pure (some a) at h1
    change PMF.map (Option.map Prod.snd) c = PMF.pure (some b) at h2
    rw [show (pure (a, b) : SPMF (α × β)) = PMF.pure (some (a, b)) from SPMF.pure_eq_pure_some (a, b)]
    exact PMF.eq_pure_of_forall_ne_eq_zero c (some (a, b)) fun x hx => by
      cases x with
      | none => exact PMF.map_eq_pure_zero _ c _ h1 none (by simp)
      | some p =>
        obtain ⟨x, y⟩ := p
        have hne : x ≠ a ∨ y ≠ b := by
          by_contra h; push_neg at h; exact hx (by rw [h.1, h.2])
        cases hne with
        | inl hx => exact PMF.map_eq_pure_zero _ c _ h1 (some (x, y)) (by simp [hx])
        | inr hy => exact PMF.map_eq_pure_zero _ c _ h2 (some (x, y)) (by simp [hy])
  · intro h; constructor <;> simp [h, - liftM_map]

theorem IsCoupling.none_iff {α β : Type u} {c : SPMF (α × β)} :
    IsCoupling c (failure : SPMF α) (failure : SPMF β) ↔ c = failure := by
  simp [failure]
  constructor
  · intro ⟨h1, h2⟩
    rw [SPMF.fmap_eq_map] at h1
    change PMF.map (Option.map Prod.fst) c = PMF.pure none at h1
    exact PMF.eq_pure_of_forall_ne_eq_zero c none fun x hx => by
      cases x with
      | none => exact absurd rfl hx
      | some p =>
        exact PMF.map_eq_pure_zero _ c _ h1 (some p) (by simp)
  · intro h
    constructor
    · subst h; rw [SPMF.fmap_eq_map]
      change PMF.map _ (PMF.pure none) = PMF.pure none; simp [PMF.pure_map]
    · subst h; rw [SPMF.fmap_eq_map]
      change PMF.map _ (PMF.pure none) = PMF.pure none; simp [PMF.pure_map]


/-- Main theorem about coupling and bind operations -/
theorem IsCoupling.bind {α₁ α₂ β₁ β₂ : Type u}
    {p : SPMF α₁} {q : SPMF α₂} {f : α₁ → SPMF β₁} {g : α₂ → SPMF β₂}
    (c : Coupling p q) (d : (a₁ : α₁) → (a₂ : α₂) → SPMF (β₁ × β₂))
    (h : ∀ (a₁ : α₁) (a₂ : α₂), c.1.1 (some (a₁, a₂)) ≠ 0 → IsCoupling (d a₁ a₂) (f a₁) (g a₂)) :
    IsCoupling (c.1 >>= λ (p : α₁ × α₂) => d p.1 p.2) (p >>= f) (q >>= g) := by
  obtain ⟨hc₁, hc₂⟩ := c.2
  constructor
  · rw [SPMF.fmap_eq_map, bind_eq_pmf_bind, PMF.map_bind]
    conv_rhs => rw [← hc₁, SPMF.fmap_eq_map, bind_eq_pmf_bind, PMF.bind_map]
    apply PMF.bind_congr; intro o ho
    cases o with
    | none => simp [PMF.pure_map]
    | some ab =>
      obtain ⟨a₁, a₂⟩ := ab
      simp only [Function.comp, Option.map]
      rw [← SPMF.fmap_eq_map]
      exact (h a₁ a₂ ho).map_fst
  · rw [SPMF.fmap_eq_map, bind_eq_pmf_bind, PMF.map_bind]
    conv_rhs => rw [← hc₂, SPMF.fmap_eq_map, bind_eq_pmf_bind, PMF.bind_map]
    apply PMF.bind_congr; intro o ho
    cases o with
    | none => simp [PMF.pure_map]
    | some ab =>
      obtain ⟨a₁, a₂⟩ := ab
      simp only [Function.comp, Option.map]
      rw [← SPMF.fmap_eq_map]
      exact (h a₁ a₂ ho).map_snd

/-- Existential version of `IsCoupling.bind` -/
theorem IsCoupling.exists_bind {α₁ α₂ β₁ β₂ : Type u}
    {p : SPMF α₁} {q : SPMF α₂} {f : α₁ → SPMF β₁} {g : α₂ → SPMF β₂}
    (c : Coupling p q)
    (h : ∀ (a₁ : α₁) (a₂ : α₂), ∃ (d : SPMF (β₁ × β₂)), IsCoupling d (f a₁) (g a₂)) :
    ∃ (d : SPMF (β₁ × β₂)), IsCoupling d (p >>= f) (q >>= g) :=
  let d : (a₁ : α₁) → (a₂ : α₂) → SPMF (β₁ × β₂) :=
    fun a₁ a₂ => Classical.choose (h a₁ a₂)
  let hd : ∀ (a₁ : α₁) (a₂ : α₂), c.1.1 (some (a₁, a₂)) ≠ 0 → IsCoupling (d a₁ a₂) (f a₁) (g a₂) :=
    fun a₁ a₂ _ => Classical.choose_spec (h a₁ a₂)
  ⟨c.1 >>= λ (p : α₁ × α₂) => d p.1 p.2, IsCoupling.bind c d hd⟩

/-- Every `SPMF` has a diagonal self-coupling. -/
theorem IsCoupling.refl (p : SPMF α) :
    IsCoupling (p >>= fun a => pure (a, a)) p p := by
  constructor <;> ext a <;> simp

/-- Diagonal self-coupling witness. -/
noncomputable def Coupling.refl (p : SPMF α) : Coupling p p :=
  ⟨p >>= fun a => pure (a, a), IsCoupling.refl p⟩

end SPMF

end
