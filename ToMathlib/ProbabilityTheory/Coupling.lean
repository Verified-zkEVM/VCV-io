/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import ToMathlib.Control.Monad.Transformer
public import Batteries.Control.AlternativeMonad

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

/-- Subprobability distribution. -/
-- @[reducible]
abbrev SubPMF : Type u → Type u := OptionT PMF

namespace SubPMF

variable {α β : Type u}

-- @[reducible] protected def mk (m : PMF (Option α)) : SubPMF α := OptionT.mk m

-- @[reducible] protected def run (m : SubPMF α) : PMF (Option α) := OptionT.run m

-- instance : AlternativeMonad SubPMF := inferInstance

-- instance : LawfulAlternative SubPMF := inferInstance

instance : FunLike (SubPMF α) (Option α) ENNReal :=
  inferInstanceAs (FunLike (PMF (Option α)) (Option α) ENNReal)

-- instance : MonadLift PMF SubPMF := inferInstance

-- instance : LawfulMonadLift PMF SubPMF := inferInstance

theorem pure_eq_pmf_pure {a : α} : (pure a : SubPMF α) = PMF.pure a := by
  simp [pure, liftM, OptionT.pure, monadLift, MonadLift.monadLift, OptionT.lift, PMF.instMonad]

theorem bind_eq_pmf_bind {p : SubPMF α} {f : α → SubPMF β} :
    (p >>= f) = PMF.bind p (fun a => match a with | some a' => f a' | none => PMF.pure none) := by
  simp [bind, OptionT.bind, PMF.instMonad, OptionT.mk]
  rfl

@[simp] lemma map_some_apply_some (p : PMF α) (x : α) : p.map some (some x) = p x := by
  simp [PMF.map_apply]
  rw [tsum_eq_single x (by intro b hb; simp [Ne.symm hb])]
  simp

@[simp] lemma PMF.map_some_apply_some (p : PMF α) (x : α) : (some <$> p) (some x) = p x := by
  change p.map some (some x) = p x
  simp [PMF.map_apply]
  rw [tsum_eq_single x (by intro b hb; simp [Ne.symm hb])]
  simp

/-- `pure a` in SubPMF equals `PMF.pure (some a)` as a PMF on `Option α`. -/
private lemma spmf_pure_eq (a : α) : (pure a : SubPMF α) = PMF.pure (some a) := by
  have : (pure a : SubPMF α) = liftM (PMF.pure a) := by
    simp [pure, liftM, OptionT.pure, monadLift, MonadLift.monadLift, OptionT.lift, PMF.instMonad]
  rw [this]; change (PMF.pure a).bind (fun x => PMF.pure (some x)) = _; rw [PMF.pure_bind]

/-- The functor map for SubPMF equals `PMF.map (Option.map f)`. -/
private lemma spmf_fmap_eq_map (f : α → β) (c : SubPMF α) :
    (f <$> c : SubPMF β) = PMF.map (Option.map f) c := by
  have : (f <$> c : SubPMF β) =
    PMF.bind c (fun a => match a with
      | some a' => (pure (f a') : SubPMF β) | none => PMF.pure none) := by
    show (c >>= (pure ∘ f)) = _; exact bind_eq_pmf_bind
  rw [this]; apply PMF.ext; intro x
  simp only [PMF.bind_apply, PMF.map_apply]
  congr 1; ext y; cases y with
  | none => cases x <;> simp [PMF.pure_apply]
  | some a => simp only [spmf_pure_eq, PMF.pure_apply]; cases x <;> simp

/-- If `PMF.map f c = PMF.pure b` and `f a ≠ b`, then `c a = 0`. -/
private lemma pmf_map_eq_pure_zero {γ δ : Type*} (f : γ → δ) (c : PMF γ) (b : δ)
    (h : PMF.map f c = PMF.pure b) (a : γ) (ha : f a ≠ b) : c a = 0 := by
  have key := congr_fun (congrArg DFunLike.coe h) (f a)
  simp [PMF.map_apply, PMF.pure_apply, ha] at key
  exact key a rfl

/-- A PMF that is zero at all points except `a` equals `PMF.pure a`. -/
private lemma pmf_eq_pure_of_forall_ne_eq_zero {γ : Type*} (p : PMF γ) (a : γ)
    (h : ∀ x, x ≠ a → p x = 0) : p = PMF.pure a := by
  ext x; by_cases hx : x = a
  · subst hx; simp only [PMF.pure_apply, if_true]
    rw [← p.tsum_coe]; exact (tsum_eq_single x (fun b hb => h b hb)).symm
  · simp [PMF.pure_apply, hx, h x hx]

@[ext]
class IsCoupling (c : SubPMF (α × β)) (p : SubPMF α) (q : SubPMF β) : Prop where
  map_fst : Prod.fst <$> c = p
  map_snd : Prod.snd <$> c = q

def Coupling (p : SubPMF α) (q : SubPMF β) :=
  { c : SubPMF (α × β) // IsCoupling c p q }

-- Interaction between `Coupling` and `pure` / `bind`

example (f g : α → β) (h : f = g) : ∀ x, f x = g x := by exact fun x ↦ congrFun h x

/-- The coupling of two pure values must be the pure pair of those values -/
theorem IsCoupling.pure_iff {α β : Type u} {a : α} {b : β} {c : SubPMF (α × β)} :
    IsCoupling c (pure a) (pure b) ↔ c = pure (a, b) := by
  constructor
  · intro ⟨h1, h2⟩
    simp [pure_eq_pmf_pure, liftM, monadLift, OptionT.instMonadLift, OptionT.lift,
      OptionT.mk] at h1 h2
    rw [spmf_fmap_eq_map] at h1 h2
    change PMF.map (Option.map Prod.fst) c = PMF.map some (PMF.pure a) at h1
    change PMF.map (Option.map Prod.snd) c = PMF.map some (PMF.pure b) at h2
    rw [PMF.pure_map] at h1 h2
    rw [show (pure (a, b) : SubPMF (α × β)) = PMF.pure (some (a, b)) from spmf_pure_eq (a, b)]
    exact pmf_eq_pure_of_forall_ne_eq_zero c (some (a, b)) fun x hx => by
      cases x with
      | none => exact pmf_map_eq_pure_zero _ c _ h1 none (by simp)
      | some p =>
        obtain ⟨x, y⟩ := p
        have hne : x ≠ a ∨ y ≠ b := by
          by_contra h; push_neg at h; exact hx (by rw [h.1, h.2])
        cases hne with
        | inl hx => exact pmf_map_eq_pure_zero _ c _ h1 (some (x, y)) (by simp [hx])
        | inr hy => exact pmf_map_eq_pure_zero _ c _ h2 (some (x, y)) (by simp [hy])
  · intro h; constructor <;> simp [h, - liftM_map]

theorem IsCoupling.none_iff {α β : Type u} {c : SubPMF (α × β)} :
    IsCoupling c (failure : SubPMF α) (failure : SubPMF β) ↔ c = failure := by
  simp [failure]
  constructor
  · intro ⟨h1, h2⟩
    rw [spmf_fmap_eq_map] at h1
    change PMF.map (Option.map Prod.fst) c = PMF.pure none at h1
    exact pmf_eq_pure_of_forall_ne_eq_zero c none fun x hx => by
      cases x with
      | none => exact absurd rfl hx
      | some p =>
        exact pmf_map_eq_pure_zero _ c _ h1 (some p) (by simp)
  · intro h
    constructor
    · subst h; rw [spmf_fmap_eq_map]
      change PMF.map _ (PMF.pure none) = PMF.pure none; simp [PMF.pure_map]
    · subst h; rw [spmf_fmap_eq_map]
      change PMF.map _ (PMF.pure none) = PMF.pure none; simp [PMF.pure_map]

/-- `PMF.bind` respects equality on the support. -/
private lemma pmf_bind_congr {γ δ : Type*} (p : PMF γ) (f g : γ → PMF δ)
    (h : ∀ x, p x ≠ 0 → f x = g x) : p.bind f = p.bind g := by
  ext y; simp only [PMF.bind_apply]; congr 1; ext x
  by_cases hx : p x = 0 <;> simp [hx, h x]

/-- Main theorem about coupling and bind operations -/
theorem IsCoupling.bind {α₁ α₂ β₁ β₂ : Type u}
    {p : SubPMF α₁} {q : SubPMF α₂} {f : α₁ → SubPMF β₁} {g : α₂ → SubPMF β₂}
    (c : Coupling p q) (d : (a₁ : α₁) → (a₂ : α₂) → SubPMF (β₁ × β₂))
    (h : ∀ (a₁ : α₁) (a₂ : α₂), c.1.1 (some (a₁, a₂)) ≠ 0 → IsCoupling (d a₁ a₂) (f a₁) (g a₂)) :
    IsCoupling (c.1 >>= λ (p : α₁ × α₂) => d p.1 p.2) (p >>= f) (q >>= g) := by
  obtain ⟨hc₁, hc₂⟩ := c.2
  constructor
  · rw [spmf_fmap_eq_map, bind_eq_pmf_bind, PMF.map_bind]
    conv_rhs => rw [← hc₁, spmf_fmap_eq_map, bind_eq_pmf_bind, PMF.bind_map]
    apply pmf_bind_congr; intro o ho
    cases o with
    | none => simp [PMF.pure_map]
    | some ab =>
      obtain ⟨a₁, a₂⟩ := ab
      simp only [Function.comp, Option.map]
      rw [← spmf_fmap_eq_map]
      exact (h a₁ a₂ ho).map_fst
  · rw [spmf_fmap_eq_map, bind_eq_pmf_bind, PMF.map_bind]
    conv_rhs => rw [← hc₂, spmf_fmap_eq_map, bind_eq_pmf_bind, PMF.bind_map]
    apply pmf_bind_congr; intro o ho
    cases o with
    | none => simp [PMF.pure_map]
    | some ab =>
      obtain ⟨a₁, a₂⟩ := ab
      simp only [Function.comp, Option.map]
      rw [← spmf_fmap_eq_map]
      exact (h a₁ a₂ ho).map_snd

/-- Existential version of `IsCoupling.bind` -/
theorem IsCoupling.exists_bind {α₁ α₂ β₁ β₂ : Type u}
    {p : SubPMF α₁} {q : SubPMF α₂} {f : α₁ → SubPMF β₁} {g : α₂ → SubPMF β₂}
    (c : Coupling p q)
    (h : ∀ (a₁ : α₁) (a₂ : α₂), ∃ (d : SubPMF (β₁ × β₂)), IsCoupling d (f a₁) (g a₂)) :
    ∃ (d : SubPMF (β₁ × β₂)), IsCoupling d (p >>= f) (q >>= g) :=
  let d : (a₁ : α₁) → (a₂ : α₂) → SubPMF (β₁ × β₂) :=
    fun a₁ a₂ => Classical.choose (h a₁ a₂)
  let hd : ∀ (a₁ : α₁) (a₂ : α₂), c.1.1 (some (a₁, a₂)) ≠ 0 → IsCoupling (d a₁ a₂) (f a₁) (g a₂) :=
    fun a₁ a₂ _ => Classical.choose_spec (h a₁ a₂)
  ⟨c.1 >>= λ (p : α₁ × α₂) => d p.1 p.2, IsCoupling.bind c d hd⟩

/-- Every `SubPMF` has a diagonal self-coupling. -/
theorem IsCoupling.refl (p : SubPMF α) :
    IsCoupling (p >>= fun a => pure (a, a)) p p := by
  constructor <;> ext a <;> simp

/-- Diagonal self-coupling witness. -/
def Coupling.refl (p : SubPMF α) : Coupling p p :=
  ⟨p >>= fun a => pure (a, a), IsCoupling.refl p⟩

end SubPMF

end
