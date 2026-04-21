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

open ENNReal

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
    rw [show (pure (a, b) : SPMF (α × β)) = PMF.pure (some (a, b))
        from SPMF.pure_eq_pure_some (a, b)]
    exact PMF.eq_pure_of_forall_ne_eq_zero c (some (a, b)) fun x hx => by
      cases x with
      | none => exact PMF.map_eq_pure_zero _ c _ h1 none (by simp)
      | some p =>
        obtain ⟨x, y⟩ := p
        have hne : x ≠ a ∨ y ≠ b := by
          by_contra h; push Not at h; exact hx (by rw [h.1, h.2])
        cases hne with
        | inl hx => exact PMF.map_eq_pure_zero _ c _ h1 (some (x, y)) (by simp [hx])
        | inr hy => exact PMF.map_eq_pure_zero _ c _ h2 (some (x, y)) (by simp [hy])
  · intro h; constructor <;> simp [h, - liftM_map]

theorem IsCoupling.none_iff {α β : Type u} {c : SPMF (α × β)} :
    IsCoupling c (failure : SPMF α) (failure : SPMF β) ↔ c = failure := by
  simp only [failure]
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
    IsCoupling (c.1 >>= fun (p : α₁ × α₂) => d p.1 p.2) (p >>= f) (q >>= g) := by
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
  ⟨c.1 >>= fun (p : α₁ × α₂) => d p.1 p.2, IsCoupling.bind c d hd⟩

/-- Every `SPMF` has a diagonal self-coupling. -/
theorem IsCoupling.refl (p : SPMF α) :
    IsCoupling (p >>= fun a => pure (a, a)) p p := by
  constructor <;> ext a <;> simp

/-- Diagonal self-coupling witness. -/
noncomputable def Coupling.refl (p : SPMF α) : Coupling p p :=
  ⟨p >>= fun a => pure (a, a), IsCoupling.refl p⟩

/-- Binding against a constant `q` collapses to `q` when the scrutinee has no failure mass. -/
theorem bind_const_of_toPMF_none_eq_zero {p : SPMF α} (hp : p.toPMF none = 0) (q : SPMF β) :
    (p >>= fun _ => q) = q := by
  have h := SPMF.tsum_run_some_eq_one_sub (p := p)
  rw [hp, tsub_zero] at h
  apply SPMF.ext; intro y
  rw [SPMF.apply_eq_toPMF_some, SPMF.apply_eq_toPMF_some, SPMF.toPMF_bind]
  simp only [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_apply]
  calc
    ∑' a, p.toPMF a * (a.elim (PMF.pure none) (fun _ => q.toPMF)) (some y)
        = ∑' a : α, p.toPMF (some a) * q.toPMF (some y) := by
          rw [tsum_option _ ENNReal.summable]
          simp [hp]
    _ = (∑' a : α, p.toPMF (some a)) * q.toPMF (some y) := ENNReal.tsum_mul_right
    _ = q.toPMF (some y) := by rw [h, one_mul]

/-- Product coupling: when both distributions have no failure mass, their independent
product forms a coupling.

This is the core coupling result for reasoning about pairs of computations that never
fail individually (e.g., `OracleComp spec α` via `HasEvalPMF`): the product distribution
`do let a ← p; let b ← q; pure (a, b)` witnesses that the pair has marginals `(p, q)`. -/
theorem IsCoupling.prod {α β : Type u} {p : SPMF α} {q : SPMF β}
    (hp : p.toPMF none = 0) (hq : q.toPMF none = 0) :
    IsCoupling (p >>= fun a => q >>= fun b => pure (a, b)) p q := by
  refine ⟨?_, ?_⟩
  · calc
      Prod.fst <$> (p >>= fun a => q >>= fun b => pure (a, b))
          = p >>= fun a => Prod.fst <$> (q >>= fun b => pure (a, b)) := by
            rw [map_bind]
      _ = p >>= fun a => q >>= fun b => Prod.fst <$> (pure (a, b) : SPMF _) := by
            congr 1; funext a; rw [map_bind]
      _ = p >>= fun a => q >>= fun _ => pure a := by
            congr 1; funext a; congr 1; funext b; rw [map_pure]
      _ = p >>= fun a => pure a := by
            congr 1; funext a; exact bind_const_of_toPMF_none_eq_zero hq (pure a)
      _ = p := bind_pure p
  · calc
      Prod.snd <$> (p >>= fun a => q >>= fun b => pure (a, b))
          = p >>= fun a => Prod.snd <$> (q >>= fun b => pure (a, b)) := by
            rw [map_bind]
      _ = p >>= fun a => q >>= fun b => Prod.snd <$> (pure (a, b) : SPMF _) := by
            congr 1; funext a; rw [map_bind]
      _ = p >>= fun _ => q >>= fun b => pure b := by
            congr 1; funext a; congr 1; funext b; rw [map_pure]
      _ = p >>= fun _ => q := by
            congr 1; funext a; rw [bind_pure]
      _ = q := bind_const_of_toPMF_none_eq_zero hp q

/-- Product coupling witness. -/
noncomputable def Coupling.prod {α β : Type u} {p : SPMF α} {q : SPMF β}
    (hp : p.toPMF none = 0) (hq : q.toPMF none = 0) : Coupling p q :=
  ⟨p >>= fun a => q >>= fun b => pure (a, b), IsCoupling.prod hp hq⟩

/-! ## Dirac couplings: when one marginal is `pure`

When the left marginal is `pure a` (and analogously on the right), the coupling collapses
to the Dirac product `(a, ·) <$> q`. This is the key combinatorial ingredient behind
*anchoring*: the relational logic must agree with the unary logic in this corner. -/

/-- Dirac coupling on the left: `(a, ·) <$> q` is a coupling between `pure a` and `q`,
provided `q` has no failure mass. -/
theorem IsCoupling.dirac_left {α β : Type u} (a : α) {q : SPMF β}
    (hq : q.toPMF none = 0) :
    IsCoupling (((a, ·) : β → α × β) <$> q) (pure a) q := by
  have hmap : (((a, ·) : β → α × β) <$> q) = q >>= fun b => pure (a, b) :=
    (bind_pure_comp _ _).symm
  rw [hmap]
  refine ⟨?_, ?_⟩
  · rw [map_bind]
    have : (fun b : β => (Prod.fst <$> pure (a, b) : SPMF α)) = fun _ => pure a := by
      funext b; rw [map_pure]
    rw [this]
    exact bind_const_of_toPMF_none_eq_zero hq (pure a)
  · rw [map_bind]
    have : (fun b : β => (Prod.snd <$> pure (a, b) : SPMF β)) = pure := by
      funext b; rw [map_pure]
    rw [this]
    exact bind_pure q

/-- Dirac coupling on the right: `(·, b) <$> p` is a coupling between `p` and `pure b`,
provided `p` has no failure mass. -/
theorem IsCoupling.dirac_right {α β : Type u} {p : SPMF α} (b : β)
    (hp : p.toPMF none = 0) :
    IsCoupling (((·, b) : α → α × β) <$> p) p (pure b) := by
  have hmap : (((·, b) : α → α × β) <$> p) = p >>= fun a => pure (a, b) :=
    (bind_pure_comp _ _).symm
  rw [hmap]
  refine ⟨?_, ?_⟩
  · rw [map_bind]
    have : (fun a : α => (Prod.fst <$> pure (a, b) : SPMF α)) = pure := by
      funext a; rw [map_pure]
    rw [this]
    exact bind_pure p
  · rw [map_bind]
    have : (fun a : α => (Prod.snd <$> pure (a, b) : SPMF β)) = fun _ => pure b := by
      funext a; rw [map_pure]
    rw [this]
    exact bind_const_of_toPMF_none_eq_zero hp (pure b)

/-- Pointwise characterization of any coupling whose left marginal is `pure a`:
mass off the slice `{a} × β` is zero. -/
theorem IsCoupling.apply_eq_zero_of_pure_left {α β : Type u} {a : α} {q : SPMF β}
    {c : SPMF (α × β)} (hc : IsCoupling c (pure a) q) {x : α} (b : β) (hxa : x ≠ a) :
    c (x, b) = 0 := by
  have h1 := hc.map_fst
  rw [SPMF.fmap_eq_map] at h1
  change PMF.map (Option.map Prod.fst) c.toPMF = PMF.pure (some a) at h1
  exact PMF.map_eq_pure_zero _ c.toPMF (some a) h1 (some (x, b)) (by simp [hxa])

/-- Pointwise characterization of any coupling whose right marginal is `pure b`:
mass off the slice `α × {b}` is zero. -/
theorem IsCoupling.apply_eq_zero_of_pure_right {α β : Type u} {p : SPMF α} {b : β}
    {c : SPMF (α × β)} (hc : IsCoupling c p (pure b)) (a : α) {y : β} (hyb : y ≠ b) :
    c (a, y) = 0 := by
  have h2 := hc.map_snd
  rw [SPMF.fmap_eq_map] at h2
  change PMF.map (Option.map Prod.snd) c.toPMF = PMF.pure (some b) at h2
  exact PMF.map_eq_pure_zero _ c.toPMF (some b) h2 (some (a, y)) (by simp [hyb])

/-- For a coupling whose left marginal is `pure a`, the value at `(a, b)` matches
the right marginal `q b`. -/
theorem IsCoupling.apply_pure_left_eq {α β : Type u} {a : α} {q : SPMF β}
    {c : SPMF (α × β)} (hc : IsCoupling c (pure a) q) (b : β) :
    c (a, b) = q b := by
  have h2 := hc.map_snd
  rw [SPMF.fmap_eq_map] at h2
  change PMF.map (Option.map Prod.snd) c.toPMF = q.toPMF at h2
  rw [SPMF.apply_eq_toPMF_some, SPMF.apply_eq_toPMF_some]
  refine Eq.symm ?_
  rw [← h2, PMF.map_apply]
  refine (tsum_eq_single (some (a, b)) ?_).trans ?_
  · intro o ho
    cases o with
    | none => simp
    | some p =>
      obtain ⟨x, b'⟩ := p
      have hne : x ≠ a ∨ b' ≠ b := by
        by_contra h
        push Not at h
        exact ho (by rw [h.1, h.2])
      cases hne with
      | inl hxa =>
        have hzero : c.toPMF (some (x, b')) = 0 :=
          hc.apply_eq_zero_of_pure_left b' hxa
        simp [Option.map, hzero]
      | inr hb =>
        have hne_some : (some b : Option β) ≠ some b' := fun h => hb (Option.some.inj h).symm
        simp [Option.map, if_neg hne_some]
  · simp

/-- For a coupling whose right marginal is `pure b`, the value at `(a, b)` matches
the left marginal `p a`. -/
theorem IsCoupling.apply_pure_right_eq {α β : Type u} {p : SPMF α} {b : β}
    {c : SPMF (α × β)} (hc : IsCoupling c p (pure b)) (a : α) :
    c (a, b) = p a := by
  have h1 := hc.map_fst
  rw [SPMF.fmap_eq_map] at h1
  change PMF.map (Option.map Prod.fst) c.toPMF = p.toPMF at h1
  rw [SPMF.apply_eq_toPMF_some, SPMF.apply_eq_toPMF_some]
  refine Eq.symm ?_
  rw [← h1, PMF.map_apply]
  refine (tsum_eq_single (some (a, b)) ?_).trans ?_
  · intro o ho
    cases o with
    | none => simp
    | some q =>
      obtain ⟨a', y⟩ := q
      have hne : a' ≠ a ∨ y ≠ b := by
        by_contra h
        push Not at h
        exact ho (by rw [h.1, h.2])
      cases hne with
      | inl ha =>
        have hne_some : (some a : Option α) ≠ some a' := fun h => ha (Option.some.inj h).symm
        simp [Option.map, if_neg hne_some]
      | inr hyb =>
        have hzero : c.toPMF (some (a', y)) = 0 :=
          hc.apply_eq_zero_of_pure_right a' hyb
        simp [Option.map, hzero]
  · simp

/-- Anchoring identity for tsum-style expectations on the left:
the expected value of `g` under any coupling between `pure a` and `q` is
the marginal expectation `∑' b, q b * g a b`. -/
theorem IsCoupling.tsum_pure_left {α β : Type u} {a : α} {q : SPMF β}
    {c : SPMF (α × β)} (hc : IsCoupling c (pure a) q) (g : α → β → ℝ≥0∞) :
    ∑' z : α × β, c z * g z.1 z.2 = ∑' b, q b * g a b := by
  rw [ENNReal.tsum_prod']
  refine (tsum_eq_single a ?_).trans ?_
  · intro x hx
    have hzero : ∀ b, c (x, b) = 0 := fun b => hc.apply_eq_zero_of_pure_left b hx
    simp_rw [hzero, zero_mul]
    exact tsum_zero
  · refine tsum_congr fun b => ?_
    rw [hc.apply_pure_left_eq]

/-- Anchoring identity for tsum-style expectations on the right:
the expected value of `g` under any coupling between `p` and `pure b` is
the marginal expectation `∑' a, p a * g a b`. -/
theorem IsCoupling.tsum_pure_right {α β : Type u} {p : SPMF α} {b : β}
    {c : SPMF (α × β)} (hc : IsCoupling c p (pure b)) (g : α → β → ℝ≥0∞) :
    ∑' z : α × β, c z * g z.1 z.2 = ∑' a, p a * g a b := by
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  refine (tsum_eq_single b ?_).trans ?_
  · intro y hy
    rw [hc.apply_eq_zero_of_pure_right a hy, zero_mul]
  · rw [hc.apply_pure_right_eq]

end SPMF

end
