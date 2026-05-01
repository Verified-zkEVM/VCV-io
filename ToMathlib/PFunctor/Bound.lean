/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.PFunctor.Free

/-!
# Roll Bounds for the Free Monad of a Polynomial Functor

We define `PFunctor.FreeM.IsRollBound oa budget canRoll cost`, a generalized
predicate that bounds the number of `roll` constructors a term `oa : FreeM P α`
unfolds, parameterized by:
- `B` — the budget type
- `budget : B` — the initial budget
- `canRoll : P.A → B → Prop` — whether a `roll` at position `a` is allowed under
  budget `b`
- `cost : P.A → B → B` — how the budget is updated after a `roll` at `a`

The definition is structural via `FreeM.construct`: `pure` satisfies any bound,
and `roll a r` satisfies the bound when `canRoll a b` holds and each
continuation `r y` satisfies the bound at `cost a b`.

`OracleComp.IsQueryBound` (in `VCVio/OracleComp/QueryTracking/QueryBound.lean`)
is the specialization of this predicate to `FreeM (spec.toPFunctor)` and is
equal to `IsRollBound` definitionally; the bridge lemma in `QueryBound.lean`
witnesses the equivalence by `Iff.rfl`.
-/

@[expose] public section

universe v uA uB

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α β : Type v} {B : Type*}

/-- Generalized roll bound on `FreeM P` parameterized by a budget type `B`,
a validity check `canRoll`, and a cost function `cost`. `pure` satisfies any
bound; `roll a r` satisfies the bound when `canRoll a b` holds and every
continuation satisfies the bound at `cost a b`. -/
def IsRollBound (oa : FreeM P α) (budget : B)
    (canRoll : P.A → B → Prop) (cost : P.A → B → B) : Prop :=
  FreeM.construct
    (C := fun _ => B → Prop)
    (fun _ _ => True)
    (fun a _r ih b => canRoll a b ∧ ∀ y, ih y (cost a b))
    oa budget

@[simp, grind .]
lemma isRollBound_pure (x : α) (b : B)
    (canRoll : P.A → B → Prop) (cost : P.A → B → B) :
    IsRollBound (pure x : FreeM P α) b canRoll cost := trivial

@[simp, grind =]
lemma isRollBound_roll_iff (a : P.A) (r : P.B a → FreeM P α) (b : B)
    (canRoll : P.A → B → Prop) (cost : P.A → B → B) :
    IsRollBound (FreeM.roll a r) b canRoll cost ↔
      canRoll a b ∧ ∀ y, IsRollBound (r y) (cost a b) canRoll cost :=
  Iff.rfl

@[simp, grind =]
lemma isRollBound_liftA_iff (a : P.A) (b : B)
    (canRoll : P.A → B → Prop) (cost : P.A → B → B) :
    IsRollBound (FreeM.liftA a : FreeM P (P.B a)) b canRoll cost ↔ canRoll a b := by
  simp [IsRollBound, FreeM.liftA, FreeM.lift]

private lemma isRollBound_map_aux (oa : FreeM P α) (f : α → β)
    (canRoll : P.A → B → Prop) (cost : P.A → B → B) :
    ∀ {b : B}, (f <$> oa).IsRollBound b canRoll cost ↔
      oa.IsRollBound b canRoll cost := by
  induction oa using FreeM.inductionOn with
  | pure x => intro b; exact ⟨fun _ => trivial, fun _ => trivial⟩
  | roll a r ih =>
    intro b
    simp only [monad_norm, Function.comp_def, monad_bind_def, bind_roll]
    rw [isRollBound_roll_iff, isRollBound_roll_iff]
    exact and_congr_right fun _ => forall_congr' fun y => ih y

@[simp, grind =]
lemma isRollBound_map_iff (oa : FreeM P α) (f : α → β) (b : B)
    (canRoll : P.A → B → Prop) (cost : P.A → B → B) :
    IsRollBound (f <$> oa) b canRoll cost ↔ IsRollBound oa b canRoll cost :=
  isRollBound_map_aux oa f canRoll cost

/-- If `f <$> oa = ob` for any `f`, the roll-bound predicate transfers between
them. The standard shape arises when `oa` and `ob` are two views of the same
underlying computation that agree up to a projection. -/
lemma isRollBound_iff_of_map_eq
    {oa : FreeM P α} {ob : FreeM P β} {f : α → β} {b : B}
    (h : f <$> oa = ob)
    (canRoll : P.A → B → Prop) (cost : P.A → B → B) :
    IsRollBound oa b canRoll cost ↔ IsRollBound ob b canRoll cost := by
  rw [← h]; exact (isRollBound_map_iff oa f b canRoll cost).symm

private lemma isRollBound_congr_aux
    (oa : FreeM P α)
    (canRoll₁ canRoll₂ : P.A → B → Prop) (cost₁ cost₂ : P.A → B → B)
    (hcan : ∀ (a : P.A) (b : B), canRoll₁ a b ↔ canRoll₂ a b)
    (hcost : ∀ (a : P.A) (b : B), cost₁ a b = cost₂ a b) :
    ∀ {b : B}, oa.IsRollBound b canRoll₁ cost₁ ↔ oa.IsRollBound b canRoll₂ cost₂ := by
  induction oa using FreeM.inductionOn with
  | pure _ =>
      intro b
      simp
  | roll a r ih =>
      intro b
      rw [isRollBound_roll_iff, isRollBound_roll_iff]
      constructor
      · intro h
        refine ⟨(hcan a b).1 h.1, fun y => ?_⟩
        have hy : IsRollBound (r y) (cost₁ a b) canRoll₂ cost₂ :=
          (ih y (b := cost₁ a b)).1 (h.2 y)
        simpa [hcost a b] using hy
      · intro h
        refine ⟨(hcan a b).2 h.1, fun y => ?_⟩
        have hy : IsRollBound (r y) (cost₁ a b) canRoll₂ cost₂ := by
          simpa [hcost a b] using h.2 y
        exact (ih y (b := cost₁ a b)).2 hy

lemma isRollBound_congr
    {oa : FreeM P α} {b : B}
    {canRoll₁ canRoll₂ : P.A → B → Prop} {cost₁ cost₂ : P.A → B → B}
    (hcan : ∀ (a : P.A) (b : B), canRoll₁ a b ↔ canRoll₂ a b)
    (hcost : ∀ (a : P.A) (b : B), cost₁ a b = cost₂ a b) :
    oa.IsRollBound b canRoll₁ cost₁ ↔ oa.IsRollBound b canRoll₂ cost₂ :=
  isRollBound_congr_aux oa canRoll₁ canRoll₂ cost₁ cost₂ hcan hcost

/-- Project an `IsRollBound` along a budget projection `proj : B → B'`.

If the source bound at budget `b` validates rolls at every step, the projected
bound at `proj b` is also validated, provided:
* `h_can`  — whenever a step is allowed in the source (`canRoll a b'`), it is
  allowed in the projection (`canRoll' a (proj b')`);
* `h_cost` — the projection commutes with the cost step on the allowed branch
  (`proj (cost a b') = cost' a (proj b')`). -/
lemma IsRollBound.proj
    {B' : Type*} (proj : B → B')
    {oa : FreeM P α} {b : B}
    {canRoll : P.A → B → Prop} {cost : P.A → B → B}
    {canRoll' : P.A → B' → Prop} {cost' : P.A → B' → B'}
    (h_can : ∀ (a : P.A) (b' : B), canRoll a b' → canRoll' a (proj b'))
    (h_cost : ∀ (a : P.A) (b' : B), canRoll a b' → proj (cost a b') = cost' a (proj b'))
    (h : IsRollBound oa b canRoll cost) :
    IsRollBound oa (proj b) canRoll' cost' := by
  induction oa using FreeM.inductionOn generalizing b with
  | pure x => simp
  | roll a r ih =>
      rw [isRollBound_roll_iff] at h ⊢
      refine ⟨h_can a b h.1, fun y => ?_⟩
      have hy : IsRollBound (r y) (proj (cost a b)) canRoll' cost' :=
        ih y (h.2 y)
      rwa [h_cost a b h.1] at hy

/-- Generic bind composition for `IsRollBound` parameterised by an arbitrary
budget type `B` and a binary `combine` operation on it.

The two side conditions are universally quantified so they survive recursion
under `generalizing b₁`:
* `h_can` — extending any validated budget on either side via `combine` keeps
  the roll valid;
* `h_cost` — `cost` distributes left and right over `combine` on validated
  budgets. -/
lemma isRollBound_bind {oa : FreeM P α} {ob : α → FreeM P β}
    {canRoll : P.A → B → Prop} {cost : P.A → B → B}
    (combine : B → B → B) {b₁ b₂ : B}
    (h_can : ∀ a b₁' b₂' b, canRoll a b → canRoll a (combine b₁' b) ∧
      canRoll a (combine b b₂'))
    (h_cost : ∀ a b₁' b₂' b, canRoll a b →
      combine b₁' (cost a b) = cost a (combine b₁' b) ∧
      cost a (combine b b₂') = combine (cost a b) b₂')
    (h₁ : IsRollBound oa b₁ canRoll cost)
    (h₂ : ∀ x, IsRollBound (ob x) b₂ canRoll cost) :
    IsRollBound (oa >>= ob) (combine b₁ b₂) canRoll cost := by
  induction oa using FreeM.inductionOn generalizing b₁ with
  | pure x =>
      simp only [monad_bind_def, bind_pure]
      exact IsRollBound.proj (combine b₁)
        (fun a b hcan => (h_can a b₁ b₂ b hcan).1)
        (fun a b hcan => (h_cost a b₁ b₂ b hcan).1)
        (h₂ x)
  | roll a r ih =>
      rw [isRollBound_roll_iff] at h₁
      simp only [monad_bind_def, bind_roll]
      rw [isRollBound_roll_iff]
      refine ⟨(h_can a b₁ b₂ b₁ h₁.1).2, fun y => ?_⟩
      have hrec := ih y (h₁.2 y)
      rw [(h_cost a b₁ b₂ b₁ h₁.1).2]
      exact hrec

/-- Forward-direction `seq` analogue of `isRollBound_bind`. Reduces to the
bind case via `seq_eq_bind_map` plus `isRollBound_map_iff`. -/
lemma isRollBound_seq {og : FreeM P (α → β)} {oa : FreeM P α}
    {canRoll : P.A → B → Prop} {cost : P.A → B → B}
    (combine : B → B → B) {b₁ b₂ : B}
    (h_can : ∀ a b₁' b₂' b, canRoll a b → canRoll a (combine b₁' b) ∧
      canRoll a (combine b b₂'))
    (h_cost : ∀ a b₁' b₂' b, canRoll a b →
      combine b₁' (cost a b) = cost a (combine b₁' b) ∧
      cost a (combine b b₂') = combine (cost a b) b₂')
    (h₁ : IsRollBound og b₁ canRoll cost)
    (h₂ : IsRollBound oa b₂ canRoll cost) :
    IsRollBound (og <*> oa) (combine b₁ b₂) canRoll cost := by
  rw [seq_eq_bind_map]
  exact isRollBound_bind combine h_can h_cost h₁
    (fun g => (isRollBound_map_iff oa g b₂ canRoll cost).mpr h₂)

end PFunctor.FreeM
