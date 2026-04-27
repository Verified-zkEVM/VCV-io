/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import ToMathlib.General
import ToMathlib.PFunctor.Bound
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT

/-!
# Bounding Queries Made by a Computation

This file defines a predicate `IsQueryBound oa budget canQuery cost` parameterized by:
- `B` — the budget type
- `budget : B` — the initial budget
- `canQuery : ι → B → Prop` — whether a query to oracle `t` is allowed under budget `b`
- `cost : ι → B → B` — how the budget is updated after a query to oracle `t`

The definition is structural via `OracleComp.construct`: `pure` satisfies any bound, and
`query t >>= mx` satisfies the bound when `canQuery t b` holds and each continuation
satisfies the bound with the updated budget `cost t b`.

The classical per-index and total query bounds are recovered by `IsPerIndexQueryBound`
and `IsTotalQueryBound`.
-/

open OracleSpec

universe u

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

section IsQueryBound

variable {B : Type*}

/-- Generalized query bound parameterized by a budget type, a validity check, and a cost
function. `pure` satisfies any bound; `query t >>= mx` satisfies the bound when
`canQuery t b` and every continuation satisfies the bound at `cost t b`.

This is the specialization of `PFunctor.FreeM.IsRollBound` to
`OracleComp spec α = FreeM spec.toPFunctor α`: an oracle index `t : ι` plays
the role of a polynomial-functor position, and a query continuation
`spec t → OracleComp spec α` is the FreeM `roll` continuation. Most
structural lemmas defer to their FreeM analogues. -/
def IsQueryBound (oa : OracleComp spec α) (budget : B)
    (canQuery : ι → B → Prop) (cost : ι → B → B) : Prop :=
  PFunctor.FreeM.IsRollBound (P := spec.toPFunctor) oa budget canQuery cost

/-- The bridge to the FreeM-level predicate is `Iff.rfl`: `IsQueryBound` is
literally `PFunctor.FreeM.IsRollBound` on the underlying free monad. -/
theorem isQueryBound_iff_isRollBound (oa : OracleComp spec α) (budget : B)
    (canQuery : ι → B → Prop) (cost : ι → B → B) :
    IsQueryBound oa budget canQuery cost ↔
      PFunctor.FreeM.IsRollBound (P := spec.toPFunctor) oa budget canQuery cost :=
  Iff.rfl

@[simp, grind .]
lemma isQueryBound_pure (x : α) (b : B)
    (canQuery : ι → B → Prop) (cost : ι → B → B) :
    IsQueryBound (pure x : OracleComp spec α) b canQuery cost := trivial

@[simp, grind =]
lemma isQueryBound_query_bind_iff (t : ι) (mx : spec t → OracleComp spec α)
    (b : B) (canQuery : ι → B → Prop) (cost : ι → B → B) :
    IsQueryBound (liftM (spec.query t) >>= mx) b canQuery cost ↔
      canQuery t b ∧ ∀ u, IsQueryBound (mx u) (cost t b) canQuery cost :=
  Iff.rfl

@[simp, grind =]
lemma isQueryBound_query_iff (t : ι) (b : B)
    (canQuery : ι → B → Prop) (cost : ι → B → B) :
    IsQueryBound (liftM (spec.query t) : OracleComp spec _) b canQuery cost ↔
    canQuery t b :=
  PFunctor.FreeM.isRollBound_liftA_iff (P := spec.toPFunctor) t b canQuery cost

private lemma isQueryBound_map_aux (oa : OracleComp spec α) (f : α → β)
    (canQuery : ι → B → Prop) (cost : ι → B → B) :
    ∀ {b : B}, (f <$> oa).IsQueryBound b canQuery cost ↔
      oa.IsQueryBound b canQuery cost :=
  fun {b} => PFunctor.FreeM.isRollBound_map_iff oa f b canQuery cost

@[simp, grind =]
lemma isQueryBound_map_iff (oa : OracleComp spec α) (f : α → β) (b : B)
    (canQuery : ι → B → Prop) (cost : ι → B → B) :
    IsQueryBound (f <$> oa) b canQuery cost ↔ IsQueryBound oa b canQuery cost :=
  PFunctor.FreeM.isRollBound_map_iff oa f b canQuery cost

/-- If `f <$> oa = ob` for any `f`, the query-bound predicate transfers between them. The
standard shape is `oa = (simulateQ wrapped mx).run s` and `ob = simulateQ inner mx` (or
`(simulateQ inner mx).run s'`), where `wrapped` threads bookkeeping (a state, a writer log)
that the underlying simulation does not see. The projection equality is supplied by the
corresponding `QueryImpl.fst_map_run_*` lemma (with `f = Prod.fst`) or by an auxiliary
projection identity such as `withCachingAux_run_proj_eq` (with `f = Prod.map id Prod.fst`). -/
lemma isQueryBound_iff_of_map_eq
    {β : Type u} {oa : OracleComp spec α} {ob : OracleComp spec β} {f : α → β} {b : B}
    (h : f <$> oa = ob) (canQuery : ι → B → Prop) (cost : ι → B → B) :
    IsQueryBound oa b canQuery cost ↔ IsQueryBound ob b canQuery cost :=
  PFunctor.FreeM.isRollBound_iff_of_map_eq h canQuery cost

lemma isQueryBound_congr
    {oa : OracleComp spec α} {b : B}
    {canQuery₁ canQuery₂ : ι → B → Prop} {cost₁ cost₂ : ι → B → B}
    (hcan : ∀ (t : ι) (b : B), canQuery₁ t b ↔ canQuery₂ t b)
    (hcost : ∀ (t : ι) (b : B), cost₁ t b = cost₂ t b) :
    oa.IsQueryBound b canQuery₁ cost₁ ↔ oa.IsQueryBound b canQuery₂ cost₂ :=
  PFunctor.FreeM.isRollBound_congr hcan hcost

/-- Project an `IsQueryBound` along a budget projection `proj : B → B'`.

If the source bound at budget `b` validates queries at every step, the projected
bound at `proj b` is also validated, provided:
* `h_can`  — whenever a step is allowed in the source (`canQuery t b'`), it is
  allowed in the projection (`canQuery' t (proj b')`);
* `h_cost` — the projection commutes with the cost step on the allowed branch
  (`proj (cost t b') = cost' t (proj b')`).

Typical use: extract a single-coordinate query bound (e.g. `qS`-only) from a
multi-coordinate bound (e.g. `(qS, qH)` from `signHashQueryBound`) by setting
`proj := Prod.fst`. -/
lemma IsQueryBound.proj
    {B' : Type*} (proj : B → B')
    {oa : OracleComp spec α} {b : B}
    {canQuery : ι → B → Prop} {cost : ι → B → B}
    {canQuery' : ι → B' → Prop} {cost' : ι → B' → B'}
    (h_can : ∀ (t : ι) (b' : B), canQuery t b' → canQuery' t (proj b'))
    (h_cost : ∀ (t : ι) (b' : B), canQuery t b' → proj (cost t b') = cost' t (proj b'))
    (h : IsQueryBound oa b canQuery cost) :
    IsQueryBound oa (proj b) canQuery' cost' :=
  PFunctor.FreeM.IsRollBound.proj proj h_can h_cost h

/-- Generic bind composition for `IsQueryBound` parameterised by an arbitrary budget type
`B` and a binary `combine` operation on it. The natural-number versions
(`isTotalQueryBound_bind`, `isQueryBoundP_bind`, `isPerIndexQueryBound_bind`) are special
cases at `combine := (· + ·)`; the vector-budget `cmaSignHashQueryBound_bind` uses this
directly with component-wise `+`.

The two side conditions are universally quantified so they survive recursion under
`generalizing b₁`:
* `h_can` — extending any validated budget on either side via `combine` keeps the query
  valid;
* `h_cost` — `cost` distributes left and right over `combine` on validated budgets. -/
lemma isQueryBound_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {canQuery : ι → B → Prop} {cost : ι → B → B}
    (combine : B → B → B) {b₁ b₂ : B}
    (h_can : ∀ t b₁' b₂' b, canQuery t b → canQuery t (combine b₁' b) ∧
      canQuery t (combine b b₂'))
    (h_cost : ∀ t b₁' b₂' b, canQuery t b →
      combine b₁' (cost t b) = cost t (combine b₁' b) ∧
      cost t (combine b b₂') = combine (cost t b) b₂')
    (h₁ : IsQueryBound oa b₁ canQuery cost)
    (h₂ : ∀ x, IsQueryBound (ob x) b₂ canQuery cost) :
    IsQueryBound (oa >>= ob) (combine b₁ b₂) canQuery cost :=
  PFunctor.FreeM.isRollBound_bind combine h_can h_cost h₁ h₂

/-- Forward-direction `seq` analogue of `isQueryBound_bind`. Reduces to the bind case via
`seq_eq_bind_map` plus `isQueryBound_map_iff` to discharge the constant continuation. -/
lemma isQueryBound_seq {og : OracleComp spec (α → β)} {oa : OracleComp spec α}
    {canQuery : ι → B → Prop} {cost : ι → B → B}
    (combine : B → B → B) {b₁ b₂ : B}
    (h_can : ∀ t b₁' b₂' b, canQuery t b → canQuery t (combine b₁' b) ∧
      canQuery t (combine b b₂'))
    (h_cost : ∀ t b₁' b₂' b, canQuery t b →
      combine b₁' (cost t b) = cost t (combine b₁' b) ∧
      cost t (combine b b₂') = combine (cost t b) b₂')
    (h₁ : IsQueryBound og b₁ canQuery cost)
    (h₂ : IsQueryBound oa b₂ canQuery cost) :
    IsQueryBound (og <*> oa) (combine b₁ b₂) canQuery cost :=
  PFunctor.FreeM.isRollBound_seq combine h_can h_cost h₁ h₂

/-- Transfer a structural query bound through `simulateQ` into a stateful target semantics,
provided each simulated source query has a target-side step bound and the target-side bind
rule composes those step budgets with the recursive continuation budget. -/
theorem IsQueryBound.simulateQ_run_of_step
    {ι' : Type u} {spec' : OracleSpec ι'} {σ : Type u} {B' : Type*}
    {canQuery : ι → B → Prop} {cost : ι → B → B}
    {canQuery' : ι' → B' → Prop} {cost' : ι' → B' → B'}
    {combine : B' → B' → B'} {mapBudget : B → B'} {stepBudget : ι → B → B'}
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    {oa : OracleComp spec α} {budget : B}
    (h : IsQueryBound oa budget canQuery cost)
    (hbind : ∀ {γ δ : Type u} {oa' : OracleComp spec' γ} {ob : γ → OracleComp spec' δ}
        {b₁ b₂ : B'},
      IsQueryBound oa' b₁ canQuery' cost' →
      (∀ x, IsQueryBound (ob x) b₂ canQuery' cost') →
      IsQueryBound (oa' >>= ob) (combine b₁ b₂) canQuery' cost')
    (hstep : ∀ t b s, canQuery t b →
      IsQueryBound ((impl t).run s) (stepBudget t b) canQuery' cost')
    (hcombine : ∀ t b, canQuery t b →
      combine (stepBudget t b) (mapBudget (cost t b)) = mapBudget b)
    (s : σ) :
    IsQueryBound ((simulateQ impl oa).run s) (mapBudget budget) canQuery' cost' := by
  induction oa using OracleComp.inductionOn generalizing budget s with
  | pure x =>
      simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isQueryBound_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind]
      have hstep' :
          IsQueryBound
            ((liftM (impl t) : StateT σ (OracleComp spec') (spec.Range t)).run s)
            (stepBudget t budget) canQuery' cost' := by
        simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using
          hstep t budget s h.1
      have hrest : ∀ p : spec.Range t × σ,
          IsQueryBound ((simulateQ impl (mx p.1)).run p.2)
            (mapBudget (cost t budget)) canQuery' cost' :=
        fun p => ih p.1 (h.2 p.1) p.2
      simpa [hcombine t budget h.1] using hbind hstep' hrest

end IsQueryBound

section IsQueryBoundP

/-- Predicate-targeted query bound: a middle ground between `IsQueryBound` and
`IsPerIndexQueryBound` / `IsTotalQueryBound`. `IsQueryBoundP oa p n` says that `oa` makes at most
`n` queries to oracle indices satisfying `p`, with no constraint on the number of queries to
indices where `p` fails.

This is built on the generic `IsQueryBound` with the validity check `¬ p t ∨ 0 < qb` and the cost
function that decrements the budget only on `p`-indices. -/
def IsQueryBoundP (oa : OracleComp spec α) (p : ι → Prop) [DecidablePred p] (n : ℕ) : Prop :=
  IsQueryBound oa n (fun t qb => ¬ p t ∨ 0 < qb)
    (fun t qb => if p t then qb - 1 else qb)

variable (p : ι → Prop) [DecidablePred p]

@[grind =]
lemma isQueryBoundP_def (oa : OracleComp spec α) (n : ℕ) : IsQueryBoundP oa p n ↔
    IsQueryBound oa n (fun t qb => ¬ p t ∨ 0 < qb)
      (fun t qb => if p t then qb - 1 else qb) := Iff.rfl

/-- `IsQueryBoundP` is `IsRollBound` on the underlying `FreeM` with the
predicate-targeted validity and cost. -/
theorem isQueryBoundP_iff_isRollBound (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa p n ↔
      PFunctor.FreeM.IsRollBound (P := spec.toPFunctor) oa n
        (fun t qb => ¬ p t ∨ 0 < qb)
        (fun t qb => if p t then qb - 1 else qb) :=
  Iff.rfl

/-- `IsQueryBoundP` rephrased with the `if … then 0 < b else True` validity check.
This is the shape that arises naturally in `expectedSCost` hypotheses, where the
gap between the two implementations is paid only on `p`-queries. -/
theorem isQueryBoundP_iff_isQueryBound_if (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa p n ↔
      IsQueryBound oa n
        (fun t b => if p t then 0 < b else True)
        (fun t b => if p t then b - 1 else b) :=
  isQueryBound_congr
    (fun t b => by by_cases ht : p t <;> simp [ht])
    (fun _ _ => rfl)

@[simp, grind =]
lemma isQueryBoundP_query_bind_iff (t : ι) (mx : spec t → OracleComp spec α) (n : ℕ) :
    IsQueryBoundP (liftM (spec.query t) >>= mx) p n ↔
      (¬ p t ∨ 0 < n) ∧ ∀ u, IsQueryBoundP (mx u) p (if p t then n - 1 else n) :=
  Iff.rfl

@[simp]
lemma isQueryBoundP_pure (x : α) (n : ℕ) :
    IsQueryBoundP (pure x : OracleComp spec α) p n := trivial

@[simp]
lemma isQueryBoundP_query_iff (t : spec.Domain) (n : ℕ) :
    IsQueryBoundP (liftM (spec.query t) : OracleComp spec _) p n ↔ (p t → 0 < n) := by
  simp [IsQueryBoundP, imp_iff_not_or]

variable {p}

/-- Projection variant of `IsQueryBound.proj` that lands directly in
`IsQueryBoundP`. Given a vector-budget bound on `oa`, project to a scalar
budget along `proj : B → ℕ` and conclude an `IsQueryBoundP` bound at the
projected coordinate. The two side conditions only have to address `p`-queries:
allowed source steps must keep the projected budget positive when `p` fires
(`h_can`), and the projection must commute with the cost step in the shape
that `IsQueryBoundP` decrements on (`h_cost`).

Typical use: extract a per-predicate scalar bound (e.g. signing-only `qS`
from a `(qS, qH)` pair) without spelling out the `if … then 0 < b else True`
boilerplate at the call site. -/
lemma IsQueryBoundP.proj
    {B : Type*} {oa : OracleComp spec α} {b : B}
    {canQuery : ι → B → Prop} {cost : ι → B → B}
    (proj : B → ℕ)
    (h_can : ∀ (t : ι) (b' : B), canQuery t b' → p t → 0 < proj b')
    (h_cost : ∀ (t : ι) (b' : B), canQuery t b' →
      proj (cost t b') = if p t then proj b' - 1 else proj b')
    (h : IsQueryBound oa b canQuery cost) :
    IsQueryBoundP oa p (proj b) := by
  rw [isQueryBoundP_iff_isQueryBound_if]
  refine OracleComp.IsQueryBound.proj proj ?_ h_cost h
  intro t b' hcan
  by_cases hpt : p t
  · simp [hpt, h_can t b' hcan hpt]
  · simp [hpt]

theorem IsQueryBoundP.mono {oa : OracleComp spec α} {n m : ℕ}
    (h : IsQueryBoundP oa p n) (hnm : n ≤ m) : IsQueryBoundP oa p m := by
  induction oa using OracleComp.inductionOn generalizing n m with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨h.1.imp id (fun hn => Nat.lt_of_lt_of_le hn hnm), fun u => ?_⟩
      have hu := h.2 u
      by_cases hpt : p t
      · simp only [if_pos hpt] at hu ⊢
        exact ih u hu (Nat.sub_le_sub_right hnm 1)
      · simp only [if_neg hpt] at hu ⊢
        exact ih u hu hnm

/-- `oa >>= ob` is `p`-bounded by `n + m` when `oa` is `p`-bounded by `n` and every reachable
continuation `ob x` is `p`-bounded by `m`. -/
lemma isQueryBoundP_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n m : ℕ}
    (h : IsQueryBoundP oa p n) (h' : ∀ x ∈ support oa, IsQueryBoundP (ob x) p m) :
    IsQueryBoundP (oa >>= ob) p (n + m) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x =>
      simp only [pure_bind]
      exact (h' x (by simp)).mono (Nat.le_add_left _ _)
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [bind_assoc, isQueryBoundP_query_bind_iff]
      refine ⟨h.1.imp id (fun hn => Nat.lt_of_lt_of_le hn (Nat.le_add_right _ _)), fun u => ?_⟩
      have hmx : IsQueryBoundP (mx u) p (if p t then n - 1 else n) := h.2 u
      have hob : ∀ x ∈ support (mx u), IsQueryBoundP (ob x) p m := fun x hx =>
        h' x ((mem_support_bind_iff _ _ _).mpr ⟨u, mem_support_query t u, hx⟩)
      have ih' := ih u hmx hob
      refine ih'.mono ?_
      by_cases hpt : p t
      · simp only [if_pos hpt]
        rcases h.1 with hnp | hn
        · exact absurd hpt hnp
        · omega
      · simp only [if_neg hpt]; omega

/-- Predicate-extensionality: replacing `p` with an equivalent predicate does not change the
bound. -/
lemma isQueryBoundP_congr_pred {oa : OracleComp spec α} {p p' : ι → Prop}
    [DecidablePred p] [DecidablePred p'] {n : ℕ}
    (hpp : ∀ t, p t ↔ p' t) :
    IsQueryBoundP oa p n ↔ IsQueryBoundP oa p' n := by
  refine isQueryBound_congr (fun t b => ?_) (fun t b => ?_)
  · rw [hpp t]
  · by_cases ht' : p' t
    · rw [if_pos ((hpp t).mpr ht'), if_pos ht']
    · rw [if_neg (fun h => ht' ((hpp t).mp h)), if_neg ht']

@[simp]
lemma isQueryBoundP_map_iff (oa : OracleComp spec α) (f : α → β) (n : ℕ) :
    IsQueryBoundP (f <$> oa) p n ↔ IsQueryBoundP oa p n :=
  isQueryBound_map_aux oa f _ _

/-- Forward-direction `seq` analogue of `isQueryBoundP_bind`. Reduces to the bind case via
`seq_eq_bind_map` plus `isQueryBoundP_map_iff` to discharge the constant continuation. -/
lemma isQueryBoundP_seq {og : OracleComp spec (α → β)} {oa : OracleComp spec α} {n m : ℕ}
    (h : IsQueryBoundP og p n) (h' : IsQueryBoundP oa p m) :
    IsQueryBoundP (og <*> oa) p (n + m) := by
  rw [seq_eq_bind_map]
  exact isQueryBoundP_bind h
    (fun g _ => (isQueryBoundP_map_iff oa g m).mpr h')

/-- Predicate-targeted analogue of `isQueryBound_iff_of_map_eq`: if `f <$> oa = ob` for any `f`,
then `IsQueryBoundP` transfers between them. -/
lemma isQueryBoundP_iff_of_map_eq
    {β : Type u} {oa : OracleComp spec α} {ob : OracleComp spec β} {f : α → β} {n : ℕ}
    (h : f <$> oa = ob) :
    IsQueryBoundP oa p n ↔ IsQueryBoundP ob p n := by
  rw [← h]; exact (isQueryBoundP_map_iff oa f n).symm

/-- The conjunction of two scalar `IsQueryBoundP` bounds combines into a vector-budget
`IsQueryBound` whose `canQuery` admits a query iff every active predicate has positive
budget, and whose cost decrements only the matching coordinates.

This is the canonical bridge from the predicate-targeted scalar API to the vector-budget API:
proofs that decompose a multi-oracle adversary into per-oracle counts can use the conjunction
form for hypothesis statements while reusing the existing `IsQueryBound` propagation machinery
(such as `simulateQ_run_of_step`) on the combined bound. The two predicates need not be
disjoint — at an overlapping query both coordinates decrement and both must be positive,
which exactly tracks the independent per-predicate counts. -/
theorem IsQueryBoundP.and_isQueryBound_pair
    {oa : OracleComp spec α}
    {p₁ p₂ : ι → Prop} [DecidablePred p₁] [DecidablePred p₂]
    {n₁ n₂ : ℕ}
    (h₁ : oa.IsQueryBoundP p₁ n₁) (h₂ : oa.IsQueryBoundP p₂ n₂) :
    oa.IsQueryBound (n₁, n₂)
      (fun t b => (¬ p₁ t ∨ 0 < b.1) ∧ (¬ p₂ t ∨ 0 < b.2))
      (fun t b => (if p₁ t then b.1 - 1 else b.1, if p₂ t then b.2 - 1 else b.2)) := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ with
  | pure x => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h₁ h₂
      rw [isQueryBound_query_bind_iff]
      refine ⟨⟨h₁.1, h₂.1⟩, fun u => ?_⟩
      exact ih u (h₁.2 u) (h₂.2 u)

end IsQueryBoundP

section IsPerIndexQueryBound

variable [DecidableEq ι]

/-- Per-index query bound: `qb t` gives the maximum number of queries to oracle `t`.
Each query to `t` decrements `qb t` by one. Recovers the classical notion. -/
abbrev IsPerIndexQueryBound (oa : OracleComp spec α) (qb : ι → ℕ) : Prop :=
  IsQueryBound oa qb (fun t qb => 0 < qb t) (fun t qb => Function.update qb t (qb t - 1))

/-- `IsPerIndexQueryBound` is `IsRollBound` on the underlying `FreeM` with the
per-index validity and cost. -/
theorem isPerIndexQueryBound_iff_isRollBound (oa : OracleComp spec α) (qb : ι → ℕ) :
    IsPerIndexQueryBound oa qb ↔
      PFunctor.FreeM.IsRollBound (P := spec.toPFunctor) oa qb
        (fun t qb => 0 < qb t)
        (fun t qb => Function.update qb t (qb t - 1)) :=
  Iff.rfl

@[simp]
lemma isPerIndexQueryBound_pure (x : α) (qb : ι → ℕ) :
    IsPerIndexQueryBound (pure x : OracleComp spec α) qb := trivial

lemma isPerIndexQueryBound_query_bind_iff (t : ι) (mx : spec t → OracleComp spec α)
    (qb : ι → ℕ) :
    IsPerIndexQueryBound (liftM (spec.query t) >>= mx) qb ↔
      0 < qb t ∧ ∀ u, IsPerIndexQueryBound (mx u) (Function.update qb t (qb t - 1)) :=
  Iff.rfl

@[simp]
lemma isPerIndexQueryBound_query_iff (t : ι) (qb : ι → ℕ) :
    IsPerIndexQueryBound (liftM (spec.query t) : OracleComp spec _) qb ↔
    0 < qb t := by
  simp [IsPerIndexQueryBound]

private lemma update_le_update {qb qb' : ι → ℕ} {t : ι} (hle : qb ≤ qb') :
    Function.update qb t (qb t - 1) ≤ Function.update qb' t (qb' t - 1) := by
  intro j
  by_cases hj : j = t
  · rw [hj, Function.update_self, Function.update_self]
    exact Nat.sub_le_sub_right (hle t) 1
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    exact hle j

private lemma isPerIndexQueryBound_mono_aux (oa : OracleComp spec α) :
    ∀ {qb qb' : ι → ℕ}, qb ≤ qb' →
      oa.IsPerIndexQueryBound qb → oa.IsPerIndexQueryBound qb' := by
  induction oa using OracleComp.inductionOn with
  | pure _ => intros; trivial
  | query_bind t mx ih =>
    intro qb qb' hle h
    rw [isPerIndexQueryBound_query_bind_iff] at h ⊢
    exact ⟨Nat.lt_of_lt_of_le h.1 (hle t), fun u => ih u (update_le_update hle) (h.2 u)⟩

lemma IsPerIndexQueryBound.mono {oa : OracleComp spec α} {qb qb' : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (hle : qb ≤ qb') : IsPerIndexQueryBound oa qb' :=
  isPerIndexQueryBound_mono_aux oa hle h

private lemma update_add_eq_update_add {qb₁ qb₂ : ι → ℕ} {t : ι} (ht : 0 < qb₁ t) :
    Function.update qb₁ t (qb₁ t - 1) + qb₂ =
      Function.update (qb₁ + qb₂) t ((qb₁ + qb₂) t - 1) := by
  ext j
  by_cases hj : j = t
  · rw [hj, Pi.add_apply, Function.update_self, Pi.add_apply, Function.update_self]; omega
  · simp only [Pi.add_apply, Function.update_of_ne hj]

private lemma isPerIndexQueryBound_bind_aux (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) (qb₂ : ι → ℕ)
    (h2 : ∀ x, IsPerIndexQueryBound (ob x) qb₂) :
    ∀ {qb₁}, oa.IsPerIndexQueryBound qb₁ →
      (oa >>= ob).IsPerIndexQueryBound (qb₁ + qb₂) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro qb₁ _
    simp only [pure_bind]
    exact (h2 x).mono le_add_self
  | query_bind t mx ih =>
    intro qb₁ h1
    rw [isPerIndexQueryBound_query_bind_iff] at h1
    rw [bind_assoc, isPerIndexQueryBound_query_bind_iff]
    refine ⟨Nat.add_pos_left h1.1 _, fun u => ?_⟩
    rw [← update_add_eq_update_add h1.1]
    exact ih u (h1.2 u)

lemma isPerIndexQueryBound_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {qb₁ qb₂ : ι → ℕ}
    (h1 : IsPerIndexQueryBound oa qb₁) (h2 : ∀ x, IsPerIndexQueryBound (ob x) qb₂) :
    IsPerIndexQueryBound (oa >>= ob) (qb₁ + qb₂) :=
  isPerIndexQueryBound_bind_aux oa ob qb₂ h2 h1

@[simp]
lemma isPerIndexQueryBound_map_iff (oa : OracleComp spec α) (f : α → β) (qb : ι → ℕ) :
    IsPerIndexQueryBound (f <$> oa) qb ↔ IsPerIndexQueryBound oa qb :=
  isQueryBound_map_aux oa f _ _

/-- Forward-direction `seq` analogue of `isPerIndexQueryBound_bind`. Reduces to the bind
case via `seq_eq_bind_map` plus `isPerIndexQueryBound_map_iff` to discharge the constant
continuation. -/
lemma isPerIndexQueryBound_seq {og : OracleComp spec (α → β)} {oa : OracleComp spec α}
    {qb₁ qb₂ : ι → ℕ}
    (h1 : IsPerIndexQueryBound og qb₁) (h2 : IsPerIndexQueryBound oa qb₂) :
    IsPerIndexQueryBound (og <*> oa) (qb₁ + qb₂) := by
  rw [seq_eq_bind_map]
  exact isPerIndexQueryBound_bind h1
    (fun g => (isPerIndexQueryBound_map_iff oa g qb₂).mpr h2)

/-- Per-index analogue of `isQueryBound_iff_of_map_eq`: if `f <$> oa = ob` for any `f`, then
`IsPerIndexQueryBound` transfers between them. -/
lemma isPerIndexQueryBound_iff_of_map_eq
    {β : Type u} {oa : OracleComp spec α} {ob : OracleComp spec β} {f : α → β} {qb : ι → ℕ}
    (h : f <$> oa = ob) :
    IsPerIndexQueryBound oa qb ↔ IsPerIndexQueryBound ob qb := by
  rw [← h]; exact (isPerIndexQueryBound_map_iff oa f qb).symm

/-! ### Soundness: structural bound implies dynamic count bound -/

/-- The structural query bound `IsPerIndexQueryBound` is sound with respect to the dynamic
query count produced by `countingOracle`: if a computation satisfies a per-index query bound,
then every execution path's query count is bounded.

Proof strategy: induction on `OracleComp`, matching the structural `IsQueryBound` decomposition
with the `mem_support_simulate_queryBind_iff` characterization of counting oracle support. -/
theorem IsPerIndexQueryBound.counting_bounded {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    z.2 ≤ qb := by
  induction oa using OracleComp.inductionOn generalizing qb z with
  | pure x =>
    rw [countingOracle.mem_support_simulate_pure_iff] at hz
    subst hz
    intro i; exact Nat.zero_le _
  | query_bind t mx ih =>
    rw [isPerIndexQueryBound_query_bind_iff] at h
    rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
    obtain ⟨hne, u, hu⟩ := hz
    have h_snd : Function.update z.2 t (z.2 t - 1) ≤
        Function.update qb t (qb t - 1) := by
      change (z.1, Function.update z.2 t (z.2 t - 1)).2 ≤ _
      exact ih u (h.2 u) hu
    intro i
    by_cases hi : i = t
    · rw [hi]
      have hle := h_snd t
      simp only [Function.update_self] at hle
      have hz_pos : 0 < z.2 t := Nat.pos_of_ne_zero hne
      have hq_pos := h.1
      calc z.2 t = (z.2 t - 1) + 1 := (Nat.succ_pred_eq_of_pos hz_pos).symm
        _ ≤ (qb t - 1) + 1 := Nat.succ_le_succ hle
        _ = qb t := Nat.succ_pred_eq_of_pos hq_pos
    · have hle := h_snd i
      rw [Function.update_of_ne hi, Function.update_of_ne hi] at hle
      exact hle

/-! ### Uniform per-step transfer for `simulateQ`

If each step `impl t` makes at most one query of the matching index `t` (and none of any
other), the source's per-index bound transfers across `simulateQ`. Captures the
`cachingOracle` / `seededOracle` shape, where each step delegates to a single `query t`. -/

theorem IsPerIndexQueryBound.simulateQ_run_of_uniform_step
    {σ : Type u}
    {impl : QueryImpl spec (StateT σ (OracleComp spec))}
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep : ∀ t : spec.Domain, ∀ s : σ,
      IsPerIndexQueryBound ((impl t).run s) (Function.update 0 t 1))
    (s : σ) :
    IsPerIndexQueryBound ((simulateQ impl oa).run s) qb := by
  induction oa using OracleComp.inductionOn generalizing qb s with
  | pure x =>
      simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isPerIndexQueryBound_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind]
      have hqb_pos : 0 < qb t := h.1
      have hstep' : IsPerIndexQueryBound
          ((liftM (impl t) : StateT σ (OracleComp spec) _).run s)
          (Function.update 0 t 1) := by
        simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep t s
      have hrest : ∀ p : spec.Range t × σ,
          IsPerIndexQueryBound ((simulateQ impl (mx p.1)).run p.2)
            (Function.update qb t (qb t - 1)) :=
        fun p => ih p.1 (h.2 p.1) p.2
      have hadd : qb =
          (Function.update (0 : ι → ℕ) t 1) + Function.update qb t (qb t - 1) := by
        ext j
        by_cases hj : j = t
        · subst hj
          simp only [Pi.add_apply, Function.update_self]
          omega
        · simp [Function.update_of_ne hj]
      rw [hadd]
      simpa [StateT.run_bind] using isPerIndexQueryBound_bind hstep' hrest

/-- Stateless analogue of `IsPerIndexQueryBound.simulateQ_run_of_uniform_step`: when the
simulation target monad is `OracleComp spec` directly (no `StateT` layer), each step's
single-`t`-query bound transfers without an external state argument. -/
theorem IsPerIndexQueryBound.simulateQ_of_uniform_step
    {impl : QueryImpl spec (OracleComp spec)}
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep : ∀ t : spec.Domain,
      IsPerIndexQueryBound (impl t) (Function.update 0 t 1)) :
    IsPerIndexQueryBound (simulateQ impl oa) qb := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isPerIndexQueryBound_query_bind_iff] at h
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      have hqb_pos : 0 < qb t := h.1
      have hrest : ∀ u, IsPerIndexQueryBound (simulateQ impl (mx u))
          (Function.update qb t (qb t - 1)) :=
        fun u => ih u (h.2 u)
      have hadd : qb =
          (Function.update (0 : ι → ℕ) t 1) + Function.update qb t (qb t - 1) := by
        ext j
        by_cases hj : j = t
        · subst hj
          simp only [Pi.add_apply, Function.update_self]
          omega
        · simp [Function.update_of_ne hj]
      rw [hadd]
      exact isPerIndexQueryBound_bind (hstep t) hrest

end IsPerIndexQueryBound

/-! ### Total query bounds -/

/-- A total query bound: the computation makes at most `n` queries total
(across all oracle indices). -/
def IsTotalQueryBound (oa : OracleComp spec α) (n : ℕ) : Prop :=
  IsQueryBound oa n (fun _ b => 0 < b) (fun _ b => b - 1)

/-- `IsTotalQueryBound` is `IsRollBound` on the underlying `FreeM` with a
single-counter validity (`0 < b`) and cost (`b - 1`), independent of the
oracle index. -/
theorem isTotalQueryBound_iff_isRollBound (oa : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound oa n ↔
      PFunctor.FreeM.IsRollBound (P := spec.toPFunctor) oa n
        (fun _ b => 0 < b) (fun _ b => b - 1) :=
  Iff.rfl

lemma isTotalQueryBound_query_bind_iff {t : spec.Domain}
    {mx : spec.Range t → OracleComp spec α} {n : ℕ} :
    IsTotalQueryBound (liftM (query t) >>= mx) n ↔
      0 < n ∧ ∀ u, IsTotalQueryBound (mx u) (n - 1) :=
  Iff.rfl

lemma IsTotalQueryBound.mono {oa : OracleComp spec α} {n₁ n₂ : ℕ}
    (h : IsTotalQueryBound oa n₁) (hle : n₁ ≤ n₂) :
    IsTotalQueryBound oa n₂ := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ with
  | pure _ =>
      exact trivial
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h ⊢
      exact ⟨Nat.lt_of_lt_of_le h.1 hle,
        fun u => ih u (h.2 u) (Nat.sub_le_sub_right hle 1)⟩

/-- `IsTotalQueryBound` instantiates the generic vector-budget bind at `B := ℕ`,
`combine := (· + ·)`, with the canQuery / cost obligations both discharged by `omega`. -/
lemma isTotalQueryBound_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {n₁ n₂ : ℕ}
    (h1 : IsTotalQueryBound oa n₁) (h2 : ∀ x, IsTotalQueryBound (ob x) n₂) :
    IsTotalQueryBound (oa >>= ob) (n₁ + n₂) := by
  refine isQueryBound_bind (combine := fun a b => a + b) ?_ ?_ h1 h2
  · intros _ _ _ _ hcan; exact ⟨by simp; omega, by simp; omega⟩
  · intros _ _ _ _ hcan; exact ⟨by simp; omega, by simp; omega⟩

/-- Forward-direction `seq` analogue of `isTotalQueryBound_bind`. Reduces to the bind case
via `seq_eq_bind_map` plus the `IsTotalQueryBound`-flavoured `isQueryBound_map_iff` to
discharge the constant continuation. -/
lemma isTotalQueryBound_seq {og : OracleComp spec (α → β)} {oa : OracleComp spec α}
    {n₁ n₂ : ℕ}
    (h1 : IsTotalQueryBound og n₁) (h2 : IsTotalQueryBound oa n₂) :
    IsTotalQueryBound (og <*> oa) (n₁ + n₂) := by
  rw [seq_eq_bind_map]
  exact isTotalQueryBound_bind h1
    (fun g => (isQueryBound_map_iff oa g n₂ _ _).mpr h2)

lemma not_isTotalQueryBound_bind_query_prefix_zero
    {oa : OracleComp spec α}
    {next : α → spec.Domain}
    {ob : ∀ x, spec.Range (next x) → OracleComp spec β} :
    ¬ IsTotalQueryBound
        (oa >>= fun x => liftM (spec.query (next x)) >>= ob x)
        0 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      rw [pure_bind, isTotalQueryBound_query_bind_iff]
      simp
  | query_bind t mx ih =>
      rw [bind_assoc, isTotalQueryBound_query_bind_iff]
      simp

/-- If a computation is followed by a continuation that always starts with one query,
then a bound on the whole computation by `n + 1` yields a bound on the prefix by `n`. -/
lemma IsTotalQueryBound.of_bind_query_prefix [spec.Inhabited]
    {oa : OracleComp spec α}
    {next : α → spec.Domain}
    {ob : ∀ x, spec.Range (next x) → OracleComp spec β}
    {n : ℕ}
    (h :
      IsTotalQueryBound
        (oa >>= fun x => liftM (spec.query (next x)) >>= ob x)
        (n + 1)) :
    IsTotalQueryBound oa n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ =>
      exact trivial
  | query_bind t mx ih =>
      rw [bind_assoc, isTotalQueryBound_query_bind_iff] at h
      rw [isTotalQueryBound_query_bind_iff]
      have hn0 : n ≠ 0 := by
        intro hz
        subst hz
        exact not_isTotalQueryBound_bind_query_prefix_zero
          (oa := mx default) (next := next) (ob := ob) (h.2 default)
      have hn : 0 < n := Nat.pos_of_ne_zero hn0
      refine ⟨hn, fun u => ?_⟩
      have hn_succ : n = (n - 1) + 1 := by omega
      have hu : IsTotalQueryBound
          (mx u >>= fun x => liftM (spec.query (next x)) >>= ob x)
          ((n - 1) + 1) := by
        rw [← hn_succ]
        exact h.2 u
      exact ih u (n := n - 1) hu

theorem IsTotalQueryBound.simulateQ_run_of_step {ι' : Type u} {spec' : OracleSpec ι'}
    {σ : Type u}
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep : ∀ t : spec.Domain, ∀ s : σ, IsTotalQueryBound ((impl t).run s) 1)
    (s : σ) :
    IsTotalQueryBound ((simulateQ impl oa).run s) n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
      simpa [simulateQ_pure] using
        (show IsTotalQueryBound (pure (x, s) : OracleComp spec' (α × σ)) n from trivial)
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind]
      have hstep' : IsTotalQueryBound
          ((liftM (impl t) : StateT σ (OracleComp spec') (spec.Range t)).run s) 1 := by
        simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep t s
      have hrest : ∀ p : spec.Range t × σ,
          IsTotalQueryBound ((simulateQ impl (mx p.1)).run p.2) (n - 1) :=
        fun p => ih p.1 (h.2 p.1) p.2
      have hn : 1 + (n - 1) = n := by omega
      simpa [StateT.run_bind, hn] using isTotalQueryBound_bind hstep' hrest

/-- Stateless analogue of `IsTotalQueryBound.simulateQ_run_of_step`: when the simulation
target monad is `OracleComp spec'` directly (no `StateT` layer), every per-step bound
applies without an external state argument. Captures the `liftComp` shape, where each
source query becomes one query in the larger spec. -/
theorem IsTotalQueryBound.simulateQ_of_step {ι' : Type u} {spec' : OracleSpec ι'}
    {impl : QueryImpl spec (OracleComp spec')}
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep : ∀ t : spec.Domain, IsTotalQueryBound (impl t) 1) :
    IsTotalQueryBound (simulateQ impl oa) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x =>
      simpa [simulateQ_pure] using
        (show IsTotalQueryBound (pure x : OracleComp spec' α) n from trivial)
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      have hrest : ∀ u, IsTotalQueryBound (simulateQ impl (mx u)) (n - 1) :=
        fun u => ih u (h.2 u)
      have hn : 1 + (n - 1) = n := by have := h.1; omega
      simpa [hn] using isTotalQueryBound_bind (hstep t) hrest

namespace countingOracle

lemma add_single_mem_support_simulate_queryBind [DecidableEq ι] {t : spec.Domain}
    {oa : spec.Range t → OracleComp spec α} {u : spec.Range t}
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate (spec := spec) (oa := oa u) 0)) :
    (z.1, QueryCount.single t + z.2) ∈
      support (countingOracle.simulate (spec := spec)
        (oa := ((query t : OracleComp spec _) >>= oa)) 0) := by
  rw [countingOracle.mem_support_simulate_queryBind_iff]
  refine ⟨by simp [QueryCount.single], ⟨u, ?_⟩⟩
  convert hz using 2
  funext j
  by_cases hj : j = t
  · subst hj
    simp [QueryCount.single]
  · simp [Function.update, hj, QueryCount.single]

section CostSupport

variable [DecidableEq ι] [spec.Fintype] [spec.Inhabited] [Fintype ι]

omit [spec.Fintype] [spec.Inhabited] in
lemma exists_mem_support_simulate_of_mem_support_run_simulateQ_le_cost
    {σ : Type u} {impl : QueryImpl spec (StateT σ (OracleComp spec))}
    (cost : σ → ℕ)
    (hstep : ∀ t : spec.Domain, ∀ st : σ,
      ∀ x : spec.Range t × σ, x ∈ support ((impl t).run st) →
        cost x.2 ≤ cost st + 1)
    {oa : OracleComp spec α} {st₀ : σ} {z : α × σ}
    (hz : z ∈ support (((simulateQ impl oa).run st₀) : OracleComp spec (α × σ))) :
    ∃ qc : QueryCount ι,
      (z.1, qc) ∈ support ((countingOracle.simulate (spec := spec) (α := α) (oa := oa)
        (0 : QueryCount ι)) : OracleComp spec (α × QueryCount ι)) ∧
      cost z.2 ≤ cost st₀ + ∑ i, qc i := by
  induction oa using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      refine ⟨0, ?_, ?_⟩
      · simp [countingOracle.simulate]
      · simp
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz'⟩ := hz
      rcases ih qu.1 (st₀ := qu.2) (z := z) hz' with ⟨qc, hqc, hcost⟩
      refine ⟨QueryCount.single t + qc, ?_, ?_⟩
      · exact countingOracle.add_single_mem_support_simulate_queryBind hqc
      · have hstep' : cost qu.2 ≤ cost st₀ + 1 :=
            hstep t st₀ qu hqu
        have hsum_single : ∑ i, QueryCount.single t i = 1 := by
          rw [QueryCount.single]
          conv_lhs =>
            rw [← Finset.add_sum_erase Finset.univ (Function.update 0 t 1) (Finset.mem_univ t)]
          simp only [Function.update_self]
          have herase :
              ∑ x ∈ Finset.univ.erase t, Function.update (0 : QueryCount ι) t 1 x = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            have hjt : j ≠ t := Finset.ne_of_mem_erase hj
            change Function.update (0 : QueryCount ι) t 1 j = 0
            simp [Function.update, hjt]
          rw [herase]
        calc
          cost z.2 ≤ cost qu.2 + ∑ i, qc i := hcost
          _ ≤ (cost st₀ + 1) + ∑ i, qc i := by omega
          _ = cost st₀ + ∑ i, (QueryCount.single t + qc) i := by
              simp [Finset.sum_add_distrib, hsum_single, add_left_comm, add_comm]

end CostSupport

end countingOracle

section CountingResidual

variable [DecidableEq ι] [Fintype ι]

/-- If `oa >>= ob` is totally query-bounded by `n`, then after any support point of the
counting run of `oa`, the continuation `ob` is bounded by the residual budget. -/
theorem IsTotalQueryBound.residual_of_mem_support_counting
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n : ℕ}
    (h : IsTotalQueryBound (oa >>= ob) n)
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    IsTotalQueryBound (ob z.1) (n - ∑ i, z.2 i) := by
  induction oa using OracleComp.inductionOn generalizing n z with
  | pure x =>
      rw [countingOracle.mem_support_simulate_pure_iff] at hz
      subst z
      simpa [pure_bind] using h
  | query_bind t mx ih =>
      rw [bind_assoc, isTotalQueryBound_query_bind_iff] at h
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hz0, u, hz'⟩ := hz
      have hu :
          IsTotalQueryBound (ob z.1)
            ((n - 1) - ∑ i, (Function.update z.2 t (z.2 t - 1)) i) :=
        ih u (h.2 u) hz'
      have hsum : ∑ i, Function.update z.2 t (z.2 t - 1) i = (∑ i, z.2 i) - 1 := by
        exact sum_update_pred (Nat.pos_of_ne_zero hz0)
      rw [hsum] at hu
      have hsum_pos : 0 < ∑ i, z.2 i := by
        exact Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hz0)
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
      have hbudget : (n - 1) - ((∑ i, z.2 i) - 1) = n - ∑ i, z.2 i := by
        omega
      simpa [hbudget] using hu

/-- Any support point of the counting simulation of a totally query-bounded
computation has total query count at most the structural bound. -/
theorem IsTotalQueryBound.counting_total_le
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    (∑ i, z.2 i) ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n z with
  | pure x =>
      rw [countingOracle.mem_support_simulate_pure_iff] at hz
      subst z
      simp
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hz0, u, hz'⟩ := hz
      have hu :
          ∑ i, Function.update z.2 t (z.2 t - 1) i ≤ n - 1 :=
        ih u (h.2 u) hz'
      have hsum : ∑ i, Function.update z.2 t (z.2 t - 1) i = (∑ i, z.2 i) - 1 := by
        exact sum_update_pred (Nat.pos_of_ne_zero hz0)
      rw [hsum] at hu
      have hsum_pos : 0 < ∑ i, z.2 i := by
        exact Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hz0)
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
      omega

omit [Fintype ι] in
/-- The counting-oracle simulation of any `OracleComp` has non-empty support whenever every
oracle range is inhabited. Used by the converse direction of
`isTotalQueryBound_iff_counting_total_le`. -/
lemma countingOracle.support_simulate_nonempty [spec.Inhabited]
    (oa : OracleComp spec α) :
    (support (countingOracle.simulate oa 0)).Nonempty := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact ⟨(x, 0), by rw [countingOracle.mem_support_simulate_pure_iff]⟩
  | query_bind t mx ih =>
      obtain ⟨z, hz⟩ := ih default
      refine ⟨(z.1, QueryCount.single t + z.2), ?_⟩
      exact countingOracle.add_single_mem_support_simulate_queryBind hz

/-- Converse of `IsTotalQueryBound.counting_total_le`: a counting-oracle bound on every
support path implies the structural total query bound. Together they characterize
`IsTotalQueryBound` purely in terms of the counting-oracle support. -/
theorem isTotalQueryBound_iff_counting_total_le [spec.Inhabited]
    {oa : OracleComp spec α} {n : ℕ} :
    IsTotalQueryBound oa n ↔
      ∀ z ∈ support (countingOracle.simulate oa 0), (∑ i, z.2 i) ≤ n := by
  refine ⟨fun h _ hz => IsTotalQueryBound.counting_total_le h hz, fun h => ?_⟩
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff]
      have hsum_single : (∑ i, QueryCount.single t i) = 1 := by
        rw [QueryCount.single, Finset.sum_update_of_mem (Finset.mem_univ t)]
        simp
      have hsplit : ∀ (q : QueryCount ι),
          (∑ i, (QueryCount.single t + q) i) = 1 + ∑ i, q i := by
        intro q
        have : (∑ i, (QueryCount.single t + q) i) =
            (∑ i, QueryCount.single t i) + ∑ i, q i := by
          simp [Pi.add_apply, Finset.sum_add_distrib]
        rw [this, hsum_single]
      obtain ⟨z₀, hz₀⟩ := countingOracle.support_simulate_nonempty (mx default)
      have hbig : (z₀.1, QueryCount.single t + z₀.2) ∈
          support (countingOracle.simulate ((query t : OracleComp spec _) >>= mx) 0) :=
        countingOracle.add_single_mem_support_simulate_queryBind hz₀
      have hbound : 1 + (∑ i, z₀.2 i) ≤ n := (hsplit z₀.2) ▸ h _ hbig
      have hpos : 0 < n := by omega
      refine ⟨hpos, fun u => ?_⟩
      apply ih u
      intro z hz
      have hbig' : (z.1, QueryCount.single t + z.2) ∈
          support (countingOracle.simulate ((query t : OracleComp spec _) >>= mx) 0) :=
        countingOracle.add_single_mem_support_simulate_queryBind hz
      have hb : 1 + (∑ i, z.2 i) ≤ n := (hsplit z.2) ▸ h _ hbig'
      omega

omit [Fintype ι] [DecidableEq ι] in
/-- If a stateful simulation has support cost at most one per query step, then any support
point of the simulated prefix leaves the continuation bounded by the residual budget measured
by that cost. The cost may under-approximate the true query count, so the resulting residual
budget is correspondingly weaker but still sound. -/
theorem IsTotalQueryBound.residual_of_mem_support_run_simulateQ_le_cost
    [spec.Fintype] [spec.Inhabited] [Finite ι]
    {σ : Type u} {impl : QueryImpl spec (StateT σ (OracleComp spec))}
    (cost : σ → ℕ)
    (hstep : ∀ t : spec.Domain, ∀ st : σ,
      ∀ x : spec.Range t × σ, x ∈ support ((impl t).run st) →
        cost x.2 ≤ cost st + 1)
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n : ℕ}
    (h : IsTotalQueryBound (oa >>= ob) n)
    {st₀ : σ} {z : α × σ}
    (hz : z ∈ support ((simulateQ impl oa).run st₀)) :
    IsTotalQueryBound (ob z.1) (n - (cost z.2 - cost st₀)) := by
  letI : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := Fintype.ofFinite ι
  rcases countingOracle.exists_mem_support_simulate_of_mem_support_run_simulateQ_le_cost
      (spec := spec) (ι := ι) (impl := impl) cost hstep hz with
    ⟨qc, hqc, hcost⟩
  have hres :
      IsTotalQueryBound (ob z.1) (n - ∑ i, qc i) :=
    IsTotalQueryBound.residual_of_mem_support_counting
      (spec := spec) (ι := ι) (oa := oa) (ob := ob) (n := n) (z := (z.1, qc)) h hqc
  have hdiff : cost z.2 - cost st₀ ≤ ∑ i, qc i := by
    omega
  exact hres.mono (by omega)

end CountingResidual

/-- Per-index bound implies total bound (sum over indices). -/
theorem IsTotalQueryBound.of_perIndex [DecidableEq ι] [Fintype ι] {oa : OracleComp spec α}
    {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    IsTotalQueryBound oa (∑ i, qb i) := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ =>
      exact trivial
  | query_bind t mx ih =>
      rw [isPerIndexQueryBound_query_bind_iff] at h
      rw [isTotalQueryBound_query_bind_iff]
      have hpos : 0 < ∑ i, qb i :=
        Nat.lt_of_lt_of_le h.1 (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t))
      refine ⟨hpos, fun u => ?_⟩
      rw [← sum_update_pred h.1]
      exact ih u (h.2 u)

/-! ### Conversions and soundness for `IsQueryBoundP` -/

section IsQueryBoundPRelations

variable {p : ι → Prop} [DecidablePred p]

/-- A total query bound implies a predicate-targeted bound for every predicate `p`. -/
theorem IsTotalQueryBound.isQueryBoundP {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : IsQueryBoundP oa p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr h.1, fun u => ?_⟩
      by_cases hpt : p t
      · simp only [if_pos hpt]
        exact ih u (h.2 u)
      · simp only [if_neg hpt]
        exact (ih u (h.2 u)).mono (Nat.sub_le _ _)

/-- With the always-true predicate, `IsQueryBoundP` reduces to `IsTotalQueryBound`. -/
lemma isQueryBoundP_true_iff (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa (fun _ => True) n ↔ IsTotalQueryBound oa n := by
  refine isQueryBound_congr (fun t b => ?_) (fun t b => ?_) <;> simp

/-- The always-false predicate places no constraint. -/
@[simp]
lemma isQueryBoundP_false (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa (fun _ => False) n := by
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (fun h => h), fun u => ?_⟩
      simp only [if_neg (fun h : False => h)]
      exact ih u

/-- A per-index bound implies a predicate-targeted bound at the sum of the per-index budgets
over the indices satisfying `p`. -/
theorem IsPerIndexQueryBound.isQueryBoundP [DecidableEq ι] [Fintype ι]
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    IsQueryBoundP oa p (∑ i ∈ Finset.univ.filter p, qb i) := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isPerIndexQueryBound_query_bind_iff] at h
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨?_, fun u => ?_⟩
      · by_cases hpt : p t
        · refine Or.inr (Nat.lt_of_lt_of_le h.1 ?_)
          exact Finset.single_le_sum (f := qb) (fun _ _ => Nat.zero_le _)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hpt⟩)
        · exact Or.inl hpt
      · by_cases hpt : p t
        · rw [if_pos hpt, ← sum_filter_update_of_pred_pos hpt h.1]
          exact ih u (h.2 u)
        · rw [if_neg hpt, ← sum_filter_update_of_not_pred hpt]
          exact ih u (h.2 u)

/-- Soundness: any path of the counting-oracle simulation of a `p`-bounded computation has
sum of per-index counts over `p`-indices at most `n`. -/
theorem IsQueryBoundP.counting_bounded [DecidableEq ι] [Fintype ι]
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    (∑ i ∈ Finset.univ.filter p, z.2 i) ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n z with
  | pure x =>
      rw [countingOracle.mem_support_simulate_pure_iff] at hz
      subst hz
      simp
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hne, u, hu⟩ := hz
      have hrec :
          (∑ i ∈ Finset.univ.filter p, (Function.update z.2 t (z.2 t - 1)) i) ≤
            (if p t then n - 1 else n) :=
        ih u (h.2 u) hu
      have hz_pos : 0 < z.2 t := Nat.pos_of_ne_zero hne
      by_cases hpt : p t
      · simp only [if_pos hpt] at hrec
        rw [sum_filter_update_of_pred_pos hpt hz_pos] at hrec
        have hp_pos : 0 < ∑ i ∈ Finset.univ.filter p, z.2 i :=
          Nat.lt_of_lt_of_le hz_pos
            (Finset.single_le_sum (f := z.2) (fun _ _ => Nat.zero_le _)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hpt⟩))
        have hn_pos : 0 < n := h.1.resolve_left (fun hnp => hnp hpt)
        have hshift : (∑ i ∈ Finset.univ.filter p, z.2 i) - 1 + 1 ≤ (n - 1) + 1 :=
          Nat.add_le_add_right hrec 1
        rwa [Nat.sub_add_cancel hp_pos, Nat.sub_add_cancel hn_pos] at hshift
      · simp only [if_neg hpt] at hrec
        rw [sum_filter_update_of_not_pred hpt] at hrec
        exact hrec

/-- Residual bound via the counting oracle: after any partial counting-simulation of `oa`, the
continuation `ob` is `p`-bounded by `n` minus the filtered count so far. -/
theorem IsQueryBoundP.residual_of_mem_support_counting [DecidableEq ι] [Fintype ι]
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n : ℕ}
    (h : IsQueryBoundP (oa >>= ob) p n)
    {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    IsQueryBoundP (ob z.1) p (n - ∑ i ∈ Finset.univ.filter p, z.2 i) := by
  induction oa using OracleComp.inductionOn generalizing n z with
  | pure x =>
      rw [countingOracle.mem_support_simulate_pure_iff] at hz
      subst z
      simpa [pure_bind] using h
  | query_bind t mx ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
      rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hne, u, hu⟩ := hz
      have hz_pos : 0 < z.2 t := Nat.pos_of_ne_zero hne
      have hrec :
          IsQueryBoundP (ob z.1) p
              ((if p t then n - 1 else n) -
                ∑ i ∈ Finset.univ.filter p, (Function.update z.2 t (z.2 t - 1)) i) :=
        ih u (h.2 u) hu
      by_cases hpt : p t
      · simp only [if_pos hpt] at hrec
        rw [sum_filter_update_of_pred_pos hpt hz_pos] at hrec
        have hp_pos : 0 < ∑ i ∈ Finset.univ.filter p, z.2 i :=
          Nat.lt_of_lt_of_le hz_pos
            (Finset.single_le_sum (f := z.2) (fun _ _ => Nat.zero_le _)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hpt⟩))
        refine hrec.mono ?_
        rw [Nat.sub_sub, Nat.add_sub_of_le hp_pos]
      · simp only [if_neg hpt] at hrec
        rw [sum_filter_update_of_not_pred hpt] at hrec
        exact hrec

/-- Predicate-targeted analogue of `isTotalQueryBound_iff_counting_total_le`: a
counting-oracle filtered-sum bound characterizes the structural `IsQueryBoundP` bound. -/
theorem isQueryBoundP_iff_counting_filter_le
    [DecidableEq ι] [Fintype ι] [spec.Inhabited]
    {oa : OracleComp spec α} {n : ℕ} :
    IsQueryBoundP oa p n ↔
      ∀ z ∈ support (countingOracle.simulate oa 0),
        (∑ i ∈ Finset.univ.filter p, z.2 i) ≤ n := by
  refine ⟨fun h _ hz => IsQueryBoundP.counting_bounded h hz, fun h => ?_⟩
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff]
      have hsplit : ∀ (q : QueryCount ι),
          (∑ i ∈ Finset.univ.filter p, (QueryCount.single t + q) i) =
          (∑ i ∈ Finset.univ.filter p, QueryCount.single t i) +
          (∑ i ∈ Finset.univ.filter p, q i) := by
        intro q
        simp [Pi.add_apply, Finset.sum_add_distrib]
      refine ⟨?_, fun u => ?_⟩
      · by_cases hpt : p t
        · refine Or.inr ?_
          obtain ⟨z₀, hz₀⟩ := countingOracle.support_simulate_nonempty (mx default)
          have hbig : (z₀.1, QueryCount.single t + z₀.2) ∈
              support (countingOracle.simulate ((query t : OracleComp spec _) >>= mx) 0) :=
            countingOracle.add_single_mem_support_simulate_queryBind hz₀
          have hsum_single : (∑ i ∈ Finset.univ.filter p, QueryCount.single t i) = 1 := by
            rw [QueryCount.single,
              Finset.sum_update_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hpt⟩)]
            simp
          have hbound := h _ hbig
          rw [hsplit, hsum_single] at hbound
          omega
        · exact Or.inl hpt
      · apply ih u
        intro z hz
        have hbig' : (z.1, QueryCount.single t + z.2) ∈
            support (countingOracle.simulate ((query t : OracleComp spec _) >>= mx) 0) :=
          countingOracle.add_single_mem_support_simulate_queryBind hz
        have hbound := h _ hbig'
        rw [hsplit] at hbound
        by_cases hpt : p t
        · simp only [if_pos hpt]
          have hsum_single : (∑ i ∈ Finset.univ.filter p, QueryCount.single t i) = 1 := by
            rw [QueryCount.single,
              Finset.sum_update_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hpt⟩)]
            simp
          rw [hsum_single] at hbound
          omega
        · simp only [if_neg hpt]
          have hsum_single : (∑ i ∈ Finset.univ.filter p, QueryCount.single t i) = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            have hjp : p j := (Finset.mem_filter.mp hj).2
            have hjt : j ≠ t := fun he => hpt (he ▸ hjp)
            simp [QueryCount.single, Function.update_of_ne hjt]
          rw [hsum_single, zero_add] at hbound
          exact hbound

end IsQueryBoundPRelations

/-- Transfer a predicate-targeted query bound through `simulateQ` into a stateful target
semantics, provided each simulated source query step is itself `q`-bounded (by `1` on
`p`-indices, by `0` on `¬ p`-indices). -/
theorem IsQueryBoundP.simulateQ_run_of_step {ι' : Type u} {spec' : OracleSpec ι'} {σ : Type u}
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → ∀ s, IsQueryBoundP ((impl t).run s) q 1)
    (hstep_np : ∀ t, ¬ p t → ∀ s, IsQueryBoundP ((impl t).run s) q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) q n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind]
      have hlift :
          IsQueryBoundP
            ((liftM (impl t) : StateT σ (OracleComp spec') (spec.Range t)).run s) q
            (if p t then 1 else 0) := by
        by_cases hpt : p t
        · simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift, if_pos hpt] using
            hstep_p t hpt s
        · simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift, if_neg hpt] using
            hstep_np t hpt s
      have hrest : ∀ pu : spec.Range t × σ,
          pu ∈ support ((liftM (impl t) :
              StateT σ (OracleComp spec') (spec.Range t)).run s) →
            IsQueryBoundP ((simulateQ impl (mx pu.1)).run pu.2) q
              (if p t then n - 1 else n) := by
        intro pu _
        exact ih pu.1 (h.2 pu.1) pu.2
      have hbound : (if p t then 1 else 0) + (if p t then n - 1 else n) = n := by
        by_cases hpt : p t
        · simp only [if_pos hpt]
          rcases h.1 with hnp | hn
          · exact absurd hpt hnp
          · omega
        · simp only [if_neg hpt]; omega
      have := isQueryBoundP_bind hlift hrest
      simpa [hbound] using this

/-- Stateless analogue of `IsQueryBoundP.simulateQ_run_of_step`: when the simulation target
monad is `OracleComp spec'` directly (no `StateT` layer), the per-step bounds apply without
an external state argument. Captures the `liftComp` shape, where each `p`-step becomes one
`q`-query and each `¬ p`-step is `q`-free. -/
theorem IsQueryBoundP.simulateQ_of_step {ι' : Type u} {spec' : OracleSpec ι'}
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')}
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → IsQueryBoundP (impl t) q 1)
    (hstep_np : ∀ t, ¬ p t → IsQueryBoundP (impl t) q 0) :
    IsQueryBoundP (simulateQ impl oa) q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      have hlift : IsQueryBoundP (impl t) q (if p t then 1 else 0) := by
        by_cases hpt : p t
        · simpa [if_pos hpt] using hstep_p t hpt
        · simpa [if_neg hpt] using hstep_np t hpt
      have hrest : ∀ u, IsQueryBoundP (simulateQ impl (mx u)) q (if p t then n - 1 else n) :=
        fun u => ih u (h.2 u)
      have hbound : (if p t then 1 else 0) + (if p t then n - 1 else n) = n := by
        by_cases hpt : p t
        · simp only [if_pos hpt]
          rcases h.1 with hnp | hn
          · exact absurd hpt hnp
          · omega
        · simp only [if_neg hpt]; omega
      simpa [hbound] using isQueryBoundP_bind hlift (fun u _ => hrest u)

/-- Transfer a predicate-targeted bound through `simulateQ` with a sum-of-implementations
`impl₁ + impl₂` on a sum source spec `spec₁ + spec₂`. The source predicate `p` is split into
its `.inl` and `.inr` branches, with separate step hypotheses for each impl on its own
sub-predicate. -/
theorem IsQueryBoundP.simulateQ_run_add_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} {σ : Type u}
    {p : ι₁ ⊕ ι₂ → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p₁ : ∀ t, p (.inl t) → ∀ s, IsQueryBoundP ((impl₁ t).run s) q 1)
    (hstep_np₁ : ∀ t, ¬ p (.inl t) → ∀ s, IsQueryBoundP ((impl₁ t).run s) q 0)
    (hstep_p₂ : ∀ t, p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 1)
    (hstep_np₂ : ∀ t, ¬ p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ (impl₁ + impl₂) oa).run s) q n := by
  refine IsQueryBoundP.simulateQ_run_of_step h ?_ ?_ s
  · rintro (t | t) hp s
    · exact hstep_p₁ t hp s
    · exact hstep_p₂ t hp s
  · rintro (t | t) hnp s
    · exact hstep_np₁ t hnp s
    · exact hstep_np₂ t hnp s

/-- Specialization of `IsQueryBoundP.simulateQ_run_add_of_step` when the source predicate
is vacuously false on `.inr _` queries: only `impl₁` interacts with the predicate, and
`impl₂` only needs a uniform 0-bound step. -/
theorem IsQueryBoundP.simulateQ_run_add_inl_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} {σ : Type u}
    {p : ι₁ ⊕ ι₂ → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (hp_inr : ∀ t, ¬ p (.inr t))
    (h : IsQueryBoundP oa p n)
    (hstep_p₁ : ∀ t, p (.inl t) → ∀ s, IsQueryBoundP ((impl₁ t).run s) q 1)
    (hstep_np₁ : ∀ t, ¬ p (.inl t) → ∀ s, IsQueryBoundP ((impl₁ t).run s) q 0)
    (hstep_right : ∀ t s, IsQueryBoundP ((impl₂ t).run s) q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ (impl₁ + impl₂) oa).run s) q n :=
  IsQueryBoundP.simulateQ_run_add_of_step h hstep_p₁ hstep_np₁
    (fun t hp _ => absurd hp (hp_inr t))
    (fun t _ s => hstep_right t s) s

/-- Specialization of `IsQueryBoundP.simulateQ_run_add_of_step` when the source predicate
is vacuously false on `.inl _` queries: only `impl₂` interacts with the predicate, and
`impl₁` only needs a uniform 0-bound step. -/
theorem IsQueryBoundP.simulateQ_run_add_inr_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} {σ : Type u}
    {p : ι₁ ⊕ ι₂ → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (hp_inl : ∀ t, ¬ p (.inl t))
    (h : IsQueryBoundP oa p n)
    (hstep_left : ∀ t s, IsQueryBoundP ((impl₁ t).run s) q 0)
    (hstep_p₂ : ∀ t, p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 1)
    (hstep_np₂ : ∀ t, ¬ p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ (impl₁ + impl₂) oa).run s) q n :=
  IsQueryBoundP.simulateQ_run_add_of_step h
    (fun t hp _ => absurd hp (hp_inl t))
    (fun t _ s => hstep_left t s)
    hstep_p₂ hstep_np₂ s

/-! ### Total-bound sum-handler transfer

`IsTotalQueryBound` lifts across `simulateQ (impl₁ + impl₂) oa` whenever each underlying
handler makes at most one query per step. The signature mirrors
`IsQueryBoundP.simulateQ_run_add_of_step` without the predicate machinery: every step on
either side counts toward the same uniform budget. -/

theorem IsTotalQueryBound.simulateQ_run_add_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ, IsTotalQueryBound ((impl₁ t).run s) 1)
    (hstep₂ : ∀ t : ι₂, ∀ s : σ, IsTotalQueryBound ((impl₂ t).run s) 1)
    (s : σ) :
    IsTotalQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) n := by
  refine IsTotalQueryBound.simulateQ_run_of_step h ?_ s
  rintro (t | t) s'
  · exact hstep₁ t s'
  · exact hstep₂ t s'

/-- Specialization of `IsTotalQueryBound.simulateQ_run_add_of_step` to a left-only
interaction: `impl₂` only needs a uniform 0-bound step. -/
theorem IsTotalQueryBound.simulateQ_run_add_inl_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ, IsTotalQueryBound ((impl₁ t).run s) 1)
    (hstep₂ : ∀ t : ι₂, ∀ s : σ, IsTotalQueryBound ((impl₂ t).run s) 0)
    (s : σ) :
    IsTotalQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) n :=
  IsTotalQueryBound.simulateQ_run_add_of_step h hstep₁
    (fun t s' => (hstep₂ t s').mono (Nat.zero_le _)) s

/-- Specialization of `IsTotalQueryBound.simulateQ_run_add_of_step` to a right-only
interaction: `impl₁` only needs a uniform 0-bound step. -/
theorem IsTotalQueryBound.simulateQ_run_add_inr_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ, IsTotalQueryBound ((impl₁ t).run s) 0)
    (hstep₂ : ∀ t : ι₂, ∀ s : σ, IsTotalQueryBound ((impl₂ t).run s) 1)
    (s : σ) :
    IsTotalQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) n :=
  IsTotalQueryBound.simulateQ_run_add_of_step h
    (fun t s' => (hstep₁ t s').mono (Nat.zero_le _))
    hstep₂ s

/-! ### Per-index sum-handler transfer

The per-index analogue of `IsTotalQueryBound.simulateQ_run_add_of_step`: each side's step
is required to make at most one query of its corresponding sum-tagged index in the result
spec, mirroring the single-spec `simulateQ_run_of_uniform_step`. -/

theorem IsPerIndexQueryBound.simulateQ_run_add_of_uniform_step
    {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {oa : OracleComp (spec₁ + spec₂) α} {qb : ι₁ ⊕ ι₂ → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ,
      IsPerIndexQueryBound ((impl₁ t).run s) (Function.update 0 (Sum.inl t) 1))
    (hstep₂ : ∀ t : ι₂, ∀ s : σ,
      IsPerIndexQueryBound ((impl₂ t).run s) (Function.update 0 (Sum.inr t) 1))
    (s : σ) :
    IsPerIndexQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) qb := by
  refine IsPerIndexQueryBound.simulateQ_run_of_uniform_step h ?_ s
  rintro (t | t) s'
  · exact hstep₁ t s'
  · exact hstep₂ t s'

/-- Specialization of `IsPerIndexQueryBound.simulateQ_run_add_of_uniform_step` to a left-only
interaction: `impl₂` only needs a uniform 0-step. -/
theorem IsPerIndexQueryBound.simulateQ_run_add_inl_of_uniform_step
    {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {oa : OracleComp (spec₁ + spec₂) α} {qb : ι₁ ⊕ ι₂ → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ,
      IsPerIndexQueryBound ((impl₁ t).run s) (Function.update 0 (Sum.inl t) 1))
    (hstep₂ : ∀ t : ι₂, ∀ s : σ, IsPerIndexQueryBound ((impl₂ t).run s) 0)
    (s : σ) :
    IsPerIndexQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) qb :=
  IsPerIndexQueryBound.simulateQ_run_add_of_uniform_step h hstep₁
    (fun t s' => (hstep₂ t s').mono (fun _ => Nat.zero_le _)) s

/-- Specialization of `IsPerIndexQueryBound.simulateQ_run_add_of_uniform_step` to a right-only
interaction: `impl₁` only needs a uniform 0-step. -/
theorem IsPerIndexQueryBound.simulateQ_run_add_inr_of_uniform_step
    {ι₁ ι₂ : Type u} [DecidableEq ι₁] [DecidableEq ι₂]
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ : Type u}
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp (spec₁ + spec₂)))}
    {oa : OracleComp (spec₁ + spec₂) α} {qb : ι₁ ⊕ ι₂ → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep₁ : ∀ t : ι₁, ∀ s : σ, IsPerIndexQueryBound ((impl₁ t).run s) 0)
    (hstep₂ : ∀ t : ι₂, ∀ s : σ,
      IsPerIndexQueryBound ((impl₂ t).run s) (Function.update 0 (Sum.inr t) 1))
    (s : σ) :
    IsPerIndexQueryBound ((simulateQ (impl₁ + impl₂) oa).run s) qb :=
  IsPerIndexQueryBound.simulateQ_run_add_of_uniform_step h
    (fun t s' => (hstep₁ t s').mono (fun _ => Nat.zero_le _))
    hstep₂ s

/-! ## Biconditional transfer under query-count-preserving simulators

`loggingOracle`, `countingOracle`, and the `withTrace*` / `withCost` / `withCounting`
combinators interpret each source query as exactly one underlying query, threading writer
bookkeeping that the underlying simulation does not see. Bounds transfer *biconditionally*
via the `fst_map_run_*` projection identities and `isXQueryBound_iff_of_map_eq`.

Cache-hit / seed-hit handlers (`cachingOracle`, `randomOracle`, `seededOracle`) discard
queries and so admit only the forward direction — use `simulateQ_run_of_step` for those. -/

theorem isTotalQueryBound_run_simulateQ_countingOracle_iff
    {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ countingOracle oa).run) n ↔
    IsTotalQueryBound oa n :=
  isQueryBound_iff_of_map_eq (countingOracle.fst_map_run_simulateQ oa) _ _

theorem isQueryBoundP_run_simulateQ_countingOracle_iff
    {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp spec α) (p : ι → Prop) [DecidablePred p] (n : ℕ) :
    IsQueryBoundP ((simulateQ countingOracle oa).run) p n ↔
    IsQueryBoundP oa p n :=
  isQueryBoundP_iff_of_map_eq (p := p) (countingOracle.fst_map_run_simulateQ oa)

theorem isTotalQueryBound_run_simulateQ_withTraceBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withTraceBefore traceFn) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTraceBefore so traceFn mx) _ _

theorem isQueryBoundP_run_simulateQ_withTraceBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withTraceBefore traceFn) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withTraceBefore so traceFn mx)

theorem isTotalQueryBound_run_simulateQ_withTraceAppend_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withTraceAppend traceFn) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTraceAppend so traceFn mx) _ _

theorem isQueryBoundP_run_simulateQ_withTraceAppend_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withTraceAppend traceFn) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withTraceAppend so traceFn mx)

theorem isTotalQueryBound_run_simulateQ_withTrace_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withTrace traceFn) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTrace so traceFn mx) _ _

theorem isQueryBoundP_run_simulateQ_withTrace_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withTrace traceFn) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withTrace so traceFn mx)

theorem isTotalQueryBound_run_simulateQ_withTraceAppendBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withTraceAppendBefore traceFn) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq
    (QueryImpl.fst_map_run_withTraceAppendBefore so traceFn mx) _ _

theorem isQueryBoundP_run_simulateQ_withTraceAppendBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withTraceAppendBefore traceFn) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q)
    (QueryImpl.fst_map_run_withTraceAppendBefore so traceFn mx)

theorem isTotalQueryBound_run_simulateQ_withCost_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (costFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withCost costFn) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withCost so costFn mx) _ _

theorem isQueryBoundP_run_simulateQ_withCost_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (costFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withCost costFn) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withCost so costFn mx)

theorem isTotalQueryBound_run_simulateQ_withCounting_iff
    {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    {α : Type u} (mx : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ (so.withCounting) mx).run) n ↔
    IsTotalQueryBound (simulateQ so mx) n :=
  isQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withCounting so mx) _ _

theorem isQueryBoundP_run_simulateQ_withCounting_iff
    {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
    {ι' : Type u} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    {α : Type u} (mx : OracleComp spec α)
    (q : ι' → Prop) [DecidablePred q] (n : ℕ) :
    IsQueryBoundP ((simulateQ (so.withCounting) mx).run) q n ↔
    IsQueryBoundP (simulateQ so mx) q n :=
  isQueryBoundP_iff_of_map_eq (p := q) (QueryImpl.fst_map_run_withCounting so mx)

/-! ### Per-index analogues -/

theorem isPerIndexQueryBound_run_simulateQ_countingOracle_iff
    {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp spec α) (qb : ι → ℕ) :
    IsPerIndexQueryBound ((simulateQ countingOracle oa).run) qb ↔
    IsPerIndexQueryBound oa qb :=
  isPerIndexQueryBound_iff_of_map_eq (countingOracle.fst_map_run_simulateQ oa)

theorem isPerIndexQueryBound_run_simulateQ_withTraceBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withTraceBefore traceFn) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTraceBefore so traceFn mx)

theorem isPerIndexQueryBound_run_simulateQ_withTrace_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withTrace traceFn) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTrace so traceFn mx)

theorem isPerIndexQueryBound_run_simulateQ_withTraceAppendBefore_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec')) (traceFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withTraceAppendBefore traceFn) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq
    (QueryImpl.fst_map_run_withTraceAppendBefore so traceFn mx)

theorem isPerIndexQueryBound_run_simulateQ_withTraceAppend_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withTraceAppend traceFn) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withTraceAppend so traceFn mx)

theorem isPerIndexQueryBound_run_simulateQ_withCost_iff
    {ι : Type u} {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    {ω : Type u} [Monoid ω]
    (so : QueryImpl spec (OracleComp spec')) (costFn : spec.Domain → ω)
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withCost costFn) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withCost so costFn mx)

theorem isPerIndexQueryBound_run_simulateQ_withCounting_iff
    {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
    {ι' : Type u} [DecidableEq ι'] {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    {α : Type u} (mx : OracleComp spec α) (qb : ι' → ℕ) :
    IsPerIndexQueryBound ((simulateQ (so.withCounting) mx).run) qb ↔
    IsPerIndexQueryBound (simulateQ so mx) qb :=
  isPerIndexQueryBound_iff_of_map_eq (QueryImpl.fst_map_run_withCounting so mx)

/-- Worst-case per-index query bound as a function of input size:
for all inputs `x` with `size x ≤ n`, the computation `f x` makes at most `bound n i`
queries to oracle `i`.

Currently unused outside this file; retained as scaffolding for future asymptotic analyses. -/
def QueryUpperBound [DecidableEq ι] (f : α → OracleComp spec β) (size : α → ℕ)
    (bound : ℕ → ι → ℕ) : Prop :=
  ∀ n x, size x ≤ n → IsPerIndexQueryBound (f x) (bound n)

/-- Total query upper bound: there exists a constant `k` such that for all inputs `x`
with `size x ≤ n`, the computation `f x` makes at most `k * bound n` total queries.
Uses the structural `IsQueryBound` to avoid dependence on oracle responses.

Currently unused outside this file; retained as scaffolding for future asymptotic analyses. -/
def TotalQueryUpperBound (f : α → OracleComp spec β) (size : α → ℕ) (bound : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, ∀ n x, size x ≤ n → IsQueryBound (f x) (k * bound n)
    (fun _ b => 0 < b) (fun _ b => b - 1)

/-- `PolyQueryUpperBound` says the per-index query count is polynomially bounded
in the input size. This is a non-parameterized version of `PolyQueries`.

Currently unused outside this file; retained as scaffolding for future asymptotic analyses. -/
def PolyQueryUpperBound [DecidableEq ι] (f : α → OracleComp spec β) (size : α → ℕ) : Prop :=
  ∃ qb : ι → Polynomial ℕ, QueryUpperBound f size (fun n i => (qb i).eval n)

/-- If `f` has a `QueryUpperBound`, then each `f x` satisfies `IsPerIndexQueryBound`. -/
lemma QueryUpperBound.apply [DecidableEq ι]
    {f : α → OracleComp spec β} {size : α → ℕ} {bound : ℕ → ι → ℕ}
    (h : QueryUpperBound f size bound) (x : α) :
    IsPerIndexQueryBound (f x) (bound (size x)) :=
  h (size x) x le_rfl

/-- If `oa` is a computation indexed by a security parameter, then `PolyQueries oa`
means that for each oracle index there is a polynomial function `qb` of the security parameter,
such that the number of queries to that oracle is bounded by the corresponding polynomial.

Currently used only in `CostModel.lean`; retained as scaffolding for future asymptotic analyses. -/
structure PolyQueries {ι : Type} [DecidableEq ι] {spec : ℕ → OracleSpec ι}
    {α β : ℕ → Type} (oa : (n : ℕ) → α n → OracleComp (spec n) (β n)) where
  /-- `qb i` is a polynomial bound on the queries made to oracle `i`. -/
  qb : ι → Polynomial ℕ
  /-- The bound is actually a bound on the number of queries made. -/
  qb_isQueryBound (n : ℕ) (x : α n) :
    IsPerIndexQueryBound (oa n x) (fun i => (qb i).eval n)

end OracleComp
