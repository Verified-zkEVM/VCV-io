/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Alexander Hicks
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import PolyFun.PFunctor.Bound
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.QueryTracking.CountingOracle
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Structural query bounds
-/

public section

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
@[expose]
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
    canQuery t b := by
  rw [isQueryBound_iff_isRollBound, OracleComp.liftM_def]
  change PFunctor.FreeM.IsRollBound
    ((id : spec.Range t → spec.Range t) <$> PFunctor.FreeM.lift (P := spec.toPFunctor) t)
    b canQuery cost ↔ canQuery t b
  rw [PFunctor.FreeM.isRollBound_map_iff, PFunctor.FreeM.isRollBound_lift_iff]

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
      simpa [hcombine t budget h.1] using
        hbind hstep' (fun p => ih p.1 (h.2 p.1) p.2)

end IsQueryBound

section IsQueryBoundP

/-- Predicate-targeted query bound: a middle ground between `IsQueryBound` and
`IsPerIndexQueryBound` / `IsTotalQueryBound`. `IsQueryBoundP oa p n` says that `oa` makes at most
`n` queries to oracle indices satisfying `p`, with no constraint on the number of queries to
indices where `p` fails.

This is built on the generic `IsQueryBound` with the validity check `¬ p t ∨ 0 < qb` and the cost
function that decrements the budget only on `p`-indices. At `n = 0` it forbids all `p`-queries;
`isQueryBoundP_zero_iff` identifies this with `AllQueriesSatisfy` on the complementary predicate. -/
@[expose]
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
  refine OracleComp.IsQueryBound.proj proj (fun t b' hcan => ?_) h_cost h
  by_cases hpt : p t <;> simp [hpt, h_can t b' hcan]

theorem IsQueryBoundP.mono {oa : OracleComp spec α} {n m : ℕ}
    (h : IsQueryBoundP oa p n) (hnm : n ≤ m) : IsQueryBoundP oa p m := by
  induction oa using OracleComp.inductionOn generalizing n m with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨h.1.imp id (fun hn => Nat.lt_of_lt_of_le hn hnm), fun u => ?_⟩
      exact ih u (h.2 u) (by split <;> omega)

/-- `oa >>= ob` is `p`-bounded by `n + m` when `oa` is `p`-bounded by `n` and every reachable
continuation `ob x` is `p`-bounded by `m`. -/
lemma isQueryBoundP_bind
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n m : ℕ}
    (h : IsQueryBoundP oa p n) (h' : ∀ x ∈ support oa, IsQueryBoundP (ob x) p m) :
    IsQueryBoundP (oa >>= ob) p (n + m) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x =>
      simp only [monad_norm]
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
      grind

/-- Transfer a predicate-targeted query bound through a `StateT` simulation
whose handler step consumes at most one target-side predicate query exactly when
the source query satisfies the source predicate.

This is the scalar `IsQueryBoundP` analogue of the more general vector-budget
`IsQueryBound.simulateQ_run_of_step`. It is useful for logging and forwarding
handlers whose state updates do not make additional oracle queries. -/
theorem IsQueryBoundP.simulateQ_run_StateT_of_step
    {ι' : Type u} {spec' : OracleSpec ι'} {σ : Type u}
    {p : ι → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep : ∀ t s, IsQueryBoundP ((impl t).run s) q (if p t then 1 else 0))
    (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) q n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
      simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind]
      have hrest : ∀ x ∈ support ((impl t).run s),
          IsQueryBoundP ((simulateQ impl (mx x.1)).run x.2) q
            (if p t then n - 1 else n) := by
        intro x hx
        exact ih x.1 (h.2 x.1) x.2
      have hbind := isQueryBoundP_bind (hstep t s) hrest
      refine hbind.mono ?_
      grind

/-- Predicate-extensionality: replacing `p` with an equivalent predicate does not change the
bound. -/
lemma isQueryBoundP_congr_pred {oa : OracleComp spec α} {p p' : ι → Prop}
    [DecidablePred p] [DecidablePred p'] {n : ℕ}
    (hpp : ∀ t, p t ↔ p' t) :
    IsQueryBoundP oa p n ↔ IsQueryBoundP oa p' n := by
  refine isQueryBound_congr (fun t b => ?_) (fun t b => ?_) <;> simp [hpp]

/-- Antitone in the predicate: if every `p`-index is also a `p'`-index, then a `p'`-targeted
bound is a `p`-targeted bound at the same budget. The `p`-indices form a sub-collection of the
`p'`-indices, so any path makes at most as many `p`-queries as `p'`-queries. -/
lemma IsQueryBoundP.of_imp {oa : OracleComp spec α} {p p' : ι → Prop}
    [DecidablePred p] [DecidablePred p'] {n : ℕ}
    (himp : ∀ t, p t → p' t) (h : IsQueryBoundP oa p' n) :
    IsQueryBoundP oa p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨?_, fun u => ?_⟩
      · by_cases hpt : p t
        · exact Or.inr (h.1.resolve_left (not_not.mpr (himp t hpt)))
        · exact Or.inl hpt
      · refine (ih u (h.2 u)).mono ?_
        grind

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

/-! ### Predicate-only bounds

`AllQueriesSatisfy oa P` is `IsQueryBound` at the unit budget: it restricts which oracle indices
`oa` may query without counting queries at all.  `allQueriesSatisfy_def` recovers the generic
form, and `isQueryBoundP_zero_iff` identifies it with `IsQueryBoundP` at budget zero, so the
predicate-targeted API applies to it as well.  The structural laws below restate the generic
`@[simp]` lemmas at the new head symbol; `allQueriesSatisfy_bind` and `allQueriesSatisfy_ofFnM`
additionally discharge the `combine` side conditions of `isQueryBound_bind`, which the unit
budget makes trivial. -/

section AllQueriesSatisfy

/-- Predicate-only query bound: every query `oa` can make, on every response path, is to an
oracle index satisfying `P`.

This is `IsQueryBound` with the unit budget `()`, the validity check `fun t _ => P t`, and the
trivial cost, so nothing is counted and only the reachable oracle indices are constrained.  It
is the `DecidablePred`-free presentation of `IsQueryBoundP oa (fun t => ¬ P t) 0`
(`isQueryBoundP_zero_iff`), through which `IsQueryBoundP.mono`, `IsQueryBoundP.of_imp`,
`isQueryBoundP_bind`, and the predicate-targeted simulation transfers apply to it. -/
def AllQueriesSatisfy (oa : OracleComp spec α) (P : ι → Prop) : Prop :=
  IsQueryBound oa () (fun t _ => P t) (fun _ _ => ())

/-- `AllQueriesSatisfy` is the unit-budget `IsQueryBound`: this is the equation through which the
generic laws (`isQueryBound_map_iff`, `isQueryBound_iff_of_map_eq`,
`IsQueryBound.simulateQ_run_of_step`) reach the predicate-only form. -/
@[grind =]
lemma allQueriesSatisfy_def (oa : OracleComp spec α) (P : ι → Prop) :
    AllQueriesSatisfy oa P ↔ IsQueryBound oa () (fun t _ => P t) (fun _ _ => ()) :=
  Iff.rfl

/-- The predicate-only bound is the predicate-targeted bound at budget zero on the complementary
predicate: spending no budget on `¬ P`-queries is exactly querying only `P`-indices.  This is the
bridge that makes the `IsQueryBoundP` API available to `AllQueriesSatisfy`. -/
theorem isQueryBoundP_zero_iff (oa : OracleComp spec α) (P : ι → Prop) [DecidablePred P] :
    IsQueryBoundP oa (fun t => ¬ P t) 0 ↔ AllQueriesSatisfy oa P := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [AllQueriesSatisfy]
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff, allQueriesSatisfy_def, isQueryBound_query_bind_iff]
      simp only [not_not, Nat.lt_irrefl, or_false]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, fun u => (ih u).1 (by simpa using h₂ u)⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, fun u => by simpa using (ih u).2 (h₂ u)⟩

@[simp]
lemma allQueriesSatisfy_pure (x : α) (P : ι → Prop) :
    AllQueriesSatisfy (pure x : OracleComp spec α) P := trivial

@[simp]
lemma allQueriesSatisfy_query_iff (t : ι) (P : ι → Prop) :
    AllQueriesSatisfy (liftM (spec.query t) : OracleComp spec _) P ↔ P t :=
  isQueryBound_query_iff t () _ _

@[simp]
lemma allQueriesSatisfy_query_bind_iff (t : ι) (mx : spec t → OracleComp spec α)
    (P : ι → Prop) :
    AllQueriesSatisfy (liftM (spec.query t) >>= mx) P ↔
      P t ∧ ∀ u, AllQueriesSatisfy (mx u) P :=
  Iff.rfl

/-- A predicate-only bound composes through monadic sequencing.  The unit budget discharges both
side conditions of `isQueryBound_bind`. -/
lemma allQueriesSatisfy_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {P : ι → Prop} (h₁ : AllQueriesSatisfy oa P) (h₂ : ∀ x, AllQueriesSatisfy (ob x) P) :
    AllQueriesSatisfy (oa >>= ob) P :=
  isQueryBound_bind (fun _ _ => ()) (fun _ _ _ _ h => ⟨h, h⟩) (fun _ _ _ _ _ => ⟨rfl, rfl⟩) h₁ h₂

/-- A predicate-only bound passes through `Vector.ofFnM` when every component has it. -/
lemma allQueriesSatisfy_ofFnM {n : ℕ} (f : Fin n → OracleComp spec α) {P : ι → Prop}
    (h : ∀ i, AllQueriesSatisfy (f i) P) :
    AllQueriesSatisfy (Vector.ofFnM f) P := by
  induction n with
  | zero =>
      rw [Vector.ofFnM_zero]
      exact allQueriesSatisfy_pure _ _
  | succ n ih =>
      rw [Vector.ofFnM_succ]
      exact allQueriesSatisfy_bind (ih (fun i => f i.castSucc) (fun i => h i.castSucc))
        fun _ => allQueriesSatisfy_bind (h (Fin.last n)) fun _ => allQueriesSatisfy_pure _ _

end AllQueriesSatisfy

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

lemma isPerIndexQueryBound_pure (x : α) (qb : ι → ℕ) :
    IsPerIndexQueryBound (pure x : OracleComp spec α) qb := trivial

lemma isPerIndexQueryBound_query_bind_iff (t : ι) (mx : spec t → OracleComp spec α)
    (qb : ι → ℕ) :
    IsPerIndexQueryBound (liftM (spec.query t) >>= mx) qb ↔
      0 < qb t ∧ ∀ u, IsPerIndexQueryBound (mx u) (Function.update qb t (qb t - 1)) :=
  Iff.rfl

lemma isPerIndexQueryBound_query_iff (t : ι) (qb : ι → ℕ) :
    IsPerIndexQueryBound (liftM (spec.query t) : OracleComp spec _) qb ↔
    0 < qb t := by
  simp [IsPerIndexQueryBound]

private lemma update_le_update {qb qb' : ι → ℕ} {t : ι} (hle : qb ≤ qb') :
    Function.update qb t (qb t - 1) ≤ Function.update qb' t (qb' t - 1) := fun j => by
  rcases eq_or_ne j t with rfl | hj
  · simpa using Nat.sub_le_sub_right (hle j) 1
  · simpa [Function.update_of_ne hj] using hle j

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
  funext j
  by_cases hj : j = t <;> simp [hj, Pi.add_apply]
  omega

/-- Split a per-index budget at index `t` into one unit at `t` plus the decremented
remainder, used to feed `isPerIndexQueryBound_bind` in the `simulateQ` transfer proofs. -/
private lemma update_zero_one_add_update {qb : ι → ℕ} {t : ι} (ht : 0 < qb t) :
    qb = Function.update (0 : ι → ℕ) t 1 + Function.update qb t (qb t - 1) := by
  funext j
  by_cases hj : j = t <;> simp [hj, Pi.add_apply]
  omega

private lemma isPerIndexQueryBound_bind_aux (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) (qb₂ : ι → ℕ)
    (h2 : ∀ x, IsPerIndexQueryBound (ob x) qb₂) :
    ∀ {qb₁}, oa.IsPerIndexQueryBound qb₁ →
      (oa >>= ob).IsPerIndexQueryBound (qb₁ + qb₂) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro qb₁ _
    simp only [monad_norm]
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
    · simpa only [Function.update_of_ne hi] using h_snd i

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
      rw [update_zero_one_add_update hqb_pos]
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
      rw [update_zero_one_add_update hqb_pos]
      exact isPerIndexQueryBound_bind (hstep t) hrest

end IsPerIndexQueryBound

/-! ### Total query bounds -/

/-- A total query bound: the computation makes at most `n` queries total
(across all oracle indices). -/
@[expose]
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
  | pure _ => trivial
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
  refine isQueryBound_bind (combine := fun a b => a + b) ?_ ?_ h1 h2 <;> grind

/-- Support-aware bind rule. Under uniform oracle semantics every syntactically reachable
continuation value lies in `support oa`, so it suffices to bound the continuation on that support
rather than on every value of its result type. -/
theorem isTotalQueryBound_bind_of_mem_support
    {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {prefixBound suffixBound : ℕ}
    (hprefix : IsTotalQueryBound oa prefixBound)
    (hsuffix : ∀ x ∈ support oa, IsTotalQueryBound (ob x) suffixBound) :
    IsTotalQueryBound (oa >>= ob) (prefixBound + suffixBound) := by
  induction oa using OracleComp.inductionOn generalizing prefixBound with
  | pure x =>
      simpa using (hsuffix x (by simp)).mono (by omega : suffixBound ≤ prefixBound + suffixBound)
  | query_bind t next ih =>
      rw [isTotalQueryBound_query_bind_iff] at hprefix
      rw [bind_assoc, isTotalQueryBound_query_bind_iff]
      refine ⟨by omega, fun response => ?_⟩
      apply (ih response (prefixBound := prefixBound - 1) (hprefix.2 response) ?_).mono
      · omega
      · intro x hx
        apply hsuffix x
        rw [mem_support_bind_iff]
        exact ⟨response, by simp, hx⟩

/-- If `oa >>= ob` has a total query bound `n`, then `oa` alone has total query bound `n`
(the continuation can only add queries, not remove them). -/
lemma IsTotalQueryBound.of_bind_left
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n : ℕ}
    (h : IsTotalQueryBound (oa >>= ob) n) :
    IsTotalQueryBound oa n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [bind_assoc, isTotalQueryBound_query_bind_iff] at h
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨h.1, fun u => ih u (h.2 u)⟩

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
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [bind_assoc, isTotalQueryBound_query_bind_iff] at h
      rw [isTotalQueryBound_query_bind_iff]
      have hn : 0 < n := Nat.pos_of_ne_zero fun hz =>
        absurd (hz ▸ h.2 default) not_isTotalQueryBound_bind_query_prefix_zero
      exact ⟨hn, fun u => ih u (n := n - 1) (Nat.sub_add_cancel hn ▸ h.2 u)⟩

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

/-- Generalisation of `IsTotalQueryBound.simulateQ_of_step` where each per-query handler
makes at most `step` queries (rather than at most `1`). The bound on the simulation is
`n * step`, where `n` is the bound on the source. -/
theorem IsTotalQueryBound.simulateQ_of_step_le {ι' : Type u} {spec' : OracleSpec ι'}
    {impl : QueryImpl spec (OracleComp spec')}
    {oa : OracleComp spec α} {n step : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep : ∀ t : spec.Domain, IsTotalQueryBound (impl t) step) :
    IsTotalQueryBound (simulateQ impl oa) (n * step) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x =>
      simpa [simulateQ_pure] using
        (show IsTotalQueryBound (pure x : OracleComp spec' α) (n * step) from trivial)
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at h
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      have hrest : ∀ u, IsTotalQueryBound (simulateQ impl (mx u)) ((n - 1) * step) :=
        fun u => ih u (h.2 u)
      have hn : step + (n - 1) * step = n * step := by
        rw [Nat.sub_one_mul, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left step h.1)]
      simpa [hn] using isTotalQueryBound_bind (hstep t) hrest

end OracleComp
