/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.Basic
public import VCVio.EvalDist.TVDist
import VCVio.EvalDist.TVDist.Positivity
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.ProgramLogic.Relational.SimulateQ.Basic
import all VCVio.ProgramLogic.Relational.SimulateQ.Basic
public import VCVio.ProgramLogic.Relational.SimulateQ.Epsilon
import all VCVio.ProgramLogic.Relational.SimulateQ.Epsilon

/-!
# State-dependent expected query slack
-/

public section

open ENNReal OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type u} {spec : OracleSpec ι}
variable {α : Type}

/-! ## Relational simulateQ rules -/

variable [IsUniformSpec spec]

/-! ### State-dep ε-perturbed identical-until-bad

A further refinement of `tvDist_simulateQ_le_queryBound_mul_slack_plus_probEvent_bad` where the
per-step ε bound is allowed to depend on the **input state** `s : σ` to the impl. The
bound on `tvDist` is then expressed as the **expected sum** of `ε s` over the trace of
charged queries fired during the simulation, captured by the recursive function
`expectedQuerySlack`.

This is essential for cryptographic reductions where the per-step gap depends on a varying
state quantity (e.g., for Fiat-Shamir signing-oracle swaps the gap is
`ζ_zk + |s.cache| · β`, growing with cache size, with no uniform constant ε).
The constant-ε lemma `tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad`
is a corollary.

To sidestep summability obligations, `expectedQuerySlack` is valued in `ℝ≥0∞` and the
bridge lemma is stated in `ℝ≥0∞` via `ENNReal.ofReal (tvDist …)`. -/

section IdenticalUntilBadEpsilonStateDep

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [IsUniformSpec spec']
variable {α : Type} {σ : Type}

/-- Per-`query_bind` step of `expectedQuerySlack`. Given the impl, the charged-query
predicate `S`, the per-state query slack `ε`, the query symbol `t`, and the IH continuation
`k : Range t → ℕ → (σ × Bool) → ℝ≥0∞`, returns the expected cost contributed by
performing the query `t` from state `p` with budget `qS`:

* if the bad flag is set in `p`, return `0` (the `Pr[bad]` term swallows the deficit);
* if `t` is a uncharged query (`¬ S t`), forward through the impl with budget unchanged;
* if `t` is a charged query and the budget is exhausted, return `0` (vacuous via
  `IsQueryBound`);
* if `t` is a charged query with positive budget, pay `ε p.1` immediately, then forward
  through the impl with budget decremented to `qS - 1`. -/
@[expose] noncomputable def expectedQuerySlackStep
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S]
    (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (p : σ × Bool) : ℝ≥0∞ :=
  if p.2 then 0
  else
    if S t then
      if 0 < qS then
        ε p.1 + ∑' z : spec.Range t × σ × Bool,
          Pr[= z | (impl t).run (p.1, false)] * k z.1 (qS - 1) z.2
      else 0
    else
      ∑' z : spec.Range t × σ × Bool,
        Pr[= z | (impl t).run (p.1, false)] * k z.1 qS z.2

/-- Recursive expected accumulated query slack over the charged queries fired during
`(simulateQ impl oa).run p`. Defined by recursion on `oa` via `OracleComp.construct`. -/
@[expose] noncomputable def expectedQuerySlack
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) :
    {α : Type} → OracleComp spec α → ℕ → (σ × Bool) → ℝ≥0∞ :=
  fun {_} oa => OracleComp.construct
    (C := fun _ => ℕ → (σ × Bool) → ℝ≥0∞)
    (fun _ _ _ => 0)
    (fun t _ ih => expectedQuerySlackStep impl S ε t ih)
    oa

@[simp]
lemma expectedQuerySlack_pure
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (x : α)
    (qS : ℕ) (p : σ × Bool) :
    expectedQuerySlack impl S ε (pure x : OracleComp spec α) qS p = 0 := rfl

/-- Defining equation of `expectedQuerySlack` at a query node: the slack of `query t >>= cont`
is a single `expectedQuerySlackStep` for the query symbol `t`, applied to the continuation
`fun u => expectedQuerySlack impl S ε (cont u)`; that continuation is left unapplied so the step
can feed it the post-query budget and state.

Together with `expectedQuerySlack_pure`, this pins `expectedQuerySlack` down on every computation.
The `expectedQuerySlackStep_*` lemmas then evaluate a single step by cases on the bad flag, on
`S t`, and on whether the budget `qS` is exhausted. -/
lemma expectedQuerySlack_query_bind
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec α)
    (qS : ℕ) (p : σ × Bool) :
    expectedQuerySlack impl S ε (query t >>= cont) qS p =
      expectedQuerySlackStep impl S ε t (fun u => expectedQuerySlack impl S ε (cont u)) qS p := rfl

lemma expectedQuerySlack_bind_eq_of_right_zero
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    {β : Type} (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (hzero : ∀ x qS p, expectedQuerySlack impl S ε (ob x) qS p = 0)
    (qS : ℕ) (p : σ × Bool) :
    expectedQuerySlack impl S ε (oa >>= ob) qS p =
      expectedQuerySlack impl S ε oa qS p := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x =>
      simp [hzero x qS p]
  | query_bind t cont ih =>
      simp only [monad_norm]
      rw [expectedQuerySlack_query_bind, expectedQuerySlack_query_bind]
      congr; funext u qS' p'; exact ih u qS' p'

@[simp]
lemma expectedQuerySlackStep_bad_eq_zero
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (s : σ) :
    expectedQuerySlackStep impl S ε t k qS (s, true) = 0 := rfl

@[simp]
lemma expectedQuerySlack_bad_eq_zero
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (oa : OracleComp spec α) (qS : ℕ) (s : σ) :
    expectedQuerySlack impl S ε oa qS (s, true) = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact expectedQuerySlack_pure impl S ε x qS (s, true)
  | query_bind t cont _ =>
      rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_bad_eq_zero]

lemma expectedQuerySlackStep_costly_pos
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (s : σ) (hS : S t) (hqS : 0 < qS) :
    expectedQuerySlackStep impl S ε t k qS (s, false) =
      ε s + ∑' z : spec.Range t × σ × Bool,
        Pr[= z | (impl t).run (s, false)] * k z.1 (qS - 1) z.2 := by
  simp [expectedQuerySlackStep, hS, hqS]

/-- Unfolding of `expectedQuerySlackStep` at an *uncharged* query (`¬ S t`) reached with the
bad flag unset: no slack is paid, and the step is exactly the expectation of the continuation
`k` over the joint output distribution of `(impl t).run (s, false)`, with the query budget `qS`
forwarded unchanged.

This is the `¬ S t` half of the case split on the step function; the companions are
`expectedQuerySlackStep_costly_pos` (charged query with budget left: `ε s` is paid up front and
the budget forwarded is `qS - 1`) and `expectedQuerySlackStep_bad_eq_zero` (bad flag already
set: the step is `0`). The remaining case, a charged query with exhausted budget, is also `0`
and is reached by unfolding `expectedQuerySlackStep` directly.

`hS` is the only side condition, so unlike the charged branch this rewrite applies at every
budget, `qS = 0` included. -/
lemma expectedQuerySlackStep_free
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (k : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞)
    (qS : ℕ) (s : σ) (hS : ¬ S t) :
    expectedQuerySlackStep impl S ε t k qS (s, false) =
      ∑' z : spec.Range t × σ × Bool,
        Pr[= z | (impl t).run (s, false)] * k z.1 qS z.2 := by
  simp [expectedQuerySlackStep, hS]

/-! #### Pointwise monotonicity of `expectedQuerySlack` in `ε`

If `ε ≤ ε'` pointwise (as functions `σ → ℝ≥0∞`), then
`expectedQuerySlack impl S ε oa qS p ≤ expectedQuerySlack impl S ε' oa qS p`.
The analogous monotonicity in the continuation `k` (for
`expectedQuerySlackStep`) is the step-level lemma, used in the inductive
step of `expectedQuerySlack_mono`. These lemmas are used to bound a
state-dependent ε by a constant upper bound so the constant-ε bound
`expectedQuerySlack_const_le_queryBudget_mul` applies. -/

@[gcongr]
lemma expectedQuerySlackStep_mono
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] {ε ε' : σ → ℝ≥0∞}
    (hε : ∀ s, ε s ≤ ε' s)
    (t : spec.Domain) {k k' : spec.Range t → ℕ → (σ × Bool) → ℝ≥0∞}
    (hk : ∀ u qS p, k u qS p ≤ k' u qS p)
    (qS : ℕ) (p : σ × Bool) :
    expectedQuerySlackStep impl S ε t k qS p ≤ expectedQuerySlackStep impl S ε' t k' qS p := by
  rcases p with ⟨s, b⟩
  cases b with
  | true => simp [expectedQuerySlackStep]
  | false =>
      by_cases hSt : S t
      · by_cases hqS : 0 < qS
        · rw [expectedQuerySlackStep_costly_pos impl S ε t k qS s hSt hqS,
              expectedQuerySlackStep_costly_pos impl S ε' t k' qS s hSt hqS]
          gcongr with z
          · exact hε s
          · exact hk z.1 (qS - 1) z.2
        · simp [expectedQuerySlackStep, hSt, hqS]
      · rw [expectedQuerySlackStep_free impl S ε t k qS s hSt,
            expectedQuerySlackStep_free impl S ε' t k' qS s hSt]
        gcongr with z
        exact hk z.1 qS z.2

@[gcongr]
theorem expectedQuerySlack_mono
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] {ε ε' : σ → ℝ≥0∞}
    (hε : ∀ s, ε s ≤ ε' s)
    (oa : OracleComp spec α) (qS : ℕ) (p : σ × Bool) :
    expectedQuerySlack impl S ε oa qS p ≤ expectedQuerySlack impl S ε' oa qS p := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x => simp
  | query_bind t cont ih =>
      exact expectedQuerySlackStep_mono impl S hε t (fun u qS' p' => ih u qS' p') qS p

/-! #### Invariant support congruence for `expectedQuerySlack` -/

/-- Two expectations against the same computation agree as soon as their integrands agree on its
support, since off-support values are weighted by zero probability. -/
private lemma tsum_probOutput_mul_congr_of_mem_support {γ : Type} (mx : OracleComp spec' γ)
    {F G : γ → ℝ≥0∞} (h : ∀ z ∈ support mx, F z = G z) :
    ∑' z, Pr[= z | mx] * F z = ∑' z, Pr[= z | mx] * G z :=
  tsum_congr fun z => by
    by_cases hz : z ∈ support mx
    · rw [h z hz]
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]

/-- If two per-state query slack functions agree on an invariant `Inv`, and the handler preserves
`Inv` along the support of every query answered from a no-bad state, then `expectedQuerySlack`
cannot tell the two apart: only invariant-reachable states are ever charged.

Where `expectedQuerySlack_mono` compares two budgets that are ordered at *every* state, this
compares two budgets that merely agree on the states an execution can reach, so a budget may be
given arbitrary values off `Inv`. To apply it, instantiate `Inv` with whatever reachability
predicate `impl` maintains; `h_pres` is then the usual support-level preservation obligation.

The state hypotheses are phrased as `p.2 = false → Inv p.1` so that bad states stay vacuous:
`expectedQuerySlack` is definitionally zero once the bad flag is set. -/
theorem expectedQuerySlack_eq_of_inv
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] {ε ε' : σ → ℝ≥0∞}
    (Inv : σ → Prop)
    (hε : ∀ s, Inv s → ε s = ε' s) (h_pres : ∀ (t : spec.Domain) (p : σ × Bool),
      p.2 = false → Inv p.1 → ∀ z ∈ support ((impl t).run p), Inv z.2.1)
    (oa : OracleComp spec α) (qS : ℕ) (p : σ × Bool) (hp : p.2 = false → Inv p.1) :
    expectedQuerySlack impl S ε oa qS p = expectedQuerySlack impl S ε' oa qS p := by
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x => simp
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true => simp
      | false =>
          have hInv : Inv s := hp rfl
          by_cases hSt : S t
          · by_cases hqS : 0 < qS
            · rw [expectedQuerySlack_query_bind, expectedQuerySlack_query_bind,
                expectedQuerySlackStep_costly_pos impl S ε t
                  (fun u => expectedQuerySlack impl S ε (cont u)) qS s hSt hqS,
                expectedQuerySlackStep_costly_pos impl S ε' t
                  (fun u => expectedQuerySlack impl S ε' (cont u)) qS s hSt hqS,
                hε s hInv]
              congr 1
              exact tsum_probOutput_mul_congr_of_mem_support _ fun z hz =>
                ih z.1 (qS - 1) z.2 fun _ => h_pres t (s, false) rfl hInv z hz
            · simp [expectedQuerySlack_query_bind, expectedQuerySlackStep, hSt, hqS]
          · rw [expectedQuerySlack_query_bind, expectedQuerySlack_query_bind,
              expectedQuerySlackStep_free impl S ε t
                (fun u => expectedQuerySlack impl S ε (cont u)) qS s hSt,
              expectedQuerySlackStep_free impl S ε' t
                (fun u => expectedQuerySlack impl S ε' (cont u)) qS s hSt]
            exact tsum_probOutput_mul_congr_of_mem_support _ fun z hz =>
              ih z.1 qS z.2 fun _ => h_pres t (s, false) rfl hInv z hz

/-! #### Helper lemma: per-summand IH bound implies the bind-sum bound -/

/-- Sum bound for the inductive step: from a per-summand `ofReal (tvDist) ≤ cost z + Pr[bad]`
IH, conclude that `ofReal (∑' z, Pr[=z|mx].toReal · tvDist (f₁ z) (f₂ z))` is bounded by
`(∑' z, Pr[=z|mx] · cost z) + Pr[bad | mx >>= f₁]`. The state-dep analogue of
`tsum_probOutput_mul_tvDist_le_const_plus_probEvent_bad`, replacing the constant `c` by a
per-summand `cost z : ℝ≥0∞`. -/
private lemma tsum_probOutput_mul_ofReal_tvDist_le_tsum_cost_plus_probEvent_bad
    {γ : Type} (mx : OracleComp spec' γ) (f₁ f₂ : γ → OracleComp spec' (α × σ × Bool))
    (cost : γ → ℝ≥0∞)
    (h_summand_le : ∀ z : γ,
      ENNReal.ofReal (tvDist (f₁ z) (f₂ z)) ≤
        cost z + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z]) :
    ENNReal.ofReal (∑' z, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
      ≤ (∑' z, Pr[= z | mx] * cost z)
        + Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁] := by
  have h_p_sum_le_one : (∑' z : γ, Pr[= z | mx]) ≤ 1 := tsum_probOutput_le_one
  have h_p_sum_ne_top : (∑' z : γ, Pr[= z | mx]) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top h_p_sum_le_one
  have h_p_summable : Summable (fun z : γ => Pr[= z | mx].toReal) :=
    ENNReal.summable_toReal h_p_sum_ne_top
  have h_lhs_summand_nn : ∀ z : γ,
      0 ≤ Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) :=
    fun z => by positivity
  have h_lhs_summand_le : ∀ z : γ,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤ Pr[= z | mx].toReal :=
    fun z => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)
  have h_lhs_summable : Summable
      (fun z : γ => Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z)) :=
    Summable.of_nonneg_of_le h_lhs_summand_nn h_lhs_summand_le h_p_summable
  have h_p_ne_top : ∀ z : γ, Pr[= z | mx] ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top one_ne_top probOutput_le_one
  have h_summand_eq : ∀ z : γ,
      ENNReal.ofReal (Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z)) =
        Pr[= z | mx] * ENNReal.ofReal (tvDist (f₁ z) (f₂ z)) := fun z => by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (h_p_ne_top z)]
  have h_ofreal_tsum :
      ENNReal.ofReal (∑' z, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
        = ∑' z, Pr[= z | mx] * ENNReal.ofReal (tvDist (f₁ z) (f₂ z)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg h_lhs_summand_nn h_lhs_summable]
    exact tsum_congr h_summand_eq
  rw [h_ofreal_tsum]
  calc
    (∑' z : γ, Pr[= z | mx] * ENNReal.ofReal (tvDist (f₁ z) (f₂ z)))
      ≤ ∑' z : γ, Pr[= z | mx] *
          (cost z + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z]) :=
        ENNReal.tsum_le_tsum fun z => by gcongr; exact h_summand_le z
    _ = (∑' z : γ, Pr[= z | mx] * cost z) +
          ∑' z : γ, Pr[= z | mx] *
            Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z] := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun z => ?_
        rw [mul_add]
    _ = (∑' z : γ, Pr[= z | mx] * cost z) +
          Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁] := by
        rw [← probEvent_bind_eq_tsum mx f₁]

/-! #### Per-step inductive helpers -/

/-- Triangle bound for a bind in which both the base computation and the continuation
change: the weighted per-branch continuation distances control the change of continuation,
and the base distance controls the change of base. -/
private lemma ofReal_tvDist_bind_le_tsum_add_tvDist {γ β : Type} (mx my : OracleComp spec' γ)
    (f₁ f₂ : γ → OracleComp spec' β) :
    ENNReal.ofReal (tvDist (mx >>= f₁) (my >>= f₂))
      ≤ ENNReal.ofReal (∑' z, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
        + ENNReal.ofReal (tvDist mx my) := by
  refine (ENNReal.ofReal_le_ofReal <|
    (tvDist_triangle (mx >>= f₁) (mx >>= f₂) (my >>= f₂)).trans <|
      add_le_add (tvDist_bind_left_le mx f₁ f₂) (tvDist_bind_right_le f₂ mx my)).trans ?_
  rw [ENNReal.ofReal_add (tsum_nonneg fun z =>
    mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)) (tvDist_nonneg mx my)]

/-- The `query_bind` step of the state-dependent-`ε` slack bound at a *charged* query (`S t`)
whose budget is not yet exhausted (`0 < qS`): the query step itself is charged `ε s`, and the
continuations are charged the inductive hypothesis' expected slack with budget `qS - 1`.
Companion of `ofReal_tvDist_simulateQ_run_free_query_bind_le_expectedQuerySlack`, which
handles a query outside `S`. -/
private theorem ofReal_tvDist_simulateQ_run_costly_query_bind_le_expectedQuerySlack
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec'))) (S : spec.Domain → Prop)
    [DecidablePred S] (ε : σ → ℝ≥0∞) (h_step_tv_S : ∀ (t : spec.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false))) ≤ ε s)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec α) {qS : ℕ} (hS : S t) (hqS : 0 < qS)
    (ih : ∀ (u : spec.Range t) (p' : σ × Bool),
      ENNReal.ofReal (tvDist ((simulateQ impl₁ (cont u)).run p')
          ((simulateQ impl₂ (cont u)).run p')) ≤ expectedQuerySlack impl₁ S ε (cont u) (qS - 1) p'
          + Pr[ fun w : α × σ × Bool => w.2.2 = true | (simulateQ impl₁ (cont u)).run p'])
    (s : σ) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false)))
      ≤ expectedQuerySlack impl₁ S ε (query t >>= cont) qS (s, false)
        + Pr[fun z : α × σ × Bool => z.2.2 = true |
            (simulateQ impl₁ (query t >>= cont)).run (s, false)] := by
  set mx : OracleComp spec' (spec.Range t × σ × Bool) := (impl₁ t).run (s, false) with hmx_def
  set my : OracleComp spec' (spec.Range t × σ × Bool) := (impl₂ t).run (s, false) with hmy_def
  set f₁ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₁ (cont z.1)).run z.2 with hf₁_def
  set f₂ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₂ (cont z.1)).run z.2 with hf₂_def
  -- each run factors as the query step bound to the simulated continuation
  have hsim₁_eq : (simulateQ impl₁ (query t >>= cont)).run (s, false) = mx >>= f₁ := by
    simp [hmx_def, hf₁_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  have hsim₂_eq : (simulateQ impl₂ (query t >>= cont)).run (s, false) = my >>= f₂ := by
    simp [hmy_def, hf₂_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  -- the query step itself is charged `ε s` by hypothesis
  have h_second : ENNReal.ofReal (tvDist mx my) ≤ ε s :=
    le_trans (by rw [hmx_def, hmy_def]) (h_step_tv_S t hS s)
  -- the continuations are charged by the inductive hypothesis, pushed through the bind
  have h_first : ENNReal.ofReal (∑' z : spec.Range t × σ × Bool,
        Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
      ≤ (∑' z : spec.Range t × σ × Bool,
          Pr[= z | mx] * expectedQuerySlack impl₁ S ε (cont z.1) (qS - 1) z.2)
        + Pr[ fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁] :=
    tsum_probOutput_mul_ofReal_tvDist_le_tsum_cost_plus_probEvent_bad mx f₁ f₂
      (fun z => expectedQuerySlack impl₁ S ε (cont z.1) (qS - 1) z.2)
      fun z => by simpa [hf₁_def, hf₂_def] using ih z.1 z.2
  -- the slack at a charged query with positive budget pays `ε s` and recurses on `qS - 1`
  have h_recurse :
      expectedQuerySlack impl₁ S ε (query t >>= cont) qS (s, false) =
        ε s + ∑' z : spec.Range t × σ × Bool,
          Pr[= z | (impl₁ t).run (s, false)] *
            expectedQuerySlack impl₁ S ε (cont z.1) (qS - 1) z.2 := by
    rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ hS hqS]
  calc
    ENNReal.ofReal (tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false)))
      = ENNReal.ofReal (tvDist (mx >>= f₁) (my >>= f₂)) := by rw [hsim₁_eq, hsim₂_eq]
    _ ≤ ENNReal.ofReal (∑' z : spec.Range t × σ × Bool,
            Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z)) + ENNReal.ofReal (tvDist mx my) :=
        ofReal_tvDist_bind_le_tsum_add_tvDist mx my f₁ f₂
    _ ≤ ((∑' z : spec.Range t × σ × Bool,
            Pr[= z | mx] * expectedQuerySlack impl₁ S ε (cont z.1) (qS - 1) z.2)
          + Pr[ fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁]) + ε s :=
        add_le_add h_first h_second
    _ = expectedQuerySlack impl₁ S ε (query t >>= cont) qS (s, false)
          + Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ (query t >>= cont)).run (s, false)] := by
        rw [h_recurse, ← hmx_def, ← hsim₁_eq]
        ring

/-- The `query_bind` step for a free (non-S) query, state-dep ε version. The impls are
pointwise equal at this query, so the only contribution is from the IH; the budget `qS`
is preserved (no decrement). -/
private theorem ofReal_tvDist_simulateQ_run_free_query_bind_le_expectedQuerySlack
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞)
    (h_step_eq_nS : ∀ (t : spec.Domain), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec α)
    {qS : ℕ} (hS : ¬ S t)
    (ih : ∀ (u : spec.Range t) (p' : σ × Bool),
      ENNReal.ofReal (tvDist ((simulateQ impl₁ (cont u)).run p')
          ((simulateQ impl₂ (cont u)).run p'))
        ≤ expectedQuerySlack impl₁ S ε (cont u) qS p'
          + Pr[ fun w : α × σ × Bool => w.2.2 = true |
              (simulateQ impl₁ (cont u)).run p'])
    (s : σ) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false)))
      ≤ expectedQuerySlack impl₁ S ε (query t >>= cont) qS (s, false)
        + Pr[fun z : α × σ × Bool => z.2.2 = true |
            (simulateQ impl₁ (query t >>= cont)).run (s, false)] := by
  set mx : OracleComp spec' (spec.Range t × σ × Bool) := (impl₁ t).run (s, false) with hmx_def
  have hmy_eq : (impl₂ t).run (s, false) = mx := (h_step_eq_nS t hS (s, false)).symm
  set f₁ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₁ (cont z.1)).run z.2 with hf₁_def
  set f₂ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₂ (cont z.1)).run z.2 with hf₂_def
  have hsim₁_eq : (simulateQ impl₁ (query t >>= cont)).run (s, false) = mx >>= f₁ := by
    simp [hmx_def, hf₁_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  have hsim₂_eq : (simulateQ impl₂ (query t >>= cont)).run (s, false) = mx >>= f₂ := by
    simp [hmy_eq, hf₂_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  have h_bd_real : tvDist (mx >>= f₁) (mx >>= f₂)
      ≤ ∑' z : spec.Range t × σ × Bool, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) :=
    tvDist_bind_left_le _ _ _
  have h_recurse :
      expectedQuerySlack impl₁ S ε (query t >>= cont) qS (s, false) =
        ∑' z : spec.Range t × σ × Bool,
          Pr[= z | (impl₁ t).run (s, false)] *
            expectedQuerySlack impl₁ S ε (cont z.1) qS z.2 := by
    rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free _ _ _ _ _ _ _ hS]
  calc
    ENNReal.ofReal (tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false)))
      = ENNReal.ofReal (tvDist (mx >>= f₁) (mx >>= f₂)) := by rw [hsim₁_eq, hsim₂_eq]
    _ ≤ ENNReal.ofReal
          (∑' z : spec.Range t × σ × Bool, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z)) :=
        ENNReal.ofReal_le_ofReal h_bd_real
    _ ≤ (∑' z : spec.Range t × σ × Bool,
            Pr[= z | mx] * expectedQuerySlack impl₁ S ε (cont z.1) qS z.2)
          + Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁] := by
        refine tsum_probOutput_mul_ofReal_tvDist_le_tsum_cost_plus_probEvent_bad
          (mx := mx) (f₁ := f₁) (f₂ := f₂)
          (cost := fun z => expectedQuerySlack impl₁ S ε (cont z.1) qS z.2)
          (fun z => ?_)
        simpa [hf₁_def, hf₂_def] using ih z.1 z.2
    _ = expectedQuerySlack impl₁ S ε (query t >>= cont) qS (s, false)
          + Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ (query t >>= cont)).run (s, false)] := by
        rw [h_recurse, ← hmx_def, ← hsim₁_eq]

/-! #### Inductive auxiliary lemma -/

/-- Auxiliary inductive lemma for the state-dep ε-perturbed bound. Inducts on `oa` and
case-splits each query on whether it's in the charged query predicate `S` (decrement budget, charge
`ε s`) or free (no decrement, no charge). The bad-flag-true branch dominates the trivial
`tvDist ≤ 1` bound via `Pr[bad | sim₁] = 1`, so `expectedQuerySlack = 0` is enough there. -/
private theorem ofReal_tvDist_simulateQ_run_le_expectedQuerySlack_plus_probEvent_output_bad_aux
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery : spec.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_tv_charged : ∀ (t : spec.Domain), chargedQuery t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false))) ≤
        querySlack s)
    (h_step_eq_uncharged : ∀ (t : spec.Domain), ¬ chargedQuery t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {queryBudget : ℕ}
    (h_qb : OracleComp.IsQueryBoundP oa chargedQuery queryBudget)
    (p : σ × Bool) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p))
      ≤ expectedQuerySlack impl₁ chargedQuery querySlack oa queryBudget p
        + Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run p] := by
  induction oa using OracleComp.inductionOn generalizing queryBudget p with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, tvDist_self, ENNReal.ofReal_zero]
      exact zero_le
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true =>
          have h_bad₁ : Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ (query t >>= cont)).run (s, true)] = 1 :=
            probEvent_simulateQ_run_bad_eq_one_of_bad impl₁ h_mono₁
              (query t >>= cont) (s, true) rfl
          have h_tv_le_one_real :
              tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, true))
                  ((simulateQ impl₂ (query t >>= cont)).run (s, true)) ≤ 1 :=
            tvDist_le_one _ _
          have h_lhs_le_one :
              ENNReal.ofReal (tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, true))
                  ((simulateQ impl₂ (query t >>= cont)).run (s, true))) ≤ 1 := by
            calc ENNReal.ofReal _
                ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h_tv_le_one_real
              _ = 1 := ENNReal.ofReal_one
          have h_cost_zero :
              expectedQuerySlack impl₁ chargedQuery querySlack
                (query t >>= cont) queryBudget (s, true) = 0 :=
            expectedQuerySlack_bad_eq_zero impl₁ chargedQuery querySlack
              (query t >>= cont) queryBudget s
          rw [h_cost_zero, zero_add, h_bad₁]
          exact h_lhs_le_one
      | false =>
          rw [isQueryBoundP_query_bind_iff] at h_qb
          obtain ⟨h_can, h_cont⟩ := h_qb
          by_cases hSt : chargedQuery t
          · simp only [hSt, if_true] at h_cont
            have hq_pos : 0 < queryBudget := h_can.resolve_left (· hSt)
            exact ofReal_tvDist_simulateQ_run_costly_query_bind_le_expectedQuerySlack
              impl₁ impl₂ chargedQuery querySlack h_step_tv_charged t cont hSt hq_pos
              (fun u p' => ih u (h_cont u) p') s
          · simp only [hSt, if_false] at h_cont
            exact ofReal_tvDist_simulateQ_run_free_query_bind_le_expectedQuerySlack
              impl₁ impl₂ chargedQuery querySlack h_step_eq_uncharged t cont hSt
              (fun u p' => ih u (h_cont u) p') s

/-! #### Public bridge lemmas -/

/-- **State-dep ε-perturbed identical-until-bad with output bad flag (joint state).**

Like `tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad`, but the
per-step ε bound is allowed to depend on the input state `s : σ` to the impl.
The `q · ε` term is replaced by the **expected accumulated query slack** over
the trace of charged queries fired during simulation, captured by
`expectedQuerySlack`.

Statement is in `ℝ≥0∞` to sidestep summability obligations on the query-slack trace. -/
theorem ofReal_tvDist_simulateQ_run_le_expectedQuerySlack_plus_probEvent_output_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery : spec.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_tv_charged : ∀ (t : spec.Domain), chargedQuery t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false))) ≤
        querySlack s)
    (h_step_eq_uncharged : ∀ (t : spec.Domain), ¬ chargedQuery t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {queryBudget : ℕ}
    (h_qb : OracleComp.IsQueryBoundP oa chargedQuery queryBudget)
    (p : σ × Bool) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p))
      ≤ expectedQuerySlack impl₁ chargedQuery querySlack oa queryBudget p
        + Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run p] :=
  ofReal_tvDist_simulateQ_run_le_expectedQuerySlack_plus_probEvent_output_bad_aux
    impl₁ impl₂ chargedQuery querySlack h_step_tv_charged h_step_eq_uncharged h_mono₁ oa h_qb p

/-- **State-dep ε-perturbed identical-until-bad with output bad flag (projected output).**

Composing the joint-state lemma with the projection `Prod.fst : α × σ × Bool → α`, which
can only decrease TV distance (data-processing inequality `tvDist_map_le`). -/
theorem ofReal_tvDist_simulateQ_le_expectedQuerySlack_plus_probEvent_output_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery : spec.Domain → Prop) [DecidablePred chargedQuery]
    (querySlack : σ → ℝ≥0∞)
    (h_step_tv_charged : ∀ (t : spec.Domain), chargedQuery t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false))) ≤
        querySlack s)
    (h_step_eq_uncharged : ∀ (t : spec.Domain), ¬ chargedQuery t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {queryBudget : ℕ}
    (h_qb : OracleComp.IsQueryBoundP oa chargedQuery queryBudget)
    (s₀ : σ) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false)))
      ≤ expectedQuerySlack impl₁ chargedQuery querySlack oa queryBudget (s₀, false)
        + Pr[fun z : α × σ × Bool => z.2.2 = true |
            (simulateQ impl₁ oa).run (s₀, false)] := by
  have h_joint :
      ENNReal.ofReal (tvDist ((simulateQ impl₁ oa).run (s₀, false))
          ((simulateQ impl₂ oa).run (s₀, false)))
        ≤ expectedQuerySlack impl₁ chargedQuery querySlack oa queryBudget (s₀, false)
          + Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ oa).run (s₀, false)] :=
    ofReal_tvDist_simulateQ_run_le_expectedQuerySlack_plus_probEvent_output_bad
      impl₁ impl₂ chargedQuery querySlack h_step_tv_charged h_step_eq_uncharged
        h_mono₁ oa h_qb (s₀, false)
  have h_map_real :
      tvDist ((simulateQ impl₁ oa).run' (s₀, false))
          ((simulateQ impl₂ oa).run' (s₀, false))
        ≤ tvDist ((simulateQ impl₁ oa).run (s₀, false))
            ((simulateQ impl₂ oa).run (s₀, false)) := by
    rw [StateT.run']
    exact tvDist_map_le (m := OracleComp spec') (α := α × σ × Bool) (β := α) Prod.fst
      ((simulateQ impl₁ oa).run (s₀, false)) ((simulateQ impl₂ oa).run (s₀, false))
  exact le_trans (ENNReal.ofReal_le_ofReal h_map_real) h_joint

/-! #### Constant-ε corollary (Phase A2 regression)

Specializing `expectedQuerySlack` to a constant query-slack function `fun _ => ε` and using
`IsQueryBoundP` to bound the number of charged queries, the accumulated slack is dominated by
`q · ε`. Combined
with the state-dep main lemma this re-derives the selective constant-ε bound
in `ENNReal` form. -/

/-- Bound a weighted average of a nonnegative functional by a uniform pointwise bound: the
output weights of `mx` sum to at most one, so the average of `F` is at most any constant
dominating `F`. -/
private lemma tsum_probOutput_mul_le_const {β : Type} (mx : OracleComp spec' β) {F : β → ℝ≥0∞}
    {c : ℝ≥0∞} (h_le : ∀ z : β, F z ≤ c) : (∑' z : β, Pr[= z | mx] * F z) ≤ c :=
  calc (∑' z : β, Pr[= z | mx] * F z)
      ≤ ∑' z : β, Pr[= z | mx] * c := tsum_probOutput_mul_mono mx h_le
    _ = (∑' z : β, Pr[= z | mx]) * c := ENNReal.tsum_mul_right
    _ ≤ c := mul_le_of_le_one_left zero_le tsum_probOutput_le_one

/-- A probability-weighted quantity is bounded by `c` when it is bounded by `c` on the
support of the computation. Values off support are irrelevant because their output
probability is zero. -/
private lemma tsum_probOutput_mul_le_const_of_mem_support
    {β : Type} (mx : OracleComp spec' β) {F : β → ℝ≥0∞} {c : ℝ≥0∞}
    (h_le : ∀ z ∈ support mx, F z ≤ c) : (∑' z : β, Pr[= z | mx] * F z) ≤ c := by
  calc
    (∑' z : β, Pr[= z | mx] * F z) ≤ ∑' z : β, Pr[= z | mx] * c :=
      ENNReal.tsum_le_tsum fun z => by
        by_cases hz : z ∈ support mx
        · exact mul_le_mul_right (h_le z hz) _
        · simp [probOutput_eq_zero_of_not_mem_support hz]
    _ = (∑' z : β, Pr[= z | mx]) * c := ENNReal.tsum_mul_right
    _ ≤ c := mul_le_of_le_one_left zero_le tsum_probOutput_le_one

/-- **Constant-ε query-budget bound for `expectedQuerySlack`.**

For the constant per-query slack `fun _ => ε`, a computation firing at most `queryBudget`
charged queries accumulates expected slack at most `queryBudget * ε`: the price of a charged
query does not depend on the simulation state, so the budget simply multiplies it. Free
queries and runs whose bad flag is already set contribute nothing.

Reach for this when the per-charged-query total-variation gap is a single uniform `ε`;
composed with `ofReal_tvDist_simulateQ_le_expectedQuerySlack_plus_probEvent_output_bad` it
recovers the selective `q · ε` bound. A state-dependent slack that admits a uniform upper
bound can be routed here through `expectedQuerySlack_mono`. When the per-query price
genuinely scales with a resource carried in the state, use a resource fold instead:
`expectedQuerySlack_resource_le` (the resource grows by at most one in support),
`expectedQuerySlack_expected_resource_le` (charged queries grow it by at most `g` in
expectation, at the cost of a binomial cross-term), or
`expectedQuerySlack_charged_read_expected_growth_le` (charged queries only read the
resource, while a separate class of queries grows it). -/
lemma expectedQuerySlack_const_le_queryBudget_mul
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery : spec.Domain → Prop) [DecidablePred chargedQuery] (ε : ℝ≥0∞)
    (oa : OracleComp spec α) {queryBudget : ℕ}
    (h_qb : OracleComp.IsQueryBoundP oa chargedQuery queryBudget) (p : σ × Bool) :
    expectedQuerySlack impl chargedQuery (fun _ => ε) oa queryBudget p ≤ queryBudget * ε := by
  induction oa using OracleComp.inductionOn generalizing queryBudget p with
  | pure x => simp
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true => simp [expectedQuerySlack_bad_eq_zero]
      | false =>
          rw [isQueryBoundP_query_bind_iff] at h_qb
          obtain ⟨h_can, h_cont⟩ := h_qb
          by_cases hSt : chargedQuery t
          -- a charged query pays `ε` up front and passes on a budget one smaller
          · have hq_pos : 0 < queryBudget := h_can.resolve_left (· hSt)
            obtain ⟨n, rfl⟩ : ∃ n, queryBudget = n + 1 :=
              ⟨queryBudget - 1, (Nat.succ_pred_eq_of_pos hq_pos).symm⟩
            simp only [hSt, if_true, Nat.add_sub_cancel] at h_cont
            rw [expectedQuerySlack_query_bind,
              expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ hSt hq_pos, Nat.add_sub_cancel]
            refine le_trans (add_le_add le_rfl (tsum_probOutput_mul_le_const
              ((impl t).run (s, false)) fun z => ih z.1 (h_cont z.1) z.2)) (le_of_eq ?_)
            push_cast
            ring
          -- a free query costs nothing and passes on the whole budget
          · simp only [hSt, if_false] at h_cont
            rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free _ _ _ _ _ _ _ hSt]
            exact tsum_probOutput_mul_le_const ((impl t).run (s, false))
              fun z => ih z.1 (h_cont z.1) z.2

/-- State-dependent resource bound for `expectedQuerySlack`.

If each charged query pays `ζ + R s * β`, and the resource `R` can increase by
at most one on charged or growth queries and never increases otherwise, then a
computation with at most `qS` charged queries and at most `qH` growth queries
has accumulated slack at most
`qS * ζ + qS * (R s + qS + qH) * β`. -/
lemma expectedQuerySlack_resource_le
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery growthQuery : spec.Domain → Prop)
    [DecidablePred chargedQuery] [DecidablePred growthQuery]
    (R : σ → ℝ≥0∞) (ζ β : ℝ≥0∞)
    (h_growth : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      chargedQuery t ∨ growthQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1 + 1)
    (h_free : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      ¬ chargedQuery t → ¬ growthQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1)
    (oa : OracleComp spec α) {qS qH : ℕ}
    (h_qS : OracleComp.IsQueryBoundP oa chargedQuery qS)
    (h_qH : OracleComp.IsQueryBoundP oa growthQuery qH)
    (s : σ) :
    expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) oa qS (s, false)
      ≤ (qS : ℝ≥0∞) * ζ + (qS : ℝ≥0∞) * (R s + qS + qH) * β := by
  induction oa using OracleComp.inductionOn generalizing qS qH s with
  | pure x => simp
  | query_bind t cont ih =>
      rw [isQueryBoundP_query_bind_iff] at h_qS h_qH
      obtain ⟨hcanS, hcontS⟩ := h_qS
      obtain ⟨hcanH, hcontH⟩ := h_qH
      let qH' : ℕ := if growthQuery t then qH - 1 else qH
      let slackSum : ℕ → ℝ≥0∞ := fun n => ∑' z : spec.Range t × σ × Bool,
        Pr[= z | (impl t).run (s, false)] *
          expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) (cont z.1) n z.2
      set B : ℝ≥0∞ := R s + qS + qH with hB
      suffices h_tail : ∀ (n : ℕ),
          (∀ u, OracleComp.IsQueryBoundP (cont u) chargedQuery n) →
          (∀ z ∈ support ((impl t).run (s, false)), R z.2.1 + n + qH' ≤ B) →
          slackSum n ≤ (n : ℝ≥0∞) * ζ + (n : ℝ≥0∞) * B * β from by
        by_cases hSt : chargedQuery t
        · let qS': ℕ := qS - 1
          simp only [hSt, if_true] at hcontS
          have hqS_pos : 0 < qS := hcanS.resolve_left (· hSt)
          have hqS_cast : (((qS - 1 : ℕ) : ℝ≥0∞) + 1) = (qS : ℝ≥0∞) := by
            exact_mod_cast Nat.sub_add_cancel hqS_pos
          rw [expectedQuerySlack_query_bind,
            expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ hSt hqS_pos]
          have hbudget : ∀ z ∈ support ((impl t).run (s, false)), R z.2.1 + qS' + qH' ≤ B := by
            intro z hz
            have hRz : R z.2.1 ≤ R s + 1 := h_growth t (s, false) rfl (Or.inl hSt) z hz
            calc R z.2.1 + qS' + qH'
                ≤ (R s + 1) + qS' + qH' := by
                  rw [add_assoc, add_assoc]; exact add_le_add_left hRz (qS' + qH')
              _ = R s + qS + qH' := by rw [add_assoc (R s), add_comm 1, hqS_cast]
              _ ≤ B := by
                dsimp only [B, qH']; gcongr; split_ifs
                · exact tsub_le_self
                · exact le_rfl
          calc ζ + R s * β + slackSum qS'
            ≤ ζ + B * β + ((qS' : ℝ≥0∞) * ζ + (qS' : ℝ≥0∞) * B * β) := by
                gcongr
                · exact (le_self_add : R s ≤ R s + (qS : ℝ≥0∞)).trans le_self_add
                · exact h_tail qS' hcontS hbudget
          _ = (qS : ℝ≥0∞) * ζ + (qS : ℝ≥0∞) * B * β := by rw [← hqS_cast]; ring
        · simp only [hSt, if_false] at hcontS
          rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free _ _ _ _ _ _ _ hSt]
          have hbudget : ∀ z ∈ support ((impl t).run (s, false)), R z.2.1 + qS + qH' ≤ B := by
            intro z hz
            have hRz : R z.2.1 ≤ R s + if growthQuery t then (1 : ℝ≥0∞) else 0 := by
              by_cases hHt : growthQuery t <;> simp only [hHt, ↓reduceIte, add_zero]
              · exact h_growth t (s, false) rfl (Or.inr hHt) z hz
              · exact h_free t (s, false) rfl hSt hHt z hz
            calc R z.2.1 + qS + qH'
                ≤ (R s + if growthQuery t then (1 : ℝ≥0∞) else 0) + (qS + qH') := by
                  rw [add_assoc]; exact add_le_add_left hRz (qS + qH')
              _ = R s + qS + qH' + if growthQuery t then (1 : ℝ≥0∞) else 0 := by ring_nf
              _ ≤ B := by
                by_cases hHt : growthQuery t <;> simp only [qH', hHt, ↓reduceIte]
                · have hqH_cast : (((qH - 1 : ℕ) : ℝ≥0∞) + 1) = (qH : ℝ≥0∞) := by
                    exact_mod_cast Nat.sub_add_cancel (hcanH.resolve_left (· hHt))
                  rw [add_assoc, hqH_cast]
                · ring_nf; exact le_refl _
          exact h_tail qS hcontS hbudget
      intro n hcont' hRz_bound
      apply tsum_probOutput_mul_le_const_of_mem_support
      intro z hz
      rcases z with ⟨u, s', bad'⟩
      cases bad' with
      | false =>
          exact (ih u (hcont' u) (hcontH u) s').trans
            (by gcongr; exact hRz_bound _ hz)
      | true => simp [expectedQuerySlack_bad_eq_zero]

/-- Expected-growth resource bound for `expectedQuerySlack`.

Like `expectedQuerySlack_resource_le`, but a charged query may grow the resource by more
than one in support, as long as it grows by at most `g` **in expectation** under the
handler. Growth queries grow the resource by at most one in support, and free queries
never grow it. The accumulated slack of a computation with at most `qS` charged and `qH`
growth queries is then at most `qS·ζ + (qS·R s + qS·qH + C(qS,2)·g)·β`, the binomial
cross term coming from the expected resource increase of earlier charged queries. -/
lemma expectedQuerySlack_expected_resource_le
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery growthQuery : spec.Domain → Prop)
    [DecidablePred chargedQuery] [DecidablePred growthQuery]
    (R : σ → ℝ≥0∞) (ζ β g : ℝ≥0∞)
    (h_charged : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false → chargedQuery t →
      ∑' z : spec.Range t × σ × Bool, Pr[= z | (impl t).run p] * R z.2.1 ≤ R p.1 + g)
    (h_growth : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      ¬ chargedQuery t → growthQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1 + 1)
    (h_free : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      ¬ chargedQuery t → ¬ growthQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1)
    (oa : OracleComp spec α) {qS qH : ℕ}
    (h_qS : OracleComp.IsQueryBoundP oa chargedQuery qS)
    (h_qH : OracleComp.IsQueryBoundP oa growthQuery qH)
    (s : σ) :
    expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) oa qS (s, false)
      ≤ (qS : ℝ≥0∞) * ζ +
        ((qS : ℝ≥0∞) * R s + (qS : ℝ≥0∞) * (qH : ℝ≥0∞) +
          (qS.choose 2 : ℝ≥0∞) * g) * β := by
  induction oa using OracleComp.inductionOn generalizing qS qH s with
  | pure x => simp only [expectedQuerySlack_pure, zero_le]
  | query_bind t cont ih =>
      rw [isQueryBoundP_query_bind_iff] at h_qS h_qH
      obtain ⟨hcanS, hcontS⟩ := h_qS
      obtain ⟨hcanH, hcontH⟩ := h_qH
      by_cases hSt : chargedQuery t
      · simp only [hSt, if_true] at hcontS
        have hqS_pos : 0 < qS := hcanS.resolve_left (· hSt)
        obtain ⟨m, rfl⟩ : ∃ m, qS = m + 1 := ⟨qS - 1, by omega⟩
        rw [expectedQuerySlack_query_bind,
          expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ hSt hqS_pos]
        simp only [Nat.add_sub_cancel] at hcontS ⊢
        have h_sum_le : ∀ z : spec.Range t × σ × Bool,
            Pr[= z | (impl t).run (s, false)] *
              expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) (cont z.1) m z.2
            ≤ Pr[= z | (impl t).run (s, false)] *
                ((m : ℝ≥0∞) * ζ +
                  ((m : ℝ≥0∞) * (qH : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞) * g) * β)
              + (m : ℝ≥0∞) * β * (Pr[= z | (impl t).run (s, false)] * R z.2.1) := by
          rintro ⟨u, s', bad'⟩
          cases bad' with
          | true => simp
          | false =>
              have hIH : expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β)
                  (cont u) m (s', false)
                  ≤ (m : ℝ≥0∞) * ζ + ((m : ℝ≥0∞) * R s' + (m : ℝ≥0∞) * (qH : ℝ≥0∞)
                      + (m.choose 2 : ℝ≥0∞) * g) * β := by
                have hqH'_le : (if growthQuery t then qH - 1 else qH) ≤ qH := by
                  split_ifs <;> omega
                refine (ih u (hcontS u) (hcontH u) s').trans ?_
                gcongr
              refine (mul_le_mul_right hIH _).trans (le_of_eq ?_)
              ring
        have h_tsum : (∑' z : spec.Range t × σ × Bool,
              Pr[= z | (impl t).run (s, false)] *
                expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) (cont z.1) m z.2)
            ≤ ((m : ℝ≥0∞) * ζ +
                ((m : ℝ≥0∞) * (qH : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞) * g) * β)
              + (m : ℝ≥0∞) * β * (R s + g) := by
          refine (ENNReal.tsum_le_tsum h_sum_le).trans ?_
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
          exact add_le_add
            (mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one)
            (mul_le_mul_right (h_charged t (s, false) rfl hSt) _)
        have hch : (((m + 1).choose 2 : ℕ) : ℝ≥0∞) = (m : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞) := by
          have hch_nat : (m + 1).choose 2 = m + m.choose 2 := by
            rw [Nat.choose_succ_succ', Nat.choose_one_right]
          exact_mod_cast hch_nat
        calc ζ + R s * β + (∑' z : spec.Range t × σ × Bool,
              Pr[= z | (impl t).run (s, false)] *
                expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) (cont z.1) m z.2)
            ≤ ζ + R s * β
              + (((m : ℝ≥0∞) * ζ +
                  ((m : ℝ≥0∞) * (qH : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞) * g) * β)
                + (m : ℝ≥0∞) * β * (R s + g)) := by gcongr
          _ = ((m : ℝ≥0∞) + 1) * ζ
              + (((m : ℝ≥0∞) + 1) * R s + (m : ℝ≥0∞) * (qH : ℝ≥0∞)
                + ((m : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞)) * g) * β := by ring
          _ ≤ ((m : ℝ≥0∞) + 1) * ζ
              + (((m : ℝ≥0∞) + 1) * R s + ((m : ℝ≥0∞) + 1) * (qH : ℝ≥0∞)
                + ((m : ℝ≥0∞) + (m.choose 2 : ℝ≥0∞)) * g) * β := by
              gcongr
              exact le_self_add
          _ = ((m + 1 : ℕ) : ℝ≥0∞) * ζ
              + (((m + 1 : ℕ) : ℝ≥0∞) * R s + ((m + 1 : ℕ) : ℝ≥0∞) * (qH : ℝ≥0∞)
                + (((m + 1).choose 2 : ℕ) : ℝ≥0∞) * g) * β := by
              rw [Nat.cast_add_one, hch]
      · simp only [hSt, if_false] at hcontS
        rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free _ _ _ _ _ _ _ hSt]
        have h_z : ∀ z ∈ support ((impl t).run (s, false)),
            expectedQuerySlack impl chargedQuery (fun s => ζ + R s * β) (cont z.1) qS z.2
              ≤ (qS : ℝ≥0∞) * ζ + ((qS : ℝ≥0∞) * R s + (qS : ℝ≥0∞) * (qH : ℝ≥0∞)
                  + (qS.choose 2 : ℝ≥0∞) * g) * β := by
          rintro ⟨u, s', bad'⟩ hz
          cases bad' with
          | true => simp
          | false =>
              refine (ih u (hcontS u) (hcontH u) s').trans ?_
              by_cases hHt : growthQuery t
              · have hqH_pos : 0 < qH := hcanH.resolve_left (· hHt)
                have hqH_cast : ((qH - 1 : ℕ) : ℝ≥0∞) + 1 = (qH : ℝ≥0∞) := by
                  exact_mod_cast Nat.sub_add_cancel hqH_pos
                have hRs' : R s' ≤ R s + 1 := h_growth t (s, false) rfl hSt hHt _ hz
                rw [if_pos hHt]
                calc (qS : ℝ≥0∞) * ζ + ((qS : ℝ≥0∞) * R s'
                        + (qS : ℝ≥0∞) * ((qH - 1 : ℕ) : ℝ≥0∞)
                        + (qS.choose 2 : ℝ≥0∞) * g) * β
                    ≤ (qS : ℝ≥0∞) * ζ + ((qS : ℝ≥0∞) * (R s + 1)
                        + (qS : ℝ≥0∞) * ((qH - 1 : ℕ) : ℝ≥0∞)
                        + (qS.choose 2 : ℝ≥0∞) * g) * β := by gcongr
                  _ = (qS : ℝ≥0∞) * ζ + ((qS : ℝ≥0∞) * R s
                        + (qS : ℝ≥0∞) * (((qH - 1 : ℕ) : ℝ≥0∞) + 1)
                        + (qS.choose 2 : ℝ≥0∞) * g) * β := by ring
                  _ = (qS : ℝ≥0∞) * ζ + ((qS : ℝ≥0∞) * R s + (qS : ℝ≥0∞) * (qH : ℝ≥0∞)
                        + (qS.choose 2 : ℝ≥0∞) * g) * β := by rw [hqH_cast]
              · have hRs' : R s' ≤ R s := h_free t (s, false) rfl hSt hHt _ hz
                rw [if_neg hHt]
                gcongr
        exact tsum_probOutput_mul_le_const_of_mem_support _ h_z

/-- **Charged-read / expected-growth resource bound for `expectedQuerySlack`.**

A variant of `expectedQuerySlack_expected_resource_le` for the situation where the
*charged* queries never grow the resource (they only read it), while a separate class of
*growth* queries grows the resource by at most `g` **in expectation** (and may grow it by
arbitrarily much in support). Free queries never grow it.

Each charged query pays `R s · β` at the state `s` reached when it fires. Since the
charged queries do not grow `R`, and the growth queries grow it by at most `g` in
expectation, the resource seen by any charged query is at most `R s₀ + qH · g` in
expectation, where `s₀` is the starting state and `qH` bounds the growth queries. Folding
the `qS` charged reads against this expected cap gives accumulated slack at most
`qS · (R s₀ + qH · g) · β`, with **no** `(qS choose 2)` cross-term and **no** dependence on
the in-support growth of the resource (which `expectedQuerySlack_expected_resource_le`
would charge through its `h_growth`/`h_charged ≤ R p.1 + g` shape).

This is the fold used by the ghost-read collision charge of the Fiat-Shamir-with-aborts
Prog → Trans hop, where the charged queries are the adversary's random-oracle reads (which
only grow the *real* cache, leaving the *ghost* cache `R` untouched) and the growth queries
are the signing queries (which grow the ghost cache by the number of rejected attempts, up
to `maxAttempts − 1` in support but at most `∑_{a} p^a ≤ 1/(1−p)` in expectation). -/
lemma expectedQuerySlack_charged_read_expected_growth_le
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (chargedQuery growthQuery : spec.Domain → Prop)
    [DecidablePred chargedQuery] [DecidablePred growthQuery]
    (R : σ → ℝ≥0∞) (β g : ℝ≥0∞)
    (h_charged : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false → chargedQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1)
    (h_growth : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      ¬ chargedQuery t → growthQuery t →
      ∑' z : spec.Range t × σ × Bool, Pr[= z | (impl t).run p] * R z.2.1 ≤ R p.1 + g)
    (h_free : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = false →
      ¬ chargedQuery t → ¬ growthQuery t →
      ∀ z ∈ support ((impl t).run p), R z.2.1 ≤ R p.1)
    (oa : OracleComp spec α) {qS qH : ℕ}
    (h_qS : OracleComp.IsQueryBoundP oa chargedQuery qS)
    (h_qH : OracleComp.IsQueryBoundP oa growthQuery qH)
    (s : σ) :
    expectedQuerySlack impl chargedQuery (fun s => R s * β) oa qS (s, false)
      ≤ (qS : ℝ≥0∞) * (R s + (qH : ℝ≥0∞) * g) * β := by
  induction oa using OracleComp.inductionOn generalizing qS qH s with
  | pure x => simp only [expectedQuerySlack_pure, zero_le]
  | query_bind t cont ih =>
      rw [isQueryBoundP_query_bind_iff] at h_qS h_qH
      obtain ⟨hcanS, hcontS⟩ := h_qS
      obtain ⟨hcanH, hcontH⟩ := h_qH
      by_cases hSt : chargedQuery t
      · -- Charged read: pays `R s · β`, does not grow `R`, continuation budget `qS - 1`.
        simp only [hSt, if_true] at hcontS
        have hqS_pos : 0 < qS := hcanS.resolve_left (· hSt)
        obtain ⟨m, rfl⟩ : ∃ m, qS = m + 1 := ⟨qS - 1, by omega⟩
        rw [expectedQuerySlack_query_bind,
          expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ hSt hqS_pos]
        simp only [Nat.add_sub_cancel] at hcontS ⊢
        -- A charged query is not a growth query budget-wise: continuation keeps budget `qH`.
        have hqH'_le : (if growthQuery t then qH - 1 else qH) ≤ qH := by split_ifs <;> omega
        have h_tsum_le :
            (∑' z : spec.Range t × σ × Bool,
              Pr[= z | (impl t).run (s, false)] *
                expectedQuerySlack impl chargedQuery (fun s => R s * β) (cont z.1) m z.2)
              ≤ (m : ℝ≥0∞) * (R s + (qH : ℝ≥0∞) * g) * β := by
          apply tsum_probOutput_mul_le_const_of_mem_support
          rintro ⟨u, s', bad'⟩ hz
          cases bad' with
          | true => simp
          | false =>
              refine (ih u (hcontS u) (hcontH u) s').trans ?_
              have hRs' : R s' ≤ R s := h_charged t (s, false) rfl hSt _ hz
              gcongr
        calc R s * β +
              (∑' z : spec.Range t × σ × Bool,
                Pr[= z | (impl t).run (s, false)] *
                  expectedQuerySlack impl chargedQuery (fun s => R s * β) (cont z.1) m z.2)
            ≤ R s * β + (m : ℝ≥0∞) * (R s + (qH : ℝ≥0∞) * g) * β := by gcongr
          _ ≤ (R s + (qH : ℝ≥0∞) * g) * β + (m : ℝ≥0∞) * (R s + (qH : ℝ≥0∞) * g) * β := by
              gcongr
              exact le_self_add
          _ = ((m + 1 : ℕ) : ℝ≥0∞) * (R s + (qH : ℝ≥0∞) * g) * β := by push_cast; ring
      · -- Uncharged query: no charge. Split growth vs. free.
        simp only [hSt, if_false] at hcontS
        rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free _ _ _ _ _ _ _ hSt]
        by_cases hHt : growthQuery t
        · -- Growth query: `R` grows by `≤ g` in expectation, charged budget unchanged.
          have hqH_pos : 0 < qH := hcanH.resolve_left (· hHt)
          obtain ⟨h, rfl⟩ : ∃ h, qH = h + 1 := ⟨qH - 1, by omega⟩
          simp only [hHt, if_true] at hcontH
          simp only [Nat.add_sub_cancel] at hcontH
          calc (∑' z : spec.Range t × σ × Bool,
                Pr[= z | (impl t).run (s, false)] *
                  expectedQuerySlack impl chargedQuery (fun s => R s * β) (cont z.1) qS z.2)
              ≤ ∑' z : spec.Range t × σ × Bool,
                  Pr[= z | (impl t).run (s, false)] *
                    ((qS : ℝ≥0∞) * (R z.2.1 + (h : ℝ≥0∞) * g) * β) :=
                ENNReal.tsum_le_tsum fun z => by
                  obtain ⟨u, s', bad'⟩ := z
                  cases bad' with
                  | true => simp
                  | false => exact mul_le_mul_right (ih u (hcontS u) (hcontH u) s') _
            _ = (qS : ℝ≥0∞) * β *
                  (∑' z : spec.Range t × σ × Bool,
                    Pr[= z | (impl t).run (s, false)] * (R z.2.1 + (h : ℝ≥0∞) * g)) := by
                rw [← ENNReal.tsum_mul_left]
                refine tsum_congr fun z => ?_
                ring
            _ ≤ (qS : ℝ≥0∞) * β * ((R s + g) + (h : ℝ≥0∞) * g) := by
                gcongr
                calc (∑' z : spec.Range t × σ × Bool,
                      Pr[= z | (impl t).run (s, false)] * (R z.2.1 + (h : ℝ≥0∞) * g))
                    = (∑' z, Pr[= z | (impl t).run (s, false)] * R z.2.1)
                        + ∑' z, Pr[= z | (impl t).run (s, false)] * ((h : ℝ≥0∞) * g) := by
                      rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]
                  _ ≤ (R s + g) + (h : ℝ≥0∞) * g := by
                      refine add_le_add (h_growth t (s, false) rfl hSt hHt) ?_
                      rw [ENNReal.tsum_mul_right]
                      exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one
            _ = (qS : ℝ≥0∞) * (R s + ((h + 1 : ℕ) : ℝ≥0∞) * g) * β := by push_cast; ring
        · -- Free query: `R` does not grow, budgets unchanged.
          simp only [hHt, if_false] at hcontH
          apply tsum_probOutput_mul_le_const_of_mem_support
          rintro ⟨u, s', bad'⟩ hz
          cases bad' with
          | true => simp
          | false =>
              refine (ih u (hcontS u) (hcontH u) s').trans ?_
              have hRs' : R s' ≤ R s := h_free t (s, false) rfl hSt hHt _ hz
              gcongr

/-- **Constant-ε version of the bridge as a corollary of the state-dep version.**

This is the ENNReal-form analogue of the existing real-valued
`tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad`. It demonstrates that
the state-dep version subsumes the constant-ε version: instantiate
`ε := fun _ => ENNReal.ofReal ε_const` and bound `expectedQuerySlack` by
`queryBudget * ENNReal.ofReal ε_const`. -/
theorem ofReal_tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ε : ℝ≥0∞)
    (chargedQuery : spec.Domain → Prop) [DecidablePred chargedQuery]
    (h_step_tv_charged : ∀ (t : spec.Domain), chargedQuery t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false))) ≤ ε)
    (h_step_eq_uncharged : ∀ (t : spec.Domain), ¬ chargedQuery t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {queryBudget : ℕ}
    (h_qb : OracleComp.IsQueryBoundP oa chargedQuery queryBudget)
    (p : σ × Bool) :
    ENNReal.ofReal (tvDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p))
      ≤ queryBudget * ε
        + Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run p] := by
  have h_step_tv_charged' : ∀ (t : spec.Domain), chargedQuery t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)))
        ≤ (fun _ : σ => ε) s := h_step_tv_charged
  refine le_trans
    (ofReal_tvDist_simulateQ_run_le_expectedQuerySlack_plus_probEvent_output_bad
      impl₁ impl₂ chargedQuery (fun _ => ε) h_step_tv_charged'
      h_step_eq_uncharged h_mono₁ oa h_qb p) ?_
  gcongr
  exact expectedQuerySlack_const_le_queryBudget_mul impl₁ chargedQuery ε oa h_qb p

end IdenticalUntilBadEpsilonStateDep

end OracleComp.ProgramLogic.Relational
