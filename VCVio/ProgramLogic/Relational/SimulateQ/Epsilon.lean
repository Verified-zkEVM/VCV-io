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

/-!
# Uniform and selectively charged simulation slack
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

/-! ## ε-perturbed "identical until bad" with output bad flag

These lemmas generalize `tvDist_simulateQ_le_probEvent_output_bad` from EXACT agreement on
the no-bad path to ε-CLOSE agreement: the per-step TV distance between the two oracle
implementations may be at most `ε` (instead of zero) on the no-bad path. Combined with a
query bound `q` on the computation, the total bound becomes `q*ε + Pr[bad]`.

The standard "identical until bad" bound (`Pr[bad]`) is recovered as the special case `ε = 0`.

**Application**: HVZK simulation in Fiat-Shamir, where the simulated transcript is only
`ε`-close to the real transcript per query (not exactly equal), but a "programming
collision" event captures the catastrophic failure mode (collision between programmed hash
entries). The total reduction loss is `qS·ε + Pr[collision]`. -/

section IdenticalUntilBadEpsilon

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [IsUniformSpec spec']
variable {α : Type} {σ : Type}

omit [IsUniformSpec spec'] in
/-- "Bad propagation": starting from a bad state, every output of the simulation has the
bad flag set. This generalizes the per-step `h_mono` hypothesis to the full simulation. -/
private lemma mem_support_simulateQ_run_of_bad
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (h_mono : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (p : σ × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((simulateQ impl oa).run p), z.2.2 = true := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure x =>
      intro z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hp
  | query_bind t cont ih =>
      intro z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion,
        exists_prop] at hz
      obtain ⟨⟨u, p'⟩, h_mem, h_z⟩ := hz
      have hp' : p'.2 = true := h_mono t p hp (u, p') h_mem
      exact ih u p' hp' z h_z

/-- Under bad-monotonicity, a simulation started from a bad state has bad output probability
exactly `1` (using the canonical `MonadLiftT (OracleComp spec) PMF` to ensure no failure
mass). -/
private lemma probEvent_simulateQ_run_bad_eq_one_of_bad
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (h_mono : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (p : σ × Bool) (hp : p.2 = true) :
    Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl oa).run p] = 1 := by
  rw [probEvent_eq_one_iff]
  exact ⟨by simp, mem_support_simulateQ_run_of_bad impl h_mono oa p hp⟩

/-! ### Exact identical-until-bad with output bad flag: joint heterogeneous variant

`tvDist_simulateQ_le_probEvent_output_bad` fixes the inner monad to `OracleComp spec`
over the same spec as the simulated computation, and projects the conclusion to the
output marginal. The variant here generalizes the inner monad to `OracleComp spec'` and
keeps the conclusion on the **joint** output-and-state distribution, which is what a
game with a state-dependent continuation (e.g. a final verification step reading the
run's cache) consumes. -/

private lemma probOutput_simulateQ_run_eq_zero_of_output_bad'
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (h_mono : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (p : σ × Bool) (hp : p.2 = true) (x : α) (s : σ) :
    Pr[= (x, (s, false)) | (simulateQ impl oa).run p] = 0 := by
  refine probOutput_eq_zero_of_not_mem_support fun h => ?_
  simpa using mem_support_simulateQ_run_of_bad impl h_mono oa p hp (x, (s, false)) h

private lemma probOutput_simulateQ_run_eq_of_not_output_bad'
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) :
    Pr[= (x, (s, false)) | (simulateQ impl₁ oa).run (s₀, false)] =
      Pr[= (x, (s, false)) | (simulateQ impl₂ oa).run (s₀, false)] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    simp only [simulateQ_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr ?_
    rintro ⟨u, ⟨s', b⟩⟩
    cases b with
    | true =>
      have h₁ : Pr[= (x, (s, false)) | (simulateQ impl₁ (oa u)).run (s', true)] = 0 :=
        probOutput_simulateQ_run_eq_zero_of_output_bad' impl₁ h_mono₁ (oa u)
          (s', true) rfl x s
      have h₂ : Pr[= (x, (s, false)) | (simulateQ impl₂ (oa u)).run (s', true)] = 0 :=
        probOutput_simulateQ_run_eq_zero_of_output_bad' impl₂ h_mono₂ (oa u)
          (s', true) rfl x s
      simp [h₁, h₂]
    | false =>
      rw [h_agree_good t s₀ u s', ih u s']

open scoped Classical in
/-- **Bad-event equality for exact identical-until-bad**, with the inner monad over an
arbitrary uniform spec `spec'`. Two state-extended implementations that agree on every
non-bad output transition from a non-bad input state (`h_agree_good`) and are bad-input
monotone (`h_mono₁`, `h_mono₂`) flip the output bad flag with *exactly the same*
probability. This is the equality counterpart of `tvDist_simulateQ_run_le_probEvent_output_bad`
(which bounds only the TV distance): the bad marginals coincide because the two runs differ
only on the already-bad trajectory, where both flags read `true`.

Applying it: because the conclusion is an equality, a bound on the flag probability proved in
either world transports to the other, which is what lets the TV-distance results in this
section quantify the loss against `impl₁` alone.

Pinning the inner monad to the simulated spec itself gives the same statement over
`OracleComp spec`; that same-spec form is the private `probEvent_output_bad_eq` in
`SimulateQ.Basic`, which backs `tvDist_simulateQ_le_probEvent_output_bad`. -/
theorem probEvent_output_bad_eq'
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true) (oa : OracleComp spec α) (s₀ : σ) :
    Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run (s₀, false)] =
      Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₂ oa).run (s₀, false)] := by
  set sim₁ := (simulateQ impl₁ oa).run (s₀, false)
  set sim₂ := (simulateQ impl₂ oa).run (s₀, false)
  have h₁ := probEvent_compl sim₁ (fun z : α × σ × Bool => z.2.2 = true)
  have h₂ := probEvent_compl sim₂ (fun z : α × σ × Bool => z.2.2 = true)
  simp only [NeverFail.probFailure_eq_zero, tsub_zero] at h₁ h₂
  -- both runs put equal mass on every unflagged endpoint, hence on the unflagged event
  have h_not_eq :
      Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₁] =
        Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₂] := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
    refine tsum_congr ?_
    rintro ⟨a, s, _ | _⟩
    · simpa using probOutput_simulateQ_run_eq_of_not_output_bad' impl₁ impl₂ h_agree_good
        h_mono₁ h_mono₂ oa s₀ a s
    · simp
  -- cancel that common unflagged mass in `flagged + unflagged = 1` on both sides
  rw [h_not_eq] at h₁
  exact (ENNReal.add_left_inj (ne_top_of_le_ne_top one_ne_top probEvent_le_one)).mp <|
    h₁.trans h₂.symm

/-- "Identical until bad" with an output bad flag, on the **joint** output-and-state
distribution, with the inner monad over an arbitrary uniform spec `spec'`.

Two state-extended oracle implementations that agree on non-bad output transitions from
non-bad input states (and are bad-input monotone) produce simulated runs whose joint
output-and-state distributions are within the probability of the flag firing in the run
of `impl₁`. Unlike `tvDist_simulateQ_le_probEvent_output_bad`, the conclusion keeps the
final state, so a state-dependent continuation (e.g. verification against the final
cache) can be appended on both sides. -/
theorem tvDist_simulateQ_run_le_probEvent_output_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (oa : OracleComp spec α) (s₀ : σ)
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true) :
    tvDist ((simulateQ impl₁ oa).run (s₀, false))
        ((simulateQ impl₂ oa).run (s₀, false))
      ≤ Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal := by
  classical
  set sim₁ := (simulateQ impl₁ oa).run (s₀, false)
  set sim₂ := (simulateQ impl₂ oa).run (s₀, false)
  have h_eq : ∀ (z : α × σ × Bool), ¬(z.2.2 = true) → Pr[= z | sim₁] = Pr[= z | sim₂] := by
    rintro ⟨x, s, b⟩ hb
    have hb' : b = false := Bool.eq_false_of_not_eq_true hb
    subst hb'
    exact probOutput_simulateQ_run_eq_of_not_output_bad' impl₁ impl₂ h_agree_good
      h_mono₁ h_mono₂ oa s₀ x s
  have h_event_eq :
      Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁] =
        Pr[fun z : α × σ × Bool => z.2.2 = true | sim₂] :=
    probEvent_output_bad_eq' impl₁ impl₂ h_agree_good h_mono₁ h_mono₂ oa s₀
  exact tvDist_le_probEvent_of_probOutput_eq_of_not (mx := sim₁) (my := sim₂)
    (fun z : α × σ × Bool => z.2.2 = true) h_eq h_event_eq

/-! ### ε-perturbed identical-until-bad: helper lemmas (in dependency order) -/

/-- Bound `∑' z, p_z.toReal * tvDist (f₁ z) (f₂ z)` by `c + Pr[bad | mx >>= f₁]`,
given that each summand is bounded by `p_z * (c + Pr[bad | f₁ z])`. The constant `c`
is intended to be `(q - 1) · ε` from the inductive hypothesis. -/
private theorem tsum_probOutput_mul_tvDist_le_const_plus_probEvent_bad
    {β : Type} (mx : OracleComp spec' β) (f₁ f₂ : β → OracleComp spec' (α × σ × Bool))
    {c : ℝ} (hc : 0 ≤ c)
    (h_summand_le : ∀ z : β,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤
        Pr[= z | mx].toReal * (c +
          Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal)) :
    (∑' z : β, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
      ≤ c + Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁].toReal := by
  have h_p_sum_le_one : (∑' z : β, Pr[= z | mx]) ≤ 1 := tsum_probOutput_le_one
  have h_p_sum_ne_top : (∑' z : β, Pr[= z | mx]) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top h_p_sum_le_one
  have h_p_summable : Summable (fun z : β => Pr[= z | mx].toReal) :=
    ENNReal.summable_toReal h_p_sum_ne_top
  have h_lhs_summand_nn : ∀ z : β, 0 ≤ Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) :=
    fun z => by positivity
  have h_lhs_summand_le : ∀ z : β,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤ Pr[= z | mx].toReal :=
    fun z => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)
  have h_lhs_summable : Summable
      (fun z : β => Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z)) :=
    Summable.of_nonneg_of_le h_lhs_summand_nn h_lhs_summand_le h_p_summable
  have h_b_z_le_one : ∀ z : β,
      Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal ≤ 1 := fun z => by
    simpa using ENNReal.toReal_mono one_ne_top probEvent_le_one
  have h_rhs_summand_nn : ∀ z : β, 0 ≤ Pr[= z | mx].toReal *
      (c + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal) :=
    fun z => mul_nonneg ENNReal.toReal_nonneg
      (add_nonneg hc ENNReal.toReal_nonneg)
  have h_rhs_summand_le : ∀ z : β,
      Pr[= z | mx].toReal * (c + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal) ≤
      Pr[= z | mx].toReal * (c + 1) := fun z => by
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    linarith [h_b_z_le_one z]
  have h_rhs_summable : Summable (fun z : β => Pr[= z | mx].toReal *
      (c + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal)) :=
    Summable.of_nonneg_of_le h_rhs_summand_nn h_rhs_summand_le
      (h_p_summable.mul_right (c + 1))
  have h_le_rhs :
      (∑' z : β, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
        ≤ ∑' z : β, Pr[= z | mx].toReal *
          (c + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal) :=
    Summable.tsum_le_tsum h_summand_le h_lhs_summable h_rhs_summable
  refine le_trans h_le_rhs ?_
  have h_distrib_summable_a : Summable
      (fun z : β => Pr[= z | mx].toReal * c) :=
    h_p_summable.mul_right _
  have h_distrib_summable_b : Summable
      (fun z : β => Pr[= z | mx].toReal *
        Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal) :=
    Summable.of_nonneg_of_le
      (fun z => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun z => mul_le_of_le_one_right ENNReal.toReal_nonneg (h_b_z_le_one z))
      h_p_summable
  have h_split :
      (∑' z : β, Pr[= z | mx].toReal *
        (c + Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal))
        = (∑' z : β, Pr[= z | mx].toReal * c) +
          (∑' z : β, Pr[= z | mx].toReal *
            Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal) := by
    rw [← Summable.tsum_add h_distrib_summable_a h_distrib_summable_b]
    refine tsum_congr fun z => ?_
    ring
  rw [h_split]
  have h_first_sum :
      (∑' z : β, Pr[= z | mx].toReal * c) = c := by
    rw [tsum_mul_right]
    have h_one : (∑' z : β, Pr[= z | mx].toReal) = 1 := by
      rw [show (∑' z : β, Pr[= z | mx].toReal) = ((∑' z : β, Pr[= z | mx])).toReal from
        (ENNReal.tsum_toReal_eq fun z => by
          have h := probOutput_le_one (mx := mx) (x := z)
          exact ne_top_of_le_ne_top one_ne_top h).symm]
      simp only [tsum_probOutput_eq_sub, probFailure_eq_zero, tsub_zero]
      simp
    rw [h_one, one_mul]
  have h_second_sum :
      (∑' z : β, Pr[= z | mx].toReal *
        Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z].toReal)
        = Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁].toReal := by
    have h_term_ne_top : ∀ z : β, Pr[= z | mx] *
        Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z] ≠ ⊤ := fun z => by
      have h₁ : Pr[= z | mx] ≤ 1 := probOutput_le_one
      have h₂ : Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z] ≤ 1 := probEvent_le_one
      have h_le : Pr[= z | mx] * Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z] ≤ 1 :=
        mul_le_one' h₁ h₂
      exact ne_top_of_le_ne_top one_ne_top h_le
    rw [show
      Pr[fun w : α × σ × Bool => w.2.2 = true | mx >>= f₁] =
        ∑' z : β, Pr[= z | mx] *
          Pr[fun w : α × σ × Bool => w.2.2 = true | f₁ z] from
        probEvent_bind_eq_tsum mx f₁ _,
      ENNReal.tsum_toReal_eq h_term_ne_top]
    refine tsum_congr fun z => ?_
    exact ENNReal.toReal_mul.symm
  rw [h_first_sum, h_second_sum]

/-- The `query_bind` (`p.2 = false`) inductive step: given the per-continuation IH bound
(parameterized by `q - 1`), combine the triangle inequality, the two `tvDist_bind_*_le`
bounds, and the algebraic distribution to get the `q · ε + Pr[bad]` bound. -/
private theorem tvDist_simulateQ_run_query_bind_le
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_step_tv : ∀ (t : spec.Domain) (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec α)
    {q : ℕ} (hq_pos : 0 < q)
    (ih : ∀ (u : spec.Range t) (p' : σ × Bool),
      tvDist ((simulateQ impl₁ (cont u)).run p')
          ((simulateQ impl₂ (cont u)).run p')
        ≤ ↑(q - 1) * ε + Pr[ fun w : α × σ × Bool => w.2.2 = true |
            (simulateQ impl₁ (cont u)).run p'].toReal)
    (s : σ) :
    tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false))
      ≤ ↑q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ (query t >>= cont)).run (s, false)].toReal := by
  set sim₁ : OracleComp spec' (α × σ × Bool) :=
    (simulateQ impl₁ (query t >>= cont)).run (s, false) with hsim₁_def
  set sim₂ : OracleComp spec' (α × σ × Bool) :=
    (simulateQ impl₂ (query t >>= cont)).run (s, false) with hsim₂_def
  set f₁ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₁ (cont z.1)).run z.2 with hf₁_def
  set f₂ : spec.Range t × σ × Bool → OracleComp spec' (α × σ × Bool) :=
    fun z => (simulateQ impl₂ (cont z.1)).run z.2 with hf₂_def
  set mx : OracleComp spec' (spec.Range t × σ × Bool) := (impl₁ t).run (s, false) with hmx_def
  set my : OracleComp spec' (spec.Range t × σ × Bool) := (impl₂ t).run (s, false) with hmy_def
  have hsim₁_eq : sim₁ = mx >>= f₁ := by
    simp [hsim₁_def, hmx_def, hf₁_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  have hsim₂_eq : sim₂ = my >>= f₂ := by
    simp [hsim₂_def, hmy_def, hf₂_def, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
  set mid : OracleComp spec' (α × σ × Bool) := mx >>= f₂ with hmid_def
  have h_tri : tvDist sim₁ sim₂ ≤ tvDist sim₁ mid + tvDist mid sim₂ :=
    tvDist_triangle _ _ _
  have h_second : tvDist mid sim₂ ≤ ε := by
    rw [hmid_def, hsim₂_eq]
    exact le_trans (tvDist_bind_right_le _ _ _) (h_step_tv t s)
  have h_first_raw :
      tvDist sim₁ mid ≤ ∑' z : spec.Range t × σ × Bool,
        Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) := by
    rw [hsim₁_eq, hmid_def]
    exact tvDist_bind_left_le _ _ _
  have h_summand_le : ∀ z : spec.Range t × σ × Bool,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤
        Pr[= z | mx].toReal * (↑(q - 1) * ε + Pr[fun w : α × σ × Bool => w.2.2 = true |
            f₁ z].toReal) := fun z => by
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    simpa [hf₁_def, hf₂_def] using ih z.1 z.2
  have h_const_nonneg : (0 : ℝ) ≤ ↑(q - 1) * ε := by positivity
  have h_first :
      tvDist sim₁ mid ≤ ↑(q - 1) * ε +
        Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁].toReal := by
    refine le_trans h_first_raw ?_
    have h_helper := tsum_probOutput_mul_tvDist_le_const_plus_probEvent_bad
      (mx := mx) (f₁ := f₁) (f₂ := f₂) (c := ↑(q - 1) * ε) h_const_nonneg h_summand_le
    rw [hsim₁_eq]
    exact h_helper
  have hq_arith : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
    have h1 : 1 ≤ q := hq_pos
    have h2 : ((q - 1 : ℕ) + 1 : ℕ) = q := Nat.sub_add_cancel h1
    have h3 : (((q - 1 : ℕ) + 1 : ℕ) : ℝ) = (q : ℝ) := by exact_mod_cast h2
    simpa using h3
  calc tvDist sim₁ sim₂
      ≤ tvDist sim₁ mid + tvDist mid sim₂ := h_tri
    _ ≤ (↑(q - 1) * ε + Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁].toReal) + ε :=
        add_le_add h_first h_second
    _ = (↑(q - 1) + 1) * ε + Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁].toReal := by ring
    _ = ↑q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁].toReal := by rw [hq_arith]

/-- Auxiliary inductive lemma for `tvDist_simulateQ_le_qeps_plus_probEvent_output_bad`. Bounds
the TV distance on the **joint** (state-included) distribution, for arbitrary starting state
`p` (whether the bad flag is set or not).

The proof inducts on `oa`:
- `pure x`: both simulations equal `pure (x, p)`, so `tvDist = 0` and the RHS is non-negative.
- `query t >>= cont`: case on `p.2`.
  - `true`: by bad-monotonicity, `Pr[bad | sim₁] = 1`, and `tvDist ≤ 1` always.
  - `false`: see `tvDist_simulateQ_run_query_bind_le`. -/
private theorem tvDist_simulateQ_run_le_qeps_plus_probEvent_output_bad_aux
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_step_tv : ∀ (t : spec.Domain) (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {q : ℕ}
    (h_qb : OracleComp.IsTotalQueryBound oa q) (p : σ × Bool) :
    tvDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p)
      ≤ q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run p].toReal := by
  induction oa using OracleComp.inductionOn generalizing q p with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, tvDist_self]
      positivity
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true =>
          have h_bad₁ : Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ (query t >>= cont)).run (s, true)] = 1 :=
            probEvent_simulateQ_run_bad_eq_one_of_bad impl₁ h_mono₁
              (query t >>= cont) (s, true) rfl
          have h_tv_le_one :
              tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, true))
                  ((simulateQ impl₂ (query t >>= cont)).run (s, true)) ≤ 1 :=
            tvDist_le_one _ _
          have h_target_ge_one :
              (1 : ℝ) ≤ ↑q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
                (simulateQ impl₁ (query t >>= cont)).run (s, true)].toReal := by
            rw [h_bad₁]
            simp only [ENNReal.toReal_one]
            have hqε : (0 : ℝ) ≤ ↑q * ε := by positivity
            linarith
          exact le_trans h_tv_le_one h_target_ge_one
      | false =>
          have hq_pos : 0 < q := h_qb.1
          have hq_cont : ∀ u, OracleComp.IsTotalQueryBound (cont u) (q - 1) := h_qb.2
          exact tvDist_simulateQ_run_query_bind_le impl₁ impl₂ hε h_step_tv t cont hq_pos
            (fun u p' => ih u (hq_cont u) p') s

/-- **ε-perturbed identical-until-bad with output bad flag.**

If two stateful oracle implementations are `ε`-close in TV distance per step on the no-bad
path (rather than exactly equal, as in `tvDist_simulateQ_le_probEvent_output_bad`), and `oa`
makes at most `q` queries, then the TV distance between the two simulated output
distributions is at most `q * ε + Pr[bad]`, the bad probability being that of `impl₁`
finishing with its flag set.

Only `impl₁` needs bad-flag monotonicity, since the bad probability on the right is read off
`impl₁`; beyond `h_step_tv` the implementation `impl₂` is unconstrained, and the two may
diverge arbitrarily once the flag is set. At `ε = 0` the bound degenerates to the exact one
of `tvDist_simulateQ_le_probEvent_output_bad`, which phrases per-step agreement as an
equality of good-transition probabilities and constrains `impl₂` as well.

When applying: the left-hand side compares output marginals (`StateT.run'`) while the right
reads the flag off the joint run (`StateT.run`), which is what keeps the bad event
observable; `q` is implicit and is fixed by `h_qb`, which charges *every* query, so `q` is a
total query count.

Two nearby refinements weaken the uniform factor `q * ε`:
`tvDist_simulateQ_le_queryBound_mul_slack_plus_probEvent_bad` charges only the queries in a
designated subset (the rest being pointwise equal), and
`ofReal_tvDist_simulateQ_le_expectedQuerySlack_plus_probEvent_output_bad` uses a state-dependent
slack and bounds it through `expectedQuerySlack` in `ℝ≥0∞`. -/
theorem tvDist_simulateQ_le_qeps_plus_probEvent_output_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec'))) {ε : ℝ} (hε : 0 ≤ ε)
    (h_step_tv : ∀ (t : spec.Domain) (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true) (oa : OracleComp spec α) {q : ℕ}
    (h_qb : OracleComp.IsTotalQueryBound oa q) (s₀ : σ) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false)) ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ q * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal :=
  -- Discard the state through the data-processing inequality for `Prod.fst`, then bound the
  -- joint (output, state, flag) distributions by the inductive lemma.
  (tvDist_map_le Prod.fst _ _).trans (tvDist_simulateQ_run_le_qeps_plus_probEvent_output_bad_aux
    impl₁ impl₂ hε h_step_tv h_mono₁ oa h_qb (s₀, false))

end IdenticalUntilBadEpsilon

/-! ### Selective ε-perturbed identical-until-bad

A refinement of `tvDist_simulateQ_le_qeps_plus_probEvent_output_bad` where the per-step ε
bound applies only to a designated subset `S` of queries (the "costly" or "perturbed"
queries), and the impls are pointwise equal on the complement (the "free" queries). The
bound counts only the charged queries, giving a tight `q · ε` instead of `q_total · ε`.

This is essential for cryptographic reductions where, e.g., signing-oracle queries are
ε-close to a simulator (HVZK guarantee) but uniform / RO queries are exactly equal (both
sides forward through the same RO cache). Direct application of the uniform-ε lemma would
give `(qS + qH) · ε`, but for tight bounds we want `q · ε`. -/

section IdenticalUntilBadEpsilonSelective

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [IsUniformSpec spec']
variable {α : Type} {σ : Type}

/-- The `query_bind` step for a "free" query (impls pointwise equal on the no-bad branch).
The budget `qS` is preserved (no decrement), since a uncharged query doesn't count toward the
charged query bound. -/
private theorem tvDist_simulateQ_run_free_query_bind_le
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (t : spec.Domain) (h_step_eq : ∀ (p : σ × Bool), (impl₁ t).run p = (impl₂ t).run p)
    (cont : spec.Range t → OracleComp spec α) {qS : ℕ}
    (ih : ∀ (u : spec.Range t) (p' : σ × Bool),
      tvDist ((simulateQ impl₁ (cont u)).run p')
          ((simulateQ impl₂ (cont u)).run p')
        ≤ ↑qS * ε + Pr[ fun w : α × σ × Bool => w.2.2 = true |
            (simulateQ impl₁ (cont u)).run p'].toReal)
    (s : σ) :
    tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, false))
        ((simulateQ impl₂ (query t >>= cont)).run (s, false))
      ≤ ↑qS * ε + Pr[ fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ (query t >>= cont)).run (s, false)].toReal := by
  set mx : OracleComp spec' (spec.Range t × σ × Bool) := (impl₁ t).run (s, false) with hmx_def
  have hmy_eq : (impl₂ t).run (s, false) = mx := (h_step_eq (s, false)).symm
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
  have h_bd : tvDist (mx >>= f₁) (mx >>= f₂)
      ≤ ∑' z : spec.Range t × σ × Bool, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) :=
    tvDist_bind_left_le _ _ _
  have h_summand_le : ∀ z : spec.Range t × σ × Bool,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤
        Pr[= z | mx].toReal * (↑qS * ε + Pr[fun w : α × σ × Bool => w.2.2 = true |
            f₁ z].toReal) := fun z => by
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    simpa [hf₁_def, hf₂_def] using ih z.1 z.2
  have h_qSε_nonneg : (0 : ℝ) ≤ ↑qS * ε := by positivity
  rw [hsim₁_eq, hsim₂_eq]
  exact le_trans h_bd
    (tsum_probOutput_mul_tvDist_le_const_plus_probEvent_bad
      (mx := mx) (f₁ := f₁) (f₂ := f₂) (c := ↑qS * ε) h_qSε_nonneg h_summand_le)

/-- Auxiliary inductive lemma for the selective ε-perturbed bound.

Inducts on `oa` and case-splits each query on whether it is charged
(use the per-step argument and decrement the budget) or uncharged
(`tvDist_simulateQ_run_free_query_bind_le`, preserving the budget). -/
private theorem tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad_aux
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (S : ι → Prop) [DecidablePred S]
    (h_step_tv_S : ∀ (t : ι), S t → ∀ (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_step_eq_nS : ∀ (t : ι), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : ι) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBoundP oa S qS)
    (p : σ × Bool) :
    tvDist ((simulateQ impl₁ oa).run p) ((simulateQ impl₂ oa).run p)
      ≤ qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run p].toReal := by
  -- Construct a global per-step bound `tvDist ≤ ε` that holds for all queries.
  -- Charged queries use `h_step_tv_S`; uncharged queries are pointwise equal.
  have h_step_tv_global : ∀ (t' : ι) (s' : σ),
      tvDist ((impl₁ t').run (s', false)) ((impl₂ t').run (s', false)) ≤ ε := by
    intro t' s'
    by_cases hSt' : S t'
    · exact h_step_tv_S t' hSt' s'
    · rw [h_step_eq_nS t' hSt' (s', false), tvDist_self]; exact hε
  induction oa using OracleComp.inductionOn generalizing qS p with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, tvDist_self]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) ENNReal.toReal_nonneg
  | query_bind t cont ih =>
      rcases p with ⟨s, b⟩
      cases b with
      | true =>
          have h_bad₁ : Pr[fun z : α × σ × Bool => z.2.2 = true |
              (simulateQ impl₁ (query t >>= cont)).run (s, true)] = 1 :=
            probEvent_simulateQ_run_bad_eq_one_of_bad impl₁ h_mono₁
              (query t >>= cont) (s, true) rfl
          have h_tv_le_one :
              tvDist ((simulateQ impl₁ (query t >>= cont)).run (s, true))
                  ((simulateQ impl₂ (query t >>= cont)).run (s, true)) ≤ 1 :=
            tvDist_le_one _ _
          have h_target_ge_one :
              (1 : ℝ) ≤ ↑qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
                (simulateQ impl₁ (query t >>= cont)).run (s, true)].toReal := by
            rw [h_bad₁]
            simp only [ENNReal.toReal_one]
            have hqε : (0 : ℝ) ≤ ↑qS * ε := by positivity
            linarith
          exact le_trans h_tv_le_one h_target_ge_one
      | false =>
          rw [isQueryBoundP_query_bind_iff] at h_qb
          obtain ⟨h_can, h_cont⟩ := h_qb
          by_cases hSt : S t
          · -- Costly query: use the existing helper with budget `qS`, decrementing to `qS - 1`.
            simp only [if_pos hSt] at h_cont
            have hqS_pos : 0 < qS := h_can.resolve_left (· hSt)
            exact tvDist_simulateQ_run_query_bind_le impl₁ impl₂ hε h_step_tv_global
              t cont hqS_pos
              (fun u p' => ih u (h_cont u) p') s
          · -- Free query: impls equal here; preserve the `qS` budget through the recursion.
            simp only [if_neg hSt] at h_cont
            exact tvDist_simulateQ_run_free_query_bind_le impl₁ impl₂ hε t
              (h_step_eq_nS t hSt) cont
              (fun u p' => ih u (h_cont u) p') s

/-- **Selective ε-perturbed identical-until-bad with output bad flag.**

Like `tvDist_simulateQ_le_qeps_plus_probEvent_output_bad`, but the per-step ε bound
applies only to queries `t` satisfying a designated predicate `S` (the "costly" queries),
and the impls are pointwise equal on `¬ S` (the "free" queries). The bound counts only
the charged queries (via `IsQueryBoundP oa S qS`), giving the tight `q · ε` instead of the
trivial `q_total · ε` from the uniform-ε lemma.

The intended use is for cryptographic reductions: e.g., for Fiat-Shamir signing-oracle
swaps, the "costly" queries are signing queries (HVZK gives per-query ε bound) and the
"free" queries are the underlying spec queries (uniform sampling and RO caching, where
both sides forward through the same `baseSim`). -/
theorem tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (S : ι → Prop) [DecidablePred S]
    (h_step_tv_S : ∀ (t : ι), S t → ∀ (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_step_eq_nS : ∀ (t : ι), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : ι) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBoundP oa S qS)
    (s₀ : σ) :
    tvDist ((simulateQ impl₁ oa).run (s₀, false))
        ((simulateQ impl₂ oa).run (s₀, false))
      ≤ qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal :=
  tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad_aux
    impl₁ impl₂ hε S h_step_tv_S h_step_eq_nS h_mono₁ oa h_qb (s₀, false)

/-- **Selective ε-perturbed identical-until-bad with output bad flag.**

Like `tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad`, but projected to the
computation output via `StateT.run'`. -/
theorem tvDist_simulateQ_le_queryBound_mul_slack_plus_probEvent_bad
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (S : ι → Prop) [DecidablePred S]
    (h_step_tv_S : ∀ (t : ι), S t → ∀ (s : σ),
      tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_step_eq_nS : ∀ (t : ι), ¬ S t → ∀ (p : σ × Bool),
      (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : ι) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBoundP oa S qS)
    (s₀ : σ) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal := by
  have h_joint :
      tvDist ((simulateQ impl₁ oa).run (s₀, false)) ((simulateQ impl₂ oa).run (s₀, false))
        ≤ qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true |
            (simulateQ impl₁ oa).run (s₀, false)].toReal :=
    tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad
      impl₁ impl₂ hε S h_step_tv_S h_step_eq_nS h_mono₁ oa h_qb s₀
  refine le_trans ?_ h_joint
  rw [StateT.run']
  exact tvDist_map_le (m := OracleComp spec') (α := α × σ × Bool) (β := α) Prod.fst
    ((simulateQ impl₁ oa).run (s₀, false)) ((simulateQ impl₂ oa).run (s₀, false))

/-! #### Query-bounded TV budget without a bad event

When the two implementations agree exactly off the charged queries and no bad event is
tracked, the selective bound simplifies to a pure per-query budget `qS * ε` on the joint
output-and-state distribution, with no bad-flag plumbing in the state. -/

/-- Bound the weighted TV sum from `tvDist_bind_left_le` by a uniform pointwise constant:
the output weights sum to at most one, so the weighted average of per-continuation TV
distances is at most any uniform bound on them. -/
private lemma tsum_probOutput_mul_tvDist_le_const {β γ : Type} (mx : OracleComp spec' β)
    (f₁ f₂ : β → OracleComp spec' γ) {c : ℝ} (hc : 0 ≤ c)
    (h_le : ∀ z : β, tvDist (f₁ z) (f₂ z) ≤ c) :
    (∑' z : β, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z)) ≤ c := by
  have h_le' : ∀ z : β,
      Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z) ≤ Pr[= z | mx].toReal * c :=
    fun z => mul_le_mul_of_nonneg_left (h_le z) ENNReal.toReal_nonneg
  have h_rhs_summable : Summable (fun z : β => Pr[= z | mx].toReal * c) :=
    (ENNReal.summable_toReal tsum_probOutput_ne_top).mul_right c
  -- the ℝ≥0∞ mass bound transfers to ℝ because every output probability is finite
  have h_sum_toReal_le_one : (∑' z : β, Pr[= z | mx].toReal) ≤ 1 := by
    simp [← ENNReal.tsum_toReal_eq fun _ => probOutput_ne_top]
  calc (∑' z : β, Pr[= z | mx].toReal * tvDist (f₁ z) (f₂ z))
      ≤ ∑' z : β, Pr[= z | mx].toReal * c :=
        Summable.tsum_le_tsum h_le' (h_rhs_summable.of_nonneg_of_le
          (fun z => by positivity) h_le') h_rhs_summable
    _ = (∑' z : β, Pr[= z | mx].toReal) * c := tsum_mul_right
    _ ≤ c := mul_le_of_le_one_left hc h_sum_toReal_le_one

/-- **Query-bounded total-variation budget for `simulateQ`.**

If two stateful oracle implementations agree exactly on every query outside a designated
set `S`, and on `S`-queries are within total-variation distance `ε` on the joint
answer-and-state distribution — uniformly in the carried state — then simulating any
computation making at most `qS` queries to `S` keeps the joint output-and-state
distributions within `qS * ε`, from any shared starting state.

This is the bad-event-free counterpart of
`tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad`: the per-query budgets
telescope across the simulation by the triangle inequality, the hybrid for the `i`-th
charged query swapping which implementation answers it. Typical use: a signing oracle
whose real and simulated bodies are within `ε` from every shared random-oracle cache,
with all remaining oracles handled identically on both sides. -/
theorem tvDist_simulateQ_run_le_queryBoundP_mul
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε)
    (S : ι → Prop) [DecidablePred S]
    (h_step_tv_S : ∀ (t : ι), S t → ∀ (s : σ),
      tvDist ((impl₁ t).run s) ((impl₂ t).run s) ≤ ε)
    (h_step_eq_nS : ∀ (t : ι), ¬ S t → ∀ (s : σ),
      (impl₁ t).run s = (impl₂ t).run s)
    (oa : OracleComp spec α) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBoundP oa S qS) (s₀ : σ) :
    tvDist ((simulateQ impl₁ oa).run s₀) ((simulateQ impl₂ oa).run s₀) ≤ qS * ε := by
  induction oa using OracleComp.inductionOn generalizing qS s₀ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, tvDist_self]
      positivity
  | query_bind t cont ih =>
      rw [isQueryBoundP_query_bind_iff] at h_qb
      obtain ⟨h_can, h_cont⟩ := h_qb
      set f₁ : spec.Range t × σ → OracleComp spec' (α × σ) :=
        fun z => (simulateQ impl₁ (cont z.1)).run z.2 with hf₁_def
      set f₂ : spec.Range t × σ → OracleComp spec' (α × σ) :=
        fun z => (simulateQ impl₂ (cont z.1)).run z.2 with hf₂_def
      have hsim₁_eq : (simulateQ impl₁ (query t >>= cont)).run s₀ =
          (impl₁ t).run s₀ >>= f₁ := by
        simp [hf₁_def, simulateQ_bind, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
      have hsim₂_eq : (simulateQ impl₂ (query t >>= cont)).run s₀ =
          (impl₂ t).run s₀ >>= f₂ := by
        simp [hf₂_def, simulateQ_bind, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
      rw [hsim₁_eq, hsim₂_eq]
      by_cases hSt : S t
      · -- Charged query: swap the step (cost `ε`), then recurse with budget `qS - 1`.
        simp only [if_pos hSt] at h_cont
        have hqS_pos : 0 < qS := h_can.resolve_left (not_not_intro hSt)
        have h_first : tvDist ((impl₁ t).run s₀ >>= f₁) ((impl₁ t).run s₀ >>= f₂)
            ≤ ↑(qS - 1) * ε :=
          le_trans (tvDist_bind_left_le _ _ _)
            (tsum_probOutput_mul_tvDist_le_const _ f₁ f₂
              (mul_nonneg (Nat.cast_nonneg _) hε) (fun z => ih z.1 (h_cont z.1) z.2))
        have h_second : tvDist ((impl₁ t).run s₀ >>= f₂) ((impl₂ t).run s₀ >>= f₂) ≤ ε :=
          le_trans (tvDist_bind_right_le _ _ _) (h_step_tv_S t hSt s₀)
        have hq_arith : (↑(qS - 1) + 1 : ℝ) = (qS : ℝ) := by
          exact_mod_cast congrArg Nat.cast (Nat.sub_add_cancel hqS_pos)
        calc tvDist ((impl₁ t).run s₀ >>= f₁) ((impl₂ t).run s₀ >>= f₂)
            ≤ tvDist ((impl₁ t).run s₀ >>= f₁) ((impl₁ t).run s₀ >>= f₂) +
                tvDist ((impl₁ t).run s₀ >>= f₂) ((impl₂ t).run s₀ >>= f₂) :=
              tvDist_triangle _ _ _
          _ ≤ ↑(qS - 1) * ε + ε := add_le_add h_first h_second
          _ = (↑(qS - 1) + 1) * ε := by ring
          _ = ↑qS * ε := by rw [hq_arith]
      · -- Free query: the step is shared; recurse with the budget intact.
        simp only [if_neg hSt] at h_cont
        rw [← h_step_eq_nS t hSt s₀]
        exact le_trans (tvDist_bind_left_le _ _ _)
          (tsum_probOutput_mul_tvDist_le_const _ f₁ f₂
            (mul_nonneg (Nat.cast_nonneg _) hε) (fun z => ih z.1 (h_cont z.1) z.2))

end IdenticalUntilBadEpsilonSelective

end OracleComp.ProgramLogic.Relational
