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
public import VCVio.ProgramLogic.Relational.SimulateQ.StateDependent
import all VCVio.ProgramLogic.Relational.SimulateQ.StateDependent

/-!
# Heterogeneous, resource, and averaged-state bad-event bounds
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

/-! ### Heterogeneous-state bad + slack `simulateQ` rule

A fully heterogeneous (`σ₁ ≠ σ₂`, `spec₁ ≠ spec₂`) one-directional `simulateQ` induction
rule carrying both a monotone bad event on side `1` and per-charged-query slack `ε`.

The simulations may have different output and state types. The conclusion is a
one-directional `Pr[= true]` inequality

  `Pr[= true | run' impl₁] ≤ Pr[= true | run' impl₂] + Pr[bad] + q · ε`,

which is exactly the shape consumed by cross-domain crypto reductions that couple a
per-tag random oracle against a per-session one. The accounting term `q · ε` comes from
the charged-query budget `IsQueryBoundP oa charged q`. -/

section HeterogeneousBadSlack

variable {ι : Type} {spec : OracleSpec ι}
variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable {σ₁ σ₂ : Type}

/-- Bad propagation for an arbitrary state predicate: if `bad` survives every single oracle
call, then a simulation started from a bad state leaves every reachable output state bad.
`mem_support_simulateQ_run_of_bad` is the special case of a `σ × Bool` state and a flag. -/
private lemma mem_support_simulateQ_run_of_bad_general
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁))) (bad : σ₁ → Prop)
    (hmono : ∀ (t : spec.Domain) (s₁ : σ₁), bad s₁ → ∀ z ∈ support ((impl₁ t).run s₁), bad z.2)
    (oa : OracleComp spec α) (s₁ : σ₁) (hbad : bad s₁) :
    ∀ z ∈ support ((simulateQ impl₁ oa).run s₁), bad z.2 := by
  induction oa using OracleComp.inductionOn generalizing s₁ with
  | pure x => simpa using hbad
  | query_bind t cont ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      rintro z ⟨⟨u, s₁'⟩, h_mem, h_z⟩
      exact ih u s₁' (hmono t s₁ hbad (u, s₁') h_mem) z h_z

/-- A simulation started from a bad state has bad probability exactly `1`. The
heterogeneous-state analogue of `probEvent_simulateQ_run_bad_eq_one_of_bad`. -/
private lemma probEvent_bad_simulateQ_run_eq_one_of_bad [IsUniformSpec spec₁]
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (bad : σ₁ → Prop)
    (hmono : ∀ (t : spec.Domain) (s₁ : σ₁), bad s₁ →
      ∀ z ∈ support ((impl₁ t).run s₁), bad z.2)
    (oa : OracleComp spec α) (s₁ : σ₁) (hbad : bad s₁) :
    Pr[ bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₁] = 1 := by
  rw [probEvent_eq_one_iff]
  exact ⟨by simp, mem_support_simulateQ_run_of_bad_general impl₁ bad hmono oa s₁ hbad⟩

/-- Inductive core of `probOutput_simulateQ_run'_le_add_bad_add_slack`, stated on the
joint `run` distribution with the event `fun z => z.1 = true`. -/
private theorem probEvent_fst_simulateQ_run_le_add_bad_add_slack
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (R : σ₁ → σ₂ → Prop)
    (bad : σ₁ → Prop)
    (charged : spec.Domain → Prop) [DecidablePred charged]
    (ε : ℝ≥0∞)
    (hmono : ∀ (t : spec.Domain) (s₁ : σ₁), bad s₁ →
      ∀ z ∈ support ((impl₁ t).run s₁), bad z.2)
    (hstep : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂), R s₁ s₂ → ¬ bad s₁ →
      ∀ (k₁ : spec.Range t × σ₁ → OracleComp spec₁ (Bool × σ₁))
        (k₂ : spec.Range t × σ₂ → OracleComp spec₂ (Bool × σ₂)) (c : ℝ≥0∞),
        (∀ (u : spec.Range t) (s₁' : σ₁) (s₂' : σ₂), R s₁' s₂' →
          Pr[ fun z => z.1 = true | k₁ (u, s₁')] ≤
            Pr[ fun z => z.1 = true | k₂ (u, s₂')] +
            Pr[ bad ∘ Prod.snd | k₁ (u, s₁')] + c) →
        Pr[ fun z => z.1 = true | (impl₁ t).run s₁ >>= k₁] ≤
          Pr[ fun z => z.1 = true | (impl₂ t).run s₂ >>= k₂] +
          Pr[ bad ∘ Prod.snd | (impl₁ t).run s₁ >>= k₁] +
          (c + (if charged t then ε else 0)))
    (oa : OracleComp spec Bool) :
    ∀ {q : ℕ}, OracleComp.IsQueryBoundP oa charged q →
      ∀ (s₁ : σ₁) (s₂ : σ₂), R s₁ s₂ →
        Pr[ fun z => z.1 = true | (simulateQ impl₁ oa).run s₁] ≤
          Pr[ fun z => z.1 = true | (simulateQ impl₂ oa).run s₂] +
          Pr[ bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₁] +
          (q : ℝ≥0∞) * ε := by
  induction oa using OracleComp.inductionOn generalizing σ₂ with
  | pure x =>
      intro q _ s₁ s₂ _
      simp only [simulateQ_pure, StateT.run_pure, probEvent_pure]
      exact le_add_right (le_add_right le_rfl)
  | @query_bind t cont ih =>
      intro q hqb s₁ s₂ hR
      by_cases hbad : bad s₁
      · -- bad branch: `Pr[ bad ∘ snd | sim₁] = 1` dominates everything.
        have hbad1 : Pr[ bad ∘ Prod.snd | (simulateQ impl₁ (query t >>= cont)).run s₁] = 1 :=
          probEvent_bad_simulateQ_run_eq_one_of_bad impl₁ bad hmono _ s₁ hbad
        refine le_trans probEvent_le_one ?_
        rw [hbad1]
        exact le_add_right le_add_self
      · -- good branch: rewrite both sides to head-bind form and apply `hstep`.
        rw [isQueryBoundP_query_bind_iff] at hqb
        obtain ⟨hvalid, hcont⟩ := hqb
        have hsim₁ : (simulateQ impl₁ (query t >>= cont)).run s₁ =
            (impl₁ t).run s₁ >>= fun z => (simulateQ impl₁ (cont z.1)).run z.2 := by
          simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, StateT.run_bind]
        have hsim₂ : (simulateQ impl₂ (query t >>= cont)).run s₂ =
            (impl₂ t).run s₂ >>= fun z => (simulateQ impl₂ (cont z.1)).run z.2 := by
          simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, StateT.run_bind]
        rw [hsim₁, hsim₂]
        set k₁ : spec.Range t × σ₁ → OracleComp spec₁ (Bool × σ₁) :=
          fun z => (simulateQ impl₁ (cont z.1)).run z.2 with hk₁
        set k₂ : spec.Range t × σ₂ → OracleComp spec₂ (Bool × σ₂) :=
          fun z => (simulateQ impl₂ (cont z.1)).run z.2 with hk₂
        -- The slack carried past one query: `(q-1)·ε` if charged, else `q·ε`.
        set c : ℝ≥0∞ := ((if charged t then q - 1 else q : ℕ) : ℝ≥0∞) * ε with hc
        -- Continuation bound for *every* `R`-related result (bad ones handled by monotonicity).
        have hcont_bound : ∀ (u : spec.Range t) (s₁' : σ₁) (s₂' : σ₂), R s₁' s₂' →
            Pr[ fun z => z.1 = true | k₁ (u, s₁')] ≤
              Pr[ fun z => z.1 = true | k₂ (u, s₂')] +
              Pr[ bad ∘ Prod.snd | k₁ (u, s₁')] + c := by
          intro u s₁' s₂' hR'
          by_cases hbad' : bad s₁'
          · -- bad continuation: `Pr[ bad ∘ snd | k₁] = 1` dominates.
            have hbad1' : Pr[ bad ∘ Prod.snd | k₁ (u, s₁')] = 1 :=
              probEvent_bad_simulateQ_run_eq_one_of_bad impl₁ bad hmono (cont u) s₁' hbad'
            refine le_trans probEvent_le_one ?_
            rw [hbad1']
            exact le_add_right le_add_self
          · -- good continuation: apply the inductive hypothesis at the decremented budget.
            have hib : OracleComp.IsQueryBoundP (cont u) charged
                (if charged t then q - 1 else q) := hcont u
            exact ih u impl₂ R hstep hib s₁' s₂' hR'
        -- Apply the per-step premise; then absorb `c + slack` into `q·ε`.
        refine le_trans (hstep t s₁ s₂ hR hbad k₁ k₂ c hcont_bound) ?_
        have hcabs : c + (if charged t then ε else 0) ≤ (q : ℝ≥0∞) * ε := by
          rcases hvalid with hnc | hpos
          · -- `t` uncharged: `c = q·ε`, slack term is `0`.
            rw [hc, if_neg hnc, if_neg hnc, add_zero]
          · -- `t` charged: `c = (q-1)·ε`, slack term is `ε`, and `0 < q`.
            by_cases hch : charged t
            · rw [hc, if_pos hch, if_pos hch]
              have hq : ((q - 1 : ℕ) : ℝ≥0∞) + 1 = (q : ℝ≥0∞) := by
                have : ((q - 1 : ℕ) + 1 : ℕ) = q := Nat.succ_pred_eq_of_pos hpos
                exact_mod_cast congrArg (Nat.cast : ℕ → ℝ≥0∞) this
              rw [show ((q - 1 : ℕ) : ℝ≥0∞) * ε + ε = (((q - 1 : ℕ) : ℝ≥0∞) + 1) * ε by
                rw [add_mul, one_mul], hq]
            · rw [hc, if_neg hch, if_neg hch, add_zero]
        gcongr

/-- **Heterogeneous-state bad + slack `simulateQ` rule.**

Couples two stateful oracle simulations with *different* state types `σ₁`, `σ₂` and
*different* base specs `spec₁`, `spec₂`, related by a coupling invariant `R`. It carries a
monotone bad event `bad` on side `1` together with per-charged-query slack `ε`, charged
queries being designated by the predicate `charged`. If the computation `oa` makes at most
`q` charged queries (`IsQueryBoundP oa charged q`), then

  `Pr[= true | run' impl₁ oa] ≤ Pr[= true | run' impl₂ oa] + Pr[bad] + q · ε`.

The per-query premise `hstep` is the bind-level coupling step: from `R`-related, non-bad
states, one query head together with any pair of continuations satisfying a continuation
bound yields the head-bind bound, paying `ε` for charged queries. This packages exactly
the obligation a concrete cross-domain reduction must discharge for its oracle pair.

Only `impl₁` requires bad monotonicity (`hmono`), since the bound is one-directional and
mentions `Pr[bad]` only on side `1`. -/
theorem probOutput_simulateQ_run'_le_add_bad_add_slack
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (R : σ₁ → σ₂ → Prop)
    (bad : σ₁ → Prop)
    (charged : spec.Domain → Prop) [DecidablePred charged]
    (ε : ℝ≥0∞)
    (hmono : ∀ (t : spec.Domain) (s₁ : σ₁), bad s₁ →
      ∀ z ∈ support ((impl₁ t).run s₁), bad z.2)
    (hstep : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂), R s₁ s₂ → ¬ bad s₁ →
      ∀ (k₁ : spec.Range t × σ₁ → OracleComp spec₁ (Bool × σ₁))
        (k₂ : spec.Range t × σ₂ → OracleComp spec₂ (Bool × σ₂)) (c : ℝ≥0∞),
        (∀ (u : spec.Range t) (s₁' : σ₁) (s₂' : σ₂), R s₁' s₂' →
          Pr[ fun z => z.1 = true | k₁ (u, s₁')] ≤
            Pr[ fun z => z.1 = true | k₂ (u, s₂')] +
            Pr[ bad ∘ Prod.snd | k₁ (u, s₁')] + c) →
        Pr[ fun z => z.1 = true | (impl₁ t).run s₁ >>= k₁] ≤
          Pr[ fun z => z.1 = true | (impl₂ t).run s₂ >>= k₂] +
          Pr[ bad ∘ Prod.snd | (impl₁ t).run s₁ >>= k₁] +
          (c + (if charged t then ε else 0)))
    (oa : OracleComp spec Bool) {q : ℕ}
    (hbound : OracleComp.IsQueryBoundP oa charged q)
    (s₁ : σ₁) (s₂ : σ₂) (hR : R s₁ s₂) :
    Pr[= true | (simulateQ impl₁ oa).run' s₁] ≤
      Pr[= true | (simulateQ impl₂ oa).run' s₂] +
      Pr[ bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₁] +
      (q : ℝ≥0∞) * ε := by
  have hjoint := probEvent_fst_simulateQ_run_le_add_bad_add_slack
    impl₁ impl₂ R bad charged ε hmono hstep oa hbound s₁ s₂ hR
  have hproj₁ : Pr[= true | (simulateQ impl₁ oa).run' s₁] =
      Pr[ fun z : Bool × σ₁ => z.1 = true | (simulateQ impl₁ oa).run s₁] := by
    rw [← probEvent_eq_eq_probOutput _ true, StateT.run'_eq,
      show (fun x : Bool × σ₁ => x.1) = Prod.fst from rfl, probEvent_map]
    rfl
  have hproj₂ : Pr[= true | (simulateQ impl₂ oa).run' s₂] =
      Pr[ fun z : Bool × σ₂ => z.1 = true | (simulateQ impl₂ oa).run s₂] := by
    rw [← probEvent_eq_eq_probOutput _ true, StateT.run'_eq,
      show (fun x : Bool × σ₂ => x.1) = Prod.fst from rfl, probEvent_map]
    rfl
  rw [hproj₁, hproj₂]
  exact hjoint

end HeterogeneousBadSlack

/-! ## Single-world resource-charged bad accumulator

A *single-world* accumulator bounding `Pr[flag = true]` for a stateful simulation whose
state `σ × Bool` carries a monotone resource `R : σ → ℝ≥0∞` and a never-reset bad flag.
This lemma bounds the bad-flag mass directly by the resource-weighted query slack
`expectedQuerySlack impl charged (fun s => R s · ε)`.

The per-step hypotheses are:

* `h_charged_step`: at a *charged* (read) step from a non-bad state, the bad mass after the
  step-and-continuation is at most `R s · ε` (the flip charge) plus the expected
  continuation bad mass;
* `h_free_step`: at a *free* step, no flip charge is paid.

Folding the resulting `expectedQuerySlack` against a resource bound (e.g. via
`expectedQuerySlack_resource_le` / `expectedQuerySlack_expected_resource_le`) yields a
closed-form bilinear bound. -/
section SingleWorldResourceBad

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [IsUniformSpec spec']
variable {σ γ : Type}

/-- Collapse a `tsum` over a state-bool product to its non-bad slice when the bad slice
vanishes. Used to discard bad-output terms (whose `expectedQuerySlack` is `0`) in the
inductive step of `probEvent_bad_simulateQ_run_le_expectedQuerySlack`. -/
private lemma tsum_prod_right_bool_eq_of_zero {A B : Type} (f : A × B × Bool → ℝ≥0∞)
    (h : ∀ z : A × B, f (z.1, z.2, true) = 0) :
    (∑' z : A × B × Bool, f z) = ∑' z : A × B, f (z.1, z.2, false) := by
  have e : (∑' z : A × B × Bool, f z)
      = ∑' z : (A × B) × Bool, f (z.1.1, z.1.2, z.2) :=
    ((Equiv.tsum_eq (Equiv.prodAssoc A B Bool) f).symm.trans rfl)
  rw [e, ENNReal.tsum_prod']
  refine tsum_congr fun z => ?_
  rw [tsum_bool (f := fun b => f (z.1, z.2, b)), h z, add_zero]

/-- Unfold `expectedQuerySlack` at a `query`-headed computation from a non-flagged state.
Charged and free queries share the shape *flip charge plus expected continuation slack*:
the charge `ε s` is paid only on a charged query, which is also the only place the
continuation budget drops. Bad-flagged output states contribute nothing, their slack being
`0` by `expectedQuerySlack_bad_eq_zero`. -/
private lemma expectedQuerySlack_query_bind_good_eq
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (S : spec.Domain → Prop) [DecidablePred S] (ε : σ → ℝ≥0∞) (t : spec.Domain)
    (cont : spec.Range t → OracleComp spec γ) {qS : ℕ} (hqS : S t → 0 < qS) (s : σ) :
    expectedQuerySlack impl S ε (query t >>= cont) qS (s, false) =
      (if S t then ε s else 0) + ∑' z : spec.Range t × σ,
        Pr[= (z.1, z.2, false) | (impl t).run (s, false)] *
          expectedQuerySlack impl S ε (cont z.1) (if S t then qS - 1 else qS) (z.2, false) := by
  rw [expectedQuerySlack_query_bind]
  by_cases h : S t
  · rw [expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ h (hqS h), if_pos h, if_pos h,
      tsum_prod_right_bool_eq_of_zero (f := fun z : spec.Range t × σ × Bool =>
        Pr[= z | (impl t).run (s, false)] * expectedQuerySlack impl S ε (cont z.1) (qS - 1) z.2)
        (by rintro ⟨u, s'⟩; simp)]
  · rw [expectedQuerySlackStep_free _ _ _ _ _ _ _ h, if_neg h, if_neg h, zero_add,
      tsum_prod_right_bool_eq_of_zero (f := fun z : spec.Range t × σ × Bool =>
        Pr[= z | (impl t).run (s, false)] * expectedQuerySlack impl S ε (cont z.1) qS z.2)
        (by rintro ⟨u, s'⟩; simp)]

/-- Inductive `query`-headed step of `probEvent_bad_simulateQ_run_le_expectedQuerySlack`,
carrying an arbitrary per-state flip charge `w`. The charged and free premises merge into
the single `if`-guarded head-bind bound matched by `expectedQuerySlack_query_bind_good_eq`,
against which the inductive hypothesis is pushed through the bind term by term. -/
private lemma probEvent_bad_simulateQ_run_query_bind_le_expectedQuerySlack
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec'))) (charged : spec.Domain → Prop)
    [DecidablePred charged] (w : σ → ℝ≥0∞)
    (h_charged_step : ∀ (t : spec.Domain) (s : σ), charged t →
      ∀ (k : spec.Range t × σ × Bool → OracleComp spec' (γ × σ × Bool)),
        Pr[ fun z : γ × σ × Bool => z.2.2 = true | (impl t).run (s, false) >>= k] ≤ w s +
          ∑' z : spec.Range t × σ, Pr[= (z.1, z.2, false) | (impl t).run (s, false)] *
            Pr[ fun y : γ × σ × Bool => y.2.2 = true | k (z.1, z.2, false)])
    (h_free_step : ∀ (t : spec.Domain) (s : σ), ¬ charged t →
      ∀ (k : spec.Range t × σ × Bool → OracleComp spec' (γ × σ × Bool)),
        Pr[ fun z : γ × σ × Bool => z.2.2 = true | (impl t).run (s, false) >>= k] ≤
          ∑' z : spec.Range t × σ, Pr[= (z.1, z.2, false) | (impl t).run (s, false)] *
            Pr[ fun y : γ × σ × Bool => y.2.2 = true | k (z.1, z.2, false)])
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec γ) {qS : ℕ}
    (hvalid : ¬ charged t ∨ 0 < qS) (ih : ∀ (u : spec.Range t) (s' : σ),
      Pr[ fun z : γ × σ × Bool => z.2.2 = true | (simulateQ impl (cont u)).run (s', false)] ≤
        expectedQuerySlack impl charged w (cont u) (if charged t then qS - 1 else qS) (s', false))
    (s : σ) :
    Pr[ fun z : γ × σ × Bool => z.2.2 = true |
        (simulateQ impl (query t >>= cont)).run (s, false)] ≤
      expectedQuerySlack impl charged w (query t >>= cont) qS (s, false) := by
  -- Rewrite the run to head-bind form.
  have hsim : (simulateQ impl (query t >>= cont)).run (s, false) =
      (impl t).run (s, false) >>= fun z => (simulateQ impl (cont z.1)).run z.2 := by
    simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, StateT.run_bind]
  -- Merge the two per-step premises into one `if`-guarded head-bind bound.
  have hstep : Pr[ fun z : γ × σ × Bool => z.2.2 = true |
      (impl t).run (s, false) >>= fun z => (simulateQ impl (cont z.1)).run z.2] ≤
      (if charged t then w s else 0) + ∑' z : spec.Range t × σ,
        Pr[= (z.1, z.2, false) | (impl t).run (s, false)] *
          Pr[ fun y : γ × σ × Bool => y.2.2 = true |
            (simulateQ impl (cont z.1)).run (z.2, false)] := by
    by_cases h : charged t
    · -- Charged step: pay the flip charge `w s`.
      rw [if_pos h]
      exact h_charged_step t s h _
    · -- Free step: no charge.
      rw [if_neg h, zero_add]
      exact h_free_step t s h _
  -- Discard the bad-flagged output states, then forward each good one to the IH.
  rw [hsim, expectedQuerySlack_query_bind_good_eq impl charged w t cont
    (fun h => hvalid.resolve_left (· h)) s]
  refine hstep.trans (add_le_add le_rfl (ENNReal.tsum_le_tsum fun z => ?_))
  gcongr
  exact ih z.1 z.2

/-- **Single-world resource-charged bad accumulator.**

For `simulateQ impl oa` over a state `σ × Bool` (resource `σ`, never-reset bad flag), if

* every charged step pays a flip charge `R s · ε` (`h_charged_step`), routing any further
  bad mass through its good (non-flagged) output states, while
* every free step pays nothing and introduces no bad mass (`h_free_step`),

then the probability the flag is set after the whole run from a non-bad state is bounded by
the resource-weighted query slack
`expectedQuerySlack impl charged (fun s => R s * ε) oa qS (s, false)`.

The ε-perturbed identical-until-bad results
(`tvDist_simulateQ_le_qeps_plus_probEvent_output_bad`,
`ofReal_tvDist_simulateQ_run_le_expectedQuerySlack_plus_probEvent_output_bad`) bound a TV
distance and leave `Pr[bad]` standing as an unbounded additive remainder; this one bounds
that bad mass itself, and is the single-world, output-event counterpart of
`probEvent_fst_simulateQ_run_le_add_bad_add_slack`.

Tips when applying it. Both step premises quantify over an *arbitrary* continuation `k`,
so a concrete handler discharges them once per query kind rather than once per computation.
`R` and `ε` enter only through the product `R s * ε`, so a purely state-dependent charge
can be supplied through `R` alone with `ε = 1`. The resulting `expectedQuerySlack` is
normally folded to a closed form by `expectedQuerySlack_resource_le` or
`expectedQuerySlack_expected_resource_le`. -/
theorem probEvent_bad_simulateQ_run_le_expectedQuerySlack
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec'))) (charged : spec.Domain → Prop)
    [DecidablePred charged] (R : σ → ℝ≥0∞) (ε : ℝ≥0∞)
    (h_charged_step : ∀ (t : spec.Domain) (s : σ), charged t →
      ∀ (k : spec.Range t × σ × Bool → OracleComp spec' (γ × σ × Bool)),
        Pr[ fun z : γ × σ × Bool => z.2.2 = true | (impl t).run (s, false) >>= k] ≤ R s * ε +
          ∑' z : spec.Range t × σ, Pr[= (z.1, z.2, false) | (impl t).run (s, false)] *
              Pr[fun w : γ × σ × Bool => w.2.2 = true | k (z.1, z.2, false)])
    (h_free_step : ∀ (t : spec.Domain) (s : σ), ¬ charged t →
      ∀ (k : spec.Range t × σ × Bool → OracleComp spec' (γ × σ × Bool)),
        Pr[fun z : γ × σ × Bool => z.2.2 = true | (impl t).run (s, false) >>= k] ≤
          ∑' z : spec.Range t × σ, Pr[= (z.1, z.2, false) | (impl t).run (s, false)] *
              Pr[fun w : γ × σ × Bool => w.2.2 = true | k (z.1, z.2, false)])
    (oa : OracleComp spec γ) : ∀ {qS : ℕ}, OracleComp.IsQueryBoundP oa charged qS → ∀ (s : σ),
        Pr[fun z : γ × σ × Bool => z.2.2 = true | (simulateQ impl oa).run (s, false)] ≤
          expectedQuerySlack impl charged (fun s => R s * ε) oa qS (s, false) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro qS _ s
      simp
  | @query_bind t cont ih =>
      intro qS hqb s
      rw [isQueryBoundP_query_bind_iff] at hqb
      obtain ⟨hvalid, hcont⟩ := hqb
      exact probEvent_bad_simulateQ_run_query_bind_le_expectedQuerySlack impl charged
        (fun s => R s * ε) h_charged_step h_free_step t cont hvalid
        (fun u s' => ih u (hcont u) s') s

end SingleWorldResourceBad

/-! ## Averaged-state-measure bad accumulator

The single-world resource accumulator `probEvent_bad_simulateQ_run_le_expectedQuerySlack`
charges a flip cost `R s · ε` **at a fixed reachable state** `s`. That is exactly the right
shape for a handler that *draws the hidden randomness at the read* (the lazy /
deferred-sampling handler), where the per-state read charge is genuinely the averaged
guessing mass `R s · ε < 1`.

It is the *wrong* shape for an **eager** handler that *commits the hidden draw upstream*
(at signing time) and then reads it back deterministically: at a committed state `s` the
read-hit indicator `1_{mc ∈ slot(s)}` is `0` or `1`, never `ε`. The averaging that
produces `ε` happened earlier, at the commit draw, and cannot be localized to any fixed
read state.

The fix carried here is to average not over a single fixed state but over a **state
measure** `ν : σ × Bool → ℝ≥0∞` — the *law* of the eager handler's slot under the pending
upstream draws. The averaged bad mass

  `avgBadM impl ν oa := ∑' p, ν p · Pr[bad | (simulateQ impl oa).run p]`

telescopes through the free monad exactly like `expectedQuerySlack`, but the read step's
charge is now `∑' p, ν p · 1_{mc ∈ slot(p)} = Pr_{p∼ν}[mc ∈ slot(p)]`, a genuine
probability over the state law. When `ν` is the pushforward of the upstream commit draws,
this collapses (by Fubini / `tsum`-swap over the pending draws) to the *same* mass the lazy
handler charges at the read — `probOutput_lazyGhostFire_one` is its single-pending base
case. This is the missing-framework analogue of `expectedQuerySlack`: it carries a
state-**law** plus an averaged-output invariant rather than a per-state resource charge.

This section builds the reusable telescoping scaffold (`avgBadM`, its `pure`/`query_bind`
unfoldings, and the output-grouped step law `avgBadM_query_bind_eq_tsum_output`) and isolates
the read-step charge as the standalone Fubini lemma (`tsum_tsum_postStepOutM_mul`) the
instantiation must match against the lazy run. -/
section AveragedStateMeasureBad

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [IsUniformSpec spec']
variable {σ γ : Type}

/-! ### Bare-measure averaged bad mass

The scaffold is stated over a **bare measure** `ν : σ × Bool → ℝ≥0∞` rather than a
probability law: the telescoping identities and the free-monad induction only ever use
`ν p` as an `ℝ≥0∞` weight, and an **aborting** signing step produces a *sub*-probability
post-step state law (its total mass drops by the rejection mass), which a `PMF`-typed
average could not carry.

A caller (e.g. the deferred-sampling charge route) telescopes with
`avgBadM_query_bind_eq_tsum_output` directly at the sub-probability state laws produced by
the aborting sign step. -/

/-- **Bare-measure averaged bad mass.** The per-state bad mass of a run, averaged against an
arbitrary measure `ν : σ × Bool → ℝ≥0∞` rather than a probability law. No total-mass
constraint is needed by the telescoping, so the average carries the sub-probability
post-step laws emitted by an aborting step. -/
@[expose] noncomputable def avgBadM
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (oa : OracleComp spec γ) : ℝ≥0∞ :=
  ∑' p : σ × Bool, ν p *
    Pr[fun z : γ × σ × Bool => z.2.2 = true | (simulateQ impl oa).run p]

open scoped Classical in
/-- `avgBadM` at a Dirac (single-point indicator) measure is the plain per-state bad
probability. -/
lemma avgBadM_pure_state
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (p₀ : σ × Bool) (oa : OracleComp spec γ) :
    avgBadM impl (fun p => if p = p₀ then 1 else 0) oa =
      Pr[fun z : γ × σ × Bool => z.2.2 = true | (simulateQ impl oa).run p₀] := by
  rw [avgBadM, tsum_eq_single p₀ (by intro p hp; rw [if_neg hp, zero_mul]), if_pos rfl, one_mul]

open scoped Classical in
/-- **Linearity of `avgBadM` in the state measure.** The averaged bad mass over `ν` is the
`ν`-weighted sum of the per-state (Dirac) bad masses. -/
lemma avgBadM_eq_tsum_pure
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (oa : OracleComp spec γ) :
    avgBadM impl ν oa =
      ∑' s' : σ × Bool, ν s' * avgBadM impl (fun p => if p = s' then 1 else 0) oa := by
  rw [avgBadM]
  exact tsum_congr fun s' => by rw [avgBadM_pure_state]

/-- **Pure base case of `avgBadM`.** With no queries, the bad mass is exactly the carried
bad mass of the measure `ν` — the `ν`-mass on states with the flag already set. -/
lemma avgBadM_pure
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (x : γ) :
    avgBadM impl ν (pure x : OracleComp spec γ) =
      ∑' p : σ × Bool, ν p * (if p.2 = true then 1 else 0) := by
  rw [avgBadM]
  refine tsum_congr fun p => ?_
  rw [simulateQ_pure, StateT.run_pure]
  rcases p with ⟨s, b⟩
  cases b with
  | false => simp
  | true => simp [probEvent_pure]

/-- **One-step telescoping of `avgBadM` (joint-law form).** Moves one query off the front
and exposes the post-step joint law, holding for any impl and any measure `ν`. No
probabilistic content — pure rearrangement.

The right-hand side is the raw double `tsum`, over the starting state `p` and then the step
outcome `z`, with the per-state impl step `Pr[= z | (impl t).run p]` left exposed; apply this
form when that step law itself has to be manipulated.
`avgBadM_telescope_eq_tsum_postStep` regroups the same right-hand side as a single `tsum`
against `postStepJointM`, and `avgBadM_query_bind_eq_tsum_output` chains the two into the
output-indexed form that a free-monad induction consumes. -/
lemma avgBadM_query_bind_eq
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) (cont : spec.Range t → OracleComp spec γ) :
    avgBadM impl ν (query t >>= cont) =
      ∑' p : σ × Bool, ν p *
        ∑' z : spec.Range t × σ × Bool,
          Pr[= z | (impl t).run p] *
            Pr[fun w : γ × σ × Bool => w.2.2 = true |
              (simulateQ impl (cont z.1)).run z.2] := by
  simp only [avgBadM, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind, probEvent_bind_eq_tsum]

/-- **Post-step joint measure of a query step (bare-measure form).** The measure over
`(output, post-state)` produced by averaging the per-state impl step `Pr[= z | (impl t).run p]`
against the state measure `ν`. Stated directly as a `tsum` since `ν` need not be a
probability law. -/
@[expose] noncomputable def postStepJointM
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) (z : spec.Range t × σ × Bool) : ℝ≥0∞ :=
  ∑' p : σ × Bool, ν p * Pr[= z | (impl t).run p]

open scoped Classical in
/-- **Output-grouped telescoping of the bare-measure average.** The telescoped one-step
average regroups as a single `tsum` over the post-step joint measure `postStepJointM impl ν t`,
weighting each `(output, post-state)` pair by the Dirac bad mass at the post-state.
Pure `tsum`-Fubini. -/
lemma avgBadM_telescope_eq_tsum_postStep
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) (cont : spec.Range t → OracleComp spec γ) :
    (∑' p : σ × Bool, ν p *
        ∑' z : spec.Range t × σ × Bool,
          Pr[= z | (impl t).run p] *
            Pr[fun w : γ × σ × Bool => w.2.2 = true |
              (simulateQ impl (cont z.1)).run z.2]) =
      ∑' z : spec.Range t × σ × Bool,
        postStepJointM impl ν t z *
          avgBadM impl (fun p => if p = z.2 then 1 else 0) (cont z.1) := by
  classical
  have hstep : (∑' p : σ × Bool, ν p *
        ∑' z : spec.Range t × σ × Bool,
          Pr[= z | (impl t).run p] *
            Pr[fun w : γ × σ × Bool => w.2.2 = true |
              (simulateQ impl (cont z.1)).run z.2]) =
      ∑' p : σ × Bool, ∑' z : spec.Range t × σ × Bool,
          ν p * (Pr[= z | (impl t).run p] *
            avgBadM impl (fun q => if q = z.2 then 1 else 0) (cont z.1)) := by
    refine tsum_congr fun p => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun z => ?_
    rw [avgBadM_pure_state, ← mul_assoc]
  rw [hstep, ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  rw [postStepJointM, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun p => ?_
  rw [mul_assoc]

/-- **Per-output post-step state measure.** Grouping the post-step joint measure
`postStepJointM impl ν t` by the query *output* `u`: the resulting state measure assigns to
each post-state `s` the joint mass of producing `(u, s)`. The state coordinate of the
output-`u` slice of the post-step joint measure. -/
@[expose] noncomputable def postStepOutM
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) (u : spec.Range t) (s : σ × Bool) : ℝ≥0∞ :=
  postStepJointM impl ν t (u, s)

open scoped Classical in
/-- **Output-grouped one-step telescoping of `avgBadM`.** The telescoped one-step average
regroups as a `tsum` over the query *output* `u`, each weighted by the averaged bad mass of
the continuation `cont u` run from the per-output post-step state measure
`postStepOutM impl ν t u`. This is the form the threaded-charge induction consumes: it
applies the inductive hypothesis once per output, at a genuine state *measure* (not a Dirac),
so the per-target charge of the post-step measure can be bounded as a measure (avoiding the
`∑`-of-`⨆` blow-up of the per-post-state Dirac grouping). -/
lemma avgBadM_query_bind_eq_tsum_output
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) (cont : spec.Range t → OracleComp spec γ) :
    avgBadM impl ν (query t >>= cont) =
      ∑' u : spec.Range t, avgBadM impl (postStepOutM impl ν t u) (cont u) := by
  classical
  rw [avgBadM_query_bind_eq, avgBadM_telescope_eq_tsum_postStep, ENNReal.tsum_prod']
  refine tsum_congr fun u => ?_
  rw [avgBadM_eq_tsum_pure]
  refine tsum_congr fun s => ?_
  rw [postStepOutM]

/-- **Weighted post-step rearrangement.** Summing any post-state functional `F` against the
post-step measure (over output `u` and post-state `s`) equals the `ν`-average of the per-state
expected value of `F` after one impl step. The Fubini bridge used to push a per-state charge
bound (e.g. ghost-size or membership-charge growth) through the post-step measure.

Unlike `avgBadM_query_bind_eq_tsum_output`, which regroups the bad mass of one specific
continuation, this carries an arbitrary `ℝ≥0∞`-valued functional `F` of the post-state and
mentions no run at all; instantiate `F` at the charge being tracked. -/
lemma tsum_tsum_postStepOutM_mul
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) (F : σ × Bool → ℝ≥0∞) :
    (∑' u : spec.Range t, ∑' s : σ × Bool, postStepOutM impl ν t u s * F s)
      = ∑' p : σ × Bool, ν p *
          ∑' z : spec.Range t × σ × Bool, Pr[= z | (impl t).run p] * F z.2 := by
  rw [← ENNReal.tsum_prod]
  simp only [postStepOutM, postStepJointM, ← ENNReal.tsum_mul_right, mul_assoc]
  exact ENNReal.tsum_comm.trans (tsum_congr fun p => ENNReal.tsum_mul_left)

end AveragedStateMeasureBad

end OracleComp.ProgramLogic.Relational
