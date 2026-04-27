/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Advantage
import VCVio.SSP.IdenticalUntilBad

/-!
# HeapSSP: Identical-Until-Bad

State-dependent ε-perturbed identical-until-bad bounds for heap packages.

The bad-flag accounting theorem expects a state of shape `σ × Bool`. A
user-supplied bijection `φ : Heap Ident ≃ σ × Bool` exposes that view of
the heap, while all step hypotheses remain phrased over `Heap Ident`.
Internally this file reuses the existing product-state theorem through that
conjugation; the public statements are heap-native.

## API

* `Package.implConjugate` — conjugate a heap handler through `φ` to an
  handler on state `σ × Bool`.
* `Package.advantage_le_expectedSCost_plus_probEvent_bad` — the
  state-dependent ε form.
* `Package.advantage_le_expectedSCost_plus_probEvent_bad_of_inv` — the
  invariant-gated form, where the costly-step TV hypothesis is needed
  only on states satisfying a user-supplied invariant.
* `Package.advantage_le_expectedSCost_plus_probEvent_bad_of_inv_preserved` —
  the invariant-preserving corollary, whose final cost bound uses the
  tight ε directly.
* `Package.advantage_le_qSeps_plus_probEvent_bad` — the constant-ε
  corollary, derived from the state-dep form.
-/

open ENNReal OracleSpec OracleComp ProbComp
open OracleComp.ProgramLogic.Relational

namespace VCVio.HeapSSP

namespace Package

variable {ιₑ : Type} {E : OracleSpec.{0, 0} ιₑ}
  {Ident : Type} [CellSpec.{0, 0} Ident] {σ : Type}

/-! ### Conjugating a heap handler -/

/-- Conjugate a heap handler through a bijection `φ : Heap Ident ≃ σ × Bool`.
Each step unpacks the paired state to a heap via `φ.symm`, runs the heap
handler, and repacks the result via `φ`. -/
def implConjugate
    (impl : QueryImpl E (StateT (Heap Ident) ProbComp))
    (φ : Heap Ident ≃ σ × Bool) :
    QueryImpl E (StateT (σ × Bool) ProbComp) :=
  fun q => fun p => Prod.map id φ <$> (impl q).run (φ.symm p)

@[simp] lemma implConjugate_run_apply
    (impl : QueryImpl E (StateT (Heap Ident) ProbComp))
    (φ : Heap Ident ≃ σ × Bool) (q : E.Domain) (p : σ × Bool) :
    (implConjugate impl φ q).run p =
      Prod.map id φ <$> (impl q).run (φ.symm p) := rfl

/-! ### Bridging the heap `simulateQ` to the conjugated `simulateQ` -/

/-- The whole-client analogue of `implConjugate_run_apply`: running a
`simulateQ` of the conjugated handler from a paired state equals running
the heap-handler `simulateQ` from the heap state, mapped forward through
`φ`. -/
lemma evalDist_simulateQ_conjugate_run_eq {α : Type}
    (impl : QueryImpl E (StateT (Heap Ident) ProbComp))
    (φ : Heap Ident ≃ σ × Bool)
    (A : OracleComp E α) (s : σ × Bool) :
    evalDist ((simulateQ (implConjugate impl φ) A).run s) =
      evalDist (Prod.map id φ <$> (simulateQ impl A).run (φ.symm s)) := by
  have h :=
    VCVio.SSP.Package.simulateQ_StateT_evalDist_congr_of_bij
      (h₁ := implConjugate impl φ) (h₂ := impl) (φ := φ.symm)
      (fun q p => by simp) A s
  simpa using h

/-- On `run'` (discarding the state), the heap and conjugated
simulations have the same output distribution: the bijection `φ` cancels
with `Prod.fst`. -/
lemma evalDist_simulateQ_run'_eq {α : Type}
    (impl : QueryImpl E (StateT (Heap Ident) ProbComp))
    (φ : Heap Ident ≃ σ × Bool)
    (A : OracleComp E α) (s_init : σ) :
    evalDist ((simulateQ impl A).run' (φ.symm (s_init, false)))
      = evalDist ((simulateQ (implConjugate impl φ) A).run' (s_init, false)) := by
  simp only [StateT.run'_eq, evalDist_map]
  rw [evalDist_simulateQ_conjugate_run_eq impl φ A (s_init, false), evalDist_map,
      Functor.map_map]
  rfl

/-! ### The state-dep ε bridge -/

/-- State-dependent ε-perturbed identical-until-bad.

With a bijection `φ : Heap Ident ≃ σ × Bool` extracting the bad flag,
and both games' init landing in the no-bad heap `φ.symm (s_init, false)`,
the advantage `G₀.advantage G₁ A` is bounded by the cumulative expected
ε-cost (computed on the conjugated handler) plus the heap-side
probability that the bad flag fires in `G₀`'s execution.

* `h_step_tv_S` — on a costly query from a no-bad heap (as witnessed by
  `φ.symm (s, false)`), the two heap handlers are ε-close in TV.
* `h_step_eq_nS` — on a free query, the handlers are pointwise equal on
  every heap.
* `h_mono₀` — once bad has fired in `G₀`'s heap, every reachable next
  heap also has bad fired. -/
theorem advantage_le_expectedSCost_plus_probEvent_bad
    (G₀ G₁ : Package unifSpec E Ident)
    (φ : Heap Ident ≃ σ × Bool) (s_init : σ)
    (h_init₀ : G₀.init = pure (φ.symm (s_init, false)))
    (h_init₁ : G₁.init = pure (φ.symm (s_init, false)))
    (S : E.Domain → Prop) [DecidablePred S]
    (ε : σ → ℝ≥0∞)
    (h_step_tv_S : ∀ (t : E.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal
        (tvDist ((G₀.impl t).run (φ.symm (s, false)))
                ((G₁.impl t).run (φ.symm (s, false)))) ≤ ε s)
    (h_step_eq_nS : ∀ (t : E.Domain), ¬ S t → ∀ (h : Heap Ident),
      (G₀.impl t).run h = (G₁.impl t).run h)
    (h_mono₀ : ∀ (t : E.Domain) (h : Heap Ident), (φ h).2 = true →
      ∀ z ∈ support ((G₀.impl t).run h), (φ z.2).2 = true)
    (A : OracleComp E Bool) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBoundP A S qS) :
    ENNReal.ofReal (G₀.advantage G₁ A)
      ≤ expectedSCost (implConjugate G₀.impl φ) S ε A qS (s_init, false)
        + Pr[fun z : Bool × Heap Ident => (φ z.2).2 = true |
            (simulateQ G₀.impl A).run (φ.symm (s_init, false))] := by
  set G₀' := implConjugate G₀.impl φ with hG₀'_def
  set G₁' := implConjugate G₁.impl φ with hG₁'_def
  have h_step_tv_S' :
      ∀ (t : E.Domain), S t → ∀ (s : σ),
        ENNReal.ofReal (tvDist ((G₀' t).run (s, false))
          ((G₁' t).run (s, false))) ≤ ε s := by
    intro t hSt s
    have hmap :
        tvDist ((G₀' t).run (s, false)) ((G₁' t).run (s, false))
          ≤ tvDist ((G₀.impl t).run (φ.symm (s, false)))
              ((G₁.impl t).run (φ.symm (s, false))) := by
      simp only [hG₀'_def, hG₁'_def, implConjugate_run_apply]
      exact tvDist_map_le (Prod.map id φ) _ _
    exact le_trans (ENNReal.ofReal_le_ofReal hmap) (h_step_tv_S t hSt s)
  have h_step_eq_nS' :
      ∀ (t : E.Domain), ¬ S t → ∀ (p : σ × Bool),
        (G₀' t).run p = (G₁' t).run p := by
    intro t hnSt p
    simp only [hG₀'_def, hG₁'_def, implConjugate_run_apply]
    rw [h_step_eq_nS t hnSt (φ.symm p)]
  have h_mono₀' :
      ∀ (t : E.Domain) (p : σ × Bool), p.2 = true →
        ∀ z ∈ support ((G₀' t).run p), z.2.2 = true := by
    intro t p hp z hz
    simp only [hG₀'_def, implConjugate_run_apply, support_map, Set.mem_image] at hz
    obtain ⟨w, hw_support, rfl⟩ := hz
    have hφ : (φ (φ.symm p)).2 = true := by simp [hp]
    have := h_mono₀ t (φ.symm p) hφ w hw_support
    simpa [Prod.map] using this
  have h_bridge :
      ENNReal.ofReal
          (tvDist ((simulateQ G₀' A).run' (s_init, false))
                  ((simulateQ G₁' A).run' (s_init, false)))
        ≤ expectedSCost G₀' S ε A qS (s_init, false)
          + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
              (simulateQ G₀' A).run (s_init, false)] :=
    ofReal_tvDist_simulateQ_le_expectedSCost_plus_probEvent_output_bad
      G₀' G₁' S ε h_step_tv_S' h_step_eq_nS' h_mono₀' A h_qb s_init
  have h_runProb₀ : evalDist (G₀.runProb A)
      = evalDist ((simulateQ G₀' A).run' (s_init, false)) := by
    simp only [Package.runProb, Package.run, h_init₀, pure_bind]
    exact evalDist_simulateQ_run'_eq G₀.impl φ A s_init
  have h_runProb₁ : evalDist (G₁.runProb A)
      = evalDist ((simulateQ G₁' A).run' (s_init, false)) := by
    simp only [Package.runProb, Package.run, h_init₁, pure_bind]
    exact evalDist_simulateQ_run'_eq G₁.impl φ A s_init
  have h_adv_le_tv :
      G₀.advantage G₁ A ≤
        tvDist ((simulateQ G₀' A).run' (s_init, false))
               ((simulateQ G₁' A).run' (s_init, false)) := by
    unfold Package.advantage ProbComp.boolDistAdvantage
    have h₀ : Pr[= true | G₀.runProb A]
        = Pr[= true | (simulateQ G₀' A).run' (s_init, false)] :=
      probOutput_congr rfl h_runProb₀
    have h₁ : Pr[= true | G₁.runProb A]
        = Pr[= true | (simulateQ G₁' A).run' (s_init, false)] :=
      probOutput_congr rfl h_runProb₁
    rw [h₀, h₁]
    exact abs_probOutput_toReal_sub_le_tvDist _ _
  have h_ofreal_adv :
      ENNReal.ofReal (G₀.advantage G₁ A) ≤
        ENNReal.ofReal
          (tvDist ((simulateQ G₀' A).run' (s_init, false))
                  ((simulateQ G₁' A).run' (s_init, false))) :=
    ENNReal.ofReal_le_ofReal h_adv_le_tv
  have h_probEvent_eq :
      Pr[fun z : Bool × σ × Bool => z.2.2 = true |
            (simulateQ G₀' A).run (s_init, false)]
        = Pr[fun z : Bool × Heap Ident => (φ z.2).2 = true |
            (simulateQ G₀.impl A).run (φ.symm (s_init, false))] := by
    have h :=
      evalDist_simulateQ_conjugate_run_eq G₀.impl φ A (s_init, false)
    rw [probEvent_congr' (q := fun z : Bool × σ × Bool => z.2.2 = true)
        (fun _ _ => Iff.rfl) h, probEvent_map]
    rfl
  calc ENNReal.ofReal (G₀.advantage G₁ A)
      ≤ _ := h_ofreal_adv
    _ ≤ expectedSCost G₀' S ε A qS (s_init, false)
          + Pr[fun z : Bool × σ × Bool => z.2.2 = true |
              (simulateQ G₀' A).run (s_init, false)] := h_bridge
    _ = expectedSCost G₀' S ε A qS (s_init, false)
          + Pr[fun z : Bool × Heap Ident => (φ z.2).2 = true |
              (simulateQ G₀.impl A).run (φ.symm (s_init, false))] := by
          rw [h_probEvent_eq]

/-! ### Invariant-gated state-dep ε bridge -/

/-- Invariant-gated state-dependent ε-perturbed identical-until-bad.

Variant of `advantage_le_expectedSCost_plus_probEvent_bad` where the
costly-step TV hypothesis is required only for states satisfying an
invariant `Inv`. The generated cost function charges the intended `ε s`
on invariant states and the conservative fallback cost `1` elsewhere.

This is the first reusable layer for proofs whose package handler only
has a meaningful cryptographic interpretation on reachable states. A
separate preservation/cost-congruence lemma can later eliminate the
fallback branch when the real handler preserves `Inv` from the initial
state. -/
theorem advantage_le_expectedSCost_plus_probEvent_bad_of_inv
    (G₀ G₁ : Package unifSpec E Ident)
    (φ : Heap Ident ≃ σ × Bool) (s_init : σ)
    (h_init₀ : G₀.init = pure (φ.symm (s_init, false)))
    (h_init₁ : G₁.init = pure (φ.symm (s_init, false)))
    (Inv : σ → Prop) [DecidablePred Inv]
    (S : E.Domain → Prop) [DecidablePred S]
    (ε : σ → ℝ≥0∞)
    (h_step_tv_S : ∀ (t : E.Domain), S t → ∀ (s : σ), Inv s →
      ENNReal.ofReal
        (tvDist ((G₀.impl t).run (φ.symm (s, false)))
                ((G₁.impl t).run (φ.symm (s, false)))) ≤ ε s)
    (h_step_eq_nS : ∀ (t : E.Domain), ¬ S t → ∀ (h : Heap Ident),
      (G₀.impl t).run h = (G₁.impl t).run h)
    (h_mono₀ : ∀ (t : E.Domain) (h : Heap Ident), (φ h).2 = true →
      ∀ z ∈ support ((G₀.impl t).run h), (φ z.2).2 = true)
    (A : OracleComp E Bool) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBoundP A S qS) :
    ENNReal.ofReal (G₀.advantage G₁ A)
      ≤ expectedSCost (implConjugate G₀.impl φ) S
          (fun s => if Inv s then ε s else 1) A qS (s_init, false)
        + Pr[fun z : Bool × Heap Ident => (φ z.2).2 = true |
            (simulateQ G₀.impl A).run (φ.symm (s_init, false))] := by
  refine advantage_le_expectedSCost_plus_probEvent_bad
    G₀ G₁ φ s_init h_init₀ h_init₁ S (fun s => if Inv s then ε s else 1) ?_
    h_step_eq_nS h_mono₀ A h_qb
  intro t hSt s
  by_cases hs : Inv s
  · simpa [hs] using h_step_tv_S t hSt s hs
  · simpa [hs] using
      ENNReal.ofReal_le_ofReal (tvDist_le_one
        ((G₀.impl t).run (φ.symm (s, false)))
        ((G₁.impl t).run (φ.symm (s, false))))

/-- Invariant-preserving state-dependent ε-perturbed identical-until-bad.

Corollary of `advantage_le_expectedSCost_plus_probEvent_bad_of_inv` for
handlers that preserve `Inv` from the initial no-bad state. Unlike the
basic invariant-gated theorem, the final expected-cost term is stated
with the tight cost function `ε`; the generic
`expectedSCost_eq_of_inv` lemma removes the fallback branch because it is
unreachable under `G₀`'s support. -/
theorem advantage_le_expectedSCost_plus_probEvent_bad_of_inv_preserved
    (G₀ G₁ : Package unifSpec E Ident)
    (φ : Heap Ident ≃ σ × Bool) (s_init : σ)
    (h_init₀ : G₀.init = pure (φ.symm (s_init, false)))
    (h_init₁ : G₁.init = pure (φ.symm (s_init, false)))
    (Inv : σ → Prop)
    (h_init_inv : Inv s_init)
    (h_pres : ∀ (t : E.Domain) (p : σ × Bool), p.2 = false → Inv p.1 →
      ∀ z ∈ support ((implConjugate G₀.impl φ t).run p), Inv z.2.1)
    (S : E.Domain → Prop) [DecidablePred S]
    (ε : σ → ℝ≥0∞)
    (h_step_tv_S : ∀ (t : E.Domain), S t → ∀ (s : σ), Inv s →
      ENNReal.ofReal
        (tvDist ((G₀.impl t).run (φ.symm (s, false)))
                ((G₁.impl t).run (φ.symm (s, false)))) ≤ ε s)
    (h_step_eq_nS : ∀ (t : E.Domain), ¬ S t → ∀ (h : Heap Ident),
      (G₀.impl t).run h = (G₁.impl t).run h)
    (h_mono₀ : ∀ (t : E.Domain) (h : Heap Ident), (φ h).2 = true →
      ∀ z ∈ support ((G₀.impl t).run h), (φ z.2).2 = true)
    (A : OracleComp E Bool) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBoundP A S qS) :
    ENNReal.ofReal (G₀.advantage G₁ A)
      ≤ expectedSCost (implConjugate G₀.impl φ) S ε A qS (s_init, false)
        + Pr[fun z : Bool × Heap Ident => (φ z.2).2 = true |
            (simulateQ G₀.impl A).run (φ.symm (s_init, false))] := by
  classical
  have h_bridge := advantage_le_expectedSCost_plus_probEvent_bad_of_inv
    G₀ G₁ φ s_init h_init₀ h_init₁ Inv S ε h_step_tv_S
    h_step_eq_nS h_mono₀ A h_qb
  have h_cost_eq :
      expectedSCost (implConjugate G₀.impl φ) S
          (fun s => if Inv s then ε s else 1) A qS (s_init, false)
        = expectedSCost (implConjugate G₀.impl φ) S ε A qS (s_init, false) :=
    expectedSCost_eq_of_inv (implConjugate G₀.impl φ) S Inv
      (ε := fun s => if Inv s then ε s else 1) (ε' := ε)
      (fun s hs => by simp [hs]) h_pres A qS (s_init, false)
      (by intro _; exact h_init_inv)
  simpa [h_cost_eq] using h_bridge

/-! ### Constant-ε corollary -/

/-- Constant-ε identical-until-bad.

Constant-ε corollary of `advantage_le_expectedSCost_plus_probEvent_bad`,
derived by specialising `ε := fun _ => ε_const` and bounding
`expectedSCost` by `qS · ε_const` via `expectedSCost_const_le_qS_mul`. -/
theorem advantage_le_qSeps_plus_probEvent_bad
    (G₀ G₁ : Package unifSpec E Ident)
    (φ : Heap Ident ≃ σ × Bool) (s_init : σ)
    (h_init₀ : G₀.init = pure (φ.symm (s_init, false)))
    (h_init₁ : G₁.init = pure (φ.symm (s_init, false)))
    (S : E.Domain → Prop) [DecidablePred S]
    (ε : ℝ≥0∞)
    (h_step_tv_S : ∀ (t : E.Domain), S t → ∀ (s : σ),
      ENNReal.ofReal
        (tvDist ((G₀.impl t).run (φ.symm (s, false)))
                ((G₁.impl t).run (φ.symm (s, false)))) ≤ ε)
    (h_step_eq_nS : ∀ (t : E.Domain), ¬ S t → ∀ (h : Heap Ident),
      (G₀.impl t).run h = (G₁.impl t).run h)
    (h_mono₀ : ∀ (t : E.Domain) (h : Heap Ident), (φ h).2 = true →
      ∀ z ∈ support ((G₀.impl t).run h), (φ z.2).2 = true)
    (A : OracleComp E Bool) {qS : ℕ}
    (h_qb : OracleComp.IsQueryBoundP A S qS) :
    ENNReal.ofReal (G₀.advantage G₁ A)
      ≤ qS * ε
        + Pr[fun z : Bool × Heap Ident => (φ z.2).2 = true |
            (simulateQ G₀.impl A).run (φ.symm (s_init, false))] := by
  refine le_trans
    (advantage_le_expectedSCost_plus_probEvent_bad
      G₀ G₁ φ s_init h_init₀ h_init₁ S (fun _ => ε)
      h_step_tv_S h_step_eq_nS h_mono₀ A h_qb) ?_
  gcongr
  exact expectedSCost_const_le_qS_mul (implConjugate G₀.impl φ) S ε A h_qb (s_init, false)

end Package

end VCVio.HeapSSP
