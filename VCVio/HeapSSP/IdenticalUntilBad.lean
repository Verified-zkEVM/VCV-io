/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Advantage
import VCVio.SSP.IdenticalUntilBad

/-!
# HeapSSP: Identical-Until-Bad

Heap-package counterpart of `VCVio.SSP.IdenticalUntilBad`, lifting the
state-dependent ε-perturbed identical-until-bad TV-distance bridge to
pairs of `HeapSSP.Package`s.

The HeapSSP `Package`'s native state is `Heap Ident`, but the bad-flag
accounting in the underlying
`ofReal_tvDist_simulateQ_le_expectedSCost_plus_probEvent_output_bad`
is specialised to `σ × Bool`. We bridge the two shapes by a user-supplied
bijection `φ : Heap Ident ≃ σ × Bool` together with an initial state
`s_init : σ` witnessing that both packages' init lands deterministically
in the no-bad heap `φ.symm (s_init, false)`. Users pick `φ` once per
game; the typical choice projects out a designated cell that carries the
bad flag. All per-query hypotheses remain in heap-native form, with the
bad flag accessed as `(φ h).2`.

Internally the proof routes through `VCVio.SSP.IdenticalUntilBad`: the
two heap impls are *conjugated* into SSP-shape impls on state `σ × Bool`
via `φ`, the SSP wrapper is applied, and the resulting advantage /
bad-event-probability terms are translated back to the heap side using
`simulateQ_StateT_evalDist_congr_of_bij` and `probEvent_congr'`.

## API

* `Package.implConjugate` — conjugate a heap handler through `φ` to an
  SSP-shape handler on state `σ × Bool`.
* `Package.advantage_le_expectedSCost_plus_probEvent_bad` — the
  state-dep ε form. Mirrors the SSP lemma of the same name.
* `Package.advantage_le_qSeps_plus_probEvent_bad` — the constant-ε
  corollary, derived from the state-dep form.
-/

open ENNReal OracleSpec OracleComp ProbComp
open OracleComp.ProgramLogic.Relational

namespace VCVio.HeapSSP

namespace Package

variable {ιₑ : Type} {E : OracleSpec.{0, 0} ιₑ}
  {Ident : Type} [CellSpec.{0, 0} Ident] {σ : Type}

/-! ### Conjugating a heap handler to an SSP handler -/

/-- Conjugate a heap-SSP handler through a bijection `φ : Heap Ident ≃ σ × Bool`
to an SSP handler on state `σ × Bool`. Each step unpacks the SSP state to a
heap via `φ.symm`, runs the heap handler, and repacks the result via `φ`. -/
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

/-! ### Bridging the heap `simulateQ` to the conjugated SSP `simulateQ` -/

/-- The whole-adversary analogue of `implConjugate_run_apply`: running a
`simulateQ` of the conjugated handler from an SSP state equals running
the heap-handler `simulateQ` from the heap state, mapped forward through
`φ`. Obtained from `simulateQ_StateT_evalDist_congr_of_bij` (the
SSP-level bijection lemma over arbitrary state types). -/
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

/-- On `run'` (discarding the state), the heap and conjugated SSP
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

/-- **Heap-SSP state-dep ε-perturbed identical-until-bad.**

Heap counterpart of
`VCVio.SSP.Package.advantage_le_expectedSCost_plus_probEvent_bad`.
With a bijection `φ : Heap Ident ≃ σ × Bool` extracting the bad flag,
and both games' init landing in the no-bad heap `φ.symm (s_init, false)`,
the advantage `G₀.advantage G₁ A` is bounded by the cumulative expected
ε-cost (computed on the conjugated SSP handler) plus the heap-side
probability that the bad flag fires in `G₀`'s execution.

The hypotheses mirror the SSP version, phrased in heap-native form:
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
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b)) :
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

/-! ### Constant-ε corollary -/

/-- **Heap-SSP constant-ε identical-until-bad.**

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
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if S t then 0 < b else True)
      (fun t b => if S t then b - 1 else b)) :
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
