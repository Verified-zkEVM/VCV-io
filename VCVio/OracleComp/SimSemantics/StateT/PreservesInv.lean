/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions
import VCVio.EvalDist.Monad.Basic

/-!
# `StateT σ ProbComp` Invariant Theory

Support-based invariant reasoning for shared, stateful oracle simulations
(ROM/AGM/hybrids) whose handlers live in `StateT σ ProbComp`. A user-supplied
predicate `Inv : σ → Prop` is preserved by an implementation when every reachable
post-state satisfies it.

We use **support-based** formulations (rather than `Pr[ ...] = 1`) to keep
downstream proofs lightweight.

The `WriterT` analogue of this theory lives in
`SimSemantics/WriterT/PreservesInv.lean`.

## Main definitions

- `QueryImpl.PreservesInv` — every oracle query implementation step preserves `Inv`
- `OracleComp.simulateQ_run_preservesInv` — simulating any oracle computation
  with a preserving implementation preserves `Inv` on the final state
- `InitSatisfiesInv` — every sampled initial state satisfies the invariant
- `StateT.StatePreserving` — computation never changes the state
- `StateT.PreservesInv` — computation preserves an invariant on the state
- `StateT.NeverFailsUnder` — computation does not fail under an invariant
- `StateT.OutputIndependent` — output distribution is independent of the initial state
  under an invariant
- `StateT.outputIndependent_after_preservesInv` — non-interference: output-independent
  computation remains so after sequencing with an invariant-preserving computation
-/

noncomputable section

open OracleComp OracleSpec

open scoped OracleSpec.PrimitiveQuery

namespace QueryImpl

/-- `PreservesInv impl Inv` means every oracle query implementation step preserves `Inv`
on all reachable post-states (support-based). -/
def PreservesInv {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop) : Prop :=
  ∀ t σ0, Inv σ0 → ∀ z ∈ support ((impl t).run σ0), Inv z.2

lemma PreservesInv.trivial {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) :
    PreservesInv impl (fun _ => True) :=
  fun _ _ _ _ _ => True.intro

lemma PreservesInv.and {ι : Type} {spec : OracleSpec ι} {σ : Type}
    {impl : QueryImpl spec (StateT σ ProbComp)} {P Q : σ → Prop}
    (hP : PreservesInv impl P) (hQ : PreservesInv impl Q) :
    PreservesInv impl (fun s => P s ∧ Q s) :=
  fun t σ0 ⟨hp, hq⟩ z hz => ⟨hP t σ0 hp z hz, hQ t σ0 hq z hz⟩

lemma PreservesInv.of_forall {ι : Type} {spec : OracleSpec ι} {σ : Type}
    {impl : QueryImpl spec (StateT σ ProbComp)} {Inv : σ → Prop}
    (h : ∀ t σ0 z, z ∈ support ((impl t).run σ0) → Inv z.2) :
    PreservesInv impl Inv :=
  fun t σ0 _ z hz => h t σ0 z hz

end QueryImpl

namespace OracleComp

open QueryImpl

/-- If `impl` preserves `Inv`, then simulating *any* oracle computation with `simulateQ impl`
preserves `Inv` on the final state (support-wise). -/
theorem simulateQ_run_preservesInv
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop)
    (himpl : QueryImpl.PreservesInv impl Inv) :
    ∀ oa : OracleComp spec α,
    ∀ σ0, Inv σ0 →
      ∀ z ∈ support ((simulateQ impl oa).run σ0), Inv z.2 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro σ0 hσ0 z hz
      have : z = (a, σ0) := by
        simpa using (show z ∈ support (pure (a, σ0) : ProbComp (α × σ)) from by
          simpa using hz)
      simpa [this] using hσ0
  | query_bind t oa ih =>
      intro σ0 hσ0 z hz
      have hz' :
          z ∈ support
            (((simulateQ impl
                  (OracleSpec.query t : OracleComp spec (spec.Range t))).run σ0) >>=
              fun us => (simulateQ impl (oa us.1)).run us.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using hz
      rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
      have hq_run :
          (simulateQ impl (OracleSpec.query t : OracleComp spec (spec.Range t))).run σ0 =
            (impl t).run σ0 := by
        have hq :
            simulateQ impl (OracleSpec.query t : OracleComp spec (spec.Range t)) =
              (impl t) := by
          simp [OracleSpec.query_def, simulateQ_query]
        simp [hq]
      have hus' : us ∈ support ((impl t).run σ0) := by simpa [hq_run] using hus
      have hσ1 : Inv us.2 := himpl t σ0 hσ0 us hus'
      exact ih us.1 us.2 hσ1 z hzcont

end OracleComp

namespace QueryImpl

/-- If `so'` preserves `Inv`, then `so' ∘ₛ so` also preserves `Inv` for any `so`. -/
lemma PreservesInv.compose {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ : Type} {so' : QueryImpl spec' (StateT σ ProbComp)}
    {so : QueryImpl spec (OracleComp spec')} {Inv : σ → Prop}
    (h : PreservesInv so' Inv) :
    PreservesInv (so' ∘ₛ so) Inv :=
  fun t σ0 hσ0 z hz =>
    OracleComp.simulateQ_run_preservesInv so' Inv h (so t) σ0 hσ0 z
      (by simpa [apply_compose] using hz)

end QueryImpl

/-- `InitSatisfiesInv init Inv` means every possible initial state sampled by `init`
satisfies `Inv` (support-based). -/
def InitSatisfiesInv {σ : Type} (init : ProbComp σ) (Inv : σ → Prop) : Prop :=
  ∀ σ0 ∈ support init, Inv σ0

/-! ## StateT invariant properties

These properties are useful for **non-interference** arguments in sequential composition proofs.
They are stated for general `StateT σ ProbComp` computations. -/

namespace StateT

/-- `StatePreserving mx` means `mx` never changes the state: for every starting state `σ0`,
every outcome in the support of `mx.run σ0` has final state equal to `σ0`. -/
def StatePreserving {σ α : Type} (mx : StateT σ ProbComp α) : Prop :=
  ∀ σ0, ∀ z ∈ support (mx.run σ0), z.2 = σ0

/-- `PreservesInv mx Inv` means that starting from any state satisfying `Inv`, every reachable
post-state (support-wise) also satisfies `Inv`. -/
def PreservesInv {σ α : Type} (mx : StateT σ ProbComp α) (Inv : σ → Prop) : Prop :=
  ∀ σ0, Inv σ0 → ∀ z ∈ support (mx.run σ0), Inv z.2

/-- `NeverFailsUnder mx Inv` means that starting from any state satisfying `Inv`, the computation
does not fail (its failure probability is `0`). -/
def NeverFailsUnder {σ α : Type} (mx : StateT σ ProbComp α) (Inv : σ → Prop) : Prop :=
  ∀ σ0, Inv σ0 → Pr[⊥ | mx.run σ0] = 0

/-- `OutputIndependent mx Inv` means the output distribution of `mx` does not depend on the
initial state, as long as the initial state satisfies `Inv`.

This is distributional equality of `run'` (which discards the final state). -/
def OutputIndependent {σ α : Type} (mx : StateT σ ProbComp α) (Inv : σ → Prop) : Prop :=
  ∀ σ0 σ1, Inv σ0 → Inv σ1 →
    𝒟[mx.run' σ0] = 𝒟[mx.run' σ1]

@[simp] lemma statePreserving_pure {σ α : Type} (a : α) :
    StatePreserving (pure a : StateT σ ProbComp α) := by
  intro σ0 z hz
  have : z = (a, σ0) := by
    simpa using (show z ∈ support (pure (a, σ0) : ProbComp (α × σ)) from by
      simpa using hz)
  simp [this]

@[simp] lemma outputIndependent_pure {σ α : Type} (Inv : σ → Prop) (a : α) :
    OutputIndependent (pure a : StateT σ ProbComp α) Inv := by
  intro σ0 σ1 _ _
  dsimp [OutputIndependent]
  simp

lemma statePreserving_bind {σ α β : Type}
    (mx : StateT σ ProbComp α) (my : α → StateT σ ProbComp β)
    (h₁ : StatePreserving mx) (h₂ : ∀ a, StatePreserving (my a)) :
    StatePreserving (mx >>= my) := by
  intro σ0 z hz
  have hz' :
      z ∈ support ((mx.run σ0) >>= fun us => (my us.1).run us.2) := by
    simpa [StateT.run_bind] using hz
  rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hcont⟩
  have hσ : us.2 = σ0 := h₁ σ0 us hus
  have hzσ : z.2 = us.2 := h₂ us.1 us.2 z (by simpa using hcont)
  simp [hzσ, hσ]

lemma preservesInv_of_statePreserving {σ α : Type}
    (mx : StateT σ ProbComp α) (Inv : σ → Prop) (h : StatePreserving mx) :
    PreservesInv mx Inv := by
  intro σ0 hσ0 z hz
  simp [h σ0 z hz, hσ0]

lemma preservesInv_bind {σ α β : Type}
    (mx : StateT σ ProbComp α) (my : α → StateT σ ProbComp β)
    (Inv : σ → Prop) (h₁ : PreservesInv mx Inv) (h₂ : ∀ a, PreservesInv (my a) Inv) :
    PreservesInv (mx >>= my) Inv := by
  intro σ0 hσ0 z hz
  have hz' :
      z ∈ support ((mx.run σ0) >>= fun us => (my us.1).run us.2) := by
    simpa [StateT.run_bind] using hz
  rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hcont⟩
  exact h₂ us.1 us.2 (h₁ σ0 hσ0 us hus) z hcont

/-- If `mx` is output-independent on `Inv`, and `my` preserves `Inv` and never fails under `Inv`,
then the output distribution of `mx` is unchanged by running `my` first and then running `mx`
on the resulting state. -/
lemma outputIndependent_after_preservesInv {σ α β : Type}
    (mx : StateT σ ProbComp α) (my : StateT σ ProbComp β) (Inv : σ → Prop)
    (hmx : OutputIndependent mx Inv)
    (hmyInv : PreservesInv my Inv)
    (hmyNoFail : NeverFailsUnder my Inv) :
    ∀ σ0, Inv σ0 →
      𝒟[(my.run σ0) >>= fun us => mx.run' us.2] = 𝒟[mx.run' σ0] := by
  intro σ0 hσ0
  refine SPMF.ext fun a => ?_
  change Pr[= a | (my.run σ0) >>= fun us => mx.run' us.2] = Pr[= a | mx.run' σ0]
  rw [probOutput_bind_eq_tsum]
  have hbind_eq :
      (∑' us : β × σ, Pr[= us | my.run σ0] * Pr[= a | mx.run' us.2]) =
        (∑' us : β × σ, Pr[= us | my.run σ0]) * Pr[= a | mx.run' σ0] := by
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun us => ?_
    rcases eq_or_ne (Pr[= us | my.run σ0]) 0 with hus | hus
    · rw [hus, zero_mul, zero_mul]
    · have hus' : us ∈ support (my.run σ0) := by
        rw [mem_support_iff]; exact hus
      have hInv : Inv us.2 := hmyInv σ0 hσ0 us hus'
      simp only [probOutput_def, hmx us.2 σ0 hInv hσ0]
  rw [hbind_eq]
  have hsum : (∑' us : β × σ, Pr[= us | my.run σ0]) = 1 := by
    have hnofail : Pr[⊥ | my.run σ0] = 0 := hmyNoFail σ0 hσ0
    have htotal := tsum_probOutput_add_probFailure (my.run σ0)
    rw [hnofail, add_zero] at htotal
    exact htotal
  rw [hsum, one_mul]

end StateT
