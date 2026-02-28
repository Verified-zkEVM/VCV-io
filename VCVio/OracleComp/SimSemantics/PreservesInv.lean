/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.SimSemantics.StateT
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.EvalDist.Monad.Basic

/-!
# Oracle State Invariants for Shared-Oracle Simulations

This module provides minimal, **model-agnostic** infrastructure for reasoning about
shared, stateful oracle simulations (ROM/AGM/hybrids) via a user-supplied invariant
`Inv : σ → Prop` on oracle states.

We use **support-based** formulations (rather than `Pr[...] = 1`) to keep downstream
proofs lightweight.

## Main definitions

- `InitSatisfiesInv` — every sampled initial state satisfies the invariant
- `QueryImpl.PreservesInv` — every oracle query implementation step preserves `Inv`
- `OracleComp.simulateQ_run_preservesInv` — simulating any oracle computation
  with a preserving implementation preserves `Inv` on the final state
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
                  (liftM (OracleQuery.query t) : OracleComp spec (spec.Range t))).run σ0) >>=
              fun us => (simulateQ impl (oa us.1)).run us.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using hz
      rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
      have hq_run :
          (simulateQ impl (liftM (OracleQuery.query t) : OracleComp spec (spec.Range t))).run σ0 =
            (impl t).run σ0 := by
        have hq :
            simulateQ impl (liftM (OracleQuery.query t) : OracleComp spec (spec.Range t)) =
              (impl t) := by
          simp [OracleQuery.query_def, simulateQ_query]
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
    evalDist (mx.run' σ0) = evalDist (mx.run' σ1)

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

/-- If `mx` is output-independent on `Inv`, and `my` preserves `Inv` and never fails, then the
output distribution of `mx` is unchanged by running `my` first and then running `mx` on the
resulting state. -/
lemma outputIndependent_after_preservesInv {σ α β : Type}
    (mx : StateT σ ProbComp α) (my : StateT σ ProbComp β) (Inv : σ → Prop)
    (hmx : OutputIndependent mx Inv)
    (hmyInv : PreservesInv my Inv) :
    ∀ σ0, Inv σ0 →
      evalDist ((my.run σ0) >>= fun us => mx.run' us.2) = evalDist (mx.run' σ0) := by
  classical
  intro σ0 hσ0
  ext y
  have hconst :
      ∀ us : support (my.run σ0), Pr[= y | mx.run' us.1.2] = Pr[= y | mx.run' σ0] := by
    intro us
    have husInv : Inv us.1.2 := hmyInv σ0 hσ0 us.1 us.2
    have hdist : evalDist (mx.run' us.1.2) = evalDist (mx.run' σ0) :=
      hmx _ _ husInv hσ0
    simpa [probOutput_def] using congrArg (fun d => d y) hdist
  have hsum_support : (∑' us : support (my.run σ0), Pr[= us | my.run σ0]) = 1 := by
    have hsum_all :
        (∑' us : β × σ, Pr[= us | my.run σ0]) = 1 - Pr[⊥ | my.run σ0] := by
      simpa [probOutput_def, probFailure, SPMF.apply_eq_toPMF_some] using
        (SPMF.tsum_run_some_eq_one_sub (p := evalDist (my.run σ0)))
    have hsum_all' : (∑' us : β × σ, Pr[= us | my.run σ0]) = 1 := by
      simp [hsum_all]
    have hrestrict :
        (∑' us : support (my.run σ0), Pr[= us | my.run σ0]) =
          (∑' us : β × σ, Pr[= us | my.run σ0]) := by
      rw [tsum_subtype (support (my.run σ0)) (fun us : β × σ => Pr[= us | my.run σ0])]
      refine (tsum_congr fun us => ?_)
      by_cases hus : us ∈ support (my.run σ0)
      · simp [hus]
      · simp [hus, probOutput_eq_zero_of_not_mem_support hus]
    simp [hrestrict, hsum_all']
  calc
    Pr[= y | (my.run σ0 >>= fun us => mx.run' us.2)]
        = ∑' us : support (my.run σ0),
            Pr[= us | my.run σ0] * Pr[= y | mx.run' us.1.2] := by
          simpa using (probOutput_bind_eq_tsum_subtype (mx := my.run σ0)
            (my := fun us => mx.run' us.2) (y := y))
    _ = ∑' us : support (my.run σ0),
          Pr[= us | my.run σ0] * Pr[= y | mx.run' σ0] := by
          refine tsum_congr fun us => ?_
          simpa using congrArg (fun p => Pr[= us | my.run σ0] * p) (hconst us)
    _ = (∑' us : support (my.run σ0), Pr[= us | my.run σ0]) * Pr[= y | mx.run' σ0] := by
          simpa [mul_assoc] using
            (ENNReal.tsum_mul_right (f := fun us : support (my.run σ0) => Pr[= us | my.run σ0])
              (a := Pr[= y | mx.run' σ0]))
    _ = Pr[= y | mx.run' σ0] := by simp [hsum_support]

end StateT
