/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Std.Tactic.Do
import VCVio.ProgramLogic.Unary.StdDoBridge
import VCVio.Interaction.UC.Runtime

/-!
# `Std.Do` / `mvcgen` bridge for the Interaction / UC runtime

Equip the runtime primitives in `VCVio.Interaction.UC.Runtime`
(`Spec.sampleTranscript`, `Concurrent.StepOver.sample`,
`Concurrent.ProcessOver.runSteps`) with the equational and Hoare-triple
machinery `mvcgen` needs, so users can prove triples about UC executions
in the same style as `VCVio.ProgramLogic.Unary.HandlerSpecs`.

## Architecture

The runtime primitives are defined by structural recursion over the
`Interaction.Spec` tree (for transcript sampling) or over fuel `ℕ` (for
`runSteps`). Neither recursion is walked by `mvcgen`, so we expose the
recursive equations as `@[simp]` lemmas and provide a closed-form
`runSteps_triple_preserves_invariant` for the most common
"fuel-indexed invariant" pattern.

The bridge is intentionally monad-parametric: every result is phrased
for an arbitrary `[Monad m] [WPMonad m ps]`. This covers both
`m = ProbComp` (coin-flip-only protocols) and
`m = OracleComp superSpec` (shared random oracle / CRS protocols),
since both carry `Std.Do.WPMonad` instances via
`VCVio.ProgramLogic.Unary.StdDoBridge`.

## Main results

* `Spec.sampleTranscript_done`, `Spec.sampleTranscript_node` — rfl-level
  unfolding of `Spec.sampleTranscript` for base and step cases.
* `Concurrent.StepOver.sample_eq` — unfolds `StepOver.sample` in terms
  of `sampleTranscript`.
* `Concurrent.ProcessOver.runSteps_zero`,
  `Concurrent.ProcessOver.runSteps_succ` — base and step unfolding of
  `runSteps` on fuel.
* `Concurrent.ProcessOver.runSteps_triple_preserves_invariant` — lifts
  a per-step invariant triple to a whole-`runSteps` triple, by
  induction on fuel.

All equations are proved by `rfl` and are tagged `@[simp]` so that
`mvcgen` can walk an exposed `sampleTranscript` / `sample` / `runSteps`
body in one simp pass before the usual `do`-block traversal.
-/

open Std.Do OracleComp

namespace Interaction

namespace Spec

section unfolding

variable {m : Type → Type} [Monad m]

@[simp]
theorem sampleTranscript_done (samp : Sampler m .done) :
    sampleTranscript .done samp = pure ⟨⟩ := rfl

@[simp]
theorem sampleTranscript_node {X : Type}
    (rest : X → Spec.{0}) (samp : m X) (sampRest : ∀ x, Sampler m (rest x)) :
    sampleTranscript (.node X rest) ⟨samp, sampRest⟩ =
      (do let x ← samp
          let tr ← sampleTranscript (rest x) (sampRest x)
          return ⟨x, tr⟩) := rfl

end unfolding

end Spec

namespace Concurrent

section StepOver

variable {m : Type → Type} [Monad m]
variable {Γ : Interaction.Spec.Node.Context.{0, 0}} {P : Type}

@[simp]
theorem StepOver.sample_eq (step : StepOver Γ P)
    (sampler : Spec.Sampler m step.spec) :
    step.sample sampler =
      (do let tr ← Spec.sampleTranscript step.spec sampler
          return step.next tr) := rfl

end StepOver

section ProcessOver

variable {m : Type → Type} [Monad m]
variable {Γ : Interaction.Spec.Node.Context.{0, 0}}

@[simp]
theorem ProcessOver.runSteps_zero
    (process : ProcessOver Γ)
    (sampler : ∀ p : process.Proc, Spec.Sampler m (process.step p).spec)
    (s : process.Proc) :
    process.runSteps sampler 0 s = pure s := rfl

@[simp]
theorem ProcessOver.runSteps_succ
    (process : ProcessOver Γ)
    (sampler : ∀ p : process.Proc, Spec.Sampler m (process.step p).spec)
    (n : ℕ) (s : process.Proc) :
    process.runSteps sampler (n + 1) s =
      (do let s' ← (process.step s).sample (sampler s)
          process.runSteps sampler n s') := rfl

end ProcessOver

end Concurrent

/-! ## Invariant preservation for `runSteps` -/

namespace Concurrent
namespace ProcessOver

variable {m : Type → Type} [Monad m]
variable {ps : PostShape} [WPMonad m ps]
variable {Γ : Interaction.Spec.Node.Context.{0, 0}}

/-- If every one-step execution preserves an invariant `I` on the
process state, then `runSteps n` preserves `I` for any fuel `n`.

This is the process-runtime analogue of
`OracleComp.ProgramLogic.StdDo.simulateQ_triple_preserves_invariant`:
a generic invariant lemma that factors out the fuel induction so
downstream proofs stay inside the `Std.Do` world. -/
theorem runSteps_triple_preserves_invariant
    (process : ProcessOver Γ)
    (sampler : ∀ p : process.Proc, Spec.Sampler m (process.step p).spec)
    (I : process.Proc → Prop)
    (hstep : ∀ p : process.Proc,
      Std.Do.Triple ((process.step p).sample (sampler p))
        (spred(⌜I p⌝))
        (⇓ p' => ⌜I p'⌝))
    (n : ℕ) (s₀ : process.Proc) :
    Std.Do.Triple
      (process.runSteps sampler n s₀)
      (spred(⌜I s₀⌝))
      (⇓ s' => ⌜I s'⌝) := by
  induction n generalizing s₀ with
  | zero =>
    simp only [runSteps_zero]
    exact Triple.pure s₀ .rfl
  | succ n ih =>
    simp only [runSteps_succ]
    exact Triple.bind _ _ (hstep s₀) (fun s' => ih s')

end ProcessOver
end Concurrent

end Interaction

/-! ## Smoke test: increment process

A minimal worked example demonstrating the bridge: an always-increment
process over `Proc := ℕ` whose every step advances the counter by one
without consuming any moves. The counter is trivially monotone and the
whole-execution corollary follows directly from
`runSteps_triple_preserves_invariant`. -/

namespace Interaction.Concurrent.ProcessOver

namespace Example

/-- Trivial node context carrying no per-node metadata. -/
private abbrev trivCtx : Interaction.Spec.Node.Context.{0, 0} := fun _ => PUnit

/-- Always-increment process: each step has no moves and bumps the
counter by one. -/
private noncomputable def incrementProcess : ProcessOver trivCtx where
  Proc := ℕ
  step p :=
    { spec := .done
      semantics := PUnit.unit
      next := fun _ => p + 1 }

/-- Trivial sampler for the always-`.done` step-spec family. -/
private def trivSampler :
    ∀ p : incrementProcess.Proc,
      Interaction.Spec.Sampler ProbComp (incrementProcess.step p).spec :=
  fun _ => PUnit.unit

private theorem incrementProcess_step_triple (p₀ p : ℕ) :
    Std.Do.Triple
      ((incrementProcess.step p).sample (trivSampler p) : ProbComp _)
      (spred(⌜p₀ ≤ p⌝))
      (⇓ p' => ⌜p₀ ≤ p'⌝) := by
  have hrw : (incrementProcess.step p).sample (trivSampler p)
      = (pure (p + 1) : ProbComp _) := rfl
  rw [hrw]
  refine Std.Do.Triple.pure (p + 1) ?_
  simp only [SPred.entails_nil, SPred.down_pure]
  intro hp; omega

/-- Smoke-test corollary: `runSteps` over `incrementProcess` never
decreases the counter. -/
private example (p₀ : ℕ) (n : ℕ) :
    Std.Do.Triple
      (incrementProcess.runSteps trivSampler n p₀ : ProbComp ℕ)
      (spred(⌜p₀ ≤ p₀⌝))
      (⇓ p' => ⌜p₀ ≤ p'⌝) :=
  runSteps_triple_preserves_invariant (m := ProbComp)
    incrementProcess trivSampler (fun s => p₀ ≤ s)
    (fun p => incrementProcess_step_triple p₀ p) n p₀

end Example

end Interaction.Concurrent.ProcessOver
