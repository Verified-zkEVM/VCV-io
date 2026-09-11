/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# `gcongr` through `wp`

Canaries for the `@[gcongr]` tag on `wp_mono`: `gcongr` descends through `wp` into the
postcondition, also under a finite sum, and `wp_eq_expectedValue` is the bridge to the
`expectedValue` laws.
-/

public section

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic

namespace VCVioTest.ProgramLogicGCongr

universe u

variable {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}

example (oa : OracleComp spec α) (f g : α → ℝ≥0∞) (h : ∀ x, f x ≤ g x) :
    wp oa f ≤ wp oa g := by
  gcongr with x
  exact h x

example (oa : OracleComp spec α) (f g : Fin 3 → α → ℝ≥0∞) (h : ∀ s x, f s x ≤ g s x) :
    ∑ s, wp oa (f s) ≤ ∑ s, wp oa (g s) := by
  gcongr with s _ x
  exact h s x

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp oa post = OracleComp.EvalDist.expectedValue oa post :=
  wp_eq_expectedValue oa post

/-- Support-aware descent exposes exactly the hypothesis needed by the continuation. -/
example (oa : OracleComp spec α) (f g : α → ℝ≥0∞)
    (h : ∀ x ∈ support oa, f x ≤ g x) : wp oa f ≤ wp oa g := by
  gcongr with x hx
  guard_hyp hx : x ∈ support oa
  guard_target = f x ≤ g x
  exact h x hx

example (oa : OracleComp spec α) (f g : Fin 3 → α → ℝ≥0∞)
    (h : ∀ i, ∀ x ∈ support oa, f i x ≤ g i x) :
    ∑ i, wp oa (f i) ≤ ∑ i, wp oa (g i) := by
  gcongr with i _ x hx
  exact h i x hx

/-- Raw Loom syntax needs an explicit façade change before congruence descent. -/
example (oa : OracleComp spec α) (f g : α → ℝ≥0∞)
    (h : ∀ x ∈ support oa, f x ≤ g x) :
    Std.Do'.wp oa f Lean.Order.bot ≤ Std.Do'.wp oa g Lean.Order.bot := by
  change wp oa f ≤ wp oa g
  gcongr with x hx
  exact h x hx

example [Finite α] (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    (hpost : ∀ x, post x ≠ ⊤) : wp oa post ≠ ⊤ := by finiteness

end VCVioTest.ProgramLogicGCongr
