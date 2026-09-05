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
open Lean.Order
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

end VCVioTest.ProgramLogicGCongr
