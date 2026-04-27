/- 
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Relational

/-!
# Derived Relational Tactic Examples

This file validates relational consequence, inlining, and `@[vcspec]` lookup.
-/

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open OracleComp.ProgramLogic.Relational
open Lean.Order
open scoped OracleComp.ProgramLogic

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β γ : Type}

/-! ## `rel_conseq` / `rel_inline` / `rel_dist` -/

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rel_conseq
  · exact h
  · exact hpost

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rel_conseq with R
  · exact h
  · exact hpost

private def inlineId (oa : OracleComp spec α) : OracleComp spec α := oa

example (oa : OracleComp spec α) :
    ⟪inlineId oa ~ oa | EqRel α⟫ := by
  rel_inline inlineId

/-! ## Registered `@[vcspec]` relational theorems -/

@[irreducible] def wrappedTrueLeft : OracleComp spec Bool := pure true
@[irreducible] def wrappedTrueRight : OracleComp spec Bool := pure true

@[local vcspec] theorem relTriple_wrappedTruePair :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  simpa [wrappedTrueLeft, wrappedTrueRight] using
    (relTriple_refl (pure true : OracleComp spec Bool))

example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  rvcstep

example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | fun _ _ => True⟫ := by
  rvcstep

@[local vcspec] theorem rawRWP_wrappedTruePair :
    (1 : ℝ≥0∞) ⊑ (Std.Do'.rwp
      (Pred := ℝ≥0∞) (EPred₁ := Std.Do'.EPost.nil) (EPred₂ := Std.Do'.EPost.nil)
      (wrappedTrueLeft (spec := spec)) (wrappedTrueRight (spec := spec))
      (fun x y => if x = y then (1 : ℝ≥0∞) else 0)
      ⊥ₗ ⊥ₗ) := by
  simpa [wrappedTrueLeft, wrappedTrueRight] using
    (Std.Do'.RelWP.rwp_pure
      (m₁ := OracleComp spec) (m₂ := OracleComp spec)
      (Pred := ℝ≥0∞) (EPred₁ := Std.Do'.EPost.nil) (EPred₂ := Std.Do'.EPost.nil)
      true true (fun x y => if x = y then (1 : ℝ≥0∞) else 0)
      ⊥ₗ ⊥ₗ)

example :
    (1 : ℝ≥0∞) ⊑ (Std.Do'.rwp
      (Pred := ℝ≥0∞) (EPred₁ := Std.Do'.EPost.nil) (EPred₂ := Std.Do'.EPost.nil)
      (wrappedTrueLeft (spec := spec)) (wrappedTrueRight (spec := spec))
      (fun _ _ => (1 : ℝ≥0∞))
      ⊥ₗ ⊥ₗ) := by
  rvcstep

example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  rvcstep with relTriple_wrappedTruePair

/--
info: Try this:

  [apply] rvcstep with relTriple_wrappedTruePair
-/
#guard_msgs in
example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  rvcstep?

/--
error: rvcstep using hf: the explicit hint did not match the current relational goal shape.
`using` is interpreted by goal shape as one of:
- bind cut relation (`α → β → Prop`)
- bind bijection coupling (`α → α`, on synchronized uniform/query binds)
- random/query bijection (`α → α`)
- `List.mapM` / `List.foldlM` input relation
- `simulateQ` state relation

Viable local `using` hints here: `S`
Goal:
  ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫
-/
#guard_msgs in
example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcstep using hf

/-! ## Relational consequence close -/

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rvcgen
