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
  unfold wrappedTrueLeft wrappedTrueRight
  rvcstep

example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  rvcstep

example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | fun _ _ => True⟫ := by
  rvcstep

@[irreducible] def wrappedAuxLeft : OracleComp spec Bool := pure true
@[irreducible] def wrappedAuxRight : OracleComp spec Bool := pure true

@[local vcspec] theorem relTriple_wrappedAuxPairStep (_haux : True) :
    ⟪wrappedAuxLeft (spec := spec) ~ wrappedAuxRight (spec := spec) | EqRel Bool⟫ := by
  unfold wrappedAuxLeft wrappedAuxRight
  rvcstep

example :
    ⟪wrappedAuxLeft (spec := spec) ~ wrappedAuxRight (spec := spec) | EqRel Bool⟫ := by
  rvcstep

example :
    ⟪wrappedAuxLeft (spec := spec) ~ wrappedAuxRight (spec := spec) | fun _ _ => True⟫ := by
  rvcstep

@[local vcspec] theorem rawRWP_wrappedTruePair :
    (1 : ℝ≥0∞) ⊑
      rwp⟦wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) |
        (fun x y => if x = y then (1 : ℝ≥0∞) else 0) ; epost⟨⟩, epost⟨⟩⟧ := by
  unfold wrappedTrueLeft wrappedTrueRight
  rvcstep

example :
    (1 : ℝ≥0∞) ⊑
      rwp⟦wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) |
        (fun _ _ => (1 : ℝ≥0∞)) ; epost⟨⟩, epost⟨⟩⟧ := by
  rvcstep
  intro a b
  split_ifs <;> simp

@[irreducible] def rawAuxLeft : OracleComp spec Bool := pure true
@[irreducible] def rawAuxRight : OracleComp spec Bool := pure true

@[local vcspec] theorem rawRWP_wrappedAuxPairStep (_haux : True) :
    (1 : ℝ≥0∞) ⊑
      rwp⟦rawAuxLeft (spec := spec) ~ rawAuxRight (spec := spec) |
        (fun x y => if x = y then (1 : ℝ≥0∞) else 0) ; epost⟨⟩, epost⟨⟩⟧ := by
  unfold rawAuxLeft rawAuxRight
  rvcstep

example :
    (1 : ℝ≥0∞) ⊑
      rwp⟦rawAuxLeft (spec := spec) ~ rawAuxRight (spec := spec) |
        (fun _ _ => (1 : ℝ≥0∞)) ; epost⟨⟩, epost⟨⟩⟧ := by
  rvcstep
  intro a b
  split_ifs <;> simp

example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  rvcstep with relTriple_wrappedTruePair

/-
These diagnostic guards preserve the shape of useful user-facing messages:
source theorem names and VCVio replay commands should remain visible, while the
exact wording may improve as the relational planner gets stronger.
-/
/--
info: Try this:

  [apply] rvcstep with relTriple_wrappedTruePair
-/
#guard_msgs in
example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | EqRel Bool⟫ := by
  rvcstep?

/--
error: rvcstep: found a `RelTriple` goal, but no relational VCGen rule matched.

Registered `@[vcspec]` candidates: `relTriple_wrappedTruePair`
Try `rvcstep?` or `rvcstep with <theorem>` for an explicit replay.
Left side:
  wrappedTrueLeft
Right side:
  wrappedTrueRight
Postcondition:
  fun x x_1 ↦ False
Consider `rel_conseq`, `rel_inline`, or `rel_dist` for a non-structural step.
-/
#guard_msgs in
example :
    ⟪wrappedTrueLeft (spec := spec) ~ wrappedTrueRight (spec := spec) | fun _ _ => False⟫ := by
  rvcstep

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

/--
info: Try this:

  [apply] rvcfinish
-/
#guard_msgs in
example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rvcstep?

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rvcgen!
