/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import VCVio.ProgramLogic.Relational.Basic

/-!
# Core eRHL Definitions

This file contains the lightweight definitions for the quantitative relational logic layer.
It is intentionally separated from the heavier coupling-development file so downstream users
that only need the interfaces and notation do not import the full theorem stack.
-/

open ENNReal OracleSpec OracleComp

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β : Type}

/-- eRHL-style quantitative relational WP for `OracleComp`.
`eRelWP oa ob g` is the supremum over all couplings `c` of the expected value of `g`
under `c`. -/
noncomputable def eRelWP (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (g : α → β → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (c : SPMF.Coupling (𝒟[oa]) (𝒟[ob])),
    ∑' z, Pr[= z | c.1] * g z.1 z.2

/-- Indicator postcondition: lifts a `Prop`-valued relation to an `ℝ≥0∞`-valued one. -/
noncomputable def RelPost.indicator (R : RelPost α β) (a : α) (b : β) : ℝ≥0∞ :=
  letI := Classical.dec (R a b)
  if R a b then 1 else 0

/-- pRHL-style exact relational triple, defined via quantitative relational WP with an
indicator postcondition. -/
def RelTriple' (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  1 ≤ eRelWP oa ob (RelPost.indicator R)

/-- ε-approximate relational triple via quantitative relational WP:
`R` holds except with probability at most `ε`. -/
def ApproxRelTriple (ε : ℝ≥0∞) (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  1 - ε ≤ eRelWP oa ob (RelPost.indicator R)

/-- Exact coupling is the zero-error special case of approximate coupling. -/
theorem relTriple'_eq_approxRelTriple_zero
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} :
    RelTriple' oa ob R ↔ ApproxRelTriple 0 oa ob R := by
  simp [RelTriple', ApproxRelTriple]

end OracleComp.ProgramLogic.Relational
