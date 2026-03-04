/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.Basic
import VCVio.EvalDist.TVDist

/-!
# Quantitative Relational Program Logic (eRHL)

This file defines the eRHL-style quantitative relational logic for `OracleComp`.

The core idea (from Avanzini-Barthe-Gregoire-Davoli, POPL 2025) is to make pre/postconditions
`ℝ≥0∞`-valued instead of `Prop`-valued. This subsumes both pRHL (exact coupling, via indicator
postconditions) and apRHL (ε-approximate coupling, via threshold preconditions).

## Main definitions

- `eRelWP`: quantitative relational WP — supremum over couplings of expected postcondition
- `eRelTriple`: quantitative relational triple (`pre ≤ eRelWP oa ob post`)
- `RelPost.indicator`: indicator postcondition lifting `Prop` to `ℝ≥0∞`
- `RelTriple'`: pRHL-style exact coupling as eRHL special case
- `ApproxRelTriple`: apRHL-style ε-approximate coupling as eRHL special case

## Design

```
                eRHL (ℝ≥0∞-valued pre/post)
               /          |           \
              /           |            \
pRHL (exact)    apRHL (ε-approx)   stat-distance
indicator R      1-ε, indicator R    1, indicator(=)
```
-/

open scoped Classical
open ENNReal OracleSpec OracleComp

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β γ δ : Type}

/-! ## Core eRHL definitions -/

/-- eRHL-style quantitative relational WP for `OracleComp`.
`eRelWP oa ob g` = supremum over all couplings `c` of `E_c[g(a,b)]`.
This is the expected value of postcondition `g` under the optimal coupling. -/
noncomputable def eRelWP (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (g : α → β → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (c : SPMF.Coupling (evalDist oa) (evalDist ob)),
    ∑' z, Pr[= z | c.1] * g z.1 z.2

/-- eRHL triple: `pre ≤ eRelWP oa ob post`. -/
def eRelTriple (pre : ℝ≥0∞) (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → ℝ≥0∞) : Prop :=
  pre ≤ eRelWP oa ob post

/-! ## Indicator postconditions: bridge from Prop to ℝ≥0∞ -/

/-- Indicator postcondition: lifts a `Prop`-valued relation to an `ℝ≥0∞`-valued one. -/
noncomputable def RelPost.indicator (R : α → β → Prop) : α → β → ℝ≥0∞ :=
  fun a b => if R a b then 1 else 0

/-! ## pRHL as a special case of eRHL -/

/-- pRHL-style exact relational triple, defined via eRHL with indicator postcondition.
Equivalent to the existing coupling-based `CouplingPost`. -/
def RelTriple' (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  eRelTriple 1 oa ob (RelPost.indicator R)

/-- Bridge: the eRHL-based definition agrees with the existing coupling-based one. -/
theorem relTriple'_iff_couplingPost
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} :
    RelTriple' oa ob R ↔ CouplingPost oa ob R := by
  sorry

/-- Bridge: `RelTriple'` agrees with the existing `RelTriple`. -/
theorem relTriple'_iff_relTriple
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} :
    RelTriple' oa ob R ↔ RelTriple oa ob R := by
  rw [relTriple'_iff_couplingPost, relTriple_iff_relWP, relWP_iff_couplingPost]

/-! ## apRHL as a special case of eRHL -/

/-- ε-approximate relational triple via eRHL:
"R holds except with probability at most ε." -/
def ApproxRelTriple (ε : ℝ≥0∞) (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  eRelTriple (1 - ε) oa ob (RelPost.indicator R)

/-- Exact coupling is the zero-error special case of approximate coupling. -/
theorem relTriple'_eq_approxRelTriple_zero
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} :
    RelTriple' oa ob R ↔ ApproxRelTriple 0 oa ob R := by
  simp [RelTriple', ApproxRelTriple]

/-! ## eRHL rules -/

/-- Pure rule for eRHL. -/
theorem eRelTriple_pure (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    eRelTriple (post a b) (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) post := by
  sorry

/-- Monotonicity/consequence rule for eRHL. -/
theorem eRelTriple_conseq {pre pre' : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {post post' : α → β → ℝ≥0∞}
    (hpre : pre' ≤ pre) (hpost : ∀ a b, post a b ≤ post' a b)
    (h : eRelTriple pre oa ob post) :
    eRelTriple pre' oa ob post' := by
  sorry

/-- Bind/sequential composition rule for eRHL. -/
theorem eRelTriple_bind
    {pre : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {cut : α → β → ℝ≥0∞} {post : γ → δ → ℝ≥0∞}
    (hxy : eRelTriple pre oa ob cut)
    (hfg : ∀ a b, eRelTriple (cut a b) (fa a) (fb b) post) :
    eRelTriple pre (oa >>= fa) (ob >>= fb) post := by
  sorry

/-! ## Statistical distance via eRHL -/

/-- Statistical distance as a complement of eRHL value with equality indicator.
Uses `SPMF.tvDist` directly to handle cross-spec comparison. -/
theorem spmf_tvDist_eq_one_sub_eRelWP_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    SPMF.tvDist (evalDist oa) (evalDist ob) =
      (1 - eRelWP oa ob (RelPost.indicator (EqRel α))).toReal := by
  sorry

/-- Same-spec version using the `tvDist` notation. -/
theorem tvDist_eq_one_sub_eRelWP_eqRel
    {oa ob : OracleComp spec₁ α} :
    tvDist oa ob = (1 - eRelWP (spec₂ := spec₁) oa ob
      (RelPost.indicator (EqRel α))).toReal := by
  sorry

/-! ## pRHL convenience rules (Prop-level, no ℝ≥0∞ visible) -/

/-- Bind for pRHL exact coupling. -/
lemma relTriple'_bind
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {R : RelPost α β} {S : RelPost γ δ}
    (hxy : RelTriple' oa ob R)
    (hfg : ∀ a b, R a b → RelTriple' (fa a) (fb b) S) :
    RelTriple' (oa >>= fa) (ob >>= fb) S := by
  sorry

/-- Game equivalence from pRHL equality coupling. -/
theorem gameEquiv_of_relTriple'_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : RelTriple' oa ob (EqRel α)) :
    evalDist oa = evalDist ob := by
  exact evalDist_eq_of_relTriple_eqRel (relTriple'_iff_relTriple.mp h)

end OracleComp.ProgramLogic.Relational
