/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import VCVio.ProgramLogic.Relational.Loom.Probabilistic
import VCVio.ProgramLogic.Relational.Loom.Qualitative

/-!
# Cross-tier coherence for the relational `RelWP` carriers

The three relational tiers (Qualitative, Probabilistic, Quantitative)
form a chain of refinements analogous to the unary case (see
`VCVio/ProgramLogic/Unary/Loom/Coherence.lean`):

```
                       indicator                       .val
  α → β → Prop  ─────────────────────▶  α → β → Prob  ─────────▶  α → β → ℝ≥0∞
  (CouplingPost)                        ([0, 1])                  (eRelWP)
```

Both edges have *coherence* lemmas relating their `rwp` values:

* **Probabilistic ↔ Quantitative** (definitional, `rfl`): the underlying
  `ℝ≥0∞` value of a probabilistic `rwp` is the quantitative `rwp` on
  the same post, viewed under `Subtype.val`. This is already proved as
  `OracleComp.Rel.Probabilistic.rwp_val_eq_eRelWP` in
  `…/Loom/Probabilistic.lean`.
* **Qualitative ↔ Quantitative** (this file, non-trivial): a coupling
  satisfying a `Prop`-valued relation `R` exists iff the quantitative
  `eRelWP` on the indicator of `R` equals `1`. This reduces to the
  existing `relTriple'_iff_couplingPost` bridge in
  `VCVio/ProgramLogic/Relational/Quantitative.lean`.

## Why state these against `eRelWP` rather than `Std.Do'.rwp`?

Both `OracleComp.Rel.Qualitative.instRelWP` and
`OracleComp.Rel.Probabilistic.instRelWP_prob` are `scoped instance`s.
To use `Std.Do'.rwp` for both at once we would have to `open` two
namespaces simultaneously, and `Std.Do'.RelWP`'s `Pred` is an
`outParam`, which would back out instance synthesis. Stating the
lemmas against `eRelWP` (and `CouplingPost`) directly sidesteps the
conflict; once a downstream user has chosen a single carrier, they
can rewrite from `Std.Do'.rwp _ _ _ _ _` to `eRelWP _ _ _` (or
`CouplingPost _ _ _`) via the keystone `rfl` lemmas in the
per-carrier files (`rwp_eq_eRelWP`, `rwp_eq_couplingPost`,
`rwp_val_eq_eRelWP`).

See `.ignore/wp-cutover-plan.md` §"Three-tier carrier design" for the
broader story.
-/

universe u

open ENNReal OracleComp.ProgramLogic.Relational

namespace OracleComp.Rel.Loom.Coherence

variable {ι₁ ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β : Type}

/-! ## Bound: `eRelWP` on an indicator post is always `≤ 1`

The relational expectation of an indicator post is bounded by `1`,
since the indicator itself is `≤ 1` pointwise and any coupling has
total mass `≤ 1`. -/

theorem eRelWP_indicator_le_one
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) :
    eRelWP oa ob (RelPost.indicator R) ≤ 1 := by
  unfold eRelWP
  refine iSup_le fun c => ?_
  calc ∑' z : α × β, Pr[= z | c.1] * RelPost.indicator R z.1 z.2
      ≤ ∑' z : α × β, Pr[= z | c.1] * 1 := by
        refine ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_
        unfold RelPost.indicator
        split_ifs <;> simp
    _ = ∑' z : α × β, Pr[= z | c.1] := by simp
    _ ≤ 1 := by rw [tsum_probOutput_eq_sub]; exact tsub_le_self

/-! ## Probabilistic ↔ Quantitative

The probabilistic `Std.Do'.rwp` agrees with the quantitative `eRelWP`
under `Subtype.val` by `rfl`; that statement lives in
`…/Loom/Probabilistic.lean` as
`OracleComp.Rel.Probabilistic.rwp_val_eq_eRelWP`. We do not restate it
here because pulling `OracleComp.Rel.Probabilistic.instRelWP_prob`
into scope to talk about `Std.Do'.rwp` requires
`open OracleComp.Rel.Probabilistic`, which then occludes the
qualitative tier discussed below. -/

/-! ## Qualitative ↔ Quantitative (coupling-existence vs total mass)

For an `OracleComp` pair, the support-based `Prop`-valued relational
WP (`CouplingPost`) holds iff the quantitative `eRelWP` on the
indicator post equals `1`. -/

/-- Qualitative ↔ Quantitative coherence: a `Prop`-valued relation
holds along some coupling iff the indicator of that relation has
quantitative `eRelWP` equal to `1`.

This is the relational analogue of
`OracleComp.Loom.Coherence.wp_qual_iff_wp_prob_indicator_eq_one` in
the unary file, and it reduces to the existing
`relTriple'_iff_couplingPost` bridge plus the upper bound
`eRelWP_indicator_le_one`. -/
theorem couplingPost_iff_eRelWP_indicator_eq_one
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) :
    CouplingPost oa ob R ↔
      eRelWP oa ob (RelPost.indicator R) = 1 := by
  constructor
  · intro h
    have h' : RelTriple' oa ob R := relTriple'_iff_couplingPost.mpr h
    have hge : 1 ≤ eRelWP oa ob (RelPost.indicator R) := h'
    exact le_antisymm (eRelWP_indicator_le_one oa ob R) hge
  · intro h
    apply relTriple'_iff_couplingPost.mp
    exact h.ge

/-- Convenience: rewrites the `couplingPost_iff_eRelWP_indicator_eq_one`
bridge as a `RelTriple'` equivalence. The `RelTriple'` form is the
eRHL-style triple with `pre = 1`. -/
theorem couplingPost_iff_relTriple'
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) :
    CouplingPost oa ob R ↔ RelTriple' oa ob R :=
  relTriple'_iff_couplingPost.symm

end OracleComp.Rel.Loom.Coherence
