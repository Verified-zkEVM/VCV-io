/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.RelWP
import VCVio.ProgramLogic.Unary.Loom.Quantitative
import VCVio.ProgramLogic.Relational.Quantitative

/-!
# Quantitative `RelWP` carrier for `OracleComp` (Loom2-style default)

This file is the **home** of the default quantitative `Std.Do'.RelWP`
instance for pairs of `OracleComp` programs valued in `ℝ≥0∞`. The
`rwpTrans` field wraps the existing `eRelWP`
(`VCVio/ProgramLogic/Relational/QuantitativeDefs.lean:31`); the three
`RelWP` axioms are discharged by the existing `eRelWP_pure`,
`eRelWP_bind_le`, `eRelWP_mono` lemmas
(`VCVio/ProgramLogic/Relational/Quantitative.lean`).

## Layout

This is one of three relational carriers we register on
`OracleComp`. Because `Std.Do'.RelWP`'s `Pred` is an `outParam`, only
one carrier can be *visible* to instance synthesis at a time. We
register them asymmetrically, matching the unary tier in
`VCVio/ProgramLogic/Unary/Loom/`:

* This file (`Loom/Quantitative.lean`) — the `ℝ≥0∞` carrier as a
  normal `instance`, always live once the file is imported. This is
  the default.
* `Loom/Qualitative.lean` — the `Prop` carrier as a `scoped instance`
  under `namespace OracleComp.Rel.Qualitative`, opt-in via
  `open OracleComp.Rel.Qualitative`.
* `Loom/Probabilistic.lean` — the `Prob` carrier as a `scoped
  instance` under `namespace OracleComp.Rel.Probabilistic`, opt-in
  via `open OracleComp.Rel.Probabilistic`.

There is no umbrella `Relational/Loom.lean` re-export. Consumers
import the specific carrier they need.

## Lattice plumbing

The `Lean.Order.{PartialOrder, CompleteLattice}` adapters for `ℝ≥0∞`
are shipped by `VCVio/ProgramLogic/Unary/Loom/Quantitative.lean` and
re-used here unchanged. We do not redefine them.
-/

open ENNReal Std.Do' OracleComp.ProgramLogic.Loom

universe u

namespace OracleComp.ProgramLogic.Relational.Loom

variable {ι₁ ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β : Type}

/-- Quantitative `Std.Do'.RelWP` interpretation of pairs of `OracleComp`
programs valued in `ℝ≥0∞`.

The `rwpTrans` is the existing `eRelWP` (the supremum over couplings
of expected values); the two `EPost.nil` arguments are ignored since
neither side of an `OracleComp` pair has a first-class exception slot.
The three `RelWP` axioms reduce to the existing `eRelWP_pure`,
`eRelWP_bind_le`, `eRelWP_mono` lemmas. -/
noncomputable instance instRelWP :
    Std.Do'.RelWP (OracleComp spec₁) (OracleComp spec₂) ℝ≥0∞
      Std.Do'.EPost.nil Std.Do'.EPost.nil where
  rwpTrans oa ob post _epost₁ _epost₂ :=
    OracleComp.ProgramLogic.Relational.eRelWP oa ob post
  rwp_trans_pure a b := by
    intro post _epost₁ _epost₂
    change post a b ≤
      OracleComp.ProgramLogic.Relational.eRelWP
        (pure a : OracleComp spec₁ _) (pure b : OracleComp spec₂ _) post
    rw [OracleComp.ProgramLogic.Relational.eRelWP_pure]
  rwp_trans_bind_le {α β γ δ} oa ob f g := by
    intro post _epost₁ _epost₂
    change OracleComp.ProgramLogic.Relational.eRelWP oa ob
            (fun a b => OracleComp.ProgramLogic.Relational.eRelWP (f a) (g b) post) ≤
          OracleComp.ProgramLogic.Relational.eRelWP (oa >>= f) (ob >>= g) post
    exact OracleComp.ProgramLogic.Relational.eRelWP_bind_le
      (spec₁ := spec₁) (spec₂ := spec₂) oa ob f g post
  rwp_trans_monotone {α β} oa ob post post' _epost₁ _epost₁' _epost₂ _epost₂' := by
    intro _h₁ _h₂ hpost
    change OracleComp.ProgramLogic.Relational.eRelWP oa ob post ≤
      OracleComp.ProgramLogic.Relational.eRelWP oa ob post'
    exact OracleComp.ProgramLogic.Relational.eRelWP_mono
      (spec₁ := spec₁) (spec₂ := spec₂) hpost

/-! ## Definitional alignment with `eRelWP`

The keystone lemma confirms `Std.Do'.rwp` agrees with `eRelWP` on the
nose, so every existing eRHL theorem in
`VCVio/ProgramLogic/Relational/Quantitative.lean` transports for free
when the user rewrites `Std.Do'.rwp _ _ _ _ _ ↦ eRelWP _ _ _`. -/

theorem rwp_eq_eRelWP
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (post : α → β → ℝ≥0∞) :
    Std.Do'.rwp oa ob post Lean.Order.bot Lean.Order.bot =
      OracleComp.ProgramLogic.Relational.eRelWP oa ob post := rfl

/-- `Std.Do'.RelTriple` agrees with `eRelTriple` propositionally. -/
theorem relTriple_iff_eRelTriple
    (pre : ℝ≥0∞) (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → ℝ≥0∞) :
    Std.Do'.RelTriple pre oa ob post Lean.Order.bot Lean.Order.bot ↔
      OracleComp.ProgramLogic.Relational.eRelTriple pre oa ob post :=
  Iff.rfl

end OracleComp.ProgramLogic.Relational.Loom
