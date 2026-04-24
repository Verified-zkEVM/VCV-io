/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Loom.WP.Basic
import VCVio.ProgramLogic.Unary.HoareTriple

-- NOTE: `import Loom.Triple.Basic` is intentionally omitted here — it's unused in this
-- file, and pulling it in transitively imports `Loom.WP.Lemmas` (via the `Loom.WP`
-- umbrella), which collides with `ExceptT.run_liftM` defined in
-- `VCVio/EvalDist/Instances/ErrorT.lean:84`. Commit 4 will need `Std.Do'.Triple`,
-- which lives in `Loom.Triple.Basic`; we'll rename our `ExceptT.run_liftM` then.
-- See `.ignore/wp-cutover-plan.md` §"Open questions", item 5.

/-!
# Quantitative `WP` carrier for `OracleComp` (Loom2 default)

Installs the **default** `Std.Do'.WP (OracleComp spec) ℝ≥0∞ EPost.nil`
instance, derived from the existing `MAlgOrdered (OracleComp spec) ℝ≥0∞`
algebra in `ToMathlib.Control.Monad.Algebra`. The new `Std.Do'.wp` agrees
*definitionally* with `MAlgOrdered.wp`, which lets every existing
quantitative `wp_*` theorem in `HoareTriple.lean` carry over to the new
`Std.Do'.WP.wp_*` framework unchanged:

* `Std.Do'.wp x post Std.Do'.EPost.nil.mk = MAlgOrdered.wp x post` — by `rfl`.

## Layout

This is one of two `WP` carriers we register on `OracleComp`. Because
`Std.Do'.WP`'s `Pred` and `EPred` are `outParam`s, only one carrier can be
*visible* to instance synthesis at a time. We register the carriers
asymmetrically:

* This file (`Loom/Quantitative.lean`) — the `ℝ≥0∞` carrier as a normal
  `instance`, always live once the file is imported. This is the default.
* `Loom/AlmostSure.lean` (Commit 3.1, planned) — the `Prop` carrier as a
  `scoped instance` under `namespace OracleComp.AlmostSure`, opt-in via
  `open OracleComp.AlmostSure`.

There is **no umbrella `Unary/Loom.lean` re-export**. Consumers import
the specific carrier they need (`…Unary.Loom.Quantitative` for the
default, `…Unary.Loom.AlmostSure` for the opt-in Prop one). This makes
the carrier choice explicit at every import site.

## Loom2 vs. Mathlib lattice plumbing

Loom2 builds on `Lean.Order.{PartialOrder, CompleteLattice, CCPO}` from
`Init.Internal.Order`, a class hierarchy distinct from Mathlib's
`Order.{PartialOrder, CompleteLattice}`. We provide the narrow `ℝ≥0∞`
adapters here; `Prop` ships with its own `Lean.Order` instances in
`Loom/LatticeExt.lean`.

When Volo's PR #12965 lands upstream and the `Std.Do.{WP,…}` API
stabilizes, this bridge collapses to a re-export and the lattice adapters
can move to a shared `ToMathlib/Order/LeanOrderAdapter.lean`.
-/

open ENNReal
open Std.Do'

universe u

namespace OracleComp.ProgramLogic.Loom

/-! ## `Lean.Order` adapters for `ℝ≥0∞` -/

/-- Bridge Mathlib's `≤` on `ℝ≥0∞` to `Lean.Order.PartialOrder`. -/
instance : Lean.Order.PartialOrder ℝ≥0∞ where
  rel a b := a ≤ b
  rel_refl := le_refl _
  rel_trans h₁ h₂ := le_trans h₁ h₂
  rel_antisymm := le_antisymm

/-- Bridge Mathlib's `sSup` on `ℝ≥0∞` to `Lean.Order.CompleteLattice`.

`Lean.Order.CompleteLattice.has_sup c` requires a least upper bound for the
predicate-encoded set `{x | c x}`. We discharge it with Mathlib's `sSup`
specialization. -/
instance : Lean.Order.CompleteLattice ℝ≥0∞ where
  has_sup c := by
    refine ⟨sSup {x | c x}, fun x => ?_⟩
    constructor
    · intro hsup y hcy
      have hle : y ≤ sSup {x | c x} := le_sSup (a := y) hcy
      exact le_trans hle hsup
    · intro h
      exact sSup_le (fun y hy => h y hy)

/-! ## `WP` instance for `OracleComp` -/

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β : Type}

/-- Quantitative `Std.Do'.WP` interpretation of `OracleComp spec` valued in `ℝ≥0∞`.

The `wpTrans` is the existing `MAlgOrdered.wp` (i.e. expectation of `post` under
`evalDist`); the `EPost.nil` argument is ignored since `OracleComp` has no
first-class exception slot. The three `WP` axioms reduce to the existing
`MAlgOrdered.{wp_pure, wp_bind, wp_mono}` equalities. -/
noncomputable instance instWP :
    Std.Do'.WP (OracleComp spec) ℝ≥0∞ Std.Do'.EPost.nil where
  wpTrans x := ⟨fun post _epost =>
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) x post⟩
  wp_trans_pure x := by
    intro post _epost
    change post x ≤ MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (pure x) post
    rw [MAlgOrdered.wp_pure]
  wp_trans_bind x f := by
    intro post _epost
    change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) x
            (fun a => MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (f a) post) ≤
          MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (x >>= f) post
    rw [MAlgOrdered.wp_bind]
  wp_trans_monotone x := by
    intro post post' _epost _epost' _hepost hpost
    exact MAlgOrdered.wp_mono (m := OracleComp spec) (l := ℝ≥0∞) x hpost

/-! ## Definitional alignment with `MAlgOrdered.wp`

The keystone lemma confirms `Std.Do'.wp` agrees with `MAlgOrdered.wp` on the nose,
so every existing quantitative `wp_*` theorem in `HoareTriple.lean` transports for
free when the user rewrites `Std.Do'.wp _ _ _ ↦ MAlgOrdered.wp _ _`. -/

theorem wp_eq_mAlgOrdered_wp
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Std.Do'.wp oa post Std.Do'.EPost.nil.mk =
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa post := rfl

end OracleComp.ProgramLogic.Loom
