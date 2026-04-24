/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Loom.WP.Basic
import VCVio.ProgramLogic.Unary.HoarePropTriple

/-!
# Qualitative `WP` carrier for `OracleComp` (`Prop`, scoped)

Installs the qualitative `Std.Do'.WP (OracleComp spec) Prop EPost.nil`
instance, derived from the existing `MAlgOrdered (OracleComp spec) Prop`
algebra in `VCVio/ProgramLogic/Unary/HoarePropTriple.lean`. The new
`Std.Do'.wp` agrees *definitionally* with the qualitative
`MAlgOrdered.wp`:

* `Std.Do'.wp x post Std.Do'.EPost.nil.mk = MAlgOrdered.wp (l := Prop) x post`
  by `rfl`.

This is the support-based / almost-sure carrier:
`MAlgOrdered.wp (l := Prop) oa post ↔ ∀ x ∈ support oa, post x`
(see `OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support`).

## Layout and discipline

Because `Std.Do'.WP`'s `Pred` and `EPred` are `outParam`s, only one
carrier can be visible to instance synthesis at a time. This carrier is
registered as a **`scoped instance`** under `namespace
OracleComp.Qualitative`, so it is not in the visible instance set unless
the user explicitly writes `open OracleComp.Qualitative`. The default
quantitative `ℝ≥0∞` carrier (in `Loom/Quantitative.lean`) remains a
normal `instance` and is always live.

Typical usage:

```
import VCVio.ProgramLogic.Unary.Loom.Qualitative
open OracleComp.Qualitative

example : ⦃True⦄ uniformOfFintype Bool ⦃fun b => b = true ∨ b = false⦄ := …
```

Never `open OracleComp.Qualitative` in a file that also relies on the
default quantitative carrier in the same elaboration scope; the
`outParam` engine will see two candidate `WP` instances and back out.
Use a `section ... end` block to localize the scope if needed.

The `Lean.Order.{PartialOrder, CompleteLattice}` adapters for `Prop` are
shipped by Loom2 in `Loom/LatticeExt.lean`, transitively imported via
`Loom.WP.Basic`; we do not redefine them here.

See `.ignore/wp-cutover-plan.md` §"Three-tier carrier design" and
§"Scoped instances" for the broader design.
-/

universe u

namespace OracleComp.Qualitative

variable {ι : Type u} {spec : OracleSpec ι}
variable {α β : Type}

/-- Qualitative `Std.Do'.WP` interpretation of `OracleComp spec` valued in `Prop`.

The `wpTrans` is the existing `Prop`-valued `MAlgOrdered.wp` (i.e.
`∀ x ∈ support oa, post x`); the `EPost.nil` argument is ignored since
`OracleComp` has no first-class exception slot. The three `WP` axioms
reduce to the existing `MAlgOrdered.{wp_pure, wp_bind, wp_mono}`
specialised at `l := Prop`.

This is a `scoped instance` rather than a normal `instance` because
`Std.Do'.WP`'s `Pred` is an `outParam`; making it scoped means it only
participates in synthesis when the user `open`s this namespace,
sidestepping the conflict with the default `ℝ≥0∞` carrier. -/
noncomputable scoped instance instWP :
    Std.Do'.WP (OracleComp spec) Prop Std.Do'.EPost.nil where
  wpTrans x := ⟨fun post _epost =>
    MAlgOrdered.wp (m := OracleComp spec) (l := Prop) x post⟩
  wp_trans_pure x := by
    intro post _epost
    change post x ≤ MAlgOrdered.wp (m := OracleComp spec) (l := Prop) (pure x) post
    rw [MAlgOrdered.wp_pure]
  wp_trans_bind x f := by
    intro post _epost
    change MAlgOrdered.wp (m := OracleComp spec) (l := Prop) x
            (fun a => MAlgOrdered.wp (m := OracleComp spec) (l := Prop) (f a) post) ≤
          MAlgOrdered.wp (m := OracleComp spec) (l := Prop) (x >>= f) post
    rw [MAlgOrdered.wp_bind]
  wp_trans_monotone x := by
    intro post post' _epost _epost' _hepost hpost
    exact MAlgOrdered.wp_mono (m := OracleComp spec) (l := Prop) x hpost

/-! ## Definitional alignment with `MAlgOrdered.wp` (Prop)

The keystone lemma confirms `Std.Do'.wp` agrees with the `Prop`-valued
`MAlgOrdered.wp` on the nose, so every existing qualitative `wp_*`
theorem in `HoarePropTriple.lean` (and the support-style lemma
`wp_iff_forall_support`) transports for free when the user rewrites
`Std.Do'.wp _ _ _ ↦ MAlgOrdered.wp (l := Prop) _ _`. -/

theorem wp_eq_mAlgOrdered_wp_prop
    (oa : OracleComp spec α) (post : α → Prop) :
    Std.Do'.wp oa post Std.Do'.EPost.nil.mk =
      MAlgOrdered.wp (m := OracleComp spec) (l := Prop) oa post := rfl

end OracleComp.Qualitative
