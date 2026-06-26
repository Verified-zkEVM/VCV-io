/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.RelWP
import VCVio.ProgramLogic.Relational.Basic

/-!
# Qualitative `RelWP` carrier for `OracleComp` (`Prop`, scoped)

Installs the qualitative `Std.Do'.RelWP (OracleComp spec₁) (OracleComp spec₂)
Prop EPost.nil EPost.nil` instance, derived from the existing
`MAlgRelOrdered (OracleComp spec₁) (OracleComp spec₂) Prop` algebra in
`VCVio/ProgramLogic/Relational/Basic.lean`. The new `Std.Do'.rwp` agrees
*definitionally* with the qualitative `MAlgRelOrdered.rwp` (i.e.
`CouplingPost`):

* `Std.Do'.rwp x y post Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk =
    CouplingPost x y post`
  by `rfl`.

This is the support-based / coupling-existence carrier:
`CouplingPost oa ob R` holds iff there exists an SPMF coupling of
`evalDist oa` and `evalDist ob` whose support is contained in `R`.

## Layout and discipline

Because `Std.Do'.RelWP`'s `Pred`, `EPred₁`, `EPred₂` are `outParam`s,
only one carrier can be visible to instance synthesis at a time. This
carrier is registered as a **`scoped instance`** under `namespace
OracleComp.Rel.Qualitative`, so it is not in the visible instance set
unless the user explicitly writes `open OracleComp.Rel.Qualitative`. The
default quantitative `ℝ≥0∞` carrier (in `Loom/Quantitative.lean`)
remains a normal `instance` and is always live.

Typical usage:

```
import VCVio.ProgramLogic.Relational.Loom.Qualitative
open OracleComp.Rel.Qualitative

example : Std.Do'.RelTriple True (oa : OracleComp spec α) ob
    (fun a b => …) Lean.Order.bot Lean.Order.bot := …
```

Never `open OracleComp.Rel.Qualitative` in a file that also relies on
the default quantitative carrier in the same elaboration scope; the
`outParam` engine will see two candidate `RelWP` instances and back out.
Use a `section ... end` block to localize the scope if needed.

The `Lean.Order.{PartialOrder, CompleteLattice}` adapters for `Prop`
are shipped by Loom2 in `Loom/LatticeExt.lean`, transitively imported
via `Loom.WP.Basic` (through `ToMathlib/Control/Monad/RelWP.lean`); we
do not redefine them here.

See `.ignore/wp-cutover-plan.md` §"Three-tier carrier design" and
§"Scoped instances" for the broader design.
-/

universe u

open Std.Do'

namespace OracleComp.Rel.Qualitative

variable {ι₁ ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [IsUniformSpec spec₁] [IsUniformSpec spec₂]
variable {α β : Type}

/-- Qualitative `Std.Do'.RelWP` interpretation of pairs of `OracleComp`
programs valued in `Prop`.

The `rwpTrans` is the existing `Prop`-valued `MAlgRelOrdered.rwp` (i.e.
`CouplingPost`); the two `EPost.nil` arguments are ignored since
neither side of an `OracleComp` pair has a first-class exception slot.
The three `RelWP` axioms reduce to the existing
`MAlgRelOrdered.{rwp_pure, rwp_bind_le, rwp_mono}` lemmas specialised
at `l := Prop`.

This is a `scoped instance` rather than a normal `instance` because
`Std.Do'.RelWP`'s `Pred` is an `outParam`; making it scoped means it
only participates in synthesis when the user `open`s this namespace,
sidestepping the conflict with the default `ℝ≥0∞` carrier. -/
noncomputable scoped instance (priority := 1100) instRelWP :
    Std.Do'.RelWP (OracleComp spec₁) (OracleComp spec₂) Prop
      Std.Do'.EPost.nil Std.Do'.EPost.nil where
  rwpTrans oa ob post _epost₁ _epost₂ :=
    OracleComp.ProgramLogic.Relational.CouplingPost oa ob post
  rwp_trans_pure a b post _epost₁ _epost₂ :=
    (MAlgRelOrdered.rwp_pure (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop)
      a b post).symm.le
  rwp_trans_bind_le oa ob f g post _epost₁ _epost₂ :=
    MAlgRelOrdered.rwp_bind_le (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop)
      oa ob f g post
  rwp_trans_monotone _oa _ob _post _post' _epost₁ _epost₁' _epost₂ _epost₂'
      _h₁ _h₂ hpost :=
    MAlgRelOrdered.rwp_mono (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂)
      (l := Prop) hpost

/-! ## Definitional alignment with `CouplingPost`

The keystone lemma confirms `Std.Do'.rwp` agrees with `CouplingPost` on
the nose, so every existing pRHL theorem in
`VCVio/ProgramLogic/Relational/Basic.lean` transports for free when the
user rewrites `Std.Do'.rwp _ _ _ _ _ ↦ CouplingPost _ _ _`. -/

theorem rwp_eq_couplingPost (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → Prop) :
    Std.Do'.rwp oa ob post Lean.Order.bot Lean.Order.bot =
      OracleComp.ProgramLogic.Relational.CouplingPost oa ob post := rfl

/-- `Std.Do'.RelTriple` agrees with the qualitative `RelTriple`
propositionally. With `pre := True` and the two exception slots set to
`Lean.Order.bot`, the new triple is exactly the existing one. -/
theorem relTriple_iff_relTriple_basic
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : OracleComp.ProgramLogic.Relational.RelPost α β) :
    Std.Do'.RelTriple True oa ob R Lean.Order.bot Lean.Order.bot ↔
      OracleComp.ProgramLogic.Relational.RelTriple oa ob R :=
  Iff.rfl

end OracleComp.Rel.Qualitative
