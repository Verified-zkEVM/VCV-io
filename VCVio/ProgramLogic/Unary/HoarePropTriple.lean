/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.Algebra
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist

/-!
# Qualitative `Prop`-valued Hoare triples for `OracleComp`

This file registers the qualitative `Prop`-valued unary monad algebra for
`OracleComp spec`. The carrier is `Prop` with its standard complete-lattice structure
(`≤` is implication), and `μ (oa : OracleComp spec Prop)` is the almost-sure assertion
`allOutputsSatisfy id oa = ∀ x ∈ support oa, x`.

The induced `MAlgOrdered.wp` is the support-based weakest precondition:
`wp oa post ↔ allOutputsSatisfy post oa = ∀ x ∈ support oa, post x`.

This is the qualitative companion of the quantitative `MAlgOrdered (OracleComp spec) ℝ≥0∞`
in `VCVio/ProgramLogic/Unary/HoareTriple.lean`. Together they let
`MAlgRelOrdered.Anchored` (in `ToMathlib/Control/Monad/RelationalAlgebra.lean`) state
its anchoring axioms uniformly across the qualitative and quantitative settings.
-/

universe u

namespace OracleComp.ProgramLogic.PropLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable {α β : Type}

/-- The qualitative `Prop`-valued unary monad algebra for `OracleComp`.

`μ` is the almost-sure assertion `allOutputsSatisfy id`; the induced `wp` is the
support-based weakest precondition; `Triple pre oa post` is
`pre → allOutputsSatisfy post oa`. -/
instance instMAlgOrdered : MAlgOrdered (OracleComp spec) Prop where
  μ := allOutputsSatisfy id
  μ_pure x := propext (allOutputsSatisfy_pure id x)
  μ_bind_mono {α} f g hfg x := by
    change allOutputsSatisfy id (x >>= f) → allOutputsSatisfy id (x >>= g)
    rw [allOutputsSatisfy_bind, allOutputsSatisfy_bind]
    exact allOutputsSatisfy_mono hfg x

/-- Support-based characterization of the `Prop`-valued WP for `OracleComp`. -/
theorem wp_iff_forall_support (oa : OracleComp spec α) (post : α → Prop) :
    MAlgOrdered.wp (m := OracleComp spec) (l := Prop) oa post ↔
      ∀ x ∈ support oa, post x := by
  change allOutputsSatisfy id (oa >>= fun a => pure (post a)) ↔ _
  rw [allOutputsSatisfy_bind]
  simp only [allOutputsSatisfy_pure]
  exact allOutputsSatisfy_iff_forall_support _ oa

end OracleComp.ProgramLogic.PropLogic
