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
`∀ x ∈ support oa, x`.

The induced `MAlgOrdered.wp` is the support-based weakest precondition:
`wp oa post ↔ ∀ x ∈ support oa, post x`.

This is the qualitative companion of the quantitative `MAlgOrdered (OracleComp spec) ℝ≥0∞`
in `VCVio/ProgramLogic/Unary/HoareTriple.lean`. Together they let
`MAlgRelOrdered.Anchored` (in `ToMathlib/Control/Monad/RelationalAlgebra.lean`) state
its anchoring axioms uniformly across the qualitative and quantitative settings.
-/

universe u

namespace OracleComp.ProgramLogic.PropLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable {α β : Type}

/-- Qualitative algebra for oracle computations returning `Prop`: the universal
quantifier over the support. -/
def μProp (oa : OracleComp spec Prop) : Prop :=
  ∀ x ∈ support oa, x

/-- The qualitative `Prop`-valued unary monad algebra for `OracleComp`.

`μ` is the almost-sure assertion `∀ x ∈ support oa, x`; `wp` is the support-based
weakest precondition; `Triple pre oa post` is `pre → ∀ x ∈ support oa, post x`. -/
instance instMAlgOrdered : MAlgOrdered (OracleComp spec) Prop where
  μ := μProp (spec := spec)
  μ_pure x := by
    refine propext ⟨fun h => h x ?_, fun hx p hp => ?_⟩
    · simp [support_pure]
    · have hpx : p ↔ x := by simpa [support_pure] using hp
      exact hpx.mpr hx
  μ_bind_mono {α} f g hfg x := by
    intro hf y hy
    rcases (mem_support_bind_iff x g y).1 hy with ⟨a, ha, hy'⟩
    have hfa : ∀ z ∈ support (f a), z := fun z hz =>
      hf z ((mem_support_bind_iff x f z).2 ⟨a, ha, hz⟩)
    exact hfg a hfa y hy'

/-- Support-based characterization of the `Prop`-valued WP for `OracleComp`. -/
theorem wp_iff_forall_support (oa : OracleComp spec α) (post : α → Prop) :
    MAlgOrdered.wp (m := OracleComp spec) (l := Prop) oa post ↔
      ∀ x ∈ support oa, post x := by
  unfold MAlgOrdered.wp
  change μProp (spec := spec) (oa >>= fun a => pure (post a)) ↔ _
  unfold μProp
  constructor
  · intro h a ha
    exact h (post a) ((mem_support_bind_iff oa _ (post a)).2
      ⟨a, ha, by simp [support_pure]⟩)
  · intro h p hp
    rcases (mem_support_bind_iff oa _ p).1 hp with ⟨a, ha, hp'⟩
    rw [show p = post a from by simpa [support_pure] using hp']
    exact h a ha

end OracleComp.ProgramLogic.PropLogic
