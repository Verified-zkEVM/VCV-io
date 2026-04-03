/- 
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.NotationCore
import VCVio.ProgramLogic.Relational.Quantitative

/-!
# Ergonomic Notation and Convenience Layer for Program Logic

This file extends `VCVio.ProgramLogic.NotationCore` with the heavier quantitative
bridge lemmas that depend on the full eRHL development.
-/

open ENNReal OracleSpec OracleComp

universe u

namespace OracleComp.ProgramLogic

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α : Type}

/-- Game equivalence from exact pRHL equality coupling. -/
theorem GameEquiv.of_relTriple'
    {g₁ g₂ : OracleComp spec₁ α}
    (h : Relational.RelTriple' (spec₁ := spec₁) (spec₂ := spec₁) g₁ g₂
      (Relational.EqRel α)) :
    GameEquiv g₁ g₂ :=
  Relational.gameEquiv_of_relTriple'_eqRel h

/-- Game equivalence from zero-error approximate coupling. -/
theorem GameEquiv.of_approxRelTriple_zero
    {g₁ g₂ : OracleComp spec₁ α}
    (h : Relational.ApproxRelTriple (spec₁ := spec₁) (spec₂ := spec₁) 0 g₁ g₂
      (Relational.EqRel α)) :
    GameEquiv g₁ g₂ :=
  GameEquiv.of_relTriple' ((Relational.relTriple'_eq_approxRelTriple_zero).mpr h)

end OracleComp.ProgramLogic
