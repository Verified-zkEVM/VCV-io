/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.Basic

/-!
# Relational program-logic examples
-/

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β γ δ : Type}

example {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {R : RelPost α β} {S : RelPost γ δ}
    (hxy : RelTriple oa ob R)
    (hfg : ∀ a b, R a b → RelTriple (fa a) (fb b) S) :
    RelTriple (oa >>= fa) (ob >>= fb) S :=
  relTriple_bind hxy hfg

example (oa : OracleComp spec₁ α) :
    RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa oa (EqRel α) :=
  relTriple_refl (spec₁ := spec₁) oa

end OracleComp.ProgramLogic.Relational
