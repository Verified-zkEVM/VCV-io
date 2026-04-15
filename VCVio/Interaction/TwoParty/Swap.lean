/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Append
import VCVio.Interaction.TwoParty.Role
import VCVio.Interaction.TwoParty.Decoration

/-!
# Swapping roles

Involutivity of `Role.swap`, compatibility with `RoleDecoration.map`, and interaction with
appended role decorations.
-/

universe u

namespace Interaction

@[simp, grind =]
theorem Role.swap_swap (r : Role) : r.swap.swap = r := by cases r <;> rfl

@[simp, grind =]
theorem RoleDecoration.swap_swap :
    (spec : Spec) → (roles : RoleDecoration spec) →
    roles.swap.swap = roles
  | .done, _ => rfl
  | .node _ rest, ⟨r, rRest⟩ => by
      simp only [Spec.Decoration.swap, Spec.Decoration.map, Role.swap_swap]
      congr 1; funext x
      exact RoleDecoration.swap_swap (rest x) (rRest x)

/-- Swapping commutes with appended role decorations. -/
theorem RoleDecoration.swap_append
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    (r₁ : RoleDecoration s₁)
    (r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)) :
    (r₁.append r₂).swap = r₁.swap.append (fun tr₁ => (r₂ tr₁).swap) :=
  Spec.Decoration.map_append (fun _ => Role.swap) s₁ s₂ r₁ r₂

end Interaction
