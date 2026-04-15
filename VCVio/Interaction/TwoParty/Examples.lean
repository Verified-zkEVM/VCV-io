/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.TwoParty.Role
import VCVio.Interaction.TwoParty.Decoration
import VCVio.Interaction.TwoParty.Strategy

/-!
# Examples: computing `withRoles` / `Counterpart` types

Small hand-crafted specs show how role-dependent strategy types unfold.
-/

universe u

namespace Interaction

section Examples

variable (m : Type u → Type u) [Monad m]
variable (T U : Type u) (α : Type u)

private def exSpec := Spec.node T fun _ => .node U fun _ => .done
private def exRoles : RoleDecoration (exSpec T U) :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨⟩⟩⟩

example : Spec.Strategy.withRoles m (exSpec T U) (exRoles T U) (fun _ => α)
    = m ((_ : T) × ((_ : U) → m α)) := rfl

example : Spec.Counterpart m (exSpec T U) (exRoles T U) (fun _ => α)
    = ((_ : T) → m (m ((_ : U) × α))) := rfl

end Examples
end Interaction
