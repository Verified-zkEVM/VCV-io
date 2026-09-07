/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.SecurityFamily

/-!
# Dependent security-family packing checks

The family below varies its input, output, and oracle-answer types with the security parameter.
The equations ensure packing retains the parameter and both branch-dependent payloads rather than
collapsing the family to a pointwise collection.
-/

public section

namespace OracleComp.SecurityFamily

/-- A genuinely nonconstant oracle family: at parameter `n`, a query returns `Fin (n + 1)`. -/
@[expose]
def indexedSpec (n : Nat) : OracleSpec Unit :=
  fun _ ↦ Fin (n + 1)

/-- The input type varies with the security parameter. -/
abbrev IndexedInput (n : Nat) := Fin (n + 1)

/-- The output records both the dependent input and the dependent oracle answer. -/
abbrev IndexedOutput (n : Nat) := IndexedInput n × Fin (n + 1)

/-- One program family whose continuation uses both dependent values. -/
def indexedProgram (n : Nat) (input : IndexedInput n) :
    OracleComp (indexedSpec n) (IndexedOutput n) := do
  let answer ← (indexedSpec n).query ()
  pure (input, answer)

/-- Packing preserves the parameter in the query and returned sigma value. -/
example (n : Nat) (input : IndexedInput n) :
    packProgram indexedProgram ⟨n, input⟩ =
      OracleComp.queryBind (spec := Spec indexedSpec) ⟨n, ()⟩
        (fun answer ↦ pure ⟨n, (input, answer)⟩) :=
  rfl

/-- Packing a pure dependent result retains its index. -/
example (n : Nat) (value : IndexedOutput n) :
    packComp (spec := indexedSpec) (β := IndexedOutput) n (pure value) = pure ⟨n, value⟩ := by
  simp

/-- Distinct parameters remain distinct in the packed input type. -/
example :
    (⟨0, (0 : IndexedInput 0)⟩ : Input IndexedInput) ≠
      ⟨1, (0 : IndexedInput 1)⟩ := by
  simp

/-- Distinct parameters also remain distinct in the aggregate query domain. -/
example :
    (⟨0, PUnit.unit⟩ : (Spec indexedSpec).Domain) ≠ ⟨1, PUnit.unit⟩ := by
  simp

end OracleComp.SecurityFamily
