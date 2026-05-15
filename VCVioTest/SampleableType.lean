/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# Regression tests for `SampleableType` and `HasUniformSelect` instance coverage

Inferable smoke tests for the instances added under issue #117. If any of these
`inferInstance` calls regress (e.g. an instance is renamed, removed, or its priority
changes so that it no longer fires), the build fails and the regression surfaces
without needing a runtime check.
-/

open OracleComp ProbComp ENNReal

section SampleableType

example : SampleableType Bool := inferInstance
example : SampleableType (Fin 3) := inferInstance
example : SampleableType (List.Vector Bool 3) := inferInstance
example : SampleableType (Vector Bool 3) := inferInstance

/-- The `Fin n → α` base instance is still present after the generalization. -/
example : SampleableType (Fin 3 → Bool) := inferInstance

/-- The general `FinEnum`-indexed function instance: any `FinEnum`-indexed function space
into a `SampleableType` is `SampleableType`. -/
example : SampleableType (Fin 4 → Fin 2) := inferInstance

/-- The original `Fin n × Fin m`-indexed Matrix instance. -/
example : SampleableType (Matrix (Fin 2) (Fin 2) Bool) := inferInstance

/-- The generalized `Matrix` instance: both row and column indices may be any `FinEnum`. -/
example : SampleableType (Matrix (Fin 2) (Fin 3) Bool) := inferInstance

/-- `Sum`-typed sampling works via `FinEnum.sum` + `FinEnum.SampleableType`. -/
example : SampleableType (Fin 2 ⊕ Fin 3) := inferInstance

/-- `Finset α` for a `FinEnum` element type: drawn uniformly from the `2^|α|` subsets. -/
example : SampleableType (Finset (Fin 3)) := inferInstance
example : SampleableType (Finset (Fin 4 ⊕ Fin 2)) := inferInstance

/-- Size-`n` multisets over a nonempty `Fintype`. -/
noncomputable example : SampleableType (Sym Bool 3) := inferInstance
noncomputable example : SampleableType (Sym (Fin 3) 2) := inferInstance

/-- Permutations of a finite type: `n!` outcomes. -/
noncomputable example : SampleableType (Equiv.Perm (Fin 3)) := inferInstance
noncomputable example : SampleableType (Equiv.Perm Bool) := inferInstance

/-- Function embeddings (injections) between finite types. The `Nonempty (β ↪ α)`
hypothesis amounts to `card β ≤ card α`, which is supplied at use-site. -/
noncomputable example : SampleableType (Fin 2 ↪ Fin 3) :=
  haveI : Nonempty (Fin 2 ↪ Fin 3) :=
    ⟨⟨Fin.castLE (by omega), Fin.castLE_injective _⟩⟩
  inferInstance
noncomputable example : SampleableType (Fin 3 ↪ Fin 3) :=
  haveI : Nonempty (Fin 3 ↪ Fin 3) := ⟨.refl _⟩
  inferInstance

end SampleableType

section HasUniformSelect

example : HasUniformSelect (List Bool) Bool := inferInstance
example : HasUniformSelect! (Vector Bool 3) Bool := inferInstance
example : HasUniformSelect! (List.Vector Bool 3) Bool := inferInstance
noncomputable example : HasUniformSelect (Finset Bool) Bool := inferInstance
example : HasUniformSelect (Array Bool) Bool := inferInstance
noncomputable example : HasUniformSelect (Multiset Bool) Bool := inferInstance

end HasUniformSelect

section MultisetProbabilities

/-- For a singleton multiset, sampling always returns the unique element with probability 1. -/
example : Pr[= true | ($ ({true} : Multiset Bool))] = 1 := by
  simp

end MultisetProbabilities
