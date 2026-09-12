/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.EvalDist.PFunctorMeasure.Core

/-!
# Native uniform-table regression checks

These imports exclude discrete probability compatibility machinery. Tests cover two
cell updates, restriction to an empty domain, and continuations with missing mass.
-/

public section

open MeasureTheory ProbabilityTheory

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "native table imports unexpectedly include {name}"

namespace VCVioTest.UniformTable

example :
    (uniformOn Set.univ : Measure (Fin 3 → Bool)).map (fun g => g ∘ Fin.elim0) =
      (uniformOn Set.univ : Measure (Fin 0 → Bool)) :=
  uniformOn_univ_map_comp_injective (Function.injective_of_subsingleton _)

example (t : Fin 3) :
    ((uniformOn Set.univ : Measure Bool).bind (fun u =>
      (uniformOn Set.univ : Measure (Fin 3 → Bool)).map (fun g => Function.update g t u))).bind
        (fun g => (1 / 2 : ENNReal) • Measure.dirac (g 0)) =
      (uniformOn Set.univ : Measure (Fin 3 → Bool)).bind
        (fun g => (1 / 2 : ENNReal) • Measure.dirac (g 0)) := by
  rw [uniformOn_univ_bind_map_update]

example (t : Fin 3) :
    ((uniformOn Set.univ : Measure Bool).bind (fun u =>
      (uniformOn Set.univ : Measure (Fin 3 → Bool)).map (fun g => Function.update g t u))).bind
        (fun _ => (0 : Measure ℝ)) = 0 := by
  simp

example {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] (value : m Bool) (table : m (Fin 3 → Bool))
    (hvalue : 𝒟[value] = uniformOn Set.univ) (htable : 𝒟[table] = uniformOn Set.univ) :
    𝒟[value >>= fun u => value >>= fun v => table >>= fun g =>
      pure ((Function.update (Function.update g 0 u) 2 v) 1)] =
      𝒟[table >>= fun g => pure (g 1)] := by
  exact evalDist_bind_bind_bind_update_two_map value table hvalue htable (by decide) (fun g => g 1)

end VCVioTest.UniformTable
