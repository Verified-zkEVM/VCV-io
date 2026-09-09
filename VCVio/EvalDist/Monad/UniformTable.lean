/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Measure
public import ToMathlib.MeasureTheory.Measure.UniformTable

/-!
# Uniform table laws for measure-valued computations

Explicit uniform-measure hypotheses suffice to resample or extract table cells. The
continuation may return any measurable result space and may lose mass. No sampling
implementation or discrete probability representation is required.
-/

public section

open MeasureTheory ProbabilityTheory

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]
  {D R α : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
  [MeasurableSpace R] [MeasurableSingletonClass R] [MeasurableSpace α]

/-- Independent uniform cell resampling preserves every subsequent observation. -/
theorem evalDist_bind_bind_update (value : m R) (table : m (D → R))
    (hvalue : 𝒟[value] = uniformOn Set.univ) (htable : 𝒟[table] = uniformOn Set.univ)
    (t : D) (f : (D → R) → m α) :
    𝒟[value >>= fun u => table >>= fun g => f (Function.update g t u)] = 𝒟[table >>= f] := by
  have hupdate : 𝒟[value >>= fun u => (fun g => Function.update g t u) <$> table] =
      𝒟[table] := by
    simp_rw [evalDist_bind_of_discrete, evalDist_map_of_discrete, hvalue, htable]
    exact uniformOn_univ_bind_map_update t
  have hbind : (value >>= fun u => table >>= fun g => f (Function.update g t u)) =
      (value >>= fun u => (fun g => Function.update g t u) <$> table) >>= f := by
    simp only [bind_assoc, bind_map_left]
  rw [hbind, evalDist_bind_of_discrete _ f, hupdate, ← evalDist_bind_of_discrete]

/-- Independent uniform cell resampling preserves a pure observation of the table. -/
theorem evalDist_bind_bind_update_map (value : m R) (table : m (D → R))
    (hvalue : 𝒟[value] = uniformOn Set.univ) (htable : 𝒟[table] = uniformOn Set.univ)
    (t : D) (f : (D → R) → α) :
    𝒟[value >>= fun u => table >>= fun g => pure (f (Function.update g t u))] =
      𝒟[table >>= fun g => pure (f g)] :=
  evalDist_bind_bind_update value table hvalue htable t (fun g => pure (f g))

/-- Expose a uniform table cell before running the continuation that reads it. -/
theorem evalDist_bind_cell_extract (value : m R) (table : m (D → R))
    (hvalue : 𝒟[value] = uniformOn Set.univ) (htable : 𝒟[table] = uniformOn Set.univ)
    (t : D) (f : (D → R) → R → m α) :
    𝒟[table >>= fun g => f g (g t)] =
      𝒟[value >>= fun u => table >>= fun g => f (Function.update g t u) u] := by
  simpa only [Function.update_self] using
    (evalDist_bind_bind_update value table hvalue htable t (fun g => f g (g t))).symm

/-- Reindexing a finite uniform draw by a permutation preserves every continuation measure. -/
theorem evalDist_bind_uniform_equiv [Finite α] [MeasurableSingletonClass α]
    {β : Type} [MeasurableSpace β] (draw : m α)
    (hdraw : 𝒟[draw] = uniformOn Set.univ) (e : α ≃ α) (f : α → m β) :
    𝒟[draw >>= f] = 𝒟[draw >>= fun x => f (e x)] := by
  have hmap : 𝒟[e <$> draw] = 𝒟[draw] := by
    rw [evalDist_map_of_discrete, hdraw, uniformOn_univ_map_equiv]
  calc
    _ = 𝒟[(e <$> draw) >>= f] := by
      rw [evalDist_bind_of_discrete _ f, evalDist_bind_of_discrete _ f, hmap]
    _ = _ := by rw [bind_map_left]

/-- Independently resample two distinct table cells before observing the table. -/
theorem evalDist_bind_bind_bind_update_two_map (value : m R) (table : m (D → R))
    (hvalue : 𝒟[value] = uniformOn Set.univ) (htable : 𝒟[table] = uniformOn Set.univ)
    {t₁ t₂ : D} (hne : t₁ ≠ t₂) (f : (D → R) → α) :
    𝒟[value >>= fun u₁ => value >>= fun u₂ => table >>= fun g =>
      pure (f (Function.update (Function.update g t₁ u₁) t₂ u₂))] =
        𝒟[table >>= fun g => pure (f g)] := by
  simp_rw [Function.update_comm hne]
  trans 𝒟[value >>= fun u₁ => table >>= fun g => pure (f (Function.update g t₁ u₁))]
  · rw [evalDist_bind_of_discrete value, evalDist_bind_of_discrete value]
    exact Measure.bind_congr_right (Filter.Eventually.of_forall fun u₁ =>
      evalDist_bind_bind_update_map value table hvalue htable t₂
        (fun g => f (Function.update g t₁ u₁)))
  · exact evalDist_bind_bind_update_map value table hvalue htable t₁ f

/-- An injective table restriction preserves uniformity under explicitly calibrated draws. -/
theorem evalDist_map_table_comp_injective {A B : Type} [Finite A] [Finite B]
    (small : m (A → R)) (large : m (B → R))
    (hsmall : 𝒟[small] = uniformOn Set.univ) (hlarge : 𝒟[large] = uniformOn Set.univ)
    {e : A → B} (he : Function.Injective e) :
    𝒟[(fun g => g ∘ e) <$> large] = 𝒟[small] := by
  rw [evalDist_map_of_discrete, hsmall, hlarge]
  exact uniformOn_univ_map_comp_injective he
