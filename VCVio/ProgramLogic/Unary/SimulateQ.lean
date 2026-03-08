/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Unary.HoareTriple
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.SimSemantics.StateT
import VCVio.OracleComp.Coercions.SubSpec

/-!
# Oracle-Aware Unary WP Rules

This file connects the quantitative weakest precondition (`wp`) to `simulateQ`,
providing rules that let program logic proofs pass through oracle simulation boundaries.

## Main results

- `wp_simulateQ_eq`: If an oracle implementation preserves distributions, then `wp` is preserved.
- `wp_liftComp`: Lifting a computation to a larger oracle spec preserves `wp`.
- `wp_simulateQ_run'_eq`: Stateful oracle implementations that preserve distributions
  preserve `wp`.
-/

open ENNReal OracleSpec OracleComp

namespace OracleComp.ProgramLogic

variable {ι : Type*} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α : Type}


/-- If every oracle query in `impl` has the same evaluation distribution as the original query,
then `wp` of the simulated computation equals `wp` of the original. -/
@[game_rule] theorem wp_simulateQ_eq
    (impl : QueryImpl spec (OracleComp spec))
    (hImpl : ∀ (t : spec.Domain),
      evalDist (impl t) = evalDist (liftM (query t) : OracleComp spec (spec.Range t)))
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (simulateQ impl oa) post = wp oa post := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query]
    rw [wp_bind, wp_bind]
    simp_rw [ih]
    exact wp_congr_evalDist (hImpl t) _


/-- Lifting a computation to a larger oracle spec via `liftComp` preserves `wp`. -/
@[game_rule] theorem wp_liftComp {ι' : Type*} {superSpec : OracleSpec ι'}
    [superSpec.Fintype] [superSpec.Inhabited]
    [h : spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec]
    (mx : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (liftComp mx superSpec) post = wp mx post := by
  show @μ _ superSpec _ _ (liftComp mx superSpec >>= fun a => pure (post a)) =
       μ (mx >>= fun a => pure (post a))
  exact μ_cross_congr_evalDist
    (by simp only [evalDist_bind, evalDist_liftComp, evalDist_pure])

/-- If a stateful oracle implementation preserves distributions (each query produces a uniform
distribution after discarding state), then `wp` of `simulateQ ... run'` equals `wp` of the
original computation. -/
@[game_rule] theorem wp_simulateQ_run'_eq {σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp spec)))
    (hImpl : ∀ (t : spec.Domain) (s : σ),
      evalDist ((impl t).run' s) =
        OptionT.lift (PMF.uniformOfFintype (spec.Range t)))
    (oa : OracleComp spec α) (s : σ) (post : α → ℝ≥0∞) :
    wp ((simulateQ impl oa).run' s) post = wp oa post :=
  wp_congr_evalDist (evalDist_simulateQ_run'_eq_evalDist impl hImpl s oa) post

end OracleComp.ProgramLogic
