/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.EvalDist
import ToMathlib.Control.WriterT

/-!
# Simulation using `WriterT` Monad Transformers

Lemmas about `simulateQ` with output monad `WriterT ω (OracleComp spec)` for some `ω`

Note we only handle `monoid` version of `WriterT`, append should be added eventually.
-/

open OracleSpec Function Prod

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec} {α : Type u} {ω : Type u} [Monoid ω]

-- lemma fst_map_writerT_run_simulateQ
--     {so : QueryImpl spec (WriterT ω (OracleComp spec))}
--     (hso : ∀ {α}, ∀ q : OracleQuery spec α, fst <$> (so.impl q).run = q)
--     (oa : OracleComp spec α) : fst <$> (simulateQ so oa).run = oa := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa h =>
--       simp_rw [simulateQ_bind, Function.comp_def, simulateQ_query, WriterT.run_bind, map_bind,
--         Functor.map_map, map_fst, id_eq, h, ← (congr_arg (· >>= oa) (hso (query i t))),
--         bind_map_left]
--   | failure => simp

-- lemma probFailure_writerT_run_simulateQ [spec.FiniteRange]
--     {so : QueryImpl spec (WriterT ω (OracleComp spec))}
--     (hso : ∀ {α}, ∀ q : OracleQuery spec α, fst <$> (so.impl q).run = q)
--     (hso' : ∀ {α}, ∀ q : OracleQuery spec α, [⊥ | (so.impl q).run] = 0)
--     (oa : OracleComp spec α) : [⊥ | (simulateQ so oa).run] = [⊥ | oa] := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa h =>
--       simp [probFailure_bind_eq_tsum, h, hso']
--       rw [ENNReal.tsum_prod']
--       refine tsum_congr fun x => ?_
--       simp [ENNReal.tsum_mul_right]
--       congr 1
--       calc ∑' (w : ω), [=(x, w) | (so.impl (query i t)).run]
--         _ = [= x | fst <$> (so.impl (query i t)).run] := by rw [probOutput_fst_map_eq_tsum]
--         _ = (↑(Fintype.card (spec.range i)))⁻¹ := by rw [hso, probOutput_query]
--   | failure => simp

-- -- TODO: less general version with `NeverFailWhen`
-- lemma NeverFail_writerT_run_simulateQ_iff
--     {so : QueryImpl spec (WriterT ω (OracleComp spec))}
--     (hso : ∀ {α}, ∀ q : OracleQuery spec α, (fst <$> (so.impl q).run).support = ⊤)
--     (hso' : ∀ {α}, ∀ q : OracleQuery spec α, (so.impl q).run.NeverFail)
--     (oa : OracleComp spec α) : (simulateQ so oa).run.NeverFail ↔ oa.NeverFail := by
--   sorry
  -- induction oa using OracleComp.inductionOn with
  -- | pure x => simp
  -- | failure => simp
  -- | query_bind i t oa h =>
  --     simp only [simulateQ_bind, simulateQ_query, WriterT.run_bind, noFailure_bind_iff, hso',
  --       noFailure_map_iff, h, Prod.forall, true_and, noFailure_query, support_liftM, Set.mem_univ,
  --       forall_const, Function.comp_def]
  --     refine ⟨fun h' x  => ?_, fun h' x w hw => h' x⟩
  --     have := congr_arg (x ∈ ·) (hso (query i t))
  --     simp only [support_map, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
  --       Set.top_eq_univ, Set.mem_univ, eq_iff_iff, iff_true] at this
  --     obtain ⟨w, hw⟩ := this
  --     exact h' x w hw

end OracleComp
