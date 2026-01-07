
-- universe u v w

-- namespace OracleComp

-- variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type v}

-- @[simp]
-- lemma evalDist_orElse [h : spec.FiniteRange] (oa oa' : OracleComp spec α) :
--     evalDist (oa <|> oa') = (evalDist oa <|> evalDist oa') := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp [Option.elimM]; sorry
--   | failure => simp
--   | query_bind i t oa h => {
--     sorry
--   }
--   -- refine OptionT.ext ?_
--   -- rw [OptionT.run_orElse]
--   -- unfold evalDist
--   -- simp [simulateQ, OptionT.run, OptionT.mk, FreeMonad.mapM, OracleComp.orElse_def,
--   --   Option.elimM, bind_assoc, FreeMonad.bind]

--   -- sorry

-- @[simp]
-- lemma probFailure_orElse {ι : Type u} {spec : OracleSpec ι} {α : Type u} [h : spec.FiniteRange]
--     (oa oa' : OracleComp spec α) : [⊥ | oa <|> oa'] = [⊥ | oa] * [⊥ | oa'] := by
--   rw [probFailure_def, evalDist_orElse, OptionT.run_orElse]
--   simp [Option.elimM]
--   rw [tsum_option _ ENNReal.summable]
--   simp
--   rfl

-- @[simp]
-- lemma support_orElse {ι : Type u} {spec : OracleSpec ι} {α : Type u}
--     (oa oa' : OracleComp spec α) [Decidable oa.NeverFail] : (oa <|> oa').support =
--       if oa.NeverFail then oa.support else oa.support ∪ oa'.support := by
--   sorry

-- end OracleComp
