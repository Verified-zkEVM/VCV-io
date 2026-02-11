


-- lemma probOutput_true_eq_probOutput_false_not {ob : OracleComp spec Bool} :
--     [= true | ob] = [= false | do let b ← ob; return !b] := by
--   simp [probOutput_map_eq_sum_fintype_ite]

-- lemma probOutput_false_eq_probOutput_true_not {ob : OracleComp spec Bool} :
--     [= false | ob] = [= true | do let b ← ob; return !b] := by
--   simp [probOutput_true_eq_probOutput_false_not]
