/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.Fork
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Forking Lemma — Program Logic Bridge

Wraps the probabilistic forking lemma bounds from `CryptoFoundations/Fork.lean` as
quantitative Hoare triples (`Triple`) for use in the program logic framework.
-/

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace OracleComp.ProgramLogic

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ i, SampleableType (spec.Range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]
  {α : Type}

variable (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    [spec.Fintype] [spec.Inhabited] [OracleSpec.LawfulSubSpec unifSpec spec]

/-- Forking lemma as a quantitative Hoare triple: the expected value of any postcondition
on successful fork outputs is lower-bounded by the forking probability. -/
theorem triple_fork (post : α × α → ℝ≥0∞) :
    Triple (spec := spec)
      (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
       let h : ℝ≥0∞ := Fintype.card (spec.Range i)
       let q := qb i + 1
       acc * (acc / q - h⁻¹))
      (fork main qb js i cf)
      (fun r => match r with | some p => post p | none => 0) := by
  sorry

end OracleComp.ProgramLogic
