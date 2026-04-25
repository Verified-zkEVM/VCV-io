/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SeededFork
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Seed-Based Forking Lemma — Program Logic Bridge

Wraps the probabilistic seeded forking lemma bounds from
`CryptoFoundations/SeededFork.lean` as quantitative Hoare triples (`Triple`) for use in the
program logic framework.
-/


open OracleSpec OracleComp ENNReal

namespace OracleComp.ProgramLogic

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ i, SampleableType (spec.Range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]
  {α : Type}

variable (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    [spec.Fintype] [spec.Inhabited] [OracleSpec.LawfulSubSpec unifSpec spec]

/-- Seeded forking lemma as a quantitative Hoare triple for the fork-success event. -/
theorem triple_seededFork :
    Triple (spec := spec)
      (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
       let h : ℝ≥0∞ := Fintype.card (spec.Range i)
       let q := qb i + 1
       acc * (acc / q - h⁻¹))
      (seededFork main qb js i cf)
      (fun r => if r.isSome then 1 else 0) :=
  triple_ofLE
    (le_trans
      (OracleComp.le_probEvent_isSome_seededFork
        (main := main) (qb := qb) (js := js) (i := i) (cf := cf))
      (triple_toLE
        (triple_probEvent_indicator
          (oa := seededFork main qb js i cf) (p := fun r => r.isSome))))

end OracleComp.ProgramLogic
