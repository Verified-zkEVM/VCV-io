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

/-- Forking lemma as a quantitative Hoare triple for the fork-success event. -/
theorem triple_fork :
    Triple (spec := spec)
      (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
       let h : ℝ≥0∞ := Fintype.card (spec.Range i)
       let q := qb i + 1
       acc * (acc / q - h⁻¹))
      (fork main qb js i cf)
      (fun r => if r.isSome then 1 else 0) := by
  refine le_trans ?_ (triple_probEvent_indicator (oa := fork main qb js i cf) (p := fun r => r.isSome))
  have hsome :
      Pr[fun r : Option (α × α) => r.isSome | fork main qb js i cf] =
        1 - Pr[= none | fork main qb js i cf] := by
    rw [probEvent_eq_tsum_ite]
    rw [tsum_option (fun r : Option (α × α) =>
      if r.isSome then Pr[= r | fork main qb js i cf] else 0) ENNReal.summable]
    simp only [Option.isSome, reduceCtorEq, ↓reduceIte, zero_add]
    have htotal :
        Pr[= none | fork main qb js i cf] + ∑' p, Pr[= some p | fork main qb js i cf] = 1 := by
      simpa [HasEvalPMF.probFailure_eq_zero, tsub_zero] using
        (probOutput_none_add_tsum_some (mx := fork main qb js i cf))
    have hsome_ne_top : (∑' p, Pr[= some p | fork main qb js i cf]) ≠ ⊤ :=
      ne_top_of_le_ne_top one_ne_top (htotal ▸ le_add_self)
    have hnone_ne_top : Pr[= none | fork main qb js i cf] ≠ ⊤ :=
      ne_top_of_le_ne_top one_ne_top probOutput_le_one
    have htotal' :
        (∑' p, Pr[= some p | fork main qb js i cf]) +
            Pr[= none | fork main qb js i cf] = 1 := by
      simpa [add_comm] using htotal
    exact ENNReal.eq_sub_of_add_eq hnone_ne_top htotal'
  rw [hsome]
  have hacc_le_one :
      ∑ s : Fin (qb i + 1), Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] ≤ 1 := by
    calc
      ∑ s, Pr[= (some s : Option _) | cf <$> main]
        ≤ ∑' x : Option (Fin (qb i + 1)), Pr[= x | cf <$> main] := by
            rw [← tsum_fintype (L := .unconditional _)]
            have h := tsum_option (fun x : Option (Fin (qb i + 1)) =>
              Pr[= x | cf <$> main]) ENNReal.summable
            rw [h]
            exact le_add_self
      _ ≤ 1 := tsum_probOutput_le_one
  have hpre_le_one :
      (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
       let h : ℝ≥0∞ := Fintype.card (spec.Range i)
       let q := qb i + 1
       acc * (acc / q - h⁻¹)) ≤ 1 := by
    simp only
    set acc : ℝ≥0∞ := ∑ s : Fin (qb i + 1),
      Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main]
    have hq : (1 : ℝ≥0∞) ≤ (↑(qb i + 1) : ℝ≥0∞) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (qb i))
    have hdiv_le_acc : acc / (↑(qb i + 1) : ℝ≥0∞) ≤ acc := by
      rw [div_eq_mul_inv]
      calc
        acc * ((↑(qb i + 1) : ℝ≥0∞))⁻¹ ≤ acc * 1 := by
          gcongr
          exact ENNReal.inv_le_one.2 hq
        _ = acc := by simp
    have hdiv_le_one : acc / (↑(qb i + 1) : ℝ≥0∞) ≤ 1 := by
      exact le_trans hdiv_le_acc (by simpa [acc] using hacc_le_one)
    calc
      acc * (acc / (↑(qb i + 1) : ℝ≥0∞) - (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹)
        ≤ acc * (acc / (↑(qb i + 1) : ℝ≥0∞)) := by gcongr; exact tsub_le_self
      _ ≤ acc * 1 := by gcongr
      _ ≤ 1 := by simpa [acc] using hacc_le_one
  have hfork := OracleComp.probOutput_none_fork_le
    (main := main) (qb := qb) (js := js) (i := i) (cf := cf)
  have hpre_ne_top :
      (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
       let h : ℝ≥0∞ := Fintype.card (spec.Range i)
       let q := qb i + 1
       acc * (acc / q - h⁻¹)) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top hpre_le_one
  have hnone_ne_top : Pr[= none | fork main qb js i cf] ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top probOutput_le_one
  have hfork' :
      Pr[= none | fork main qb js i cf] +
          (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
           let h : ℝ≥0∞ := Fintype.card (spec.Range i)
           let q := qb i + 1
           acc * (acc / q - h⁻¹)) ≤ 1 := by
    exact (ENNReal.le_sub_iff_add_le_right hpre_ne_top hpre_le_one).1 hfork
  exact (ENNReal.le_sub_iff_add_le_right hnone_ne_top probOutput_le_one).2 (by simpa [add_comm] using hfork')

end OracleComp.ProgramLogic
