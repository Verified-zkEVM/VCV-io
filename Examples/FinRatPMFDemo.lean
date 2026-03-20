/- 
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.FinRatPMF

/-!
# FinRatPMF Demo

Small executable demos for the array-backed `FinRatPMF.Raw` evaluator and the
`simulateQ` executable oracle semantics.
-/

open OracleComp

namespace FinRatPMFDemo

instance : FinEnum Bool where
  card := 2
  equiv :=
    { toFun := fun b => if b then ⟨1, by decide⟩ else ⟨0, by decide⟩
      invFun := fun i => i.1 = 1
      left_inv := by
        intro b
        cases b <;> rfl
      right_inv := by
        intro i
        fin_cases i <;> rfl }
  decEq := inferInstance

instance : (t : coinSpec.Domain) → FinEnum (coinSpec.Range t) := by
  intro t
  change FinEnum Bool
  infer_instance

def xorTwoCoins : FinRatPMF.Raw Bool := do
  let b1 <- FinRatPMF.Raw.coin
  let b2 <- FinRatPMF.Raw.coin
  pure (b1 != b2)

def threeCoinCount : FinRatPMF.Raw Nat := do
  let b1 <- FinRatPMF.Raw.coin
  let b2 <- FinRatPMF.Raw.coin
  let b3 <- FinRatPMF.Raw.coin
  pure (cond b1 1 0 + cond b2 1 0 + cond b3 1 0)

def twoCoinQueries : OracleComp coinSpec Nat := do
  let b1 <- OracleComp.coin
  let b2 <- OracleComp.coin
  pure (cond b1 1 0 + cond b2 1 0)

#eval FinRatPMF.Raw.coin
#eval xorTwoCoins
#eval xorTwoCoins.normalize
#eval threeCoinCount.normalize
#eval! simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries
#eval! (simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries).normalize
#eval! (((simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries).normalize.prob 1 : ℚ≥0) : ℚ)

end FinRatPMFDemo
