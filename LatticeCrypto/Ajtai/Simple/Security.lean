/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Simple.Correctness
import LatticeCrypto.HardnessAssumptions.ModuleShortIntegerSolution
import LatticeCrypto.Ring.Laws

/-!
# Security of the Simple Ajtai Commitment
-/

open OracleComp
open CommitmentScheme

universe u

namespace LatticeCrypto
namespace Ajtai
namespace Simple

variable {Coeff : Type u} [CommRing Coeff]

/-! ## Binding -/

/-- A binding adversary against simple Ajtai commitments yields a Module-SIS adversary. -/
def bindingAdvToModuleSIS (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [SampleableType (PublicParams ring rows cols)]
    [DecidableEq (Message ring cols)]
    [DecidableEq (Commitment ring rows)]
    (adv : BindingAdv
      (PublicParams ring rows cols)
      (Message ring cols)
      (Commitment ring rows)
      Opening) :
    ModuleSIS.Adversary ring rows cols (fun _ => true) :=
  fun A => do
    let (_c, s₁, _opening₁, s₂, _opening₂) ← adv A
    pure (s₁ - s₂)

/-- Binding of the simple Ajtai commitment reduces to Module-SIS.
TODO actually reduce to SIS. -/
theorem bindingAdvantage_le_moduleSIS (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PublicParams ring rows cols)]
    [DecidableEq (Message ring cols)]
    [DecidableEq (Commitment ring rows)]
    (linearLaws : NegacyclicRing.LinearLaws ring)
    (adv : BindingAdv
      (PublicParams ring rows cols)
      (Message ring cols)
      (Commitment ring rows)
      Opening) :
    bindingAdvantage (commitmentScheme ring rows cols) adv ≤
      ModuleSIS.advantage ring rows cols (fun _ => true) -- TODO replace fun true with a proper norm
        (bindingAdvToModuleSIS ring adv) := by
  unfold bindingAdvantage CommitmentScheme.bindingExp ModuleSIS.advantage
    SIS.advantage SIS.experiment ModuleSIS.problem bindingAdvToModuleSIS
    commitmentScheme ModuleSIS.relation
  simp only [monad_norm]
  refine probOutput_bind_mono fun A _ => ?_
  refine probOutput_bind_mono fun ⟨c, s₁, opening₁, s₂, opening₂⟩ _ => ?_
  by_cases hwin :
      (decide (s₁ ≠ s₂) &&
        verify ring A s₁ c opening₁ &&
        verify ring A s₂ c opening₂) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
    rcases hwin with ⟨⟨hne, hverify₁⟩, hverify₂⟩
    have hcommit₁ : commit ring A s₁ = c :=
      (verify_eq_true_iff ring A s₁ c opening₁).1 hverify₁
    have hcommit₂ : commit ring A s₂ = c :=
      (verify_eq_true_iff ring A s₂ c opening₂).1 hverify₂
    have hmat : ring.matVecMul A s₁ = ring.matVecMul A s₂ := by
      simpa [commit] using hcommit₁.trans hcommit₂.symm
    have hnonzero : s₁ - s₂ ≠ 0 := by
      intro hzero
      apply hne
      apply Vector.ext
      intro i hi
      have hget := congrArg (fun v : Message ring cols => v[i]) hzero
      have hcoordVec : s₁[i] - s₂[i] = (0 : Message ring cols)[i] := by
        simpa [Vector.getElem_sub] using hget
      have hzeroGet : (0 : Message ring cols)[i] = 0 := by
        rw [show (0 : Message ring cols) =
          Vector.ofFn (fun _ : Fin cols => (0 : ring.Poly)) by rfl]
        simp
      have hcoord : s₁[i] - s₂[i] = 0 :=
        hcoordVec.trans hzeroGet
      exact sub_eq_zero.mp hcoord
    have hker : ring.matVecMul A (s₁ - s₂) = 0 := by
      rw [linearLaws.matVecMul_sub A s₁ s₂, hmat]
      apply Vector.ext
      intro i hi
      rw [show (0 : PolyVec ring.Poly rows) =
        Vector.ofFn (fun _ : Fin rows => (0 : ring.Poly)) by rfl]
      simp [Vector.getElem_sub]
    simp [hne, hcommit₁, hcommit₂, hnonzero, hker]
  · have hleftFalse :
        ¬((s₁ ≠ s₂ ∧ commit ring A s₁ = c) ∧ commit ring A s₂ = c) := by
      intro hleft
      apply hwin
      simpa [verify] using hleft
    simp [hleftFalse]
end Simple
end Ajtai
end LatticeCrypto
