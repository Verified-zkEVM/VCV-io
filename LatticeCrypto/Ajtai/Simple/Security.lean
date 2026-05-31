/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Simple.Correctness
import LatticeCrypto.HardnessAssumptions.ModuleShortIntegerSolution
import LatticeCrypto.Ring.VectorCommRing
import LatticeCrypto.Ring.NormBounds

/-!
# Security of the Simple Ajtai Commitment

Binding of the simple non-hiding Ajtai commitment reduces to Module-SIS over the
canonical vector-backed negacyclic ring `vectorNegacyclicRing (ZMod q) d`, under
the centered squared-`ℓ₂` norm `zmodPolyNormOps q (vectorBackend (ZMod q) d)`. A
binding adversary whose two opened messages each have squared-`ℓ₂` norm at most
`boundSq` yields a Module-SIS witness whose norm is within `subL2NormSqBound
boundSq = 4 · boundSq` (via `LatticeCrypto.sub_l2NormSq_le`).
-/

open OracleComp ENNReal
open CommitmentScheme

universe u

namespace LatticeCrypto
namespace Ajtai
namespace Simple

variable {Coeff : Type u} [CommRing Coeff]

/-! ## Binding -/

/-- A binding adversary against simple Ajtai commitments yields a Module-SIS adversary
for any short-vector predicate `isShort`: the extracted witness is the difference of the
two opened messages. -/
def bindingAdvToModuleSIS (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [SampleableType (PublicParams ring rows cols)]
    [DecidableEq (Message ring cols)]
    [DecidableEq (Commitment ring rows)]
    (isShort : ModuleSIS.Solution ring cols → Bool)
    (adv : BindingAdv
      (PublicParams ring rows cols)
      (Message ring cols)
      (Commitment ring rows)
      Opening) :
    ModuleSIS.Adversary ring rows cols isShort :=
  fun A => do
    let (_c, s₁, _opening₁, s₂, _opening₂) ← adv A
    pure (s₁ - s₂)

section Canonical

variable {q : ℕ} [NeZero q] [Fact (1 < q)] {d : ℕ} [NeZero d]

/-- Binding of the simple Ajtai commitment reduces to Module-SIS.

The commitment scheme accepts an opening only when the message has squared-`ℓ₂` norm at
most `boundSq`, so a winning binding adversary produces two short messages `s₁ ≠ s₂` with
`A·s₁ = A·s₂`. Their difference is a nonzero kernel vector within `subL2NormSqBound boundSq
= 4 · boundSq` (via `LatticeCrypto.sub_l2NormSq_le`), hence a valid Module-SIS witness. -/
theorem bindingAdvantage_le_moduleSIS (rows cols : Nat) (boundSq : ℕ)
    [SampleableType (PublicParams R rows cols)]
    [DecidableEq (Message R cols)]
    [DecidableEq (Commitment R rows)]
    (adv : BindingAdv
      (PublicParams R rows cols)
      (Message R cols)
      (Commitment R rows)
      Opening) :
    bindingAdvantage
        (commitmentScheme R rows cols
          (fun s => decide (‖s‖⟪normOps⟫₂² ≤ boundSq))) adv ≤
      ModuleSIS.advantage R rows cols
        (fun z => decide (‖z‖⟪normOps⟫₂² ≤ subL2NormSqBound boundSq))
        (bindingAdvToModuleSIS R
          (fun z => decide (‖z‖⟪normOps⟫₂² ≤ subL2NormSqBound boundSq)) adv) := by
  unfold bindingAdvantage CommitmentScheme.bindingExp ModuleSIS.advantage
    SIS.advantage SIS.experiment ModuleSIS.problem bindingAdvToModuleSIS
    commitmentScheme ModuleSIS.relation
  simp only [monad_norm]
  refine probOutput_bind_mono fun A _ => ?_
  refine probOutput_bind_mono fun ⟨c, s₁, opening₁, s₂, opening₂⟩ _ => ?_
  by_cases hwin :
      (decide (s₁ ≠ s₂) &&
        (decide (‖s₁‖⟪normOps⟫₂² ≤ boundSq) && verify R A s₁ c opening₁) &&
        (decide (‖s₂‖⟪normOps⟫₂² ≤ boundSq) && verify R A s₂ c opening₂)) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
    rcases hwin with ⟨⟨hne, hshort₁, hverify₁⟩, hshort₂, hverify₂⟩
    have hcommit₁ : commit R A s₁ = c :=
      (verify_eq_true_iff R A s₁ c opening₁).1 hverify₁
    have hcommit₂ : commit R A s₂ = c :=
      (verify_eq_true_iff R A s₂ c opening₂).1 hverify₂
    have hmat : A *ᵥ s₁ = A *ᵥ s₂ := by
      simpa [commit] using hcommit₁.trans hcommit₂.symm
    have hnonzero : s₁ - s₂ ≠ 0 := by
      intro hzero
      apply hne
      apply Vector.ext
      intro i hi
      have hget := congrArg (fun v : Message R cols => v[i]) hzero
      have hcoordVec : s₁[i] - s₂[i] = (0 : Message R cols)[i] := by
        simpa [Vector.getElem_sub] using hget
      have hzeroGet : (0 : Message R cols)[i] = 0 := by
        rw [show (0 : Message R cols) =
          Vector.ofFn (fun _ : Fin cols => (0 : (R).Poly)) by rfl]
        simp
      have hcoord : s₁[i] - s₂[i] = 0 :=
        hcoordVec.trans hzeroGet
      exact sub_eq_zero.mp hcoord
    have hker : A *ᵥ (s₁ - s₂) = 0 := by
      rw [LatticeCrypto.matVecMul_sub A s₁ s₂, hmat]
      apply Vector.ext
      intro i hi
      rw [show (0 : PolyVec (R).Poly rows) =
        Vector.ofFn (fun _ : Fin rows => (0 : (R).Poly)) by rfl]
      simp [Vector.getElem_sub]
    have hshort : ‖s₁ - s₂‖⟪normOps⟫₂² ≤ subL2NormSqBound boundSq :=
      sub_l2NormSq_le s₁ s₂ hshort₁ hshort₂
    simp [hne, hshort₁, hshort₂, hcommit₁, hcommit₂, hnonzero, hker, hshort]
  · have hleftFalse :
        ¬((s₁ ≠ s₂ ∧ ‖s₁‖⟪normOps⟫₂² ≤ boundSq ∧ commit R A s₁ = c) ∧
            ‖s₂‖⟪normOps⟫₂² ≤ boundSq ∧ commit R A s₂ = c) := by
      rintro ⟨⟨hne, hs₁, hc₁⟩, hs₂, hc₂⟩
      apply hwin
      simp [hne, hs₁, hs₂, hc₁, hc₂, verify]
    simp [hleftFalse]

end Canonical

end Simple
end Ajtai
end LatticeCrypto
