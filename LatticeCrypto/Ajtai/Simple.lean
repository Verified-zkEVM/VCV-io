/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Gadget
import LatticeCrypto.HardnessAssumptions.ModuleShortIntegerSolution
import VCVio.CryptoFoundations.CommitmentScheme

/-!
# Simple Ajtai Commitment

The simple Ajtai commitment over a bundled negacyclic ring.  Public parameters
are a uniformly sampled matrix `A`; committing to a vector `s` returns `A * s`
and uses the trivial opening. Non-hiding, but binding under Module-SIS.
-/

open OracleComp
open CommitmentScheme

universe u

namespace LatticeCrypto
namespace Ajtai
namespace Simple

variable {Coeff : Type u} [CommRing Coeff]

/-- Public parameters for the simple Ajtai commitment. -/
abbrev PublicParams (ring : NegacyclicRing Coeff) (rows cols : Nat) :=
  PolyMatrix ring.Poly rows cols

/-- Messages for the simple Ajtai commitment. -/
abbrev Message (ring : NegacyclicRing Coeff) (cols : Nat) :=
  PolyVec ring.Poly cols

/-- Commitments for the simple Ajtai commitment. -/
abbrev Commitment (ring : NegacyclicRing Coeff) (rows : Nat) :=
  PolyVec ring.Poly rows

/-- Deterministically commit by multiplying the public matrix by the message vector. -/
def commit (ring : NegacyclicRing Coeff) {rows cols : Nat}
    (A : PublicParams ring rows cols) (s : Message ring cols) : Commitment ring rows :=
  ring.matVecMul A s

/-- The simple Ajtai commitment has no auxiliary opening data. -/
abbrev Opening := Unit

/-- Verify a simple Ajtai opening by checking the matrix product. -/
def verify (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [DecidableEq (Commitment ring rows)]
    (A : PublicParams ring rows cols) (s : Message ring cols)
    (c : Commitment ring rows) (_opening : Opening) : Bool :=
  commit ring A s == c

@[simp] theorem verify_commit (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [DecidableEq (Commitment ring rows)]
    (A : PublicParams ring rows cols) (s : Message ring cols) :
    verify ring A s (commit ring A s) () = true := by
  simp [verify]

@[simp] theorem verify_eq_true_iff (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [DecidableEq (Commitment ring rows)]
    (A : PublicParams ring rows cols) (s : Message ring cols)
    (c : Commitment ring rows) (opening : Opening) :
    verify ring A s c opening = true ↔ commit ring A s = c := by
  simp [verify]

/-- The simple Ajtai commitment instantiated as `CommitmentScheme`. -/
def commitmentScheme (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PublicParams ring rows cols)]
    [DecidableEq (Commitment ring rows)] :
    CommitmentScheme
      (PublicParams ring rows cols)
      (Message ring cols)
      (Commitment ring rows)
      Opening where
  setup := $ᵗ PublicParams ring rows cols
  commit A s := pure (commit ring A s, ())
  verify A s c opening := verify ring A s c opening

/-- Simple Ajtai commitments are perfectly correct by construction. -/
theorem perfectlyCorrect (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PublicParams ring rows cols)]
    [DecidableEq (Commitment ring rows)] :
    (commitmentScheme ring rows cols).PerfectlyCorrect := by
  intro A _ s cd hmem
  simp only [commitmentScheme, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl
  change verify ring A s (commit ring A s) () = true
  simp

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
    pure { left := s₁, right := s₂ }

/-- Binding of the simple Ajtai commitment reduces to collision-form Module-SIS. -/
theorem bindingAdvantage_le_moduleSIS (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PublicParams ring rows cols)]
    [DecidableEq (Message ring cols)]
    [DecidableEq (Commitment ring rows)]
    (adv : BindingAdv
      (PublicParams ring rows cols)
      (Message ring cols)
      (Commitment ring rows)
      Opening) :
    bindingAdvantage (commitmentScheme ring rows cols) adv ≤
      ModuleSIS.advantage ring rows cols (fun _ => true)
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
    simp [hne, hcommit₁, hcommit₂, hmat]
  · have hleftFalse :
        ¬((s₁ ≠ s₂ ∧ commit ring A s₁ = c) ∧ commit ring A s₂ = c) := by
      intro hleft
      apply hwin
      simpa [verify] using hleft
    simp [hleftFalse]

end Simple
end Ajtai
end LatticeCrypto
