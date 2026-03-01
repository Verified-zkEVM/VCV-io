/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.HardnessAssumptions.HardHomogeneousSpace

/-!
# Diffie-Hellman Assumptions

This file defines DLog/CDH/DDH *via* the `HardHomogeneousSpace` experiments:
- DLog = vectorization
- CDH = parallelization
- DDH = parallel testing

This enforces the intended modeling choice directly at the definition level.

For cyclic-group instantiations, we also define an explicit
`NondegenerateGenerator` condition to rule out degenerate choices of base element.
-/

open OracleComp OracleSpec ENNReal

namespace DiffieHellman

section HardHomogeneousModel

variable {V P : Type} [AddCommGroup V] [AddTorsor V P]
  [SampleableType V] [SampleableType P]

/-- DLog adversary, modeled as vectorization on a hard homogeneous space. -/
abbrev DLogAdversary (V P : Type) := vectorizationAdversary V P

/-- DLog experiment, defined as `HardHomogeneousSpace.vectorizationExp`. -/
abbrev dlogExp [DecidableEq V] (adversary : DLogAdversary V P) : ProbComp Bool :=
  vectorizationExp (G := V) (P := P) adversary

/-- CDH adversary, modeled as parallelization on a hard homogeneous space. -/
abbrev CDHAdversary (V P : Type) := parallelizationAdversary V P

/-- CDH experiment, defined as `HardHomogeneousSpace.parallelizationExp`. -/
abbrev cdhExp [DecidableEq P] (adversary : CDHAdversary V P) : ProbComp Bool :=
  parallelizationExp (G := V) (P := P) adversary

/-- DDH adversary, modeled as parallel testing on a hard homogeneous space. -/
abbrev DDHAdversary (V P : Type) := parallelTestingAdversary V P

/-- DDH experiment, defined as `HardHomogeneousSpace.parallelTesting_experiment`. -/
abbrev ddhExp [DecidableEq V] (adversary : DDHAdversary V P) : ProbComp Bool :=
  parallelTesting_experiment (G := V) (P := P) adversary

/-- DDH advantage from the hard-homogeneous-space parallel-testing experiment. -/
noncomputable abbrev ddhAdvantage [DecidableEq V]
    (adversary : DDHAdversary V P) : ℝ≥0∞ :=
  parallelTestingAdvantage (G := V) (P := P) adversary

end HardHomogeneousModel

section NondegenerateBase

variable {V P : Type} [AddCommGroup V] [AddTorsor V P]

/-- A base point is nondegenerate when translating vectors from it is bijective. -/
def NondegenerateBase (base : P) : Prop :=
  Function.Bijective fun v : V => v +ᵥ base

/-- In any additive torsor, every base point is nondegenerate. -/
lemma nondegenerateBase (base : P) : NondegenerateBase (V := V) base := by
  constructor
  · intro v₁ v₂ h
    simpa using congrArg (fun p => p -ᵥ base) h
  · intro p
    refine ⟨p -ᵥ base, ?_⟩
    simp

end NondegenerateBase

section CyclicInstantiation

variable {G : Type} [CommGroup G] [Fintype G]

/-- In a cyclic-group style instantiation, this rules out degenerate base choices. -/
def NondegenerateGenerator (g : G) : Prop :=
  Function.Surjective fun a : Fin (Fintype.card G) => g ^ a.1

lemma NondegenerateGenerator.ne_one [Nontrivial G] {g : G}
    (hg : NondegenerateGenerator (G := G) g) : g ≠ 1 := by
  intro hg1
  rcases exists_ne (1 : G) with ⟨x, hx⟩
  rcases hg x with ⟨a, ha⟩
  have h1x : (1 : G) = x := by simpa [hg1] using ha
  exact hx h1x.symm

end CyclicInstantiation

end DiffieHellman
