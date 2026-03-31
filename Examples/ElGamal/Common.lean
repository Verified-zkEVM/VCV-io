/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Shared ElGamal-family helpers

Small distribution lemmas shared by the plain and hashed ElGamal examples.
-/


open OracleComp OracleSpec ENNReal

namespace ElGamalExamples

variable {A M : Type}
variable [AddGroup M] [SampleableType M]

/-- A fixed header plus a uniform additive mask hides which payload was chosen, even after an
arbitrary continuation from ciphertexts. -/
lemma uniformMaskedCipher_bind_dist_indep {β : Type}
    (head : A) (m₁ m₂ : M) (cont : A × M → ProbComp β) :
    evalDist (do
      let y ← ($ᵗ M : ProbComp M)
      cont (head, m₁ + y)) =
    evalDist (do
      let y ← ($ᵗ M : ProbComp M)
      cont (head, m₂ + y)) := by
  have hmask :
      evalDist (((fun y : M => (head, m₁ + y)) <$> ($ᵗ M : ProbComp M))) =
        evalDist (((fun y : M => (head, m₂ + y)) <$> ($ᵗ M : ProbComp M))) := by
    simpa using
      evalDist_map_eq_of_evalDist_eq
        (h := evalDist_add_left_uniform_eq (α := M) m₁ m₂)
        (f := fun z : M => (head, z))
  simpa [map_eq_bind_pure_comp, Function.comp, evalDist_bind, bind_assoc] using
    congrArg (fun p => p >>= fun c => evalDist (cont c)) hmask

end ElGamalExamples
