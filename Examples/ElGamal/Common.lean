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

variable {A M : Type} [AddGroup M] [SampleableType M]

/-- A fixed header plus a uniform additive mask hides which payload was chosen, even after an
arbitrary continuation from ciphertexts. -/
lemma uniformMaskedCipher_bind_dist_indep {β : Type}
    (head : A) (m₁ m₂ : M) (cont : A × M → ProbComp β) :
    𝒟[do
      let y ← ($ᵗ M)
      cont (head, m₁ + y)] =
    𝒟[do
      let y ← ($ᵗ M)
      cont (head, m₂ + y)] := by
  have hmask :
      𝒟[((fun y : M => (head, m₁ + y)) <$> ($ᵗ M))] =
        𝒟[((fun y : M => (head, m₂ + y)) <$> ($ᵗ M))] := by
    simpa using
      evalDist_map_eq_of_evalDist_eq
        (h := evalDist_add_left_uniform_eq (α := M) m₁ m₂)
        (f := fun z : M => (head, z))
  simpa [monad_norm, Function.comp, evalDist_bind] using
    congrArg (fun p => p >>= fun c => 𝒟[cont c]) hmask

end ElGamalExamples
