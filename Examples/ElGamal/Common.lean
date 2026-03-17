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

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace ElGamalExamples

variable {A M : Type}
variable [AddGroup M] [SampleableType M]

/-- Uniform additive masking hides the underlying message. -/
lemma uniformMaskedPayload_dist_indep (m₁ m₂ : M) :
    evalDist ((fun y : M => m₁ + y) <$> ($ᵗ M : ProbComp M)) =
      evalDist ((fun y : M => m₂ + y) <$> ($ᵗ M : ProbComp M)) := by
  exact evalDist_add_left_uniform_eq (α := M) m₁ m₂

/-- Pairing a fixed header with a uniformly masked payload preserves message-independence. -/
lemma uniformMaskedCipher_dist_indep (head : A) (m₁ m₂ : M) :
    evalDist ((fun y : M => (head, m₁ + y)) <$> ($ᵗ M : ProbComp M)) =
      evalDist ((fun y : M => (head, m₂ + y)) <$> ($ᵗ M : ProbComp M)) := by
  simpa [Function.comp] using
    evalDist_map_eq_of_evalDist_eq
      (h := uniformMaskedPayload_dist_indep (m₁ := m₁) (m₂ := m₂))
      (f := fun z : M => (head, z))

end ElGamalExamples
