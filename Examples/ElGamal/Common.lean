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

namespace ElGamalExamples

variable {A M : Type}
variable [AddCommGroup M] [SampleableType M]

/-- Uniform additive masking via a bijective pushforward: if `f : α → M` is a bijection out of
a finite uniformly sampleable type `α`, then `f x + m` with `x ← $ᵗ α` has the same distribution
for any two offsets `m`. Generalizes `uniformMaskedCipher_bind_dist_indep` to the case where the
mask is sampled in a different space and transported to `M` by a bijection (as in ElGamal, where
randomness lives in the scalar field and the ciphertext lives in the module). -/
lemma evalDist_bind_bijectiveSmul_add_eq {α β : Type}
    [Finite α] [SampleableType α]
    (f : α → M) (hf : Function.Bijective f)
    (m₁ m₂ : M) (cont : M → ProbComp β) :
    evalDist (do
      let x ← ($ᵗ α : ProbComp α)
      cont (f x + m₁)) =
    evalDist (do
      let x ← ($ᵗ α : ProbComp α)
      cont (f x + m₂)) := by
  have bridge : ∀ m : M,
      evalDist (do let x ← ($ᵗ α : ProbComp α); cont (f x + m)) =
        evalDist (do let z ← ($ᵗ M : ProbComp M); cont z) := by
    intro m
    have hbind :
        (do let x ← ($ᵗ α : ProbComp α); cont (f x + m)) =
          (f <$> ($ᵗ α : ProbComp α)) >>= fun y => cont (y + m) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    rw [hbind, evalDist_bind,
      evalDist_map_bijective_uniform_cross (α := α) (β := M) f hf, ← evalDist_bind]
    have hshift :
        (do let z ← ($ᵗ M : ProbComp M); cont (z + m)) =
          (((fun z : M => m + z) <$> ($ᵗ M : ProbComp M)) >>= cont) := by
      simp [map_eq_bind_pure_comp, bind_assoc, add_comm]
    rw [hshift, evalDist_bind, evalDist_add_left_uniform (α := M) m, ← evalDist_bind]
  rw [bridge m₁, bridge m₂]

end ElGamalExamples
