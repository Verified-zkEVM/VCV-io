/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SecExp

/-!
# Asymmetric Encryption Schemes

Core definitions for asymmetric encryption schemes and correctness.
-/

open OracleSpec OracleComp ENNReal

universe u v w

/-- An `AsymmEncAlg` with message space `M`, key spaces `PK` and `SK`, and ciphertexts in `C`.
`m` is the monad used to execute key generation, encryption, and decryption.
It extends `ExecutionMethod m`, typically `ExecutionMethod.default`. -/
structure AsymmEncAlg (m : Type → Type u) (M PK SK C : Type)
    extends ExecutionMethod m where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) →  m C
  decrypt : (sk : SK) → (c : C) →  m (Option M)

alias PKE_Alg := AsymmEncAlg

namespace AsymmEncAlg

variable {m : Type → Type v} {M PK SK C : Type}
  (encAlg : AsymmEncAlg m M PK SK C)

section Correct

variable [DecidableEq M] [Monad m]

/-- Correctness experiment: returns `true` iff decrypting the ciphertext recovers the message.

The game returns a `Bool` directly rather than using `guard`, so it does not require
`AlternativeMonad`. -/
def CorrectExp (msg : M) : m Bool := do
  let (pk, sk) ← encAlg.keygen
  let c ← encAlg.encrypt pk msg
  let msg' ← encAlg.decrypt sk c
  return decide (msg' = some msg)

/-- An asymmetric encryption scheme is perfectly correct when decrypting a fresh encryption of any
message succeeds with probability `1`. -/
def PerfectlyCorrect [HasEvalSPMF m] : Prop :=
  ∀ (msg : M), Pr[= true | encAlg.exec (encAlg.CorrectExp msg)] = 1

end Correct

end AsymmEncAlg
