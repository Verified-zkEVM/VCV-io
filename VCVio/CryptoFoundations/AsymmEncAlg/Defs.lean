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

/-- An explicit-coins asymmetric encryption scheme in the monad `m`.

Key generation runs in `m`, while encryption and decryption become pure once the randomness type
`R` is supplied explicitly. This is the natural refinement used by FO-style transforms, where the
coins are sampled externally or derived from an oracle. -/
structure AsymmEncAlg.ExplicitCoins (m : Type → Type u) (M PK SK R C : Type)
    extends ExecutionMethod m where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) → (coins : R) → C
  decrypt : (sk : SK) → (c : C) → Option M

abbrev PKE_Alg := AsymmEncAlg

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
def PerfectlyCorrect : Prop :=
  ∀ (msg : M), Pr[= true | encAlg.exec (encAlg.CorrectExp msg)] = 1

end Correct

namespace ExplicitCoins

variable {m : Type → Type v} {M PK SK R C : Type}
  (encAlg : AsymmEncAlg.ExplicitCoins m M PK SK R C)

/-- Forget the explicit-coins presentation by sampling the coins through the ambient execution
method. -/
def toAsymmEncAlg [Monad m] [SampleableType R] : AsymmEncAlg m M PK SK C where
  keygen := encAlg.keygen
  encrypt := fun pk msg => do
    let r ← encAlg.lift_probComp ($ᵗ R)
    return encAlg.encrypt pk msg r
  decrypt := fun sk c => return (encAlg.decrypt sk c)
  __ := encAlg.toExecutionMethod

end ExplicitCoins

end AsymmEncAlg
