/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbCompLift
import ToMathlib.Control.Monad.Hom

/-!
# Asymmetric Encryption Schemes

Core definitions for asymmetric encryption schemes and correctness.
-/

open OracleSpec OracleComp ENNReal

universe u v w

/-- An `AsymmEncAlg` with message space `M`, key spaces `PK` and `SK`, and ciphertexts in `C`.
`m` is the monad used to execute key generation, encryption, and decryption. The scheme data stays
purely algorithmic; probabilistic semantics and public-randomness injection are supplied
separately when defining security experiments. -/
structure AsymmEncAlg (m : Type → Type u) [Monad m] (M PK SK C : Type) where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) →  m C
  decrypt : (sk : SK) → (c : C) →  m (Option M)

/-- An explicit-coins asymmetric encryption scheme in the monad `m`.

Key generation runs in `m`, while encryption and decryption become pure once the randomness type
`R` is supplied explicitly. This is the natural refinement used by FO-style transforms, where the
coins are sampled externally or derived from an oracle. -/
structure AsymmEncAlg.ExplicitCoins (m : Type → Type u) [Monad m] (M PK SK R C : Type) where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) → (coins : R) → C
  decrypt : (sk : SK) → (c : C) → Option M

abbrev PKE_Alg := AsymmEncAlg

namespace AsymmEncAlg
variable {m : Type → Type v} [Monad m] {M PK SK C : Type}
  (encAlg : AsymmEncAlg m M PK SK C)

section map

variable {n : Type → Type w} [Monad n]

/-- Transport an asymmetric encryption scheme across a monad morphism by mapping each algorithmic
component. -/
def map (F : m →ᵐ n) : AsymmEncAlg n M PK SK C where
  keygen := F encAlg.keygen
  encrypt pk msg := F (encAlg.encrypt pk msg)
  decrypt sk c := F (encAlg.decrypt sk c)

@[simp]
lemma map_keygen (F : m →ᵐ n) :
    (encAlg.map F).keygen = F encAlg.keygen := rfl

@[simp]
lemma map_encrypt (F : m →ᵐ n) (pk : PK) (msg : M) :
    (encAlg.map F).encrypt pk msg = F (encAlg.encrypt pk msg) := rfl

@[simp]
lemma map_decrypt (F : m →ᵐ n) (sk : SK) (c : C) :
    (encAlg.map F).decrypt sk c = F (encAlg.decrypt sk c) := rfl

end map

section ext

/-- Two asymmetric encryption schemes are equal when their algorithmic components agree. -/
@[ext]
theorem ext {encAlg' : AsymmEncAlg m M PK SK C}
    (hKeygen : encAlg.keygen = encAlg'.keygen)
    (hEncrypt : encAlg.encrypt = encAlg'.encrypt)
    (hDecrypt : encAlg.decrypt = encAlg'.decrypt) :
    encAlg = encAlg' := by
  cases encAlg
  cases encAlg'
  cases hKeygen
  cases hEncrypt
  cases hDecrypt
  rfl

end ext

section Correct

variable [DecidableEq M]

/-- Correctness experiment: returns `true` iff decrypting the ciphertext recovers the message.

The game returns a `Bool` directly rather than using `guard`, so it does not require
`AlternativeMonad`. -/
def CorrectExp (msg : M) : m Bool :=
  do
    let (pk, sk) ← encAlg.keygen
    let c ← encAlg.encrypt pk msg
    let msg' ← encAlg.decrypt sk c
    return decide (msg' = some msg)

/-- An asymmetric encryption scheme is perfectly correct under the given runtime when decrypting a
fresh encryption of any message succeeds with probability `1`. -/
def PerfectlyCorrect (runtime : ProbCompRuntime m) : Prop :=
  ∀ (msg : M), Pr[= true | runtime.evalDist (encAlg.CorrectExp msg)] = 1

end Correct

namespace ExplicitCoins
variable {m : Type → Type v} [Monad m] {M PK SK R C : Type}
  (encAlg : AsymmEncAlg.ExplicitCoins m M PK SK R C)

/-- Forget the explicit-coins presentation by sampling the coins through the ambient runtime's
public-randomness capability. -/
def toAsymmEncAlg [SampleableType R] (runtime : ProbCompRuntime m) : AsymmEncAlg m M PK SK C :=
  { keygen := encAlg.keygen
    encrypt := fun pk msg => do
      let r ← runtime.liftProbComp ($ᵗ R)
      return encAlg.encrypt pk msg r
    decrypt := fun sk c => return (encAlg.decrypt sk c) }

end ExplicitCoins

end AsymmEncAlg
