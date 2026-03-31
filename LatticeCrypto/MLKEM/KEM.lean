/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLKEM.Internal
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# ML-KEM Top-Level KEM

This file packages the probabilistic top-level algorithms from FIPS 203 Section 7 on top of the
deterministic internal algorithms from `Examples.MLKEM.Internal`.
-/


namespace MLKEM

variable {params : Params}

/-- Check the semantic public-key component against the abstract byte-level canonicality test. -/
def encapsulationKeyCheck (encoding : Encoding params) [DecidableEq encoding.EncodedTHat]
    (ek : EncapsulationKey params encoding) : Bool :=
  encoding.publicKeyCanonical ek.tHatEncoded

@[simp] theorem encapsulationKeyCheck_keygenFromSeed_eq_true (ring : NTTRingOps)
    (encoding : Encoding params) [DecidableEq encoding.EncodedTHat]
    (prims : Primitives params encoding) (d : Seed32) :
    encapsulationKeyCheck encoding (KPKE.keygenFromSeed ring encoding prims d).1 = true := by
  unfold encapsulationKeyCheck KPKE.keygenFromSeed
  simp

@[simp] theorem encapsulationKeyCheck_keygenInternal_eq_true (ring : NTTRingOps)
    (encoding : Encoding params) [DecidableEq encoding.EncodedTHat]
    (prims : Primitives params encoding) (d z : Seed32) :
    encapsulationKeyCheck encoding (keygenInternal ring encoding prims d z).1 = true := by
  simp [keygenInternal]

/-- Check the semantic decapsulation key against the stored encapsulation-key hash. -/
def decapsulationKeyCheck (encoding : Encoding params) (prims : Primitives params encoding)
    (dk : DecapsulationKey params encoding) : Bool :=
  encapsulationKeyHash encoding prims dk.ekPKE == dk.ekHash

/-- In the semantic model, ciphertexts are already well-typed, so the top-level runtime check is
reduced to `true`. A later byte-level refinement can strengthen this predicate. -/
def ciphertextCheck (encoding : Encoding params)
    (_c : Ciphertext params encoding) : Bool := true

/-- Combined decapsulation input check. -/
def decapsulationInputCheck (encoding : Encoding params) (prims : Primitives params encoding)
    (dk : DecapsulationKey params encoding) (c : Ciphertext params encoding) : Bool :=
  decapsulationKeyCheck encoding prims dk && ciphertextCheck encoding c

/-- `ML-KEM.KeyGen`. This spec-level version assumes randomness generation succeeds and, by the
encoding canonicality law, always outputs an encapsulation key accepted by `encaps`. -/
def keygen (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) :
    ProbComp (EncapsulationKey params encoding × DecapsulationKey params encoding) := do
  let d ← $ᵗ Seed32
  let z ← $ᵗ Seed32
  return keygenInternal ring encoding prims d z

/-- `ML-KEM.Encaps` with its input check made explicit. -/
def encaps (ring : NTTRingOps) (encoding : Encoding params)
    [DecidableEq encoding.EncodedTHat]
    (prims : Primitives params encoding) (ek : EncapsulationKey params encoding) :
    OptionT ProbComp (SharedSecret × Ciphertext params encoding) := do
  if encapsulationKeyCheck encoding ek then
    let m ← OptionT.lift (m := ProbComp) ($ᵗ Message)
    return encapsInternal ring encoding prims ek m
  else
    OptionT.mk (pure none)

/-- `ML-KEM.Decaps` with its input checks made explicit. -/
def decaps (ring : NTTRingOps) (encoding : Encoding params)
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV]
    (prims : Primitives params encoding) (dk : DecapsulationKey params encoding)
    (c : Ciphertext params encoding) : Option SharedSecret :=
  if decapsulationInputCheck encoding prims dk c then
    some (decapsInternal ring encoding prims dk c)
  else
    none

/-- Package the internal checked-interface semantics as a `KEMScheme`.

This wrapper is intended for reuse inside the repo's generic KEM interfaces; it assumes callers
only supply inputs that have already passed the public `encaps` / `decaps` checks above. -/
def asKEMScheme (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) [DecidableEq encoding.EncodedTHat]
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV] :
    KEMScheme ProbComp SharedSecret (EncapsulationKey params encoding)
      (DecapsulationKey params encoding) (Ciphertext params encoding) where
  keygen := keygen ring encoding prims
  encaps := fun ek => do
    let m ← $ᵗ Message
    let (k, c) := encapsInternal ring encoding prims ek m
    return (c, k)
  decaps := fun dk c => return some (decapsInternal ring encoding prims dk c)
  __ := ExecutionMethod.default

end MLKEM
