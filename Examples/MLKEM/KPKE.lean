/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.MLKEM.Encoding
import Examples.MLKEM.Primitives
import VCVio.CryptoFoundations.AsymmEncAlg.Defs

/-!
# ML-KEM K-PKE

This file gives a spec-level implementation of the `K-PKE` component used by ML-KEM. The
arithmetic, encoding, and primitive operations are supplied abstractly, but the algorithm structure
follows FIPS 203 Section 5 closely.
-/

set_option autoImplicit false

namespace MLKEM
namespace KPKE

/-- The semantic public key for K-PKE. -/
structure PublicKey (params : Params) (encoding : Encoding params) where
  tHatEncoded : encoding.EncodedTHat
  rho : Seed32

/-- The semantic secret key for K-PKE. -/
structure SecretKey (params : Params) (encoding : Encoding params) where
  sHatEncoded : encoding.EncodedTHat

/-- The semantic ciphertext for K-PKE. -/
structure Ciphertext (params : Params) (encoding : Encoding params) where
  uEncoded : encoding.EncodedU
  vEncoded : encoding.EncodedV

variable {params : Params}
variable {encoding : Encoding params}

instance [DecidableEq encoding.EncodedTHat] : DecidableEq (PublicKey params encoding) := by
  intro x y
  cases x
  cases y
  simp
  infer_instance

instance [DecidableEq encoding.EncodedTHat] : DecidableEq (SecretKey params encoding) := by
  intro x y
  cases x
  cases y
  simp
  infer_instance

instance [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV] :
    DecidableEq (Ciphertext params encoding) := by
  intro x y
  cases x
  cases y
  simp
  infer_instance

/-- K-PKE key generation from an explicit 32-byte seed.

This expands the input seed into the public matrix seed `rho` and sampling seed `sigma`,
samples the secret and error vectors, moves them into the NTT domain, and forms the public
key relation `tHat = Ahat * sHat + eHat` before serializing the public and secret outputs. -/
def keygenFromSeed (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (d : Seed32) :
    PublicKey params encoding × SecretKey params encoding :=
  let (rho, sigma) := prims.gKeygen params d
  let aHat := prims.publicMatrix rho
  let s := prims.sampleVecEta1 sigma 0
  let e := prims.sampleVecEta1 sigma params.k
  let sHat := ring.nttVec s
  let eHat := ring.nttVec e
  let tHat := ring.matVecMul aHat sHat + eHat
  ({ tHatEncoded := encoding.byteEncode12Vec tHat, rho := rho },
    { sHatEncoded := encoding.byteEncode12Vec sHat })

/-- K-PKE encryption with explicit coins.

This decodes the public key, deterministically derives the ephemeral secret and noise terms from
`coins`, computes the ML-KEM ciphertext components `(u, v)`, and then compresses and serializes
them into the abstract ciphertext representation. -/
def encrypt (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (ek : PublicKey params encoding) (msg : Message)
    (coins : Coins) : Ciphertext params encoding :=
  let tHat := encoding.byteDecode12Vec ek.tHatEncoded
  let aHat := prims.publicMatrix ek.rho
  let y := prims.sampleVecEta1 coins 0
  let e1 := prims.sampleVecEta2 coins params.k
  let e2 := prims.prfEta2 coins (2 * params.k)
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  let mu := encoding.decompress1 (encoding.byteDecode1 msg)
  let v := ring.invNTT (ring.dot tHat yHat) + e2 + mu
  { uEncoded := encoding.byteEncodeDUVec (encoding.compressDU u)
    vEncoded := encoding.byteEncodeDV (encoding.compressDV v) }

/-- K-PKE decryption.

This decodes the ciphertext into its semantic `(u, v)` components, subtracts the secret-key
contribution from `v`, and re-encodes the resulting message representative as the recovered
32-byte plaintext. -/
def decrypt (ring : NTTRingOps) (encoding : Encoding params)
    (_prims : Primitives params encoding) (dk : SecretKey params encoding)
    (c : Ciphertext params encoding) : Message :=
  let (u', v') := encoding.decodeCiphertext c.uEncoded c.vEncoded
  let sHat := encoding.byteDecode12Vec dk.sHatEncoded
  let w := v' - ring.invNTT (ring.dot sHat (ring.nttVec u'))
  encoding.byteEncode1 (encoding.compress1 w)

/-- Package the spec-level K-PKE as an explicit-coins public-key encryption scheme. -/
def asExplicitCoins (params : Params) (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) :
    AsymmEncAlg.ExplicitCoins ProbComp Message (PublicKey params encoding)
      (SecretKey params encoding) Coins (Ciphertext params encoding) where
  keygen := do
    let d ← $ᵗ Seed32
    return keygenFromSeed ring encoding prims d
  encrypt := encrypt ring encoding prims
  decrypt := fun sk c => some (decrypt ring encoding prims sk c)
  __ := ExecutionMethod.default

end KPKE
end MLKEM
