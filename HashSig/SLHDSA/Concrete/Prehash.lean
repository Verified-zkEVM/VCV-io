/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.External
public import HashSig.SLHDSA.Concrete.Sha2
public import HashSig.SLHDSA.Concrete.Keccak
public import HashSig.SLHDSA.Concrete.FIPS

/-!
# Checked FIPS 205 pre-hash adapter

This module closes the descriptor-parametric external semantics over the twelve hash algorithms
named by ACVP. An `Algorithm` determines the digest implementation, exact output width, and DER
OID together. The public signing and verification entry points also enforce FIPS 205 §10.2's
`2n`-byte collision-strength boundary.

It also hosts the FIPS-pinned deterministic entry points (`signDeterministicApproved` and
`signPureDeterministicApproved`), which bind the deterministic variants' `opt_rand` input to
`PK.seed` via `SLHDSA.Concrete.approvedRandomizerOfPkSeed` as FIPS 205 Algorithm 19 line 2
requires, together with sign→verify completeness theorems for the checked boundary.
-/

@[expose] public section

namespace SLHDSA.Concrete.Prehash

open OracleComp
open SLHDSA.External

/-- The complete pre-hash algorithm menu named by the FIPS 205 ACVP external interface. -/
inductive Algorithm where
  | sha2_224
  | sha2_256
  | sha2_384
  | sha2_512
  | sha2_512_224
  | sha2_512_256
  | sha3_224
  | sha3_256
  | sha3_384
  | sha3_512
  | shake128
  | shake256
deriving Repr, DecidableEq, BEq

/-- Every ACVP pre-hash algorithm, in registration order. -/
def all : List Algorithm :=
  [.sha2_224, .sha2_256, .sha2_384, .sha2_512, .sha2_512_224, .sha2_512_256,
    .sha3_224, .sha3_256, .sha3_384, .sha3_512, .shake128, .shake256]

/-- Exact ACVP spelling. -/
def Algorithm.name : Algorithm → String
  | .sha2_224 => "SHA2-224"
  | .sha2_256 => "SHA2-256"
  | .sha2_384 => "SHA2-384"
  | .sha2_512 => "SHA2-512"
  | .sha2_512_224 => "SHA2-512/224"
  | .sha2_512_256 => "SHA2-512/256"
  | .sha3_224 => "SHA3-224"
  | .sha3_256 => "SHA3-256"
  | .sha3_384 => "SHA3-384"
  | .sha3_512 => "SHA3-512"
  | .shake128 => "SHAKE-128"
  | .shake256 => "SHAKE-256"

/-- Parse an exact ACVP algorithm name. -/
def Algorithm.ofName? : String → Option Algorithm
  | "SHA2-224" => some .sha2_224
  | "SHA2-256" => some .sha2_256
  | "SHA2-384" => some .sha2_384
  | "SHA2-512" => some .sha2_512
  | "SHA2-512/224" => some .sha2_512_224
  | "SHA2-512/256" => some .sha2_512_256
  | "SHA3-224" => some .sha3_224
  | "SHA3-256" => some .sha3_256
  | "SHA3-384" => some .sha3_384
  | "SHA3-512" => some .sha3_512
  | "SHAKE-128" => some .shake128
  | "SHAKE-256" => some .shake256
  | _ => none

@[simp] theorem Algorithm.ofName?_name (algorithm : Algorithm) :
    Algorithm.ofName? algorithm.name = some algorithm := by
  cases algorithm <;> rfl

/-- Digest width, including FIPS 205's fixed 32/64-byte SHAKE outputs. -/
def Algorithm.outputLength : Algorithm → ℕ
  | .sha2_224 | .sha2_512_224 | .sha3_224 => 28
  | .sha2_256 | .sha2_512_256 | .sha3_256 | .shake128 => 32
  | .sha2_384 | .sha3_384 => 48
  | .sha2_512 | .sha3_512 | .shake256 => 64

/-- FIPS 205 §10.2 compatibility: collision strength requires at least `2n` digest bytes. -/
def Algorithm.validFor (algorithm : Algorithm) (p : Params) : Bool :=
  2 * p.n ≤ algorithm.outputLength

/-- Proposition-level strength requirement. -/
def Algorithm.ValidFor (algorithm : Algorithm) (p : Params) : Prop :=
  2 * p.n ≤ algorithm.outputLength

theorem Algorithm.validFor_iff (algorithm : Algorithm) (p : Params) :
    algorithm.validFor p = true ↔ algorithm.ValidFor p := by
  simp [Algorithm.validFor, Algorithm.ValidFor]

/-- Complete DER encoding of the NIST hash-algorithm OID (`hashAlgs` arcs 1–12). -/
def Algorithm.oidDer : Algorithm → List Byte
  | .sha2_256 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01]
  | .sha2_384 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02]
  | .sha2_512 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03]
  | .sha2_224 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x04]
  | .sha2_512_224 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x05]
  | .sha2_512_256 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x06]
  | .sha3_224 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x07]
  | .sha3_256 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x08]
  | .sha3_384 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x09]
  | .sha3_512 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0a]
  | .shake128 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0b]
  | .shake256 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0c]

/-- Concrete FFI-free digest bytes. -/
def Algorithm.digestRaw (algorithm : Algorithm) (message : List Byte) : ByteArray :=
  let input := ByteArray.mk message.toArray
  match algorithm with
  | .sha2_224 => Sha2.sha224 input
  | .sha2_256 => Sha2.sha256 input
  | .sha2_384 => Sha2.sha384 input
  | .sha2_512 => Sha2.sha512 input
  | .sha2_512_224 => Sha2.sha512_224 input
  | .sha2_512_256 => Sha2.sha512_256 input
  | .sha3_224 => Keccak.sha3_224 input
  | .sha3_256 => Keccak.sha3_256 input
  | .sha3_384 => Keccak.sha3_384 input
  | .sha3_512 => Keccak.sha3_512 input
  | .shake128 => Keccak.squeeze (Keccak.absorb input 168 0x1f) 32
  | .shake256 => Keccak.squeeze (Keccak.absorb input 136 0x1f) 64

@[simp] theorem Algorithm.digestRaw_size (algorithm : Algorithm) (message : List Byte) :
    (algorithm.digestRaw message).size = algorithm.outputLength := by
  cases algorithm <;> simp [Algorithm.digestRaw, Algorithm.outputLength]

/-- Fail-closed exact-width projection; there is no padding or truncation path. -/
def digestBytesExact (n : ℕ) (digest : ByteArray) : Except Error (Bytes n) :=
  if h : digest.size = n then
    .ok (Vector.ofFn fun i : Fin n => digest[i.val]'(by omega))
  else
    .error (.digestLengthMismatch n digest.size)

/-- Exact-width digest checked against the engine's advertised width through the fail-closed
projection; `Algorithm.digest_eq_ok` shows the error branch is unreachable for the registry
engines. -/
def Algorithm.digest (algorithm : Algorithm) (message : List Byte) :
    Except Error (Bytes algorithm.outputLength) :=
  digestBytesExact algorithm.outputLength (algorithm.digestRaw message)

/-- Every registry digest engine meets its advertised exact width (`digestRaw_size`), so the
checked digest succeeds on every message. -/
theorem Algorithm.digest_eq_ok (algorithm : Algorithm) (message : List Byte) :
    algorithm.digest message =
      .ok (Vector.ofFn fun i : Fin algorithm.outputLength =>
        (algorithm.digestRaw message)[i.val]'(by
          rw [algorithm.digestRaw_size message]
          exact i.isLt)) := by
  unfold Algorithm.digest digestBytesExact
  rw [dif_pos (algorithm.digestRaw_size message)]

/-- Canonical binding of one registry entry's DER OID and digest implementation. -/
def Algorithm.descriptor (algorithm : Algorithm) : PrehashDescriptor where
  oidDer := algorithm.oidDer
  outputLength := algorithm.outputLength
  digest := algorithm.digest

/-- Reject a pre-hash algorithm below the selected parameter set's claimed strength. -/
def requireStrength (p : Params) (algorithm : Algorithm) : Except Error Unit :=
  if algorithm.validFor p then
    .ok ()
  else
    .error (.prehashTooWeak p.n algorithm.outputLength)

/-- Checked Algorithm 23/25 message encoding. -/
def encodeMessage (p : Params) (algorithm : Algorithm) (context message : List Byte) :
    Except Error (List Byte) := do
  requireContext context
  requireStrength p algorithm
  encodePrehashMessageWithDescriptor algorithm.descriptor context message

/-- Checked Algorithm 23 with caller-supplied hedging randomness. -/
def signWithRandomizer (vp : ValidatedParams) (prims : Primitives vp.params)
    (algorithm : Algorithm) (message context : List Byte) (sk : SecretKeyCore prims.core)
    (addrnd : prims.Y) : Except Error (GeneralScheme.SignatureCore vp prims.core) := do
  requireContext context
  requireStrength vp.params algorithm
  signPrehashWithDescriptorAndRandomizer vp prims algorithm.descriptor message context sk addrnd

/-- Checked deterministic Algorithm 23. FIPS 205 Algorithm 19 line 2 normatively sets
`opt_rand = PK.seed`; FIPS-conforming callers must pass the canonical conversion for the
selected approved family (`SLHDSA.Concrete.approvedRandomizerOfPkSeed`), or use the pinned
entry point `signDeterministicApproved` which does so. -/
def signDeterministic (vp : ValidatedParams) (prims : Primitives vp.params)
    (pkSeedToRandomizer : prims.PkSeed → prims.Y) (algorithm : Algorithm)
    (message context : List Byte) (sk : SecretKeyCore prims.core) :
    Except Error (GeneralScheme.SignatureCore vp prims.core) := do
  requireContext context
  requireStrength vp.params algorithm
  signPrehashWithDescriptorDeterministic vp prims pkSeedToRandomizer algorithm.descriptor
    message context sk

/-- Checked hedged Algorithm 23 under the ideal total random source. -/
noncomputable def sign (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.Y] (algorithm : Algorithm) (message context : List Byte)
    (sk : SecretKeyCore prims.core) :
    ProbComp (Except Error (GeneralScheme.SignatureCore vp prims.core)) :=
  match requireContext context with
  | .error error => pure (.error error)
  | .ok _ =>
      match requireStrength vp.params algorithm with
      | .error error => pure (.error error)
      | .ok _ => signPrehashWithDescriptor vp prims algorithm.descriptor message context sk

/-- Checked Algorithm 25. Weak pairings and message-boundary failures reject as `false`. -/
def verify (vp : ValidatedParams) (prims : Primitives vp.params) [DecidableEq prims.Y]
    (algorithm : Algorithm) (message : List Byte)
    (signature : GeneralScheme.SignatureCore vp prims.core) (context : List Byte)
    (pk : PublicKeyCore prims.core) : Bool :=
  match requireContext context with
  | .error _ => false
  | .ok _ =>
      match requireStrength vp.params algorithm with
      | .error _ => false
      | .ok _ =>
          verifyPrehashWithDescriptor vp prims algorithm.descriptor message signature context pk

/-! ## Checked completeness and boundary rejection -/

/-- A registry algorithm meeting the §10.2 strength policy passes the checked boundary. -/
theorem requireStrength_eq_ok (p : Params) (algorithm : Algorithm)
    (h : algorithm.ValidFor p) : requireStrength p algorithm = .ok () :=
  if_pos ((algorithm.validFor_iff p).mpr h)

/-- **Checked pre-hash completeness** (Algorithms 21, 23, 25): under the FIPS 205 context
bound and the §10.2 strength policy, checked pre-hash signing under an honestly generated key
succeeds, and checked verification of the produced signature for the same message and context
with the matching public key accepts. -/
theorem verify_signWithRandomizer (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (algorithm : Algorithm) (message context : List Byte)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) (addrnd : prims.Y)
    (hcontext : context.length ≤ 255) (hstrength : algorithm.ValidFor vp.params) :
    (signWithRandomizer vp prims algorithm message context
        (keygenWithSeeds vp prims skSeed skPrf pkSeed).1 addrnd).map
      (fun signature => verify vp prims algorithm message signature context
        (keygenWithSeeds vp prims skSeed skPrf pkSeed).2) = .ok true := by
  simp only [signWithRandomizer, verify, requireContext_eq_ok context hcontext,
    requireStrength_eq_ok vp.params algorithm hstrength]
  exact verifyPrehashWithDescriptor_signPrehashWithDescriptorAndRandomizer vp prims
    algorithm.descriptor message context skSeed skPrf pkSeed addrnd hcontext
    (algorithm.digest_eq_ok message)

/-- Algorithm 25 lines 1--2: checked verification rejects an overlong context as `false` for
every signature and public key, before the strength policy and before any hashing. -/
theorem verify_eq_false_of_contextTooLong (vp : ValidatedParams)
    (prims : Primitives vp.params) [DecidableEq prims.Y] (algorithm : Algorithm)
    (message : List Byte) (signature : GeneralScheme.SignatureCore vp prims.core)
    (context : List Byte) (pk : PublicKeyCore prims.core) (h : 255 < context.length) :
    verify vp prims algorithm message signature context pk = false := by
  unfold verify
  rw [requireContext_eq_error context h]

/-! ## FIPS-pinned deterministic entry point -/

/-- Checked deterministic Algorithm 23 pinned to FIPS 205 Algorithm 19 line 2: `opt_rand` is
`PK.seed` under `approvedRandomizerOfPkSeed`, in the exact approved primitive family selected
by `approvedPrimitives`. FIPS-conforming deterministic pre-hash signing must use this entry
point (or pass the same conversion to `signDeterministic` explicitly). -/
def signDeterministicApproved (set : FipsParameterSet) (algorithm : Algorithm)
    (message context : List Byte) (sk : SecretKeyCore (approvedPrimitives set).core) :
    Except Error
      (GeneralScheme.SignatureCore set.validatedParams (approvedPrimitives set).core) :=
  signDeterministic set.validatedParams (approvedPrimitives set)
    (approvedRandomizerOfPkSeed set) algorithm message context sk

/-- Completeness of the pinned deterministic checked entry point: the honest key pair produced
by Algorithm 21 round-trips through `signDeterministicApproved` and `verify`. -/
theorem verify_signDeterministicApproved (set : FipsParameterSet)
    [DecidableEq (approvedPrimitives set).Y] (algorithm : Algorithm)
    (message context : List Byte) (skSeed : (approvedPrimitives set).SkSeed)
    (skPrf : (approvedPrimitives set).SkPrf) (pkSeed : (approvedPrimitives set).PkSeed)
    (hcontext : context.length ≤ 255) (hstrength : algorithm.ValidFor set.params) :
    (signDeterministicApproved set algorithm message context
        (keygenWithSeeds set.validatedParams (approvedPrimitives set)
          skSeed skPrf pkSeed).1).map
      (fun signature => verify set.validatedParams (approvedPrimitives set) algorithm message
        signature context
        (keygenWithSeeds set.validatedParams (approvedPrimitives set)
          skSeed skPrf pkSeed).2) = .ok true :=
  verify_signWithRandomizer set.validatedParams (approvedPrimitives set) algorithm message
    context skSeed skPrf pkSeed
    (approvedRandomizerOfPkSeed set
      (keygenWithSeeds set.validatedParams (approvedPrimitives set)
        skSeed skPrf pkSeed).1.pkSeed)
    hcontext hstrength

end SLHDSA.Concrete.Prehash

namespace SLHDSA.Concrete

/-! ## FIPS-pinned deterministic pure-mode entry point -/

/-- Deterministic Algorithm 22 pinned to FIPS 205 Algorithm 19 line 2: `opt_rand` is `PK.seed`
under `approvedRandomizerOfPkSeed`, in the exact approved primitive family selected by
`approvedPrimitives`. FIPS-conforming deterministic pure-mode signing must use this entry
point (or pass the same conversion to `External.signPureDeterministic` explicitly). -/
def signPureDeterministicApproved (set : FipsParameterSet) (message context : List Byte)
    (sk : SecretKeyCore (approvedPrimitives set).core) :
    Except External.Error
      (GeneralScheme.SignatureCore set.validatedParams (approvedPrimitives set).core) :=
  External.signPureDeterministic set.validatedParams (approvedPrimitives set)
    (approvedRandomizerOfPkSeed set) message context sk

/-- Completeness of the pinned deterministic pure-mode entry point: the honest key pair
produced by Algorithm 21 round-trips through `signPureDeterministicApproved` and
`External.verifyPure`. -/
theorem verifyPure_signPureDeterministicApproved (set : FipsParameterSet)
    [DecidableEq (approvedPrimitives set).Y] (message context : List Byte)
    (skSeed : (approvedPrimitives set).SkSeed) (skPrf : (approvedPrimitives set).SkPrf)
    (pkSeed : (approvedPrimitives set).PkSeed) (hcontext : context.length ≤ 255) :
    (signPureDeterministicApproved set message context
        (External.keygenWithSeeds set.validatedParams (approvedPrimitives set)
          skSeed skPrf pkSeed).1).map
      (fun signature => External.verifyPure set.validatedParams (approvedPrimitives set)
        message signature context
        (External.keygenWithSeeds set.validatedParams (approvedPrimitives set)
          skSeed skPrf pkSeed).2) = .ok true :=
  External.verifyPure_signPureWithRandomizer set.validatedParams (approvedPrimitives set)
    message context skSeed skPrf pkSeed
    (approvedRandomizerOfPkSeed set
      (External.keygenWithSeeds set.validatedParams (approvedPrimitives set)
        skSeed skPrf pkSeed).1.pkSeed)
    hcontext

end SLHDSA.Concrete
