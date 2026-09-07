/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.RandomOracle
public import HashSig.SLHDSA.Concrete.Sha2

/-!
# Concrete SLH-DSA-SHA2-128-24 instantiation

Wires pure-Lean SHA-256 (`HashSig.SLHDSA.Concrete.Sha2`) into the abstract `Primitives` bundle
to make the proof-level scheme executable at the SLH-DSA-SHA2-128-24 parameter set, following
the FIPS 205 §11.2.1 SHA-2 (category-1) instantiation:

- node/seed type `Y = PkSeed = SkSeed = SkPrf = Bytes 16` (`n = 16`);
- `F`/`H`/`T_ℓ`/`PRF` = `Trunc₁₆(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ payload))`;
- `PRF_msg` = `Trunc₁₆(HMAC-SHA-256(SK.prf, opt_rand ‖ M))`;
- `H_msg` = `MGF1-SHA-256(R ‖ PK.seed ‖ SHA-256(R ‖ PK.seed ‖ PK.root ‖ M), 21)`;

where `ADRSc` is the 22-byte compressed address (`Adrs.compressSha2`). A fixed-width signature
decoder (`decodeSignature`) parses the 3856-byte FIPS wire format
(`R ‖ SIG_FORS ‖ SIG_HT`) so reference signatures can be verified; it is proved to agree with
the strict structured codec on every canonical wire in `HashSig.SLHDSA.Concrete.Codec`.

`keygen`/`sign` are intentionally not executed here (they build the full `2^22`-leaf XMSS and
FORS trees — ~`10^9` hashes); `verify` is ~`400` hashes and is the executable validation path.

## References

- NIST FIPS 205, §11.2.1 (SHA-2 category-1 instantiation), Fig 17 (signature layout)
-/

@[expose] public section


namespace SLHDSA.Concrete

open SLHDSA Sha2

/-! ### Byte conversions -/

/-- A 16-byte node as a `ByteArray`. -/
def b16ToBA (v : Bytes 16) : ByteArray := ByteArray.mk v.toArray

/-- Read a 16-byte node from `ba` starting at byte offset `off`. -/
def baSliceToB16 (ba : ByteArray) (off : ℕ) : Bytes 16 :=
  Vector.ofFn fun i : Fin 16 => ba[off + i.val]!

/-- Read the first `n` bytes of `ba` as a fixed-length byte vector (zero past the end). -/
def baToBytes (ba : ByteArray) (n : ℕ) : Bytes n :=
  Vector.ofFn fun i : Fin n => ba[i.val]?.getD 0

/-- 48 zero bytes (`toByte(0, 64 − n)` for `n = 16`). -/
def zeros48 : ByteArray := ByteArray.mk (Array.replicate 48 0)

/-- The shared SHA-2 thash prefix `PK.seed ‖ 0^48 ‖ ADRSc`. -/
def thashPrefix (pkSeed : Bytes 16) (adrs : Adrs) : ByteArray :=
  b16ToBA pkSeed ++ zeros48 ++ ByteArray.mk adrs.compressSha2.toArray

/-- The fixed-width 22-byte SHA-2 address key. -/
def shaAdrsKey (adrs : Adrs) : Bytes 22 :=
  ⟨adrs.compressSha2.toArray, by simp [Adrs.compressSha2, Adrs.toBytesBE]⟩

/-- The fixed-width SHA-2 public-hash key is exactly the FIPS 205 compressed address `ADRSc`. -/
@[simp]
theorem shaAdrsKey_toList (adrs : Adrs) :
    (shaAdrsKey adrs).toList = adrs.compressSha2 := by
  simp [shaAdrsKey]

/-- The shared SHA-2 thash prefix from an already-canonicalized `ADRSc`. -/
def thashPrefixEncoded (pkSeed : Bytes 16) (encodedAdrs : Bytes 22) : ByteArray :=
  b16ToBA pkSeed ++ zeros48 ++ ByteArray.mk encodedAdrs.toArray

/-- Concatenate a list of 16-byte nodes. -/
def concatNodes (ys : List (Bytes 16)) : ByteArray :=
  ys.foldl (fun acc y => acc ++ b16ToBA y) ByteArray.empty

/-! ### The SHA-2 tweakable hash family (FIPS 205 §11.2.1) -/

/-- The common variable-arity SHA-2 tweakable hash underlying `F`, `H = T₂`, and `T_ℓ`. -/
def shaThash (pkSeed : Bytes 16) (encodedAdrs : Bytes 22) (ys : List (Bytes 16)) : Bytes 16 :=
  baToBytes (sha256 (thashPrefixEncoded pkSeed encodedAdrs ++ concatNodes ys)) 16

/-- `F(PK.seed, ADRS, M₁) = Trunc₁₆(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ M₁))`. -/
def shaF (pkSeed : Bytes 16) (adrs : Adrs) (y : Bytes 16) : Bytes 16 :=
  shaThash pkSeed (shaAdrsKey adrs) [y]

/-- `H(PK.seed, ADRS, M_l ‖ M_r) = Trunc₁₆(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ M_l ‖ M_r))`. -/
def shaH (pkSeed : Bytes 16) (adrs : Adrs) (l r : Bytes 16) : Bytes 16 :=
  shaThash pkSeed (shaAdrsKey adrs) [l, r]

/-- `T_ℓ(PK.seed, ADRS, M) = Trunc₁₆(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ M))`. -/
def shaTl (pkSeed : Bytes 16) (adrs : Adrs) (ys : List (Bytes 16)) : Bytes 16 :=
  shaThash pkSeed (shaAdrsKey adrs) ys

/-- `PRF(PK.seed, SK.seed, ADRS) = Trunc₁₆(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ SK.seed))`. -/
def shaPRF (pkSeed : Bytes 16) (skSeed : Bytes 16) (adrs : Adrs) : Bytes 16 :=
  baToBytes (sha256 (thashPrefix pkSeed adrs ++ b16ToBA skSeed)) 16

/-- `PRF_msg(SK.prf, opt_rand, M) = Trunc₁₆(HMAC-SHA-256(SK.prf, opt_rand ‖ M))`. -/
def shaPRFmsg (skPrf : Bytes 16) (optrand : Bytes 16) (msg : List Byte) : Bytes 16 :=
  baToBytes (hmacSha256 (b16ToBA skPrf) (b16ToBA optrand ++ ByteArray.mk msg.toArray)) 16

/-- `H_msg(R, PK.seed, PK.root, M) = MGF1-SHA-256(R ‖ PK.seed ‖ SHA-256(R ‖ PK.seed ‖ PK.root ‖ M),
m)` (FIPS 205 §10.2 / §11.2.1). -/
def shaHmsg (R : Bytes 16) (pkSeed : Bytes 16) (pkRoot : Bytes 16) (msg : List Byte) :
    Bytes slhdsaSha2_128_24.m :=
  let inner := sha256 (b16ToBA R ++ b16ToBA pkSeed ++ b16ToBA pkRoot ++ ByteArray.mk msg.toArray)
  baToBytes (mgf1 (b16ToBA R ++ b16ToBA pkSeed ++ inner) slhdsaSha2_128_24.m) slhdsaSha2_128_24.m

/-- The concrete SLH-DSA-SHA2-128-24 primitive bundle. -/
def shaPrimitives : Primitives slhdsaSha2_128_24 where
  PkSeed := Bytes 16
  SkSeed := Bytes 16
  SkPrf := Bytes 16
  Y := Bytes 16
  AdrsKey := Bytes 22
  adrsToKey := shaAdrsKey
  Thash := shaThash
  PRF := shaPRF
  PRFmsg := shaPRFmsg
  Hmsg := shaHmsg
  yToBytes := fun y => y

/-- The supported reduced SHA2-128-24 compatibility profile has one hypertree layer. -/
theorem shaParams_d_eq_one : slhdsaSha2_128_24.d = 1 := rfl

/-! ### Fixed-width signature decoding (FIPS 205 Fig 17 wire format) -/

/-- Decode the 3856-byte signature `R ‖ SIG_FORS ‖ SIG_HT` (FORS: `k` trees of
`sk(16) ‖ auth(a×16)`; HT: WOTS `len×16` then XMSS auth `h'×16`).

This fixed-offset reader predates the strict structured codec (`HashSig.SLHDSA.Codec`) and
performs no width check of its own; KAT inputs are exact-width by construction. It is proved
to agree with the strict codec on every canonical wire:
`SLHDSA.Concrete.decodeSignature_encodeSignature` shows that decoding a strict
`encodeSignature` wire recovers exactly the encoded signature, and
`SLHDSA.Concrete.decodeSignature_eq_of_strict_ok` shows that whenever the strict checked
decoder accepts an input, this decoder produces the same structured value
(`HashSig.SLHDSA.Concrete.Codec`). New FIPS-facing byte surfaces should use the strict
codec, which rejects non-exact widths before any semantic value is built. -/
def decodeSignature (ba : ByteArray) : SignatureCore slhdsaSha2_128_24 shaPrimitives.core :=
  let R : Bytes 16 := baSliceToB16 ba 0
  let fors : ForsSigCore slhdsaSha2_128_24 shaPrimitives.core :=
    Vector.ofFn fun i : Fin 6 =>
      let base := 16 + i.val * 400
      { sk := baSliceToB16 ba base
        auth := Vector.ofFn fun j : Fin 24 => baSliceToB16 ba (base + 16 + j.val * 16) }
  let wots : Vector (Bytes 16) 68 :=
    Vector.ofFn fun i : Fin 68 => baSliceToB16 ba (2416 + i.val * 16)
  let xmssAuth : Vector (Bytes 16) 22 :=
    Vector.ofFn fun j : Fin 22 => baSliceToB16 ba (2416 + 1088 + j.val * 16)
  let xmss : XmssSigCore slhdsaSha2_128_24 shaPrimitives.core := ⟨wots, xmssAuth⟩
  ⟨R, fors, HtSigCore.singleLayer shaParams_d_eq_one xmss⟩

/-- Concrete FIPS 205 external verification of a decoded signature against
`(pkSeed, pkRoot, message)`. -/
def verifyBytes (pkSeed pkRoot : Bytes 16) (msg : List Byte) (sigBytes : ByteArray) : Bool :=
  letI : DecidableEq shaPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 16))
  slhVerifyInternal shaParams_d_eq_one shaPrimitives (emptyContextMessage msg)
    (decodeSignature sigBytes) ⟨pkSeed, pkRoot⟩

/-- Verification against the internal `M'` interface. This entry point supports reference vectors
whose message is already the exact input consumed by `H_msg`, without applying the external
context encoding a second time. -/
def verifyInternalBytes (pkSeed pkRoot : Bytes 16) (msg : List Byte)
    (sigBytes : ByteArray) : Bool :=
  letI : DecidableEq shaPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 16))
  slhVerifyInternal shaParams_d_eq_one shaPrimitives msg (decodeSignature sigBytes) ⟨pkSeed, pkRoot⟩

/-! ### Completeness transfers to the concrete bundle

The carrier instances are supplied explicitly: the structure projections `shaPrimitives.SkSeed`
… are definitionally `Bytes 16`, but instance synthesis does not unfold them automatically. -/

instance : SampleableType shaPrimitives.SkSeed := inferInstanceAs (SampleableType (Bytes 16))
instance : SampleableType shaPrimitives.SkPrf := inferInstanceAs (SampleableType (Bytes 16))
instance : SampleableType shaPrimitives.PkSeed := inferInstanceAs (SampleableType (Bytes 16))
instance : SampleableType shaPrimitives.Y := inferInstanceAs (SampleableType (Bytes 16))
instance : DecidableEq shaPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 16))

/-- **Perfect completeness at the concrete SHA2-128-24 bundle.** This specializes the
definitional concrete-function interpretation of the canonical oracle-parametric scheme to the
exact primitive bundle exercised by `verifyBytes`. -/
theorem shaPrimitives_perfectlyComplete :
    (slhdsaConcreteAlg shaParams_d_eq_one shaPrimitives).PerfectlyComplete
      ProbCompRuntime.probComp :=
  slhdsaConcreteAlg_perfectlyComplete shaParams_d_eq_one shaPrimitives

end SLHDSA.Concrete
