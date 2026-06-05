/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Scheme
import HashSig.SLHDSA.Concrete.Sha2

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
(`R ‖ SIG_FORS ‖ SIG_HT`) so reference signatures can be verified.

`keygen`/`sign` are intentionally not executed here (they build the full `2^22`-leaf XMSS and
FORS trees — ~`10^9` hashes); `verify` is ~`400` hashes and is the executable validation path.

## References

- NIST FIPS 205, §11.2.1 (SHA-2 category-1 instantiation), Fig 17 (signature layout)
-/


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

/-- Concatenate a list of 16-byte nodes. -/
def concatNodes (ys : List (Bytes 16)) : ByteArray :=
  ys.foldl (fun acc y => acc ++ b16ToBA y) ByteArray.empty

/-! ### The SHA-2 tweakable hash family (FIPS 205 §11.2.1) -/

/-- `F(PK.seed, ADRS, M₁) = Trunc₁₆(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ M₁))`. -/
def shaF (pkSeed : Bytes 16) (adrs : Adrs) (y : Bytes 16) : Bytes 16 :=
  baToBytes (sha256 (thashPrefix pkSeed adrs ++ b16ToBA y)) 16

/-- `H(PK.seed, ADRS, M_l ‖ M_r) = Trunc₁₆(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ M_l ‖ M_r))`. -/
def shaH (pkSeed : Bytes 16) (adrs : Adrs) (l r : Bytes 16) : Bytes 16 :=
  baToBytes (sha256 (thashPrefix pkSeed adrs ++ b16ToBA l ++ b16ToBA r)) 16

/-- `T_ℓ(PK.seed, ADRS, M) = Trunc₁₆(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ M))`. -/
def shaTl (pkSeed : Bytes 16) (adrs : Adrs) (ys : List (Bytes 16)) : Bytes 16 :=
  baToBytes (sha256 (thashPrefix pkSeed adrs ++ concatNodes ys)) 16

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
  F := shaF
  H := shaH
  Tl := shaTl
  PRF := shaPRF
  PRFmsg := shaPRFmsg
  Hmsg := shaHmsg
  yToBytes := fun y => y

/-! ### Fixed-width signature decoding (FIPS 205 Fig 17 wire format) -/

/-- Decode the 3856-byte signature `R ‖ SIG_FORS ‖ SIG_HT` (FORS: `k` trees of
`sk(16) ‖ auth(a×16)`; HT: WOTS `len×16` then XMSS auth `h'×16`). -/
def decodeSignature (ba : ByteArray) : Signature shaPrimitives :=
  let R : Bytes 16 := baSliceToB16 ba 0
  let fors : Vector (Bytes 16 × List (Bytes 16)) 6 :=
    Vector.ofFn fun i : Fin 6 =>
      let base := 16 + i.val * 400
      (baSliceToB16 ba base,
        (List.range 24).map fun j => baSliceToB16 ba (base + 16 + j * 16))
  let wots : Vector (Bytes 16) 68 :=
    Vector.ofFn fun i : Fin 68 => baSliceToB16 ba (2416 + i.val * 16)
  let xmssAuth : List (Bytes 16) :=
    (List.range 22).map fun j => baSliceToB16 ba (2416 + 1088 + j * 16)
  (R, fors, (wots, xmssAuth))

/-- Concrete verification of a decoded reference signature against `(pkSeed, pkRoot, message)`. -/
def verifyBytes (pkSeed pkRoot : Bytes 16) (msg : List Byte) (sigBytes : ByteArray) : Bool :=
  letI : DecidableEq shaPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 16))
  slhVerify shaPrimitives ⟨pkSeed, pkRoot⟩ msg (decodeSignature sigBytes)

/-! ### Completeness transfers to the concrete bundle

The carrier instances are supplied explicitly: the structure projections `shaPrimitives.SkSeed`
… are definitionally `Bytes 16`, but instance synthesis does not unfold them, so the abstract
`slhdsaAlg_perfectlyComplete` cannot be specialized to `shaPrimitives` by `inferInstance` alone. -/

instance : SampleableType shaPrimitives.SkSeed := inferInstanceAs (SampleableType (Bytes 16))
instance : SampleableType shaPrimitives.SkPrf := inferInstanceAs (SampleableType (Bytes 16))
instance : SampleableType shaPrimitives.PkSeed := inferInstanceAs (SampleableType (Bytes 16))
instance : SampleableType shaPrimitives.Y := inferInstanceAs (SampleableType (Bytes 16))
instance : DecidableEq shaPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 16))

/-- **Perfect completeness at the concrete SHA2-128-24 bundle.** The abstract
`slhdsaAlg_perfectlyComplete` (proved for any `Primitives`) specialized to `shaPrimitives` — the
exact bundle `verifyBytes` executes. This is the in-tree object asserting that the proved
`Pr[verify (sign m)] = 1` property holds for the concrete code path the KAT exercises, closing the
gap between the abstract theorem and the executable instance. -/
theorem shaPrimitives_perfectlyComplete :
    (slhdsaAlg shaPrimitives).PerfectlyComplete ProbCompRuntime.probComp :=
  slhdsaAlg_perfectlyComplete shaPrimitives

end SLHDSA.Concrete
