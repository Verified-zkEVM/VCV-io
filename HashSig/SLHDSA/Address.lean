/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.EncodingLemmas

/-!
# SLH-DSA Addresses (ADRS)

The 32-byte hash address `ADRS` of FIPS 205 §4.2, used as the per-call tweak of every SLH-DSA
tweakable hash. It consists of the fields `layer ‖ tree ‖ type ‖ w₁ ‖ w₂ ‖ w₃`
(the `tree` field spanning words 1–3, i.e. 12 bytes / 96 bits; the final three words are
type-dependent). We model it as a record of its fields rather than a raw byte vector. Internal
construction code uses plain field updates under its algorithmic range preconditions; checked
variants reject out-of-range external values. The address stays opaque to the verified core and
enters only as the hash tweak.

Two type-dependent words alias by name exactly as in FIPS 205:
`setChainAddress = setTreeHeight` (word 2) and `setHashAddress = setTreeIndex` (word 3).

`toBytes` / `compressSha2` give the 32-byte serialization and the 22-byte SHA-2 `ADRSc`
compression (§11.2.1) as byte lists. `encodeChecked`, `compressSha2Checked`, and `decode` enforce
representability, recognized types, and type-specific canonical padding at external boundaries.

## References

- NIST FIPS 205, §4.2 (ADRS), Table 1 (member functions), §11.2.1 (ADRSc compression)
-/

@[expose] public section


namespace SLHDSA

/-- The seven SLH-DSA address types (FIPS 205 §4.2). -/
inductive AddrType where
  | wotsHash | wotsPk | tree | forsTree | forsRoots | wotsPrf | forsPrf
deriving Repr, DecidableEq, Inhabited

/-- Decode one of the seven exact FIPS address type codes. -/
def AddrType.ofCode : ℕ → Option AddrType
  | 0 => some .wotsHash
  | 1 => some .wotsPk
  | 2 => some .tree
  | 3 => some .forsTree
  | 4 => some .forsRoots
  | 5 => some .wotsPrf
  | 6 => some .forsPrf
  | _ => none

/-- The numeric type code written into the ADRS `type` word. -/
def AddrType.toCode : AddrType → ℕ
  | .wotsHash => 0
  | .wotsPk => 1
  | .tree => 2
  | .forsTree => 3
  | .forsRoots => 4
  | .wotsPrf => 5
  | .forsPrf => 6

@[simp] theorem AddrType.ofCode_toCode (ty : AddrType) :
    AddrType.ofCode ty.toCode = some ty := by cases ty <;> rfl

/-- A FIPS 205 hash address, as the eight conceptual words (the 96-bit `tree` field is one `ℕ`).
The three type-dependent words `word1/word2/word3` occupy byte offsets 20–23/24–27/28–31. -/
structure Adrs where
  /-- Hypertree layer address (bytes 0–3). -/
  layer : ℕ
  /-- Tree address within the layer (bytes 4–15, big-endian). -/
  tree : ℕ
  /-- Address type code (bytes 16–19); one of `AddrType.toCode`. -/
  type : ℕ
  /-- First type-dependent word (bytes 20–23): key-pair address, or padding. -/
  word1 : ℕ
  /-- Second type-dependent word (bytes 24–27): chain address / tree height / padding. -/
  word2 : ℕ
  /-- Third type-dependent word (bytes 28–31): hash address / tree index / padding. -/
  word3 : ℕ
deriving Repr, DecidableEq, Inhabited

namespace Adrs

/-- Two structured addresses are equal when all six encoded fields are equal. -/
@[ext] theorem ext {a b : Adrs} (hlayer : a.layer = b.layer) (htree : a.tree = b.tree)
    (htype : a.type = b.type) (hword1 : a.word1 = b.word1) (hword2 : a.word2 = b.word2)
    (hword3 : a.word3 = b.word3) : a = b := by
  cases a
  cases b
  simp_all

/-- Executable check that a natural number fits in an unsigned big-endian field. -/
def Fits (widthBytes value : ℕ) : Bool := decide (value < 256 ^ widthBytes)

/-- Shared rejecting range check for ADRS setters. -/
def requireFits (widthBytes value : ℕ) : Except CodecError ℕ :=
  if Fits widthBytes value then .ok value else .error (.outOfRange widthBytes value)

/-- The all-zero address (`toByte(0, 32)`). -/
def zero : Adrs := ⟨0, 0, 0, 0, 0, 0⟩

/-- `ADRS.setLayerAddress(l)`. -/
def setLayerAddress (a : Adrs) (l : ℕ) : Adrs := { a with layer := l }

/-- `ADRS.setTreeAddress(t)`. -/
def setTreeAddress (a : Adrs) (t : ℕ) : Adrs := { a with tree := t }

/-- Checked 32-bit layer setter for decoded or external values. -/
def setLayerAddressChecked (a : Adrs) (l : ℕ) : Except CodecError Adrs := do
  return a.setLayerAddress (← requireFits 4 l)

/-- Checked 96-bit tree setter for decoded or external values. -/
def setTreeAddressChecked (a : Adrs) (t : ℕ) : Except CodecError Adrs := do
  return a.setTreeAddress (← requireFits 12 t)

/-- `ADRS.setTypeAndClear(Y)`: set the type and zero the three type-dependent words. -/
def setTypeAndClear (a : Adrs) (ty : AddrType) : Adrs :=
  { a with type := ty.toCode, word1 := 0, word2 := 0, word3 := 0 }

/-- `ADRS.setKeyPairAddress(i)` (word 1). -/
def setKeyPairAddress (a : Adrs) (i : ℕ) : Adrs := { a with word1 := i }

/-- `ADRS.setChainAddress(i)` (word 2); aliases `setTreeHeight`. -/
def setChainAddress (a : Adrs) (i : ℕ) : Adrs := { a with word2 := i }

/-- `ADRS.setTreeHeight(z)` (word 2); aliases `setChainAddress`. -/
def setTreeHeight (a : Adrs) (z : ℕ) : Adrs := { a with word2 := z }

/-- `ADRS.setHashAddress(i)` (word 3); aliases `setTreeIndex`. -/
def setHashAddress (a : Adrs) (i : ℕ) : Adrs := { a with word3 := i }

/-- `ADRS.setTreeIndex(i)` (word 3); aliases `setHashAddress`. -/
def setTreeIndex (a : Adrs) (i : ℕ) : Adrs := { a with word3 := i }

/-- Checked 32-bit type-dependent word setters. -/
def setKeyPairAddressChecked (a : Adrs) (i : ℕ) : Except CodecError Adrs := do
  return a.setKeyPairAddress (← requireFits 4 i)

def setChainAddressChecked (a : Adrs) (i : ℕ) : Except CodecError Adrs := do
  return a.setChainAddress (← requireFits 4 i)

def setTreeHeightChecked (a : Adrs) (z : ℕ) : Except CodecError Adrs := do
  return a.setTreeHeight (← requireFits 4 z)

def setHashAddressChecked (a : Adrs) (i : ℕ) : Except CodecError Adrs := do
  return a.setHashAddress (← requireFits 4 i)

def setTreeIndexChecked (a : Adrs) (i : ℕ) : Except CodecError Adrs := do
  return a.setTreeIndex (← requireFits 4 i)

/-- `ADRS.getKeyPairAddress()` (word 1). -/
def getKeyPairAddress (a : Adrs) : ℕ := a.word1

/-- `ADRS.getTreeIndex()` (word 3). -/
def getTreeIndex (a : Adrs) : ℕ := a.word3

@[simp] theorem getKeyPairAddress_setKeyPairAddress (a : Adrs) (i : ℕ) :
    (a.setKeyPairAddress i).getKeyPairAddress = i := rfl

@[simp] theorem getTreeIndex_setTreeIndex (a : Adrs) (i : ℕ) :
    (a.setTreeIndex i).getTreeIndex = i := rfl

@[simp] theorem getTreeIndex_setTreeHeight (a : Adrs) (z : ℕ) :
    (a.setTreeHeight z).getTreeIndex = a.getTreeIndex := rfl

@[simp] theorem getKeyPairAddress_setTreeHeight (a : Adrs) (z : ℕ) :
    (a.setTreeHeight z).getKeyPairAddress = a.getKeyPairAddress := rfl

@[simp] theorem getKeyPairAddress_setTreeIndex (a : Adrs) (i : ℕ) :
    (a.setTreeIndex i).getKeyPairAddress = a.getKeyPairAddress := rfl

@[simp] theorem setTypeAndClear_word1 (a : Adrs) (ty : AddrType) :
    (a.setTypeAndClear ty).word1 = 0 := rfl

@[simp] theorem setTypeAndClear_word2 (a : Adrs) (ty : AddrType) :
    (a.setTypeAndClear ty).word2 = 0 := rfl

@[simp] theorem setTypeAndClear_word3 (a : Adrs) (ty : AddrType) :
    (a.setTypeAndClear ty).word3 = 0 := rfl

@[simp] theorem setTypeAndClear_type (a : Adrs) (ty : AddrType) :
    (a.setTypeAndClear ty).type = ty.toCode := rfl

/-- FIPS-canonical full ADRS values have exact field widths, a recognized type, and zeroes in every
word unused by the selected WOTS, tree, FORS, or PRF address layout. -/
def isCanonical (a : Adrs) : Bool :=
  Fits 4 a.layer && Fits 12 a.tree && Fits 4 a.type &&
  Fits 4 a.word1 && Fits 4 a.word2 && Fits 4 a.word3 &&
  (AddrType.ofCode a.type).isSome &&
  match AddrType.ofCode a.type with
  | some .wotsPk | some .forsRoots => decide (a.word2 = 0 ∧ a.word3 = 0)
  | some .tree => decide (a.word1 = 0)
  | some .wotsPrf => decide (a.word3 = 0)
  | some .forsPrf => decide (a.word2 = 0)
  | some _ => true
  | none => false

/-! ### Byte serialization (for the future concrete hashing layer) -/

/-- Big-endian `len`-byte serialization of a natural number (`toByte(x, len)`, FIPS 205 Alg 3),
as a byte list. -/
def toBytesBE (x len : ℕ) : List Byte :=
  toByte x len

/-- The full 32-byte ADRS serialization (canonical whenever `a.isCanonical` is true):
`layer(4) ‖ tree(12) ‖ type(4) ‖ w₁(4) ‖ w₂(4) ‖ w₃(4)`. -/
def toBytes (a : Adrs) : List Byte :=
  toBytesBE a.layer 4 ++ toBytesBE a.tree 12 ++ toBytesBE a.type 4 ++
    toBytesBE a.word1 4 ++ toBytesBE a.word2 4 ++ toBytesBE a.word3 4

/-- The 22-byte SHA-2 compressed address `ADRSc` (FIPS 205 §11.2.1): the low layer byte, low
eight tree bytes, low type byte, then the three four-byte type-dependent words. -/
def compressSha2 (a : Adrs) : List Byte :=
  toBytesBE a.layer 1 ++ toBytesBE a.tree 8 ++ toBytesBE a.type 1 ++
    toBytesBE a.word1 4 ++ toBytesBE a.word2 4 ++ toBytesBE a.word3 4

@[simp] theorem toBytesBE_length (x len : ℕ) : (toBytesBE x len).length = len := by
  simp [toBytesBE]

@[simp] theorem toBytes_length (a : Adrs) : a.toBytes.length = 32 := by
  simp [toBytes]

@[simp] theorem compressSha2_length (a : Adrs) : a.compressSha2.length = 22 := by
  simp [compressSha2]

/-- Parse the six address fields from the exact byte layout used by SHA-2 `ADRSc`.  This is a
mathematical left inverse on the narrower SHA-2 address domain; it intentionally does not accept or
reject addresses at the external codec boundary. -/
def fromCompressedSha2 (raw : List Byte) : Adrs :=
  let afterLayer := raw.drop 1
  let afterTree := afterLayer.drop 8
  let afterType := afterTree.drop 1
  let afterWord1 := afterType.drop 4
  let afterWord2 := afterWord1.drop 4
  { layer := toInt (raw.take 1)
    tree := toInt (afterLayer.take 8)
    type := toInt (afterTree.take 1)
    word1 := toInt (afterType.take 4)
    word2 := toInt (afterWord1.take 4)
    word3 := toInt (afterWord2.take 4) }

/-- SHA-2 compressed-address parsing reconstructs every field that fits its exact compressed
width: one byte for layer and type, eight bytes for the tree, and four bytes for each
type-dependent word. -/
theorem fromCompressedSha2_compressSha2 (a : Adrs)
    (hlayer : Fits 1 a.layer = true) (htree : Fits 8 a.tree = true)
    (htype : Fits 1 a.type = true) (hword1 : Fits 4 a.word1 = true)
    (hword2 : Fits 4 a.word2 = true) (hword3 : Fits 4 a.word3 = true) :
    fromCompressedSha2 a.compressSha2 = a := by
  have hlayer' : a.layer < 256 ^ 1 := by simpa [Fits] using hlayer
  have htree' : a.tree < 256 ^ 8 := by simpa [Fits] using htree
  have htype' : a.type < 256 ^ 1 := by simpa [Fits] using htype
  have hword1' : a.word1 < 256 ^ 4 := by simpa [Fits] using hword1
  have hword2' : a.word2 < 256 ^ 4 := by simpa [Fits] using hword2
  have hword3' : a.word3 < 256 ^ 4 := by simpa [Fits] using hword3
  have htakeWord3 : (toByte a.word3 4).take 4 = toByte a.word3 4 := by
    simpa only [toByte_length] using (List.take_length (l := toByte a.word3 4))
  apply Adrs.ext
  · simpa [fromCompressedSha2, compressSha2, toBytesBE] using
      toInt_toByte a.layer 1 hlayer'
  · simpa [fromCompressedSha2, compressSha2, toBytesBE] using
      toInt_toByte a.tree 8 htree'
  · simpa [fromCompressedSha2, compressSha2, toBytesBE] using
      toInt_toByte a.type 1 htype'
  · simpa [fromCompressedSha2, compressSha2, toBytesBE] using
      toInt_toByte a.word1 4 hword1'
  · simpa [fromCompressedSha2, compressSha2, toBytesBE] using
      toInt_toByte a.word2 4 hword2'
  · simpa [fromCompressedSha2, compressSha2, toBytesBE, htakeWord3] using
      toInt_toByte a.word3 4 hword3'

/-- SHA-2 `ADRSc` is injective when both structural addresses lie in its exact field-width domain.
No claim is made for arbitrary `Adrs`: compression truncates out-of-range fields. -/
theorem compressSha2_injective_of_fits {a b : Adrs}
    (haLayer : Fits 1 a.layer = true) (haTree : Fits 8 a.tree = true)
    (haType : Fits 1 a.type = true) (haWord1 : Fits 4 a.word1 = true)
    (haWord2 : Fits 4 a.word2 = true) (haWord3 : Fits 4 a.word3 = true)
    (hbLayer : Fits 1 b.layer = true) (hbTree : Fits 8 b.tree = true)
    (hbType : Fits 1 b.type = true) (hbWord1 : Fits 4 b.word1 = true)
    (hbWord2 : Fits 4 b.word2 = true) (hbWord3 : Fits 4 b.word3 = true)
    (hbytes : a.compressSha2 = b.compressSha2) : a = b := by
  rw [← fromCompressedSha2_compressSha2 a haLayer haTree haType haWord1 haWord2 haWord3,
    ← fromCompressedSha2_compressSha2 b hbLayer hbTree hbType hbWord1 hbWord2 hbWord3,
    hbytes]

/-- The full serialization packaged at its exact wire width. -/
def toVector (a : Adrs) : Bytes 32 := ⟨a.toBytes.toArray, by simp⟩

/-- Parse the six ADRS fields from an exact 32-byte carrier. -/
def fromVector (bytes : Bytes 32) : Adrs :=
  let raw := bytes.toList
  let afterLayer := raw.drop 4
  let afterTree := afterLayer.drop 12
  let afterType := afterTree.drop 4
  let afterWord1 := afterType.drop 4
  let afterWord2 := afterWord1.drop 4
  { layer := toInt (raw.take 4)
    tree := toInt (afterLayer.take 12)
    type := toInt (afterTree.take 4)
    word1 := toInt (afterType.take 4)
    word2 := toInt (afterWord1.take 4)
    word3 := toInt (afterWord2.take 4) }

/-- Parsing full serialization reconstructs every representable ADRS field. Canonicality is not
needed for this arithmetic identity; only the six exact field-width conditions matter. -/
theorem fromVector_toVector (a : Adrs)
    (hlayer : Fits 4 a.layer = true) (htree : Fits 12 a.tree = true)
    (htype : Fits 4 a.type = true) (hword1 : Fits 4 a.word1 = true)
    (hword2 : Fits 4 a.word2 = true) (hword3 : Fits 4 a.word3 = true) :
    fromVector a.toVector = a := by
  have hlayer' : a.layer < 256 ^ 4 := by simpa [Fits] using hlayer
  have htree' : a.tree < 256 ^ 12 := by simpa [Fits] using htree
  have htype' : a.type < 256 ^ 4 := by simpa [Fits] using htype
  have hword1' : a.word1 < 256 ^ 4 := by simpa [Fits] using hword1
  have hword2' : a.word2 < 256 ^ 4 := by simpa [Fits] using hword2
  have hword3' : a.word3 < 256 ^ 4 := by simpa [Fits] using hword3
  have htakeWord3 : (toByte a.word3 4).take 4 = toByte a.word3 4 := by
    simpa only [toByte_length] using (List.take_length (l := toByte a.word3 4))
  apply Adrs.ext
  · simpa [fromVector, toVector, toBytes, toBytesBE] using toInt_toByte a.layer 4 hlayer'
  · simpa [fromVector, toVector, toBytes, toBytesBE] using toInt_toByte a.tree 12 htree'
  · simpa [fromVector, toVector, toBytes, toBytesBE] using toInt_toByte a.type 4 htype'
  · simpa [fromVector, toVector, toBytes, toBytesBE] using toInt_toByte a.word1 4 hword1'
  · simpa [fromVector, toVector, toBytes, toBytesBE] using toInt_toByte a.word2 4 hword2'
  · simpa [fromVector, toVector, toBytes, toBytesBE, htakeWord3] using
      toInt_toByte a.word3 4 hword3'

/-- Canonicality exposes all six exact field-width checks used by serialization. -/
theorem fits_of_isCanonical (a : Adrs) (h : a.isCanonical = true) :
    Fits 4 a.layer = true ∧ Fits 12 a.tree = true ∧ Fits 4 a.type = true ∧
      Fits 4 a.word1 = true ∧ Fits 4 a.word2 = true ∧ Fits 4 a.word3 = true := by
  simp only [isCanonical, Bool.and_eq_true] at h
  aesop

/-- Full serialization/parsing is identity for every canonical structured address. -/
theorem fromVector_toVector_of_isCanonical (a : Adrs) (h : a.isCanonical = true) :
    fromVector a.toVector = a := by
  rcases fits_of_isCanonical a h with ⟨hlayer, htree, htype, hword1, hword2, hword3⟩
  exact fromVector_toVector a hlayer htree htype hword1 hword2 hword3

/-- A decoded ADRS wire carrier together with the canonicality fact checked at the boundary. -/
structure Wire where
  bytes : Bytes 32
  valid : (fromVector bytes).isCanonical = true

namespace Wire

/-- Canonical ADRS wire encoding is exactly 32 bytes. -/
def encode (wire : Wire) : List Byte := wire.bytes.toList

/-- Parse the structured canonical address carried by a wire value. -/
def value (wire : Wire) : Adrs := fromVector wire.bytes

@[simp] theorem encode_length (wire : Wire) : wire.encode.length = 32 := by
  simp [encode]

end Wire

/-- Reject wrong lengths, unknown address types, and noncanonical type-specific padding. -/
def decode (raw : List Byte) : Except CodecError Wire :=
  match decodeExact 32 raw with
  | .error error => .error error
  | .ok bytes =>
      let a := fromVector bytes
      if h : a.isCanonical = true then
        .ok ⟨bytes, h⟩
      else
        match AddrType.ofCode a.type with
        | none => .error (.invalidAddressType a.type)
        | some _ => .error .noncanonicalAddress

@[simp] theorem decode_encode (wire : Wire) : decode wire.encode = .ok wire := by
  change decode (encodeExact wire.bytes) = .ok wire
  simp only [decode, decodeExact_encode]
  simp [wire.valid]

/-- Checked full serialization rejects noncanonical in-memory values before truncation. -/
def encodeChecked (a : Adrs) : Except CodecError (Bytes 32) :=
  if a.isCanonical then
    .ok a.toVector
  else
    .error .noncanonicalAddress

/-- A canonical structured address determines a canonical wire value. -/
def toWire (a : Adrs) (h : a.isCanonical = true) : Wire :=
  ⟨a.toVector, by simpa [fromVector_toVector_of_isCanonical a h] using h⟩

/-- Checked full encoding of a canonical structured address succeeds exactly. -/
theorem encodeChecked_eq (a : Adrs) (h : a.isCanonical = true) :
    encodeChecked a = .ok a.toVector := by
  simp [encodeChecked, h]

/-- Decoding a canonical structured address's full bytes recovers its canonical wire. -/
theorem decode_toBytes (a : Adrs) (h : a.isCanonical = true) :
    decode a.toBytes = .ok (toWire a h) := by
  change decode (encodeExact a.toVector) = .ok (toWire a h)
  simp [decode, toWire, h, fromVector_toVector_of_isCanonical]

/-- The semantic value obtained from the decoded canonical wire is the original address. -/
theorem toWire_value (a : Adrs) (h : a.isCanonical = true) :
    (toWire a h).value = a := by
  exact fromVector_toVector_of_isCanonical a h

/-- SHA-2 compression additionally requires that layer and tree fit the narrower ADRSc fields. -/
def compressSha2Checked (a : Adrs) : Except CodecError (Bytes 22) :=
  if !a.isCanonical then
    .error .noncanonicalAddress
  else if !Fits 1 a.layer then
    .error (.outOfRange 1 a.layer)
  else if !Fits 8 a.tree then
    .error (.outOfRange 8 a.tree)
  else
    .ok ⟨a.compressSha2.toArray, by simp⟩

end Adrs

end SLHDSA
