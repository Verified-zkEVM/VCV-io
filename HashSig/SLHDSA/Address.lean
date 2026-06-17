/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Params

/-!
# SLH-DSA Addresses (ADRS)

The 32-byte hash address `ADRS` of FIPS 205 §4.2, used as the per-call tweak of every SLH-DSA
tweakable hash. Conceptually `ADRS` is eight 32-bit words: `layer ‖ tree ‖ type ‖ w₁ ‖ w₂ ‖ w₃`
(the `tree` field spanning words 1–3, i.e. 12 bytes / 96 bits; the final three words are
type-dependent). We model it as a record of its fields rather than a raw byte vector: the member
functions of FIPS 205 Table 1 then become plain field updates with `rfl`-level roundtrip lemmas,
and the address stays opaque to the verified core (it enters only as the hash tweak).

Two type-dependent words alias by name exactly as in FIPS 205:
`setChainAddress = setTreeHeight` (word 2) and `setHashAddress = setTreeIndex` (word 3).

`toBytes` / `compressSha2` give the canonical 32-byte serialization and the 22-byte SHA-2
`ADRSc` compression (§11.2.1) as byte lists, for use by a future concrete hashing layer; the
proof-level development never unfolds them.

## References

- NIST FIPS 205, §4.2 (ADRS), Table 1 (member functions), §11.2.1 (ADRSc compression)
-/


namespace SLHDSA

/-- The seven SLH-DSA address types (FIPS 205 §4.2). -/
inductive AddrType where
  | wotsHash | wotsPk | tree | forsTree | forsRoots | wotsPrf | forsPrf
deriving Repr, DecidableEq, Inhabited

/-- The numeric type code written into the ADRS `type` word. -/
def AddrType.toCode : AddrType → ℕ
  | .wotsHash => 0
  | .wotsPk => 1
  | .tree => 2
  | .forsTree => 3
  | .forsRoots => 4
  | .wotsPrf => 5
  | .forsPrf => 6

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

/-- The all-zero address (`toByte(0, 32)`). -/
def zero : Adrs := ⟨0, 0, 0, 0, 0, 0⟩

/-- `ADRS.setLayerAddress(l)`. -/
def setLayerAddress (a : Adrs) (l : ℕ) : Adrs := { a with layer := l }

/-- `ADRS.setTreeAddress(t)`. -/
def setTreeAddress (a : Adrs) (t : ℕ) : Adrs := { a with tree := t }

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

/-! ### Byte serialization (for the future concrete hashing layer) -/

/-- Big-endian `len`-byte serialization of a natural number (`toByte(x, len)`, FIPS 205 Alg 3),
as a byte list. -/
def toBytesBE (x len : ℕ) : List Byte :=
  (List.range len).map (fun i => UInt8.ofNat (x / 256 ^ (len - 1 - i) % 256))

/-- The canonical 32-byte ADRS serialization:
`layer(4) ‖ tree(12) ‖ type(4) ‖ w₁(4) ‖ w₂(4) ‖ w₃(4)`. -/
def toBytes (a : Adrs) : List Byte :=
  toBytesBE a.layer 4 ++ toBytesBE a.tree 12 ++ toBytesBE a.type 4 ++
    toBytesBE a.word1 4 ++ toBytesBE a.word2 4 ++ toBytesBE a.word3 4

/-- The 22-byte SHA-2 compressed address `ADRSc` (FIPS 205 §11.2.1):
`layer[low byte](1) ‖ tree[low 8 bytes](8) ‖ type[low byte](1) ‖ w₁(4) ‖ w₂(4) ‖ w₃(4)`. -/
def compressSha2 (a : Adrs) : List Byte :=
  toBytesBE a.layer 1 ++ toBytesBE a.tree 8 ++ toBytesBE a.type 1 ++
    toBytesBE a.word1 4 ++ toBytesBE a.word2 4 ++ toBytesBE a.word3 4

end Adrs

end SLHDSA
