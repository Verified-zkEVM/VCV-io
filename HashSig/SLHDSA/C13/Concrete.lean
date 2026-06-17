/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.C13.Scheme
import HashSig.SLHDSA.Concrete.Keccak
import HashSig.SLHDSA.Concrete.Instance

/-!
# Concrete C13 instantiation (keccak256, 32-byte ADRS)

Wires pure-Lean `keccak256` into the C13 abstract bundle, following `SPHINCs-C13Asm.sol`:

- node/seed type `Y = Bytes 16`; every 16-byte value is **top-aligned** in a 32-byte EVM word
  (`nodeWord v = v ‖ 0^16`);
- the **uncompressed 32-byte ADRS** (`Adrs.toBytes`, *not* the 22-byte SHA-2 `ADRSc`);
- `F`/`H`/`T_ℓ`/`PRF` = `keccak256(seed32 ‖ ADRS32 ‖ payload)` truncated to the **top** 16 bytes;
- `H_msg = keccak256(PK.seed ‖ PK.root ‖ R ‖ message ‖ 0xFF·32)` as the full 256-bit integer;
- `H_wots = keccak256(PK.seed ‖ ADRS32 ‖ node ‖ counter)` as the 256-bit integer, counter in the
  top 4 bytes of its word.

A fixed-width decoder for the 3688-byte C13 signature and an executable `verifyBytes` are
provided for byte-exact KAT checks against the on-chain verifier.
-/


namespace SLHDSA.C13.Concrete

open SLHDSA (Adrs toInt)
open SLHDSA.Concrete (b16ToBA baToBytes baSliceToB16)
open SLHDSA.Concrete.Keccak (keccak256)

/-- 16 zero bytes (the low half of a top-aligned word). -/
def zeros16 : ByteArray := ByteArray.mk (Array.replicate 16 0)

/-- A 16-byte value top-aligned in a 32-byte EVM word. -/
def nodeWord (v : Bytes 16) : ByteArray := b16ToBA v ++ zeros16

/-- The 32-byte uncompressed ADRS. -/
def adrs32 (a : Adrs) : ByteArray := ByteArray.mk a.toBytes.toArray

/-- Top 16 bytes of a keccak digest (the `N_MASK` truncation). -/
def top16 (ba : ByteArray) : Bytes 16 := baToBytes ba 16

/-- A keccak digest read as a big-endian 256-bit integer. -/
def toInt256 (ba : ByteArray) : ℕ := toInt ba.toList

/-- 32 bytes of `0xFF` (the `H_msg` domain separator). -/
def ffWord : ByteArray := ByteArray.mk (Array.replicate 32 0xFF)

/-- The counter as a 32-byte big-endian word (`to_b32(count)`): the 32-bit value occupies the
**low** 4 bytes, the top 28 bytes are zero. -/
def countWord (c : ℕ) : ByteArray :=
  ByteArray.mk ((List.replicate 28 0) ++ SLHDSA.Adrs.toBytesBE c 4).toArray

/-! ### keccak256 tweakable hashes -/

def kF (pkSeed : Bytes 16) (adrs : Adrs) (y : Bytes 16) : Bytes 16 :=
  top16 (keccak256 (nodeWord pkSeed ++ adrs32 adrs ++ nodeWord y))

def kH (pkSeed : Bytes 16) (adrs : Adrs) (l r : Bytes 16) : Bytes 16 :=
  top16 (keccak256 (nodeWord pkSeed ++ adrs32 adrs ++ nodeWord l ++ nodeWord r))

def kTl (pkSeed : Bytes 16) (adrs : Adrs) (ys : List (Bytes 16)) : Bytes 16 :=
  top16 (keccak256 (ys.foldl (fun acc y => acc ++ nodeWord y) (nodeWord pkSeed ++ adrs32 adrs)))

def kPRF (_pkSeed : Bytes 16) (skSeed : Bytes 16) (adrs : Adrs) : Bytes 16 :=
  top16 (keccak256 (nodeWord skSeed ++ adrs32 adrs))

def kPRFmsg (skPrf : Bytes 16) (optrand : Bytes 16) (msg : List Byte) : Bytes 16 :=
  top16 (keccak256 (nodeWord skPrf ++ nodeWord optrand ++ ByteArray.mk msg.toArray))

/-- `H_msg = keccak256(PK.seed ‖ PK.root ‖ R ‖ message ‖ 0xFF·32)` as a 256-bit integer.
`message` is taken as a 32-byte word. -/
def kHmsg (R : Bytes 16) (pkSeed : Bytes 16) (pkRoot : Bytes 16) (msg : List Byte) : ℕ :=
  toInt256 (keccak256 (nodeWord pkSeed ++ nodeWord pkRoot ++ nodeWord R ++
    ByteArray.mk msg.toArray ++ ffWord))

/-- `H_wots = keccak256(PK.seed ‖ ADRS32 ‖ node ‖ counter)` as a 256-bit integer. -/
def kHwots (pkSeed : Bytes 16) (adrs : Adrs) (node : Bytes 16) (count : ℕ) : ℕ :=
  toInt256 (keccak256 (nodeWord pkSeed ++ adrs32 adrs ++ nodeWord node ++ countWord count))

/-- The concrete C13 primitive bundle. -/
def keccakPrimitives : Primitives where
  PkSeed := Bytes 16
  SkSeed := Bytes 16
  SkPrf := Bytes 16
  Y := Bytes 16
  F := kF
  H := kH
  Tl := kTl
  PRF := kPRF
  PRFmsg := kPRFmsg
  Hmsg := kHmsg
  Hwots := kHwots

/-! ### Fixed-width signature decoding (3688-byte C13 wire format) -/

/-- Decode the 3688-byte C13 signature `R ‖ FORS+C ‖ HT` (FORS+C: `k` leaf secrets then `k−1`
auth paths; HT: per layer `WOTS(l·n) ‖ counter(4) ‖ auth(h'·n)`). -/
def decodeSignature (ba : ByteArray) : Signature keccakPrimitives :=
  let R : Bytes 16 := baSliceToB16 ba 0
  let fors : Vector (Bytes 16 × List (Bytes 16)) 7 :=
    Vector.ofFn fun i : Fin 7 =>
      (baSliceToB16 ba (16 + i.val * 16),
        if i.val < 6 then (List.range 19).map fun j => baSliceToB16 ba (128 + i.val * 304 + j * 16)
        else [])
  let layer (off : ℕ) : XmssSig keccakPrimitives :=
    (Vector.ofFn fun i : Fin 43 => baSliceToB16 ba (off + i.val * 16),
      toInt ((ba.extract (off + 688) (off + 692)).toList),
      (List.range 11).map fun j => baSliceToB16 ba (off + 692 + j * 16))
  (R, fors, (layer 1952, layer 2820))

/-- Concrete C13 verification of a decoded reference signature. -/
def verifyBytes (pkSeed pkRoot : Bytes 16) (msg : List Byte) (sigBytes : ByteArray) : Bool :=
  letI : DecidableEq keccakPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 16))
  slhVerifyInternal keccakPrimitives msg (decodeSignature sigBytes) ⟨pkSeed, pkRoot⟩

end SLHDSA.C13.Concrete
