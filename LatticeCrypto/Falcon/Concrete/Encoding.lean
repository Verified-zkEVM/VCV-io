/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Batteries.Data.ByteArray
public import Batteries.Data.Array.Lemmas
public import LatticeCrypto.Falcon.Arithmetic

/-!
# Concrete Falcon Encoding

Executable compress/decompress for Falcon signature polynomials (Golomb-Rice style),
plus 14-bit public key encoding/decoding for `q = 12289`.

## Signature Compression (comp_encode / comp_decode)

Each coefficient `x` with `|x| ≤ 2047` is encoded as:
- 1 sign bit (0 = positive, 1 = negative)
- 7 low bits of `|x|`
- unary-coded high bits: `(|x| >> 7)` zero bits followed by a `1` bit

This is a variable-length code: small coefficients use ~9 bits, larger ones up to ~24 bits.

## Public Key Encoding

Each coefficient of `h ∈ R_q` takes exactly 14 bits (since `q = 12289 < 2^14`),
packed 4 coefficients into 7 bytes.

## Round-trip theorems

`sigDecode_sigEncode` recovers the salt and the compressed payload of any nonempty encoded
signature, `publicKeyBytes_extract` strips the one-byte public-key header back to the packed
coefficients, and `pkDecode_pkEncode` recovers the polynomial from its packed encoding whenever
`4 ∣ n`, the case of every Falcon degree. These are what the concrete verifier's agreement with
the abstract one (`Falcon.Concrete.FPRBridge.concrete_verify_eq_verify`) needs from the codec.

## References

- c-fn-dsa: `codec.c` (comp_encode, comp_decode, mqpoly_encode, mqpoly_decode)
- Falcon specification v1.2, Section 3.12 (Algorithms 17–18)
-/

public section


namespace Falcon.Concrete

open Falcon

/-! ## Signature compression -/

/-- Compress a Falcon signature polynomial into at most `dlen` bytes. -/
def compress (n : ℕ) (s : IntPoly n) (dlen : ℕ) : Option (List UInt8) := Id.run do
  let mut acc : UInt32 := 0
  let mut accLen : UInt32 := 0
  let mut out : Array UInt8 := #[]
  for i in [0:n] do
    let x : Int := s[i]!
    if x < -2047 || x > 2047 then
      return none
    let sw : UInt32 := if x < 0 then 0xFFFFFFFF else 0
    let w : UInt32 := x.natAbs.toUInt32
    acc := (acc <<< 8) ||| ((sw &&& 0x80) ||| (w &&& 0x7F))
    accLen := accLen + 8
    let wh := (w >>> 7).toNat + 1
    acc := (acc <<< wh.toUInt32) ||| 1
    accLen := accLen + wh.toUInt32
    while accLen ≥ 8 do
      accLen := accLen - 8
      if out.size ≥ dlen then
        return none
      out := out.push (acc >>> accLen).toUInt8
  if accLen > 0 then
    if out.size ≥ dlen then
      return none
    out := out.push (acc <<< (8 - accLen)).toUInt8
  while out.size < dlen do
    out := out.push 0
  return some out.toList

/-- Decompress a fixed-length Falcon signature polynomial.

`compress` pads every successful output to exactly `dlen` bytes. Accordingly, this decoder
accepts exactly that length; the optional unpadded Falcon representation is outside its format. -/
def decompress (n : ℕ) (d : List UInt8) (dlen : ℕ) : Option (IntPoly n) := Id.run do
  if d.length ≠ dlen then return none
  let bytes := d.toArray
  let mut acc : UInt32 := 0
  let mut accLen : UInt32 := 0
  let mut j := 0
  let mut result : Array ℤ := Array.replicate n 0
  for i in [0:n] do
    if j ≥ dlen then return none
    acc := (acc <<< 8) ||| bytes[j]!.toUInt32
    j := j + 1
    let full := acc >>> accLen
    let t := (full >>> 7) &&& 1
    let mut m : UInt32 := full &&& 0x7F
    let mut done := false
    while !done do
      if accLen == 0 then
        if j ≥ dlen then return none
        acc := (acc <<< 8) ||| bytes[j]!.toUInt32
        j := j + 1
        accLen := 8
      accLen := accLen - 1
      if ((acc >>> accLen) &&& 1) != 0 then
        done := true
      else
        m := m + 0x80
        if m > 2047 then return none
    if m == 0 && t != 0 then return none
    let val : UInt32 := (m ^^^ (0 - t)) + t
    let signedVal : ℤ :=
      if val &&& 0x80000000 != 0 then -(((~~~val) + 1).toNat : ℤ)
      else (val.toNat : ℤ)
    result := result.set! i signedVal
  if accLen > 0 then
    if (acc &&& ((1 <<< accLen) - 1)) != 0 then
      return none
  while j < dlen do
    if bytes[j]! != 0 then return none
    j := j + 1
  return some (Vector.ofFn fun ⟨i, _⟩ => result.getD i 0)

@[simp] theorem decompress_eq_none_of_length_ne (n d dlen) (h : d.length ≠ dlen) :
    decompress n d dlen = none := by
  simp [decompress, h]

/-! ## Public key encoding (14 bits per coefficient) -/

/-- The FN-DSA public-key header byte for a given `logn`. -/
@[inline] def publicKeyHeader (logn : Nat) : UInt8 :=
  (0x00 + logn).toUInt8

/-- Encode a Falcon public key polynomial using the packed 14-bit coefficient format. -/
def pkEncode (n : ℕ) (h : Rq n) : ByteArray := Id.run do
  if n % 4 != 0 then
    panic! s!"Falcon public-key encoding requires n divisible by 4, got {n}"
  let mut out := ByteArray.empty
  for b in [0:n / 4] do
    let i := 4 * b
    let h0 := (h[i]!).val
    let h1 := (h[i+1]!).val
    let h2 := (h[i+2]!).val
    let h3 := (h[i+3]!).val
    out := out.push (h0 >>> 6).toUInt8
    out := out.push ((h0 <<< 2) ||| (h1 >>> 12)).toUInt8
    out := out.push (h1 >>> 4).toUInt8
    out := out.push ((h1 <<< 4) ||| (h2 >>> 10)).toUInt8
    out := out.push (h2 >>> 2).toUInt8
    out := out.push ((h2 <<< 6) ||| (h3 >>> 8)).toUInt8
    out := out.push h3.toUInt8
  return out

/-- Decode a Falcon public key polynomial from the packed 14-bit coefficient format. -/
def pkDecode (n : ℕ) (d : ByteArray) : Option (Rq n) := Id.run do
  if n % 4 != 0 then return none
  let needed := 7 * n / 4
  if d.size < needed then return none
  let mut result : Array Coeff := Array.replicate n 0
  for b in [0:n / 4] do
    let i := 4 * b
    let j := 7 * b
    let d0 := d[j]!.toNat
    let d1 := d[j+1]!.toNat
    let d2 := d[j+2]!.toNat
    let d3 := d[j+3]!.toNat
    let d4 := d[j+4]!.toNat
    let d5 := d[j+5]!.toNat
    let d6 := d[j+6]!.toNat
    let h0 := (d0 <<< 6) ||| (d1 >>> 2)
    let h1 := ((d1 <<< 12) ||| (d2 <<< 4) ||| (d3 >>> 4)) &&& 0x3FFF
    let h2 := ((d3 <<< 10) ||| (d4 <<< 2) ||| (d5 >>> 6)) &&& 0x3FFF
    let h3 := ((d5 <<< 8) ||| d6) &&& 0x3FFF
    if h0 ≥ modulus || h1 ≥ modulus || h2 ≥ modulus || h3 ≥ modulus then
      return none
    result := result.set! i (h0 : Coeff)
    result := result.set! (i+1) (h1 : Coeff)
    result := result.set! (i+2) (h2 : Coeff)
    result := result.set! (i+3) (h3 : Coeff)
  return some (Vector.ofFn fun ⟨i, _⟩ => result.getD i 0)

/-- External public-key bytes used by FN-DSA verification and raw-message hashing:
one header byte followed by the packed 14-bit coefficient encoding. -/
def publicKeyBytes (logn : Nat) {n : ℕ} (h : Rq n) : ByteArray :=
  ByteArray.mk #[publicKeyHeader logn] ++ pkEncode n h

/-! ## Public key codec round-trip

The packing identity is per-group: four 14-bit coefficients pack into seven bytes and unpack
back to the same four values. `group_roundtrip` certifies the bit-twiddling identity, `gblock`
isolates the seven bytes of one group, and `E` reconstructs the encoder output as a foldl whose
per-byte values are characterized by `E_getElem` + `gblock_byte`. `pkDecode_pkEncode` then runs
the decoder loop invariant against those bytes, using `group_roundtrip` (and `ZMod.val_lt`) to
rule out the `≥ modulus` reject branch. -/

private theorem toU8 (a : Nat) : a.toUInt8.toNat = a % 256 := by
  simp [Nat.toUInt8, Nat.toUInt8.eq_1]

private theorem lor_add (a b k : Nat) (hb : b < 2 ^ k) (hd : 2 ^ k ∣ a) : a ||| b = a + b := by
  obtain ⟨c, rfl⟩ := hd
  rw [mul_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq, mul_comm]

private theorem and3fff (a : Nat) : a &&& 0x3FFF = a % 2^14 := by
  have := Nat.and_two_pow_sub_one_eq_mod a 14
  norm_num at this ⊢; exact this

set_option maxHeartbeats 1000000 in
-- The four bit-packing identities are discharged by a single `omega`/`norm_num` sweep over the
-- expanded shift/mask arithmetic, which exceeds the default heartbeat budget.
private theorem group_roundtrip (c0 c1 c2 c3 : Nat)
    (b0 : c0 < modulus) (b1 : c1 < modulus) (b2 : c2 < modulus) (b3 : c3 < modulus) :
    let d0 := (c0 >>> 6).toUInt8.toNat
    let d1 := ((c0 <<< 2) ||| (c1 >>> 12)).toUInt8.toNat
    let d2 := (c1 >>> 4).toUInt8.toNat
    let d3 := ((c1 <<< 4) ||| (c2 >>> 10)).toUInt8.toNat
    let d4 := (c2 >>> 2).toUInt8.toNat
    let d5 := ((c2 <<< 6) ||| (c3 >>> 8)).toUInt8.toNat
    let d6 := c3.toUInt8.toNat
    ((d0 <<< 6) ||| (d1 >>> 2)) = c0 ∧
    (((d1 <<< 12) ||| (d2 <<< 4) ||| (d3 >>> 4)) &&& 0x3FFF) = c1 ∧
    (((d3 <<< 10) ||| (d4 <<< 2) ||| (d5 >>> 6)) &&& 0x3FFF) = c2 ∧
    (((d5 <<< 8) ||| d6) &&& 0x3FFF) = c3 := by
  simp only [modulus] at b0 b1 b2 b3
  intro d0 d1 d2 d3 d4 d5 d6
  have hd0 : d0 = c0 / 64 := by
    change (c0 >>> 6).toUInt8.toNat = _; rw [toU8, Nat.shiftRight_eq_div_pow]; norm_num; omega
  have hd1 : d1 = (c0 * 4 + c1 / 4096) % 256 := by
    change ((c0 <<< 2) ||| (c1 >>> 12)).toUInt8.toNat = _
    rw [toU8, lor_add _ _ 2 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨c0, by rw [Nat.shiftLeft_eq]; ring⟩, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hd2 : d2 = (c1 / 16) % 256 := by
    change (c1 >>> 4).toUInt8.toNat = _; rw [toU8, Nat.shiftRight_eq_div_pow]
  have hd3 : d3 = (c1 * 16 + c2 / 1024) % 256 := by
    change ((c1 <<< 4) ||| (c2 >>> 10)).toUInt8.toNat = _
    rw [toU8, lor_add _ _ 4 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨c1, by rw [Nat.shiftLeft_eq]; ring⟩, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hd4 : d4 = (c2 / 4) % 256 := by
    change (c2 >>> 2).toUInt8.toNat = _; rw [toU8, Nat.shiftRight_eq_div_pow]
  have hd5 : d5 = (c2 * 64 + c3 / 256) % 256 := by
    change ((c2 <<< 6) ||| (c3 >>> 8)).toUInt8.toNat = _
    rw [toU8, lor_add _ _ 6 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨c2, by rw [Nat.shiftLeft_eq]; ring⟩, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hd6 : d6 = c3 % 256 := by change c3.toUInt8.toNat = _; rw [toU8]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd0, hd1, lor_add _ _ 6 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨c0/64, by rw [Nat.shiftLeft_eq]; ring⟩, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    norm_num; omega
  · set e1 := (c0 * 4 + c1 / 4096) % 256 with he1
    set e2 := (c1 / 16) % 256 with he2
    set e3 := (c1 * 16 + c2 / 1024) % 256 with he3
    rw [hd1, hd2, hd3,
      lor_add (e1 <<< 12) (e2 <<< 4) 12 (by rw [Nat.shiftLeft_eq]; show e2 * 2^4 < 2^12; omega)
        ⟨e1, by rw [Nat.shiftLeft_eq]; ring⟩,
      lor_add (e1 <<< 12 + e2 <<< 4) (e3 >>> 4) 4 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨e1 * 2^8 + e2, by rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]; ring⟩,
      and3fff, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    simp only [he1, he2, he3]; norm_num; omega
  · set e3 := (c1 * 16 + c2 / 1024) % 256 with he3
    set e4 := (c2 / 4) % 256 with he4
    set e5 := (c2 * 64 + c3 / 256) % 256 with he5
    rw [hd3, hd4, hd5,
      lor_add (e3 <<< 10) (e4 <<< 2) 10 (by rw [Nat.shiftLeft_eq]; show e4 * 2^2 < 2^10; omega)
        ⟨e3, by rw [Nat.shiftLeft_eq]; ring⟩,
      lor_add (e3 <<< 10 + e4 <<< 2) (e5 >>> 6) 2 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨e3 * 2^8 + e4, by rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]; ring⟩,
      and3fff, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    simp only [he3, he4, he5]; norm_num; omega
  · rw [hd5, hd6, lor_add _ _ 8 (by omega) ⟨_, by rw [Nat.shiftLeft_eq]; ring⟩, and3fff,
      Nat.shiftLeft_eq]
    norm_num; omega

private def gblock (n : ℕ) (h : Rq n) (b : ℕ) : ByteArray :=
  let i := 4 * b
  let h0 := (h[i]!).val
  let h1 := (h[i+1]!).val
  let h2 := (h[i+2]!).val
  let h3 := (h[i+3]!).val
  ByteArray.mk #[ (h0 >>> 6).toUInt8, ((h0 <<< 2) ||| (h1 >>> 12)).toUInt8, (h1 >>> 4).toUInt8,
     ((h1 <<< 4) ||| (h2 >>> 10)).toUInt8, (h2 >>> 2).toUInt8,
     ((h2 <<< 6) ||| (h3 >>> 8)).toUInt8, h3.toUInt8 ]

private def encStep (n : ℕ) (h : Rq n) (out : ByteArray) (b : ℕ) : ByteArray :=
  let i := 4 * b
  let h0 := (h[i]!).val
  let h1 := (h[i+1]!).val
  let h2 := (h[i+2]!).val
  let h3 := (h[i+3]!).val
  ((((((out.push ((h0 >>> 6).toUInt8)).push (((h0 <<< 2) ||| (h1 >>> 12)).toUInt8)).push
    ((h1 >>> 4).toUInt8)).push (((h1 <<< 4) ||| (h2 >>> 10)).toUInt8)).push
    ((h2 >>> 2).toUInt8)).push (((h2 <<< 6) ||| (h3 >>> 8)).toUInt8)).push (h3.toUInt8)

private theorem gblock_size (n : ℕ) (h : Rq n) (b : ℕ) : (gblock n h b).size = 7 := rfl
private theorem gblock_data_size (n : ℕ) (h : Rq n) (b : ℕ) : (gblock n h b).data.size = 7 := rfl

private theorem encStep_eq_append (n : ℕ) (h : Rq n) (out : ByteArray) (b : ℕ) :
    encStep n h out b = out ++ gblock n h b := by
  apply ByteArray.ext
  simp only [encStep, gblock, ByteArray.data_push, ByteArray.data_append]
  rfl

private theorem encStep_size (n : ℕ) (h : Rq n) (out : ByteArray) (b : ℕ) :
    (encStep n h out b).size = out.size + 7 := by
  rw [encStep_eq_append, ByteArray.size_append, gblock_size]

private def E (n : ℕ) (h : Rq n) (m : ℕ) : ByteArray :=
  List.foldl (encStep n h) ByteArray.empty (List.range' 0 m)

private theorem E_succ (n : ℕ) (h : Rq n) (m : ℕ) :
    E n h (m+1) = encStep n h (E n h m) m := by
  simp only [E, List.range'_concat, List.foldl_concat]
  norm_num

private theorem E_size (n : ℕ) (h : Rq n) (m : ℕ) : (E n h m).size = 7 * m := by
  induction m with
  | zero => rfl
  | succ k ih => rw [E_succ, encStep_size, ih]; ring

private theorem E_getElem (n : ℕ) (h : Rq n) (m : ℕ) :
    ∀ b, b < m → ∀ t, t < 7 → (E n h m).data[7 * b + t]! = (gblock n h b).data[t]! := by
  induction m with
  | zero => intro b hb; omega
  | succ k ih =>
    intro b hb t ht
    rw [E_succ, encStep_eq_append, ByteArray.data_append]
    rcases Nat.lt_or_ge b k with hbk | hbk
    · -- b < k : append_left into E k
      have hlt : 7 * b + t < (E n h k).data.size := by
        rw [← ByteArray.size, E_size]; omega
      rw [getElem!_pos _ (7*b+t) (by rw [Array.size_append]; omega),
          Array.getElem_append_left hlt, ← getElem!_pos _ (7*b+t) hlt]
      exact ih b hbk t ht
    · -- b = k
      have hbeq : b = k := by omega
      subst hbeq
      have hsz : (E n h b).data.size = 7 * b := by rw [← ByteArray.size, E_size]
      have hidx : 7 * b + t = (E n h b).data.size + t := by rw [hsz]
      rw [hidx,
          getElem!_pos _ ((E n h b).data.size + t)
            (by rw [Array.size_append, gblock_data_size]; omega),
          getElem!_pos (gblock n h b).data t (by rw [gblock_data_size]; exact ht),
          Array.getElem_append_right (by omega)]
      congr 1
      omega

private theorem pkEncode_eq_E (n : ℕ) (h : Rq n) (hn : n % 4 = 0) :
    pkEncode n h = E n h (n / 4) := by
  unfold pkEncode E
  have hb : (n % 4 != 0) = false := by simp [hn]
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.div_one, Nat.add_sub_cancel, hb, Bool.false_eq_true, if_false]
  simp only [List.forIn_pure_yield_eq_foldl, bind_pure]
  rfl

-- explicit bytes of gblock
private theorem gblock_byte (n : ℕ) (h : Rq n) (b : ℕ) :
    let i := 4 * b
    let c0 := (h[i]!).val; let c1 := (h[i+1]!).val
    let c2 := (h[i+2]!).val; let c3 := (h[i+3]!).val
    (gblock n h b).data[0]! = (c0 >>> 6).toUInt8 ∧
    (gblock n h b).data[1]! = ((c0 <<< 2) ||| (c1 >>> 12)).toUInt8 ∧
    (gblock n h b).data[2]! = (c1 >>> 4).toUInt8 ∧
    (gblock n h b).data[3]! = ((c1 <<< 4) ||| (c2 >>> 10)).toUInt8 ∧
    (gblock n h b).data[4]! = (c2 >>> 2).toUInt8 ∧
    (gblock n h b).data[5]! = ((c2 <<< 6) ||| (c3 >>> 8)).toUInt8 ∧
    (gblock n h b).data[6]! = c3.toUInt8 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem pkEncode_size (n : ℕ) (h : Rq n) (hn4 : n % 4 = 0) :
    (pkEncode n h).size = 7 * (n / 4) := by
  rw [pkEncode_eq_E n h hn4, E_size]

/-! ## Full signature encoding/decoding -/

/-- Encode a Falcon signature as header, salt, and compressed `s₂` bytes. -/
def sigEncode (salt : Bytes 40) (compSig : List UInt8) (logn : ℕ) : ByteArray :=
  let header : UInt8 := (0x30 + logn).toUInt8
  let saltBA := ByteArray.mk salt.toArray
  let compBA := ByteArray.mk compSig.toArray
  ByteArray.mk #[header] ++ saltBA ++ compBA

/-- Decode a Falcon signature into its salt and compressed `s₂` bytes. -/
def sigDecode (d : ByteArray) (logn : ℕ) : Option (Bytes 40 × List UInt8) := Id.run do
  if d.size < 42 then return none
  let header := d[0]!
  if header != (0x30 + logn).toUInt8 then return none
  let salt : Bytes 40 := Vector.ofFn fun ⟨i, _⟩ => d[i + 1]!
  let comp := (d.extract 41 d.size).toList
  return some (salt, comp)

@[simp] theorem sigDecode_sigEncode_nil (salt : Bytes 40) (logn : ℕ) :
    sigDecode (sigEncode salt [] logn) logn = none := by
  cases salt with
  | mk xs hxs =>
      have hsalt : ({ data := xs } : ByteArray).size = 40 := by
        change xs.size = 40
        exact hxs
      have hone : ({ data := #[48 + UInt8.ofNat logn] } : ByteArray).size = 1 := rfl
      have hempty : ({ data := #[] } : ByteArray).size = 0 := rfl
      simp [sigDecode, sigEncode, hsalt, hone, hempty]

/-- The accumulator loop underlying `ByteArray.toList` reverses its accumulator onto the
remaining bytes, so the full traversal recovers the underlying array as a list. -/
private theorem toList_loop_eq (a : ByteArray) :
    ∀ i (acc : List UInt8), ByteArray.toList.loop a i acc
      = acc.reverse ++ (a.data.toList.drop i) := by
  intro i acc
  fun_induction ByteArray.toList.loop a i acc with
  | case1 i acc h ih =>
      rw [ih]
      have hi : i < a.data.toList.length := by rw [Array.length_toList]; exact h
      rw [List.drop_eq_getElem_cons hi]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      congr 2
      cases a with
      | mk bs =>
        change bs[i]! = _
        rw [getElem!_pos bs i (show i < bs.size from h), Array.getElem_toList]
  | case2 i acc h =>
      have : a.data.toList.length ≤ i := by
        rw [Array.length_toList]; exact Nat.le_of_not_lt h
      rw [List.drop_eq_nil_of_le this]; simp

/-- `ByteArray.toList` agrees with the list of the underlying data array. -/
private theorem byteArray_toList_eq (a : ByteArray) : a.toList = a.data.toList := by
  rw [ByteArray.toList, toList_loop_eq]; simp

/-- `ByteArray` `getElem!` agrees with the underlying data array's `getElem!`. -/
private theorem byteArray_getElem!_data (a : ByteArray) (i : ℕ) : a[i]! = a.data[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi, getElem!_pos a.data i (by rwa [← ByteArray.size])]
    rfl
  · rw [getElem!_neg a i hi, getElem!_neg a.data i (by rwa [← ByteArray.size])]

/-- Round-trip: decoding an encoded signature recovers the original salt and compressed bytes.
A nonempty compressed payload guarantees the encoded length passes the `42`-byte minimum check,
so the header, salt, and payload segments all decode back to their inputs. -/
theorem sigDecode_sigEncode (salt : Bytes 40) (compSig : List UInt8) (logn : ℕ)
    (hne : compSig ≠ []) :
    sigDecode (sigEncode salt compSig logn) logn = some (salt, compSig) := by
  have hlen : 1 ≤ compSig.length := by
    rw [Nat.one_le_iff_ne_zero, ne_eq, List.length_eq_zero_iff]; exact hne
  set hdr : UInt8 := (0x30 + logn).toUInt8 with hhdr
  have hb1 : (ByteArray.mk #[hdr]).size = 1 := rfl
  have hss : (ByteArray.mk salt.toArray).size = 40 := by change salt.toArray.size = 40; simp
  have hcs : (ByteArray.mk compSig.toArray).size = compSig.length := by
    change compSig.toArray.size = compSig.length; simp
  have hesize : (sigEncode salt compSig logn).size = 41 + compSig.length := by
    change (ByteArray.mk #[hdr] ++ ByteArray.mk salt.toArray ++ ByteArray.mk compSig.toArray).size
        = 41 + compSig.length
    rw [ByteArray.size_append, ByteArray.size_append, hb1, hss, hcs]
  have hguard : ¬ (sigEncode salt compSig logn).size < 42 := by rw [hesize]; omega
  have hdata : (sigEncode salt compSig logn).data = #[hdr] ++ salt.toArray ++ compSig.toArray := by
    simp only [sigEncode, ByteArray.data_append, hhdr]
  have hhead : (sigEncode salt compSig logn)[0]! = hdr := by
    rw [byteArray_getElem!_data, hdata, getElem!_pos _ 0 (by simp),
      Array.getElem_append_left (by simp), Array.getElem_append_left (by simp)]
    rfl
  have hsalt : (Vector.ofFn fun (i : Fin 40) => (sigEncode salt compSig logn)[i.val + 1]!)
      = salt := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_ofFn, byteArray_getElem!_data, hdata,
      getElem!_pos _ (i + 1) (by simp; omega), Array.getElem_append_left (by simp; omega),
      Array.getElem_append_right (by simp)]
    simp [Vector.getElem_toArray]
  have hcomp : ((sigEncode salt compSig logn).extract 41
      (sigEncode salt compSig logn).size).toList = compSig := by
    rw [hesize]
    change ((ByteArray.mk #[hdr] ++ ByteArray.mk salt.toArray
        ++ ByteArray.mk compSig.toArray).extract 41 (41 + compSig.length)).toList = compSig
    rw [ByteArray.extract_append_eq_right
      (a := ByteArray.mk #[hdr] ++ ByteArray.mk salt.toArray) (b := ByteArray.mk compSig.toArray)
      (by rw [ByteArray.size_append, hb1, hss]) (by rw [ByteArray.size_append, hb1, hss, hcs])]
    rw [byteArray_toList_eq]
  unfold sigDecode
  simp only [Id.run, hguard, hhead, hhdr, if_false, bne_self_eq_false, Bool.false_eq_true,
    hsalt, hcomp]
  rfl

/-! ### Public key decode round-trip -/

/-- The seven bytes of `pkEncode n h` at group `b` are exactly the bytes of `gblock n h b`. -/
private theorem pkEncode_group_byte (n : ℕ) (h : Rq n) (hn4 : n % 4 = 0)
    (b : ℕ) (hb : b < n / 4) (t : ℕ) (ht : t < 7) :
    (pkEncode n h)[7 * b + t]! = (gblock n h b).data[t]! := by
  rw [byteArray_getElem!_data, pkEncode_eq_E n h hn4, E_getElem n h (n / 4) b hb t ht]

/-- Each decoded coefficient of `pkEncode n h` at group `b` recovers `h[4b+s].val`, which is
`< modulus`; hence the decoder's reject branch is never taken. -/
private theorem pkEncode_group_decode (n : ℕ) (h : Rq n) (hn4 : n % 4 = 0)
    (b : ℕ) (hb : b < n / 4) :
    let g := pkEncode n h
    let d0 := g[7 * b]!.toNat
    let d1 := g[7 * b + 1]!.toNat
    let d2 := g[7 * b + 2]!.toNat
    let d3 := g[7 * b + 3]!.toNat
    let d4 := g[7 * b + 4]!.toNat
    let d5 := g[7 * b + 5]!.toNat
    let d6 := g[7 * b + 6]!.toNat
    ((d0 <<< 6) ||| (d1 >>> 2)) = (h[4 * b]!).val ∧
    (((d1 <<< 12) ||| (d2 <<< 4) ||| (d3 >>> 4)) &&& 0x3FFF) = (h[4 * b + 1]!).val ∧
    (((d3 <<< 10) ||| (d4 <<< 2) ||| (d5 >>> 6)) &&& 0x3FFF) = (h[4 * b + 2]!).val ∧
    (((d5 <<< 8) ||| d6) &&& 0x3FFF) = (h[4 * b + 3]!).val := by
  intro g d0 d1 d2 d3 d4 d5 d6
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := gblock_byte n h b
  have hb0 : d0 = ((h[4 * b]!).val >>> 6).toUInt8.toNat := by
    change g[7 * b]!.toNat = _
    rw [show 7 * b = 7 * b + 0 from rfl, pkEncode_group_byte n h hn4 b hb 0 (by omega), e0]
  have hb1 : d1 = (((h[4 * b]!).val <<< 2) ||| ((h[4 * b + 1]!).val >>> 12)).toUInt8.toNat := by
    change g[7 * b + 1]!.toNat = _
    rw [pkEncode_group_byte n h hn4 b hb 1 (by omega), e1]
  have hb2 : d2 = ((h[4 * b + 1]!).val >>> 4).toUInt8.toNat := by
    change g[7 * b + 2]!.toNat = _
    rw [pkEncode_group_byte n h hn4 b hb 2 (by omega), e2]
  have hb3 : d3 = (((h[4 * b + 1]!).val <<< 4) ||| ((h[4 * b + 2]!).val >>> 10)).toUInt8.toNat := by
    change g[7 * b + 3]!.toNat = _
    rw [pkEncode_group_byte n h hn4 b hb 3 (by omega), e3]
  have hb4 : d4 = ((h[4 * b + 2]!).val >>> 2).toUInt8.toNat := by
    change g[7 * b + 4]!.toNat = _
    rw [pkEncode_group_byte n h hn4 b hb 4 (by omega), e4]
  have hb5 : d5 = (((h[4 * b + 2]!).val <<< 6) ||| ((h[4 * b + 3]!).val >>> 8)).toUInt8.toNat := by
    change g[7 * b + 5]!.toNat = _
    rw [pkEncode_group_byte n h hn4 b hb 5 (by omega), e5]
  have hb6 : d6 = (h[4 * b + 3]!).val.toUInt8.toNat := by
    change g[7 * b + 6]!.toNat = _
    rw [pkEncode_group_byte n h hn4 b hb 6 (by omega), e6]
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6]
  exact group_roundtrip _ _ _ _ (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)

/-- Stripping the one-byte public-key header recovers the packed coefficient encoding. -/
theorem publicKeyBytes_extract (logn : Nat) {n : ℕ} (h : Rq n) :
    (publicKeyBytes logn h).extract 1 (publicKeyBytes logn h).size = pkEncode n h := by
  set hdr : UInt8 := publicKeyHeader logn with hhdr
  have hb1 : (ByteArray.mk #[hdr]).size = 1 := rfl
  have hsz : (publicKeyBytes logn h).size = 1 + (pkEncode n h).size := by
    change (ByteArray.mk #[hdr] ++ pkEncode n h).size = 1 + (pkEncode n h).size
    rw [ByteArray.size_append, hb1]
  rw [hsz]
  change (ByteArray.mk #[hdr] ++ pkEncode n h).extract 1 (1 + (pkEncode n h).size) = pkEncode n h
  rw [ByteArray.extract_append_eq_right (a := ByteArray.mk #[hdr]) (b := pkEncode n h)
      (by rw [hb1]) (by rw [hb1])]

/-- The decoded value written at sub-index `s ∈ {0,1,2,3}` of group `b`, as a `Coeff`. -/
private def decVal (g : ByteArray) (b s : ℕ) : Coeff :=
  let d0 := g[7 * b]!.toNat
  let d1 := g[7 * b + 1]!.toNat
  let d2 := g[7 * b + 2]!.toNat
  let d3 := g[7 * b + 3]!.toNat
  let d4 := g[7 * b + 4]!.toNat
  let d5 := g[7 * b + 5]!.toNat
  let d6 := g[7 * b + 6]!.toNat
  match s with
  | 0 => (((d0 <<< 6) ||| (d1 >>> 2) : ℕ) : Coeff)
  | 1 => ((((d1 <<< 12) ||| (d2 <<< 4) ||| (d3 >>> 4)) &&& 0x3FFF : ℕ) : Coeff)
  | 2 => ((((d3 <<< 10) ||| (d4 <<< 2) ||| (d5 >>> 6)) &&& 0x3FFF : ℕ) : Coeff)
  | _ => ((((d5 <<< 8) ||| d6) &&& 0x3FFF : ℕ) : Coeff)

/-- `getD` of `Array.set!` at the same in-bounds index returns the written value. -/
private theorem getD_set!_self' (out : Array Coeff) (k : ℕ) (v : Coeff) (h : k < out.size) :
    (out.set! k v).getD k 0 = v := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]; simp [h]

/-- `getD` of `Array.set!` at a different index is unaffected. -/
private theorem getD_set!_ne' (out : Array Coeff) (k k' : ℕ) (v : Coeff) (h : k ≠ k') :
    (out.set! k v).getD k' 0 = out.getD k' 0 := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]; simp [h]

/-- The decoder loop body (in `Id`) over a single group index. -/
private def decBody (n : ℕ) (g : ByteArray) :
    ℕ → Option (Option (Rq n)) × Array Coeff →
      Id (ForInStep (Option (Option (Rq n)) × Array Coeff)) :=
  fun b r =>
    let d0 := g[7 * b]!.toNat
    let d1 := g[7 * b + 1]!.toNat
    let d2 := g[7 * b + 2]!.toNat
    let d3 := g[7 * b + 3]!.toNat
    let d4 := g[7 * b + 4]!.toNat
    let d5 := g[7 * b + 5]!.toNat
    let d6 := g[7 * b + 6]!.toNat
    let h0 := (d0 <<< 6) ||| (d1 >>> 2)
    let h1 := ((d1 <<< 12) ||| (d2 <<< 4) ||| (d3 >>> 4)) &&& 0x3FFF
    let h2 := ((d3 <<< 10) ||| (d4 <<< 2) ||| (d5 >>> 6)) &&& 0x3FFF
    let h3 := ((d5 <<< 8) ||| d6) &&& 0x3FFF
    if h0 ≥ modulus || h1 ≥ modulus || h2 ≥ modulus || h3 ≥ modulus then
      pure (ForInStep.done (some none, r.2))
    else
      pure (ForInStep.yield (none,
        (((r.2.set! (4 * b) (h0 : Coeff)).set! (4 * b + 1) (h1 : Coeff)).set!
          (4 * b + 2) (h2 : Coeff)).set! (4 * b + 3) (h3 : Coeff)))

/-- The reject predicate for group `b`: at least one of the four decoded coefficients is out of
range. The loop's `done` branch fires exactly when this holds. -/
private def decReject (g : ByteArray) (b : ℕ) : Prop :=
  (g[7 * b]!.toNat <<< 6 ||| g[7 * b + 1]!.toNat >>> 2 ≥ modulus) ∨
  (((g[7 * b + 1]!.toNat <<< 12 ||| g[7 * b + 2]!.toNat <<< 4 |||
     g[7 * b + 3]!.toNat >>> 4) &&& 0x3FFF) ≥ modulus) ∨
  (((g[7 * b + 3]!.toNat <<< 10 ||| g[7 * b + 4]!.toNat <<< 2 |||
     g[7 * b + 5]!.toNat >>> 6) &&& 0x3FFF) ≥ modulus) ∨
  (((g[7 * b + 5]!.toNat <<< 8 ||| g[7 * b + 6]!.toNat) &&& 0x3FFF) ≥ modulus)

/-- The decoder loop invariant: when every visited group decodes in-range, the loop never takes
the reject branch, the status component stays `none`, the result keeps size `n`, every cell of a
visited group holds its decoded value, and cells outside the visited range are preserved. The
statement is generalized over a starting group offset `s` so the standard `range'` cons recursion
applies. -/
private theorem decode_loop_invariant (n : ℕ) (g : ByteArray) :
    ∀ (m s : ℕ) (R0 : Array Coeff), R0.size = n → 4 * (s + m) ≤ n →
      (∀ b, s ≤ b → b < s + m → ¬ decReject g b) →
      ∃ R : Array Coeff,
        forIn (m := Id) (List.range' s m)
            ((none, R0) : Option (Option (Rq n)) × Array Coeff) (decBody n g)
          = ((none, R) : Option (Option (Rq n)) × Array Coeff) ∧
        R.size = n ∧
        (∀ b k', s ≤ b → b < s + m → k' < 4 → R.getD (4 * b + k') 0 = decVal g b k') ∧
        (∀ k, k < 4 * s ∨ 4 * (s + m) ≤ k → R.getD k 0 = R0.getD k 0) := by
  intro m
  induction m with
  | zero =>
    intro s R0 hsz0 _ _
    refine ⟨R0, rfl, hsz0, ?_, ?_⟩
    · intro b k' hb hb2; omega
    · intro k _; rfl
  | succ m ih =>
    intro s R0 hsz0 hbound hrej
    have hrejs : ¬ decReject g s := hrej s (le_refl s) (by omega)
    -- process group s first
    rw [show List.range' s (m + 1) = s :: List.range' (s + 1) m from by
        rw [List.range'_succ]]
    rw [List.forIn_cons]
    -- the body at group s yields (no reject), with updated array R1
    set R1 := (((R0.set! (4 * s) (decVal g s 0)).set! (4 * s + 1) (decVal g s 1)).set!
      (4 * s + 2) (decVal g s 2)).set! (4 * s + 3) (decVal g s 3) with hR1
    have hcondfalse :
        ((g[7 * s]!.toNat <<< 6 ||| g[7 * s + 1]!.toNat >>> 2 ≥ modulus ||
          (g[7 * s + 1]!.toNat <<< 12 ||| g[7 * s + 2]!.toNat <<< 4 |||
            g[7 * s + 3]!.toNat >>> 4) &&& 0x3FFF ≥ modulus ||
          (g[7 * s + 3]!.toNat <<< 10 ||| g[7 * s + 4]!.toNat <<< 2 |||
            g[7 * s + 5]!.toNat >>> 6) &&& 0x3FFF ≥ modulus ||
          (g[7 * s + 5]!.toNat <<< 8 ||| g[7 * s + 6]!.toNat) &&& 0x3FFF ≥ modulus)) = false := by
      have h4 := hrejs
      simp only [decReject, not_or, not_le] at h4
      obtain ⟨e0, e1, e2, e3⟩ := h4
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, ge_iff_le, not_le]
      exact ⟨⟨⟨e0, e1⟩, e2⟩, e3⟩
    have hstep : (decBody n g s (none, R0) : Id _)
        = ForInStep.yield (none, R1) := by
      change (if (g[7 * s]!.toNat <<< 6 ||| g[7 * s + 1]!.toNat >>> 2 ≥ modulus ||
          (g[7 * s + 1]!.toNat <<< 12 ||| g[7 * s + 2]!.toNat <<< 4 |||
            g[7 * s + 3]!.toNat >>> 4) &&& 0x3FFF ≥ modulus ||
          (g[7 * s + 3]!.toNat <<< 10 ||| g[7 * s + 4]!.toNat <<< 2 |||
            g[7 * s + 5]!.toNat >>> 6) &&& 0x3FFF ≥ modulus ||
          (g[7 * s + 5]!.toNat <<< 8 ||| g[7 * s + 6]!.toNat) &&& 0x3FFF ≥ modulus) then
          (pure (ForInStep.done ((some none, R0) : Option (Option (Rq n)) × Array Coeff))
            : Id _)
        else pure (ForInStep.yield ((none, R1) : Option (Option (Rq n)) × Array Coeff)))
          = ForInStep.yield ((none, R1) : Option (Option (Rq n)) × Array Coeff)
      rw [if_neg (by rw [hcondfalse]; exact Bool.false_ne_true)]
      rfl
    rw [hstep]
    have hR1sz : R1.size = n := by rw [hR1]; simp [hsz0]
    have hrej' : ∀ b, s + 1 ≤ b → b < (s + 1) + m → ¬ decReject g b := by
      intro b hb hb2; exact hrej b (by omega) (by omega)
    obtain ⟨R, hforIn, hRsz, hRval, hRkeep⟩ := ih (s + 1) R1 hR1sz (by omega) hrej'
    refine ⟨R, hforIn, hRsz, ?_, ?_⟩
    · intro b k' hb hb2 hk'
      rcases Nat.lt_or_ge s b with hsb | hsb
      · exact hRval b k' (by omega) (by omega) hk'
      · -- b = s
        have hbeq : b = s := by omega
        subst hbeq
        rw [hRkeep (4 * b + k') (by left; omega)]
        rw [hR1]
        have hbn : 4 * b + 3 < n := by omega
        interval_cases k'
        · simp only [Nat.add_zero]
          rw [getD_set!_ne' _ _ _ _ (by omega), getD_set!_ne' _ _ _ _ (by omega),
              getD_set!_ne' _ _ _ _ (by omega), getD_set!_self' _ _ _ (by rw [hsz0]; omega)]
        · rw [getD_set!_ne' _ _ _ _ (by omega), getD_set!_ne' _ _ _ _ (by omega),
              getD_set!_self' _ _ _ (by rw [Array.size_set!, hsz0]; omega)]
        · rw [getD_set!_ne' _ _ _ _ (by omega),
              getD_set!_self' _ _ _ (by rw [Array.size_set!, Array.size_set!, hsz0]; omega)]
        · rw [getD_set!_self' _ _ _
              (by rw [Array.size_set!, Array.size_set!, Array.size_set!, hsz0]; omega)]
    · intro k hk
      rw [hRkeep k (by omega)]
      rw [hR1]
      rw [getD_set!_ne' _ _ _ _ (by omega), getD_set!_ne' _ _ _ _ (by omega),
          getD_set!_ne' _ _ _ _ (by omega), getD_set!_ne' _ _ _ _ (by omega)]

/-- On `pkEncode n h` input, no decoder group is ever rejected. -/
private theorem pkEncode_not_reject (n : ℕ) (h : Rq n) (hn4 : n % 4 = 0)
    (b : ℕ) (hb : b < n / 4) : ¬ decReject (pkEncode n h) b := by
  obtain ⟨v0, v1, v2, v3⟩ := pkEncode_group_decode n h hn4 b hb
  simp only [decReject, not_or, not_le]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [v0]; exact ZMod.val_lt _
  · rw [v1]; exact ZMod.val_lt _
  · rw [v2]; exact ZMod.val_lt _
  · rw [v3]; exact ZMod.val_lt _

/-- On `pkEncode n h` input, the decoded value at group `b`, sub-index `s`, is the original
coefficient `h[4b+s]`. -/
private theorem decVal_pkEncode (n : ℕ) (h : Rq n) (hn4 : n % 4 = 0)
    (b : ℕ) (hb : b < n / 4) (s : ℕ) (hs : s < 4) :
    decVal (pkEncode n h) b s = h[4 * b + s]! := by
  obtain ⟨v0, v1, v2, v3⟩ := pkEncode_group_decode n h hn4 b hb
  have hcoeff : ∀ (k : ℕ) (hk : k < n), ((h[k]!).val : Coeff) = h[k]! := by
    intro k hk
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hbn : 4 * b + 3 < n := by omega
  interval_cases s
  · change (((pkEncode n h)[7 * b]!.toNat <<< 6 ||| (pkEncode n h)[7 * b + 1]!.toNat >>> 2 : ℕ)
        : Coeff) = h[4 * b + 0]!
    rw [v0, hcoeff (4 * b) (by omega), Nat.add_zero]
  · change ((((pkEncode n h)[7 * b + 1]!.toNat <<< 12 ||| (pkEncode n h)[7 * b + 2]!.toNat <<< 4 |||
        (pkEncode n h)[7 * b + 3]!.toNat >>> 4) &&& 0x3FFF : ℕ) : Coeff) = _
    rw [v1, hcoeff (4 * b + 1) (by omega)]
  · change ((((pkEncode n h)[7 * b + 3]!.toNat <<< 10 ||| (pkEncode n h)[7 * b + 4]!.toNat <<< 2 |||
        (pkEncode n h)[7 * b + 5]!.toNat >>> 6) &&& 0x3FFF : ℕ) : Coeff) = _
    rw [v2, hcoeff (4 * b + 2) (by omega)]
  · change ((((pkEncode n h)[7 * b + 5]!.toNat <<< 8 ||| (pkEncode n h)[7 * b + 6]!.toNat) &&&
        0x3FFF : ℕ) : Coeff) = _
    rw [v3, hcoeff (4 * b + 3) (by omega)]

/-- Round-trip: decoding an encoded Falcon public key recovers the original polynomial.
Requires `4 ∣ n` (true for every Falcon degree); for `n % 4 ≠ 0` the encoder pads to a
non-canonical length and the decoder rejects. -/
theorem pkDecode_pkEncode (n : ℕ) (h : Rq n) (hn4 : 4 ∣ n) :
    pkDecode n (pkEncode n h) = some h := by
  have hmod : n % 4 = 0 := by omega
  -- the encoder output has exactly the canonical length, so the size guard is not taken
  have hsize : (pkEncode n h).size = 7 * n / 4 := by
    rw [pkEncode_size n h hmod]; omega
  have hguard : ¬ (pkEncode n h).size < 7 * n / 4 := by rw [hsize]; omega
  -- obtain the loop result via the invariant
  obtain ⟨R, hforIn, hRsz, hRval, hRkeep⟩ :=
    decode_loop_invariant n (pkEncode n h) (n / 4) 0 (Array.replicate n 0)
      (by simp) (by omega) (fun b _ hb => pkEncode_not_reject n h hmod b (by omega))
  -- unfold pkDecode and reduce to the post-loop assembly
  unfold pkDecode
  have hb : (n % 4 != 0) = false := by simp [hmod]
  simp only [Id.run, hb, Bool.false_eq_true, if_false, hguard,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.div_one,
    Nat.add_sub_cancel]
  -- the forIn body is definitionally `decBody`, so rewrite using the invariant result
  have hforIn' : (forIn (m := Id) (List.range' 0 (n / 4))
        ((none, Array.replicate n 0) : Option (Option (Rq n)) × Array Coeff)
        (fun b r =>
          let d0 := (pkEncode n h)[7 * b]!.toNat
          let d1 := (pkEncode n h)[7 * b + 1]!.toNat
          let d2 := (pkEncode n h)[7 * b + 2]!.toNat
          let d3 := (pkEncode n h)[7 * b + 3]!.toNat
          let d4 := (pkEncode n h)[7 * b + 4]!.toNat
          let d5 := (pkEncode n h)[7 * b + 5]!.toNat
          let d6 := (pkEncode n h)[7 * b + 6]!.toNat
          let h0 := (d0 <<< 6) ||| (d1 >>> 2)
          let h1 := ((d1 <<< 12) ||| (d2 <<< 4) ||| (d3 >>> 4)) &&& 0x3FFF
          let h2 := ((d3 <<< 10) ||| (d4 <<< 2) ||| (d5 >>> 6)) &&& 0x3FFF
          let h3 := ((d5 <<< 8) ||| d6) &&& 0x3FFF
          if h0 ≥ modulus || h1 ≥ modulus || h2 ≥ modulus || h3 ≥ modulus then
            pure (ForInStep.done (some none, r.2))
          else
            pure (ForInStep.yield (none,
              (((r.2.set! (4 * b) (h0 : Coeff)).set! (4 * b + 1) (h1 : Coeff)).set!
                (4 * b + 2) (h2 : Coeff)).set! (4 * b + 3) (h3 : Coeff)))))
      = ((none, R) : Option (Option (Rq n)) × Array Coeff) := hforIn
  erw [hforIn']
  -- the status is `none`, so the assembly returns `some (Vector.ofFn (R.getD · 0))`
  change some (Vector.ofFn fun x : Fin n => R.getD x.val 0) = some h
  -- every cell of `R` recovers the original coefficient
  have hRcoeff : ∀ j, j < n → R.getD j 0 = h[j]! := by
    intro j hj
    have hj4 : j = 4 * (j / 4) + j % 4 := by omega
    have hbk : j / 4 < n / 4 := by omega
    have hsk : j % 4 < 4 := by omega
    calc R.getD j 0
        = R.getD (4 * (j / 4) + j % 4) 0 := by rw [← hj4]
      _ = decVal (pkEncode n h) (j / 4) (j % 4) :=
          hRval (j / 4) (j % 4) (by omega) (by omega) hsk
      _ = h[4 * (j / 4) + j % 4]! := decVal_pkEncode n h hmod (j / 4) hbk (j % 4) hsk
      _ = h[j]! := by rw [← hj4]
  congr 1
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_ofFn, hRcoeff k hk, getElem!_pos h k hk]
  rfl

end Falcon.Concrete
