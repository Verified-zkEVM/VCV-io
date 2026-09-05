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

## References

- c-fn-dsa: `codec.c` (comp_encode, comp_decode, mqpoly_encode, mqpoly_decode)
- Falcon specification v1.2, Section 3.12 (Algorithms 17–18)
-/

@[expose] public section


namespace Falcon.Concrete

open Falcon

/-! ## Signature compression

Falcon stores the signature polynomial `s₂` with the Golomb-Rice style code of the specification
(Algorithms 17–18): a coefficient `x` with `|x| ≤ 2047` becomes a sign bit, the seven low bits of
`|x|` (most significant first), `|x| / 128` zero bits, and a terminating one bit. The bits of all
coefficients are packed most significant first and the output is zero-padded to exactly `dlen`
bytes; the decoder accepts exactly that length and only zero padding. Both directions are written
over the bit stream, which is what the round-trip theorem `decompress_compress` reasons about. -/

/-- The `k`-bit big-endian representation of `v` (bits `k-1` down to `0`). -/
def natBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, v => v.testBit k :: natBits k v

/-- The number whose big-endian bits are `bits`. -/
def natOfBits : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + natOfBits bs

/-- The bits of a byte, most significant first. -/
def byteBits (b : UInt8) : List Bool := natBits 8 b.toNat

/-- The bit stream of a byte string, most significant bit of each byte first. -/
def bytesToBits (d : List UInt8) : List Bool := d.flatMap byteBits

/-- Pack a bit stream into bytes, most significant bit first; the last byte is zero-padded. -/
def bitsToBytes (bits : List Bool) : List UInt8 :=
  if bits.isEmpty then []
  else
    (natOfBits (bits.take 8 ++ List.replicate (8 - (bits.take 8).length) false)).toUInt8 ::
      bitsToBytes (bits.drop 8)
termination_by bits.length
decreasing_by
  simp only [List.length_drop]
  have : bits.length ≠ 0 := by simpa [List.isEmpty_iff_length_eq_zero] using ‹¬bits.isEmpty›
  omega

/-- The code of one coefficient: sign, seven low bits of `|x|`, `|x| / 128` zeros, a one. -/
def coeffBits (x : ℤ) : List Bool :=
  decide (x < 0) :: (natBits 7 (x.natAbs % 128) ++ List.replicate (x.natAbs / 128) false ++ [true])

/-- Compress a Falcon signature polynomial into exactly `dlen` bytes, or `none` when a
coefficient is out of range or the code does not fit. -/
def compress (n : ℕ) (s : IntPoly n) (dlen : ℕ) : Option (List UInt8) :=
  if ∀ i : Fin n, -2047 ≤ s.get i ∧ s.get i ≤ 2047 then
    let bits := (List.finRange n).flatMap fun i => coeffBits (s.get i)
    if 8 * dlen < bits.length then none
    else some (bitsToBytes bits ++ List.replicate (dlen - (bitsToBytes bits).length) 0)
  else none

/-- Read the unary part of a coefficient code: each zero adds `128` to the magnitude `m`, a one
terminates. Fails past `2047`, on the negative zero `-0`, and at the end of the stream. -/
def parseUnary (t : Bool) : ℕ → List Bool → Option (ℤ × List Bool)
  | m, true :: rest => if m = 0 ∧ t then none else some (if t then -(m : ℤ) else (m : ℤ), rest)
  | m, false :: rest => if 2047 < m + 128 then none else parseUnary t (m + 128) rest
  | _, [] => none

/-- Read one coefficient code from the bit stream. -/
def parseCoeff : List Bool → Option (ℤ × List Bool)
  | t :: rest =>
    if 7 ≤ rest.length then parseUnary t (natOfBits (rest.take 7)) (rest.drop 7) else none
  | [] => none

/-- Read `k` coefficient codes from the bit stream. -/
def parseCoeffs : ℕ → List Bool → Option (List ℤ × List Bool)
  | 0, bits => some ([], bits)
  | k + 1, bits => do
    let (x, rest) ← parseCoeff bits
    let (xs, rest') ← parseCoeffs k rest
    pure (x :: xs, rest')

/-- Decompress a fixed-length Falcon signature polynomial.

`compress` pads every successful output to exactly `dlen` bytes. Accordingly, this decoder
accepts exactly that length and rejects any nonzero padding; the optional unpadded Falcon
representation is outside its format. -/
def decompress (n : ℕ) (d : List UInt8) (dlen : ℕ) : Option (IntPoly n) :=
  if d.length ≠ dlen then none
  else
    match parseCoeffs n (bytesToBits d) with
    | none => none
    | some (vals, rest) =>
      if rest.all (fun b => !b) then some (Vector.ofFn fun i => vals.getD i.val 0) else none

@[simp] theorem decompress_eq_none_of_length_ne (n d dlen) (h : d.length ≠ dlen) :
    decompress n d dlen = none := by
  simp [decompress, h]

/-! ### Bit-level lemmas -/

theorem natBits_length (k v : ℕ) : (natBits k v).length = k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [natBits, ih]

theorem natOfBits_lt (bs : List Bool) : natOfBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [natOfBits]
  | cons b bs ih =>
    simp only [natOfBits, List.length_cons, pow_succ]
    split <;> omega

/-- `natBits k` reads only the low `k` bits. -/
theorem natBits_congr {k v w : ℕ} (h : ∀ j, j < k → v.testBit j = w.testBit j) :
    natBits k v = natBits k w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [natBits, h k (Nat.lt_succ_self k)]
    congr 1
    exact ih fun j hj => h j (Nat.lt_succ_of_lt hj)

theorem natBits_natOfBits (bs : List Bool) : natBits bs.length (natOfBits bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hlt := natOfBits_lt bs
    have hval : natOfBits (b :: bs) = 2 ^ bs.length * (if b then 1 else 0) + natOfBits bs := by
      simp only [natOfBits]; split <;> simp
    simp only [List.length_cons, natBits, hval]
    rw [List.cons.injEq]
    refine ⟨?_, ?_⟩
    · rw [Nat.testBit_two_pow_mul_add _ hlt]
      simp
      cases b <;> simp
    · refine (natBits_congr fun j hj => ?_).trans ih
      rw [Nat.testBit_two_pow_mul_add _ hlt, if_pos hj]

theorem natOfBits_natBits {k v : ℕ} (h : v < 2 ^ k) : natOfBits (natBits k v) = v := by
  induction k generalizing v with
  | zero => simp [natBits, natOfBits]; omega
  | succ k ih =>
    have hmod : natBits k v = natBits k (v % 2 ^ k) :=
      natBits_congr fun j hj => by rw [Nat.testBit_mod_two_pow]; simp [hj]
    simp only [natBits, natOfBits, natBits_length, hmod, ih (Nat.mod_lt _ (by positivity))]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : v / 2 ^ k < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at h; omega
    have := Nat.div_add_mod v (2 ^ k)
    have hcases : v / 2 ^ k = 0 ∨ v / 2 ^ k = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hdiv)
    rcases hcases with h0 | h0 <;> simp [h0] at this ⊢ <;> omega

theorem byteBits_toUInt8 (bs : List Bool) (h : bs.length = 8) :
    byteBits (natOfBits bs).toUInt8 = bs := by
  have hlt : natOfBits bs < 256 := by have := natOfBits_lt bs; rw [h] at this; exact this
  have : (natOfBits bs).toUInt8.toNat = natOfBits bs := by
    change (UInt8.ofNat _).toNat = _
    rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt hlt
  rw [byteBits, this, ← h, natBits_natOfBits]

theorem bytesToBits_append (a b : List UInt8) :
    bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b := by
  simp [bytesToBits, List.flatMap_append]

theorem bytesToBits_replicate_zero (k : ℕ) :
    bytesToBits (List.replicate k 0) = List.replicate (8 * k) false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, bytesToBits, List.flatMap_cons, ← bytesToBits, ih,
      show byteBits 0 = List.replicate 8 false from rfl, List.replicate_append_replicate]
    congr 1
    omega

theorem bytesToBits_bitsToBytes (bits : List Bool) :
    bytesToBits (bitsToBytes bits) =
      bits ++ List.replicate ((8 - bits.length % 8) % 8) false := by
  fun_induction bitsToBytes bits with
  | case1 bits hempty =>
    rw [List.isEmpty_iff] at hempty
    subst hempty
    rfl
  | case2 bits hempty ih =>
    rw [bytesToBits, List.flatMap_cons, ← bytesToBits, ih,
      byteBits_toUInt8 _ (by simp [List.length_take])]
    have hne : bits.length ≠ 0 := by simpa [List.isEmpty_iff_length_eq_zero] using hempty
    rcases Nat.lt_or_ge bits.length 8 with hlt | hge
    · rw [List.drop_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp only [List.length_nil, Nat.zero_mod, Nat.sub_zero, Nat.mod_self, List.replicate_zero,
        List.append_nil]
      congr 2
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)]
    · rw [List.length_take, min_eq_left hge, Nat.sub_self, List.replicate_zero, List.append_nil,
        ← List.append_assoc, List.take_append_drop, List.length_drop]
      congr 3
      omega

theorem bitsToBytes_length (bits : List Bool) :
    (bitsToBytes bits).length = (bits.length + 7) / 8 := by
  fun_induction bitsToBytes bits with
  | case1 bits hempty =>
    rw [List.isEmpty_iff] at hempty
    subst hempty
    rfl
  | case2 bits hempty ih =>
    rw [List.length_cons, ih, List.length_drop]
    have hne : bits.length ≠ 0 := by simpa [List.isEmpty_iff_length_eq_zero] using hempty
    omega

/-! ### Coefficient-level lemmas -/

theorem parseUnary_replicate (t : Bool) (m q : ℕ) (rest : List Bool)
    (hle : m + 128 * q ≤ 2047) (hz : ¬ (m + 128 * q = 0 ∧ t = true)) :
    parseUnary t m (List.replicate q false ++ true :: rest) =
      some (if t then -((m + 128 * q : ℕ) : ℤ) else ((m + 128 * q : ℕ) : ℤ), rest) := by
  induction q generalizing m with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, parseUnary, Nat.mul_zero, Nat.add_zero] at *
    rw [if_neg hz]
  | succ q ih =>
    rw [List.replicate_succ, List.cons_append, parseUnary, if_neg (by omega)]
    rw [ih (m + 128) (by omega) (by omega), show m + 128 + 128 * q = m + 128 * (q + 1) by ring]

theorem parseCoeff_coeffBits (x : ℤ) (hx : -2047 ≤ x ∧ x ≤ 2047) (rest : List Bool) :
    parseCoeff (coeffBits x ++ rest) = some (x, rest) := by
  have habs : x.natAbs ≤ 2047 := by omega
  simp only [coeffBits, List.cons_append, parseCoeff, List.append_assoc]
  rw [if_pos (by simp [natBits_length]), List.take_append_of_le_length (by simp [natBits_length]),
    List.take_of_length_le (by simp [natBits_length]),
    List.drop_append_of_le_length (by simp [natBits_length]),
    List.drop_of_length_le (by simp [natBits_length]), List.nil_append,
    natOfBits_natBits (k := 7)
      (by have := Nat.mod_lt x.natAbs (by norm_num : 0 < 128); simpa using this),
    List.nil_append,
    parseUnary_replicate _ _ _ _ (by rw [Nat.mod_add_div]; exact habs)]
  · rw [Nat.mod_add_div]
    congr 2
    split_ifs with hneg <;> simp only [decide_eq_true_eq] at hneg <;> omega
  · rw [Nat.mod_add_div]
    rintro ⟨h0, ht⟩
    have : x < 0 := by simpa using ht
    omega

theorem parseCoeffs_flatMap (xs : List ℤ) (hxs : ∀ x ∈ xs, -2047 ≤ x ∧ x ≤ 2047)
    (tail : List Bool) :
    parseCoeffs xs.length (xs.flatMap coeffBits ++ tail) = some (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.flatMap_cons, parseCoeffs, parseCoeff_coeffBits x (hxs x (List.mem_cons_self ..)),
      ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))]

/-! ### The round-trip -/

/-- **Decompression inverts compression**: every byte string `compress` produces decodes back to
the polynomial it came from. This is the `compress_decompress` law of `Primitives.Laws` for the
concrete codec. -/
theorem decompress_compress (n : ℕ) (s : IntPoly n) (dlen : ℕ) (d : List UInt8)
    (h : compress n s dlen = some d) : decompress n d dlen = some s := by
  unfold compress at h
  dsimp only at h
  split_ifs at h with hbound hfit
  rw [Option.some.injEq] at h
  subst h
  set bits := (List.finRange n).flatMap fun i => coeffBits (s.get i) with hbits
  set L := bits.length with hL
  set NB := (bitsToBytes bits).length with hNB
  have hnb : NB ≤ dlen := by
    rw [hNB, bitsToBytes_length]; omega
  have hlen : (bitsToBytes bits ++ List.replicate (dlen - NB) 0).length = dlen := by
    simp only [List.length_append, List.length_replicate, ← hNB]; omega
  set T := List.replicate ((8 - L % 8) % 8) false ++ List.replicate (8 * (dlen - NB)) false
    with hT
  have hstream : bytesToBits (bitsToBytes bits ++ List.replicate (dlen - NB) 0) = bits ++ T := by
    rw [bytesToBits_append, bytesToBits_bitsToBytes, bytesToBits_replicate_zero, List.append_assoc]
  set xs := (List.finRange n).map fun i => s.get i with hxsdef
  have hxs : bits = xs.flatMap coeffBits := by
    rw [hbits, hxsdef, List.flatMap_map]
  have hparse : parseCoeffs n (xs.flatMap coeffBits ++ T) = some (xs, T) := by
    have h := parseCoeffs_flatMap xs
      (fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        exact hbound i) T
    rwa [hxsdef, List.length_map, List.length_finRange, ← hxsdef] at h
  unfold decompress
  rw [if_neg (by rw [hlen]; exact fun h => h rfl), hstream, hxs, hparse]
  dsimp only
  rw [if_pos (by simp [hT, List.all_replicate])]
  congr 1
  apply LatticeCrypto.Poly.ext_get_eq
  intro i
  rw [Vector.get_ofFn, List.getD_eq_getElem?_getD, hxsdef, List.getElem?_map,
    List.getElem?_eq_getElem (by simp [List.length_finRange]), Option.map_some, Option.getD_some]
  simp [List.getElem_finRange]

/-! ## Public key encoding (14 bits per coefficient) -/

/-- The FN-DSA public-key header byte for a given `logn`. -/
@[inline] def publicKeyHeader (logn : Nat) : UInt8 :=
  (0x00 + logn).toUInt8

/-- Encode a Falcon public key polynomial using the packed 14-bit coefficient format. -/
def pkEncode (n : ℕ) (h : Rq n) : ByteArray := Id.run do
  if n % 4 != 0 then
    panic! s!"Falcon public-key encoding requires n divisible by 4, got {n}"
  let mut out := ByteArray.empty
  let mut i := 0
  while i + 3 < n do
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
    i := i + 4
  return out

/-- Decode a Falcon public key polynomial from the packed 14-bit coefficient format. -/
def pkDecode (n : ℕ) (d : ByteArray) : Option (Rq n) := Id.run do
  if n % 4 != 0 then return none
  let needed := 7 * n / 4
  if d.size < needed then return none
  let mut result : Array Coeff := Array.replicate n 0
  let mut i := 0
  let mut j := 0
  while i + 3 < n do
    let d0 := d[j]!.toNat
    let d1 := d[j+1]!.toNat
    let d2 := d[j+2]!.toNat
    let d3 := d[j+3]!.toNat
    let d4 := d[j+4]!.toNat
    let d5 := d[j+5]!.toNat
    let d6 := d[j+6]!.toNat
    j := j + 7
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
    i := i + 4
  return some (Vector.ofFn fun ⟨i, _⟩ => result.getD i 0)

/-- External public-key bytes used by FN-DSA verification and raw-message hashing:
one header byte followed by the packed 14-bit coefficient encoding. -/
def publicKeyBytes (logn : Nat) {n : ℕ} (h : Rq n) : ByteArray :=
  ByteArray.mk #[publicKeyHeader logn] ++ pkEncode n h

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

end Falcon.Concrete
