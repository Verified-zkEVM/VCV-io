/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Params

/-!
# SLH-DSA Integer / Byte / Base Helpers

The pure conversion helpers of FIPS 205 §4.4: `toInt` (Algorithm 2, big-endian byte string →
integer), `toByte` (Algorithm 3, integer → big-endian byte string), and `base2b`
(Algorithm 4, split a byte string into `outLen` big-endian `b`-bit digits, most significant
first). These are used by WOTS+ (`b = lg_w`) and FORS (`b = a`) to derive digit/index vectors,
and by the message-digest split (`Position.splitDigest`).

## References

- NIST FIPS 205, §4.4 (Algorithms 2, 3, 4)
-/

@[expose] public section


namespace SLHDSA

/-- Failures exposed by checked fixed-width SLH-DSA decoders. `invalidLength` reports a wrong
exact byte width and is the sole failure of the structured wire codecs; `zeroDigitWidth` and
`insufficientInput` classify digit-extraction boundaries; `outOfRange`, `invalidAddressType`,
and `noncanonicalAddress` classify checked address encodings. -/
inductive CodecError where
  | invalidLength (expected actual : ℕ)
  | zeroDigitWidth
  | insufficientInput (requiredBits availableBits : ℕ)
  | outOfRange (widthBytes value : ℕ)
  | invalidAddressType (code : ℕ)
  | noncanonicalAddress
deriving Repr, DecidableEq

/-- `toInt(X, |X|)`: interpret a byte list as a big-endian natural number (FIPS 205 Alg 2). -/
def toInt (x : List Byte) : ℕ :=
  x.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `toByte(x, len)`: big-endian `len`-byte serialization of `x` (FIPS 205 Alg 3). -/
def toByte (x len : ℕ) : List Byte :=
  (List.range len).map (fun i => UInt8.ofNat (x / 256 ^ (len - 1 - i) % 256))

/-- Decode a list only when its length is exactly the requested wire width. -/
def decodeExact (n : ℕ) (raw : List Byte) : Except CodecError (Bytes n) :=
  if h : raw.length = n then
    .ok ⟨raw.toArray, by simpa using h⟩
  else
    .error (.invalidLength n raw.length)

/-- Fixed-width vectors encode without adding or dropping bytes. -/
def encodeExact {n : ℕ} (bytes : Bytes n) : List Byte := bytes.toList

@[simp] theorem decodeExact_encode {n : ℕ} (bytes : Bytes n) :
    decodeExact n (encodeExact bytes) = .ok bytes := by
  simp only [decodeExact, encodeExact, Vector.length_toList, ↓reduceDIte]
  congr 1

/-- A successful exact-width decode has consumed the complete input. -/
theorem decodeExact_eq_ok_iff {n : ℕ} {raw : List Byte} {bytes : Bytes n} :
    decodeExact n raw = .ok bytes ↔ raw = bytes.toList := by
  simp only [decodeExact]
  split
  · constructor
    · intro h
      injection h with hbytes
      subst bytes
      simp
    · intro h
      subst raw
      congr 1
  · constructor
    · simp
    · intro h
      subst raw
      simp_all

/-- Inputs of any other length are rejected before structured parsing begins. -/
theorem decodeExact_eq_error_of_length_ne (n : ℕ) (raw : List Byte)
    (h : raw.length ≠ n) :
    decodeExact n raw = .error (.invalidLength n raw.length) := by
  simp [decodeExact, h]

/-- Consume bytes from the front of `inp` into the `(total, bits)` accumulator until at least
`b` bits are buffered (the inner `while` of `base2b`). Returns the leftover input and the
updated accumulator. -/
def base2bFill (b : ℕ) : List Byte → ℕ → ℕ → (List Byte × ℕ × ℕ)
  | [], total, bits => ([], total, bits)
  | x :: xs, total, bits =>
      if b ≤ bits then (x :: xs, total, bits)
      else base2bFill b xs (total * 256 + x.toNat) (bits + 8)

/-- Emit `out` big-endian `b`-bit digits, threading the `(total, bits)` bit buffer. -/
def base2bGo (b : ℕ) : ℕ → List Byte → ℕ → ℕ → List ℕ
  | 0, _, _, _ => []
  | out + 1, inp, total, bits =>
      let r := base2bFill b inp total bits
      let bits' := r.2.2 - b
      ((r.2.1 >>> bits') % 2 ^ b) :: base2bGo b out r.1 r.2.1 bits'

/-- `base2b(X, b, outLen)`: the first `outLen` big-endian `b`-bit digits of the byte string `X`
(FIPS 205 Algorithm 4). Requires `X` to have at least `⌈outLen·b / 8⌉` bytes; missing bits read
as zero. -/
def base2b (x : List Byte) (b outLen : ℕ) : List ℕ :=
  base2bGo b outLen x 0 0

@[simp] theorem base2b_length (x : List Byte) (b outLen : ℕ) :
    (base2b x b outLen).length = outLen := by
  unfold base2b
  suffices h : ∀ (out : ℕ) (inp : List Byte) (total bits : ℕ),
      (base2bGo b out inp total bits).length = out by
    exact h outLen x 0 0
  intro out
  induction out with
  | zero => intro inp total bits; rfl
  | succ out ih => intro inp total bits; simp [base2bGo, ih]

/-- Every digit produced by `base2b` is bounded by `2^b` (it is reduced mod `2^b`). -/
theorem base2b_lt (x : List Byte) (b outLen : ℕ) :
    ∀ d ∈ base2b x b outLen, d < 2 ^ b := by
  unfold base2b
  suffices h : ∀ (out : ℕ) (inp : List Byte) (total bits : ℕ),
      ∀ d ∈ base2bGo b out inp total bits, d < 2 ^ b by
    exact h outLen x 0 0
  intro out
  induction out with
  | zero => intro inp total bits d hd; simp [base2bGo] at hd
  | succ out ih =>
    intro inp total bits d hd
    simp only [base2bGo, List.mem_cons] at hd
    rcases hd with h | h
    · subst h; exact Nat.mod_lt _ (by positivity)
    · exact ih _ _ _ d h

end SLHDSA
