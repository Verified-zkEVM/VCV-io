/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Encoding

/-!
# Round-Trip Lemmas For The SLH-DSA Conversion Helpers

Arithmetic characterizations of `toInt`, `toByte`, and `base2b` (FIPS 205 §4.4, Algorithms
2–4): Algorithm 2 inverts Algorithm 3 on values that fit their byte width, and the streaming
digit extractor of Algorithm 4 agrees with the pointwise MSB-first arithmetic form whenever the
input supplies enough bits. These facts back the WOTS+ checksum pipeline and the checked
address codecs.

## References

- NIST FIPS 205, §4.4 (Algorithms 2, 3, 4)
-/

@[expose] public section


namespace SLHDSA

/-! ## Algorithm 2 (`toInt`) -/

@[simp] theorem toInt_nil : toInt [] = 0 := rfl

/-- Appending one byte performs one big-endian radix-256 step. -/
theorem toInt_append_byte (x : List Byte) (b : Byte) :
    toInt (x ++ [b]) = toInt x * 256 + b.toNat := by
  simp [toInt, List.foldl_append]

/-- Concatenation scales the prefix by `256^|suffix|` and adds the suffix. -/
theorem toInt_append (x y : List Byte) :
    toInt (x ++ y) = toInt x * 256 ^ y.length + toInt y := by
  induction y using List.reverseRecOn with
  | nil => simp
  | append_singleton ys b ih =>
      rw [← List.append_assoc, toInt_append_byte, ih, toInt_append_byte,
        List.length_append, List.length_singleton, pow_succ]
      ring

/-- A byte string of length `n` denotes an integer strictly below `256^n`. -/
theorem toInt_lt_pow (x : List Byte) : toInt x < 256 ^ x.length := by
  induction x using List.reverseRecOn with
  | nil => simp [toInt]
  | append_singleton xs b ih =>
      rw [toInt_append_byte]
      simp only [List.length_append, List.length_singleton, Nat.pow_succ]
      have hb : b.toNat < 256 := UInt8.toNat_lt_size b
      omega

/-! ## Algorithm 3 (`toByte`) -/

@[simp] theorem toByte_length (x len : ℕ) : (toByte x len).length = len := by
  simp [toByte]

/-- Algorithm 3 emits the least significant byte last. -/
theorem toByte_succ (x len : ℕ) :
    toByte x (len + 1) = toByte (x / 256) len ++ [UInt8.ofNat (x % 256)] := by
  simp only [toByte, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi' : i < len := List.mem_range.mp hi
    have hexp : len + 1 - 1 - i = (len - 1 - i) + 1 := by omega
    rw [hexp, pow_succ', ← Nat.div_div_eq_div_mul]
  · have hzero : len + 1 - 1 - len = 0 := by omega
    rw [hzero, pow_zero, Nat.div_one]

/-- Algorithm 2 reconstructs the low `len` bytes emitted by Algorithm 3. -/
theorem toInt_toByte_mod (x len : ℕ) : toInt (toByte x len) = x % 256 ^ len := by
  induction len generalizing x with
  | zero => simp [toByte, Nat.mod_one]
  | succ len ih =>
      rw [toByte_succ, toInt_append_byte, ih, pow_succ', Nat.mod_mul]
      have hbyte : (UInt8.ofNat (x % 256)).toNat = x % 256 := by
        simp [UInt8.toNat_ofNat', Nat.mod_mod_of_dvd]
      rw [hbyte]
      ring

/-- In the Algorithm 3 precondition range, Algorithm 2 is an exact left inverse. -/
theorem toInt_toByte (x len : ℕ) (h : x < 256 ^ len) :
    toInt (toByte x len) = x := by
  rw [toInt_toByte_mod, Nat.mod_eq_of_lt h]

/-! ## Algorithm 4 (`base2b`) closed form -/

/-- One `base2bFill` call started on a consumed prefix of `x` stops at a longer prefix that
still lies within `x` and buffers at least `b` bits (given enough input for one more digit). -/
private theorem base2bFill_consume (b : ℕ) (x : List Byte) :
    ∀ (n c j : ℕ), x.length - c ≤ n → c ≤ x.length → b * j ≤ 8 * c →
      b * (j + 1) ≤ 8 * x.length →
      ∃ c', c ≤ c' ∧ c' ≤ x.length ∧ b * (j + 1) ≤ 8 * c' ∧
        base2bFill b (x.drop c) (toInt (x.take c)) (8 * c - b * j) =
          (x.drop c', toInt (x.take c'), 8 * c' - b * j) := by
  intro n
  induction n with
  | zero =>
      intro c j hn hc hbj htot
      have hcl : c = x.length := by omega
      subst hcl
      refine ⟨x.length, le_rfl, le_rfl, htot, ?_⟩
      rw [List.drop_length]
      rfl
  | succ n ih =>
      intro c j hn hc hbj htot
      have hmul : b * (j + 1) = b * j + b := by ring
      by_cases hble : b ≤ 8 * c - b * j
      · refine ⟨c, le_rfl, hc, by omega, ?_⟩
        cases hdrop : x.drop c with
        | nil => rfl
        | cons y ys =>
            simp only [base2bFill]
            rw [if_pos hble]
      · have hclt : c < x.length := by
          rcases Nat.lt_or_ge c x.length with h | h
          · exact h
          · exact absurd (le_antisymm hc h) (fun hcl => hble (by omega))
        have htake : toInt (x.take (c + 1)) = toInt (x.take c) * 256 + (x[c]'hclt).toNat := by
          rw [List.take_add_one, List.getElem?_eq_getElem hclt]
          simpa using toInt_append_byte (x.take c) (x[c]'hclt)
        obtain ⟨c', h1, h2, h3, h4⟩ := ih (c + 1) j (by omega) hclt (by omega) htot
        refine ⟨c', by omega, h2, h3, ?_⟩
        rw [List.drop_eq_getElem_cons hclt]
        simp only [base2bFill]
        rw [if_neg hble, ← htake,
          show 8 * c - b * j + 8 = 8 * (c + 1) - b * j by omega]
        exact h4

/-- The streaming digit emitter, resumed on a consumed prefix of `x` with the corresponding
bit buffer, produces the pointwise MSB-first digits of the full input. -/
private theorem base2bGo_bigEndian (b : ℕ) (x : List Byte) :
    ∀ (out j c : ℕ), c ≤ x.length → b * j ≤ 8 * c → b * (j + out) ≤ 8 * x.length →
      base2bGo b out (x.drop c) (toInt (x.take c)) (8 * c - b * j) =
        (List.range out).map
          (fun i => toInt x / 2 ^ (8 * x.length - b * (j + i + 1)) % 2 ^ b) := by
  intro out
  induction out with
  | zero => intro j c _ _ _; rfl
  | succ out ih =>
      intro j c hc hbj htot
      have hmul : b * (j + 1) = b * j + b := by ring
      have hnext : b * (j + 1) ≤ 8 * x.length :=
        le_trans (Nat.mul_le_mul_left b (by omega)) htot
      obtain ⟨c', hcc', hc'len, hfits, hfill⟩ :=
        base2bFill_consume b x (x.length - c) c j le_rfl hc hbj hnext
      have hbits : 8 * c' - b * j - b = 8 * c' - b * (j + 1) := by omega
      have htot' : b * (j + 1 + out) ≤ 8 * x.length := by
        rw [show j + 1 + out = j + (out + 1) by omega]
        exact htot
      have hhead : toInt (x.take c') / 2 ^ (8 * c' - b * (j + 1)) % 2 ^ b =
          toInt x / 2 ^ (8 * x.length - b * (j + 1)) % 2 ^ b := by
        have hsplit : toInt x =
            toInt (x.take c') * 256 ^ (x.length - c') + toInt (x.drop c') := by
          conv_lhs => rw [← List.take_append_drop c' x]
          rw [toInt_append, List.length_drop]
        have hlt : toInt (x.drop c') < 256 ^ (x.length - c') := by
          simpa [List.length_drop] using toInt_lt_pow (x.drop c')
        have hexp : 8 * x.length - b * (j + 1) =
            8 * (x.length - c') + (8 * c' - b * (j + 1)) := by omega
        have h256 : (256 : ℕ) ^ (x.length - c') = 2 ^ (8 * (x.length - c')) := by
          rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul]
        have hpos : 0 < (256 : ℕ) ^ (x.length - c') := by positivity
        rw [hsplit, hexp, pow_add, ← h256, ← Nat.div_div_eq_div_mul,
          Nat.mul_comm (toInt (x.take c')) (256 ^ (x.length - c')),
          Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt]
        simp only [Nat.add_zero]
      simp only [base2bGo, hfill]
      rw [hbits, Nat.shiftRight_eq_div_pow, List.range_succ_eq_map, List.map_cons,
        List.map_map]
      congr 1
      rw [ih (j + 1) c' hc'len hfits htot']
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp_apply, Nat.succ_eq_add_one]
      rw [show j + 1 + i + 1 = j + (i + 1) + 1 by omega]

/-- Pointwise MSB-first characterization of Algorithm 4 on sufficiently long inputs: with at
least `outLen * b` input bits available, digit `i` reads bits `[b*i, b*(i+1))` (MSB first) of
the big-endian input value. -/
theorem base2b_bigEndian (x : List Byte) (b outLen : ℕ)
    (hlen : outLen * b ≤ 8 * x.length) :
    base2b x b outLen = (List.range outLen).map
      (fun i => toInt x / 2 ^ (8 * x.length - b * (i + 1)) % 2 ^ b) := by
  have h := base2bGo_bigEndian b x outLen 0 0 (Nat.zero_le _) (by simp)
    (by simpa [Nat.mul_comm] using hlen)
  simpa [base2b] using h

end SLHDSA
