/-
Copyright (c) 2026 Vitalik Buterin, Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin, Nicolas Consigny
-/

module
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Forall2
public import Mathlib.Tactic.Ring

/-!
# WOTS+ Checksum Incomparability

The combinatorial core of WOTS+ existential unforgeability: for any two distinct message-digit
vectors, the resulting full WOTS+ digit vectors (message digits followed by checksum digits) are
incomparable under the pointwise `≤` ordering. This is what blocks an attacker from forging a
signature by advancing every hash chain forward — increasing any message digit forces the
checksum to decrease, and equal checksums together with pointwise `≤` force equality.

This module is a standard-model statement over `List ℕ` / `ℕ`, independent of the oracle/hash
layer; a WOTS+ one-wayness reduction consumes
`wots_fullDigits_incomparable` as its purely combinatorial ingredient.

See FIPS 205 §5 for the WOTS+ specification this validates.
-/

@[expose] public section


namespace SLHDSA.WotsChecksum

/-! ## Pointwise ordering on lists -/

variable {α β : Type}

open List (Forall₂)

/-- Pointwise-`≤` lists with equal sums are equal. -/
theorem Forall₂.eq_of_sum_eq {xs ys : List ℕ}
    (hLE : Forall₂ (· ≤ ·) xs ys) (hSum : xs.sum = ys.sum) : xs = ys := by
  match xs, ys, hLE with
  | [], [], .nil => rfl
  | a :: as, b :: bs, .cons hd htl =>
    simp only [List.sum_cons] at hSum
    have hSumLE : as.sum ≤ bs.sum := htl.sum_le_sum
    obtain rfl : a = b := by omega
    rw [Forall₂.eq_of_sum_eq htl (by omega)]

/-! ## Splitting `Forall₂` at equal-length prefixes -/

/-- A `Forall₂` relation between two appends splits at an equal-length prefix. -/
theorem Forall₂.append_inv {R : α → α → Prop} {xs₁ xs₂ ys₁ ys₂ : List α}
    (h : Forall₂ R (xs₁ ++ ys₁) (xs₂ ++ ys₂)) (hlen : xs₁.length = xs₂.length) :
    Forall₂ R xs₁ xs₂ ∧ Forall₂ R ys₁ ys₂ :=
  ⟨by simpa [hlen] using List.forall₂_take_append _ _ _ h,
   by simpa [hlen] using List.forall₂_drop_append _ _ _ h⟩

/-! ## Base-w digit arithmetic -/

/-- Reconstruct a natural number from its big-endian base-`w` digit list. -/
def fromBaseW (w : ℕ) (digits : List ℕ) : ℕ :=
  digits.foldl (fun acc d => acc * w + d) 0

@[simp]
theorem fromBaseW_nil (w : ℕ) : fromBaseW w [] = 0 := rfl

private theorem foldl_mul_add_shift (w a : ℕ) (ds : List ℕ) :
    List.foldl (fun acc x => acc * w + x) a ds
      = a * w ^ ds.length + List.foldl (fun acc x => acc * w + x) 0 ds := by
  induction ds generalizing a with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (a * w + d), ih (0 * w + d),
      List.length_cons, Nat.pow_succ]
    ring

@[simp]
theorem fromBaseW_cons (w d : ℕ) (ds : List ℕ) :
    fromBaseW w (d :: ds) = d * w ^ ds.length + fromBaseW w ds := by
  change List.foldl (fun acc x => acc * w + x) 0 (d :: ds)
    = d * w ^ ds.length + List.foldl (fun acc x => acc * w + x) 0 ds
  rw [List.foldl_cons, foldl_mul_add_shift w (0 * w + d) ds]
  ring

theorem fromBaseW_append (w : ℕ) (xs ys : List ℕ) :
    fromBaseW w (xs ++ ys) = fromBaseW w xs * w ^ ys.length + fromBaseW w ys := by
  change List.foldl (fun acc x => acc * w + x) 0 (xs ++ ys)
    = (List.foldl (fun acc x => acc * w + x) 0 xs) * w ^ ys.length
      + List.foldl (fun acc x => acc * w + x) 0 ys
  rw [List.foldl_append]
  exact foldl_mul_add_shift w (List.foldl (fun acc x => acc * w + x) 0 xs) ys

/-- Helper: pointwise `≤` at the `foldl` level with an accumulator. -/
private theorem foldl_acc_le (ds1 ds2 : List ℕ) (w : ℕ) (a b : ℕ) (hAcc : a ≤ b)
    (hLE : Forall₂ (· ≤ ·) ds1 ds2) :
    List.foldl (fun acc d => acc * w + d) a ds1 ≤
    List.foldl (fun acc d => acc * w + d) b ds2 := by
  match ds1, ds2, hLE with
  | [], [], .nil => exact hAcc
  | d1 :: ds1', d2 :: ds2', .cons hd htl =>
    simp only [List.foldl_cons]
    refine foldl_acc_le ds1' ds2' w (a * w + d1) (b * w + d2) ?_ htl
    exact Nat.add_le_add (Nat.mul_le_mul hAcc (Nat.le_refl _)) hd

theorem fromBaseW_pointwiseLE {ds1 ds2 : List ℕ} {w : ℕ}
    (hLE : Forall₂ (· ≤ ·) ds1 ds2) : fromBaseW w ds1 ≤ fromBaseW w ds2 :=
  foldl_acc_le ds1 ds2 w 0 0 (Nat.le_refl 0) hLE

/-- The big-endian base-`w` digit list of `n` with `len` digits (most significant first). -/
def digitsOfBaseW (n w len : ℕ) : List ℕ :=
  match len with
  | 0 => []
  | len + 1 => ((n / w ^ len) % w) :: digitsOfBaseW n w len

theorem digitsOfBaseW_nil (n w : ℕ) : digitsOfBaseW n w 0 = [] := rfl

theorem digitsOfBaseW_length (n w len : ℕ) : (digitsOfBaseW n w len).length = len := by
  induction len with
  | zero => simp [digitsOfBaseW]
  | succ len ih => simp [digitsOfBaseW, ih]

/-- Every digit produced by `digitsOfBaseW` is a genuine base-`w` digit (`< w`). -/
theorem digitsOfBaseW_lt (n w len : ℕ) (hw : 0 < w) :
    ∀ d ∈ digitsOfBaseW n w len, d < w := by
  induction len with
  | zero => intro d hd; simp [digitsOfBaseW] at hd
  | succ len ih =>
    intro d hd
    simp only [digitsOfBaseW, List.mem_cons] at hd
    rcases hd with h | h
    · subst h; exact Nat.mod_lt _ hw
    · exact ih d h

theorem fromBaseW_digitsOfBaseW_eq_mod (n w len : ℕ) :
    fromBaseW w (digitsOfBaseW n w len) = n % (w ^ len) := by
  induction len generalizing n with
  | zero => simp [digitsOfBaseW, fromBaseW, Nat.mod_one]
  | succ len ih =>
    simp only [digitsOfBaseW, fromBaseW_cons, digitsOfBaseW_length n w len, ih n]
    rw [Nat.mod_pow_succ, Nat.mul_comm, Nat.add_comm]

theorem fromBaseW_digitsOfBaseW_of_lt (n w len : ℕ)
    (h : n < w ^ len) : fromBaseW w (digitsOfBaseW n w len) = n := by
  rw [fromBaseW_digitsOfBaseW_eq_mod n w len]
  exact Nat.mod_eq_of_lt h

theorem digitsOfBaseW_pointwiseLE_imp_le {a b w len : ℕ}
    (ha : a < w ^ len) (hb : b < w ^ len)
    (hLE : Forall₂ (· ≤ ·) (digitsOfBaseW a w len) (digitsOfBaseW b w len)) :
    a ≤ b := by
  have ha' : fromBaseW w (digitsOfBaseW a w len) = a :=
    fromBaseW_digitsOfBaseW_of_lt a w len ha
  have hb' : fromBaseW w (digitsOfBaseW b w len) = b :=
    fromBaseW_digitsOfBaseW_of_lt b w len hb
  have hValLE : fromBaseW w (digitsOfBaseW a w len) ≤ fromBaseW w (digitsOfBaseW b w len) :=
    fromBaseW_pointwiseLE hLE
  simpa [ha', hb'] using hValLE

/-! ## WOTS+ checksum -/

/-- The WOTS+ checksum value `Σ (w − 1 − dᵢ)` over the message digits. -/
def wotsChecksumValue (w : ℕ) (digits : List ℕ) : ℕ :=
  (digits.map (fun d => w - 1 - d)).sum

private theorem checksum_each_le (w : ℕ) (digits : List ℕ)
    (hBound : ∀ d ∈ digits, d < w) : ∀ x ∈ digits.map (fun d => w - 1 - d), x ≤ w - 1 := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨d, hd, rfl⟩
  have hlt : d < w := hBound d hd
  omega

private theorem sum_le_length_mul (xs : List ℕ) (M : ℕ)
    (h : ∀ x ∈ xs, x ≤ M) : xs.sum ≤ xs.length * M :=
  List.sum_le_card_nsmul xs M h

theorem wotsChecksumValue_le {digits : List ℕ} {w l1 : ℕ}
    (hLen : digits.length = l1) (hBound : ∀ d ∈ digits, d < w) :
    wotsChecksumValue w digits ≤ l1 * (w - 1) := by
  rw [wotsChecksumValue]
  have h_each := checksum_each_le w digits hBound
  have h_len_map : (digits.map (fun d => w - 1 - d)).length = l1 := by simp [hLen]
  have h_sum_bound := sum_le_length_mul (digits.map (fun d => w - 1 - d)) (w - 1) h_each
  rw [h_len_map] at h_sum_bound
  exact h_sum_bound

/-- The full WOTS+ digit vector: message digits followed by the base-`w` checksum digits.
(The message length `_l1` is carried for spec parity but not used in the definition.) -/
def wotsFullDigits (dig : List ℕ) (w _l1 l2 : ℕ) : List ℕ :=
  dig ++ digitsOfBaseW (wotsChecksumValue w dig) w l2

theorem wotsFullDigits_length (dig : List ℕ) (w l1 l2 : ℕ)
    (hLen : dig.length = l1) : (wotsFullDigits dig w l1 l2).length = l1 + l2 := by
  simp [wotsFullDigits, hLen, digitsOfBaseW_length]

/-! ## Checksum algebra -/

theorem wotsChecksumValue_add_sum_eq (w : ℕ) (digits : List ℕ)
    (hBound : ∀ d ∈ digits, d < w) :
    wotsChecksumValue w digits + digits.sum = digits.length * (w - 1) := by
  rw [wotsChecksumValue]
  induction digits with
  | nil => simp
  | cons d ds ih =>
    have hBound' : ∀ d' ∈ ds, d' < w := fun d' hd' => hBound d' (by simp [hd'])
    have h_ih := ih hBound'
    rw [List.map_cons, List.sum_cons, List.sum_cons]
    have hd_lt_w : d < w := hBound d (by simp)
    have hsub : (w - 1 - d) + d = w - 1 := by omega
    have h_all : (w - 1 - d) + (ds.map (fun d' => w - 1 - d')).sum + (d + ds.sum) =
        (w - 1) + ds.length * (w - 1) := by
      calc
        (w - 1 - d) + (ds.map (fun d' => w - 1 - d')).sum + (d + ds.sum)
            = ((w - 1 - d) + d) + ((ds.map (fun d' => w - 1 - d')).sum + ds.sum) := by
              simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = (w - 1) + ((ds.map (fun d' => w - 1 - d')).sum + ds.sum) := by rw [hsub]
        _ = (w - 1) + (ds.length * (w - 1)) := by rw [h_ih]
    rw [h_all]
    simp [List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- `Forall₂ (≤) (map f dig2) (map f dig1)` helper for the antitone lemma. -/
private theorem Forall₂_map_checksum_rev {dig1 dig2 : List ℕ} {w : ℕ}
    (hLE : Forall₂ (· ≤ ·) dig1 dig2)
    (hBound1 : ∀ d ∈ dig1, d < w) (hBound2 : ∀ d ∈ dig2, d < w) :
    Forall₂ (· ≤ ·) (dig2.map (fun d => w - 1 - d)) (dig1.map (fun d => w - 1 - d)) := by
  match dig1, dig2, hLE with
  | [], [], .nil => exact .nil
  | a :: as, b :: bs, .cons hd htl =>
    have ha_lt_w : a < w := hBound1 a (by simp)
    have hb_lt_w : b < w := hBound2 b (by simp)
    have h_rev : (w - 1 - b) ≤ (w - 1 - a) := by omega
    have h_tail := Forall₂_map_checksum_rev htl
      (fun d hd' => hBound1 d (by simp [hd']))
      (fun d hd' => hBound2 d (by simp [hd']))
    simpa using Forall₂.cons h_rev h_tail

theorem wotsChecksumValue_antitone {dig1 dig2 : List ℕ} {w : ℕ}
    (hLE : Forall₂ (· ≤ ·) dig1 dig2)
    (hBound1 : ∀ d ∈ dig1, d < w) (hBound2 : ∀ d ∈ dig2, d < w) :
    wotsChecksumValue w dig2 ≤ wotsChecksumValue w dig1 := by
  rw [wotsChecksumValue, wotsChecksumValue]
  exact (Forall₂_map_checksum_rev hLE hBound1 hBound2).sum_le_sum

theorem wotsChecksum_eq_imp_sum_eq {dig1 dig2 : List ℕ} {w : ℕ}
    (hLE : Forall₂ (· ≤ ·) dig1 dig2)
    (hBound1 : ∀ d ∈ dig1, d < w) (hBound2 : ∀ d ∈ dig2, d < w)
    (hCsumEq : wotsChecksumValue w dig1 = wotsChecksumValue w dig2) :
    dig1.sum = dig2.sum := by
  have hLenEq : dig1.length = dig2.length := hLE.length_eq
  have hIdent1 := wotsChecksumValue_add_sum_eq w dig1 hBound1
  have hIdent2 := wotsChecksumValue_add_sum_eq w dig2 hBound2
  rw [hLenEq] at hIdent1
  rw [hCsumEq] at hIdent1
  omega

/-! ## Main incomparability theorem -/

/-- If two full WOTS+ digit vectors (from message digits of common length `l1`, each digit
`< w`, with enough checksum room `l1·(w−1) < w^l2`) are pointwise `≤`, then the underlying
message-digit vectors are equal. -/
theorem wots_fullDigits_pointwiseLE_imp_dig_eq
    {dig1 dig2 : List ℕ} {w l1 l2 : ℕ}
    (hLen1 : dig1.length = l1) (hLen2 : dig2.length = l1)
    (hBound1 : ∀ d ∈ dig1, d < w) (hBound2 : ∀ d ∈ dig2, d < w)
    (hL2suff : l1 * (w - 1) < w ^ l2)
    (hLE : Forall₂ (· ≤ ·)
      (wotsFullDigits dig1 w l1 l2) (wotsFullDigits dig2 w l1 l2)) :
    dig1 = dig2 := by
  simp only [wotsFullDigits] at hLE
  have hlen_prefix : dig1.length = dig2.length := by rw [hLen1, hLen2]
  obtain ⟨hMsgLE, hcsLE⟩ := Forall₂.append_inv hLE hlen_prefix
  have hCsumGE : wotsChecksumValue w dig2 ≤ wotsChecksumValue w dig1 :=
    wotsChecksumValue_antitone hMsgLE hBound1 hBound2
  have hCsumLE : wotsChecksumValue w dig1 ≤ wotsChecksumValue w dig2 := by
    have hC1 : wotsChecksumValue w dig1 < w ^ l2 :=
      Nat.lt_of_le_of_lt (wotsChecksumValue_le hLen1 hBound1) hL2suff
    have hC2 : wotsChecksumValue w dig2 < w ^ l2 :=
      Nat.lt_of_le_of_lt (wotsChecksumValue_le hLen2 hBound2) hL2suff
    exact digitsOfBaseW_pointwiseLE_imp_le hC1 hC2 hcsLE
  have hCsumEq : wotsChecksumValue w dig1 = wotsChecksumValue w dig2 :=
    Nat.le_antisymm hCsumLE hCsumGE
  have hSumEq : dig1.sum = dig2.sum :=
    wotsChecksum_eq_imp_sum_eq hMsgLE hBound1 hBound2 hCsumEq
  exact Forall₂.eq_of_sum_eq hMsgLE hSumEq

/-- For distinct message-digit vectors, neither full WOTS+ digit vector is pointwise `≤` the
other: the WOTS+ encoding is incomparable, which is the combinatorial obstruction to
chain-advancing forgeries. -/
theorem wots_fullDigits_incomparable
    {dig1 dig2 : List ℕ} {w l1 l2 : ℕ}
    (hLen1 : dig1.length = l1) (hLen2 : dig2.length = l1)
    (hBound1 : ∀ d ∈ dig1, d < w) (hBound2 : ∀ d ∈ dig2, d < w)
    (hL2suff : l1 * (w - 1) < w ^ l2)
    (hNeq : dig1 ≠ dig2) :
    ¬ Forall₂ (· ≤ ·) (wotsFullDigits dig1 w l1 l2) (wotsFullDigits dig2 w l1 l2) ∧
    ¬ Forall₂ (· ≤ ·) (wotsFullDigits dig2 w l1 l2) (wotsFullDigits dig1 w l1 l2) := by
  refine ⟨fun h => hNeq ?_, fun h => hNeq ?_⟩
  · exact wots_fullDigits_pointwiseLE_imp_dig_eq hLen1 hLen2 hBound1 hBound2 hL2suff h
  · exact (wots_fullDigits_pointwiseLE_imp_dig_eq hLen2 hLen1 hBound2 hBound1 hL2suff h).symm

end SLHDSA.WotsChecksum
