/-
Copyright (c) 2026 Vitalik Buterin, Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vitalik Buterin, Nicolas Consigny
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

/-!
# WOTS+ Checksum Incomparability

The combinatorial core of WOTS+ existential unforgeability: for any two distinct message-digit
vectors, the resulting full WOTS+ digit vectors (message digits followed by checksum digits) are
incomparable under the pointwise `≤` ordering. This is what blocks an attacker from forging a
signature by advancing every hash chain forward — increasing any message digit forces the
checksum to decrease, and equal checksums together with pointwise `≤` force equality.

This module is a standard-model statement over `List ℕ` / `ℕ`, independent of the oracle/hash
layer; the WOTS+ one-wayness reduction (in `HashSig.SLHDSA.Security`) consumes
`wots_fullDigits_incomparable` as its purely combinatorial ingredient.

See FIPS 205 §5 for the WOTS+ specification this validates.
-/


namespace SLHDSA.WotsChecksum

/-! ## Pointwise ordering on lists -/

variable {α β : Type}

/-- Pointwise relation: `Forall₂ R xs ys` means `xs` and `ys` have equal length
and corresponding elements are related by `R`. -/
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil  : Forall₂ R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

theorem Forall₂.length_eq {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : Forall₂ R xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Forall₂.sum_le {xs ys : List ℕ} (h : Forall₂ (· ≤ ·) xs ys) :
    xs.sum ≤ ys.sum := by
  induction h with
  | nil => exact Nat.le_refl 0
  | cons hd htl ih =>
    simp only [List.sum_cons]
    exact Nat.add_le_add hd ih

theorem Forall₂.eq_of_sum_eq {xs ys : List ℕ}
    (hLE : Forall₂ (· ≤ ·) xs ys) (hSum : xs.sum = ys.sum) : xs = ys := by
  match xs, ys, hLE with
  | [], [], .nil => rfl
  | a :: as, b :: bs, .cons hd htl =>
    simp only [List.sum_cons] at hSum
    have hSumLE : as.sum ≤ bs.sum := htl.sum_le
    by_cases hlt : a < b
    · have h1 : a + as.sum < b + as.sum := Nat.add_lt_add_right hlt as.sum
      have h2 : b + as.sum ≤ b + bs.sum := Nat.add_le_add_left hSumLE b
      have : a + as.sum < b + bs.sum := Nat.lt_of_lt_of_le h1 h2
      rw [hSum] at this
      exact absurd this (Nat.lt_irrefl _)
    · have hge : b ≤ a := Nat.ge_of_not_lt hlt
      have heq : a = b := Nat.le_antisymm hd hge
      subst heq
      have hSumAsEq : as.sum = bs.sum := Nat.add_left_cancel hSum
      have hAsEqBs : as = bs := Forall₂.eq_of_sum_eq htl hSumAsEq
      rw [hAsEqBs]

/-! ## Splitting `Forall₂` at equal-length prefixes -/

theorem Forall₂.take {xs ys : List α} {R : α → α → Prop}
    (h : Forall₂ R xs ys) (n : ℕ) : Forall₂ R (xs.take n) (ys.take n) := by
  induction h generalizing n with
  | nil => simpa using Forall₂.nil
  | cons hd htl ih =>
    cases n with
    | zero => simpa using Forall₂.nil
    | succ n => simpa using Forall₂.cons hd (ih n)

theorem Forall₂.drop {xs ys : List α} {R : α → α → Prop}
    (h : Forall₂ R xs ys) (n : ℕ) : Forall₂ R (xs.drop n) (ys.drop n) := by
  induction h generalizing n with
  | nil => simpa using Forall₂.nil
  | cons hd htl ih =>
    cases n with
    | zero => simpa using Forall₂.cons hd htl
    | succ n => simpa using ih n

theorem Forall₂.append_inv {R : α → α → Prop} {xs₁ xs₂ ys₁ ys₂ : List α}
    (h : Forall₂ R (xs₁ ++ ys₁) (xs₂ ++ ys₂))
    (hlen : xs₁.length = xs₂.length) :
    Forall₂ R xs₁ xs₂ ∧ Forall₂ R ys₁ ys₂ := by
  have take1 : (xs₁ ++ ys₁).take xs₁.length = xs₁ := by simp
  have drop1 : (xs₁ ++ ys₁).drop xs₁.length = ys₁ := by simp
  have take2 : (xs₂ ++ ys₂).take xs₂.length = xs₂ := by simp
  have drop2 : (xs₂ ++ ys₂).drop xs₂.length = ys₂ := by simp
  have htake := h.take xs₁.length
  rw [take1, hlen, take2] at htake
  have hdrop := h.drop xs₁.length
  rw [drop1, hlen, drop2] at hdrop
  exact ⟨htake, hdrop⟩

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

/-- The key modular identity: `n % w^(len+1) = ((n / w^len) % w) * w^len + n % w^len`. -/
theorem mod_pow_succ_extract (n w len : ℕ) (hw : 0 < w) :
    n % (w ^ (len + 1)) = ((n / w ^ len) % w) * w ^ len + n % w ^ len := by
  let M := w ^ len
  let MW := M * w
  let R := ((n / M) % w) * M + n % M
  let q := (n / M) / w
  have hMW_eq : MW = w ^ (len + 1) := by
    dsimp [MW, M]; rw [Nat.pow_succ]
  rw [← hMW_eq]
  have h_bound : R < MW := by
    dsimp [R, MW, M]
    have h1 : (n / (w ^ len)) % w < w := Nat.mod_lt (n / (w ^ len)) hw
    have h2 : n % (w ^ len) < w ^ len := Nat.mod_lt n (Nat.pow_pos (a := w) (n := len) hw)
    have hMpos : 0 < w ^ len := Nat.pow_pos (a := w) (n := len) hw
    have h_dle : (n / (w ^ len)) % w ≤ w - 1 := Nat.le_sub_one_of_lt h1
    have h_ble : n % (w ^ len) ≤ (w ^ len) - 1 := Nat.le_sub_one_of_lt h2
    have h_mul : ((n / (w ^ len)) % w) * (w ^ len) ≤ (w - 1) * (w ^ len) :=
      Nat.mul_le_mul h_dle (Nat.le_refl _)
    have h_sum_le : ((n / (w ^ len)) % w) * (w ^ len) + n % (w ^ len) ≤
        (w - 1) * (w ^ len) + ((w ^ len) - 1) :=
      Nat.add_le_add h_mul h_ble
    have h_final : (w - 1) * (w ^ len) + ((w ^ len) - 1) < (w ^ len) * w := by
      have h_sub_lt : (w ^ len) - 1 < w ^ len := Nat.sub_lt hMpos (by omega)
      have h_lt : (w - 1) * (w ^ len) + ((w ^ len) - 1) < (w - 1) * (w ^ len) + (w ^ len) :=
        Nat.add_lt_add_left h_sub_lt ((w - 1) * (w ^ len))
      have h_eq : (w - 1) * (w ^ len) + (w ^ len) = (w ^ len) * w := by
        calc
          (w - 1) * (w ^ len) + (w ^ len) = ((w - 1) + 1) * (w ^ len) := by rw [← Nat.succ_mul]
          _ = w * (w ^ len) := by rw [Nat.sub_add_cancel (Nat.one_le_of_lt hw)]
          _ = (w ^ len) * w := Nat.mul_comm _ _
      simpa [h_eq] using h_lt
    exact Nat.lt_of_le_of_lt h_sum_le h_final
  have h1 := Nat.div_add_mod n M
  have h2 := Nat.div_add_mod (n / M) w
  have h_n_eq : n = q * MW + R := by
    dsimp [R, MW, M, q]
    calc
      n = (w ^ len) * (n / (w ^ len)) + n % (w ^ len) := by rw [h1]
      _ = (w ^ len) * (w * ((n / (w ^ len)) / w) + (n / (w ^ len)) % w) + n % (w ^ len) := by
            rw [h2]
      _ = (w ^ len) * (w * ((n / (w ^ len)) / w)) + (w ^ len) * ((n / (w ^ len)) % w)
            + n % (w ^ len) := by rw [Nat.mul_add]
      _ = ((w ^ len) * w) * ((n / (w ^ len)) / w) + ((n / (w ^ len)) % w) * (w ^ len)
            + n % (w ^ len) := by
            rw [Nat.mul_assoc, Nat.mul_comm ((n / (w ^ len)) % w) (w ^ len)]
      _ = ((n / (w ^ len)) / w) * ((w ^ len) * w)
            + (((n / (w ^ len)) % w) * (w ^ len) + n % (w ^ len)) := by
            simp [Nat.mul_comm, Nat.add_comm, Nat.add_assoc]
  calc
    n % MW = (q * MW + R) % MW := by rw [h_n_eq]
    _ = R % MW := by simp
    _ = R := Nat.mod_eq_of_lt h_bound

theorem fromBaseW_digitsOfBaseW_eq_mod (n w len : ℕ) (hw : 0 < w) :
    fromBaseW w (digitsOfBaseW n w len) = n % (w ^ len) := by
  induction len generalizing n with
  | zero => simp [digitsOfBaseW, fromBaseW, Nat.mod_one]
  | succ len ih =>
    simp only [digitsOfBaseW, fromBaseW_cons, digitsOfBaseW_length n w len, ih n]
    rw [mod_pow_succ_extract n w len hw]

theorem fromBaseW_digitsOfBaseW_of_lt (n w len : ℕ) (hw : 0 < w)
    (h : n < w ^ len) : fromBaseW w (digitsOfBaseW n w len) = n := by
  rw [fromBaseW_digitsOfBaseW_eq_mod n w len hw]
  exact Nat.mod_eq_of_lt h

theorem digitsOfBaseW_pointwiseLE_imp_le {a b w len : ℕ} (hw : 0 < w)
    (ha : a < w ^ len) (hb : b < w ^ len)
    (hLE : Forall₂ (· ≤ ·) (digitsOfBaseW a w len) (digitsOfBaseW b w len)) :
    a ≤ b := by
  have ha' : fromBaseW w (digitsOfBaseW a w len) = a :=
    fromBaseW_digitsOfBaseW_of_lt a w len hw ha
  have hb' : fromBaseW w (digitsOfBaseW b w len) = b :=
    fromBaseW_digitsOfBaseW_of_lt b w len hw hb
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
    (h : ∀ x ∈ xs, x ≤ M) : xs.sum ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons]
    have hx : x ≤ M := h x (by simp)
    have hxs : ∀ y ∈ xs, y ≤ M := fun y hy => h y (by simp [hy])
    have ih' : xs.sum ≤ xs.length * M := ih hxs
    have h1 : x + xs.sum ≤ M + xs.sum := Nat.add_le_add_right hx xs.sum
    have h2 : M + xs.sum ≤ M + xs.length * M := Nat.add_le_add_left ih' M
    have h_eq : M + xs.length * M = (xs.length + 1) * M := by
      rw [Nat.succ_mul, Nat.add_comm]
    simp only [List.length_cons]
    rw [h_eq] at h2
    exact Nat.le_trans h1 h2

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
  exact (Forall₂_map_checksum_rev hLE hBound1 hBound2).sum_le

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
    (hw : 0 < w)
    (hLen1 : dig1.length = l1) (hLen2 : dig2.length = l1)
    (hBound1 : ∀ d ∈ dig1, d < w) (hBound2 : ∀ d ∈ dig2, d < w)
    (hL2suff : l1 * (w - 1) < w ^ l2)
    (hLE : Forall₂ (· ≤ ·)
      (wotsFullDigits dig1 w l1 l2) (wotsFullDigits dig2 w l1 l2)) :
    dig1 = dig2 := by
  simp only [wotsFullDigits] at hLE
  have hlen_prefix : dig1.length = dig2.length := by rw [hLen1, hLen2]
  obtain ⟨hMsgLE, hcsLE⟩ := hLE.append_inv hlen_prefix
  have hCsumGE : wotsChecksumValue w dig2 ≤ wotsChecksumValue w dig1 :=
    wotsChecksumValue_antitone hMsgLE hBound1 hBound2
  have hCsumLE : wotsChecksumValue w dig1 ≤ wotsChecksumValue w dig2 := by
    have hC1 : wotsChecksumValue w dig1 < w ^ l2 :=
      Nat.lt_of_le_of_lt (wotsChecksumValue_le hLen1 hBound1) hL2suff
    have hC2 : wotsChecksumValue w dig2 < w ^ l2 :=
      Nat.lt_of_le_of_lt (wotsChecksumValue_le hLen2 hBound2) hL2suff
    exact digitsOfBaseW_pointwiseLE_imp_le hw hC1 hC2 hcsLE
  have hCsumEq : wotsChecksumValue w dig1 = wotsChecksumValue w dig2 :=
    Nat.le_antisymm hCsumLE hCsumGE
  have hSumEq : dig1.sum = dig2.sum :=
    wotsChecksum_eq_imp_sum_eq hMsgLE hBound1 hBound2 hCsumEq
  exact hMsgLE.eq_of_sum_eq hSumEq

/-- For distinct message-digit vectors, neither full WOTS+ digit vector is pointwise `≤` the
other: the WOTS+ encoding is incomparable, which is the combinatorial obstruction to
chain-advancing forgeries. -/
theorem wots_fullDigits_incomparable
    {dig1 dig2 : List ℕ} {w l1 l2 : ℕ}
    (hw : 0 < w)
    (hLen1 : dig1.length = l1) (hLen2 : dig2.length = l1)
    (hBound1 : ∀ d ∈ dig1, d < w) (hBound2 : ∀ d ∈ dig2, d < w)
    (hL2suff : l1 * (w - 1) < w ^ l2)
    (hNeq : dig1 ≠ dig2) :
    ¬ Forall₂ (· ≤ ·) (wotsFullDigits dig1 w l1 l2) (wotsFullDigits dig2 w l1 l2) ∧
    ¬ Forall₂ (· ≤ ·) (wotsFullDigits dig2 w l1 l2) (wotsFullDigits dig1 w l1 l2) := by
  refine ⟨fun h => hNeq ?_, fun h => hNeq ?_⟩
  · exact wots_fullDigits_pointwiseLE_imp_dig_eq hw hLen1 hLen2 hBound1 hBound2 hL2suff h
  · exact (wots_fullDigits_pointwiseLE_imp_dig_eq hw hLen2 hLen1 hBound2 hBound1 hL2suff h).symm

end SLHDSA.WotsChecksum
