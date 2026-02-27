/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.EvalDist.BitVec
import Mathlib.Data.Vector.Zip

/-!
# One Time Pad

This file defines the one-time pad scheme, proves correctness, and proves perfect secrecy
in the canonical independence form used by `SymmEncAlg.perfectSecrecy`.
-/

open Mathlib OracleSpec OracleComp ENNReal BigOperators

/-- The one-time pad symmetric encryption algorithm, using `BitVec`s as keys and messages.
Encryption and decryption both just apply `BitVec.xor` with the key.
The only oracles needed are `unifSpec`, which requires no implementation. -/
@[simps!] def oneTimePad : SymmEncAlg ℕ
    (M := BitVec) (K := BitVec) (C := BitVec) where
  keygen n := do $ᵗ BitVec n -- Generate a key by choosing a random bit-vector
  encrypt k m := return k ^^^ m -- encrypt by xor-ing with the key
  decrypt k σ := return (k ^^^ σ) -- decrypt by xor-ing with the key
  __ := unifSpec.defaultContext

namespace oneTimePad

/-- Encryption and decryption are inverses for any OTP key. -/
lemma complete : (oneTimePad).Complete := by
  simp [oneTimePad, SymmEncAlg.Complete, SymmEncAlg.CompleteExp]

lemma probOutput_xor_uniform (sp : ℕ) (msg σ : BitVec sp) :
    Pr[= σ | (fun k : BitVec sp => k ^^^ msg) <$> ($ᵗ BitVec sp)] =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[= σ | (fun k : BitVec sp => k ^^^ msg) <$> ($ᵗ BitVec sp)] =
        Pr[= σ | (msg ^^^ ·) <$> ($ᵗ BitVec sp)] := by
          simp [BitVec.xor_comm]
    _ = Pr[= msg ^^^ σ | ($ᵗ BitVec sp)] := by
          simpa using probOutput_xor_map (mx := ($ᵗ BitVec sp)) (x := msg) (y := σ)
    _ = (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
          simp [probOutput_uniformSample]

lemma probOutput_pair_xor_uniform (sp : ℕ) (mx : ProbComp (BitVec sp))
    (msg σ : BitVec sp) :
    Pr[= (msg, σ) | do
      let msg' ← mx
      let k ← $ᵗ BitVec sp
      return (msg', k ^^^ msg')] =
      Pr[= msg | mx] * (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  let inv : ℝ≥0∞ := (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹
  rw [probOutput_bind_eq_tsum]
  have hinner (msg' : BitVec sp) :
      Pr[= (msg, σ) | do
        let k ← $ᵗ BitVec sp
        return (msg', k ^^^ msg')] = if msg = msg' then inv else 0 := by
    calc
      Pr[= (msg, σ) | do
        let k ← $ᵗ BitVec sp
        return (msg', k ^^^ msg')] =
          Pr[= (msg, σ) | (msg', ·) <$> ((fun k : BitVec sp => k ^^^ msg') <$> ($ᵗ BitVec sp))] := by
            simp
      _ = if msg = msg' then
          Pr[= σ | (fun k : BitVec sp => k ^^^ msg') <$> ($ᵗ BitVec sp)] else 0 := by
            simpa using
              (probOutput_prod_mk_snd_map
                (my := (fun k : BitVec sp => k ^^^ msg') <$> ($ᵗ BitVec sp))
                (x := msg') (z := (msg, σ)))
      _ = if msg = msg' then inv else 0 := by
            by_cases h : msg = msg' <;> simp [h, inv, probOutput_xor_uniform]
  simp_rw [hinner]
  calc
    ∑' msg', Pr[= msg' | mx] * (if msg = msg' then inv else 0) =
        ∑' msg', (Pr[= msg' | mx] * (if msg = msg' then 1 else 0)) * inv := by
          refine tsum_congr fun msg' => ?_
          by_cases h : msg = msg' <;> simp [h, inv, mul_comm]
    _ = (∑' msg', Pr[= msg' | mx] * (if msg = msg' then 1 else 0)) * inv := by
          rw [ENNReal.tsum_mul_right]
    _ = Pr[= msg | mx] * inv := by
          have hsum :
              ∑' msg', Pr[= msg' | mx] * (if msg = msg' then 1 else 0) =
                Pr[= msg | mx] := by
            simp
          rw [hsum]

lemma probOutput_cipher_from_pair_uniform (sp : ℕ) (mx : ProbComp (BitVec sp))
    (σ : BitVec sp) :
    Pr[= σ | do
      let msg' ← mx
      let k ← $ᵗ BitVec sp
      return (k ^^^ msg')] =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_bind_of_const (mx := mx)
    (y := σ) (r := (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹)]
  · simp
  · intro msg hmsg
    simpa using probOutput_xor_uniform sp msg σ

lemma probOutput_cipher_uniform (sp : ℕ)
    (mgen : OracleComp oneTimePad.spec (BitVec sp)) (σ : BitVec sp) :
    Pr[= σ | oneTimePad.PerfectSecrecyCipherExp sp mgen] =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  simpa [SymmEncAlg.PerfectSecrecyCipherExp, SymmEncAlg.PerfectSecrecyExp, oneTimePad] using
    probOutput_cipher_from_pair_uniform sp (mx := simulateQ oneTimePad.impl mgen) σ

/-- The one-time pad is perfectly secret in the canonical independence form. -/
lemma perfectSecrecyAt (sp : ℕ) : oneTimePad.perfectSecrecyAt sp := by
  intro mgen msg σ
  have hpair :
      Pr[= (msg, σ) | oneTimePad.PerfectSecrecyExp sp mgen] =
        Pr[= msg | oneTimePad.PerfectSecrecyPriorExp sp mgen] *
          (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
    simpa [SymmEncAlg.PerfectSecrecyExp, SymmEncAlg.PerfectSecrecyPriorExp, oneTimePad] using
      probOutput_pair_xor_uniform sp (mx := simulateQ oneTimePad.impl mgen) msg σ
  calc
    Pr[= (msg, σ) | oneTimePad.PerfectSecrecyExp sp mgen] =
        Pr[= msg | oneTimePad.PerfectSecrecyPriorExp sp mgen] *
          (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := hpair
    _ = Pr[= msg | oneTimePad.PerfectSecrecyPriorExp sp mgen] *
        Pr[= σ | oneTimePad.PerfectSecrecyCipherExp sp mgen] := by
          rw [probOutput_cipher_uniform]

/-- The one-time pad is perfectly secret for all security parameters. -/
lemma perfectSecrecy : oneTimePad.perfectSecrecy := by
  intro sp
  exact perfectSecrecyAt sp

end oneTimePad
