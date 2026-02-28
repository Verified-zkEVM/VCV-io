/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.BitVec
import VCVio.EvalDist.Prod

/-!
# Probability lemmas for uniform `BitVec` sampling

Lemmas about `probOutput` for `ProbComp (BitVec n)` computations involving XOR with
uniformly sampled keys. These are reusable building blocks for encryption proofs
(e.g., one-time pad privacy).
-/

open OracleSpec OracleComp ENNReal

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
