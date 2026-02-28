/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.OracleComp.Constructions.BitVec
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
