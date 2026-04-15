/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.OracleComp.Constructions.BitVec
import VCVio.ProgramLogic.Tactics.Relational
import VCVioWidgets.GameHop.Panel
import Mathlib.Data.Vector.Zip

/-!
# One Time Pad

This file defines the one-time pad scheme, proves correctness, and proves perfect secrecy
in the canonical independence form used by `SymmEncAlg.perfectSecrecyAt`.

The file includes two proof styles:
1. **Direct probability calculations** (`perfectSecrecyAt`): computes joint/marginal
   probabilities directly using `probOutput_pair_xor_uniform`.
2. **Relational / game-hopping** (`cipherGivenMsg_equiv`, `ciphertextRowsEqual`):
   proves that any two messages yield the same ciphertext distribution via a bijection
   coupling, using the `by_equiv` / `rvcstep` tactic workflow.
-/

show_panel_widgets [local VCVioWidgets.GameHop.GameHopPanel]

open Mathlib OracleSpec OracleComp ENNReal BigOperators

/-- The one-time pad symmetric encryption algorithm, using `BitVec`s as keys and messages.
Encryption and decryption both just apply `BitVec.xor` with the key. -/
def oneTimePad (sp : ℕ) :
    SymmEncAlg ProbComp (BitVec sp) (BitVec sp) (BitVec sp) where
  keygen := $ᵗ BitVec sp
  encrypt k m := return k ^^^ m
  decrypt k σ := return some (k ^^^ σ)

namespace oneTimePad

/-- Encryption and decryption are inverses for any OTP key. -/
lemma complete (sp : ℕ) : (oneTimePad sp).Complete := by
  intro msg
  have hsimp : (oneTimePad sp).CompleteExp msg =
      (fun _ : BitVec sp => (some msg : Option (BitVec sp))) <$>
        ($ᵗ BitVec sp : ProbComp (BitVec sp)) := by
    simp [SymmEncAlg.CompleteExp, oneTimePad, map_eq_bind_pure_comp, pure_bind, Function.comp]
  rw [hsimp, probOutput_eq_one_iff]
  exact ⟨HasEvalPMF.probFailure_eq_zero _,
    support_map_const (mx := ($ᵗ BitVec sp : ProbComp (BitVec sp))) (y := some msg)
      (by simp [support_uniformSample])⟩

lemma probOutput_cipher_uniform (sp : ℕ)
    (mgen : ProbComp (BitVec sp)) (σ : BitVec sp) :
    Pr[= σ | (oneTimePad sp).PerfectSecrecyCipherExp mgen] =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  simpa [SymmEncAlg.PerfectSecrecyCipherExp, SymmEncAlg.PerfectSecrecyExp, oneTimePad,
    map_eq_bind_pure_comp, bind_assoc, pure_bind] using
    probOutput_cipher_from_pair_uniform sp (mx := mgen) σ

/-- The one-time pad is perfectly secret in the canonical independence form. -/
lemma perfectSecrecyAt (sp : ℕ) : (oneTimePad sp).perfectSecrecyAt := by
  intro mgen msg σ
  have hpair :
      Pr[= (msg, σ) | (oneTimePad sp).PerfectSecrecyExp mgen] =
        Pr[= msg | mgen] *
          (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
    simpa [SymmEncAlg.PerfectSecrecyExp, oneTimePad,
      bind_assoc, pure_bind] using
      probOutput_pair_xor_uniform sp (mx := mgen) msg σ
  calc
    Pr[= (msg, σ) | (oneTimePad sp).PerfectSecrecyExp mgen] =
        Pr[= msg | mgen] *
          (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := hpair
    _ = Pr[= msg | mgen] *
        Pr[= σ | (oneTimePad sp).PerfectSecrecyCipherExp mgen] := by
          rw [probOutput_cipher_uniform]

/-- The one-time pad is perfectly secret for all security parameters. -/
lemma perfectSecrecy : ∀ sp, (oneTimePad sp).perfectSecrecyAt := perfectSecrecyAt

/-! ### Relational proof of ciphertext uniformity

Alternative proof that encrypting any two messages with a random OTP key yields
the same ciphertext distribution. Uses the bijection coupling `k ↦ k ⊕ m₀ ⊕ m₁`. -/

open OracleComp.ProgramLogic in
/-- Encrypting any two messages with a random OTP key yields the same distribution,
proved via a bijection coupling. -/
lemma cipherGivenMsg_equiv (sp : ℕ) (msg₀ msg₁ : BitVec sp) :
    GameEquiv
      ((oneTimePad sp).PerfectSecrecyCipherGivenMsgExp msg₀)
      ((oneTimePad sp).PerfectSecrecyCipherGivenMsgExp msg₁) := by
  simp only [SymmEncAlg.PerfectSecrecyCipherGivenMsgExp, oneTimePad]
  let c := msg₀ ^^^ msg₁
  have hxor : Function.Bijective (fun x : BitVec sp => x ^^^ c) :=
    Function.Involutive.bijective fun x => by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  change GameEquiv (($ᵗ BitVec sp) >>= fun k => pure (k ^^^ msg₀))
    (($ᵗ BitVec sp) >>= fun k => pure (k ^^^ msg₁))
  by_equiv
  rvcstep using (fun k₁ k₂ => k₂ = k₁ ^^^ c)
  swap
  · rvcstep
    · exact hxor
    · intro; rfl
  · intro k₁ k₂ hk
    subst hk
    apply Relational.relTriple_pure_pure
    change k₁ ^^^ msg₀ = k₁ ^^^ c ^^^ msg₁
    simp only [show c = msg₀ ^^^ msg₁ from rfl,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The one-time pad has equal ciphertext rows: all messages yield the same
ciphertext distribution. Derived from the relational `GameEquiv` proof above. -/
@[game_hop_root]
lemma ciphertextRowsEqual (sp : ℕ) : (oneTimePad sp).ciphertextRowsEqualAt :=
  fun msg₀ msg₁ σ => (cipherGivenMsg_equiv sp msg₀ msg₁).probOutput_eq σ

end oneTimePad
