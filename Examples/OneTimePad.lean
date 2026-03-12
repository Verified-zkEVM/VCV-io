/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.OracleComp.Constructions.BitVec
import VCVio.ProgramLogic.Tactics
import VCVioWidgets.GameHop.Panel
import Mathlib.Data.Vector.Zip

/-!
# One Time Pad

This file defines the one-time pad scheme, proves correctness, and proves perfect secrecy
in the canonical independence form used by `SymmEncAlg.perfectSecrecy`.

The file includes two proof styles:
1. **Direct probability calculations** (`perfectSecrecyAt`): computes joint/marginal
   probabilities directly using `probOutput_pair_xor_uniform`.
2. **Relational / game-hopping** (`cipherGivenMsg_equiv`, `ciphertextRowsEqual`):
   proves that any two messages yield the same ciphertext distribution via a bijection
   coupling, using the `by_equiv` / `rvcgen_step` tactic workflow.
-/

show_panel_widgets [local VCVioWidgets.GameHop.GameHopPanel]

open Mathlib OracleSpec OracleComp ENNReal BigOperators
open VCVioWidgets.GameHop

/-- Source-backed GameHop diagram metadata for the OTP proof.
Placed near the top of the file so the infoview can render it without waiting for
the entire proof file to elaborate. -/
def oneTimePadGameHopDiagram : GameDiagram := {
  title := "One-time pad: relational hop"
  subtitle := .moduleDoc
  layout := .sequenceWithSideEdges
  mainPath := #["msg0", "msg1", "rows"]
  nodes := #[
    { id := "msg0"
      kind := .game
      title := "Cipher game for msg₀"
      anchor? := some (AnchorRef.defn `SymmEncAlg.PerfectSecrecyCipherGivenMsgExp)
      snippets := #[
        .declSource `SymmEncAlg.PerfectSecrecyCipherGivenMsgExp
      ] }
    , { id := "msg1"
        kind := .game
        title := "Cipher game for msg₁"
        anchor? := some (AnchorRef.defn `SymmEncAlg.PerfectSecrecyCipherGivenMsgExp)
        snippets := #[
          .declSource `SymmEncAlg.PerfectSecrecyCipherGivenMsgExp
        ] }
    , { id := "rows"
        kind := .result
        title := "Equal ciphertext rows"
        anchor? := some (AnchorRef.result `oneTimePad.ciphertextRowsEqual)
        snippets := #[
          .declSignature `oneTimePad.ciphertextRowsEqual
        ] }
  ]
  edges := #[
    { source := "msg0"
      target := "msg1"
      kind := .equivalence
      label := "GameEquiv"
      detail? := some "Couple keys by the bijection `k ↦ k ⊕ msg₀ ⊕ msg₁`."
      anchor? := some (AnchorRef.thm `oneTimePad.cipherGivenMsg_equiv) }
    , { source := "msg1"
        target := "rows"
        kind := .consequence
        label := "probOutput_eq"
        detail? := some "Turn the equivalence into equality of ciphertext output probabilities."
        anchor? := some (AnchorRef.result `oneTimePad.ciphertextRowsEqual)
        notes := #[
          { label := "separate direct proof"
            detail? := some "`perfectSecrecyAt` is proved independently via probability identities."
            anchor? := some (AnchorRef.result `oneTimePad.perfectSecrecyAt) }
        ] }
  ]
}

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

/-! ### Relational proof of ciphertext uniformity

Alternative proof that encrypting any two messages with a random OTP key yields
the same ciphertext distribution. Uses the bijection coupling `k ↦ k ⊕ m₀ ⊕ m₁`. -/

open OracleComp.ProgramLogic in
/-- Encrypting any two messages with a random OTP key yields the same distribution,
proved via a bijection coupling. -/
lemma cipherGivenMsg_equiv (sp : ℕ) (msg₀ msg₁ : BitVec sp) :
    GameEquiv
      (oneTimePad.PerfectSecrecyCipherGivenMsgExp sp msg₀)
      (oneTimePad.PerfectSecrecyCipherGivenMsgExp sp msg₁) := by
  simp only [SymmEncAlg.PerfectSecrecyCipherGivenMsgExp, oneTimePad, simulateQ_id']
  let c := msg₀ ^^^ msg₁
  show GameEquiv (($ᵗ BitVec sp) >>= fun k => pure (k ^^^ msg₀))
    (($ᵗ BitVec sp) >>= fun k => pure (k ^^^ msg₁))
  by_equiv
  rvcgen_step using (fun k₁ k₂ => k₂ = k₁ ^^^ c)
  swap
  · rvcgen_step using (· ^^^ c)
    · exact Function.Involutive.bijective fun x => by
        rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    · intro; rfl
  · intro k₁ k₂ hk
    subst hk
    apply Relational.relTriple_pure_pure
    show k₁ ^^^ msg₀ = k₁ ^^^ c ^^^ msg₁
    simp only [show c = msg₀ ^^^ msg₁ from rfl,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The one-time pad has equal ciphertext rows: all messages yield the same
ciphertext distribution. Derived from the relational `GameEquiv` proof above. -/
lemma ciphertextRowsEqual (sp : ℕ) : oneTimePad.ciphertextRowsEqualAt sp :=
  fun msg₀ msg₁ σ => (cipherGivenMsg_equiv sp msg₀ msg₁).probOutput_eq σ

end oneTimePad
