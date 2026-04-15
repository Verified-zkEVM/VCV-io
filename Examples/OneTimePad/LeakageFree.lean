/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.OneTimePad.Basic
import VCVio.ProgramLogic.Relational.Leakage

/-!
# OTP Side-Channel Leakage Analysis

This file proves that the one-time pad is leak-free under a constant-time observation model.

The OTP is instrumented automatically via `QueryImpl.withCost` (see the docstring on
`QueryImpl.withCost` for the general pattern). The cost function `fun _ => ()` encodes
the constant-time model: every oracle query is indistinguishable to the observer.

## Main Definitions

* `oneTimePad.tracedEncrypt`: the auto-instrumented OTP encryption.

## Main Results

* `oneTimePad.otp_traceNoninterference`: exact trace noninterference for any two messages.
* `oneTimePad.otp_probLeakFree`: distributional trace independence.
* `oneTimePad.otp_traceNoninterference_post`: compositionality under post-processing.
-/

open OracleSpec OracleComp ENNReal

namespace oneTimePad

/-- The OTP encryption experiment: sample a key and encrypt the message.
This is the standard `keygen ∘ encrypt` pipeline from the `SymmEncAlg` structure. -/
def encryptMsg (sp : ℕ) (msg : BitVec sp) : ProbComp (BitVec sp) := do
  let key ← (oneTimePad sp).keygen
  (oneTimePad sp).encrypt key msg

/-- Auto-instrumented OTP encryption via `QueryImpl.withCost`. Every oracle query
(here, just the uniform key sample) emits a `Unit` trace event. No manual `observe()`
calls are needed. -/
def tracedEncrypt (sp : ℕ) (msg : BitVec sp) : ProbComp (BitVec sp × Unit) :=
  (simulateQ ((QueryImpl.id' unifSpec).withCost (fun _ => ())) (encryptMsg sp msg)).run

/-- The traced encryption reduces to a simple form: sample a key uniformly,
XOR with the message, and pair with the trivial `()` trace. -/
theorem tracedEncrypt_eq (sp : ℕ) (msg : BitVec sp) :
    tracedEncrypt sp msg = do
      let key ← $ᵗ BitVec sp
      return (key ^^^ msg, ()) := by
  simp [tracedEncrypt, encryptMsg, oneTimePad]

/-- The traced OTP satisfies exact trace noninterference: encrypting any two messages
produces identical observation traces. -/
theorem otp_traceNoninterference (sp : ℕ) (msg₀ msg₁ : BitVec sp) :
    Leakage.TraceNoninterference (tracedEncrypt sp msg₀) (tracedEncrypt sp msg₁) := by
  simp only [tracedEncrypt_eq]
  unfold Leakage.TraceNoninterference
  rw [ProgramLogic.Relational.relTriple'_iff_relTriple]
  refine ProgramLogic.Relational.relTriple_bind
    (ProgramLogic.Relational.relTriple_refl ($ᵗ BitVec sp)) fun _ _ _ => ?_
  exact ProgramLogic.Relational.relTriple_pure_pure rfl

/-- The traced OTP is probabilistically leak-free: the trace distribution is independent
of the encrypted message. -/
theorem otp_probLeakFree (sp : ℕ) (msg₀ msg₁ : BitVec sp) :
    Leakage.ProbLeakFree (tracedEncrypt sp msg₀) (tracedEncrypt sp msg₁) :=
  Leakage.traceNoninterference_implies_probLeakFree (otp_traceNoninterference sp msg₀ msg₁)

/-- Compositionality: post-processing the ciphertext preserves trace noninterference. -/
theorem otp_traceNoninterference_post {γ : Type} (sp : ℕ) (msg₀ msg₁ : BitVec sp)
    (f₁ f₂ : BitVec sp → γ) :
    Leakage.TraceNoninterference
      (Prod.map f₁ id <$> tracedEncrypt sp msg₀)
      (Prod.map f₂ id <$> tracedEncrypt sp msg₁) :=
  Leakage.traceNoninterference_map_fst (otp_traceNoninterference sp msg₀ msg₁) f₁ f₂

end oneTimePad
