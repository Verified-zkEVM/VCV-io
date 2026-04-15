/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.ProgramLogic.Relational.Leakage
import VCVio.OracleComp.Constructions.BitVec

/-!
# OTP Side-Channel Leakage Analysis

This file demonstrates the leakage framework by proving that the one-time pad encryption
is leak-free under a constant-time observation model.

The observation model captures what a side-channel attacker can see during encryption:
only the fact that a single XOR operation occurred, not the values involved.
This is the formal analogue of "constant-time" execution.

## Main Results

* `otp_traceNoninterference`: the observed OTP satisfies exact trace noninterference.
  Changing the message does not change the observation trace.
* `otp_probLeakFree`: derived from `otp_traceNoninterference` via
  `traceNoninterference_implies_probLeakFree`. The trace distribution is
  independent of the message.
* `otp_traceNoninterference_post`: compositionality: post-processing the ciphertext
  (e.g., hashing) preserves trace noninterference.
-/

open OracleSpec OracleComp ENNReal

namespace OneTimePadLeakage

/-- OTP encryption with constant-time observation trace. The ciphertext is `key ⊕ msg`
where `key` is sampled uniformly; the trace component is `()`, modeling an
implementation where only the occurrence of the XOR (not its operands) is visible. -/
def otpConstantTime (sp : ℕ) (msg : BitVec sp) : ProbComp (BitVec sp × Unit) := do
  let key ← $ᵗ BitVec sp
  return (key ^^^ msg, ())

/-- The OTP satisfies exact trace noninterference: encrypting any two messages
produces identical observation traces. -/
theorem otp_traceNoninterference (sp : ℕ) (msg₀ msg₁ : BitVec sp) :
    Leakage.TraceNoninterference (otpConstantTime sp msg₀) (otpConstantTime sp msg₁) := by
  unfold Leakage.TraceNoninterference otpConstantTime
  rw [ProgramLogic.Relational.relTriple'_iff_relTriple]
  refine ProgramLogic.Relational.relTriple_bind
    (ProgramLogic.Relational.relTriple_refl ($ᵗ BitVec sp)) fun _ _ _ => ?_
  exact ProgramLogic.Relational.relTriple_pure_pure rfl

/-- The OTP is probabilistically leak-free: the trace distribution is independent
of the encrypted message. Derived from `otp_traceNoninterference`. -/
theorem otp_probLeakFree (sp : ℕ) (msg₀ msg₁ : BitVec sp) :
    Leakage.ProbLeakFree (otpConstantTime sp msg₀) (otpConstantTime sp msg₁) :=
  Leakage.traceNoninterference_implies_probLeakFree (otp_traceNoninterference sp msg₀ msg₁)

/-- Compositionality: post-processing the ciphertext preserves trace noninterference.
For example, hashing the ciphertext before sending it does not introduce leakage. -/
theorem otp_traceNoninterference_post {γ : Type} (sp : ℕ) (msg₀ msg₁ : BitVec sp)
    (f₁ f₂ : BitVec sp → γ) :
    Leakage.TraceNoninterference
      (Prod.map f₁ id <$> otpConstantTime sp msg₀)
      (Prod.map f₂ id <$> otpConstantTime sp msg₁) :=
  Leakage.traceNoninterference_map_fst (otp_traceNoninterference sp msg₀ msg₁) f₁ f₂

end OneTimePadLeakage
