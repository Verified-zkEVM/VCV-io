/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Wots

/-!
# WOTS+ Message-Encoding Injectivity

The full-width WOTS+ message encoding of FIPS 205 Algorithms 7 and 8 (lines 1–7) determines the
node being signed, and any two distinct nodes have a chain on which the first node's step count
is strictly smaller than the second's.

Two facts combine here. `WotsEncoding.base2b_msg_injective` shows that under the alignment
obligation `lgw ∣ 8n` of `Params.Valid` the `len1` message digits lose no bit of the `n`-byte
message; `CorePrimitives.ByteLaws` transports that from the byte encoding to the abstract node
carrier `core.Y`. `WotsChecksum.wots_fullDigits_incomparable` is the purely combinatorial
statement that distinct message-digit vectors yield pointwise-incomparable full digit vectors.
Together they give `chainLengthsCore_incomparable` and its index-wise form
`chainStepsCore_two_encodings`: for `msg ≠ msg'` some chain index `i < len` has
`chainStepsCore core msg i < chainStepsCore core msg' i`. That statement is the Lean
counterpart of the `two_encodings` axiom of the EasyCrypt SPHINCS+ proof (`WOTS_TW_ES.ec`),
which is the only fact about the message encoding that proof assumes; here it is proved for the
concrete FIPS 205 encoding, under `p.Valid` and `core.ByteLaws`.

## References

- NIST FIPS 205, §5.2–5.3 (Algorithms 7 and 8)
-/

public section

namespace SLHDSA

open WotsChecksum
open WotsEncoding

variable {p : Params} {core : CorePrimitives p}

/-- Full-width message-encoding injectivity: under the alignment obligation of `Params.Valid`
and byte coherence of the node carrier, the `len1` message digits determine the node. -/
theorem wotsMsgDigitsCore_injective (valid : p.Valid) (laws : core.ByteLaws) :
    Function.Injective (wotsMsgDigitsCore core) := by
  intro x y h
  have h' : base2b (core.yToBytes x).toList p.lgw p.len1 =
      base2b (core.yToBytes y).toList p.lgw p.len1 := h
  exact laws.yToBytes_injective (base2b_msg_injective valid h')

/-- The complete `len`-digit chain-length vector (message digits followed by the FIPS checksum
digits) determines the node. -/
theorem chainLengthsCore_injective (valid : p.Valid) (laws : core.ByteLaws) :
    Function.Injective (chainLengthsCore core) :=
  (fullDigits_injective p).comp (wotsMsgDigitsCore_injective valid laws)

/-- Distinct nodes have pointwise-incomparable chain-length vectors: neither is pointwise `≤`
the other. This combines `wotsMsgDigitsCore_injective` (distinct nodes have distinct message
digits) with `WotsChecksum.wots_fullDigits_incomparable`. -/
theorem chainLengthsCore_incomparable (valid : p.Valid) (laws : core.ByteLaws)
    {msg msg' : core.Y} (hne : msg ≠ msg') :
    ¬ Forall₂ (· ≤ ·) (chainLengthsCore core msg) (chainLengthsCore core msg') ∧
    ¬ Forall₂ (· ≤ ·) (chainLengthsCore core msg') (chainLengthsCore core msg) := by
  simp only [chainLengthsCore_eq_wotsFullDigits valid]
  exact wots_fullDigits_incomparable (Params.w_pos p)
    (wotsMsgDigitsCore_length core msg) (wotsMsgDigitsCore_length core msg')
    (wotsMsgDigitsCore_mem_lt core msg) (wotsMsgDigitsCore_mem_lt core msg')
    valid.len1_mul_pred_w_lt_pow_len2
    (fun h => hne ((wotsMsgDigitsCore_injective valid laws) h))

/-- Two distinct nodes have a chain index at which the first node's step count is strictly
smaller than the second's. This is the combinatorial ingredient a WOTS+ unforgeability
reduction consumes: a forger who only advances the honest signer's chains cannot reach the
encoding of a different message. It is the index-wise reading of the second conjunct of
`chainLengthsCore_incomparable`, and the Lean counterpart of the EasyCrypt `two_encodings`
axiom. -/
theorem chainStepsCore_two_encodings (valid : p.Valid) (laws : core.ByteLaws)
    {msg msg' : core.Y} (hne : msg ≠ msg') :
    ∃ i, i < p.len ∧ chainStepsCore core msg i < chainStepsCore core msg' i := by
  by_contra hnot
  have hle : ∀ i, i < p.len → chainStepsCore core msg' i ≤ chainStepsCore core msg i :=
    fun i hi => Nat.le_of_not_lt fun hlt => hnot ⟨i, hi, hlt⟩
  exact (chainLengthsCore_incomparable valid laws hne).2
    (Forall₂.of_getD 0 (by simp) fun i hi => hle i (by simpa using hi))

end SLHDSA
