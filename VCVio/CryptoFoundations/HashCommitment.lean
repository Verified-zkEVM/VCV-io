/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
import VCVio.CryptoFoundations.CommitmentScheme
import VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Hash-Based Commitment Schemes — Binding via Collision Resistance

Hash-based commitment scheme construction and the standard-model reduction
from binding to keyed collision resistance.

Given a keyed hash family `H : KeyedHashFamily K (M × S) C`, the scheme
`H.toCommitment` commits to `m : M` by sampling a uniform opening `s : S` and
returning `(H k (m, s), s)`. Verification recomputes the hash and compares.

A binding adversary outputting two openings `(c, m₁, s₁, m₂, s₂)` with
`m₁ ≠ m₂` and both verifications passing yields a keyed-CR collision at
`(m₁, s₁) ≠ (m₂, s₂)` with `H k (m₁, s₁) = c = H k (m₂, s₂)`. Bound:
`bindingAdvantage H.toCommitment A ≤ keyedCRAdvantage H (bindingAdv_toCRAdv A)`.

This is the standard-model layer of the
[#284](https://github.com/Verified-zkEVM/VCV-io/issues/284) consolidation
chain `binding ≤ keyed-CR ≤ birthday`.

## Main Definitions

- `KeyedHashFamily.toCommitment` — hash-based commitment scheme.
- `bindingAdv_toCRAdv` — reduction adversary from binding to keyed-CR.
- `bindingAdvantage_toCommitment_le_keyedCRAdvantage` — the binding bound.
-/


open OracleComp OracleSpec ENNReal CommitmentScheme

namespace CollisionResistance

variable {K M S C : Type}

/-- Hash-based commitment scheme: commit to `m` by sampling a uniform opening
`s ← $ᵗ S` and returning `(H k (m, s), s)`. Verification recomputes the hash
and compares to the committed value. -/
def KeyedHashFamily.toCommitment
    [SampleableType S] [DecidableEq C]
    (H : KeyedHashFamily K (M × S) C) : CommitmentScheme K M C S where
  setup := H.keygen
  commit k m := do
    let s ← $ᵗ S
    return (H.hash k (m, s), s)
  verify k m c s := decide (H.hash k (m, s) = c)

/-- Reduction adversary: a binding adversary against `H.toCommitment` becomes
a keyed-CR adversary against `H` by forgetting the commitment value and
forwarding the two opening pairs `((m₁, s₁), (m₂, s₂))`. -/
def bindingAdv_toCRAdv (A : BindingAdv K M C S) : KeyedCRAdversary K (M × S) :=
  fun k => do
    let (_c, m₁, s₁, m₂, s₂) ← A k
    return ((m₁, s₁), (m₂, s₂))

/-- **Binding ≤ keyed-CR (standard model)**: for any binding adversary `A`
against the hash-based commitment scheme `H.toCommitment`, the binding
advantage is bounded by the keyed-CR advantage of `H` against the natural
reduction adversary `bindingAdv_toCRAdv A`.

A binding-game win has `m₁ ≠ m₂` together with both openings verifying:
`H k (m₁, s₁) = c = H k (m₂, s₂)`. Since `m₁ ≠ m₂` implies
`(m₁, s₁) ≠ (m₂, s₂)`, this is exactly a keyed-CR win for the reduction
adversary, by transitivity through the common commitment `c`. -/
theorem bindingAdvantage_toCommitment_le_keyedCRAdvantage
    [SampleableType S] [DecidableEq M] [DecidableEq S] [DecidableEq C]
    (H : KeyedHashFamily K (M × S) C) (A : BindingAdv K M C S) :
    bindingAdvantage H.toCommitment A ≤
      keyedCRAdvantage H (bindingAdv_toCRAdv A) := by
  unfold bindingAdvantage CommitmentScheme.bindingExp
    keyedCRAdvantage keyedCRExp bindingAdv_toCRAdv KeyedHashFamily.toCommitment
  simp only [monad_norm]
  refine probOutput_bind_mono fun k _ => ?_
  refine probOutput_bind_mono fun ⟨c, m₁, s₁, m₂, s₂⟩ _ => ?_
  grind

end CollisionResistance
