/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.EncodedTargets

/-!
# Shared SLH-DSA encoder fixtures

The two bridges naming the tweak map each concrete bundle installs, and the one parameter profile
whose hypertree is too tall for SHA-2's compressed eight-byte tree field, together with the two
facts about that profile a ledger canary needs.

`HashSigTest.SLHDSA.EncodedTargets` and `HashSigTest.SLHDSA.WotsWitnesses` both pin the SHA-2
out-of-domain fallback on this profile — the first for XMSS internal-node targets, the second for
WOTS+ chain-step targets — so the profile and the fallback lemma live here rather than in two
copies that can drift apart.

Nothing here is a claim about an approved instantiation: the profile is deliberately outside the
approved address bounds, which is exactly what makes it separate the two encoders.
-/

public section

namespace SLHDSA.EncoderFixtures

open Security Concrete

/-! ## The tweak map each bundle installs -/

/-- The SHA-2 bundle's tweak map is the compressed `ADRSc` key map. -/
theorem adrsToKey_sha2 (p : Params) (a : Adrs) :
    (sha2Primitives p).adrsToKey a = sha2AdrsKey a := rfl

/-- The SHAKE bundle's tweak map is the plain address vector. -/
theorem adrsToKey_shake (p : Params) (a : Adrs) :
    (shakePrimitives p).adrsToKey a = Adrs.toVector a := rfl

/-! ## A profile SHA-2's compressed layout cannot hold

Ninety tree-index bits at layer zero: the canonical twelve-byte tree word holds them and the
compressed eight-byte one does not. -/

-- Exposed: both canary modules evaluate a tweak map at concrete addresses of this profile and
-- discharge its side conditions by `decide`, so its arithmetic has to reduce downstream.
/-- Eleven layers of height nine: ninety tree-index bits at layer zero. -/
@[expose] def deepParams : Params :=
  { n := 16, h := 99, d := 11, hp := 9, a := 12, k := 14, lgw := 4 }

/-- The validated form of `deepParams`. -/
@[expose] def deep : ValidatedParams := ⟨deepParams, by decide⟩

/-- Every index below `2 ^ 64 + 2` is a layer-zero tree index of this profile, whose layer-zero
trees carry ninety index bits. -/
theorem deep_tree_bound (t : ℕ) (ht : t < 2 ^ 64 + 2) : t < 2 ^ layerTreeHeight deep 0 := by
  have hle : (2 : ℕ) ^ 64 + 2 ≤ 2 ^ layerTreeHeight deep 0 := by
    rw [show layerTreeHeight deep 0 = 90 from by decide]
    norm_num
  omega

/-- Past the checked domain the SHA-2 key map returns the all-zero key — which is the genuine key
of the all-zero WOTS-hash address, not a sentinel. -/
theorem sha2AdrsKey_eq_zero_of_tree_overflow (a : Adrs) (ha : Adrs.Fits 8 a.tree = false) :
    sha2AdrsKey a = zeroBytes 22 := by
  unfold sha2AdrsKey Adrs.compressSha2Checked
  by_cases h1 : a.isCanonical = false
  · simp [h1]
  · by_cases h2 : Adrs.Fits 1 a.layer = false
    · simp [h1, h2]
    · simp [h1, h2, ha]

end SLHDSA.EncoderFixtures
