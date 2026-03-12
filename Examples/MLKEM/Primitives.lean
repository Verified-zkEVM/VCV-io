/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.MLKEM.Encoding

/-!
# ML-KEM Primitive Interfaces

This file keeps the hash, PRF, and XOF components abstract while exposing the semantic outputs that
the FIPS 203 pseudocode needs. The intent is to keep the spec executable once a concrete primitive
bundle is supplied, without committing to one implementation yet.
-/

set_option autoImplicit false

namespace MLKEM

/-- The primitive algorithms referenced by the ML-KEM specification. -/
structure Primitives (params : Params) (encoding : Encoding params) where
  /-- `G(d || k)` from K-PKE key generation, modeled as a pair of 32-byte seeds. -/
  gKeygen : Params → Seed32 → Seed32 × Seed32
  /-- `SampleNTT(ρ || j || i)` specialized to the chosen parameter set. -/
  sampleNTT : Seed32 → Fin params.k → Fin params.k → Tq
  /-- `PRF_η₁` followed by CBD sampling, specialized to output one polynomial. -/
  prfEta1 : Seed32 → ℕ → Rq
  /-- `PRF_η₂` followed by CBD sampling, specialized to output one polynomial. -/
  prfEta2 : Seed32 → ℕ → Rq
  /-- `G(m || H(ek))` from ML-KEM encapsulation/decapsulation. -/
  gEncaps : Message → PublicKeyHash → SharedSecret × Coins
  /-- `H(ek)` on the serialized public-key components. -/
  hEncapsulationKey : encoding.EncodedTHat → Seed32 → PublicKeyHash
  /-- `J(z || c)` used for implicit rejection on the serialized ciphertext components. -/
  jReject : Seed32 → encoding.EncodedU → encoding.EncodedV → SharedSecret

namespace Primitives

variable {params : Params} {encoding : Encoding params} (prims : Primitives params encoding)

/-- Reconstruct the public matrix `Â` from the public seed `ρ`. -/
def publicMatrix (rho : Seed32) : TqMatrix params.k params.k :=
  Vector.ofFn fun i => Vector.ofFn fun j => prims.sampleNTT rho j i

/-- Sample a length-`k` noise vector using `PRF_η₁` and an explicit counter offset. -/
def sampleVecEta1 (seed : Seed32) (offset : ℕ) : RqVec params.k :=
  Vector.ofFn fun i => prims.prfEta1 seed (offset + i.1)

/-- Sample a length-`k` noise vector using `PRF_η₂` and an explicit counter offset. -/
def sampleVecEta2 (seed : Seed32) (offset : ℕ) : RqVec params.k :=
  Vector.ofFn fun i => prims.prfEta2 seed (offset + i.1)

end Primitives

end MLKEM
