/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Skas
-/

module
public import LatticeCrypto.Ring.Transform
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Uniform Sampling On Negacyclic Ring Carriers

`SampleableType` instances for the generic lattice ring layer, so that `$ᵗ ring.Poly`
and `$ᵗ (TransformPoly ring)` elaborate for every bundled ring whose coefficient type is
itself sampleable:

- `PolyBackend.instSampleableTypePoly`: uniform sampling on a backend carrier, obtained
  by sampling each coefficient independently and rebuilding through `PolyBackend.build`.
  The transport is `PolyBackend.equivPi`, so the sampled distribution is uniform on the
  carrier whenever the coefficient sampler is uniform.
- `TransformPoly.instSampleableType`: the same distribution pushed through the
  transform-domain tag `TransformPoly.equivPoly`.

Because `PolyVec` and `PolyMatrix` are `Vector` abbreviations, the vector and matrix
carriers of every scheme (`RqVec`, `TqVec`, `TqMatrix`, …) become sampleable through the
framework's `Vector` instance with no further scheme-level declarations.

The instances are stated on the semantic carrier `backend.Poly`, so they apply to a
scheme alias such as `MLKEM.Rq := coeffRing.Poly` without unfolding the bundled ring
(`vectorNegacyclicRing` is deliberately not reducible). A scheme only has to make its
coefficient type sampleable — for `ZMod modulus` that is a `NeZero modulus` instance.

The file lives outside `LatticeCrypto.Ring.Kernel` so the rest of the ring layer stays
free of the `VCVio` oracle-computation imports.
-/

@[expose] public section

namespace LatticeCrypto

/-- Uniform sampling on a backend carrier: sample a coefficient function uniformly and
rebuild it through `PolyBackend.build`. -/
instance PolyBackend.instSampleableTypePoly {Coeff : Type} [SampleableType Coeff]
    (backend : PolyBackend Coeff) : SampleableType backend.Poly :=
  SampleableType.ofEquiv backend.equivPi.symm

/-- Uniform sampling on the transform-domain carrier, transported from the underlying
coefficient-domain carrier along `TransformPoly.equivPoly`. -/
instance TransformPoly.instSampleableType {Coeff : Type} [CommRing Coeff]
    [SampleableType Coeff] (ring : NegacyclicRing Coeff) :
    SampleableType (TransformPoly ring) :=
  SampleableType.ofEquiv (TransformPoly.equivPoly ring).symm

/-- Every carrier element is sampled with probability `card⁻¹`. -/
theorem PolyBackend.probOutput_uniformSample_eq_inv_card {Coeff : Type} [SampleableType Coeff]
    [Fintype Coeff] (backend : PolyBackend Coeff) (p : backend.Poly) :
    Pr[= p | $ᵗ backend.Poly] = (Fintype.card backend.Poly : ENNReal)⁻¹ :=
  probOutput_uniformSample backend.Poly p

/-- Every transform-domain element is sampled with probability `card⁻¹`. -/
theorem TransformPoly.probOutput_uniformSample_eq_inv_card {Coeff : Type} [CommRing Coeff]
    [SampleableType Coeff] [Fintype Coeff] (ring : NegacyclicRing Coeff)
    (fHat : TransformPoly ring) :
    Pr[= fHat | $ᵗ (TransformPoly ring)] =
      (Fintype.card (TransformPoly ring) : ENNReal)⁻¹ :=
  probOutput_uniformSample (TransformPoly ring) fHat

end LatticeCrypto
