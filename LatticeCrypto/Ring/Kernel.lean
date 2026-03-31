/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Ring.Core

/-!
# Generic Negacyclic Ring Kernels

Executable layer for the generic lattice ring architecture. Defines:

- `PolyKernel`: array-level read/write interface for a `PolyBackend`, bridging
  semantic coefficient indexing to mutable `Array` operations.
- `NegacyclicRing`: the principal executable bundle carrying a backend, a kernel,
  and coefficient-domain ring operations (zero, add, sub, neg, mul). This is the
  type that downstream scheme `Arithmetic.lean` modules instantiate.
- `NegacyclicRingSemantics`: a proof-facing soundness certificate relating the
  executable operations of a `NegacyclicRing` to the quotient ring
  `R[X] / (X^n + 1)` via a homomorphism `quotientOf`.
- `schoolbookNegacyclicMul`: a backend-generic `O(n²)` reference multiplier
  implementing negacyclic convolution.

The executable / proof boundary is enforced structurally: `NegacyclicRing` is
computable and carries no quotient types, while `NegacyclicRingSemantics` is
`noncomputable` and provides the algebraic soundness bridge.
-/


open scoped BigOperators

universe u v

namespace LatticeCrypto

/-- Executable array interface for a `PolyBackend`.

Bridges the semantic coefficient-indexed carrier to mutable `Array` operations
(`toArray` / `ofArray`) with round-trip and size laws. Scheme-specific fast
paths (e.g. concrete NTTs) operate on arrays via the kernel, then convert back
to the backend carrier. -/
structure PolyKernel (Coeff : Type u) (backend : PolyBackend Coeff) where
  toArray : backend.Poly → Array Coeff
  ofArray : Array Coeff → backend.Poly
  toArray_size : ∀ p, (toArray p).size = backend.degree
  coeff_ofArray : ∀ a (h : a.size = backend.degree) i,
    backend.coeff (ofArray a) i = a[i.val]'(by
      exact Nat.lt_of_lt_of_eq i.isLt h.symm)
  ofArray_toArray : ∀ p, ofArray (toArray p) = p

namespace PolyKernel

variable {Coeff : Type u} {backend : PolyBackend Coeff}

/-- Reify a kernel array back to the backend coefficient function. -/
def coeffFn (_kernel : PolyKernel Coeff backend) (a : Array Coeff) (h : a.size = backend.degree) :
    Fin backend.degree → Coeff :=
  fun i => a[i.val]'(by
    exact Nat.lt_of_lt_of_eq i.isLt h.symm)

end PolyKernel

/-- Bundled executable coefficient-domain arithmetic for `R[X] / (X^n + 1)`.

Packages a `PolyBackend`, a `PolyKernel`, and the five basic ring operations
into a single computable bundle. Downstream scheme `Arithmetic.lean` modules
(e.g. `MLDSA.Arithmetic`, `MLKEM.Arithmetic`, `Falcon.Arithmetic`) instantiate
this structure via `vectorNegacyclicRing` and then expose scheme-local type
aliases (`Rq`, `Tq`, `RqVec`, etc.) that the rest of the scheme imports. -/
structure NegacyclicRing (Coeff : Type u) [CommRing Coeff] where
  backend : PolyBackend Coeff
  kernel : PolyKernel Coeff backend
  zero : backend.Poly
  add : backend.Poly → backend.Poly → backend.Poly
  sub : backend.Poly → backend.Poly → backend.Poly
  neg : backend.Poly → backend.Poly
  mul : backend.Poly → backend.Poly → backend.Poly

/-- Proof-facing soundness certificate for a `NegacyclicRing`.

Provides a ring homomorphism `quotientOf` from the executable carrier into the
semantic quotient `R[X] / (X^n + 1)`, together with proofs that each executable
operation is sound with respect to the corresponding quotient-ring operation.

This structure is `noncomputable` by design — it exists only for proof-level
reasoning and is never evaluated at runtime. -/
structure NegacyclicRingSemantics {Coeff : Type u} [CommRing Coeff]
    (ring : NegacyclicRing Coeff) where
  quotientOf : ring.backend.Poly → NegacyclicQuotient Coeff ring.backend.degree
  zero_sound : quotientOf ring.zero = 0
  add_sound : ∀ f g, quotientOf (ring.add f g) = quotientOf f + quotientOf g
  sub_sound : ∀ f g, quotientOf (ring.sub f g) = quotientOf f - quotientOf g
  neg_sound : ∀ f, quotientOf (ring.neg f) = -quotientOf f
  mul_sound : ∀ f g, quotientOf (ring.mul f g) = quotientOf f * quotientOf g

namespace NegacyclicRing

variable {Coeff : Type u} [CommRing Coeff]

/-- The coefficient-domain carrier of a bundled negacyclic ring. -/
abbrev Poly (ring : NegacyclicRing Coeff) : Type _ :=
  ring.backend.Poly

/-- The degree of the bundled polynomial carrier. -/
abbrev degree (ring : NegacyclicRing Coeff) : Nat :=
  ring.backend.degree

/-- The semantic quotient associated to a bundled negacyclic ring. -/
abbrev Quotient (ring : NegacyclicRing Coeff) : Type _ :=
  NegacyclicQuotient Coeff ring.degree

/-- Coefficient projection from the bundled backend. -/
def coeff (ring : NegacyclicRing Coeff) (p : ring.Poly) : Fin ring.degree → Coeff :=
  ring.backend.coeff p

instance (ring : NegacyclicRing Coeff) : Zero ring.Poly :=
  ⟨ring.zero⟩

instance (ring : NegacyclicRing Coeff) : Add ring.Poly :=
  ⟨ring.add⟩

instance (ring : NegacyclicRing Coeff) : Sub ring.Poly :=
  ⟨ring.sub⟩

instance (ring : NegacyclicRing Coeff) : Neg ring.Poly :=
  ⟨ring.neg⟩

/-- Indexed access into a polynomial carrier by coefficient position. -/
instance (ring : NegacyclicRing Coeff) :
    GetElem ring.Poly Nat Coeff (fun _ i => i < ring.degree) where
  getElem p i hi := ring.backend.coeff p ⟨i, hi⟩

end NegacyclicRing

namespace NegacyclicRingSemantics

variable {Coeff : Type u} [CommRing Coeff] {ring : NegacyclicRing Coeff}

/-- The semantic quotient associated to a bundled soundness interpretation. -/
abbrev Quotient (_sem : NegacyclicRingSemantics ring) : Type _ :=
  NegacyclicQuotient Coeff ring.degree

end NegacyclicRingSemantics

/-- Generic `O(n²)` schoolbook negacyclic multiplication.

Implements the convolution `(f · g) mod (X^n + 1)` by iterating over all
coefficient pairs and subtracting (instead of adding) when the index wraps.
Used as the default `mul` in `vectorNegacyclicRing` and as the reference
multiplier for integer polynomials in `IntegralLift`. Concrete NTT-accelerated
schemes override this at runtime via `@[implemented_by]`. -/
def schoolbookNegacyclicMul {Coeff : Type u} [Ring Coeff]
    {backend : PolyBackend Coeff} (kernel : PolyKernel Coeff backend)
    (f g : backend.Poly) : backend.Poly := Id.run do
  let fa := kernel.toArray f
  let ga := kernel.toArray g
  let mut h : Array Coeff := Array.replicate backend.degree 0
  for i in [0:backend.degree] do
    for j in [0:backend.degree] do
      let fi := fa.getD i 0
      let gj := ga.getD j 0
      let k := (i + j) % backend.degree
      if i + j < backend.degree then
        h := h.set! k ((h.getD k 0) + fi * gj)
      else
        h := h.set! k ((h.getD k 0) - fi * gj)
  return kernel.ofArray h

end LatticeCrypto
