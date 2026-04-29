/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import LatticeCrypto.Falcon.Params
import LatticeCrypto.Ring.SchoolbookCert
import LatticeCrypto.Ring.Transform
import LatticeCrypto.Ring.Norms
import LatticeCrypto.Ring.IntegralLift

/-!
# Falcon Arithmetic Assembly

Instantiates the generic negacyclic ring architecture for the Falcon coefficient
ring `ℤ_q[X]/(X^n + 1)` where `q = 12289` and `n` is parameterized (typically
512 or 1024), and exposes scheme-local type and operation aliases consumed by
downstream Falcon files.

Provides:
- `coeffRing` / `polyBackend` / `intBackend` / `coeffSemantics`: the bundled
  executable ring, `ZMod q` backend, integer backend, and proof-facing semantics.
- `Rq`, `IntPoly`, `Tq`, `Quotient`: scheme-local carrier aliases.
- `negacyclicMul`, `quotientOfRq`: coefficient-domain multiplication and
  quotient embedding.
- `NTTRingOps` / `NTTRingLaws`: transform-domain interface and law aliases.
- `normOps`, `polyL2NormSq`, `pairL2NormSq`: norm infrastructure (Falcon uses
  `ℓ₂` norms rather than `ℓ∞`).
- `integralLift`, `IntPoly.toRq`, `intPolyMul`, `intPolyConst`: integer-lift
  infrastructure for secret-key arithmetic.
- `centeredRepr`, `isInvertibleModQ`: coefficient-level utilities.

This module is mixed: the executable aliases are computable, while
`coeffSemantics` and `quotientOfRq` are `noncomputable`.
-/


namespace Falcon

/-- Coefficients in the Falcon base ring `ℤ_q` where `q = 12289`. -/
abbrev Coeff := ZMod modulus

instance : NeZero modulus := ⟨by
  unfold modulus
  decide
⟩

/-- The canonical bundled coefficient-domain ring used by the current Falcon development. -/
abbrev coeffRing (n : ℕ) : LatticeCrypto.NegacyclicRing Coeff :=
  LatticeCrypto.vectorNegacyclicRing Coeff n

/-- The semantic coefficient backend. -/
abbrev polyBackend (n : ℕ) : LatticeCrypto.PolyBackend Coeff :=
  (coeffRing n).backend

/-- The semantic integer backend used for Falcon secret-key arithmetic. -/
abbrev intBackend (n : ℕ) : LatticeCrypto.PolyBackend ℤ :=
  LatticeCrypto.vectorBackend ℤ n

/-- Coefficient-domain polynomials in `R_q = ℤ_q[x] / (x^n + 1)`. -/
abbrev Rq (n : ℕ) := (coeffRing n).Poly

/-- Integer-coefficient polynomials in `ℤ[x] / (x^n + 1)`. -/
abbrev IntPoly (n : ℕ) := LatticeCrypto.Poly ℤ n

/-- The proof-facing semantic interpretation of the bundled Falcon ring. -/
noncomputable abbrev coeffSemantics (n : ℕ) : LatticeCrypto.NegacyclicRingSemantics (coeffRing n) :=
  LatticeCrypto.vectorNegacyclicSemantics Coeff n

/-- The proof-facing quotient `Z_q[X] / (X^n + 1)`. -/
abbrev Quotient (n : ℕ) := LatticeCrypto.NegacyclicRingSemantics.Quotient (coeffSemantics n)

/-- Transform-domain polynomials for the Falcon bundled ring. -/
abbrev Tq (n : ℕ) := LatticeCrypto.TransformPoly (coeffRing n)

instance {n : ℕ} : DecidableEq (Rq n) := by
  change DecidableEq (LatticeCrypto.Poly Coeff n)
  infer_instance

instance {n : ℕ} : Fintype (Rq n) := by
  change Fintype (LatticeCrypto.Poly Coeff n)
  infer_instance

instance {n : ℕ} : Inhabited (Rq n) := by
  change Inhabited (LatticeCrypto.Poly Coeff n)
  infer_instance

instance {n : ℕ} : SampleableType (Rq n) := by
  change SampleableType (LatticeCrypto.Poly Coeff n)
  infer_instance

instance {n : ℕ} : DecidableEq (Tq n) := by
  change DecidableEq (LatticeCrypto.TransformPoly (coeffRing n))
  infer_instance

/-- The quotient interpretation of a coefficient-domain polynomial. -/
noncomputable abbrev quotientOfRq {n : ℕ} (f : Rq n) : Quotient n :=
  (coeffSemantics n).quotientOf f

/-- The canonical executable negacyclic multiplication on `Rq`. -/
abbrev negacyclicMul {n : ℕ} (f g : Rq n) : Rq n :=
  (coeffRing n).mul f g

/-- Optional transform-domain acceleration specialized to Falcon carriers. -/
abbrev NTTRingOps (n : ℕ) := LatticeCrypto.TransformOps (coeffRing n) (Tq n)

/-- Proof-oriented transform laws specialized to Falcon carriers. -/
abbrev NTTRingLaws {n : ℕ} (ops : NTTRingOps n) := LatticeCrypto.TransformOps.Laws ops

section Norms

variable {n : ℕ}

/-- The canonical norm bundle on Falcon coefficient-domain polynomials. -/
def normOps (n : ℕ) : LatticeCrypto.NormOps (polyBackend n) :=
  LatticeCrypto.zmodPolyNormOps modulus (polyBackend n)

/-- The squared `ℓ₂` norm of a Falcon polynomial. -/
abbrev polyL2NormSq (f : Rq n) : ℕ :=
  (normOps n).l2NormSq f

/-- The squared `ℓ₂` norm of a pair of Falcon polynomials `(s₁, s₂)`. -/
abbrev pairL2NormSq (s₁ s₂ : Rq n) : ℕ :=
  (normOps n).pairL2NormSq s₁ s₂

end Norms

section IntPolyOps

variable {n : ℕ}

/-- The Falcon-specific lift from integer polynomials to `R_q`. -/
def integralLift (n : ℕ) : LatticeCrypto.IntegralLift (IntPoly n) (Rq n) :=
  LatticeCrypto.vectorIntegralLift modulus n

/-- Reduce an integer polynomial mod `q` to obtain an element of `R_q`. -/
abbrev IntPoly.toRq (f : IntPoly n) : Rq n :=
  (integralLift n).toRq f

/-- The centered representative of a `ZMod q` element, mapping to `[-(q-1)/2, (q-1)/2]`. -/
def centeredRepr (x : ZMod modulus) : ℤ :=
  LatticeCrypto.centeredRepr x

/-- Check whether all NTT coefficients of a polynomial are nonzero. -/
def isInvertibleModQ (nttOps : NTTRingOps n) (f : Rq n) : Bool :=
  let fHat := nttOps.ntt f
  (Vector.toList fHat.coeffs).all (· != 0)

end IntPolyOps

/-- Schoolbook negacyclic multiplication for integer polynomials in `ℤ[x]/(x^n + 1)`. -/
abbrev intPolyMul {n : ℕ} (f g : IntPoly n) : IntPoly n :=
  (integralLift n).mul f g

/-- The constant integer polynomial with value `c` at position `0` and `0` elsewhere. -/
abbrev intPolyConst {n : ℕ} (c : ℤ) : IntPoly n :=
  (integralLift n).const c

end Falcon
