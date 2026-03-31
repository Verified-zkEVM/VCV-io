/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Params
import LatticeCrypto.Ring
import LatticeCrypto.Norm

/-!
# Falcon Ring Layer

This file now acts as a thin Falcon instantiation of the generic negacyclic lattice
arithmetic layer from `LatticeCrypto.Ring`, including the Falcon-specific integer lift.
-/


namespace Falcon

/-- Coefficients in the Falcon base ring `ℤ_q` where `q = 12289`. -/
abbrev Coeff := ZMod modulus

instance : NeZero modulus := ⟨by
  unfold modulus
  decide
⟩

/-- The vector-backed coefficient-domain backend used by the current Falcon development. -/
abbrev polyBackend (n : ℕ) : LatticeCrypto.PolyBackend Coeff :=
  LatticeCrypto.vectorBackend Coeff n

/-- The vector-backed integer backend used for Falcon secret-key arithmetic. -/
abbrev intBackend (n : ℕ) : LatticeCrypto.PolyBackend ℤ :=
  LatticeCrypto.vectorBackend ℤ n

/-- Coefficient-domain polynomials in `R_q = ℤ_q[x] / (x^n + 1)`. -/
abbrev Rq (n : ℕ) := LatticeCrypto.Poly Coeff n

/-- Integer-coefficient polynomials in `ℤ[x] / (x^n + 1)`. -/
abbrev IntPoly (n : ℕ) := LatticeCrypto.Poly ℤ n

/-- The proof-facing quotient `Z_q[X] / (X^n + 1)`. -/
abbrev Quotient (n : ℕ) := LatticeCrypto.NegacyclicQuotient Coeff n

/-- Transform-domain polynomials tagged via the generic transform wrapper. -/
abbrev Tq (n : ℕ) := LatticeCrypto.TransformPoly (polyBackend n)

instance {n : ℕ} : Zero (polyBackend n).Poly := by
  change Zero (LatticeCrypto.Poly Coeff n)
  infer_instance

instance {n : ℕ} : Add (polyBackend n).Poly := by
  change Add (LatticeCrypto.Poly Coeff n)
  infer_instance

instance {n : ℕ} : Sub (polyBackend n).Poly := by
  change Sub (LatticeCrypto.Poly Coeff n)
  infer_instance

instance {n : ℕ} : Neg (polyBackend n).Poly := by
  change Neg (LatticeCrypto.Poly Coeff n)
  infer_instance

instance {n : ℕ} : DecidableEq (polyBackend n).Poly := by
  change DecidableEq (LatticeCrypto.Poly Coeff n)
  infer_instance

/-- The quotient interpretation of a coefficient-domain polynomial. -/
noncomputable abbrev quotientOfRq {n : ℕ} (f : Rq n) : Quotient n :=
  LatticeCrypto.NegacyclicQuotient.ofBackend (polyBackend n) f

/-- Executable coefficient-domain negacyclic multiplication. -/
def negacyclicOps (n : ℕ) : LatticeCrypto.NegacyclicOps (polyBackend n) where
  mul := LatticeCrypto.schoolbookNegacyclicMul (polyBackend n)

/-- The canonical executable negacyclic multiplication on `Rq`. -/
abbrev negacyclicMul {n : ℕ} (f g : Rq n) : Rq n := (negacyclicOps n).mul f g

/-- Optional transform-domain acceleration specialized to Falcon carriers. -/
abbrev NTTRingOps (n : ℕ) := LatticeCrypto.TransformOps (polyBackend n) (Tq n)

/-- Proof-oriented transform laws specialized to Falcon carriers. -/
abbrev NTTRingLaws {n : ℕ} (ops : NTTRingOps n) := LatticeCrypto.TransformOps.Laws ops

section Norms

variable {n : ℕ}

/-- The canonical norm bundle on Falcon coefficient-domain polynomials. -/
def normOps (n : ℕ) : LatticeCrypto.NormOps (Rq n) :=
  LatticeCrypto.zmodPolyNormOps modulus n

/-- The squared ℓ₂ norm of a Falcon polynomial. -/
abbrev polyL2NormSq (f : Rq n) : ℕ := (normOps n).l2NormSq f

/-- The squared ℓ₂ norm of a pair of Falcon polynomials `(s₁, s₂)`. -/
abbrev pairL2NormSq (s₁ s₂ : Rq n) : ℕ := LatticeCrypto.pairL2NormSq s₁ s₂

end Norms

section IntPolyOps

variable {n : ℕ}

/-- The Falcon-specific lift from integer polynomials to `Rq`. -/
def integralLift (n : ℕ) : LatticeCrypto.IntegralLift (IntPoly n) (Rq n) :=
  LatticeCrypto.vectorIntegralLift modulus n

/-- Reduce an integer polynomial mod `q` to obtain an element of `R_q`. -/
abbrev IntPoly.toRq (f : IntPoly n) : Rq n := (integralLift n).toRq f

/-- The centered representative of a `ZMod q` element, mapping to `[-(q-1)/2, (q-1)/2]`. -/
def centeredRepr (x : ZMod modulus) : ℤ := LatticeCrypto.centeredRepr x

/-- Check whether all NTT coefficients of a polynomial are nonzero (i.e., invertible mod `q`).
This is needed to verify that `f` is invertible in `R_q`, which is required for computing
the public key `h = g · f⁻¹ mod q`. -/
def isInvertibleModQ (nttOps : NTTRingOps n) (f : Rq n) : Bool :=
  let fHat := nttOps.ntt f
  (Vector.toList fHat.coeffs).all (· != 0)

end IntPolyOps

/-- Schoolbook negacyclic multiplication for integer polynomials in `ℤ[x]/(x^n + 1)`. -/
abbrev intPolyMul {n : ℕ} (f g : IntPoly n) : IntPoly n := (integralLift n).mul f g

/-- The constant integer polynomial with value `c` at position 0 and 0 elsewhere. -/
abbrev intPolyConst {n : ℕ} (c : ℤ) : IntPoly n := (integralLift n).const c

end Falcon
