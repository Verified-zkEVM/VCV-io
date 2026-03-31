/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLKEM.Params
import LatticeCrypto.Ring

/-!
# ML-KEM Ring Layer

This file now acts as a thin ML-KEM instantiation of the generic negacyclic lattice
arithmetic layer from `LatticeCrypto.Ring`.
-/


namespace MLKEM

/-- Coefficients in the ML-KEM base ring. -/
abbrev Coeff := ZMod modulus

/-- The vector-backed coefficient-domain backend used by the current ML-KEM development. -/
abbrev polyBackend : LatticeCrypto.PolyBackend Coeff :=
  LatticeCrypto.vectorBackend Coeff ringDegree

/-- The proof-facing quotient `Z_q[X] / (X^256 + 1)`. -/
abbrev Quotient := LatticeCrypto.NegacyclicQuotient Coeff ringDegree

/-- Coefficient-domain polynomials in `R_q = Z_q[X] / (X^256 + 1)`. -/
abbrev Rq := polyBackend.Poly

/-- Transform-domain polynomials tagged via the generic transform wrapper. -/
abbrev Tq := LatticeCrypto.TransformPoly polyBackend

instance : Zero polyBackend.Poly := by
  change Zero (LatticeCrypto.Poly Coeff ringDegree)
  infer_instance

instance : Add polyBackend.Poly := by
  change Add (LatticeCrypto.Poly Coeff ringDegree)
  infer_instance

instance : Sub polyBackend.Poly := by
  change Sub (LatticeCrypto.Poly Coeff ringDegree)
  infer_instance

instance : Neg polyBackend.Poly := by
  change Neg (LatticeCrypto.Poly Coeff ringDegree)
  infer_instance

instance : DecidableEq polyBackend.Poly := by
  change DecidableEq (LatticeCrypto.Poly Coeff ringDegree)
  infer_instance

instance : GetElem Rq Nat Coeff (fun _ i => i < ringDegree) where
  getElem f i hi := polyBackend.toCoeffFn f ⟨i, hi⟩

/-- Length-`k` vectors over `R_q`. -/
abbrev RqVec (k : ℕ) := LatticeCrypto.CarrierVec polyBackend k

/-- Length-`k` vectors over `T_q`. -/
abbrev TqVec (k : ℕ) := Vector Tq k

/-- `rows × cols` row-major matrices over `T_q`. -/
abbrev TqMatrix (rows cols : ℕ) := Vector (TqVec cols) rows

/-- The quotient interpretation of a coefficient-domain polynomial. -/
noncomputable abbrev quotientOfRq (f : Rq) : Quotient :=
  LatticeCrypto.NegacyclicQuotient.ofBackend polyBackend f

/-- Executable coefficient-domain negacyclic multiplication. -/
def negacyclicOps : LatticeCrypto.NegacyclicOps polyBackend where
  mul := LatticeCrypto.schoolbookNegacyclicMul polyBackend

/-- The canonical executable negacyclic multiplication on `Rq`. -/
abbrev negacyclicMul (f g : Rq) : Rq := negacyclicOps.mul f g

/-- Optional transform-domain acceleration specialized to ML-KEM carriers. -/
abbrev NTTRingOps := LatticeCrypto.TransformOps polyBackend Tq

/-- Proof-oriented transform laws specialized to ML-KEM carriers. -/
abbrev NTTRingLaws (ops : NTTRingOps) := LatticeCrypto.TransformOps.Laws ops

end MLKEM
