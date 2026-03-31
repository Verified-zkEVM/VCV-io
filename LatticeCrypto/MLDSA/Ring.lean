/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Params
import LatticeCrypto.Ring
import LatticeCrypto.Norm
import LatticeCrypto.Rounding

/-!
# ML-DSA Ring Layer

This file now acts as a thin ML-DSA instantiation of the generic negacyclic lattice
arithmetic layer from `LatticeCrypto.Ring`.
-/


namespace MLDSA

/-- Coefficients in the ML-DSA base ring. -/
abbrev Coeff := ZMod modulus

instance : NeZero modulus := ⟨by
  unfold modulus
  decide
⟩

/-- The vector-backed coefficient-domain backend used by the current ML-DSA development. -/
abbrev polyBackend : LatticeCrypto.PolyBackend Coeff :=
  LatticeCrypto.vectorBackend Coeff ringDegree

/-- The proof-facing quotient `Z_q[X] / (X^256 + 1)`. -/
abbrev Quotient := LatticeCrypto.NegacyclicQuotient Coeff ringDegree

/-- Coefficient-domain polynomials in `R_q = Z_q[X] / (X^256 + 1)`. -/
abbrev Rq := LatticeCrypto.Poly Coeff ringDegree

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

/-- Optional transform-domain acceleration specialized to ML-DSA carriers. -/
abbrev NTTRingOps := LatticeCrypto.TransformOps polyBackend Tq

/-- Proof-oriented transform laws specialized to ML-DSA carriers. -/
abbrev NTTRingLaws (ops : NTTRingOps) := LatticeCrypto.TransformOps.Laws ops

section Norms

/-- The canonical norm bundle on ML-DSA coefficient-domain polynomials. -/
def normOps : LatticeCrypto.NormOps Rq :=
  LatticeCrypto.zmodPolyNormOps modulus ringDegree

/-- The centered infinity norm of an ML-DSA polynomial. -/
abbrev polyNorm (f : Rq) : ℕ := normOps.cInfNorm f

/-- The centered infinity norm of an ML-DSA polynomial vector. -/
abbrev polyVecNorm {k : ℕ} (v : RqVec k) : ℕ :=
  Finset.sup Finset.univ fun j : Fin k => polyNorm (v.get j)

/-- Whether all coefficients of a polynomial are in `[-b, b]`. -/
def polyBounded (f : Rq) (b : ℕ) : Prop := polyNorm f ≤ b

/-- Whether all coefficients of every component of a polynomial vector are in `[-b, b]`. -/
def polyVecBounded {k : ℕ} (v : RqVec k) (b : ℕ) : Prop :=
  polyVecNorm v ≤ b

end Norms

section Rounding

/-- Abstract rounding operations for ML-DSA, parameterized by `2 * γ₂`. -/
abbrev RoundingOps (alpha : ℕ) := LatticeCrypto.RoundingOps Rq alpha

/-- Abstract power-2 rounding operations for ML-DSA, parameterized by `d = 13`. -/
abbrev Power2RoundOps := LatticeCrypto.Power2RoundOps Rq droppedBits

end Rounding

end MLDSA
