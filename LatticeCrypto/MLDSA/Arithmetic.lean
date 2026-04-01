/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Params
import LatticeCrypto.Ring.SchoolbookCert
import LatticeCrypto.Ring.Transform
import LatticeCrypto.Ring.Norms
import LatticeCrypto.Ring.Rounding

/-!
# ML-DSA Arithmetic Assembly

Instantiates the generic negacyclic ring architecture for the ML-DSA coefficient
ring `ℤ_q[X]/(X^256 + 1)` where `q = 8380417`, and exposes scheme-local type
and operation aliases consumed by downstream ML-DSA files.

Provides:
- `coeffRing` / `polyBackend` / `polyKernel` / `coeffSemantics`: the bundled
  executable ring, backend, kernel, and proof-facing semantics.
- `Rq`, `Tq`, `RqVec`, `TqVec`, `TqMatrix`, `Quotient`: scheme-local
  carrier aliases.
- `negacyclicMul`, `quotientOfRq`: coefficient-domain multiplication and
  quotient embedding.
- `NTTRingOps` / `NTTRingLaws`: transform-domain interface and law aliases.
- `normOps`, `polyNorm`, `polyVecNorm`, `polyBounded`, `polyVecBounded`:
  norm infrastructure.
- `RoundingOps`, `Power2RoundOps`: rounding interface aliases.

This module is mixed: the executable aliases are computable, while
`coeffSemantics` and `quotientOfRq` are `noncomputable`.
-/


namespace MLDSA

/-- Coefficients in the ML-DSA base ring. -/
abbrev Coeff := ZMod modulus

instance : NeZero modulus := ⟨by
  unfold modulus
  decide
⟩

/-- The canonical bundled coefficient-domain ring used by the current ML-DSA development. -/
abbrev coeffRing : LatticeCrypto.NegacyclicRing Coeff :=
  LatticeCrypto.vectorNegacyclicRing Coeff ringDegree

/-- The semantic backend used by the bundled ML-DSA ring. -/
abbrev polyBackend : LatticeCrypto.PolyBackend Coeff :=
  coeffRing.backend

/-- The executable kernel used by the bundled ML-DSA ring. -/
abbrev polyKernel : LatticeCrypto.PolyKernel Coeff polyBackend :=
  coeffRing.kernel

/-- The proof-facing semantic interpretation of the bundled ML-DSA ring. -/
noncomputable abbrev coeffSemantics : LatticeCrypto.NegacyclicRingSemantics coeffRing :=
  LatticeCrypto.vectorNegacyclicSemantics Coeff ringDegree

/-- The proof-facing quotient `Z_q[X] / (X^256 + 1)`. -/
abbrev Quotient := LatticeCrypto.NegacyclicRingSemantics.Quotient coeffSemantics

/-- Coefficient-domain polynomials in `R_q = Z_q[X] / (X^256 + 1)`. -/
abbrev Rq := coeffRing.Poly

/-- Transform-domain polynomials for the ML-DSA bundled ring. -/
abbrev Tq := LatticeCrypto.TransformPoly coeffRing

instance : DecidableEq Rq := by
  change DecidableEq (LatticeCrypto.Poly Coeff ringDegree)
  infer_instance

instance : DecidableEq Tq := by
  change DecidableEq (LatticeCrypto.TransformPoly coeffRing)
  infer_instance

/-- Length-`k` vectors over `R_q`. -/
abbrev RqVec (k : ℕ) := LatticeCrypto.PolyVec Rq k

/-- Length-`k` vectors over `T_q`. -/
abbrev TqVec (k : ℕ) := LatticeCrypto.PolyVec Tq k

/-- `rows × cols` row-major matrices over `T_q`. -/
abbrev TqMatrix (rows cols : ℕ) := LatticeCrypto.PolyMatrix Tq rows cols

/-- The quotient interpretation of a coefficient-domain polynomial. -/
noncomputable abbrev quotientOfRq (f : Rq) : Quotient :=
  coeffSemantics.quotientOf f

/-- The canonical executable negacyclic multiplication on `Rq`. -/
abbrev negacyclicMul (f g : Rq) : Rq :=
  coeffRing.mul f g

/-- Optional transform-domain acceleration specialized to ML-DSA carriers. -/
abbrev NTTRingOps := LatticeCrypto.TransformOps coeffRing Tq

/-- Proof-oriented transform laws specialized to ML-DSA carriers. -/
abbrev NTTRingLaws (ops : NTTRingOps) := LatticeCrypto.TransformOps.Laws ops

section Norms

/-- The canonical norm bundle on ML-DSA coefficient-domain polynomials. -/
def normOps : LatticeCrypto.NormOps polyBackend :=
  LatticeCrypto.zmodPolyNormOps modulus polyBackend

/-- The centered infinity norm of an ML-DSA polynomial. -/
abbrev polyNorm (f : Rq) : ℕ :=
  normOps.cInfNorm f

/-- The centered infinity norm of an ML-DSA polynomial vector. -/
abbrev polyVecNorm {k : ℕ} (v : RqVec k) : ℕ :=
  LatticeCrypto.PolyVec.cInfNorm normOps v

/-- Whether all coefficients of a polynomial are in `[-b, b]`. -/
def polyBounded (f : Rq) (b : ℕ) : Prop :=
  polyNorm f ≤ b

/-- Whether all coefficients of every component of a polynomial vector are in `[-b, b]`. -/
def polyVecBounded {k : ℕ} (v : RqVec k) (b : ℕ) : Prop :=
  polyVecNorm v ≤ b

end Norms

section Rounding

/-- Abstract rounding operations for ML-DSA, parameterized by `2 * γ₂`. -/
abbrev RoundingOps (alpha : ℕ) := LatticeCrypto.RoundingOps coeffRing alpha

/-- Abstract power-2 rounding operations for ML-DSA, parameterized by `d = 13`. -/
abbrev Power2RoundOps := LatticeCrypto.Power2RoundOps coeffRing droppedBits

end Rounding

end MLDSA
