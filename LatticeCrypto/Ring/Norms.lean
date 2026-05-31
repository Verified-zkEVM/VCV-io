/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Tobias Rothmann
-/
import LatticeCrypto.Ring.VectorBackend
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Norms For Negacyclic Ring Backends

Backend-generic norm infrastructure for the lattice ring layer. Defines:

- `CenteredCoeffView`: an integer-valued centered representative map for
  coefficients, used to define norms generically over any backend.
- `NormOps`: a norm bundle (`cInfNorm`, `l1Norm`, `l2NormSq`) parameterized
  by a `PolyBackend`, with a `pairL2NormSq` helper for Falcon-style signature
  norm bounds.
- `centeredRepr` and associated lemmas: the canonical centered representative
  for `ZMod q`, mapping each element to `[-(q-1)/2, (q-1)/2]`.
- `lpNormPowOf`: the generic un-rooted `ℓ_p` norm `Σᵢ |cᵢ|^p`, with `l1NormOf`
  (`p = 1`) and `l2NormSqOf` (`p = 2`) as special cases.
- Generic norm constructors (`cInfNormOf`, `l1NormOf`, `l2NormSqOf`) and their
  specialized vector-backend versions (`cInfNorm`, `l1Norm`, `l2NormSq`,
  `lpNormPow`).
- `PolyVec` norm lifts and `zmodPolyNormOps`.

`MLDSA.Arithmetic` and `Falcon.Arithmetic` assemble scheme-local norm aliases
from `zmodPolyNormOps`.
-/

open scoped BigOperators

namespace LatticeCrypto

/-- A centered integer view of coefficients.

Maps each coefficient to a representative integer, enabling backend-generic
norm definitions. The canonical instance for `ZMod q` is `zmodCenteredCoeffView`,
which uses `centeredRepr`. -/
structure CenteredCoeffView (Coeff : Type*) where
  repr : Coeff → ℤ

/-- Norm bundle layered over a `PolyBackend`.

Bundles the three standard polynomial norms used across ML-DSA and Falcon:
centered `ℓ∞`, `ℓ₁`, and squared `ℓ₂`. Constructed generically via
`normOpsOfCenteredView`, or directly via `zmodPolyNormOps` for `ZMod q`
coefficients. -/
structure NormOps {Coeff : Type*} (backend : PolyBackend Coeff) where
  /-- The centered `ℓ∞` norm of a backend polynomial. -/
  cInfNorm : backend.Poly → ℕ
  /-- The `ℓ₁` norm `Σᵢ |cᵢ|` of a backend polynomial. -/
  l1Norm : backend.Poly → ℕ
  /-- The squared `ℓ₂` norm `Σᵢ |cᵢ|²` of a backend polynomial. -/
  l2NormSq : backend.Poly → ℕ

namespace NormOps

variable {Coeff : Type*} {backend : PolyBackend Coeff}

/-- The squared `ℓ₂` norm of a pair of polynomials. -/
def pairL2NormSq (ops : NormOps backend) (p₁ p₂ : backend.Poly) : ℕ :=
  ops.l2NormSq p₁ + ops.l2NormSq p₂

end NormOps

section CenteredRepr

variable {q : ℕ} [NeZero q]

/-- The centered representative of `x : ZMod q`, mapping to the unique integer in
`[-(q-1)/2, (q-1)/2]` congruent to `x` mod `q`. -/
def centeredRepr (x : ZMod q) : ℤ :=
  if (x.val : ℤ) ≤ (q : ℤ) / 2 then (x.val : ℤ) else (x.val : ℤ) - q

omit [NeZero q] in
@[simp] theorem centeredRepr_of_le {x : ZMod q} (h : (x.val : ℤ) ≤ (q : ℤ) / 2) :
    centeredRepr x = x.val := by
  unfold centeredRepr
  exact if_pos h

omit [NeZero q] in
@[simp] theorem centeredRepr_of_gt {x : ZMod q} (h : (q : ℤ) / 2 < (x.val : ℤ)) :
    centeredRepr x = (x.val : ℤ) - q := by
  unfold centeredRepr
  exact if_neg (not_le.mpr h)

/-- The centered representative is always at most `q / 2`. -/
theorem centeredRepr_upper_bound (x : ZMod q) : centeredRepr x ≤ (q : ℤ) / 2 := by
  simp only [centeredRepr]
  split_ifs with h
  · exact h
  · push Not at h
    have hval := ZMod.val_lt x
    omega

/-- The centered representative has absolute value at most `q / 2`. -/
theorem centeredRepr_abs_le (x : ZMod q) : (centeredRepr x).natAbs ≤ q / 2 := by
  simp only [centeredRepr]
  have hval := ZMod.val_lt x
  split_ifs with h <;> omega

/-- Negation preserves the absolute value of the centered representative. -/
theorem centeredRepr_natAbs_neg (x : ZMod q) :
    (centeredRepr (-x)).natAbs = (centeredRepr x).natAbs := by
  by_cases hx : x = 0
  · simp [hx]
  · haveI : NeZero x := ⟨hx⟩
    simp only [centeredRepr, ZMod.val_neg_of_ne_zero]
    have hval := ZMod.val_lt x
    have hpos : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero x).mpr hx)
    split_ifs <;> omega

/-- Casting the centered representative back into `ZMod q` recovers the original element. -/
theorem centeredRepr_intCast (x : ZMod q) :
    (x : ZMod q) = ((centeredRepr x : ℤ) : ZMod q) := by
  by_cases h : (x.val : ℤ) ≤ (q : ℤ) / 2
  · rw [centeredRepr_of_le h, Int.cast_natCast, ZMod.natCast_zmod_val]
  · have hgt : (q : ℤ) / 2 < x.val := lt_of_not_ge h
    rw [centeredRepr_of_gt hgt, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_self]
    simp

/-- Twice the centered representative lies in the interval used by `ZMod.valMinAbs`. -/
theorem centeredRepr_mem_Ioc (x : ZMod q) :
    centeredRepr x * 2 ∈ Set.Ioc (-(q : ℤ)) q := by
  by_cases h : (x.val : ℤ) ≤ (q : ℤ) / 2
  · rw [centeredRepr_of_le h]
    have hx : 0 ≤ (x.val : ℤ) := by positivity
    have hmod : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
    constructor <;> omega
  · have hgt : (q : ℤ) / 2 < x.val := lt_of_not_ge h
    rw [centeredRepr_of_gt hgt]
    have hval := ZMod.val_lt x
    constructor <;> omega

/-- The centered representative agrees with `ZMod.valMinAbs`. -/
theorem centeredRepr_eq_valMinAbs (x : ZMod q) :
    centeredRepr x = x.valMinAbs := by
  simpa using ((ZMod.valMinAbs_spec x (centeredRepr x)).2
    ⟨centeredRepr_intCast x, centeredRepr_mem_Ioc x⟩).symm

/-- Casting an integer already in the centered interval preserves that integer. -/
theorem centeredRepr_intCast_eq (z : ℤ)
    (hzlo : -(q : ℤ) < z * 2) (hzhi : z * 2 ≤ q) :
    centeredRepr ((z : ZMod q)) = z := by
  rw [centeredRepr_eq_valMinAbs]
  exact (ZMod.valMinAbs_spec ((z : ZMod q)) z).2 ⟨rfl, ⟨hzlo, hzhi⟩⟩

/-- A small-enough integer is unchanged by casting into `ZMod q` and taking `centeredRepr`. -/
theorem centeredRepr_intCast_eq_of_natAbs_le (z : ℤ) {b : ℕ}
    (hbound : z.natAbs ≤ b) (hbq : 2 * b < q) :
    centeredRepr ((z : ZMod q)) = z := by
  apply centeredRepr_intCast_eq
  · have : -(b : ℤ) ≤ z := by omega
    omega
  · have : z ≤ b := by omega
    omega

/-- A `natAbs` bound yields both lower and upper integer bounds. -/
theorem neg_le_and_le_of_natAbs_le {z : ℤ} {b : ℕ}
    (hbound : z.natAbs ≤ b) : -(b : ℤ) ≤ z ∧ z ≤ b := by
  constructor <;> omega

/-- Lower and upper integer bounds yield a `natAbs` bound. Inverse of
`neg_le_and_le_of_natAbs_le`. -/
theorem natAbs_le_of_neg_le_and_le {z : ℤ} {b : ℕ}
    (hl : -(b : ℤ) ≤ z) (hu : z ≤ b) : z.natAbs ≤ b := by
  omega

/-- The canonical centered coefficient view for `ZMod q`. -/
def zmodCenteredCoeffView (q : ℕ) [NeZero q] : CenteredCoeffView (ZMod q) where
  repr := centeredRepr

end CenteredRepr

section GenericNorms

variable {Coeff : Type*} (backend : PolyBackend Coeff) (view : CenteredCoeffView Coeff)

/-- Backend-generic `p`-th-power `ℓ_p` "norm" `Σᵢ |cᵢ|^p`, i.e. the un-rooted `ℓ_p`
norm of the centered coefficient vector.

Keeping the sum un-rooted keeps the value in `ℕ` (no square root). The two cases the
lattice schemes actually use are `l1NormOf` (`p = 1`) and `l2NormSqOf` (`p = 2`),
both defined below as special cases. -/
def lpNormPowOf (p : ℕ) (poly : backend.Poly) : ℕ :=
  ∑ i : Fin backend.degree, (view.repr (backend.coeff poly i)).natAbs ^ p

/-- Backend-generic centered infinity norm. -/
def cInfNormOf (p : backend.Poly) : ℕ :=
  Finset.sup Finset.univ fun i : Fin backend.degree => (view.repr (backend.coeff p i)).natAbs

/-- Backend-generic `ℓ₁` norm `Σᵢ |cᵢ|`, the `p = 1` case of `lpNormPowOf`. -/
def l1NormOf (p : backend.Poly) : ℕ :=
  lpNormPowOf backend view 1 p

/-- Backend-generic squared `ℓ₂` norm `Σᵢ |cᵢ|²`, the `p = 2` case of `lpNormPowOf`. -/
def l2NormSqOf (p : backend.Poly) : ℕ :=
  lpNormPowOf backend view 2 p

/-- Construct a generic norm bundle from a centered coefficient view. -/
def normOpsOfCenteredView : NormOps backend where
  cInfNorm := cInfNormOf backend view
  l1Norm := l1NormOf backend view
  l2NormSq := l2NormSqOf backend view

end GenericNorms

section SpecializedVectorNorms

variable {q : ℕ} [NeZero q] {n : Nat}

/-- The centered infinity norm on the canonical vector backend. -/
def cInfNorm (p : Poly (ZMod q) n) : ℕ :=
  cInfNormOf (vectorBackend (ZMod q) n) (zmodCenteredCoeffView q) p

/-- The `ℓ₁` norm on the canonical vector backend. -/
def l1Norm (p : Poly (ZMod q) n) : ℕ :=
  l1NormOf (vectorBackend (ZMod q) n) (zmodCenteredCoeffView q) p

/-- The squared `ℓ₂` norm on the canonical vector backend. -/
def l2NormSq (p : Poly (ZMod q) n) : ℕ :=
  l2NormSqOf (vectorBackend (ZMod q) n) (zmodCenteredCoeffView q) p

/-- The squared `ℓ₂` norm of a pair of vector-backed polynomials. -/
def pairL2NormSq (p₁ p₂ : Poly (ZMod q) n) : ℕ :=
  l2NormSq p₁ + l2NormSq p₂

/-- The un-rooted `ℓ_p` norm on the canonical vector backend. -/
def lpNormPow (p : ℕ) (poly : Poly (ZMod q) n) : ℕ :=
  lpNormPowOf (vectorBackend (ZMod q) n) (zmodCenteredCoeffView q) p poly

theorem l1Norm_eq_lpNormPow (p : Poly (ZMod q) n) : l1Norm p = lpNormPow 1 p :=
  rfl

theorem l2NormSq_eq_lpNormPow (p : Poly (ZMod q) n) : l2NormSq p = lpNormPow 2 p :=
  rfl

theorem cInfNorm_le_iff {p : Poly (ZMod q) n} {b : ℕ} :
    cInfNorm p ≤ b ↔ ∀ i : Fin n, (centeredRepr (p.get i)).natAbs ≤ b := by
  simp [cInfNorm, cInfNormOf, vectorBackend, zmodCenteredCoeffView, Finset.sup_le_iff]

theorem cInfNorm_le_of_coeff_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : ∀ i : Fin n, (centeredRepr (p.get i)).natAbs ≤ b) : cInfNorm p ≤ b :=
  cInfNorm_le_iff.mpr h

theorem coeff_le_cInfNorm (p : Poly (ZMod q) n) (i : Fin n) :
    (centeredRepr (p.get i)).natAbs ≤ cInfNorm p :=
  Finset.le_sup (f := fun i => (centeredRepr (p.get i)).natAbs) (Finset.mem_univ i)

/-- Every polynomial has centered infinity norm at most `q / 2`. -/
theorem cInfNorm_le_halfq (p : Poly (ZMod q) n) : cInfNorm p ≤ q / 2 :=
  cInfNorm_le_iff.mpr (fun i => centeredRepr_abs_le (p.get i))

/-- Negation preserves the centered infinity norm. -/
@[simp] theorem cInfNorm_neg (f : Poly (ZMod q) n) : cInfNorm (-f) = cInfNorm f := by
  simp only [cInfNorm, cInfNormOf, vectorBackend, zmodCenteredCoeffView]
  congr 1
  ext i
  have hneg : (-f).get i = -(f.get i) := Vector.getElem_map (- ·) i.isLt
  rw [hneg, centeredRepr_natAbs_neg]

theorem l1Norm_le_of_cInfNorm_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : cInfNorm p ≤ b) : l1Norm p ≤ n * b := by
  unfold l1Norm l1NormOf lpNormPowOf
  simp only [pow_one]
  calc
    ∑ i : Fin n, (centeredRepr (p.get i)).natAbs
      ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ => (cInfNorm_le_iff.mp h) i
    _ = n * b := by simp [Finset.sum_const]

theorem l2NormSq_le_of_cInfNorm_le {p : Poly (ZMod q) n} {b : ℕ}
    (h : cInfNorm p ≤ b) : l2NormSq p ≤ n * b ^ 2 := by
  unfold l2NormSq l2NormSqOf lpNormPowOf
  calc
    ∑ i : Fin n, (centeredRepr (p.get i)).natAbs ^ 2
      ≤ ∑ _i : Fin n, b ^ 2 :=
        Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (cInfNorm_le_iff.mp h i) 2
    _ = n * b ^ 2 := by simp [Finset.sum_const]

/-- The squared `ℓ₂` norm is bounded by the square of the `ℓ₁` norm (`Σ aᵢ² ≤ (Σ aᵢ)²`). -/
theorem l2NormSq_le_l1Norm_sq (p : Poly (ZMod q) n) : l2NormSq p ≤ l1Norm p ^ 2 := by
  unfold l2NormSq l2NormSqOf l1Norm l1NormOf lpNormPowOf
  simp only [pow_one]
  calc
    ∑ i : Fin n, (centeredRepr (p.get i)).natAbs ^ 2
      ≤ ∑ i : Fin n, (centeredRepr (p.get i)).natAbs
          * ∑ j : Fin n, (centeredRepr (p.get j)).natAbs := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [pow_two]
        exact Nat.mul_le_mul le_rfl
          (Finset.single_le_sum (f := fun j : Fin n => (centeredRepr (p.get j)).natAbs)
            (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
    _ = (∑ i : Fin n, (centeredRepr (p.get i)).natAbs) ^ 2 := by
        rw [← Finset.sum_mul, ← pow_two]

/-- The `ℓ₁` norm is bounded by the squared `ℓ₂` norm (`Σ aᵢ ≤ Σ aᵢ²`, since `a ≤ a²`). -/
theorem l1Norm_le_l2NormSq (p : Poly (ZMod q) n) : l1Norm p ≤ l2NormSq p := by
  unfold l1Norm l1NormOf l2NormSq l2NormSqOf lpNormPowOf
  simp only [pow_one]
  exact Finset.sum_le_sum (fun i _ => Nat.le_self_pow (by norm_num) _)

/-- A nonzero `ℓ₁` norm forces a nonzero squared `ℓ₂` norm (both vanish iff `p = 0`). -/
theorem l2NormSq_pos_of_l1Norm_pos {p : Poly (ZMod q) n} (h : 0 < l1Norm p) :
    0 < l2NormSq p :=
  lt_of_lt_of_le h (l1Norm_le_l2NormSq p)

end SpecializedVectorNorms

namespace PolyVec

variable {Coeff : Type*} {backend : PolyBackend Coeff} (ops : NormOps backend) {k : Nat}

/-- The centered infinity norm of a polynomial vector. -/
def cInfNorm (v : PolyVec backend.Poly k) : ℕ :=
  Finset.sup Finset.univ fun j : Fin k => ops.cInfNorm (v.get j)

/-- A polynomial vector has centered infinity norm at most `b` exactly when each component
polynomial does. -/
theorem cInfNorm_le_iff {v : PolyVec backend.Poly k} {b : ℕ} :
    PolyVec.cInfNorm ops v ≤ b ↔ ∀ j : Fin k, ops.cInfNorm (v.get j) ≤ b := by
  simp [PolyVec.cInfNorm, Finset.sup_le_iff]

/-- Each component polynomial is bounded by the centered infinity norm of the whole vector. -/
theorem component_cInfNorm_le (v : PolyVec backend.Poly k) (j : Fin k) :
    ops.cInfNorm (v.get j) ≤ PolyVec.cInfNorm ops v :=
  Finset.le_sup (f := fun j => ops.cInfNorm (v.get j)) (Finset.mem_univ j)

/-- The squared `ℓ₂` norm of a polynomial vector (sum of component squared `ℓ₂`
norms, matching the `‖w‖₂ = (Σⱼ ‖wⱼ‖²)^{1/2}` convention). -/
def l2NormSq (v : PolyVec backend.Poly k) : ℕ :=
  ∑ j : Fin k, ops.l2NormSq (v.get j)

end PolyVec

/-- The canonical backend-generic norm bundle for `ZMod q` coefficients. -/
def zmodPolyNormOps (q : ℕ) [NeZero q] (backend : PolyBackend (ZMod q)) : NormOps backend :=
  normOpsOfCenteredView backend (zmodCenteredCoeffView q)

/-! ## Notation

Scoped notation (`open scoped LatticeCrypto`, or being inside `namespace
LatticeCrypto`) for the centered norms. Two families:

* Bare bars `‖p‖∞`, `‖p‖₁`, `‖p‖₂²`, `‖(p₁, p₂)‖₂²` denote the canonical centered
  norms on the vector backend `Poly (ZMod q) n` (`cInfNorm`, `l1Norm`, `l2NormSq`,
  `pairL2NormSq`).
* `⟪ops⟫`-annotated bars `‖f‖⟪ops⟫∞`, `‖f‖⟪ops⟫₁`, `‖f‖⟪ops⟫₂²`, `‖(s₁, s₂)‖⟪ops⟫₂²`
  denote the norms of a `NormOps` bundle `ops`, applied either to a single backend
  polynomial or — by overloading the same syntax — to a `PolyVec`.

The trailing subscript on the closing bar keeps these distinct from Mathlib's
`‖·‖` (`Norm.norm`). -/

@[inherit_doc cInfNorm]
scoped notation:max "‖" p "‖∞" => LatticeCrypto.cInfNorm p
@[inherit_doc l1Norm]
scoped notation:max "‖" p "‖₁" => LatticeCrypto.l1Norm p
@[inherit_doc l2NormSq]
scoped notation:max "‖" p "‖₂²" => LatticeCrypto.l2NormSq p
@[inherit_doc pairL2NormSq]
scoped notation:max "‖(" p₁ "," p₂ ")" "‖₂²" => LatticeCrypto.pairL2NormSq p₁ p₂

@[inherit_doc NormOps.cInfNorm]
scoped notation:max "‖" f "‖⟪" ops "⟫∞" => LatticeCrypto.NormOps.cInfNorm ops f
@[inherit_doc NormOps.l1Norm]
scoped notation:max "‖" f "‖⟪" ops "⟫₁" => LatticeCrypto.NormOps.l1Norm ops f
@[inherit_doc NormOps.l2NormSq]
scoped notation:max "‖" f "‖⟪" ops "⟫₂²" => LatticeCrypto.NormOps.l2NormSq ops f
@[inherit_doc NormOps.pairL2NormSq]
scoped notation:max "‖(" p₁ "," p₂ ")" "‖⟪" ops "⟫₂²" =>
  LatticeCrypto.NormOps.pairL2NormSq ops p₁ p₂

@[inherit_doc PolyVec.cInfNorm]
scoped notation:max "‖" v "‖⟪" ops "⟫∞" => LatticeCrypto.PolyVec.cInfNorm ops v
@[inherit_doc PolyVec.l2NormSq]
scoped notation:max "‖" v "‖⟪" ops "⟫₂²" => LatticeCrypto.PolyVec.l2NormSq ops v

end LatticeCrypto
