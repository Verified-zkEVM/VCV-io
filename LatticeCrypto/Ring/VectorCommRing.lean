/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ring.SchoolbookCert
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.Polynomial.Div

/-!
# A Genuine `CommRing` On The Vector-Backed Negacyclic Ring

This file equips the vector-backed negacyclic ring with a *genuine* commutative
ring structure on its executable carrier `Poly Coeff n = Vector Coeff n`, obtained
by transport from the semantic quotient `R[X] / (Xⁿ + 1)`. The point is that the
linearity / bilinearity facts about `matVecMul`, `dot`, and `scalarVecMul` used by
downstream reductions become ordinary Mathlib ring facts, with **no** law-carrying
assumptions.

The transport rests on a single algebraic fact:

* `ofBackend_vectorBackend_bijective` — the canonical interpretation
  `NegacyclicQuotient.ofBackend (vectorBackend Coeff n)`, which sends a coefficient
  vector to its class in `R[X] / (Xⁿ + 1)`, is a bijection (unique degree-`< n`
  representatives modulo the monic modulus `Xⁿ + 1`).

`ofBackend` is additively a homomorphism (the additive soundness already proved in
`VectorBackend`) and multiplicatively a homomorphism (`negacyclicMulPure_sound` from
`SchoolbookCert`). The `CommRing` reuses the ambient pointwise additive group on
`Vector` and takes the bundled negacyclic multiplication of `vectorNegacyclicRing`
as `*`; its multiplicative axioms are obtained by transporting the quotient's
identities along the injective `ofBackend`. Reusing the additive group keeps the
instance free of diamonds.
-/

open Polynomial
open scoped BigOperators

namespace LatticeCrypto

universe u

variable {Coeff : Type u} [CommRing Coeff] {n : Nat}

/-! ## The coefficient polynomial of the vector backend -/

/-- `toPolynomial` of the canonical vector backend is the monomial sum of the
coefficient vector. -/
theorem toPolynomial_vectorBackend (p : Poly Coeff n) :
    (vectorBackend Coeff n).toPolynomial p = ∑ i : Fin n, monomial i.val (p.get i) :=
  rfl

/-- The coefficient polynomial of a vector backend element has degree `< n`. -/
theorem degree_toPolynomial_vectorBackend_lt (p : Poly Coeff n) :
    ((vectorBackend Coeff n).toPolynomial p).degree < (n : WithBot ℕ) := by
  rw [toPolynomial_vectorBackend]
  have h : (∑ i : Fin n, monomial i.val (p.get i))
      = ∑ i : Fin n, C (p.get i) * X ^ (i : ℕ) :=
    Finset.sum_congr rfl (fun i _ => (C_mul_X_pow_eq_monomial).symm)
  rw [h]
  exact degree_sum_fin_lt _

/-- Reading off the `i`-th coefficient of the backend polynomial recovers the
`i`-th entry of the vector. -/
theorem coeff_toPolynomial_vectorBackend (p : Poly Coeff n) (i : Fin n) :
    ((vectorBackend Coeff n).toPolynomial p).coeff i.val = p.get i := by
  rw [toPolynomial_vectorBackend, finset_sum_coeff,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hj => by rw [coeff_monomial, if_neg (fun h => hj (Fin.ext h))])]
  rw [coeff_monomial, if_pos rfl]

/-- The `i`-th entry of the scalar polynomial `scalarPoly c`. -/
theorem get_scalarPoly (c : Coeff) (i : Fin n) :
    ((vectorNegacyclicRing Coeff n).scalarPoly c).get i = if i.val = 0 then c else 0 := by
  have h := (vectorBackend Coeff n).coeff_build (fun j : Fin n => if j.val = 0 then c else 0) i
  rwa [vectorBackend_coeff] at h

/-- The coefficient polynomial of `scalarPoly c` is the constant `C c`. -/
theorem toPolynomial_scalarPoly (hn : 0 < n) (c : Coeff) :
    (vectorBackend Coeff n).toPolynomial ((vectorNegacyclicRing Coeff n).scalarPoly c) = C c := by
  rw [toPolynomial_vectorBackend,
    Finset.sum_eq_single_of_mem (⟨0, hn⟩ : Fin n) (Finset.mem_univ _)
      (fun j _ hj => by
        have hjne : j.val ≠ 0 := fun hj0 => hj (Fin.ext (by simpa using hj0))
        rw [get_scalarPoly, if_neg hjne, monomial_zero_right])]
  rw [get_scalarPoly]
  simp [monomial_zero_left]

/-! ## The negacyclic modulus is monic of degree `n` -/

theorem negacyclicModulus_monic (hn : n ≠ 0) : (negacyclicModulus Coeff n).Monic := by
  simp only [negacyclicModulus]
  rw [show (1 : Polynomial Coeff) = C 1 from (C_1).symm]
  exact monic_X_pow_add_C 1 hn

theorem degree_negacyclicModulus [Nontrivial Coeff] (hn : 0 < n) :
    (negacyclicModulus Coeff n).degree = (n : WithBot ℕ) := by
  simp only [negacyclicModulus]
  rw [show (1 : Polynomial Coeff) = C 1 from (C_1).symm]
  exact degree_X_pow_add_C hn 1

/-! ## `ofBackend` is bijective for the vector backend -/

/-- The interpretation map is injective: two coefficient vectors with the same
class in `R[X] / (Xⁿ + 1)` are equal, since each is the unique degree-`< n`
representative. -/
theorem ofBackend_vectorBackend_injective [Nontrivial Coeff] (hn : 0 < n) :
    Function.Injective (NegacyclicQuotient.ofBackend (vectorBackend Coeff n)) := by
  intro p q hpq
  simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial] at hpq
  have hmem :
      (vectorBackend Coeff n).toPolynomial p - (vectorBackend Coeff n).toPolynomial q
        ∈ Ideal.span {negacyclicModulus Coeff n} := (Ideal.Quotient.eq).mp hpq
  have hdvd : negacyclicModulus Coeff n ∣
      ((vectorBackend Coeff n).toPolynomial p - (vectorBackend Coeff n).toPolynomial q) :=
    Ideal.mem_span_singleton.mp hmem
  have hmono : (negacyclicModulus Coeff n).Monic := negacyclicModulus_monic hn.ne'
  have hdeg :
      ((vectorBackend Coeff n).toPolynomial p
          - (vectorBackend Coeff n).toPolynomial q).degree
        < (negacyclicModulus Coeff n).degree := by
    rw [degree_negacyclicModulus hn]
    exact lt_of_le_of_lt (degree_sub_le _ _)
      (max_lt (degree_toPolynomial_vectorBackend_lt p) (degree_toPolynomial_vectorBackend_lt q))
  -- A monic divisor of a strictly-smaller-degree polynomial forces it to vanish.
  have hzero :
      (vectorBackend Coeff n).toPolynomial p - (vectorBackend Coeff n).toPolynomial q = 0 := by
    have hmod0 :
        ((vectorBackend Coeff n).toPolynomial p - (vectorBackend Coeff n).toPolynomial q)
          %ₘ (negacyclicModulus Coeff n) = 0 := (modByMonic_eq_zero_iff_dvd hmono).mpr hdvd
    have hmodself :
        ((vectorBackend Coeff n).toPolynomial p - (vectorBackend Coeff n).toPolynomial q)
          %ₘ (negacyclicModulus Coeff n)
          = (vectorBackend Coeff n).toPolynomial p - (vectorBackend Coeff n).toPolynomial q :=
      (modByMonic_eq_self_iff hmono).mpr hdeg
    rw [← hmodself, hmod0]
  have htp : (vectorBackend Coeff n).toPolynomial p = (vectorBackend Coeff n).toPolynomial q :=
    sub_eq_zero.mp hzero
  apply Poly.ext_get_eq
  intro i
  have h := coeff_toPolynomial_vectorBackend p i
  rw [htp, coeff_toPolynomial_vectorBackend q i] at h
  exact h.symm

/-- The interpretation map is surjective: every class has a degree-`< n`
representative, whose coefficients form a preimage vector. -/
theorem ofBackend_vectorBackend_surjective [Nontrivial Coeff] (hn : 0 < n) :
    Function.Surjective (NegacyclicQuotient.ofBackend (vectorBackend Coeff n)) := by
  intro x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hmono : (negacyclicModulus Coeff n).Monic := negacyclicModulus_monic hn.ne'
  set r := g %ₘ (negacyclicModulus Coeff n) with hrdef
  have hrdeg : r.degree < (negacyclicModulus Coeff n).degree := degree_modByMonic_lt g hmono
  rw [degree_negacyclicModulus hn] at hrdeg
  have hrnat : r.natDegree < n := by
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; exact hn
    · exact (natDegree_lt_iff_degree_lt h0).mpr hrdeg
  have hget : ∀ i : Fin n,
      ((vectorBackend Coeff n).build (fun j : Fin n => r.coeff j.val)).get i = r.coeff i.val := by
    intro i
    have h := (vectorBackend Coeff n).coeff_build (fun j : Fin n => r.coeff j.val) i
    rwa [vectorBackend_coeff] at h
  refine ⟨(vectorBackend Coeff n).build (fun j : Fin n => r.coeff j.val), ?_⟩
  have htp :
      (vectorBackend Coeff n).toPolynomial
        ((vectorBackend Coeff n).build (fun j : Fin n => r.coeff j.val)) = r := by
    rw [toPolynomial_vectorBackend]
    have hsum : (∑ i : Fin n, monomial i.val
          (((vectorBackend Coeff n).build (fun j : Fin n => r.coeff j.val)).get i))
        = ∑ i : Fin n, monomial i.val (r.coeff i.val) :=
      Finset.sum_congr rfl (fun i _ => by rw [hget i])
    rw [hsum, show (∑ i : Fin n, monomial i.val (r.coeff i.val))
          = ∑ i ∈ Finset.range n, monomial i (r.coeff i)
        from Fin.sum_univ_eq_sum_range (fun k => monomial k (r.coeff k)) n]
    exact (as_sum_range' r n hrnat).symm
  change NegacyclicQuotient.ofBackend (vectorBackend Coeff n) _ = Ideal.Quotient.mk _ g
  simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial]
  rw [htp, hrdef]
  apply Ideal.Quotient.eq.mpr
  rw [modByMonic_eq_sub_mul_div g (negacyclicModulus Coeff n)]
  rw [show (g - negacyclicModulus Coeff n * (g /ₘ negacyclicModulus Coeff n)) - g
        = -(negacyclicModulus Coeff n * (g /ₘ negacyclicModulus Coeff n)) from by ring]
  exact neg_mem (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _))

/-- The interpretation map for the vector backend is bijective. -/
theorem ofBackend_vectorBackend_bijective [Nontrivial Coeff] (hn : 0 < n) :
    Function.Bijective (NegacyclicQuotient.ofBackend (vectorBackend Coeff n)) :=
  ⟨ofBackend_vectorBackend_injective hn, ofBackend_vectorBackend_surjective hn⟩


/-! ## Multiplicative structure transported onto the carrier

The additive group on `(vectorNegacyclicRing Coeff n).Poly` is the bundled one
from `LatticeCrypto.Ring.Kernel`. We add the missing multiplicative operations,
reusing the bundled negacyclic multiplication and the constant embedding
`scalarPoly`, so that the `CommRing` transport reuses this `+` (rather than
redefining it). -/

/-- `ofBackend` sends the unit `scalarPoly 1` to the one of the quotient. -/
theorem ofBackend_one (hn : 0 < n) :
    NegacyclicQuotient.ofBackend (vectorBackend Coeff n)
        ((vectorNegacyclicRing Coeff n).scalarPoly 1) = 1 := by
  simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial]
  rw [toPolynomial_scalarPoly hn 1, C_1]
  exact map_one _

/-! ## The transported `CommRing` instance

The multiplicative ring axioms for the bundled negacyclic multiplication are proved
as standalone facts about `(vectorNegacyclicRing Coeff n).mul` by transporting the
corresponding quotient identities along the injective interpretation `ofBackend`;
they are then assembled into a `CommRing` that **reuses** the bundled additive group
(so `+` is the existing one and `*` is `mul`), avoiding any instance diamond. -/

section CommRingInstance

variable [Nontrivial Coeff] [NeZero n]

private theorem npos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)

/-- `ofBackend` is multiplicative for the vector backend. -/
private theorem ofBackend_mul' (a b : (vectorNegacyclicRing Coeff n).Poly) :
    NegacyclicQuotient.ofBackend (vectorBackend Coeff n) ((vectorNegacyclicRing Coeff n).mul a b)
      = NegacyclicQuotient.ofBackend (vectorBackend Coeff n) a
        * NegacyclicQuotient.ofBackend (vectorBackend Coeff n) b :=
  (vectorNegacyclicSemantics Coeff n).mul_sound a b

/-- `ofBackend` is additive for the vector backend. -/
private theorem ofBackend_add' (a b : (vectorNegacyclicRing Coeff n).Poly) :
    NegacyclicQuotient.ofBackend (vectorBackend Coeff n) (a + b)
      = NegacyclicQuotient.ofBackend (vectorBackend Coeff n) a
        + NegacyclicQuotient.ofBackend (vectorBackend Coeff n) b :=
  (vectorNegacyclicSemantics Coeff n).add_sound a b

/-- `ofBackend` sends `0` to `0`. -/
private theorem ofBackend_zero' :
    NegacyclicQuotient.ofBackend (vectorBackend Coeff n)
        (0 : (vectorNegacyclicRing Coeff n).Poly) = 0 :=
  (vectorNegacyclicSemantics Coeff n).zero_sound

private theorem ring_mul_assoc' (a b c : (vectorNegacyclicRing Coeff n).Poly) :
    (vectorNegacyclicRing Coeff n).mul ((vectorNegacyclicRing Coeff n).mul a b) c
      = (vectorNegacyclicRing Coeff n).mul a ((vectorNegacyclicRing Coeff n).mul b c) :=
  ofBackend_vectorBackend_injective npos (by simp only [ofBackend_mul']; ring)

private theorem ring_one_mul' (a : (vectorNegacyclicRing Coeff n).Poly) :
    (vectorNegacyclicRing Coeff n).mul ((vectorNegacyclicRing Coeff n).scalarPoly 1) a = a :=
  ofBackend_vectorBackend_injective npos
    (by simp only [ofBackend_mul', ofBackend_one npos]; ring)

private theorem ring_mul_one' (a : (vectorNegacyclicRing Coeff n).Poly) :
    (vectorNegacyclicRing Coeff n).mul a ((vectorNegacyclicRing Coeff n).scalarPoly 1) = a :=
  ofBackend_vectorBackend_injective npos
    (by simp only [ofBackend_mul', ofBackend_one npos]; ring)

private theorem ring_left_distrib' (a b c : (vectorNegacyclicRing Coeff n).Poly) :
    (vectorNegacyclicRing Coeff n).mul a (b + c)
      = (vectorNegacyclicRing Coeff n).mul a b + (vectorNegacyclicRing Coeff n).mul a c :=
  ofBackend_vectorBackend_injective npos (by simp only [ofBackend_mul', ofBackend_add']; ring)

private theorem ring_right_distrib' (a b c : (vectorNegacyclicRing Coeff n).Poly) :
    (vectorNegacyclicRing Coeff n).mul (a + b) c
      = (vectorNegacyclicRing Coeff n).mul a c + (vectorNegacyclicRing Coeff n).mul b c :=
  ofBackend_vectorBackend_injective npos (by simp only [ofBackend_mul', ofBackend_add']; ring)

private theorem ring_mul_comm' (a b : (vectorNegacyclicRing Coeff n).Poly) :
    (vectorNegacyclicRing Coeff n).mul a b = (vectorNegacyclicRing Coeff n).mul b a :=
  ofBackend_vectorBackend_injective npos (by simp only [ofBackend_mul']; ring)

private theorem ring_zero_mul' (a : (vectorNegacyclicRing Coeff n).Poly) :
    (vectorNegacyclicRing Coeff n).mul 0 a = 0 :=
  ofBackend_vectorBackend_injective npos (by simp only [ofBackend_mul', ofBackend_zero']; ring)

private theorem ring_mul_zero' (a : (vectorNegacyclicRing Coeff n).Poly) :
    (vectorNegacyclicRing Coeff n).mul a 0 = 0 :=
  ofBackend_vectorBackend_injective npos (by simp only [ofBackend_mul', ofBackend_zero']; ring)

/-- The genuine commutative ring structure on `(vectorNegacyclicRing Coeff n).Poly`
(definitionally `Poly Coeff n`). It **reuses** the bundled additive group and takes
the bundled negacyclic multiplication as `*`; the multiplicative axioms are the
transported facts above. Reusing the additive group avoids any instance diamond, so
the linearity facts about `matVecMul` / `dot` / `scalarVecMul` become ordinary
`CommRing` facts. -/
noncomputable instance instCommRingPoly :
    CommRing ((vectorNegacyclicRing Coeff n).Poly) :=
  { (inferInstance : AddCommGroup ((vectorNegacyclicRing Coeff n).Poly)) with
    mul := (vectorNegacyclicRing Coeff n).mul
    one := (vectorNegacyclicRing Coeff n).scalarPoly 1
    mul_assoc := ring_mul_assoc'
    one_mul := ring_one_mul'
    mul_one := ring_mul_one'
    left_distrib := ring_left_distrib'
    right_distrib := ring_right_distrib'
    mul_comm := ring_mul_comm'
    zero_mul := ring_zero_mul'
    mul_zero := ring_mul_zero' }

end CommRingInstance

/-! ## Linearity / bilinearity of `matVecMul`, `dot`, `scalarVecMul`

Ordinary consequences of the transported `CommRing` on the vector-backed negacyclic
ring: `matVecMul` is additive and commutes with left scalar multiplication, and
scaling by a unit is injective. -/



/-- `Vector.foldl (· + ·) 0` over an `AddCommMonoid` is the `Finset.sum`. -/
private theorem foldl_add_eq_sum {M : Type*} [AddCommMonoid M] {k : ℕ} (g : Fin k → M) :
    (Vector.ofFn g).foldl (· + ·) 0 = ∑ i, g i := by
  haveI : Std.Commutative (α := M) (· + ·) := ⟨add_comm⟩
  haveI : Std.Associative (α := M) (· + ·) := ⟨add_assoc⟩
  show (Vector.ofFn g).toArray.foldl (· + ·) 0 = ∑ i, g i
  rw [← Array.foldl_toList,
    show (Vector.ofFn g).toArray.toList = List.ofFn g from Vector.toList_ofFn,
    List.foldl_eq_foldr, ← List.sum_eq_foldr, List.sum_ofFn]



section AlgebraicLaws

variable [Nontrivial Coeff] [NeZero n]

/-- `ring.mul` is the `CommRing` multiplication on the carrier. -/
private theorem mul_eq_hmul (a b : (vectorNegacyclicRing Coeff n).Poly) :
    (vectorNegacyclicRing Coeff n).mul a b = a * b := rfl

/-- `dot` is the `Finset.sum` of the coordinatewise products. -/
theorem dot_eq_sum {k : ℕ} (u v : PolyVec (vectorNegacyclicRing Coeff n).Poly k) :
    u ⬝ᵥ v = ∑ i : Fin k, u.get i * v.get i := by
  have hzip : Vector.zipWith (vectorNegacyclicRing Coeff n).mul u v
      = Vector.ofFn (fun i => u.get i * v.get i) := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_zipWith, Vector.getElem_ofFn]
    rfl
  show (Vector.zipWith (vectorNegacyclicRing Coeff n).mul u v).foldl
      (vectorNegacyclicRing Coeff n).add (vectorNegacyclicRing Coeff n).zero = _
  rw [hzip]
  exact foldl_add_eq_sum (fun i => u.get i * v.get i)






/-- Reading off a row of a matrix-vector product. -/
theorem matVecMul_getElem {rows cols : ℕ}
    (A : PolyMatrix (vectorNegacyclicRing Coeff n).Poly rows cols)
    (z : PolyVec (vectorNegacyclicRing Coeff n).Poly cols) {r : ℕ} (hr : r < rows) :
    (A *ᵥ z)[r]'hr = A[r]'hr ⬝ᵥ z :=
  Vector.getElem_map _ hr

/-- Reading off an entry of a scalar multiple (`.get` form). -/
theorem scalarVecMul_get {cols : ℕ} (c : (vectorNegacyclicRing Coeff n).Poly)
    (v : PolyVec (vectorNegacyclicRing Coeff n).Poly cols) (i : Fin cols) :
    ((vectorNegacyclicRing Coeff n).scalarVecMul c v).get i = c * v.get i := by
  rw [NegacyclicRing.scalarVecMul, Vector.get_map]; rfl

/-- Reading off an entry of a scalar multiple (`getElem` form). -/
theorem scalarVecMul_getElem {cols : ℕ} (c : (vectorNegacyclicRing Coeff n).Poly)
    (v : PolyVec (vectorNegacyclicRing Coeff n).Poly cols) {i : ℕ} (hi : i < cols) :
    ((vectorNegacyclicRing Coeff n).scalarVecMul c v)[i]'hi = c * v[i]'hi := by
  rw [NegacyclicRing.scalarVecMul, Vector.getElem_map]; rfl

/-- The bundled left scalar multiplication `scalarVecMul` is the ordinary scalar
action `•`: over the canonical vector-backed ring, scaling a `PolyVec` by a ring
element coincides with the pointwise `Vector` `SMul` (whose entrywise action is the
ring's own `Monoid` self-multiplication). This lets the Mathlib `•` notation stand
in for `scalarVecMul`. -/
@[simp]
theorem scalarVecMul_eq_smul {k : ℕ} (c : (vectorNegacyclicRing Coeff n).Poly)
    (v : PolyVec (vectorNegacyclicRing Coeff n).Poly k) :
    (vectorNegacyclicRing Coeff n).scalarVecMul c v = c • v := by
  apply Vector.ext
  intro i hi
  rw [NegacyclicRing.scalarVecMul]
  simp only [Vector.getElem_map, Vector.getElem_smul, smul_eq_mul]
  rfl

/-- `dot` distributes over subtraction in the second argument. -/
theorem dot_sub {k : ℕ} (u v w : PolyVec (vectorNegacyclicRing Coeff n).Poly k) :
    u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by
  simp only [dot_eq_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (v - w).get i = v.get i - w.get i from Vector.getElem_sub v w i.val i.isLt, mul_sub]

/-- `dot` pulls out a left scalar from the second argument. -/
theorem dot_scalarVecMul {k : ℕ} (c : (vectorNegacyclicRing Coeff n).Poly)
    (u v : PolyVec (vectorNegacyclicRing Coeff n).Poly k) :
    u ⬝ᵥ (vectorNegacyclicRing Coeff n).scalarVecMul c v = c * (u ⬝ᵥ v) := by
  simp only [dot_eq_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [scalarVecMul_get]
  ring

/-- Matrix-vector multiplication preserves subtraction. -/
theorem matVecMul_sub {rows cols : ℕ}
    (A : PolyMatrix (vectorNegacyclicRing Coeff n).Poly rows cols)
    (v w : PolyVec (vectorNegacyclicRing Coeff n).Poly cols) :
    A *ᵥ (v - w) = A *ᵥ v - A *ᵥ w := by
  apply Vector.ext; intro r hr
  rw [Vector.getElem_sub, matVecMul_getElem, matVecMul_getElem, matVecMul_getElem, dot_sub]

/-- Matrix-vector multiplication commutes with left scalar multiplication. -/
theorem matVecMul_scalarVecMul {rows cols : ℕ}
    (A : PolyMatrix (vectorNegacyclicRing Coeff n).Poly rows cols)
    (c : (vectorNegacyclicRing Coeff n).Poly)
    (v : PolyVec (vectorNegacyclicRing Coeff n).Poly cols) :
    A *ᵥ (vectorNegacyclicRing Coeff n).scalarVecMul c v
      = (vectorNegacyclicRing Coeff n).scalarVecMul c (A *ᵥ v) := by
  apply Vector.ext; intro r hr
  rw [scalarVecMul_getElem, matVecMul_getElem, matVecMul_getElem, dot_scalarVecMul]

/-- Left scalar multiplication by a unit is injective. -/
theorem scalarVecMul_injective_of_isUnit {cols : ℕ}
    {c : (vectorNegacyclicRing Coeff n).Poly} (hc : IsUnit c) :
    Function.Injective ((vectorNegacyclicRing Coeff n).scalarVecMul (cols := cols) c) := by
  intro v w h
  apply Vector.ext; intro i hi
  have hcong : ((vectorNegacyclicRing Coeff n).scalarVecMul c v)[i]'hi
      = ((vectorNegacyclicRing Coeff n).scalarVecMul c w)[i]'hi := by rw [h]
  rw [scalarVecMul_getElem, scalarVecMul_getElem] at hcong
  exact hc.mul_right_injective hcong

/-- Scaling by a product of two units preserves vector inequality. -/
theorem scalarVecMul_mul_ne_of_ne {cols : ℕ}
    {c d : (vectorNegacyclicRing Coeff n).Poly}
    {v w : PolyVec (vectorNegacyclicRing Coeff n).Poly cols}
    (hc : IsUnit c) (hd : IsUnit d) (hvw : v ≠ w) :
    (vectorNegacyclicRing Coeff n).scalarVecMul ((vectorNegacyclicRing Coeff n).mul c d) v
      ≠ (vectorNegacyclicRing Coeff n).scalarVecMul ((vectorNegacyclicRing Coeff n).mul d c) w := by
  intro h
  apply hvw
  rw [show (vectorNegacyclicRing Coeff n).mul d c = (vectorNegacyclicRing Coeff n).mul c d
        from mul_comm d c] at h
  exact scalarVecMul_injective_of_isUnit (hc.mul hd) h

/-- Equality of matrix products is preserved by scaling with a product of two scalars. -/
theorem matVecMul_scalarVecMul_mul_eq_of_eq {rows cols : ℕ}
    (A : PolyMatrix (vectorNegacyclicRing Coeff n).Poly rows cols)
    (c d : (vectorNegacyclicRing Coeff n).Poly)
    {v w : PolyVec (vectorNegacyclicRing Coeff n).Poly cols}
    (h : A *ᵥ v = A *ᵥ w) :
    A *ᵥ
        (vectorNegacyclicRing Coeff n).scalarVecMul ((vectorNegacyclicRing Coeff n).mul c d) v
      = A *ᵥ
        (vectorNegacyclicRing Coeff n).scalarVecMul ((vectorNegacyclicRing Coeff n).mul d c) w := by
  rw [matVecMul_scalarVecMul A ((vectorNegacyclicRing Coeff n).mul c d) v,
    matVecMul_scalarVecMul A ((vectorNegacyclicRing Coeff n).mul d c) w,
    show (vectorNegacyclicRing Coeff n).mul d c = (vectorNegacyclicRing Coeff n).mul c d
      from mul_comm d c, h]

end AlgebraicLaws

end LatticeCrypto
