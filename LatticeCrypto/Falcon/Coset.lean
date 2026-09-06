/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.Falcon.Scheme

/-!
# The coset condition of Falcon's trapdoor sampler

`Falcon.verify_sign_correct` and the GPV correctness law `CorrectAt` ask that every output
`(s₁, s₂)` of the trapdoor sampler at target `c` satisfy `s₁ + s₂ · h = c`. This file reduces
that condition to a statement about the primitives alone. `fromFFTPreimage` multiplies the
sampler's FFT-domain output by the FFT of the secret basis, inverse-transforms, and rounds;
`LandsOnLattice` says the rounded result is an integer lattice point `z · B`. Given that and
the key relations `f · h = g` and `F · h = G`, the coset identity is ring algebra in `R_q`,
carried out in the semantic quotient `ℤ_q[X]/(X^n + 1)` through the soundness certificate
`coeffSemantics` (`eval_fromFFTPreimage_of_landsOnLattice`, `hpreimage_of_landsOnLattice`).

`F · h = G` follows from the NTRU equation and `f · h = g` once `f` is invertible modulo `q`
(`capRelation_of_validKeyPair`), which Falcon's key generation guarantees and which is what
makes `h = g · f⁻¹` exist in the first place.

What remains for the concrete primitives is `LandsOnLattice` itself: that the fixed-point FFT
pipeline `fftInt`/`ifftRound` rounds to the exact lattice point, a deterministic rounding-error
bound on those two primitives.
-/

public section

open OracleComp OracleSpec LatticeCrypto

namespace Falcon

/-! ## Coefficients in `R_q` and reduction modulo `q` -/

theorem Rq.get_add {n : ℕ} (a b : Rq n) (i : Fin n) : (a + b).get i = a.get i + b.get i :=
  NegacyclicRing.coeff_add (coeffRing n) a b i

theorem Rq.get_sub {n : ℕ} (a b : Rq n) (i : Fin n) : (a - b).get i = a.get i - b.get i :=
  NegacyclicRing.coeff_sub (coeffRing n) a b i

theorem Rq.get_neg {n : ℕ} (a : Rq n) (i : Fin n) : (-a).get i = -a.get i :=
  NegacyclicRing.coeff_neg (coeffRing n) a i

theorem Rq.get_zero {n : ℕ} (i : Fin n) : (0 : Rq n).get i = 0 :=
  NegacyclicRing.coeff_zero (coeffRing n) i

theorem Rq.get_mul {n : ℕ} (a b : Rq n) (i : Fin n) :
    (negacyclicMul a b).get i = negacyclicConvCoeff a.get b.get i :=
  vectorKernel_mul_get a b i

theorem IntPoly.get_mul {n : ℕ} (a b : IntPoly n) (i : Fin n) :
    (intPolyMul a b).get i = negacyclicConvCoeff a.get b.get i :=
  vectorKernel_mul_get a b i

theorem toRq_add {n : ℕ} (a b : IntPoly n) :
    IntPoly.toRq (a + b) = IntPoly.toRq a + IntPoly.toRq b := by
  apply Poly.ext_get_eq
  intro i
  rw [toRq_get, Poly.get_add, Rq.get_add, toRq_get, toRq_get]
  push_cast
  rfl

theorem toRq_sub {n : ℕ} (a b : IntPoly n) :
    IntPoly.toRq (a - b) = IntPoly.toRq a - IntPoly.toRq b := by
  apply Poly.ext_get_eq
  intro i
  rw [toRq_get, Poly.get_sub, Rq.get_sub, toRq_get, toRq_get]
  push_cast
  rfl

theorem toRq_neg {n : ℕ} (a : IntPoly n) : IntPoly.toRq (-a) = -IntPoly.toRq a := by
  apply Poly.ext_get_eq
  intro i
  rw [toRq_get, Poly.get_neg, Rq.get_neg, toRq_get]
  push_cast
  rfl

/-- Reduction modulo `q` turns the integer negacyclic product into the product in `R_q`. -/
theorem toRq_mul {n : ℕ} (a b : IntPoly n) :
    IntPoly.toRq (intPolyMul a b) = negacyclicMul (IntPoly.toRq a) (IntPoly.toRq b) := by
  apply Poly.ext_get_eq
  intro i
  rw [toRq_get, IntPoly.get_mul, Rq.get_mul]
  simp only [negacyclicConvCoeff, toRq_get]
  push_cast
  rfl

/-- The constant `q` reduces to zero modulo `q`. -/
theorem toRq_const_modulus (n : ℕ) :
    IntPoly.toRq (intPolyConst (modulus : ℤ) : IntPoly n) = 0 := by
  apply Poly.ext_get_eq
  intro i
  rw [toRq_get, Rq.get_zero]
  simp [intPolyConst, integralLift, vectorIntegralLift, constPoly]

/-! ## The semantic quotient -/

section Quotient

variable {n : ℕ} (hn : 0 < n)

theorem quotientOf_add (a b : Rq n) :
    (coeffSemantics hn).quotientOf (a + b) =
      (coeffSemantics hn).quotientOf a + (coeffSemantics hn).quotientOf b :=
  (coeffSemantics hn).add_sound a b

theorem quotientOf_sub (a b : Rq n) :
    (coeffSemantics hn).quotientOf (a - b) =
      (coeffSemantics hn).quotientOf a - (coeffSemantics hn).quotientOf b :=
  (coeffSemantics hn).sub_sound a b

theorem quotientOf_neg (a : Rq n) :
    (coeffSemantics hn).quotientOf (-a) = -(coeffSemantics hn).quotientOf a :=
  (coeffSemantics hn).neg_sound a

theorem quotientOf_mul (a b : Rq n) :
    (coeffSemantics hn).quotientOf (negacyclicMul a b) =
      (coeffSemantics hn).quotientOf a * (coeffSemantics hn).quotientOf b :=
  (coeffSemantics hn).mul_sound a b

theorem quotientOf_zero : (coeffSemantics hn).quotientOf (0 : Rq n) = 0 :=
  (coeffSemantics hn).zero_sound

theorem quotientOf_one : (coeffSemantics hn).quotientOf (1 : Rq n) = 1 :=
  (coeffSemantics hn).one_sound

theorem quotientOf_injective {a b : Rq n}
    (h : (coeffSemantics hn).quotientOf a = (coeffSemantics hn).quotientOf b) : a = b :=
  NegacyclicQuotient.ofBackend_injective (vectorBackend Coeff n) h

end Quotient

/-! ## The lattice-point condition and the coset identity -/

variable (p : Params) (prims : Primitives p)

/-- **The basis application lands on the lattice.** For the sampler's FFT-domain output `z`,
the two rounded inverse transforms of `fromFFTPreimage` are the integer polynomials
`z₀ · g + z₁ · G` and `-(z₀ · f + z₁ · F)` for some integer `(z₀, z₁)`: the lattice point
`z · B` for the secret basis `B = [[g, -f], [G, -F]]`. -/
def LandsOnLattice (sk : SecretKey p) (z : FFTPair p.fftDepth) : Prop :=
  ∃ z₀ z₁ : IntPoly p.n,
    prims.ifftRound (Primitives.mulFFT z.1 (prims.fftInt sk.g) +
        Primitives.mulFFT z.2 (prims.fftInt sk.capG)) =
      intPolyMul z₀ sk.g + intPolyMul z₁ sk.capG ∧
    prims.ifftRound (-(Primitives.mulFFT z.1 (prims.fftInt sk.f) +
        Primitives.mulFFT z.2 (prims.fftInt sk.capF))) =
      -(intPolyMul z₀ sk.f + intPolyMul z₁ sk.capF)

/-- **The coset identity.** On a lattice point, `fromFFTPreimage` returns a preimage of the
target: `s₁ + s₂ · h = c` follows from `f · h = g` and `F · h = G` by ring algebra. -/
theorem eval_fromFFTPreimage_of_landsOnLattice (hn : 0 < p.n) (pk : PublicKey p)
    (sk : SecretKey p)
    (hkey : negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)
    (hcap : negacyclicMul (IntPoly.toRq sk.capF) pk.h = IntPoly.toRq sk.capG)
    (c : Rq p.n) (z : FFTPair p.fftDepth) (hz : LandsOnLattice p prims sk z) :
    (falconPSF p prims).eval pk (fromFFTPreimage p prims c sk z) = c := by
  obtain ⟨z₀, z₁, h₀, h₁⟩ := hz
  change (c - IntPoly.toRq (prims.ifftRound _)) +
    negacyclicMul (-IntPoly.toRq (prims.ifftRound _)) pk.h = c
  rw [h₀, h₁, toRq_add, toRq_neg, toRq_add, toRq_mul, toRq_mul, toRq_mul, toRq_mul]
  apply quotientOf_injective hn
  have hk := congrArg (coeffSemantics hn).quotientOf hkey
  have hc := congrArg (coeffSemantics hn).quotientOf hcap
  simp only [quotientOf_mul] at hk hc
  simp only [quotientOf_add, quotientOf_sub, quotientOf_neg, quotientOf_mul]
  linear_combination ((coeffSemantics hn).quotientOf (IntPoly.toRq z₀)) * hk +
    ((coeffSemantics hn).quotientOf (IntPoly.toRq z₁)) * hc

/-- **The coset condition from the lattice-point condition.** Every output of the trapdoor
sampler is a preimage of its target once the basis application lands on the lattice for every
sample. This is the `hpreimage` hypothesis of `verify_sign_correct` and the `eval` half of
`CorrectAt`. -/
theorem hpreimage_of_landsOnLattice (hn : 0 < p.n) (pk : PublicKey p) (sk : SecretKey p)
    (hkey : negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)
    (hcap : negacyclicMul (IntPoly.toRq sk.capF) pk.h = IntPoly.toRq sk.capG)
    (hz : ∀ c : Rq p.n, ∀ z ∈ support
      (Primitives.ffSampling prims p.fftDepth (toFFTTarget p prims c sk) sk.tree),
      LandsOnLattice p prims sk z) :
    ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
      x ∈ support ((falconPSF p prims).trapdoorSample pk sk c) →
        (falconPSF p prims).eval pk x = c := by
  intro c x hx
  change x ∈ support (do
    let z ← Primitives.ffSampling prims p.fftDepth (toFFTTarget p prims c sk) sk.tree
    return fromFFTPreimage p prims c sk z) at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨z, hzmem, hx⟩ := hx
  rw [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact eval_fromFFTPreimage_of_landsOnLattice p prims hn pk sk hkey hcap c z (hz c z hzmem)

/-- **`F · h = G` on a valid key with `f` invertible modulo `q`.** From the NTRU equation
`f · G − g · F = q` reduced modulo `q` and `f · h = g`, cancelling `f`. -/
theorem capRelation_of_validKeyPair (hn : 0 < p.n) (pk : PublicKey p) (sk : SecretKey p)
    (hvalid : validKeyPair p pk sk = true)
    (hunit : ∃ u : Rq p.n, negacyclicMul (IntPoly.toRq sk.f) u = 1) :
    negacyclicMul (IntPoly.toRq sk.capF) pk.h = IntPoly.toRq sk.capG := by
  rw [validKeyPair_eq_true_iff] at hvalid
  obtain ⟨hntru, hkey⟩ := hvalid
  obtain ⟨u, hu⟩ := hunit
  have hq : IntPoly.toRq (intPolyMul sk.f sk.capG - intPolyMul sk.g sk.capF) =
      IntPoly.toRq (intPolyConst (modulus : ℤ)) := by
    unfold ntruEquation at hntru
    rw [hntru]
  rw [toRq_sub, toRq_mul, toRq_mul, toRq_const_modulus] at hq
  apply quotientOf_injective hn
  have hq' := congrArg (coeffSemantics hn).quotientOf hq
  have hk := congrArg (coeffSemantics hn).quotientOf hkey
  have hu' := congrArg (coeffSemantics hn).quotientOf hu
  simp only [quotientOf_sub, quotientOf_mul, quotientOf_zero, quotientOf_one] at hq' hk hu'
  rw [quotientOf_mul]
  set Q := (coeffSemantics hn).quotientOf with hQ
  linear_combination (-(Q u)) * hq' + (Q u * Q (IntPoly.toRq sk.capF)) * hk +
    (Q (IntPoly.toRq sk.capG) - Q (IntPoly.toRq sk.capF) * Q pk.h) * hu'

end Falcon

end
