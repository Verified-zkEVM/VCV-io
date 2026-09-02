/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.Falcon.SISBridge
public import LatticeCrypto.Falcon.Concrete.NTT

/-!
# Falcon attempt-level frontier: a witness at a genuine NTRU key with a rejecting sampler

`Falcon.euf_cma_security` is a conditional theorem. This file instantiates
its hypothesis bundle at an instance that has the real structure of a Falcon key and a real
rejection loop, and pins the numbers the attempt-level frontier produces there.

## The instance

* **Ring degree `n = 2` at Falcon's modulus `q = 12289`.** The ring `ℤ[x]/(x² + 1)` is the
  Gaussian integers, and `q = 108² + 25²` splits in it. The key
  `f = −106 + 32x`, `g = 5 + 2x`, `F = −5 + 2x`, `G = −106 − 32x`
  satisfies the NTRU equation `fG − gF = q` exactly, `f` is invertible modulo `q`, and the
  public key is `h = g · f⁻¹ = 8915 + 8488x ≠ 0`. Both rows of the secret basis
  `[[g, −f], [G, −F]]` have squared norm exactly `q` and are orthogonal, so the NTRU lattice
  of this key has an orthogonal basis: Babai round-off against it is exact within the cube
  `[−½, ½]⁴`, whose image has squared norm at most `q`. The verifier's bound is therefore
  `betaSquared = q`, far below the trivial representative bound `n · (q/2)²`, and the
  short-vector target `4 · betaSquared` of the derived NTRU-SIS instance is far below `q²`,
  so the key vectors themselves are the only short solutions in sight — the shape of a genuine
  NTRU-SIS instance, at a size where nothing is hard.

* **Falcon's own sampler pipeline, with exact arithmetic.** The packed FFT of a degree-2
  polynomial `a + bx` is its value at `x = i`, encoded as `(a, b)`; on this encoding
  `Primitives.mulFFT` is polynomial multiplication and rounding is the identity on integer
  values, so `toFFTTarget`, `Primitives.ffSampling`, and `fromFFTPreimage` run Falcon's
  algorithm exactly. `SamplerZ(μ, σ)` is randomized rounding: `round μ + δ` with `δ` uniform on
  `{−1, 0, 1}`. The signing attempt is therefore the Babai round-off of the target perturbed
  by a uniform point of the box `{−1, 0, 1}⁴` in basis coordinates, followed by Falcon's norm
  check — a genuine rejection sampler, rejecting whenever the perturbation leaves the ball.

* **The idealized attempt is the attempt itself** (`ε_step = 0`, `attemptTransport_self_zero`),
  and the ideal PSF is its accept-conditional: uniform over the accepting perturbations. The
  rejection probability is at most `80/81` for every target (`toy_attemptRejectBound`): the
  unperturbed round-off always lands inside the ball (`toy_center_accepts`).

## What is pinned

* `falcon_attempt_hyps_inhabited`: every sampler-side hypothesis of
  `euf_cma_security` holds simultaneously at this instance, at
  `ε_step = 0` and `pRej = 80/81`.
* `toy_samplerLoss_lt_half`: at Falcon's signing budget `qSign = 2^64` the sampler loss of the
  attempt-level frontier is below `1/2` once the attempt budget is `5265`.
* `toy_oneShot_samplerLoss_one_le`: at the same instance the one-shot frontier is vacuous —
  its budget must absorb the per-draw rejection probability `8/9` at the target `c = 0`, so
  `qSign · ε_step ≥ 1` already at `qSign = 2`.

## What is not claimed

Regularity (`hReg`) is witnessed with the domain sampler that is the ideal sampler's own
marginal; it is a distribution, and the framework attaches no cost to sampling it, but only the
holder of the basis can sample it efficiently. A public domain sampler for a regular short
preimage sampler is the discrete Gaussian, and the guessing bound `idealSamplerGuessBound`
below the trivial budget needs its pointwise-mass theory; neither exists in this repository.
Nothing here is a security claim about any Falcon parameter set.
-/

@[expose] public section

open OracleComp OracleSpec Falcon LatticeCrypto ENNReal

namespace Falcon.NonVacuity

/-! ## Parameters and the NTRU key -/

/-- Ring degree `2` at Falcon's modulus, with the verifier's squared-norm bound `q`. Reducible,
so that `toyP.n` unfolds to `2` wherever the scheme's types meet the degree-2 arithmetic. -/
noncomputable abbrev toyP : Params :=
  { n := 2, sigma := 0, sigmaMin := 0, betaSquared := modulus, sbytelen := 0 }

theorem toyP_n : toyP.n = 2 := rfl

theorem toyP_fftDepth : toyP.fftDepth = 0 := rfl

theorem toyP_betaSquared : toyP.betaSquared = modulus := rfl

/-- The degree-2 integer polynomial `a + b x`. -/
def polyOfPair (a b : ℤ) : IntPoly 2 := Poly.ofPi ![a, b]

@[simp] theorem polyOfPair_get_zero (a b : ℤ) : (polyOfPair a b).get 0 = a := by
  simp [polyOfPair]

@[simp] theorem polyOfPair_get_one (a b : ℤ) : (polyOfPair a b).get 1 = b := by
  simp [polyOfPair]

/-- `f = −106 + 32x`. -/
def keyF : IntPoly 2 := polyOfPair (-106) 32
/-- `g = 5 + 2x`. -/
def keyG : IntPoly 2 := polyOfPair 5 2
/-- `F = −5 + 2x`. -/
def keyCapF : IntPoly 2 := polyOfPair (-5) 2
/-- `G = −106 − 32x`. -/
def keyCapG : IntPoly 2 := polyOfPair (-106) (-32)

/-- The public key `h = g · f⁻¹ mod q = 8915 + 8488x`. -/
noncomputable def keyH : Rq 2 := Poly.ofPi ![(8915 : ZMod modulus), 8488]

/-- Reduction of a degree-2 integer polynomial modulo `q`, coefficientwise. -/
theorem toRq_polyOfPair (a b : ℤ) :
    (IntPoly.toRq (polyOfPair a b) : Rq 2) =
      Poly.ofPi ![(a : ZMod modulus), (b : ZMod modulus)] := by
  apply Poly.ext_get_eq
  intro i
  fin_cases i <;> simp [IntPoly.toRq, integralLift, vectorIntegralLift, polyOfPair,
    PolyBackend.mapCoeffs, vectorBackend]

/-- The coefficients of the reduction of a degree-2 integer polynomial. -/
theorem toRq_get (a : IntPoly 2) (i : Fin 2) :
    (IntPoly.toRq a : Rq 2).get i = ((a.get i : ℤ) : ZMod modulus) := by
  simp [IntPoly.toRq, integralLift, vectorIntegralLift, PolyBackend.mapCoeffs, vectorBackend]

/-- **The NTRU equation** `fG − gF = q`, evaluated through the integer multiplier at
degree `2`. -/
theorem toy_ntruEquation_deg2 :
    intPolyMul (n := 2) keyF keyCapG - intPolyMul (n := 2) keyG keyCapF =
      intPolyConst (n := 2) (modulus : ℤ) := by
  unfold intPolyMul intPolyConst
  simp only [integralLift, vectorIntegralLift]
  apply Poly.ext_get_eq
  intro i
  fin_cases i <;>
  · simp only [schoolbookNegacyclicMul, keyF, keyG, keyCapF, keyCapG, polyOfPair, vectorKernel,
      vectorBackend, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.range'_succ, Poly.ofPi, Vector.toArray_ofFn, constPoly, Id.run]
    simp only [zero_add, Nat.reduceAdd, List.range'_zero, Order.lt_two_iff,
      Array.getD_eq_getD_getElem?, Int.reduceNeg, Array.set!_eq_setIfInBounds, List.forIn_cons,
      add_zero, Array.size_ofFn, zero_le, getElem?_pos, Array.getElem_ofFn, Fin.zero_eta,
      Fin.isValue, Matrix.cons_val_zero, Option.getD_some, mul_neg, sub_neg_eq_add,
      add_le_iff_nonpos_left, nonpos_iff_eq_zero, Std.le_refl, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, List.forIn_nil, bind_pure_comp, map_bind, ↓reduceIte, Nat.zero_mod,
      Array.size_replicate, Array.getElem_replicate, neg_mul, Int.reduceMul, neg_neg, Nat.mod_succ,
      pure_bind, Array.size_setIfInBounds, ne_eq, zero_ne_one, not_false_eq_true,
      Array.getElem_setIfInBounds_ne, map_pure, one_ne_zero, Nat.mod_self,
      Array.getElem?_setIfInBounds_ne, Array.getElem_setIfInBounds_self, add_neg_cancel,
      Array.setIfInBounds_setIfInBounds, Int.reduceAdd, Int.reduceSub, Poly.get_sub,
      Fin.val_eq_zero_iff, Vector.get_ofFn]
    change Vector.get (Vector.ofFn _) _ - Vector.get (Vector.ofFn _) _ = _
    simp only [Vector.get_ofFn, Array.getElem?_setIfInBounds, modulus]
    simp

/-- **The NTRU equation** `fG − gF = q` holds exactly for the key. -/
theorem toy_ntruEquation : ntruEquation toyP keyF keyG keyCapF keyCapG :=
  toy_ntruEquation_deg2

/-- The coefficients of the negacyclic product of two degree-2 polynomials. -/
theorem negacyclicMulPure_get (a b : IntPoly 2) (i : Fin 2) :
    (negacyclicMulPure (vectorKernel ℤ 2) a b).get i =
      negacyclicConvCoeff (fun j => a.get j) (fun j => b.get j) i := by
  simp [vectorBackend]

/-- `negacyclicMul` on `R_q` at degree `2` is the pure negacyclic convolution. -/
theorem negacyclicMul_get (a b : Rq 2) (i : Fin 2) :
    (negacyclicMul a b).get i =
      negacyclicConvCoeff (fun j => a.get j) (fun j => b.get j) i := by
  have hc := negacyclicMulPure_coeff (vectorKernel (ZMod modulus) 2) a b i
  simp only [vectorBackend] at hc
  exact hc

/-- Coefficients of a sum in `R_q` at degree `2`. -/
theorem Rq_get_add (a b : Rq 2) (i : Fin 2) : (a + b).get i = a.get i + b.get i :=
  LatticeCrypto.NegacyclicRing.coeff_add (coeffRing 2) a b i

/-- Coefficients of a difference in `R_q` at degree `2`. -/
theorem Rq_get_sub (a b : Rq 2) (i : Fin 2) : (a - b).get i = a.get i - b.get i :=
  LatticeCrypto.NegacyclicRing.coeff_sub (coeffRing 2) a b i

/-- Coefficients of a negation in `R_q` at degree `2`. -/
theorem Rq_get_neg (a : Rq 2) (i : Fin 2) : (-a).get i = -a.get i :=
  LatticeCrypto.NegacyclicRing.coeff_neg (coeffRing 2) a i

/-- **The public-key relation** `f · h = g` in `R_q`. -/
theorem toy_keyRelation : negacyclicMul (IntPoly.toRq keyF) keyH = IntPoly.toRq keyG := by
  rw [keyF, keyG, toRq_polyOfPair, toRq_polyOfPair]
  apply Poly.ext_get_eq
  intro i
  fin_cases i <;> simp (config := { decide := true }) [negacyclicMul_get, negacyclicConvCoeff,
    Fintype.sum_prod_type, Fin.sum_univ_two, keyH]

/-- `F · h = G` in `R_q`, the second column relation of the basis. -/
theorem toy_capRelation :
    negacyclicMul (IntPoly.toRq keyCapF) keyH = IntPoly.toRq keyCapG := by
  rw [keyCapF, keyCapG, toRq_polyOfPair, toRq_polyOfPair]
  apply Poly.ext_get_eq
  intro i
  fin_cases i <;> simp (config := { decide := true }) [negacyclicMul_get, negacyclicConvCoeff,
    Fintype.sum_prod_type, Fin.sum_univ_two, keyH]

/-- The public key. -/
noncomputable def toyPk : PublicKey toyP := { h := keyH }

/-- The public key is not degenerate: `h ≠ 0`. -/
theorem toyPk_h_ne_zero : toyPk.h ≠ 0 := by
  intro h
  have h' : (toyPk.h : Rq 2) = (0 : Rq 2) := h
  have := congrArg (fun p : Rq 2 => p.get 0) h'
  simp only [toyPk, keyH, Poly.get_ofPi, Matrix.cons_val_zero] at this
  rw [show (0 : Rq 2).get 0 = 0 from
    LatticeCrypto.NegacyclicRing.coeff_zero (coeffRing 2) ⟨0, by decide⟩] at this
  exact absurd this (by decide)

/-- The Falcon tree at depth `0`. -/
noncomputable def toyTree : FalconTree toyP.fftDepth := FalconTree.leaf 0

/-- The secret key: the NTRU basis `(f, g, F, G)`. -/
noncomputable def toySk : SecretKey toyP :=
  { f := keyF, g := keyG, capF := keyCapF, capG := keyCapG, tree := toyTree }

/-- **The key pair is a valid Falcon key.** -/
theorem toy_validKeyPair : validKeyPair toyP toyPk toySk = true := by
  rw [validKeyPair_eq_true_iff]
  exact ⟨toy_ntruEquation, toy_keyRelation⟩

/-! ## Exact packed FFT at degree `2`

At depth `0` a packed FFT polynomial is a pair of reals `(re, im)`: the value of the degree-2
polynomial `a + bx` at `x = i`. On this encoding the packed pointwise product is complex
multiplication, i.e. multiplication in `ℤ[x]/(x² + 1)`. -/

/-- The exact packed FFT of a degree-2 integer polynomial. -/
noncomputable def fftInt2 (a : IntPoly 2) : RealFFTPoly 0 :=
  Vector.ofFn fun j : Fin 2 => ((a.get j : ℤ) : ℝ)

/-- The packed FFT of a hash target, its coefficients read in `[0, q)`. -/
noncomputable def fftTarget2 (c : Rq 2) : RealFFTPoly 0 :=
  Vector.ofFn fun j : Fin 2 => (((c.get j).val : ℕ) : ℝ)

/-- Inverse packed FFT with rounding: the pair `(re, im)` becomes `round re + (round im) x`. -/
noncomputable def ifftRound2 (v : RealFFTPoly 0) : IntPoly 2 :=
  Poly.ofPi fun j : Fin 2 => round (v.get j)

theorem re_fftInt2 (a : IntPoly 2) : RealFFTPoly.re (fftInt2 a) 0 = (a.get 0 : ℝ) := by
  simp [RealFFTPoly.re, fftInt2, Vector.get_ofFn]

theorem im_fftInt2 (a : IntPoly 2) : RealFFTPoly.im (fftInt2 a) 0 = (a.get 1 : ℝ) := by
  simp [RealFFTPoly.im, fftInt2, Vector.get_ofFn]

/-- Packed pointwise multiplication is negacyclic multiplication on the exact encoding. -/
theorem mulFFT_fftInt2 (a b : IntPoly 2) :
    Primitives.mulFFT (fftInt2 a) (fftInt2 b) =
      fftInt2 (negacyclicMulPure (vectorKernel ℤ 2) a b) := by
  have hc := fun i => negacyclicMulPure_coeff (vectorKernel ℤ 2) a b i
  simp only [vectorBackend] at hc
  conv_rhs => unfold fftInt2
  apply Vector.ext
  intro j hj
  interval_cases j <;>
  simp [Primitives.mulFFT, RealFFTPoly.pack, Vector.getElem_ofFn, Vector.get_ofFn, re_fftInt2,
    im_fftInt2, hc, negacyclicConvCoeff, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- Rounding is the identity on the exact encoding of an integer polynomial. -/
theorem ifftRound2_fftInt2 (a : IntPoly 2) : ifftRound2 (fftInt2 a) = a := by
  apply Poly.ext_get_eq
  intro i
  simp [ifftRound2, fftInt2, Vector.get_ofFn]

theorem add_fftInt2 (a b : IntPoly 2) : fftInt2 a + fftInt2 b = fftInt2 (a + b) := by
  apply Vector.ext
  intro j hj
  simp [fftInt2, Vector.getElem_ofFn, Vector.getElem_add]

theorem neg_fftInt2 (a : IntPoly 2) : -fftInt2 a = fftInt2 (-a) := by
  apply Vector.ext
  intro j hj
  simp [fftInt2, Vector.getElem_ofFn, Vector.getElem_neg]

/-- The sampled output of `ffSampling` at depth `0` is the exact encoding of the integer
polynomial with the two sampled coordinates. -/
theorem pack_eq_fftInt2 (x y : ℤ) :
    RealFFTPoly.pack (k := 0) (Vector.ofFn fun _ => (x : ℝ)) (Vector.ofFn fun _ => (y : ℝ)) =
      fftInt2 (polyOfPair x y) := by
  apply Vector.ext
  intro j hj
  interval_cases j <;> simp [RealFFTPoly.pack, fftInt2, Vector.getElem_ofFn, Vector.get_ofFn]

/-! ## The primitives: exact arithmetic and a perturbed-rounding sampler -/

/-- `SamplerZ(μ, σ)` as randomized rounding: `round μ + δ` with `δ` uniform on `{−1, 0, 1}`. -/
noncomputable def toySamplerZ (μ : ℝ) (_σ : ℝ) : ProbComp ℤ := do
  let δ ← $ᵗ (Fin 3)
  pure (round μ + ((δ : ℕ) : ℤ) - 1)

/-- The primitives of the instance: exact packed FFT, perturbed rounding, and trivial
encodings. Only the sampler pipeline (`samplerZ`, `fftTarget`, `fftInt`, `ifftRound`) is ever
executed by the security statements. -/
noncomputable def toyPrims : Primitives toyP where
  publicKeyBytes := fun _ => ByteArray.empty
  hashToPoint := fun _ _ _ => 0
  samplerZ := toySamplerZ
  fftTarget := fftTarget2
  fftInt := fftInt2
  ifftRound := ifftRound2
  compress := fun _ _ => none
  decompress := fun _ _ => none
  nttOps := Falcon.Concrete.concreteNTTRingOps 1

theorem toyPrims_samplerZ : toyPrims.samplerZ = toySamplerZ := rfl

/-! ## The signing attempt as a box sampler

`Primitives.ffSampling` at depth `0` makes four `samplerZ` calls, one per real coordinate of the
target pair `(t₀, t₁)`; with `toySamplerZ` each returns the rounded coordinate plus an offset in
`{−1, 0, 1}`. The attempt is therefore a uniform draw from the box `(Fin 3)⁴`, mapped through the
lattice basis and Falcon's norm check. -/

/-- The perturbation box: four independent draws from `Fin 3`, read as offsets in `{−1, 0, 1}`. -/
abbrev Box : Type := Fin 3 × Fin 3 × Fin 3 × Fin 3

/-- The offset encoded by a box coordinate. -/
def off (d : Fin 3) : ℤ := ((d : ℕ) : ℤ) - 1

/-- The center of the box: no perturbation. -/
def center : Box := (1, 1, 1, 1)

@[simp] theorem off_one : off 1 = 0 := rfl

/-- The target pair `toFFTTarget` at this key, for target `c`. -/
noncomputable def tgt (c : Rq 2) : FFTPair 0 := toFFTTarget toyP toyPrims c toySk

/-- The sampled lattice coordinates `(z₀, z₁)` for target `c` and box point `δ`: the rounded
target coordinates, each offset by the corresponding box coordinate. -/
noncomputable def zOf (c : Rq 2) (δ : Box) : IntPoly 2 × IntPoly 2 :=
  (polyOfPair (round (RealFFTPoly.re (tgt c).1 0) + off δ.1)
      (round (RealFFTPoly.im (tgt c).1 0) + off δ.2.1),
   polyOfPair (round (RealFFTPoly.re (tgt c).2 0) + off δ.2.2.1)
      (round (RealFFTPoly.im (tgt c).2 0) + off δ.2.2.2))

/-- The candidate preimage for target `c` and box point `δ`: `(c − v₀, −v₁)` for the lattice
point `v = z · B`. -/
noncomputable def sOf (c : Rq 2) (δ : Box) : Rq 2 × Rq 2 :=
  fromFFTPreimage toyP toyPrims c toySk (fftInt2 (zOf c δ).1, fftInt2 (zOf c δ).2)

/-- Falcon's trapdoor sampler at these primitives is the box sampler. -/
theorem toy_trapdoorSample (c : Rq 2) :
    (falconPSF toyP toyPrims).trapdoorSample toyPk toySk c = (fun δ => sOf c δ) <$> ($ᵗ Box) := by
  change (do
    let z ← Primitives.ffSampling toyPrims 0 (tgt c) (FalconTree.leaf 0)
    pure (fromFFTPreimage toyP toyPrims c toySk z)) = _
  simp only [Primitives.ffSampling, toyPrims_samplerZ, toySamplerZ, bind_assoc, pure_bind]
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun d₀ => bind_congr fun d₁ => bind_congr fun d₂ => bind_congr fun d₃ => ?_
  simp only [sOf, zOf, off, tgt, pack_eq_fftInt2, Fin.zero_eta, add_sub_assoc]
  rfl

/-- The signing attempt at these primitives: draw a box point and accept iff the candidate is
short. -/
theorem toy_signAttempt (c : Rq 2) :
    signAttempt toyP toyPrims toyPk toySk c =
      (fun δ => if (falconPSF toyP toyPrims).isShort (sOf c δ) then some (sOf c δ) else none)
        <$> ($ᵗ Box) := by
  unfold signAttempt
  rw [toy_trapdoorSample]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun δ => ?_
  split_ifs <;> rfl

/-! ## Every candidate is a preimage of the target -/

/-- The candidate's components as reductions of integer polynomials. -/
theorem sOf_eq (c : Rq 2) (δ : Box) :
    sOf c δ =
      (c - IntPoly.toRq (negacyclicMulPure (vectorKernel ℤ 2) (zOf c δ).1 keyG +
          negacyclicMulPure (vectorKernel ℤ 2) (zOf c δ).2 keyCapG),
       -IntPoly.toRq (-(negacyclicMulPure (vectorKernel ℤ 2) (zOf c δ).1 keyF +
          negacyclicMulPure (vectorKernel ℤ 2) (zOf c δ).2 keyCapF))) := by
  change (c - IntPoly.toRq (ifftRound2 (Primitives.mulFFT (k := 0) (fftInt2 _) (fftInt2 keyG) +
      Primitives.mulFFT (k := 0) (fftInt2 _) (fftInt2 keyCapG))),
    -IntPoly.toRq (ifftRound2 (-(Primitives.mulFFT (k := 0) (fftInt2 _) (fftInt2 keyF) +
      Primitives.mulFFT (k := 0) (fftInt2 _) (fftInt2 keyCapF))))) = _
  simp only [mulFFT_fftInt2, add_fftInt2, neg_fftInt2, ifftRound2_fftInt2]

/-- **Coset membership.** Every candidate evaluates to the target: `s₁ + s₂ · h = c`. -/
theorem toy_eval_sOf (c : Rq 2) (δ : Box) :
    (falconPSF toyP toyPrims).eval toyPk (sOf c δ) = c := by
  rw [sOf_eq]
  change _ + negacyclicMul _ _ = _
  apply Poly.ext_get_eq
  intro i
  fin_cases i <;>
  · simp only [Rq_get_add, Rq_get_sub, Rq_get_neg, negacyclicMul_get, toRq_get, Poly.get_add,
      Poly.get_neg, negacyclicMulPure_get, negacyclicConvCoeff, Fintype.sum_prod_type,
      Fin.sum_univ_two, toyPk, keyH, keyF, keyG, keyCapF, keyCapG, polyOfPair_get_zero,
      polyOfPair_get_one, Poly.get_ofPi, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp
    ring_nf
    -- The surviving coefficients are the multiples `99q`, `50q`, `5q`, `2q` of the modulus.
    simp only [show (1216611 : ZMod modulus) = 0 from by decide,
      show (614450 : ZMod modulus) = 0 from by decide,
      show (61445 : ZMod modulus) = 0 from by decide,
      show (24578 : ZMod modulus) = 0 from by decide, mul_zero, sub_zero, add_zero]

/-! ## The unperturbed round-off lands in the ball

For the target `c` with coefficients `c̃ = (c̃₀, c̃₁)` read in `[0, q)`, Falcon's target pair is
`t = (c̃, 0) · B⁻¹`, whose four real coordinates are explicit rationals in `c̃`. The center of
the box rounds each to the nearest integer; the resulting candidate is `u · B` for the rounding
residual `u = t − round t ∈ [−½, ½]⁴`, and since the rows of `B` are orthogonal of squared norm
`q`, its squared norm is `q · ‖u‖² ≤ q`. -/

theorem re_scaleFFT (r : ℝ) (v : RealFFTPoly 0) :
    RealFFTPoly.re (Primitives.scaleFFT r v) 0 = r * RealFFTPoly.re v 0 := by
  simp [RealFFTPoly.re, Primitives.scaleFFT, Vector.get_ofFn]

theorem im_scaleFFT (r : ℝ) (v : RealFFTPoly 0) :
    RealFFTPoly.im (Primitives.scaleFFT r v) 0 = r * RealFFTPoly.im v 0 := by
  simp [RealFFTPoly.im, Primitives.scaleFFT, Vector.get_ofFn]

theorem re_mulFFT (a b : RealFFTPoly 0) :
    RealFFTPoly.re (Primitives.mulFFT a b) 0 =
      RealFFTPoly.re a 0 * RealFFTPoly.re b 0 - RealFFTPoly.im a 0 * RealFFTPoly.im b 0 := by
  simp [RealFFTPoly.re, RealFFTPoly.im, Primitives.mulFFT, RealFFTPoly.pack, Vector.get_ofFn]

theorem im_mulFFT (a b : RealFFTPoly 0) :
    RealFFTPoly.im (Primitives.mulFFT a b) 0 =
      RealFFTPoly.re a 0 * RealFFTPoly.im b 0 + RealFFTPoly.im a 0 * RealFFTPoly.re b 0 := by
  simp [RealFFTPoly.re, RealFFTPoly.im, Primitives.mulFFT, RealFFTPoly.pack, Vector.get_ofFn]

theorem re_fftTarget2 (c : Rq 2) : RealFFTPoly.re (fftTarget2 c) 0 = ((c.get 0).val : ℝ) := by
  simp [RealFFTPoly.re, fftTarget2, Vector.get_ofFn]

theorem im_fftTarget2 (c : Rq 2) : RealFFTPoly.im (fftTarget2 c) 0 = ((c.get 1).val : ℝ) := by
  simp [RealFFTPoly.im, fftTarget2, Vector.get_ofFn]

/-- The target pair, coordinate by coordinate: `t₀ = c̃ · (−F) / q` and `t₁ = c̃ · f / q`. -/
theorem tgt_coords (c : Rq 2) :
    RealFFTPoly.re (tgt c).1 0 = (5 * ((c.get 0).val : ℝ) + 2 * ((c.get 1).val : ℝ)) / modulus ∧
    RealFFTPoly.im (tgt c).1 0 = (5 * ((c.get 1).val : ℝ) - 2 * ((c.get 0).val : ℝ)) / modulus ∧
    RealFFTPoly.re (tgt c).2 0 =
      -(106 * ((c.get 0).val : ℝ) + 32 * ((c.get 1).val : ℝ)) / modulus ∧
    RealFFTPoly.im (tgt c).2 0 =
      -(106 * ((c.get 1).val : ℝ) - 32 * ((c.get 0).val : ℝ)) / modulus := by
  have hF : (-keyCapF : IntPoly 2) = polyOfPair 5 (-2) := by
    apply Poly.ext_get_eq; intro i; fin_cases i <;> simp [keyCapF]
  have hf : (-keyF : IntPoly 2) = polyOfPair 106 (-32) := by
    apply Poly.ext_get_eq; intro i; fin_cases i <;> simp [keyF]
  change RealFFTPoly.re (Primitives.scaleFFT (k := 0) _ (Primitives.mulFFT (fftTarget2 c)
      (fftInt2 (-keyCapF)))) 0 = _ ∧
    RealFFTPoly.im (Primitives.scaleFFT (k := 0) _ (Primitives.mulFFT (fftTarget2 c)
      (fftInt2 (-keyCapF)))) 0 = _ ∧
    RealFFTPoly.re (Primitives.scaleFFT (k := 0) _ (Primitives.mulFFT (fftInt2 (-keyF))
      (fftTarget2 c))) 0 = _ ∧
    RealFFTPoly.im (Primitives.scaleFFT (k := 0) _ (Primitives.mulFFT (fftInt2 (-keyF))
      (fftTarget2 c))) 0 = _
  rw [hF, hf]
  simp only [re_scaleFFT, im_scaleFFT, re_mulFFT, im_mulFFT, re_fftTarget2, im_fftTarget2,
    re_fftInt2, im_fftInt2, polyOfPair_get_zero, polyOfPair_get_one]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- The coordinates read by the sampler at target `c`. -/
noncomputable def ta (c : Rq 2) : ℝ := RealFFTPoly.re (tgt c).1 0
noncomputable def tb (c : Rq 2) : ℝ := RealFFTPoly.im (tgt c).1 0
noncomputable def tc (c : Rq 2) : ℝ := RealFFTPoly.re (tgt c).2 0
noncomputable def td (c : Rq 2) : ℝ := RealFFTPoly.im (tgt c).2 0

/-- The integer coefficients of the unperturbed candidate `(c̃ − z·B)`, with `z = round t`. -/
noncomputable def s10 (c : Rq 2) : ℤ :=
  ((c.get 0).val : ℤ) - (5 * round (ta c) - 2 * round (tb c) - 106 * round (tc c) +
    32 * round (td c))
noncomputable def s11 (c : Rq 2) : ℤ :=
  ((c.get 1).val : ℤ) - (2 * round (ta c) + 5 * round (tb c) - 32 * round (tc c) -
    106 * round (td c))
noncomputable def s20 (c : Rq 2) : ℤ :=
  -(106 * round (ta c) + 32 * round (tb c) + 5 * round (tc c) + 2 * round (td c))
noncomputable def s21 (c : Rq 2) : ℤ :=
  32 * round (ta c) - 106 * round (tb c) + 2 * round (tc c) - 5 * round (td c)

theorem zOf_center (c : Rq 2) :
    zOf c center = (polyOfPair (round (ta c)) (round (tb c)),
      polyOfPair (round (tc c)) (round (td c))) := by
  simp [zOf, center, ta, tb, tc, td]

/-- The unperturbed candidate, coefficient by coefficient. -/
theorem sOf_center_eq (c : Rq 2) :
    sOf c center = (IntPoly.toRq (polyOfPair (s10 c) (s11 c)),
      IntPoly.toRq (polyOfPair (s20 c) (s21 c))) := by
  rw [sOf_eq, zOf_center]
  refine Prod.ext ?_ ?_
  · apply Poly.ext_get_eq
    intro i
    fin_cases i <;>
    · simp only [Rq_get_sub, toRq_get, Poly.get_add, negacyclicMulPure_get, negacyclicConvCoeff,
        Fintype.sum_prod_type, Fin.sum_univ_two, keyG, keyCapG, polyOfPair_get_zero,
        polyOfPair_get_one, s10, s11]
      simp
      ring
  · apply Poly.ext_get_eq
    intro i
    fin_cases i <;>
    · simp only [Rq_get_neg, toRq_get, Poly.get_add, Poly.get_neg, negacyclicMulPure_get,
        negacyclicConvCoeff, Fintype.sum_prod_type, Fin.sum_univ_two, keyF, keyCapF,
        polyOfPair_get_zero, polyOfPair_get_one, s20, s21]
      simp
      ring

/-- The rounding residuals `u = t − round t`. -/
noncomputable def ua (c : Rq 2) : ℝ := ta c - round (ta c)
noncomputable def ub (c : Rq 2) : ℝ := tb c - round (tb c)
noncomputable def uc (c : Rq 2) : ℝ := tc c - round (tc c)
noncomputable def ud (c : Rq 2) : ℝ := td c - round (td c)

theorem modulus_real : (modulus : ℝ) = 12289 := by norm_num [modulus]

/-- **The candidate is the residual through the basis**: `ŝ = u · B`, as real identities. -/
theorem s_eq_uB (c : Rq 2) :
    ((s10 c : ℤ) : ℝ) = 5 * ua c - 2 * ub c - 106 * uc c + 32 * ud c ∧
    ((s11 c : ℤ) : ℝ) = 2 * ua c + 5 * ub c - 32 * uc c - 106 * ud c ∧
    ((s20 c : ℤ) : ℝ) = 106 * ua c + 32 * ub c + 5 * uc c + 2 * ud c ∧
    ((s21 c : ℤ) : ℝ) = -32 * ua c + 106 * ub c - 2 * uc c + 5 * ud c := by
  obtain ⟨ha, hb, hc, hd⟩ := tgt_coords c
  have hq : (modulus : ℝ) ≠ 0 := by rw [modulus_real]; norm_num
  simp only [s10, s11, s20, s21, ua, ub, uc, ud, ta, tb, tc, td] at *
  rw [ha, hb, hc, hd]
  push_cast
  rw [modulus_real] at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The rounding residuals lie in `[−½, ½]`. -/
theorem abs_u_le (c : Rq 2) :
    |ua c| ≤ 1 / 2 ∧ |ub c| ≤ 1 / 2 ∧ |uc c| ≤ 1 / 2 ∧ |ud c| ≤ 1 / 2 :=
  ⟨abs_sub_round _, abs_sub_round _, abs_sub_round _, abs_sub_round _⟩

/-- **Orthogonality of the basis.** The squared norm of the candidate is `q · ‖u‖²`, hence at
most `q`. -/
theorem s_normSq_le (c : Rq 2) :
    ((s10 c : ℤ) : ℝ) ^ 2 + ((s11 c : ℤ) : ℝ) ^ 2 + ((s20 c : ℤ) : ℝ) ^ 2 +
      ((s21 c : ℤ) : ℝ) ^ 2 ≤ 12289 := by
  obtain ⟨h1, h2, h3, h4⟩ := s_eq_uB c
  obtain ⟨ha, hb, hc, hd⟩ := abs_u_le c
  rw [h1, h2, h3, h4]
  have hnorm : (5 * ua c - 2 * ub c - 106 * uc c + 32 * ud c) ^ 2 +
      (2 * ua c + 5 * ub c - 32 * uc c - 106 * ud c) ^ 2 +
      (106 * ua c + 32 * ub c + 5 * uc c + 2 * ud c) ^ 2 +
      (-32 * ua c + 106 * ub c - 2 * uc c + 5 * ud c) ^ 2 =
      12289 * (ua c ^ 2 + ub c ^ 2 + uc c ^ 2 + ud c ^ 2) := by ring
  rw [hnorm]
  have ha2 : ua c ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp ha; nlinarith [this.1, this.2]
  have hb2 : ub c ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hb; nlinarith [this.1, this.2]
  have hc2 : uc c ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hc; nlinarith [this.1, this.2]
  have hd2 : ud c ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hd; nlinarith [this.1, this.2]
  nlinarith

/-- Each coefficient of the candidate is at most `72` in absolute value. -/
theorem s_abs_le (c : Rq 2) :
    (s10 c).natAbs ≤ 72 ∧ (s11 c).natAbs ≤ 72 ∧ (s20 c).natAbs ≤ 72 ∧ (s21 c).natAbs ≤ 72 := by
  obtain ⟨h1, h2, h3, h4⟩ := s_eq_uB c
  obtain ⟨ha, hb, hc, hd⟩ := abs_u_le c
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hd' := abs_le.mp hd
  have key : ∀ z : ℤ, ((z : ℤ) : ℝ) ≤ 145 / 2 → -(145 / 2) ≤ ((z : ℤ) : ℝ) → z.natAbs ≤ 72 := by
    intro z hz1 hz2
    have hz1' : z ≤ 72 := by
      have : (z : ℝ) < 73 := by linarith
      exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
    have hz2' : -72 ≤ z := by
      have : (-73 : ℝ) < z := by linarith
      have h' : (-73 : ℤ) < z := by exact_mod_cast this
      omega
    omega
  refine ⟨key _ ?_ ?_, key _ ?_ ?_, key _ ?_ ?_, key _ ?_ ?_⟩ <;>
    first
    | (rw [h1]; linarith [ha'.1, ha'.2, hb'.1, hb'.2, hc'.1, hc'.2, hd'.1, hd'.2])
    | (rw [h2]; linarith [ha'.1, ha'.2, hb'.1, hb'.2, hc'.1, hc'.2, hd'.1, hd'.2])
    | (rw [h3]; linarith [ha'.1, ha'.2, hb'.1, hb'.2, hc'.1, hc'.2, hd'.1, hd'.2])
    | (rw [h4]; linarith [ha'.1, ha'.2, hb'.1, hb'.2, hc'.1, hc'.2, hd'.1, hd'.2])

/-- The squared norm of the unperturbed candidate: its coefficients are small enough that the
centered representatives modulo `q` are the integers themselves. -/
theorem pairL2NormSq_center (c : Rq 2) :
    pairL2NormSq (sOf c center).1 (sOf c center).2 =
      (s10 c).natAbs ^ 2 + (s11 c).natAbs ^ 2 + (s20 c).natAbs ^ 2 + (s21 c).natAbs ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := s_abs_le c
  rw [sOf_center_eq]
  change (∑ i : Fin 2, (LatticeCrypto.centeredRepr
      ((IntPoly.toRq (polyOfPair (s10 c) (s11 c)) : Rq 2).get i)).natAbs ^ 2) +
    (∑ i : Fin 2, (LatticeCrypto.centeredRepr
      ((IntPoly.toRq (polyOfPair (s20 c) (s21 c)) : Rq 2).get i)).natAbs ^ 2) = _
  simp only [Fin.sum_univ_two, toRq_get, polyOfPair_get_zero, polyOfPair_get_one]
  rw [centeredRepr_intCast_eq_of_natAbs_le _ h1 (by norm_num [modulus]),
    centeredRepr_intCast_eq_of_natAbs_le _ h2 (by norm_num [modulus]),
    centeredRepr_intCast_eq_of_natAbs_le _ h3 (by norm_num [modulus]),
    centeredRepr_intCast_eq_of_natAbs_le _ h4 (by norm_num [modulus])]
  ring

/-- **The unperturbed round-off is accepted by the norm check.** -/
theorem toy_center_accepts (c : Rq 2) :
    (falconPSF toyP toyPrims).isShort (sOf c center) = true := by
  have hreal := s_normSq_le c
  have hint : s10 c ^ 2 + s11 c ^ 2 + s20 c ^ 2 + s21 c ^ 2 ≤ 12289 := by
    exact_mod_cast hreal
  have hnat : (s10 c).natAbs ^ 2 + (s11 c).natAbs ^ 2 + (s20 c).natAbs ^ 2 +
      (s21 c).natAbs ^ 2 ≤ modulus := by
    rw [modulus]
    zify
    simp only [sq_abs]
    exact hint
  simp only [falconPSF, decide_eq_true_iff, pairL2NormSq_center]
  exact hnat

/-! ## The ideal PSF: the attempt's accept-conditional -/

/-- The box points whose candidate passes the norm check. -/
def accepts (c : Rq 2) (δ : Box) : Prop := (falconPSF toyP toyPrims).isShort (sOf c δ) = true

noncomputable instance (c : Rq 2) : DecidablePred (accepts c) :=
  fun _ => inferInstanceAs (Decidable (_ = true))

instance (c : Rq 2) : Nonempty {δ : Box // accepts c δ} := ⟨⟨center, toy_center_accepts c⟩⟩

/-- Uniform over the accepting box points, mapped to their candidates: the attempt conditioned
on acceptance. -/
noncomputable def condSample (c : Rq 2) : ProbComp (Rq 2 × Rq 2) :=
  (fun δ : {δ : Box // accepts c δ} => sOf c δ.1) <$>
    (@uniformSample {δ : Box // accepts c δ} (SampleableType.ofFintype _))

/-- The ideal preimage-sampleable function: Falcon's `eval` and `isShort`, with the trapdoor
sampler the attempt's accept-conditional. -/
noncomputable def toyIdealPSF :
    PreimageSampleableFunction (PublicKey toyP) (SecretKey toyP) (Rq toyP.n × Rq toyP.n)
      (Rq toyP.n) where
  eval := (falconPSF toyP toyPrims).eval
  isShort := (falconPSF toyP toyPrims).isShort
  trapdoorSample := fun _ _ c => condSample c

/-- The honest key relation: the single key pair `(toyPk, toySk)`. -/
noncomputable def toyHr :
    GenerableRelation (PublicKey toyP) (SecretKey toyP) (validKeyPair toyP) where
  gen := pure (toyPk, toySk)
  gen_sound := fun pk sk h => by
    rw [support_pure, Set.mem_singleton_iff] at h
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact toy_validKeyPair

theorem toy_mem_gen {pk : PublicKey toyP} {sk : SecretKey toyP}
    (h : (pk, sk) ∈ support toyHr.gen) : pk = toyPk ∧ sk = toySk := by
  rw [show toyHr.gen = pure (toyPk, toySk) from rfl, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at h
  exact h

theorem mem_support_condSample {c : Rq 2} {x : Rq 2 × Rq 2} (hx : x ∈ support (condSample c)) :
    ∃ δ : Box, accepts c δ ∧ x = sOf c δ := by
  simp only [condSample, support_map, Set.mem_image] at hx
  obtain ⟨⟨δ, hδ⟩, -, rfl⟩ := hx
  exact ⟨δ, hδ, rfl⟩

/-- `hCorrect`: every draw of the ideal sampler is a short preimage of the target. -/
theorem toy_correctAt (pk : PublicKey toyP) (sk : SecretKey toyP)
    (hmem : (pk, sk) ∈ support toyHr.gen) : toyIdealPSF.CorrectAt pk sk := by
  obtain ⟨rfl, rfl⟩ := toy_mem_gen hmem
  intro t x hx
  obtain ⟨δ, hδ, rfl⟩ := mem_support_condSample hx
  exact ⟨toy_eval_sOf t δ, hδ⟩

/-- `hNeverFail`: the ideal sampler never fails. -/
theorem toy_neverFail (pk : PublicKey toyP) (sk : SecretKey toyP) (c : Rq toyP.n) :
    NeverFail (toyIdealPSF.trapdoorSample pk sk c) :=
  ⟨by simp [toyIdealPSF, condSample]⟩

/-- `hReg`: regularity, with the domain sampler the ideal sampler's own marginal. Every draw is a
preimage of its target (`toy_eval_sOf`), so pairing a draw with its image is pairing a uniform
target with a conditional draw. -/
theorem toy_hReg :
    ∃ domainSample : PublicKey toyP → ProbComp (Rq toyP.n × Rq toyP.n),
      ∀ pk sk, (pk, sk) ∈ support toyHr.gen →
        𝒮[(do let s ← domainSample pk; pure (toyIdealPSF.eval pk s, s)
              : ProbComp (Rq toyP.n × (Rq toyP.n × Rq toyP.n)))] =
        𝒮[(do let c ← ($ᵗ (Rq toyP.n)); let s ← toyIdealPSF.trapdoorSample pk sk c; pure (c, s)
              : ProbComp (Rq toyP.n × (Rq toyP.n × Rq toyP.n)))] := by
  refine ⟨fun _ => do let c ← ($ᵗ (Rq 2)); condSample c, fun pk sk hmem => ?_⟩
  obtain ⟨rfl, rfl⟩ := toy_mem_gen hmem
  simp only [bind_assoc]
  refine evalSPMF_bind_congr' _ fun c => ?_
  refine evalSPMF_bind_congr fun x hx => ?_
  obtain ⟨δ, -, rfl⟩ := mem_support_condSample hx
  rw [show toyIdealPSF.eval toyPk (sOf c δ) = c from toy_eval_sOf c δ]

/-! ## The attempt-level sampler package -/

/-- `hAttempt` at `ε_step = 0`: the idealized attempt is Falcon's attempt itself. -/
theorem toy_attemptTransport :
    attemptTransport toyP toyPrims toyHr (signAttempt toyP toyPrims) 0 :=
  attemptTransport_self_zero toyP toyPrims toyHr

/-- `hRes`: the attempt resamples to its accept-conditional, the ideal sampler. -/
theorem toy_idealAttemptResamples :
    idealAttemptResamples toyP toyHr (signAttempt toyP toyPrims) toyIdealPSF := by
  intro pk sk hmem c
  obtain ⟨rfl, rfl⟩ := toy_mem_gen hmem
  rw [toy_signAttempt]
  exact ProbComp.ResamplesTo.uniform_filter (accepts c) (sOf c)

/-- `hRej`: the attempt rejects with probability at most `80/81` at every target, since the
center of the box is always accepted. -/
theorem toy_attemptRejectBound :
    attemptRejectBound toyP toyHr (signAttempt toyP toyPrims) (80 / 81) := by
  intro pk sk hmem c
  obtain ⟨rfl, rfl⟩ := toy_mem_gen hmem
  rw [toy_signAttempt, probOutput_map]
  have hle : Pr[fun δ : Box =>
      (if (falconPSF toyP toyPrims).isShort (sOf c δ) then some (sOf c δ) else none) = none |
        $ᵗ Box] ≤ Pr[fun δ : Box => δ ≠ center | $ᵗ Box] := by
    refine probEvent_mono fun δ _ hδ => ?_
    rintro rfl
    simp [toy_center_accepts c] at hδ
  have hcard : (Finset.univ.filter fun δ : Box => δ ≠ center).card = 80 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp [Fintype.card_prod, Fintype.card_fin]
  have hBox : Fintype.card Box = 81 := by simp [Fintype.card_prod, Fintype.card_fin]
  rw [probEvent_uniformSample (p := fun δ : Box => δ ≠ center), hcard, hBox] at hle
  calc (Pr[fun δ : Box =>
        (if (falconPSF toyP toyPrims).isShort (sOf c δ) then some (sOf c δ) else none) = none |
          $ᵗ Box]).toReal
      ≤ (((80 : ℕ) : ℝ≥0∞) / ((81 : ℕ) : ℝ≥0∞)).toReal :=
        ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by simp)) hle
    _ = 80 / 81 := by
        rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]; norm_num

/-! ## The hypothesis bundle and its numbers -/

/-- **Joint witness for the attempt-level frontier.** Every sampler-side hypothesis of
`Falcon.euf_cma_security` holds simultaneously at this instance, at
`ε_step = 0` and `pRej = 80/81`, together with the GPV laws on the honest key. -/
theorem falcon_attempt_hyps_inhabited :
    (∀ pk x, toyIdealPSF.eval pk x = (falconPSF toyP toyPrims).eval pk x) ∧
    (∀ x, toyIdealPSF.isShort x = (falconPSF toyP toyPrims).isShort x) ∧
    (∀ pk sk, (pk, sk) ∈ support toyHr.gen → toyIdealPSF.CorrectAt pk sk) ∧
    (∀ pk sk, (pk, sk) ∈ support toyHr.gen →
      ∀ c, NeverFail (toyIdealPSF.trapdoorSample pk sk c)) ∧
    (∃ domainSample : PublicKey toyP → ProbComp (Rq toyP.n × Rq toyP.n),
      ∀ pk sk, (pk, sk) ∈ support toyHr.gen →
        𝒮[(do let s ← domainSample pk; pure (toyIdealPSF.eval pk s, s)
              : ProbComp (Rq toyP.n × (Rq toyP.n × Rq toyP.n)))] =
        𝒮[(do let c ← ($ᵗ (Rq toyP.n)); let s ← toyIdealPSF.trapdoorSample pk sk c; pure (c, s)
              : ProbComp (Rq toyP.n × (Rq toyP.n × Rq toyP.n)))]) ∧
    attemptTransport toyP toyPrims toyHr (signAttempt toyP toyPrims) 0 ∧
    attemptRejectBound toyP toyHr (signAttempt toyP toyPrims) (80 / 81) ∧
    idealAttemptResamples toyP toyHr (signAttempt toyP toyPrims) toyIdealPSF :=
  ⟨fun _ _ => rfl, fun _ => rfl, toy_correctAt, fun pk sk _ c => toy_neverFail pk sk c, toy_hReg,
    toy_attemptTransport, toy_attemptRejectBound, toy_idealAttemptResamples⟩

/-- **The attempt-level sampler loss at Falcon's signing budget.** With `ε_step = 0` and
`pRej = 80/81`, an attempt budget of `5265` keeps the loss
`qSign · (ε_step / (1 − pRej) + pRej ^ maxAttempts)` below `1/2` at `qSign = 2^64`. -/
theorem toy_samplerLoss_lt_half :
    (2 ^ 64 : ℝ) * ((0 : ℝ) / (1 - 80 / 81) + (80 / 81 : ℝ) ^ 5265) < 1 / 2 := by
  have h81 : (80 / 81 : ℝ) ^ 81 < 1 / 2 := by norm_num
  have hpow : (80 / 81 : ℝ) ^ 5265 = ((80 / 81 : ℝ) ^ 81) ^ 65 := by
    rw [← pow_mul]
  have hlt : ((80 / 81 : ℝ) ^ 81) ^ 65 < (1 / 2 : ℝ) ^ 65 :=
    pow_lt_pow_left₀ h81 (by positivity) (by norm_num)
  rw [zero_div, zero_add, hpow]
  calc (2 ^ 64 : ℝ) * ((80 / 81 : ℝ) ^ 81) ^ 65 < (2 ^ 64 : ℝ) * (1 / 2 : ℝ) ^ 65 := by
        gcongr
    _ = 1 / 2 := by norm_num

/-! ## The one-shot frontier fails at the same instance

At the zero target the sampler's box is centred at the origin, so the candidates are the lattice
points `z · B` for `z ∈ {−1, 0, 1}⁴`.  The rows of `B` have squared norm exactly `q`, so the norm
check `‖s‖² ≤ q` accepts precisely the origin and the eight unit moves: `9` of the `81` box
points.  The one-shot rejection probability at this target is therefore `8/9`, and the per-call
budget of any one-shot transport hypothesis is forced to at least `1/2`
(`Falcon.oneShot_samplerLoss_one_le_of_samplerTransport`): the one-shot loss `qSign · ε_step`
reaches one at every signing budget from two upward, whatever ideal sampler is chosen. -/

/-- Coefficients of zero in `R_q` at degree `2`. -/
theorem Rq_get_zero (i : Fin 2) : (0 : Rq 2).get i = 0 :=
  LatticeCrypto.NegacyclicRing.coeff_zero (coeffRing 2) i

/-- The target pair vanishes at the zero target. -/
theorem tgt_zero_coords : ta 0 = 0 ∧ tb 0 = 0 ∧ tc 0 = 0 ∧ td 0 = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := tgt_coords 0
  simp only [ta, tb, tc, td, h1, h2, h3, h4, Rq_get_zero, ZMod.val_zero, Nat.cast_zero, mul_zero,
    add_zero, sub_zero, neg_zero, zero_div, and_self]

/-- At the zero target the sampled coordinates are the box offsets themselves. -/
theorem zOf_zero (δ : Box) :
    zOf 0 δ = (polyOfPair (off δ.1) (off δ.2.1), polyOfPair (off δ.2.2.1) (off δ.2.2.2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := tgt_zero_coords
  simp only [ta, tb, tc, td] at h1 h2 h3 h4
  simp only [zOf, h1, h2, h3, h4, round_zero, zero_add]

/-- The candidate's coefficients at the zero target, as integer linear forms in the offsets. -/
def w10 (δ : Box) : ℤ := -(5 * off δ.1 - 2 * off δ.2.1 - 106 * off δ.2.2.1 + 32 * off δ.2.2.2)
def w11 (δ : Box) : ℤ := -(2 * off δ.1 + 5 * off δ.2.1 - 32 * off δ.2.2.1 - 106 * off δ.2.2.2)
def w20 (δ : Box) : ℤ := -(106 * off δ.1 + 32 * off δ.2.1 + 5 * off δ.2.2.1 + 2 * off δ.2.2.2)
def w21 (δ : Box) : ℤ := 32 * off δ.1 - 106 * off δ.2.1 + 2 * off δ.2.2.1 - 5 * off δ.2.2.2

/-- The candidate at the zero target, coefficient by coefficient. -/
theorem sOf_zero_eq (δ : Box) :
    sOf 0 δ = (IntPoly.toRq (polyOfPair (w10 δ) (w11 δ)),
      IntPoly.toRq (polyOfPair (w20 δ) (w21 δ))) := by
  rw [sOf_eq, zOf_zero]
  refine Prod.ext ?_ ?_
  · apply Poly.ext_get_eq
    intro i
    fin_cases i <;>
    · simp only [Rq_get_sub, Rq_get_zero, toRq_get, Poly.get_add, negacyclicMulPure_get,
        negacyclicConvCoeff, Fintype.sum_prod_type, Fin.sum_univ_two, keyG, keyCapG,
        polyOfPair_get_zero, polyOfPair_get_one, w10, w11]
      simp
      ring
  · apply Poly.ext_get_eq
    intro i
    fin_cases i <;>
    · simp only [Rq_get_neg, toRq_get, Poly.get_add, Poly.get_neg, negacyclicMulPure_get,
        negacyclicConvCoeff, Fintype.sum_prod_type, Fin.sum_univ_two, keyF, keyCapF,
        polyOfPair_get_zero, polyOfPair_get_one, w20, w21]
      simp
      ring

theorem off_bounds (d : Fin 3) : -1 ≤ off d ∧ off d ≤ 1 := by
  fin_cases d <;> simp [off]

/-- The candidate's coefficients at the zero target are at most `145` in absolute value. -/
theorem w_natAbs_le (δ : Box) :
    (w10 δ).natAbs ≤ 145 ∧ (w11 δ).natAbs ≤ 145 ∧ (w20 δ).natAbs ≤ 145 ∧
      (w21 δ).natAbs ≤ 145 := by
  obtain ⟨ha1, ha2⟩ := off_bounds δ.1
  obtain ⟨hb1, hb2⟩ := off_bounds δ.2.1
  obtain ⟨hc1, hc2⟩ := off_bounds δ.2.2.1
  obtain ⟨hd1, hd2⟩ := off_bounds δ.2.2.2
  simp only [w10, w11, w20, w21]
  omega

/-- The squared norm of the candidate at the zero target: its coefficients are small enough that
the centered representatives modulo `q` are the integers themselves. -/
theorem pairL2NormSq_sOf_zero (δ : Box) :
    pairL2NormSq (sOf 0 δ).1 (sOf 0 δ).2 =
      (w10 δ).natAbs ^ 2 + (w11 δ).natAbs ^ 2 + (w20 δ).natAbs ^ 2 + (w21 δ).natAbs ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := w_natAbs_le δ
  rw [sOf_zero_eq]
  change (∑ i : Fin 2, (LatticeCrypto.centeredRepr
      ((IntPoly.toRq (polyOfPair (w10 δ) (w11 δ)) : Rq 2).get i)).natAbs ^ 2) +
    (∑ i : Fin 2, (LatticeCrypto.centeredRepr
      ((IntPoly.toRq (polyOfPair (w20 δ) (w21 δ)) : Rq 2).get i)).natAbs ^ 2) = _
  simp only [Fin.sum_univ_two, toRq_get, polyOfPair_get_zero, polyOfPair_get_one]
  rw [centeredRepr_intCast_eq_of_natAbs_le _ h1 (by norm_num [modulus]),
    centeredRepr_intCast_eq_of_natAbs_le _ h2 (by norm_num [modulus]),
    centeredRepr_intCast_eq_of_natAbs_le _ h3 (by norm_num [modulus]),
    centeredRepr_intCast_eq_of_natAbs_le _ h4 (by norm_num [modulus])]
  ring

/-- **Acceptance at the zero target** is an integer inequality in the four linear forms. -/
theorem accepts_zero_iff (δ : Box) :
    accepts 0 δ ↔ w10 δ ^ 2 + w11 δ ^ 2 + w20 δ ^ 2 + w21 δ ^ 2 ≤ 12289 := by
  simp only [accepts, falconPSF, decide_eq_true_iff, pairL2NormSq_sOf_zero]
  constructor
  · intro h
    have h' : (w10 δ).natAbs ^ 2 + (w11 δ).natAbs ^ 2 + (w20 δ).natAbs ^ 2 +
        (w21 δ).natAbs ^ 2 ≤ 12289 := h
    zify at h'
    simpa only [sq_abs] using h'
  · intro h
    change (w10 δ).natAbs ^ 2 + (w11 δ).natAbs ^ 2 + (w20 δ).natAbs ^ 2 +
        (w21 δ).natAbs ^ 2 ≤ 12289
    zify
    simpa only [sq_abs] using h

/-- **Exactly nine box points are accepted at the zero target**: the origin and the eight unit
moves, each of squared norm exactly `q`. -/
theorem card_accepts_zero : (Finset.univ.filter (accepts 0)).card = 9 := by
  rw [Finset.filter_congr fun δ _ => accepts_zero_iff δ]
  decide

theorem toy_mem_gen_self : (toyPk, toySk) ∈ support toyHr.gen := by
  rw [show toyHr.gen = pure (toyPk, toySk) from rfl, support_pure]
  rfl

/-- **The one-shot acceptance probability at the zero target is `1/9`.** -/
theorem toy_oneShot_accept_zero :
    (Pr[fun x => (falconPSF toyP toyPrims).isShort x = true |
      (falconPSF toyP toyPrims).trapdoorSample toyPk toySk 0]).toReal = 1 / 9 := by
  rw [toy_trapdoorSample, probEvent_map]
  have hBox : Fintype.card Box = 81 := by simp [Fintype.card_prod, Fintype.card_fin]
  change (Pr[accepts 0 | $ᵗ Box]).toReal = 1 / 9
  rw [probEvent_uniformSample, card_accepts_zero, hBox, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  norm_num

/-- **The one-shot frontier is vacuous at this instance.** Every ideal sampler admissible for the
one-shot transport hypotheses at the honest key has its per-call budget forced to at least
`1/2`: the norm check rejects `8/9` of the draws at the zero target, so the one-shot loss
`qSign · ε_step` of `Falcon.oneShot_samplerLoss_one_le_of_samplerTransport` already reaches
one at a signing budget of two. -/
theorem toy_oneShot_epsStep_ge_half
    (idealPSF : PreimageSampleableFunction (PublicKey toyP) (SecretKey toyP)
      (Rq toyP.n × Rq toyP.n) (Rq toyP.n))
    (ε_step : ℝ)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF toyP toyPrims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support toyHr.gen → idealPSF.CorrectAt pk sk)
    (hNeverFail : ∀ pk sk, (pk, sk) ∈ support toyHr.gen →
      ∀ c, NeverFail (idealPSF.trapdoorSample pk sk c))
    (hStep : samplerTransport toyP toyPrims toyHr idealPSF ε_step) :
    (1 / 2 : ℝ) ≤ ε_step := by
  have h := oneShot_samplerLoss_one_le_of_samplerTransport toyP toyPrims toyHr idealPSF 2 ε_step
    hShort hCorrect hNeverFail hStep toyPk toySk toy_mem_gen_self 0
    (by rw [toy_oneShot_accept_zero]; norm_num)
  norm_num at h
  linarith

/-- The one-shot loss term reaches one at every signing budget from two upward, while the
attempt-level term stays below `1/2` at `2^64` (`toy_samplerLoss_lt_half`). -/
theorem toy_oneShot_samplerLoss_one_le
    (idealPSF : PreimageSampleableFunction (PublicKey toyP) (SecretKey toyP)
      (Rq toyP.n × Rq toyP.n) (Rq toyP.n))
    (ε_step : ℝ)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF toyP toyPrims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support toyHr.gen → idealPSF.CorrectAt pk sk)
    (hNeverFail : ∀ pk sk, (pk, sk) ∈ support toyHr.gen →
      ∀ c, NeverFail (idealPSF.trapdoorSample pk sk c))
    (hStep : samplerTransport toyP toyPrims toyHr idealPSF ε_step)
    (qSign : ℕ) (hq : 2 ≤ qSign) :
    (1 : ℝ) ≤ (qSign : ℝ) * ε_step := by
  have h := toy_oneShot_epsStep_ge_half idealPSF ε_step hShort hCorrect hNeverFail hStep
  have hq' : (2 : ℝ) ≤ qSign := by exact_mod_cast hq
  nlinarith

/-! ## The headline at the instance -/

/-- **The attempt-level headline, instantiated.** For every query-bounded forger against the
rejection-loop signer at this key, the split bound of `Falcon.euf_cma_security` holds with the
sampler loss `qSign · (80/81) ^ maxAttempts`: every sampler-side hypothesis is discharged by the
witnesses above, and nothing is assumed beyond the forger's query bound. -/
theorem toy_euf_cma_security
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] [Nonempty Salt]
    (qSign qHash maxAttempts : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (falconRetrySignatureAlg toyP toyPrims Salt maxAttempts toyHr))
    (hQ : ∀ pk, GPVHashAndSign.signHashQueryBound
      (M := List Byte) (Salt := Salt) (Range := Rq toyP.n)
      (S' := Salt × (Rq toyP.n × Rq toyP.n))
      (α := List Byte × (Salt × (Rq toyP.n × Rq toyP.n))) (oa := adv.main pk)
      (qSign := qSign) (qHash := qHash)) :
    ∃ (collisionReduction : SIS.Adversary (ntruPSFCollisionProblem toyP toyPrims toyHr))
      (exactMatchReduction : GPVHashAndSign.ProgrammedPreimageAdversary
        (PK := PublicKey toyP) (Domain := Rq toyP.n × Rq toyP.n) (Range := Rq toyP.n)),
      adv.advantage (GPVHashAndSign.runtime (Range := Rq toyP.n) (List Byte) Salt) ≤
        SIS.advantage (ntruPSFCollisionProblem toyP toyPrims toyHr) collisionReduction +
        ((qSign + (qHash + 1) : ℕ) : ENNReal) *
          GPVHashAndSign.programmedPreimageAdvantage toyIdealPSF toyHr exactMatchReduction +
        GPVHashAndSign.collisionBound Salt qSign (qHash + 1) +
        ENNReal.ofReal (qSign * (80 / 81 : ℝ) ^ maxAttempts) := by
  have h := euf_cma_security toyP toyPrims Salt toyHr qSign qHash maxAttempts 0 (80 / 81)
    le_rfl (by norm_num) (by norm_num) adv (signAttempt toyP toyPrims) toyIdealPSF
    (fun _ _ => rfl) (fun _ => rfl) toy_correctAt toy_hReg (fun pk sk _ c => toy_neverFail pk sk c)
    toy_attemptTransport toy_attemptRejectBound toy_idealAttemptResamples hQ
  simpa only [zero_div, zero_add] using h

end Falcon.NonVacuity
