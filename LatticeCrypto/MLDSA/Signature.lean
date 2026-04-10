/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Scheme
import LatticeCrypto.MLDSA.Encoding

/-!
# ML-DSA FIPS 204 Signature Algorithms

This file implements the faithful FIPS 204 signature algorithms:

- `fipsKeyGen` — Algorithm 1 / 6 (key generation with random seed sampling)
- `fipsSign` — Algorithm 2 / 7 (signing with message-dependent hashing and retry loop)
- `fipsVerify` — Algorithm 3 / 8 (verification with direct RO consistency check)

Unlike the IDS-core in `Scheme.lean`, this layer:

- Uses the FIPS signature format `(c̃, z, h)` instead of `(w₁, z, h)`
- Derives `μ = H(tr ‖ M')` from the actual message
- Derives `ρ'' = H(K ‖ rnd ‖ μ)` from the private seed, randomness, and message
- Uses `ExpandMask(ρ'', κ)` with counter `κ` incrementing by `l` each retry
- Checks RO consistency `c̃ = H(μ ‖ w1Encode(w₁'))` directly in verification

## References

- NIST FIPS 204, Algorithms 1–3 (outer API) and 6–8 (internal algorithms)
-/


open OracleComp OracleSpec

namespace MLDSA

variable (p : Params) (prims : Primitives p) (nttOps : NTTRingOps)

/-- The FIPS 204 signature format: `(c̃, z, h)`. -/
structure FIPSSignature where
  cTilde : CommitHashBytes p
  z : RqVec p.l
  h : Vector prims.Hint p.k

/-! ### Key Generation -/

/-- ML-DSA.KeyGen (Algorithm 1 / Algorithm 6): sample a random seed and generate keys. -/
def fipsKeyGen : ProbComp (PublicKey p prims × SecretKey p) := do
  let seed ← $ᵗ (Bytes 32)
  return keyGenFromSeed p prims nttOps seed

/-! ### Signing -/

/-- A single signing attempt at counter value `κ` (Algorithm 7, lines 5–30).

Deterministic given all its inputs; randomness enters through `ρ''` which was
derived from a random `rnd` by the caller. -/
def fipsSignAttempt
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (rhoDoublePrime : Bytes 64) (kappa : ℕ) :
    Option (FIPSSignature p prims) :=
  let y := prims.expandMask rhoDoublePrime kappa
  let w := nttOps.coeffMatVecMul aHat y
  let w1 := prims.highBitsVec w
  let cTilde := prims.hashCommitment mu (prims.w1Encode w1)
  let c := prims.sampleInBall cTilde
  let cs1 := nttOps.coeffScalarVecMul c sk.s1
  let cs2 := nttOps.coeffScalarVecMul c sk.s2
  let z := y + cs1
  let r0 := prims.lowBitsVec (w - cs2)
  if polyVecNorm z < p.gamma1 - p.beta ∧ polyVecNorm r0 < p.gamma2 - p.beta then
    let ct0 := nttOps.coeffScalarVecMul c sk.t0
    let h := prims.makeHintVec (-ct0) (w - cs2 + ct0)
    if polyVecNorm ct0 < p.gamma2 ∧ prims.hintWeight h ≤ p.omega then
      some ⟨cTilde, z, h⟩
    else
      none
  else
    none

/-- The deterministic signing loop: try counter values `κ = 0, l, 2l, ...`
up to `maxAttempts` iterations (Algorithm 7, lines 4–31). -/
def fipsSignLoop
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ) :
    Option (FIPSSignature p prims) :=
  (List.range maxAttempts).findSome? fun i =>
    fipsSignAttempt p prims nttOps sk aHat mu rhoDoublePrime (i * p.l)

/-- ML-DSA.Sign (Algorithm 2 / Algorithm 7): sign a message.

1. Compute `μ = H(tr ‖ M')`
2. Sample `rnd` and compute `ρ'' = H(K ‖ rnd ‖ μ)`
3. Expand `Â = ExpandA(ρ)`
4. Try signing attempts with incrementing `κ`

Returns `none` if all `maxAttempts` attempts abort. In a correct implementation with
typical parameters, the probability of exhausting all attempts is negligible. -/
def fipsSign (pk : PublicKey p prims) (sk : SecretKey p)
    (msg : List Byte) (maxAttempts : ℕ) :
    ProbComp (Option (FIPSSignature p prims)) := do
  let mu := prims.hashMessage sk.tr msg
  let rnd ← $ᵗ (Bytes 32)
  let rhoDoublePrime := prims.hashPrivateSeed sk.key rnd mu
  let aHat := prims.expandA pk.rho
  return fipsSignLoop p prims nttOps sk aHat mu rhoDoublePrime maxAttempts

/-! ### Verification -/

/-- ML-DSA.Verify (Algorithm 3 / Algorithm 8): verify a signature.

1. Expand `Â = ExpandA(ρ)` from the public key
2. Compute `tr = H(pk)`, `μ = H(tr ‖ M')`
3. Derive `c = SampleInBall(c̃)` and compute `w'_Approx = Az - c·(t₁·2^d)`
4. Apply hint: `w₁' = UseHint(h, w'_Approx)`
5. Recompute `c̃' = H(μ ‖ w1Encode(w₁'))`
6. Accept iff `‖z‖∞ < γ₁ - β`, `c̃' = c̃`, and `hintWeight(h) ≤ ω` -/
def fipsVerify (pk : PublicKey p prims) (msg : List Byte)
    (sig : FIPSSignature p prims) : Bool :=
  let aHat := prims.expandA pk.rho
  let tr := prims.hashPublicKey pk.rho pk.t1
  let mu := prims.hashMessage tr msg
  let c := prims.sampleInBall sig.cTilde
  let wApprox := computeWApprox p prims nttOps aHat c sig.z pk.t1
  let w1' := prims.useHintVec sig.h wApprox
  let cTildeRecomputed := prims.hashCommitment mu (prims.w1Encode w1')
  decide (polyVecNorm sig.z < p.gamma1 - p.beta) &&
  decide (cTildeRecomputed = sig.cTilde) &&
  decide (prims.hintWeight sig.h ≤ p.omega)

/-! ### Vector Arithmetic Helpers -/

private lemma rqvec_add_get {k : ℕ} (v u : RqVec k) (j : Fin k) :
    (v + u).get j = v.get j + u.get j :=
  congr_fun (Vector.vectorAdd_get v u) j

private lemma rq_sub_add_cancel (a b : Rq) : a - b + b = a := by
  apply Vector.ext; intro i hi
  change ((coeffRing.add (coeffRing.sub a b) b) : Rq).get ⟨i, hi⟩ = a.get ⟨i, hi⟩
  simp [sub_add_cancel]

private lemma rq_add_neg_cancel (a b : Rq) : a + b + (-b) = a := by
  apply Vector.ext; intro i hi
  change ((coeffRing.add (coeffRing.add a b) (coeffRing.neg b)) : Rq).get ⟨i, hi⟩ = a.get ⟨i, hi⟩
  simp [add_neg_cancel_right]

private lemma neg_rq_get (f : Rq) (i : Fin ringDegree) : (-f).get i = -(f.get i) := by
  change (coeffRing.neg f).get i = _
  simp [LatticeCrypto.vectorNegacyclicRing, Vector.get_ofFn]

private lemma polyNorm_neg (f : Rq) : polyNorm (-f) = polyNorm f := by
  unfold polyNorm normOps
  simp only [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView]
  unfold LatticeCrypto.cInfNormOf
  apply Finset.sup_congr rfl
  intro i _
  simp only [LatticeCrypto.zmodCenteredCoeffView, polyBackend,
    LatticeCrypto.vectorNegacyclicRing, LatticeCrypto.vectorBackend]
  rw [neg_rq_get]
  exact LatticeCrypto.centeredRepr_natAbs_neg _

/-! ### Correctness -/

private lemma fipsSignLoop_exists
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ)
    (sig : FIPSSignature p prims)
    (h : fipsSignLoop p prims nttOps sk aHat mu rhoDoublePrime maxAttempts = some sig) :
    ∃ i ∈ List.range maxAttempts,
      fipsSignAttempt p prims nttOps sk aHat mu rhoDoublePrime (i * p.l) = some sig :=
  List.exists_of_findSome?_eq_some h

private lemma fipsSignAttempt_spec
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (rhoDoublePrime : Bytes 64) (kappa : ℕ)
    (sig : FIPSSignature p prims)
    (h : fipsSignAttempt p prims nttOps sk aHat mu rhoDoublePrime kappa = some sig) :
    let y := prims.expandMask rhoDoublePrime kappa
    let w := nttOps.coeffMatVecMul aHat y
    let w1 := prims.highBitsVec w
    let c := prims.sampleInBall (prims.hashCommitment mu (prims.w1Encode w1))
    let cs2 := nttOps.coeffScalarVecMul c sk.s2
    let z := y + nttOps.coeffScalarVecMul c sk.s1
    let ct0 := nttOps.coeffScalarVecMul c sk.t0
    sig.cTilde = prims.hashCommitment mu (prims.w1Encode w1) ∧
    sig.z = z ∧
    sig.h = prims.makeHintVec (-ct0) (w - cs2 + ct0) ∧
    polyVecNorm z < p.gamma1 - p.beta ∧
    polyVecNorm (prims.lowBitsVec (w - cs2)) < p.gamma2 - p.beta ∧
    polyVecNorm ct0 < p.gamma2 ∧
    prims.hintWeight sig.h ≤ p.omega := by
  sorry

/-- Single-component recovery: `UseHint(MakeHint(-ct₀, r + ct₀), r + ct₀) = HighBits(r + s)`
when `‖ct₀‖ ≤ γ₂`, `‖LowBits(r)‖ < γ₂ - β`, and `‖s‖ ≤ β`, and `r + s = w`.

Proof strategy:
1. `useHint_makeHint` with `z = -ct₀`: need `polyNorm (-ct₀) ≤ γ₂`, from `cInfNorm_neg`.
2. Result: `highBits((r + ct₀) + (-ct₀)) = highBits(r)` — need `r + ct₀ + (-ct₀) = r`.
3. `hide_low` with perturbation `s`: `highBits(r + s) = highBits(r)` when
   `polyNorm s ≤ β` and `polyNorm(lowBits(r)) + β < γ₂`. -/
lemma useHint_makeHint_eq_highBits
    (h_useHint_makeHint : ∀ z r : Rq,
      polyNorm z ≤ p.gamma2 →
      prims.useHint (prims.makeHint z r) r = prims.highBits (r + z))
    (h_hide_low : ∀ (r s : Rq) (b : ℕ),
      polyNorm s ≤ b →
      polyNorm (prims.lowBits r) + b < p.gamma2 →
      prims.highBits (r + s) = prims.highBits r)
    (w_j r_j ct0_j s_j : Rq)
    (h_r_eq : r_j = w_j - s_j)
    (h_norm_ct0 : polyNorm ct0_j ≤ p.gamma2)
    (h_norm_r0 : polyNorm (prims.lowBits r_j) < p.gamma2 - p.beta)
    (h_s_bound : polyNorm s_j ≤ p.beta) :
    prims.useHint (prims.makeHint (-ct0_j) (r_j + ct0_j)) (r_j + ct0_j) =
      prims.highBits w_j := by
  have h_neg_norm : polyNorm (-ct0_j) ≤ p.gamma2 := by
    rw [polyNorm_neg]; exact h_norm_ct0
  rw [h_useHint_makeHint (-ct0_j) (r_j + ct0_j) h_neg_norm]
  rw [rq_add_neg_cancel r_j ct0_j]
  have h2 : polyNorm (prims.lowBits r_j) + p.beta < p.gamma2 := by omega
  rw [← h_hide_low r_j s_j p.beta h_s_bound h2]
  rw [h_r_eq, rq_sub_add_cancel w_j s_j]

/-- When all signing norm bounds hold, UseHint recovers the original commitment:
`UseHintVec(MakeHintVec(-ct₀, w - cs₂ + ct₀), w - cs₂ + ct₀) = HighBitsVec(w)`.

Follows componentwise from `useHint_makeHint_eq_highBits`. -/
lemma useHintVec_makeHintVec_eq_highBitsVec
    (h_useHint_makeHint : ∀ z r : Rq,
      polyNorm z ≤ p.gamma2 →
      prims.useHint (prims.makeHint z r) r = prims.highBits (r + z))
    (h_hide_low : ∀ (r s : Rq) (b : ℕ),
      polyNorm s ≤ b →
      polyNorm (prims.lowBits r) + b < p.gamma2 →
      prims.highBits (r + s) = prims.highBits r)
    (w cs2 ct0 : RqVec p.k)
    (h_norm_ct0 : polyVecNorm ct0 < p.gamma2)
    (h_norm_r0 : polyVecNorm (prims.lowBitsVec (w - cs2)) < p.gamma2 - p.beta)
    (h_cs2_bound : ∀ (j : Fin p.k),
      LatticeCrypto.cInfNorm (cs2.get j) ≤ p.beta) :
    prims.useHintVec (prims.makeHintVec (-ct0) (w - cs2 + ct0))
      (w - cs2 + ct0) = prims.highBitsVec w := by
  apply Vector.ext
  intro j hj
  unfold Primitives.useHintVec Primitives.makeHintVec Primitives.highBitsVec
  simp only [Vector.getElem_zipWith, Vector.getElem_neg, Vector.getElem_map]
  let jj : Fin p.k := ⟨j, hj⟩
  let w_j := w.get jj
  let r_j := (w - cs2).get jj
  let ct0_j := ct0.get jj
  let s_j := cs2.get jj
  have h_ct0_lt : polyNorm ct0_j < p.gamma2 := by
      exact lt_of_le_of_lt
        (LatticeCrypto.PolyVec.component_cInfNorm_le normOps ct0 jj)
        h_norm_ct0
  have h_r0_lt : polyNorm ((prims.lowBitsVec (w - cs2)).get jj) < p.gamma2 - p.beta := by
      exact lt_of_le_of_lt
        (LatticeCrypto.PolyVec.component_cInfNorm_le normOps (prims.lowBitsVec (w - cs2)) jj)
        h_norm_r0
  have h_hint : -ct0[j] = -ct0_j := by
    change -(ct0.get jj) = -ct0_j
    simp only [ct0_j]
  have h_arg : (w - cs2 + ct0)[j] = r_j + ct0_j := by
    change (w - cs2 + ct0).get jj = r_j + ct0_j
    simp only [Vector.vectorAdd_get, Pi.add_apply, r_j, ct0_j]
  have h_w : w[j] = w_j := by
    change w.get jj = w_j
    simp only [w_j]
  rw [h_hint, h_arg, h_w]
  refine useHint_makeHint_eq_highBits (p := p) (prims := prims)
    h_useHint_makeHint h_hide_low
    w_j r_j ct0_j s_j
    ?_ ?_ ?_ ?_
  · change (w - cs2).get jj = w.get jj - cs2.get jj
    simp only [Vector.get_eq_getElem, Vector.getElem_sub]
  · exact Nat.le_of_lt h_ct0_lt
  · simpa [Primitives.lowBitsVec, r_j] using h_r0_lt
  · unfold polyNorm normOps
    simpa [s_j, LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView,
      LatticeCrypto.cInfNorm] using h_cs2_bound jj

/-- Correctness of FIPS ML-DSA, conditional on the algebraic key identity (`h_wApprox_eq`)
and the product norm bound (`h_cs2_bound`). These conditions follow from the key generation
relationship `t = A·s₁ + s₂`, `(t₁,t₀) = Power2Round(t)`, and the weight/norm structure
of challenge polynomials and secret keys. -/
theorem fipsSign_fipsVerify_correct'
    (pk : PublicKey p prims) (sk : SecretKey p)
    (msg : List Byte) (sig : FIPSSignature p prims)
    (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ)
    (h_valid : validKeyPair p prims pk sk = true)
    (h_useHint_makeHint : ∀ z r : Rq,
      polyNorm z ≤ p.gamma2 →
      prims.useHint (prims.makeHint z r) r = prims.highBits (r + z))
    (h_hide_low : ∀ (r s : Rq) (b : ℕ),
      polyNorm s ≤ b →
      polyNorm (prims.lowBits r) + b < p.gamma2 →
      prims.highBits (r + s) = prims.highBits r)
    (h_wApprox_eq : ∀ (c : Rq) (y : RqVec p.l),
      computeWApprox p prims nttOps (prims.expandA pk.rho) c
        (y + nttOps.coeffScalarVecMul c sk.s1) pk.t1 =
      nttOps.coeffMatVecMul (prims.expandA pk.rho) y - nttOps.coeffScalarVecMul c sk.s2 +
        nttOps.coeffScalarVecMul c sk.t0)
    (h_cs2_bound : ∀ (c : Rq) (j : Fin p.k),
      LatticeCrypto.cInfNorm ((nttOps.coeffScalarVecMul c sk.s2).get j) ≤ p.beta)
    (h_sign : fipsSignLoop p prims nttOps sk
      (prims.expandA pk.rho) (prims.hashMessage sk.tr msg)
      rhoDoublePrime maxAttempts = some sig) :
    fipsVerify p prims nttOps pk msg sig = true := by
  sorry

/-- Correctness of FIPS ML-DSA: if a key pair was generated honestly and signing succeeds,
then verification accepts the resulting signature.

The proof requires deriving the algebraic key identity and product norm bounds from
`validKeyPair` and `Primitives.Laws`; see `fipsSign_fipsVerify_correct'` for the
conditional version. -/
theorem fipsSign_fipsVerify_correct
    (pk : PublicKey p prims) (sk : SecretKey p)
    (msg : List Byte) (sig : FIPSSignature p prims)
    (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ)
    (h_valid : validKeyPair p prims pk sk = true)
    (h_laws : Primitives.Laws prims nttOps)
    (h_sign : fipsSignLoop p prims nttOps sk
      (prims.expandA pk.rho) (prims.hashMessage sk.tr msg)
      rhoDoublePrime maxAttempts = some sig) :
    fipsVerify p prims nttOps pk msg sig = true := by
  sorry

end MLDSA
