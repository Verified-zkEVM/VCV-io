/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Primitives
import VCVio.CryptoFoundations.IdenSchemeWithAbort
import VCVio.OracleComp.Constructions.SampleableType

/-!
# ML-DSA Identification Scheme Core

This file defines the core ML-DSA identification scheme with aborts, following the
proof-level abstraction used in the EasyCrypt formalization (formosa-crypto/dilithium).
The concrete FIPS 204 signing algorithm (with message-dependent hashing and retry counters)
is built on top of this in `LatticeCrypto.MLDSA.Signature`.

## Architecture

The `IdenSchemeWithAbort` type parameters instantiate as follows for ML-DSA:

| IdenSchemeWithAbort | ML-DSA meaning |
|---|---|
| `Stmt` (statement) | `PublicKey` — `(ρ, t₁)` |
| `Wit` (witness) | `SecretKey` — `(ρ, K, tr, s₁, s₂, t₀)` |
| `Commit` (commitment) | `Vector prims.High p.k` — `w₁ = HighBits(Ay)` |
| `PrvState` (state) | `SigningState` — `(y, w)` retained for the respond phase |
| `Chal` (challenge) | `CommitHashBytes p` — the `λ/4`-byte hash `c̃` |
| `Resp` (response) | `RqVec p.l × Vector prims.Hint p.k` — `(z, h)` |

## Separation from FIPS 204

This file models the **proof-level IDS** used in the Fiat-Shamir-with-aborts security argument:

- **Commit** samples `y` uniformly at random, rather than deriving it from message-dependent
  seeds via `ExpandMask(ρ'', κ)`.
- **No message hashing**: the IDS operates without messages; the message enters only through
  the Fiat-Shamir transform.
- **No retry counter**: the IDS commit is a single probabilistic step; retry logic with
  incrementing `κ` is handled by the signing layer.

## References

- EasyCrypt `IDSabort.ec`, `SimplifiedScheme.ec` (formosa-crypto/dilithium)
- NIST FIPS 204, Algorithms 7 and 8 (for the underlying arithmetic)
-/


open OracleComp OracleSpec
open LatticeCrypto TransformOps

namespace MLDSA

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]

/-- The semantic public key: the public seed `ρ` and the power-2 rounded key vector `t₁`. -/
structure PublicKey where
  rho : Bytes 32
  t1 : Vector prims.Power2High p.k

/-- The semantic secret key: includes the expanded public key material for efficient signing. -/
structure SecretKey where
  rho : Bytes 32
  key : Bytes 32
  tr : Bytes 64
  s1 : RqVec p.l
  s2 : RqVec p.k
  t0 : RqVec p.k

/-- The signing state: commitment data retained between commit and respond phases. -/
structure SigningState where
  y : RqVec p.l
  w : RqVec p.k

/-- The public commitment: `w₁ = HighBits(w)`. -/
abbrev Commitment := Vector prims.High p.k

/-- The signature response: the short vector `z` paired with the hint `h`. -/
abbrev Response := RqVec p.l × Vector prims.Hint p.k

/-- Compute `w'_Approx = NTT⁻¹(Â · NTT(z) - NTT(c) · NTT(t₁ · 2^d))` (Algorithm 8, line 9). -/
def computeWApprox (aHat : TqMatrix p.k p.l) (c : ChallengePoly) (z : RqVec p.l)
    (t1 : Vector prims.Power2High p.k) : RqVec p.k :=
  let cHat := nttOps.toHat c
  let zHat := nttOps.hatVec z
  let t1Shifted := prims.power2RoundShiftVec t1
  let t1ShiftedHat := nttOps.hatVec t1Shifted
  let azHat := nttOps.matVecMul aHat zHat
  let ct1Hat := nttOps.scalarVecMul cHat t1ShiftedHat
  nttOps.unhatVec (azHat - ct1Hat)

/-! ### Key Generation -/

/-- ML-DSA key generation (Algorithm 6), modeled as a deterministic function from seed.

Given a 32-byte seed `ξ`:
1. Expand to `(ρ, ρ', K)` via `H(ξ ‖ k ‖ l, 128)`
2. Generate matrix `Â = ExpandA(ρ)`
3. Generate secret vectors `(s₁, s₂) = ExpandS(ρ')`
4. Compute `t = A·s₁ + s₂`
5. Split `t` into `(t₁, t₀)` via `Power2Round`
6. Compute `tr = H(pkEncode(ρ, t₁), 64)` -/
def keyGenFromSeed (seed : Bytes 32) : PublicKey p prims × SecretKey p :=
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let aHat := prims.expandA rho
  let (s1, s2) := prims.expandS rhoPrime
  let t := aHat * s1 + s2
  let (t1, t0) := prims.power2RoundVec t
  let pk : PublicKey p prims := ⟨rho, t1⟩
  let tr := prims.hashPublicKey rho t1
  let sk : SecretKey p := ⟨rho, key, tr, s1, s2, t0⟩
  (pk, sk)

open Classical in
/-- A key pair is valid when it is honestly generated: there is a seed `ξ` such that
`keyGenFromSeed ξ = (pk, sk)`. This captures the full key-generation relationship
(`t = A·s₁ + s₂`, `(t₁, t₀) = Power2Round(t)`, `s₁, s₂` bounded by `η`), which is what the
completeness and signing-correctness proofs require. The predicate is decidable because the
seed space `Bytes 32` is finite. -/
noncomputable def validKeyPair (pk : PublicKey p prims) (sk : SecretKey p) : Bool :=
  decide (∃ seed : Bytes 32, keyGenFromSeed p prims seed = (pk, sk))

@[simp] theorem validKeyPair_eq_true_iff (pk : PublicKey p prims) (sk : SecretKey p) :
    validKeyPair p prims pk sk = true ↔
      ∃ seed : Bytes 32, keyGenFromSeed p prims seed = (pk, sk) := by
  simp [validKeyPair]

/-! ### Identification Scheme -/

/-- The core identification scheme with aborts for ML-DSA.

- **Commit**: sample `y` uniformly, compute `w = NTT⁻¹(Â · NTT(y))`,
  return `(w₁ = HighBits(w), state = (y, w))`.
- **Respond** (Alg 7, lines 16–30): derive `c = SampleInBall(c̃)`, compute
  `z = y + c·s₁`, check `‖z‖∞ < γ₁ - β` and `‖LowBits(w - c·s₂)‖∞ < γ₂ - β`,
  compute hint `h = MakeHint(-c·t₀, w - c·s₂ + c·t₀)`, check `‖c·t₀‖∞ < γ₂`
  and hint weight `≤ ω`. Return `some (z, h)` on success, `none` on abort.
- **Verify** (Alg 8, lines 8–13): check `‖z‖∞ < γ₁ - β`, reconstruct
  `w'_Approx = Az - c·(t₁·2^d)`, verify `UseHint(h, w'_Approx) = w₁` and
  hint weight `≤ ω`. -/
def identificationScheme
    [DecidableEq prims.High] [SampleableType (RqVec p.l)] :
    IdenSchemeWithAbort
      (PublicKey p prims) (SecretKey p)
      (Commitment p prims) (SigningState p)
      (CommitHashBytes p) (Response p prims)
      (validKeyPair p prims) where
  commit := fun pk _sk => do
    let aHat := prims.expandA pk.rho
    let y ← $ᵗ (RqVec p.l)
    let w := aHat * y
    let w1 := prims.highBitsVec w
    return (w1, ⟨y, w⟩)
  respond := fun _pk sk st cTilde => do
    let c := prims.sampleInBall cTilde
    let cs1 := c • sk.s1
    let cs2 := c • sk.s2
    let z := st.y + cs1
    let r0 := prims.lowBitsVec (st.w - cs2)
    if polyVecNorm z < p.gamma1 - p.beta ∧ polyVecNorm r0 < p.gamma2 - p.beta then do
      let ct0 := c • sk.t0
      let h := prims.makeHintVec (-ct0) (st.w - cs2 + ct0)
      if polyVecNorm ct0 < p.gamma2 ∧ prims.hintWeight h ≤ p.omega then
        return some (z, h)
      else
        return none
    else
      return none
  verify := fun pk w1 cTilde (z, h) =>
    let c := prims.sampleInBall cTilde
    let aHat := prims.expandA pk.rho
    let wApprox := computeWApprox p prims aHat c z pk.t1
    let w1' := prims.useHintVec h wApprox
    decide (polyVecNorm z < p.gamma1 - p.beta) &&
    decide (w1' = w1) &&
    decide (prims.hintWeight h ≤ p.omega)

/-! ### Key Generation Algebraic Properties -/

/-- Keys generated by `keyGenFromSeed` satisfy `validKeyPair`. -/
theorem keyGenFromSeed_validKeyPair (seed : Bytes 32) :
    let (pk, sk) := keyGenFromSeed p prims seed
    validKeyPair p prims pk sk = true := by
  simp only [validKeyPair_eq_true_iff]
  exact ⟨seed, rfl⟩

/-- The key generation algebraic identity: `A·z - c·(t₁·2^d) = A·y - c·s₂ + c·t₀`
when `z = y + c·s₁` and the key pair comes from `keyGenFromSeed`.

This is the core identity underlying both signing correctness and the security proof.
It follows from `t = A·s₁ + s₂` (key generation), `t₁·2^d + t₀ = t` (Power2Round),
and NTT linearity. -/
theorem keyGenFromSeed_wApprox_eq {pk : PublicKey p prims} {sk : SecretKey p}
    (h_laws : Primitives.Laws prims nttOps)
    (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) :
    ∀ (c : Rq) (y : RqVec p.l),
      computeWApprox p prims (prims.expandA pk.rho) c (y + c • sk.s1) pk.t1 =
      (prims.expandA pk.rho) * y - c • sk.s2 + c • sk.t0 := by
  intro c y
  haveI := h_laws.transform
  let laws := h_laws.transform
  set aHat := prims.expandA pk.rho
  simp only [computeWApprox]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_add, Vector.getElem_sub,
    nttOps.hatVec_add, nttOps.unhatVec_sub, nttOps.matVecMul_add, nttOps.unhatVec_add]
  have h_kg : prims.power2RoundShiftVec pk.t1 + sk.t0 = aHat * sk.s1 + sk.s2 := by
    simp only [keyGenFromSeed, Prod.mk.injEq] at hkeygen
    obtain ⟨hpk, hsk⟩ := hkeygen
    have hrho  := congr_arg PublicKey.rho hpk.symm
    have hs1   := congr_arg SecretKey.s1 hsk.symm
    have hs2   := congr_arg SecretKey.s2 hsk.symm
    have haHat : aHat = prims.expandA (prims.expandSeed seed).1 := by simp [aHat, hrho]
    rw [show pk.t1 = (prims.power2RoundVec (aHat * sk.s1 + sk.s2)).1 from by
          rw [hs1, hs2, haHat]; exact congr_arg PublicKey.t1 hpk.symm,
        show sk.t0 = (prims.power2RoundVec (aHat * sk.s1 + sk.s2)).2 from by
          rw [hs1, hs2, haHat]; exact congr_arg SecretKey.t0 hsk.symm]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_add, Primitives.power2RoundShiftVec, Primitives.power2RoundVec,
      Vector.map_map, Vector.getElem_map, Function.comp]
    exact h_laws.power2Round_decomp _
  have hAs1_hat : nttOps.matVecMul aHat (nttOps.hatVec sk.s1) =
      nttOps.hatVec (prims.power2RoundShiftVec pk.t1 + sk.t0 - sk.s2) := by
    rw [h_kg]
    refine Vector.ext fun j hj => ?_
    simp only [hatVec, HMul.hMul, coeffMatVecMul, unhatVec, matVecMul,
               Vector.getElem_map, Vector.getElem_sub, Vector.getElem_add]
    have hcancel : (fromHat (dot nttOps aHat[j] (Vector.map toHat sk.s1)) : Rq) +
        sk.s2[j] - sk.s2[j] = fromHat (dot nttOps aHat[j] (Vector.map toHat sk.s1)) := by
      abel
    rw [hcancel, laws.toHat_fromHat]
  have hMatScalarComm : nttOps.matVecMul aHat (nttOps.hatVec (c • sk.s1)) =
      nttOps.scalarVecMul (toHat c) (nttOps.matVecMul aHat (nttOps.hatVec sk.s1)) := by
    have hNTTSmul : nttOps.hatVec (c • sk.s1) =
        nttOps.scalarVecMul (toHat c) (nttOps.hatVec sk.s1) := by
      refine Vector.ext fun j hj => ?_
      simp only [hatVec, scalarVecMul, Vector.getElem_map]
      change nttOps.toHat (nttOps.coeffScalarVecMul c sk.s1)[j] = _
      simp only [coeffScalarVecMul, unhatVec, scalarVecMul, hatVec,
                 Vector.map_map, Vector.getElem_map, Function.comp_apply, laws.toHat_fromHat]
    rw [hNTTSmul]
    refine Vector.ext fun j hj => ?_
    simp only [matVecMul, scalarVecMul, Vector.getElem_map]
    exact nttOps.dot_scalar_right (toHat c) _ _
  simp only [hMatScalarComm, hAs1_hat]
  change (aHat * y)[i] +
      (nttOps.coeffScalarVecMul c (prims.power2RoundShiftVec pk.t1 + sk.t0 - sk.s2))[i] -
      (nttOps.coeffScalarVecMul c (prims.power2RoundShiftVec pk.t1))[i] =
      (aHat * y)[i] -
      (nttOps.coeffScalarVecMul c sk.s2)[i] + (nttOps.coeffScalarVecMul c sk.t0)[i]
  simp only [nttOps.coeffScalarVecMul_sub, nttOps.coeffScalarVecMul_add,
             Vector.getElem_sub, Vector.getElem_add]
  abel

end MLDSA
