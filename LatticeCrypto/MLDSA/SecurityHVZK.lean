/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Security

/-!
# ML-DSA Honest-Verifier Zero-Knowledge: the simulator

This file develops the honest-verifier zero-knowledge (HVZK) simulator for the ML-DSA
identification scheme, towards refining the vacuous placeholder `MLDSA.idsWithAbort_hvzk`
(`LatticeCrypto/MLDSA/Security.lean`). The placeholder asserts only that *some* simulator with
*some* nonnegative total-variation error exists; that is trivially dischargeable with
`ζ_zk := 1` (because `tvDist ≤ 1` always, `SPMF.tvDist_le_one`) and carries no content.

`hvzkSimulator` is the concrete Dilithium HVZK simulator (no witness), built from the
commitment-recovery equation. It samples the challenge hash `c̃` and the short response `z` from
their marginals, applies the same `‖z‖∞ < γ₁ − β` rejection gate that the honest `respond`
applies, and reconstructs the commitment `w₁` as `UseHint(h, Az − c·t₁·2^d)` via
`computeWApprox`, exactly the value that `verify` recomputes. `hvzkSimulator_verify` records the
consequence: every non-aborting simulated transcript is accepted by `verify` (modulo the
hint-weight side condition the honest distribution also imposes).

## Why there is no quantitative HVZK theorem here yet

A *perfect* HVZK statement pinning this simulator with error `ζ_zk = 0`, i.e.
`(identificationScheme p prims).HVZK (hvzkSimulator p prims) 0`, is **unsound** and was
deliberately not added. `HVZK ids sim ζ` compares the full honest and simulated distributions
over `Option (Commit × Chal × Resp)` by total-variation distance, so it is sensitive to the
abort probability. The honest `respond` (`Scheme.lean`) aborts on four gates — `‖z‖∞ < γ₁ − β`,
the secret-dependent `‖LowBits(w − c·s₂)‖∞ < γ₂ − β`, `‖c·t₀‖∞ < γ₂`, and `hintWeight h ≤ ω` —
whereas `hvzkSimulator` applies only the first. Because the honest abort event is a strict
superset and `tvDist ≥ |Pr_honest[none] − Pr_sim[none]|`, the distance is strictly positive in
general (with `p`/`prims` unconstrained and no `Primitives.Laws` hypothesis a literal
counterexample exists, e.g. `hintWeight ≡ 1` with `ω = 0`). The honest hint `h` is moreover a
deterministic function of the witness, against the simulator's independent-uniform draw.

A sound quantitative statement must therefore either (i) use a *statistical* bound
`ζ_zk = ε_low + ε_hint` capturing the un-mirrored gates and the hint-marginal distance (the form
proved in `HVZK_FSa.ec`), or (ii) reach `ζ_zk = 0` only with a gate-mirroring simulator under an
explicit `[Primitives.Laws]` hypothesis. Both are sizeable rejection-sampling arguments left for
future work; this file provides the simulator and its acceptance lemma as the shared substrate.

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246), Lemma 4 (HVZK of the IDS)
- EasyCrypt `HVZK_FSa.ec`, `SimplifiedScheme.ec` (formosa-crypto/dilithium)
- NIST FIPS 204, Algorithms 7 and 8
-/


open OracleComp OracleSpec ENNReal
open LatticeCrypto TransformOps

namespace MLDSA

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High]

section HVZK

variable [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [SampleableType (Vector prims.Hint p.k)] [IsUniformSpec unifSpec]

/-! ### The simulator -/

/-- The Dilithium honest-verifier zero-knowledge simulator for the ML-DSA identification
scheme. It receives only the public key `pk` (no secret) and produces an optional transcript
`(w₁, c̃, (z, h))`:

1. sample the challenge hash `c̃` uniformly (its honest marginal is uniform);
2. sample the short response `z` uniformly from `RqVec p.l` and the hint vector `h` from its
   marginal;
3. apply the same response gate `‖z‖∞ < γ₁ − β` the honest `respond` applies — on failure,
   abort (`none`);
4. on success, reconstruct the commitment via the verification equation
   `w₁ = UseHint(h, computeWApprox(Â, c, z, t₁))` and output `some (w₁, c̃, (z, h))`.

Because `w₁` is defined exactly as the value `verify` recomputes, every non-aborting simulated
transcript is accepted by `verify` (see `hvzkSimulator_verify`). The remaining HVZK content is
that this distribution is statistically close to the honest transcript distribution; the gap is
the rejection-sampling error `hvzkBound`. -/
noncomputable def hvzkSimulator (pk : PublicKey p prims) :
    ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)) := do
  let cTilde ← $ᵗ (CommitHashBytes p)
  let z ← $ᵗ (RqVec p.l)
  let h ← $ᵗ (Vector prims.Hint p.k)
  if polyVecNorm z < p.gamma1 - p.beta then
    let c := prims.sampleInBall cTilde
    let aHat := prims.expandA pk.rho
    let wApprox := computeWApprox p prims aHat c z pk.t1
    let w1 := prims.useHintVec h wApprox
    return some (w1, cTilde, (z, h))
  else
    return none

/-! ### Well-definedness: simulated non-aborts are accepted -/

omit [SampleableType (CommitHashBytes p)]
  [SampleableType (Vector prims.Hint p.k)] [IsUniformSpec unifSpec] in
/-- Every transcript in the support of `hvzkSimulator pk` is either an abort or an accepting
transcript: the recovered `w₁` satisfies `verify pk w₁ c̃ (z, h) = true` whenever the
hint-weight side condition `hintWeight h ≤ ω` holds. (The `‖z‖∞ < γ₁ − β` half of `verify`
is exactly the simulator's own rejection gate, so it holds on the support by construction.)

This is the simulator's well-definedness: it never emits a non-aborting transcript that the
verifier would reject, modulo the hint-weight side condition that the honest distribution also
imposes. -/
theorem hvzkSimulator_verify (pk : PublicKey p prims) (cTilde : CommitHashBytes p)
    (z : RqVec p.l) (h : Vector prims.Hint p.k)
    (hz : polyVecNorm z < p.gamma1 - p.beta)
    (hw : prims.hintWeight h ≤ p.omega) :
    (identificationScheme p prims).verify pk
        (prims.useHintVec h
          (computeWApprox p prims (prims.expandA pk.rho) (prims.sampleInBall cTilde) z pk.t1))
        cTilde (z, h) = true := by
  simp only [identificationScheme, Bool.and_eq_true, decide_eq_true_eq, and_true]
  exact ⟨hz, hw⟩

end HVZK

end MLDSA
