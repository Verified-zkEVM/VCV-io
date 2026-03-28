/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.IdenSchemeWithAbort
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.Constructions.Replicate

/-!
# Fiat-Shamir with Aborts Transform

This file defines the Fiat-Shamir with aborts transform, which converts an identification
scheme with aborts (`IdenSchemeWithAbort`) into a signature scheme (`SignatureAlg`). Unlike
the standard Fiat-Shamir transform (`FiatShamir`), signing involves a **retry loop**: the
prover commits, hashes (message, commitment) to get a challenge, attempts to respond, and if
the response aborts, restarts from scratch.

This is the transform used by ML-DSA (CRYSTALS-Dilithium, FIPS 204).

## Main Definitions

- `FiatShamirWithAbort`: the signature scheme produced by the transform
- `FiatShamirWithAbort.euf_cma_bound`: EUF-CMA security statement (proof is future work)

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246)
- EasyCrypt `FSabort.eca`, `SimplifiedScheme.ec`
- NIST FIPS 204, Algorithms 2 (ML-DSA.Sign) and 3 (ML-DSA.Verify)
-/

set_option autoImplicit false

universe u v

open OracleComp OracleSpec

variable {S W W' St C Z P : Type}
  {p : S → W → Bool}
  [SampleableType S] [SampleableType W]
  [DecidableEq W'] [DecidableEq C] [SampleableType C]

/-- The Fiat-Shamir with aborts transform applied to an identification scheme with aborts.
Produces a signature scheme in the random oracle model.

The signing algorithm runs a retry loop (up to `maxAttempts` iterations):
1. Commit to get `(w', st)`
2. Hash `(msg, w')` using the random oracle to get challenge `c`
3. Try to respond; if `none` (abort), retry from step 1

The type parameters are:
- `M`: message space
- `W'`: public commitment (included in signature for verification)
- `C`: challenge space (range of the hash/random oracle)
- `Z`: response space
- `S` / `W`: statement / witness (= public key / secret key) -/
def FiatShamirWithAbort (ids : IdenSchemeWithAbort S W W' St C Z p)
    (hr : GenerableRelation S W p) (M : Type) [DecidableEq M]
    [Inhabited Z] (maxAttempts : ℕ) :
    SignatureAlg (OracleComp (unifSpec + (M × W' →ₒ C)))
      (M := M) (PK := S) (SK := W) (S := W' × Z) where
  keygen := hr.gen
  sign := fun _pk sk m => do
    let result ← OracleComp.replicate maxAttempts (do
      let (w', st) ← (ids.commit _pk sk : ProbComp _)
      let c ← query (spec := unifSpec + (M × W' →ₒ C)) (Sum.inr (m, w'))
      let oz ← (ids.respond _pk sk st c : ProbComp _)
      return oz.map fun z => (w', z))
    match result.filterMap id |>.head? with
    | some sig => return sig
    | none =>
        let (w', st) ← (ids.commit _pk sk : ProbComp _)
        let c ← query (spec := unifSpec + (M × W' →ₒ C)) (Sum.inr (m, w'))
        let oz ← (ids.respond _pk sk st c : ProbComp _)
        return (w', oz.getD default)
  verify := fun pk m (w', z) => do
    let c ← query (spec := unifSpec + (M × W' →ₒ C)) (Sum.inr (m, w'))
    return ids.verify pk w' c z
  exec comp :=
    let ro : QueryImpl (M × W' →ₒ C)
      (StateT ((M × W' →ₒ C).QueryCache) ProbComp) := randomOracle
    let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((M × W' →ₒ C).QueryCache) ProbComp)
    StateT.run' (simulateQ (idImpl + ro) comp) ∅
  lift_probComp := monadLift
  exec_lift_probComp c := by
    let ro : QueryImpl (M × W' →ₒ C)
      (StateT ((M × W' →ₒ C).QueryCache) ProbComp) := randomOracle
    let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((M × W' →ₒ C).QueryCache) ProbComp)
    change StateT.run' (simulateQ (idImpl + ro) (monadLift c)) ∅ = c
    rw [show simulateQ (idImpl + ro) (monadLift c) = simulateQ idImpl c by
      simpa [MonadLift.monadLift] using
        (QueryImpl.simulateQ_add_liftComp_left
          (impl₁' := idImpl) (impl₂' := ro) c)]
    have hid : ∀ t s, (idImpl t).run' s = query t := by
      intro t s; rfl
    simpa using
      (StateT_run'_simulateQ_eq_self (so := idImpl) (h := hid) (oa := c)
        (s := (∅ : (M × W' →ₒ C).QueryCache)))

namespace FiatShamirWithAbort

variable (ids : IdenSchemeWithAbort S W W' St C Z p)
  (hr : GenerableRelation S W p)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

section EUF_CMA

set_option linter.unusedDecidableInType false

variable [DecidableEq Z] [Inhabited Z]

/-- Structural query bound counting only random-oracle queries in a
Fiat-Shamir with aborts EUF-CMA adversary. -/
def hashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (M × W' →ₒ C)) + (M →ₒ S')) α)
    (Q : ℕ) : Prop :=
  OracleComp.IsQueryBound oa Q
    (fun t b => match t with
      | .inl (.inl _) | .inr _ => True
      | .inl (.inr _) => 0 < b)
    (fun t b => match t with
      | .inl (.inl _) | .inr _ => b
      | .inl (.inr _) => b - 1)

/-- EUF-CMA security bound for the Fiat-Shamir with aborts transform.

The security reduces to:
1. The hardness of the underlying relation (via SelfTargetMSIS-like assumption)
2. The HVZK property of the identification scheme (for simulating signing queries)
3. Commitment recoverability (for the CMA-to-NMA reduction)

The proof follows the structure of Theorem 4 in the CRYPTO 2023 paper. -/
theorem euf_cma_bound
    (_hc : ids.Complete)
    (sim : S → ProbComp (Option (W' × C × Z)))
    (_hhvzk : ids.HVZK sim)
    (recover : S → C → Z → W')
    (_hcr : ids.CommitmentRecoverable recover)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort ids hr M maxAttempts))
    (qBound : ℕ)
    (_hQ : ∀ pk, hashQueryBound M
      (S' := W' × Z) (oa := adv.main pk) qBound) :
    ∃ reduction : S → ProbComp W,
      adv.advantage ≤
        Pr[= true | hardRelationExp (r := p) reduction] := by
  sorry

end EUF_CMA

end FiatShamirWithAbort
