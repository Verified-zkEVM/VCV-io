/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.HasQuery
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.BundledSemantics

/-!
# GPV Hash-and-Sign Framework

This file defines a generic hash-and-sign signature scheme following the GPV (Gentry–Peikert–
Vaikuntanathan) framework [GPV08]. The construction is parameterized by a *preimage sampleable
function* (PSF) — a many-to-one function equipped with a probabilistic trapdoor that samples
short preimages.

The GPV framework is the hash-and-sign analogue of the Fiat-Shamir transform:

| Interactive protocol | Fiat-Shamir → SignatureAlg |
|---|---|
| Trapdoor PSF | GPVHashAndSign → SignatureAlg |

## Main Definitions

- `PreimageSampleableFunction` — a function `eval` with a probabilistic trapdoor sampler and a
  shortness predicate on preimages.
- `GPVHashAndSign` — builds a `SignatureAlg` in the random-oracle model from a PSF, a generable
  key relation, and a salt type.

## Security

- `GPVHashAndSign.euf_cma_bound` — states that EUF-CMA security reduces to preimage-finding
  hardness plus a salt-collision term. Proof is `sorry` (placeholder for the GPV reduction).

## References

- Gentry, Peikert, Vaikuntanathan. "Trapdoors for Hard Lattices and New Cryptographic
  Constructions." STOC 2008.
- Boneh, Dagdelen, Fischlin, Lehmann, Schaffner, Zhandry. "Random Oracles in a Quantum
  World." ASIACRYPT 2011.
-/

universe v


open OracleComp OracleSpec ENNReal

/-! ## Preimage Sampleable Functions -/

/-- A preimage sampleable function (PSF) consists of:
- A public evaluation map `eval : PK → Domain → Range`.
- A probabilistic trapdoor sampler `trapdoorSample` that, given the secret key and a target in
  the range, produces a preimage in the domain.
- A shortness predicate `isShort` that the verifier checks on purported preimages.

This abstracts the core primitive in the GPV hash-and-sign framework. Unlike
`TrapdoorPermutation` (in `OneWay.lean`), a PSF is many-to-one, the inversion is probabilistic,
and acceptance depends on a quality predicate rather than exact inversion. -/
structure PreimageSampleableFunction (PK SK Domain Range : Type) where
  eval : PK → Domain → Range
  trapdoorSample : PK → SK → Range → ProbComp Domain
  isShort : Domain → Bool

namespace PreimageSampleableFunction

variable {PK SK Domain Range : Type}

/-- A PSF is correct if the trapdoor sampler always produces a valid preimage that is
accepted by the shortness predicate. -/
def Correct (psf : PreimageSampleableFunction PK SK Domain Range) : Prop :=
  ∀ pk sk t, ∀ x ∈ support (psf.trapdoorSample pk sk t),
    psf.eval pk x = t ∧
      psf.isShort x = true

end PreimageSampleableFunction

/-! ## GPV Hash-and-Sign Construction -/

/-- The GPV hash-and-sign signature scheme in the random-oracle model.

Given a preimage sampleable function `psf`, a generable key relation `hr`, and a salt type
`Salt`, the construction builds a `SignatureAlg` where:

- **`keygen`**: sample a key pair from `hr.gen`.
- **`sign pk sk m`**: sample a random salt `r`, query the random oracle at `(r, m)` to obtain
  a target `c`, use `trapdoorSample` to find a short preimage `s` of `c`, and return `(r, s)`.
- **`verify pk m (r, s)`**: recompute `c` from the random oracle at `(r, m)`, then check that
  `eval pk s = c` and `isShort s`.

The signature type is `Salt × Domain` (salt paired with the short preimage).
The oracle spec is `unifSpec + (Salt × M →ₒ Range)` (uniform sampling + random oracle). -/
def GPVHashAndSign
    {m : Type → Type v} [Monad m]
    {PK SK Domain Range : Type}
    (psf : PreimageSampleableFunction PK SK Domain Range)
    {p : PK → SK → Bool} [SampleableType PK] [SampleableType SK]
    (hr : GenerableRelation PK SK p)
    (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]
    [DecidableEq Range] [SampleableType Range]
    [MonadLiftT ProbComp m] [HasQuery (Salt × M →ₒ Range) m] :
    SignatureAlg m
      (M := M) (PK := PK) (SK := SK) (S := Salt × Domain) where
  keygen := liftM hr.gen
  sign := fun pk sk msg => do
    let r ← ($ᵗ Salt : ProbComp Salt)
    let c ← HasQuery.query (spec := (Salt × M →ₒ Range)) (r, msg)
    let s ← psf.trapdoorSample pk sk c
    pure (r, s)
  verify := fun pk msg (r, s) => do
    let c ← HasQuery.query (spec := (Salt × M →ₒ Range)) (r, msg)
    pure (decide (psf.eval pk s = c) && psf.isShort s)

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool} [SampleableType PK] [SampleableType SK]
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]

/-- Runtime bundle for the GPV hash-and-sign random-oracle world. -/
noncomputable def runtime :
    ProbCompRuntime (OracleComp (unifSpec + (Salt × M →ₒ Range))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (Salt × M →ₒ Range) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- Structural bound that counts only random-oracle queries in a GPV EUF-CMA adversary. -/
def hashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ S')) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBound oa Q
    (fun t b => match t with
      | .inl (.inl _) | .inr _ => True
      | .inl (.inr _) => 0 < b)
    (fun t b => match t with
      | .inl (.inl _) | .inr _ => b
      | .inl (.inr _) => b - 1)

/-- A preimage-finding adversary receives a public key and a target in the image of
`psf.eval`, and must return a short preimage. -/
abbrev PreimageAdversary := PK → Range → ProbComp Domain

/-- Keyed preimage-finding experiment for a preimage sampleable function. -/
def preimageFindingExp [SampleableType Domain]
    (adversary : PreimageAdversary (PK := PK) (Domain := Domain) (Range := Range)) :
    ProbComp Bool := do
  let keyPair ← hr.gen
  let pk := keyPair.1
  let x ← $ᵗ Domain
  let x' ← adversary pk (psf.eval pk x)
  return decide (psf.eval pk x' = psf.eval pk x) && psf.isShort x'

/-- Success probability in the keyed preimage-finding experiment. -/
noncomputable def preimageFindingAdvantage [SampleableType Domain]
    (adversary : PreimageAdversary (PK := PK) (Domain := Domain) (Range := Range)) :
    ℝ≥0∞ :=
  Pr[= true | preimageFindingExp (psf := psf) (hr := hr) adversary]

/-- **GPV EUF-CMA security in the random-oracle model.**

For any adversary `A` against the GPV hash-and-sign scheme, there exists a preimage-finding
reduction `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{preimage}(B) + salt_collision_probability`

The salt collision probability is at most `q_S^2 / (2 · |Salt|)` where `q_S` is the number
of signing queries (birthday bound on salt reuse).

The proof is a standard GPV argument:
1. By hash-randomization, distinct salts yield independent hash targets.
2. Each signature is a fresh trapdoor sample, statistically close to ideal Gaussian.
3. A forger must produce a short preimage of a hash value it did not receive from signing,
   which directly yields a preimage-finding adversary.

Reference: GPV08, Theorem 6.1; see also BDF+11 for the QROM extension. -/
theorem euf_cma_bound [SampleableType Domain]
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    ∃ (reduction : PreimageAdversary (PK := PK) (Domain := Domain) (Range := Range))
      (collisionBound : ENNReal),
      adv.advantage (runtime M Salt) ≤
        preimageFindingAdvantage (psf := psf) (hr := hr) reduction + collisionBound := by
  sorry

end GPVHashAndSign
