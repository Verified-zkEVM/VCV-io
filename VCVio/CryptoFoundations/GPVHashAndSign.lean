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
function* (PSF), a many-to-one function equipped with a probabilistic trapdoor that samples
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

The PFDH (Probabilistic Full-Domain Hash) variant of the GPV scheme uses a random salt per
signing query. The precise EUF-CMA bound from [FGdG+25] Theorem 1 is:

  `Adv^{UF-CMA}(A) ≤ (r_u^{C_s} · (r_p^{C_s} · Adv^{ISIS}(B))^{...})^{...}`
  `                  + tail_bound + Q_s · (C_s + Q_H) / 2^k`

where the salt-collision term `Q_s · (C_s + Q_H) / 2^k` bounds the probability that
a fresh salt collides with any prior RO query. The simpler birthday bound
`qSign² / (2 · |Salt|)` from GPV08 Prop 6.2 is slightly looser but still valid and is
the one we formalize here.

The proof decomposes into:
- `GPVHashAndSign.reduction`: the preimage-finding adversary (sign-then-hash simulation)
- `GPVHashAndSign.collisionBound`: the salt-collision birthday bound
- `GPVHashAndSign.forgery_yields_preimage`: the core game-hop

## References

- [FGdG+25]: Fouque, Gajland, de Groote, Janneck, Kiltz. "A Closer Look at Falcon."
  ePrint 2024/1769. First concrete proof for Falcon+ (Theorem 1).
- [Jia+26]: Jia, Zhang, Yu, Tang. "Revisiting the Concrete Security of Falcon-type
  Signatures." ePrint 2026/096. Tightens Rényi loss to < 0.2 bits.
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008, Propositions 6.1–6.2.
- BDF+11: Boneh et al. "Random Oracles in a Quantum World." ASIACRYPT 2011.
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
    {p : PK → SK → Bool}
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
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

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

/-! ## Proof Decomposition

The EUF-CMA security proof proceeds by a game-hopping argument:

**Game 0**: The real EUF-CMA experiment with a lazy random oracle and the honest
signing oracle (trapdoor sampler).

**Game 1**: Replace signing with "sign-then-hash": for each signing query on message `m`,
sample a short preimage `s ← D_short`, set `c := psf.eval pk s`, program the RO at
`(r, m) := c`, and return `(r, s)`. This is indistinguishable from Game 0 when the PSF
sampler is correct (the output distribution conditioned on the target is the same).

**Bad event**: A salt collision occurs (two distinct signing queries or the forgery reuse
the same `(salt, message)` pair as a prior RO entry). Under the birthday bound, this
happens with probability at most `q_S² / (2 · |Salt|)`.

**Game 2 (reduction)**: Embed the preimage-finding challenge `y` at a random position in
the RO table. If the adversary's forgery targets that position, extract the short preimage.
The success probability of the reduction is at least `Adv^{CMA}(A) - collisionBound`,
giving the desired bound.
-/

/-- The GPV reduction adversary. Given a public key `pk` and a target `y : Range`,
the reduction internally simulates the CMA experiment for the adversary:

1. Program a lazy random oracle, embedding `y` at a random position.
2. Answer signing queries by sampling short preimages and programming the RO
   (sign-then-hash strategy, using the PSF correctness).
3. Run the adversary and extract the short preimage from any valid forgery.

This is defined abstractly as the composition of the adversary's logic with
the simulation internals. The detailed simulation requires replaying the
adversary's oracle interactions as `ProbComp` computations. -/
noncomputable def reduction [SampleableType Domain]
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    PreimageAdversary (PK := PK) (Domain := Domain) (Range := Range) :=
  fun _pk _y => sorry

/-- The salt-collision birthday bound (GPV08, Proposition 6.2).

For `qSign` signing queries with salts drawn uniformly from a set of size `|Salt|`,
the birthday bound gives collision probability at most `qSign² / (2 · |Salt|)`.

For Falcon with 40-byte salts (`|Salt| = 2^320`) and `qSign ≤ 2^64`:
  `collisionBound (Bytes 40) (2^64) = 2^128 / (2 · 2^320) = 2^{-193}` -/
noncomputable def collisionBound (qSign : ℕ) : ENNReal :=
  (qSign : ENNReal) ^ 2 / (2 * Fintype.card Salt)

/-- **Key lemma** (GPV08, Proposition 6.2, proof): when the PSF is correct and the
adversary makes at most `qSign` signing queries, its EUF-CMA advantage is bounded by
the preimage-finding advantage of the reduction plus the salt-collision birthday bound.

The argument proceeds in two steps:

**Step 1 (sign-then-hash ≡ real).**  Replace the signing oracle with one that:
  (a) samples a fresh salt `r ← Salt`,
  (b) samples a short preimage `s ← SampleDom`,
  (c) programs the RO at `(r, msg) := psf.eval pk s`.
By PSF correctness (`hcorrect`), the joint distribution `(r, s, H(r, msg))` is identical
to the real game. This step is exact (zero statistical distance).

**Step 2 (embed challenge).**  In the sign-then-hash game, every RO entry is
programmed by the simulator. Embed the preimage-finding challenge `y` at a
random RO position. If the adversary's forgery `(msg*, (r*, s*))` hits that
position, extract `s*` as a valid preimage. The success probability of the
reduction equals the adversary's advantage minus the salt-collision probability.

The salt-collision probability is at most `qSign² / (2 · |Salt|)` by the birthday bound:
each of the `qSign` salts is drawn uniformly, and a collision would cause the RO
programming to conflict. -/
theorem forgery_yields_preimage [SampleableType Domain]
    (hcorrect : psf.Correct) (qSign : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    adv.advantage (runtime M Salt) ≤
      preimageFindingAdvantage (psf := psf) (hr := hr)
        (reduction psf hr M Salt adv) +
      collisionBound Salt qSign := by
  sorry

/-- **GPV PFDH EUF-CMA security in the random-oracle model** (GPV08, Proposition 6.2).

For any adversary `A` making at most `qSign` signing queries against the GPV hash-and-sign
scheme with a correct PSF and `k`-bit salts, there exists a preimage-finding reduction `B`
such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{preimage}(B) + qSign² / (2 · |Salt|)`

The reduction `B` is **tight**: unlike FDH with trapdoor permutations (which loses a factor
of `Q_hash`), the PSF-based reduction exploits collision resistance to avoid guessing which
hash query the adversary will target.

The salt-collision term `qSign² / (2 · |Salt|)` is the birthday bound on reuse of the
`(salt, message)` random-oracle input across signing queries. For Falcon with 40-byte
salts (`|Salt| = 2^320`), this is `2^{-193}` even for `qSign = 2^64`.

References: GPV08 Proposition 6.2; BDF+11 for the QROM extension. -/
theorem euf_cma_bound [SampleableType Domain]
    (hcorrect : psf.Correct) (qSign : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    ∃ (red : PreimageAdversary (PK := PK) (Domain := Domain) (Range := Range)),
      adv.advantage (runtime M Salt) ≤
        preimageFindingAdvantage (psf := psf) (hr := hr) red +
        collisionBound Salt qSign := by
  exact ⟨reduction psf hr M Salt adv,
    forgery_yields_preimage psf hr M Salt hcorrect qSign adv⟩

end GPVHashAndSign
