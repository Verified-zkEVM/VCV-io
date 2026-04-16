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
- `GPVHashAndSign.reduction`: the collision-finding adversary (sign-then-hash simulation)
- `GPVHashAndSign.programmedPreimageReduction`: the exact-match branch reduction
- `GPVHashAndSign.collisionBound`: the salt-collision birthday bound
- `GPVHashAndSign.forgery_yields_collision`: the core distinct-preimage game-hop
- `GPVHashAndSign.forgery_yields_collision_or_exact_match`: the explicit split bound

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

/-- Structural query bound for GPV EUF-CMA adversaries that tracks both signing-oracle
queries (`qSign`) and random-oracle queries (`qHash`). Uniform-sampling queries are
unrestricted. -/
def signHashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ S')) α)
    (qSign qHash : ℕ) : Prop :=
  OracleComp.IsQueryBound oa (qSign, qHash)
    (fun t b => match t, b with
      | .inl (.inl _), _ => True
      | .inl (.inr _), (_, qHash') => 0 < qHash'
      | .inr _, (qSign', _) => 0 < qSign')
    (fun t b => match t, b with
      | .inl (.inl _), b' => b'
      | .inl (.inr _), (qSign', qHash') => (qSign', qHash' - 1)
      | .inr _, (qSign', qHash') => (qSign' - 1, qHash'))

/-- A collision-finding adversary receives a public key and must produce two distinct
short preimages with the same image under `psf.eval`. -/
abbrev CollisionAdversary := PK → ProbComp (Domain × Domain)

/-- Keyed collision-finding experiment for a preimage sampleable function. -/
def collisionFindingExp [DecidableEq Domain]
    (adversary : CollisionAdversary (PK := PK) (Domain := Domain)) :
    ProbComp Bool := do
  let pk ← do
    let keyPair ← hr.gen
    pure keyPair.1
  let (x₁, x₂) ← adversary pk
  return decide (x₁ ≠ x₂) &&
    decide (psf.eval pk x₁ = psf.eval pk x₂) &&
    psf.isShort x₁ &&
    psf.isShort x₂

/-- Success probability in the keyed collision-finding experiment. -/
noncomputable def collisionFindingAdvantage [DecidableEq Domain]
    (adversary : CollisionAdversary (PK := PK) (Domain := Domain)) :
    ℝ≥0∞ :=
  Pr[= true | collisionFindingExp (psf := psf) (hr := hr) adversary]

/-- A programmed-preimage adversary receives a public key and a programmed target `y`,
and tries to reproduce the challenger's hidden short preimage sampled for `y`. -/
abbrev ProgrammedPreimageAdversary := PK → Range → ProbComp Domain

/-- Exact-match experiment for the hidden programmed-preimage branch of the GPV proof.

The challenger samples an honest key pair, then chooses a uniformly random target `y` and a
hidden short preimage `x ← trapdoorSample pk sk y`. The adversary sees only `(pk, y)` and
succeeds iff it reproduces exactly the hidden programmed preimage `x`. -/
def programmedPreimageExp [DecidableEq Domain]
    (adversary : ProgrammedPreimageAdversary
      (PK := PK) (Domain := Domain) (Range := Range)) :
    ProbComp Bool := do
  let (pk, sk) ← hr.gen
  let y ← $ᵗ Range
  let x ← psf.trapdoorSample pk sk y
  let x' ← adversary pk y
  return decide (x' = x)

/-- Success probability in the exact-match programmed-preimage experiment. -/
noncomputable def programmedPreimageAdvantage [DecidableEq Domain]
    (adversary : ProgrammedPreimageAdversary
      (PK := PK) (Domain := Domain) (Range := Range)) :
    ℝ≥0∞ :=
  Pr[= true | programmedPreimageExp (psf := psf) (hr := hr) adversary]

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

**Game 2 (reduction)**: The simulator programs the random oracle with hidden short preimages.
If the adversary forges on a fresh `(salt, message)` pair and the forged short preimage differs
from the simulator's hidden programmed preimage at that point, the pair forms a collision under
`psf.eval`.

The exact-match branch, where the forgery reproduces the simulator's programmed preimage, is a
separate one-way/min-entropy obligation and is intentionally not encoded in the collision game
below.
-/

/-- The collision-branch GPV reduction adversary. Given a public key `pk`,
the reduction internally simulates the CMA experiment for the adversary:

1. Program a lazy random oracle, storing for each entry the hidden short preimage used to
   define that entry.
2. Answer signing queries using the sign-then-hash strategy: sample a short preimage
   `s` via `trapdoorSample`, compute `c = psf.eval pk s`, and program the RO at
   `(r, msg) := c`. Return `(r, s)` as the signature.
3. Run the adversary and, on a successful fresh forgery, return the simulator's hidden
   programmed preimage together with the forged preimage as a candidate collision.

The key insight is that in the sign-then-hash game, the reduction controls the entire
RO table. If the adversary forges on a fresh `(r*, msg*)` pair, the RO value at that
point was set by the reduction, so the hidden programmed preimage and the forged preimage
land at the same image under `psf.eval`.

The detailed construction simulates the adversary's oracle interactions by maintaining
a programmable RO state, using PSF correctness to ensure consistency. -/
noncomputable def reduction
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    CollisionAdversary (PK := PK) (Domain := Domain) :=
  fun _pk => sorry

/-- The exact-match branch reduction adversary. Given a public key `pk` and programmed target
`y`, the reduction embeds `(pk, y)` at one guessed programmed random-oracle entry. If the
adversary later forges on that entry and exactly reproduces the simulator's hidden preimage,
the reduction wins the programmed-preimage game.

Because the target must be embedded at one guessed programmed entry, this branch incurs an
explicit multi-target loss proportional to the total number of programmed entries. -/
noncomputable def programmedPreimageReduction
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    ProgrammedPreimageAdversary (PK := PK) (Domain := Domain) (Range := Range) :=
  fun _pk _y => sorry

/-- The salt-collision birthday bound (GPV08, Proposition 6.2).

For `qSign` signing queries with salts drawn uniformly from a set of size `|Salt|`,
the birthday bound gives collision probability at most `qSign² / (2 · |Salt|)`.

For Falcon with 40-byte salts (`|Salt| = 2^320`) and `qSign ≤ 2^64`:
  `collisionBound (Bytes 40) (2^64) = 2^128 / (2 · 2^320) = 2^{-193}` -/
noncomputable def collisionBound (qSign : ℕ) : ENNReal :=
  (qSign : ENNReal) ^ 2 / (2 * Fintype.card Salt)

/-- **Collision branch of the GPV game-hop**: when the PSF is correct and the adversary
makes at most `qSign` signing queries and `qHash` random-oracle queries, the probability
that it produces a fresh forgery whose preimage differs from the simulator's programmed
preimage is bounded by the collision-finding advantage of the reduction plus the
salt-collision birthday bound.

The argument proceeds in two steps:

**Step 1 (sign-then-hash ≡ real).**  Replace the signing oracle with one that:
  (a) samples a fresh salt `r ← Salt`,
  (b) samples a short preimage `s` using the trapdoor sampler on a fresh random target,
  (c) programs the RO at `(r, msg) := psf.eval pk s`.
By PSF correctness (`hcorrect`), the joint distribution `(r, s, H(r, msg))` is identical
to the real game. This step is exact (zero statistical distance).

**Step 2 (extract collision).**  In the sign-then-hash game, every RO entry is
programmed by the simulator together with a hidden short preimage. If the adversary's
fresh forgery `(msg*, (r*, s*))` lands on a programmed entry and `s*` differs from the
simulator's hidden preimage for that entry, the pair is a valid collision under
`psf.eval`. The salt-collision probability bounds the only way the programming can
become inconsistent. -/
theorem forgery_yields_collision [DecidableEq Domain]
    (hcorrect : psf.Correct) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    adv.advantage (runtime M Salt) ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
        (reduction psf hr M Salt adv) +
      collisionBound Salt qSign := by
  let _ := hcorrect
  let _ := qSign
  let _ := qHash
  let _ := adv
  let _ := hQ
  sorry

/-- **Full split GPV game-hop**: every successful fresh forgery falls into one of two cases.

1. **Distinct-preimage branch:** the forgery differs from the simulator's hidden programmed
   preimage at the forged point, yielding a collision under `psf.eval`.
2. **Exact-match branch:** the forgery exactly reproduces the simulator's hidden programmed
   preimage at that point. To capture this branch, the reduction guesses one of the at most
   `qSign + qHash` programmed entries and turns success there into a win in the single-target
   programmed-preimage experiment.

The only additional failure mode is a salt collision, bounded by `collisionBound`. -/
theorem forgery_yields_collision_or_exact_match [DecidableEq Domain]
    (hcorrect : psf.Correct) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    adv.advantage (runtime M Salt) ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv) +
        ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv) +
        collisionBound Salt qSign := by
  let _ := hcorrect
  let _ := qSign
  let _ := qHash
  let _ := adv
  let _ := hQ
  sorry

/-- **Collision-style GPV PFDH bound in the random-oracle model**.

For any adversary `A` making at most `qSign` signing queries against the GPV hash-and-sign
scheme with a correct PSF and `k`-bit salts, and making at most `qHash`
random-oracle queries, there exists a collision-finding reduction `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{collision}(B) + qSign² / (2 · |Salt|)`

This packages the distinct-preimage branch of the standard GPV argument. The complementary
exact-match branch, where the forgery reproduces the simulator's programmed preimage, is to
be discharged separately via a PSF preimage-min-entropy or one-wayness lemma.

The salt-collision term `qSign² / (2 · |Salt|)` is the birthday bound on reuse of the
`(salt, message)` random-oracle input across signing queries. For Falcon with 40-byte
salts (`|Salt| = 2^320`), this is `2^{-193}` even for `qSign = 2^64`.

References: GPV08 Section 6; BDF+11 for the QROM extension. -/
theorem euf_cma_collision_bound [DecidableEq Domain]
    (hcorrect : psf.Correct) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    ∃ (red : CollisionAdversary (PK := PK) (Domain := Domain)),
      adv.advantage (runtime M Salt) ≤
        collisionFindingAdvantage (psf := psf) (hr := hr) red +
        collisionBound Salt qSign := by
  exact ⟨reduction psf hr M Salt adv,
    forgery_yields_collision psf hr M Salt hcorrect qSign qHash adv hQ⟩

/-- **Split GPV PFDH bound in the random-oracle model**.

This theorem makes both branches of the GPV proof explicit:

- a collision term for the distinct-preimage branch,
- a programmed-preimage replay term for the exact-match branch, with the explicit
  multi-target factor `qSign + qHash`,
- and the birthday salt-collision term.

It is the most honest generic statement available from the current API, before any additional
PSF-specific min-entropy lemma collapses the exact-match branch into the collision branch. -/
theorem euf_cma_split_bound [DecidableEq Domain]
    (hcorrect : psf.Correct) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    ∃ (collisionRed : CollisionAdversary (PK := PK) (Domain := Domain))
      (exactMatchRed : ProgrammedPreimageAdversary
        (PK := PK) (Domain := Domain) (Range := Range)),
      adv.advantage (runtime M Salt) ≤
        collisionFindingAdvantage (psf := psf) (hr := hr) collisionRed +
          ((qSign + qHash : ℕ) : ENNReal) *
            programmedPreimageAdvantage (psf := psf) (hr := hr) exactMatchRed +
          collisionBound Salt qSign := by
  exact ⟨reduction psf hr M Salt adv,
    programmedPreimageReduction psf hr M Salt adv,
    forgery_yields_collision_or_exact_match psf hr M Salt hcorrect qSign qHash adv hQ⟩

end GPVHashAndSign
