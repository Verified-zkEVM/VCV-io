/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
public import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps
public import VCVio.OracleComp.Coercions.Add
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
public import VCVio.ProgramLogic.Relational.ProgrammingOracle

/-! # GPV Hash-and-Sign: Preimage Sampleable Functions and the Scheme

The preimage-sampleable-function (PSF) abstraction, the GPV hash-and-sign
signature construction in the random-oracle model, its runtime bundle, the
structural query-bound predicates, and the collision-finding and
programmed-preimage adversary interfaces with their experiments.
-/

public section

universe v


open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

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
@[expose] def Correct (psf : PreimageSampleableFunction PK SK Domain Range) : Prop :=
  ∀ pk sk t, ∀ x ∈ support (psf.trapdoorSample pk sk t),
    psf.eval pk x = t ∧
      psf.isShort x = true

/-- A PSF is correct *at a fixed key pair* `(pk, sk)` if the trapdoor sampler at that key always
produces a valid preimage that is accepted by the shortness predicate. This is the per-key slice of
`Correct`: `Correct psf` is definitionally `∀ pk sk, psf.CorrectAt pk sk`. -/
@[expose]
def CorrectAt (psf : PreimageSampleableFunction PK SK Domain Range) (pk : PK) (sk : SK) : Prop :=
  ∀ (t : Range) (x : Domain), x ∈ support (psf.trapdoorSample pk sk t) →
    psf.eval pk x = t ∧ psf.isShort x = true

/-- The GPV *regularity* (preimage-sampleability) property, expressed externally as an
equality of joint distributions.

A PSF is regular when there is a domain sampler `domainSample : PK → ProbComp Domain` such
that, for every key pair `(pk, sk)`, the joint distribution of `(eval pk s, s)` for a
forward-sampled preimage `s ← domainSample pk` matches the joint distribution of `(c, s)`
where the target `c` is drawn uniformly from `Range` and `s ← trapdoorSample pk sk c` is the
trapdoor preimage of `c`.

This is the classical GPV08 preimage-sampleability requirement: sampling a short preimage and
hashing it forward is statistically identical to sampling a uniform target and inverting it
with the trapdoor. It is the hypothesis that justifies the sign-then-hash hop in the EUF-CMA
proof. It is entered as an external hypothesis rather than as a field of
`PreimageSampleableFunction`, so the generic GPV theorem stays loss-free and each concrete
instance (e.g. Falcon) accounts for any sampler imperfection separately.

The property is satisfiable in principle: when `eval pk` is a bijection,
`trapdoorSample pk sk c := pure ((eval pk)⁻¹ c)` and `domainSample pk := $ᵗ Domain` realize
the equality. It is also non-trivial: the equation genuinely constrains `domainSample` against
the trapdoor sampler, so it is not vacuously true. -/
@[expose] def Regularity [SampleableType Range]
    (psf : PreimageSampleableFunction PK SK Domain Range) : Prop :=
  ∃ domainSample : PK → ProbComp Domain,
    ∀ (pk : PK) (sk : SK),
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]

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
@[expose] def GPVHashAndSign
    {m : Type → Type v} [Monad m]
    {PK SK Domain Range : Type}
    (psf : PreimageSampleableFunction PK SK Domain Range)
    {p : PK → SK → Bool}
    (hr : GenerableRelation PK SK p)
    (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]
    [DecidableEq Range] [SampleableType Range]
    [MonadLiftT ProbComp m] [MonadLiftT (OracleQuery (Salt × M →ₒ Range)) m] :
    SignatureAlg m
      (M := M) (PK := PK) (SK := SK) (S := Salt × Domain) where
  keygen := liftM hr.gen
  sign := fun pk sk msg => do
    let r ← ($ᵗ Salt : ProbComp Salt)
    let c ← (Salt × M →ₒ Range).query (r, msg)
    let s ← psf.trapdoorSample pk sk c
    pure (r, s)
  verify := fun pk msg (r, s) => do
    let c ← (Salt × M →ₒ Range).query (r, msg)
    pure (decide (psf.eval pk s = c) && psf.isShort s)

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

/-- Runtime bundle for the GPV hash-and-sign random-oracle world. -/
@[expose] noncomputable def runtime :
    ProbCompRuntime (OracleComp (unifSpec + (Salt × M →ₒ Range))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (Salt × M →ₒ Range) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- Structural query bound for GPV EUF-CMA adversaries that tracks both signing-oracle
queries (`qSign`) and random-oracle queries (`qHash`). Uniform-sampling queries are
unrestricted.

Defined as the conjunction of two predicate-targeted query bounds `IsQueryBoundP`, one per
counted oracle. Because the two index predicates are disjoint, the conjunction is
equivalent to the prior single-vector `IsQueryBound` formulation. -/
@[expose] def signHashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ S')) α)
    (qSign qHash : ℕ) : Prop :=
  oa.IsQueryBoundP (· matches .inr _) qSign ∧
  oa.IsQueryBoundP (· matches .inl (.inr _)) qHash

/-- A collision-finding adversary receives a public key and must produce two distinct
short preimages with the same image under `psf.eval`. -/
abbrev CollisionAdversary := PK → ProbComp (Domain × Domain)

/-- Keyed collision-finding experiment for a preimage sampleable function. -/
@[expose] def collisionFindingExp [DecidableEq Domain]
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
@[expose] noncomputable def collisionFindingAdvantage [DecidableEq Domain]
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
@[expose] def programmedPreimageExp [DecidableEq Domain]
    (adversary : ProgrammedPreimageAdversary
      (PK := PK) (Domain := Domain) (Range := Range)) :
    ProbComp Bool := do
  let (pk, sk) ← hr.gen
  let y ← $ᵗ Range
  let x ← psf.trapdoorSample pk sk y
  let x' ← adversary pk y
  return decide (x' = x)

/-- Success probability in the exact-match programmed-preimage experiment. -/
@[expose] noncomputable def programmedPreimageAdvantage [DecidableEq Domain]
    (adversary : ProgrammedPreimageAdversary
      (PK := PK) (Domain := Domain) (Range := Range)) :
    ℝ≥0∞ :=
  Pr[= true | programmedPreimageExp (psf := psf) (hr := hr) adversary]


end GPVHashAndSign
