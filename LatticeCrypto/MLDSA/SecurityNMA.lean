/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Security

/-!
# ML-DSA EUF-NMA Security: the MLWE key-swap hop (Lemma 7, Step 1)

This file builds the reduction infrastructure for the ML-DSA EUF-NMA security theorem
`MLDSA.nma_security` (issue #227, the real Dilithium Lemma 7), covering the **MLWE key-swap hop**
and the **SelfTargetMSIS extractor**:

1. **MLWE key-swap (`nma_keyswap_hop`).** Replace the honest key generation, where the public key
   vector is `t = Â · s₁ + s₂`, with a variant `keygen1` that samples `t` uniformly. The gap
   between the two EUF-NMA games equals the decisional MLWE advantage of the (seed-based)
   distinguisher `B = distinguisherB`. The `(Hadv)` and uniform-branch `(H1)` parts are fully
   proven; the real-branch `(H0)` reduces to a precise honest-sampling residue (`sorry`).
2. **SelfTargetMSIS extraction (`nmaAdvantage_keygen1_le_stmsis`).** Once `t` is uniform the key
   carries no secret, so a forgery is a short vector satisfying the SelfTargetMSIS relation; the
   extractor `extractorC` reads `(z, c̃)` out of the forged signature. The structural definitions
   are in place; the RO read-back identity is a precise `sorry`.

The `H₁` reprogramming step of the paper folds into the random-oracle modeling and is not separated
out here. `MLDSA.nma_security` itself keeps its existing `sorry` (the abstract-problem bridge is a
statement change flagged for owner negotiation; see the closing note).

## What is defined here

The honest ML-DSA key distribution embeds an MLWE instance: sample a public seed `ρ`, set the
public matrix `Â = ExpandA(ρ)`, sample short secrets `(s₁, s₂)`, and publish the `Power2Round`
high half of `t = Â · s₁ + s₂`. The uniform-`t` variant replaces `Â · s₁ + s₂` by a uniform
sample. We package both as `ProbComp` key generators, lift each to an EUF-NMA game over an
arbitrary forging adversary `main`, and exhibit the MLWE distinguisher `B` that interpolates
between them: `B (Â, t)` reconstructs the public key from `(ρ, t)` and runs the adversary.

## Modeling note (seeds, not matrices)

The verifier recomputes `Â = ExpandA(pk.ρ)` from the seed stored in the public key, so the MLWE
challenge matrix `Â` must be presented to the adversary *through* a seed `ρ`. Rather than carrying
an embedding witness `ExpandA(ρ) = Â` (which need not exist, since `ExpandA` is not surjective), we
**re-seed-base** the MLWE problem: the public challenge of `mldsaMLWE` is the *seed* `ρ` itself, and
the matrix is *defined* as `Â := ExpandA(ρ)` wherever it is used, so that
`noiseless s₁ ρ = ExpandA(ρ)·s₁`.
This is the standard ROM modeling of Dilithium with `ExpandA` a random oracle, and it makes the
distinguisher `B` total: it consumes `(ρ, t)` and forms `pk = (ρ, Power2Round(t).1)` directly with
no embedding. The `MlweEmbedding` record is therefore gone.
-/

open OracleComp OracleSpec ENNReal
open LatticeCrypto TransformOps

namespace MLDSA

namespace NMA

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High]

section KeyGen

variable [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]

/-- Build an ML-DSA public/secret key pair from the raw key material
`(ρ, ρ', key, s₁, s₂, t)`, splitting `t` via `Power2Round`. This is the common tail of both the
real and the uniform-`t` key generators: only the *distribution* of `t` differs between them.

When `t = ExpandA(ρ) · s₁ + s₂` this reproduces `keyGenFromSeed` (see `keyFromMaterial_eq`). -/
def keyFromMaterial (rho : Bytes 32) (key : Bytes 32)
    (s1 : RqVec p.l) (s2 : RqVec p.k) (t : RqVec p.k) :
    PublicKey p prims × SecretKey p :=
  let (t1, t0) := prims.power2RoundVec t
  let pk : PublicKey p prims := ⟨rho, t1⟩
  let tr := prims.hashPublicKey rho t1
  let sk : SecretKey p := ⟨rho, key, tr, s1, s2, t0⟩
  (pk, sk)

/-- **Game 0 key generation (real `t`).** Sample a seed, expand it into `(ρ, ρ', key)` and the
secrets `(s₁, s₂)`, then form the key from `t = ExpandA(ρ) · s₁ + s₂`. This is `keyGenFromSeed`
phrased as a `ProbComp` over the uniform seed distribution. -/
def keygen0 : ProbComp (PublicKey p prims × SecretKey p) := do
  let seed ← $ᵗ (Bytes 32)
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let (s1, s2) := prims.expandS rhoPrime
  let t := prims.expandA rho * s1 + s2
  return keyFromMaterial p prims rho key s1 s2 t

/-- **Game 1 key generation (uniform `t`).** Identical to `keygen0` except the public vector `t`
is sampled uniformly instead of being computed as `ExpandA(ρ) · s₁ + s₂`. This is the
intermediate game used in the first hop of Lemma 7. -/
def keygen1 : ProbComp (PublicKey p prims × SecretKey p) := do
  let seed ← $ᵗ (Bytes 32)
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let (s1, s2) := prims.expandS rhoPrime
  let t ← $ᵗ (RqVec p.k)
  return keyFromMaterial p prims rho key s1 s2 t

omit [DecidableEq prims.High] [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] in
/-- `keyFromMaterial` reproduces `keyGenFromSeed` on the honest material derived from a seed. -/
theorem keyFromMaterial_eq (seed : Bytes 32) :
    let (rho, rhoPrime, key) := prims.expandSeed seed
    let (s1, s2) := prims.expandS rhoPrime
    keyFromMaterial p prims rho key s1 s2 (prims.expandA rho * s1 + s2) =
      keyGenFromSeed p prims seed := by
  simp only [keyFromMaterial, keyGenFromSeed]

end KeyGen

section Game

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec]

/-- The EUF-NMA game over an arbitrary forging strategy `main` and an arbitrary key generator
`keygen`, observed through the Fiat-Shamir-with-aborts runtime. `main` receives the public key
(but no signing oracle) and returns a candidate `(message, signature)`; the game outputs the
validity bit of the forgery.

Specializing `keygen` to `keygen0` / `keygen1` gives the real / uniform-`t` NMA games whose gap
the MLWE hop bounds. The signature scheme is the same `FiatShamirWithAbort (identificationScheme …)`
used by `nma_security`, so `verify` recomputes `Â = ExpandA(pk.ρ)` from the published seed. -/
noncomputable def nmaGame
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    SPMF Bool :=
  (FiatShamirWithAbort.runtime (Commit := Commitment p prims)
    (Chal := CommitHashBytes p) M).evalDist do
      let (pk, _) ← (FiatShamirWithAbort.runtime (Commit := Commitment p prims)
        (Chal := CommitHashBytes p) M).liftProbComp keygen
      let (msg, σ) ← main pk
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ

/-- The advantage of the NMA game with key generator `keygen` is its `true`-probability. The hop
lemma below bounds `|nmaAdvantage keygen0 − nmaAdvantage keygen1|`. -/
noncomputable def nmaAdvantage
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) : ℝ≥0∞ :=
  Pr[= true | nmaGame p prims hr maxAttempts keygen main]

end Game

section Distinguisher

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (TqMatrix p.k p.l)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec]

/-- The random-oracle simulation implementation used by `FiatShamirWithAbort.runtime`: forward
`unifSpec` queries to fresh sampling and answer hash queries through a cached random oracle, all
inside `StateT QueryCache ProbComp`. Running an oracle computation through this implementation and
projecting away the final cache turns it into a plain `ProbComp`, which is what the MLWE
distinguisher must return. -/
noncomputable def roImpl :
    QueryImpl (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp) :=
  unifFwdImpl (M × Commitment p prims →ₒ CommitHashBytes p) +
    (randomOracle : QueryImpl (M × Commitment p prims →ₒ CommitHashBytes p)
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp))

/-- Observe an oracle computation as a plain `ProbComp` by simulating its random oracle from an
empty cache and discarding the final cache state. This is exactly the `ProbComp` underlying
`FiatShamirWithAbort.runtime.evalDist` (see `BundledSemantics.withStateOracle`), exposed so the
MLWE distinguisher — which must inhabit `… → ProbComp Bool` — can run the NMA game internally. -/
noncomputable def simulateToProbComp {α : Type}
    (mx : OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) α) :
    ProbComp α :=
  StateT.run' (simulateQ (roImpl p prims (M := M)) mx) ∅

/-- The concrete MLWE problem embedded by ML-DSA key generation, **seed-based**: the public
challenge is the public matrix seed `ρ = (ExpandSeed(seed)).1` for a uniform `seed`, the secret is
`s₁`, and the output is `t`. The matrix is recovered on demand as `Â := ExpandA(ρ)`, so
`noiseless s₁ ρ = ExpandA(ρ) · s₁`; the secret and error/uniform distributions are uniform.

Sampling `ρ` through `ExpandSeed` (rather than uniformly) makes the `ρ` marginal line up *exactly*
with `keygen0` / `keygen1`, so the uniform-branch identity `(H1)` against `keygen1` is a clean
monad-rewriting fact (no distributional assumption: `keygen1` discards the secret, and its `ρ` is
this same `(ExpandSeed seed).1`). What it does **not** reconcile is the *joint* law of `(ρ, s₁, s₂)`
in `keygen0`, where `(s₁, s₂) = ExpandS((ExpandSeed seed).2)` are derived from the *same* seed as
`ρ`, whereas the MLWE problem samples `s₁`/error independently of `ρ`; that joint independence is
the residual honest-sampling gap `(H0)` recorded below and folded into the ROM by the paper.

The matrix never appears as a free challenge: phrasing the MLWE instance over seeds is exactly the
ROM modeling of Dilithium with `ExpandA` a random oracle, and it makes the distinguisher `B` total
(no `ExpandA`-surjectivity assumption). The `nma_security` statement quantifies over an *abstract*
`mlwe` problem; relating that abstract problem to this concrete seed-based one is a deferred
statement-level obligation. -/
noncomputable def mldsaMLWE (p : Params) (prims : Primitives p)
    [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] :
    LearningWithErrors.Problem (Bytes 32) (RqVec p.l) (RqVec p.k) where
  sampleChallenge := do
    let seed ← $ᵗ (Bytes 32)
    return (prims.expandSeed seed).1
  sampleSecret := $ᵗ (RqVec p.l)
  sampleError := $ᵗ (RqVec p.k)
  noiseless := fun s1 rho => prims.expandA rho * s1
  sampleUniform := $ᵗ (RqVec p.k)

/-- **The MLWE distinguisher `B`.** Given a seed-based MLWE challenge `(ρ, t)` (real
`ExpandA(ρ)·s₁ + s₂` vs uniform `t`), `B` forms the ML-DSA public key `pk = (ρ, Power2Round(t).1)`
directly from the seed, runs the NMA forging strategy `main` on `pk`, simulates the random oracle
to verify the returned forgery, and outputs the validity bit as its decision.

When `(ρ, t)` is real, `B` reproduces `nmaGame … keygen0`; when `t` is uniform, it reproduces
`nmaGame … keygen1`. Thus `B`'s distinguishing advantage is exactly the NMA-game gap (the content
of `nma_keyswap_hop`). The seed-based phrasing means `B` needs no matrix-to-seed embedding. -/
noncomputable def distinguisherB
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    LearningWithErrors.Adversary (mldsaMLWE p prims) :=
  fun (challenge : Bytes 32 × RqVec p.k) =>
    let rho := challenge.1
    let t := challenge.2
    let pk : PublicKey p prims := ⟨rho, (prims.power2RoundVec t).1⟩
    simulateToProbComp p prims (M := M) do
      let (msg, σ) ← main pk
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ

end Distinguisher

section Hop

omit nttOps [DecidableEq prims.High] in
/-- **(Hadv) bias domination, in equality form.** For *any* LWE-style problem and decisional
adversary, the MLWE distinguishing advantage is exactly the Boolean distinguishing advantage between
the two single-branch games `game0` (real distribution) and `game1` (uniform distribution).

This unfolds `LearningWithErrors.experiment` — `b ← coin; sample ← if b then distr else uniform;
b' ← adv sample; return (b == b')` — into the hidden-bit guessing form
`z ← if b then (distr >>= adv) else (uniform >>= adv); pure (b == z)` and applies
`ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch`. It is fully generic and
discharges the (Hadv) obligation once the NMA games are identified with `game0`/`game1`. -/
theorem advantage_eq_game_boolDistAdvantage
    {Sample Secret Output : Type} [Add Output]
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (adv : LearningWithErrors.Adversary problem) :
    LearningWithErrors.advantage problem adv =
      (LearningWithErrors.game0 problem adv).boolDistAdvantage
        (LearningWithErrors.game1 problem adv) := by
  rw [LearningWithErrors.advantage]
  rw [show (LearningWithErrors.experiment problem adv) =
      (do
        let b ← ($ᵗ Bool)
        let z ← if b then LearningWithErrors.game0 problem adv
                      else LearningWithErrors.game1 problem adv
        pure (b == z)) by
    simp only [LearningWithErrors.experiment, LearningWithErrors.game0,
      LearningWithErrors.game1, bind_assoc]]
  exact ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch _ _

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (CommitHashBytes p)]

omit [SampleableType (RqVec p.k)] in
/-- **NMA-game / distinguisher plumbing.** Pushing the `keygen` sampling out of the
Fiat-Shamir-with-aborts runtime: the `Pr[= true]` of `nmaGame … keygen` equals the `Pr[= true]` of
first sampling `(pk, _) ← keygen` (in plain `ProbComp`) and then running the forge-and-verify tail
through `simulateToProbComp` — which is exactly the body of `distinguisherB` evaluated at `pk`.

This is the bundled-semantics fact `runtime.evalDist (liftM oa >>= rest) = 𝒟[oa] >>= …`
(`SPMFSemantics.withStateOracle` interpret/observe with `roSim.run'_liftM_bind`), specialised to
the ML-DSA NMA game; it reduces both (H0) and (H1) to comparing the *key distribution* against
`mldsaMLWE`'s `distr` / `uniformDistr`, with all the runtime plumbing already discharged. -/
theorem nmaGame_eq_keygen_bind
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    nmaGame p prims hr maxAttempts keygen main =
      𝒟[(do
        let (pk, _) ← keygen
        simulateToProbComp p prims (M := M) (do
          let (msg, σ) ← main pk
          (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
            pk msg σ))] := by
  classical
  let ro : QueryImpl (M × Commitment p prims →ₒ CommitHashBytes p)
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp) := randomOracle
  let impl : QueryImpl (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp) :=
    unifFwdImpl (M × Commitment p prims →ₒ CommitHashBytes p) + ro
  let rest : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) Bool := fun pk => do
    let (msg, σ) ← main pk
    (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ
  unfold nmaGame FiatShamirWithAbort.runtime ProbCompRuntime.evalDist
    ProbCompRuntime.liftProbComp SPMFSemantics.evalDist SemanticsVia.denote
  change 𝒟[(simulateQ impl (liftM keygen >>= fun pk => rest pk.1)).run' ∅] =
    𝒟[keygen >>= fun pk => simulateToProbComp p prims (rest pk.1)]
  rw [simulateQ_bind,
    roSim.run'_liftM_bind (ro := ro) (oa := keygen)
      (rest := fun pk => simulateQ impl (rest pk.1)) (s := ∅)]
  rw [evalDist_bind, evalDist_bind]
  simp only [simulateToProbComp, roImpl]
  rfl

/-- **The MLWE key-swap hop (Lemma 7, Step 1).** For every NMA forging strategy `main`, the gap
between the real-`t` and uniform-`t` EUF-NMA games is bounded by (in fact equal to) the decisional
MLWE advantage of the seed-based distinguisher `B`.

The proof factors through three facts:
- **(Hadv)** the MLWE advantage equals `(game0 B).boolDistAdvantage (game1 B)`
  (`advantage_eq_game_boolDistAdvantage`, fully proven and generic);
- **(H1)** `nmaGame … keygen1` and `game1 (mldsaMLWE) B` have equal `Pr[= true]`
  (proven below: both are the uniform-`t` game, and the `ρ` marginals coincide because
  `mldsaMLWE` samples `ρ` through the *same* `ExpandSeed` that `keygen1` uses, and `keygen1`'s
  secret is discarded);
- **(H0)** `nmaGame … keygen0` and `game0 (mldsaMLWE) B` have equal `Pr[= true]` — the residual
  honest-sampling assumption (the only `sorry`), see the inline comment for exactly what it needs.

This is the first of the three steps of `nma_security`; steps 2 and 3 (the `H₁` reprogramming and
the SelfTargetMSIS extraction) are handled elsewhere. The bound is stated on `toReal` because the
NMA advantages are `ℝ≥0∞` while MLWE advantage is `ℝ`. -/
theorem nma_keyswap_hop
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    |(nmaAdvantage p prims hr maxAttempts (keygen0 p prims) main).toReal -
        (nmaAdvantage p prims hr maxAttempts (keygen1 p prims) main).toReal| ≤
      LearningWithErrors.advantage (mldsaMLWE p prims)
        (distinguisherB p prims hr maxAttempts main) := by
  set B := distinguisherB p prims hr maxAttempts main (M := M) with hB
  -- (Hadv): the MLWE advantage is exactly the gap between the two single-branch games.
  apply le_of_eq
  rw [advantage_eq_game_boolDistAdvantage (mldsaMLWE p prims) B,
    ProbComp.boolDistAdvantage, nmaAdvantage, nmaAdvantage]
  -- It now suffices to identify `Pr[= true]` of each NMA game with the matching MLWE game.
  -- (H0) real branch and (H1) uniform branch.
  have hH1 : Pr[= true | nmaGame p prims hr maxAttempts (keygen1 p prims) main] =
      Pr[= true | LearningWithErrors.game1 (mldsaMLWE p prims) B] := by
    -- (H1) uniform-branch identity. Both games sample `t` uniformly and discard `keygen1`'s
    -- secret `(s₁, s₂)`; the public key reduces to `⟨(ExpandSeed seed).1, Power2Round(t).1⟩`,
    -- which is exactly what `game1 = uniformDistr >>= B` builds (its challenge `ρ` is sampled
    -- through the *same* `ExpandSeed seed`, see `mldsaMLWE.sampleChallenge`). This is a pure
    -- monad-rewriting identity once `nmaGame`/`liftProbComp` and `simulateToProbComp` are
    -- recognised as the same `withStateOracle` semantics; no distributional assumption.
    rw [nmaGame_eq_keygen_bind]
    simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr, hB, distinguisherB,
      mldsaMLWE, keygen1, keyFromMaterial, bind_assoc, pure_bind]
    rw [probOutput_def, probOutput_def, SPMF.evalDist_def]
  have hH0 : Pr[= true | nmaGame p prims hr maxAttempts (keygen0 p prims) main] =
      Pr[= true | LearningWithErrors.game0 (mldsaMLWE p prims) B] := by
    -- (H0) real-branch identity — THE residual honest-sampling assumption.
    -- `nmaGame … keygen0` samples one `seed ← $ᵗ Bytes 32`, derives `ρ := (ExpandSeed seed).1`,
    -- `(s₁, s₂) := ExpandS (ExpandSeed seed).2`, and sets `t := ExpandA(ρ)·s₁ + s₂`.
    -- `game0 = distr >>= B` instead samples `ρ` through `ExpandSeed` but `s₁ ← $ᵗ RqVec l`,
    -- `s₂ ← $ᵗ RqVec k` *independently* of `ρ` and of each other, with `t := ExpandA(ρ)·s₁ + s₂`.
    -- These agree on `Pr[= true]` iff the joint law of `(ρ, s₁, s₂)` produced by
    -- `ExpandSeed`/`ExpandS` from one uniform `seed` equals the product law
    -- `((ExpandSeed (·)).1 of uniform seed) ⊗ Uniform(RqVec l) ⊗ Uniform(RqVec k)`.
    -- This is the ML-DSA *honest sampling assumption* (`ExpandSeed`/`ExpandS` modeled as
    -- independent uniform samplers in the ROM); it is NOT derivable from the deterministic
    -- `prims` and must enter as an added hypothesis on `prims` (or be supplied by the ROM
    -- modeling of `ExpandSeed`/`ExpandA`). See obligation (1) in the closing note.
    rw [nmaGame_eq_keygen_bind]
    simp only [LearningWithErrors.game0, LearningWithErrors.distr, hB, distinguisherB,
      mldsaMLWE, keygen0, keyFromMaterial, bind_assoc, pure_bind]
    rw [probOutput_def, probOutput_def, SPMF.evalDist_def]
    -- After the runtime plumbing the goal is purely about the *key distribution*:
    --   LHS: `seed ← $ᵗ; t := ExpandA((ExpandSeed seed).1)·(ExpandS (ExpandSeed seed).2).1
    --           + (ExpandS (ExpandSeed seed).2).2; run B-tail on pk(seed, t)`
    --   RHS: `seed ← $ᵗ; s₁ ← $ᵗ; s₂ ← $ᵗ; t := ExpandA((ExpandSeed seed).1)·s₁ + s₂;
    --           run B-tail on pk(seed, t)`.
    -- These coincide exactly when `(s₁, s₂) = ExpandS (ExpandSeed seed).2` is, jointly over a
    -- uniform `seed`, distributed as an *independent* `Uniform(RqVec l) × Uniform(RqVec k)`
    -- (and independent of `(ExpandSeed seed).1`). That is the ML-DSA honest-sampling assumption
    -- on `ExpandSeed`/`ExpandS`, not derivable from the deterministic `prims`; see obligation (1).
    sorry
  -- The hop is in fact an *equality* modulo (H0)/(H1): after rewriting both NMA games into the
  -- matching MLWE games the bound becomes `|x - y| = |x - y|`, closed by reflexivity.
  rw [hH0, hH1]

end Hop

section Extractor

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (CommitHashBytes p)]

/-- The concrete SelfTargetMSIS problem embedded by ML-DSA verification (Lemma 7, Step 3).

After the key has uniform `t` (`keygen1`), a forgery `(msg, some (w', (z, h)))` accepted by
`verify` is, via the random oracle answer `c̃ = H(msg, w')`, a SelfTargetMSIS solution: the matrix
`Â = ExpandA(ρ)` is the challenge, the public key `pk` is the target, the hash input is `(msg, w')`,
and the response is `(z, h)`. Validity recomputes the commitment from `(pk, c̃, (z, h))` via
`UseHint ∘ computeWApprox` (commitment recoverability) and runs the identification-scheme verifier;
this is precisely the equation `verify` checks, so an accepted forgery maps to a valid STMSIS
solution.

The `sampleParams` draws the same seed-based key as `keygen1`/`mldsaMLWE`: it samples `ρ` through
`ExpandSeed`, a uniform `t`, and publishes `(ExpandA(ρ), pk)` with `pk = ⟨ρ, Power2Round(t).1⟩`. -/
noncomputable def mldsaSTMSIS (M : Type) :
    SelfTargetMSIS.Problem (TqMatrix p.k p.l) (Response p prims) (PublicKey p prims)
      (M × Commitment p prims) (CommitHashBytes p) where
  sampleParams := do
    let (pk, _) ← keygen1 p prims
    return (prims.expandA pk.rho, pk)
  isValid := fun aHat pk cTilde (z, h) =>
    -- Recover the commitment `w'` from `(pk, c̃, (z, h))` and run the identification verifier.
    let w' := prims.useHintVec h (computeWApprox p prims aHat (prims.sampleInBall cTilde) z pk.t1)
    (identificationScheme p prims).verify pk w' cTilde (z, h)

/-- **The SelfTargetMSIS extractor `C` (Lemma 7, Step 3).**

`C` runs the NMA forger `main` on the public key `pk` (the STMSIS target). The forger interacts with
the random oracle `H : (M × Commitment) →ₒ CommitHashBytes`. On a forgery `(msg, some (w', (z, h)))`
`C` outputs the STMSIS preimage `(msg, w')` together with the response `(z, h)`. An aborting forgery
`(msg, none)` is mapped to a dummy preimage with a zeroed response, which the STMSIS RO-consistency
check rejects. The matrix in `params.1` is ignored by `C` (it equals `ExpandA(params.2.ρ)`).

The STMSIS experiment then looks up `c̃ = H(msg, w')` in the oracle cache and checks
`mldsaSTMSIS.isValid Â pk c̃ (z, h)`, which recomputes `w'` from `(pk, c̃, (z, h))` and runs the
identification verifier — exactly what the NMA `verify` does after querying `H(msg, w')`. -/
noncomputable def extractorC [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    SelfTargetMSIS.Adversary (mldsaSTMSIS p prims M) where
  run := fun (params : TqMatrix p.k p.l × PublicKey p prims) => do
    let pk := params.2
    let (msg, σ) ← main pk
    match σ with
    | some (w', (z, h)) =>
      -- Force the RO answer `H(msg, w')` to be cached (the STMSIS experiment reads it back), then
      -- return the SelfTargetMSIS preimage/response.
      let _c ← HasQuery.query (spec := (M × Commitment p prims →ₒ CommitHashBytes p)) (msg, w')
      return ((msg, w'), (z, h))
    | none =>
      -- Aborting forgery: no valid preimage. Emit a dummy that fails RO consistency / `isValid`.
      return ((msg, default), default)

/-- **The SelfTargetMSIS extraction bound (Lemma 7, Step 3).** The uniform-`t` EUF-NMA advantage is
bounded by the SelfTargetMSIS advantage of the extractor `C`.

A forgery accepted by the NMA game (after the `H(msg, w')` query inside `verify`) is exactly a valid
SelfTargetMSIS solution for `mldsaSTMSIS`: `C` reproduces the forger's oracle trace, the
experiment's RO-consistency lookup recovers the same `c̃ = H(msg, w')`, `isValid` recovers `w'` and
runs the identical verifier. The remaining `sorry` is the distributional identity between the two
RO-threaded experiments (the same `withStateOracle` plumbing as `nmaGame_eq_keygen_bind`, now with a
cache read-back), plus the bookkeeping that an accepted NMA forgery is necessarily non-aborting and
hence routed to the `some` branch of `C`. -/
theorem nmaAdvantage_keygen1_le_stmsis
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    nmaAdvantage p prims hr maxAttempts (keygen1 p prims) main ≤
      SelfTargetMSIS.advantage (extractorC p prims main) := by
  -- Both `Pr[= true]`s reduce, through the shared `withStateOracle` random-oracle semantics, to:
  --   sample the uniform-`t` key `(pk, _)`; run `main pk` against the RO; on `some (w', (z,h))`
  --   read `c̃ = H(msg, w')` from the cache and accept iff `ids.verify pk w' c̃ (z,h)`.
  -- The NMA game performs exactly this (its `verify` queries `H(msg, w')` then runs `ids.verify`);
  -- the STMSIS experiment performs exactly this (its RO-consistency lookup yields `c̃`, and
  -- `mldsaSTMSIS.isValid` recovers `w'` from `(pk, c̃, (z,h))` and runs `ids.verify`).  Equating
  -- the two requires the bundled-semantics rewrite plus commitment-recoverability of `w'`; both
  -- ingredients exist (`roSim.run'_liftM_bind`, `idsWithAbort_commitment_recoverable`) but the
  -- read-back-of-the-cached-answer step is not yet packaged as a lemma.  Left as a precise sorry.
  sorry

end Extractor

end NMA

/-! ## Remaining obligations (Phase 2)

**Re-seed-base done (Phase 2A).** `MlweEmbedding` is gone: `mldsaMLWE` is now phrased over the
public *seed* `ρ` (sampled through `ExpandSeed`), with the matrix defined on demand as
`ExpandA(ρ)`; `distinguisherB` consumes `(ρ, t)` directly and is total. **`(Hadv)` and `(H1)` are
fully proven**, axiom-clean (`advantage_eq_game_boolDistAdvantage`, the `hH1` branch of
`nma_keyswap_hop`, via the runtime-plumbing lemma `nmaGame_eq_keygen_bind`). Two precise `sorry`s
and one statement-level bridge remain:

1. **`(H0)` real-branch identity (`nma_keyswap_hop`, one `sorry`).** After the runtime plumbing and
   `simp` the goal is the *pure key-distribution identity*
   `𝒟[seed ← $ᵗ; run B-tail on pk(seed, ExpandA(ρ)·(ExpandS ρ').1 + (ExpandS ρ').2)] =
    𝒟[seed ← $ᵗ; s₁ ← $ᵗ; s₂ ← $ᵗ; run B-tail on pk(seed, ExpandA(ρ)·s₁ + s₂)]`
   (with `ρ = (ExpandSeed seed).1`, `ρ' = (ExpandSeed seed).2`). It holds iff
   `(s₁, s₂) = ExpandS (ExpandSeed seed).2` is, over a uniform `seed`, jointly distributed as
   `Uniform(RqVec l) × Uniform(RqVec k)` independently of `ρ`. This is the ML-DSA **honest-sampling
   assumption**; it is NOT derivable from the deterministic `prims` and must enter as an added
   hypothesis on `prims` (or be supplied by modeling `ExpandSeed`/`ExpandS`/`ExpandA` as random
   oracles). **Difficulty: requires a statement-level hypothesis; the Lean residue is then short.**

2. **STMSIS extraction identity (`nmaAdvantage_keygen1_le_stmsis`, one `sorry`).** Both
   `Pr[= true]`s reduce, through the shared `withStateOracle` semantics, to: sample the uniform-`t`
   key, run `main` against the RO, and on `some (w', (z,h))` read `c̃ = H(msg, w')` from the cache
   and accept iff `ids.verify pk w' c̃ (z,h)`. The NMA `verify` does exactly this; the STMSIS
   experiment does exactly this (`mldsaSTMSIS.isValid` recovers `w'` from `(pk, c̃, (z,h))` via
   commitment recoverability — see `MLDSA.idsWithAbort_commitment_recoverable` — and runs the same
   verifier). The residue needs (a) the cache-read-back analogue of `nmaGame_eq_keygen_bind`
   (package the `withStateOracle` rewrite when the experiment *reads* the final cache, cf.
   `SelfTargetMSIS.experiment`), and (b) the bookkeeping that an accepted NMA forgery is
   non-aborting (routed to the `some` branch of `extractorC`). **Difficulty: medium-high**, all
   ingredients exist but the read-back plumbing is not yet a lemma.

3. **Bridge to the abstract `mlwe`/`stmsis`/`hr` of `nma_security` (statement-level, NOT made
   here).** `nma_security` quantifies over an *abstract* `mlwe`, an *abstract* `stmsis`, and an
   *abstract* `hr : GenerableRelation …` whose `gen` need not be ML-DSA keygen. The work here is
   against the *concrete* `mldsaMLWE` / `mldsaSTMSIS` and `keygen0/1`. Wiring requires added
   hypotheses to `nma_security`: at least `hr.gen = keygen0 p prims` (the FS scheme is instantiated
   with the real ML-DSA keygen), `mlwe = mldsaMLWE p prims` (or an advantage inequality), and
   `stmsis = mldsaSTMSIS p prims M` (or an advantage inequality). These are **statement changes to
   `nma_security` flagged for owner negotiation in Phase 3** — they are not made in this file, and
   `nma_security` keeps its `sorry`.

**Phase 3 plan.** (i) Negotiate the item-3 bridge hypotheses with the owner; (ii) discharge (H0)
under the honest-sampling hypothesis from item 1; (iii) finish the STMSIS read-back lemma for
item 2; (iv) assemble `nma_security` as `keyswap_hop` (MLWE) + `keygen1_le_stmsis` (STMSIS) via the
triangle/`probOutput_true_le_add_ofReal_boolDistAdvantage` bound.
-/

end MLDSA
