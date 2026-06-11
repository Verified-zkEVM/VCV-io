/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Security

/-!
# ML-DSA EUF-NMA Security: the MLWE key-swap hop (Lemma 7, Step 1)

This file is **Phase 1 scaffolding** for the ML-DSA EUF-NMA security theorem
`MLDSA.nma_security` (issue #227, the real Dilithium Lemma 7). It isolates the **first of
the three proof steps** of the paper:

1. *(this file)* replace the honest key generation, where the public key vector is
   `t = Â · s₁ + s₂`, with a variant `keygen1` that samples `t` uniformly. The probability
   gap between the two EUF-NMA games is bounded by the decisional MLWE advantage of an
   explicit distinguisher `B`.
2. reprogram `H₁(w₁, m) := G(shift_α(w₁), m)` — no loss because `shift_α` is injective.
3. extract a SelfTargetMSIS solution from a forgery — gap `Adv^STMSIS(C)`.

Steps 2 and 3 are **out of scope**; `MLDSA.nma_security` itself keeps its existing `sorry`.

## What is defined here

The honest ML-DSA key distribution embeds an MLWE instance: sample a public seed `ρ`, set the
public matrix `Â = ExpandA(ρ)`, sample short secrets `(s₁, s₂)`, and publish the `Power2Round`
high half of `t = Â · s₁ + s₂`. The uniform-`t` variant replaces `Â · s₁ + s₂` by a uniform
sample. We package both as `ProbComp` key generators, lift each to an EUF-NMA game over an
arbitrary forging adversary `main`, and exhibit the MLWE distinguisher `B` that interpolates
between them: `B (Â, t)` reconstructs the public key from `(ρ, t)` and runs the adversary.

## Modeling note (the `ρ ↔ Â` bridge)

The verifier recomputes `Â = ExpandA(pk.ρ)` from the seed stored in the public key, so the MLWE
challenge matrix `Â` must be presented to the adversary *through* a seed `ρ`. We therefore work
with an `MlweEmbedding` record that carries both a seed `ρ` and the witness that
`ExpandA(ρ) = Â`. In the standard ROM modeling of Dilithium, `ExpandA` is a random oracle and
this embedding is exactly the MLWE-with-`ExpandA` instance; making that precise is one of the
remaining obligations recorded below.
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

/-- An embedding of an MLWE challenge matrix `Â` into an ML-DSA public seed: a seed `ρ` together
with the proof that `ExpandA(ρ) = Â`. The MLWE distinguisher needs such an embedding to present
the challenge matrix to the NMA adversary, because the public key only carries the seed `ρ` and
the verifier recomputes `Â = ExpandA(ρ)`.

In the ROM modeling of Dilithium `ExpandA` is a random oracle, so the MLWE instance is naturally
phrased over seeds and this embedding is the identity. Supplying it generically is one of the
deferred obligations (see the `## Remaining obligations` note at the end of the file). -/
structure MlweEmbedding (aHat : TqMatrix p.k p.l) where
  /-- A public seed reproducing the challenge matrix. -/
  rho : Bytes 32
  /-- The expansion identity `ExpandA(ρ) = Â`. -/
  expandA_rho : prims.expandA rho = aHat

/-- The concrete MLWE problem embedded by ML-DSA key generation: the public matrix `Â`, secret
`s₁`, output `t`, with `noiseless s₁ Â = Â · s₁` and uniform challenge/secret/error/uniform
distributions matching `keygen0` / `keygen1`. The `nma_security` statement quantifies over an
*abstract* `mlwe` problem; relating that abstract problem to this concrete one is one of the
deferred obligations. -/
noncomputable def mldsaMLWE (p : Params)
    [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
    [SampleableType (TqMatrix p.k p.l)] :
    LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k) where
  sampleChallenge := $ᵗ (TqMatrix p.k p.l)
  sampleSecret := $ᵗ (RqVec p.l)
  sampleError := $ᵗ (RqVec p.k)
  noiseless := fun s1 aHat => aHat * s1
  sampleUniform := $ᵗ (RqVec p.k)

/-- **The MLWE distinguisher `B`.** Given an MLWE challenge `(Â, t)` (real `Â·s₁ + s₂` vs uniform
`t`) and an embedding of every matrix `Â` into a public seed `ρ`, `B` forms the ML-DSA public key
`pk = (ρ, Power2Round(t).1)`, runs the NMA forging strategy `main` on `pk`, simulates the random
oracle to verify the returned forgery, and outputs the validity bit as its decision.

When `(Â, t)` is real, `B` reproduces `nmaGame … keygen0`; when `t` is uniform, it reproduces
`nmaGame … keygen1` (up to the `ρ ↔ Â` embedding). Thus `B`'s distinguishing advantage is exactly
the NMA-game gap (the content of `nma_keyswap_hop`). -/
noncomputable def distinguisherB
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims)))
    (embed : (aHat : TqMatrix p.k p.l) → MlweEmbedding p prims aHat) :
    LearningWithErrors.Adversary (mldsaMLWE p) :=
  fun (challenge : TqMatrix p.k p.l × RqVec p.k) =>
    let aHat := challenge.1
    let t := challenge.2
    let pk : PublicKey p prims := ⟨(embed aHat).rho, (prims.power2RoundVec t).1⟩
    simulateToProbComp p prims (M := M) do
      let (msg, σ) ← main pk
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ

end Distinguisher

section Hop

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (TqMatrix p.k p.l)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec]

/-- **The MLWE key-swap hop (Lemma 7, Step 1).** For every NMA forging strategy `main` and every
matrix-to-seed embedding `embed`, the gap between the real-`t` and uniform-`t` EUF-NMA games is
bounded by the decisional MLWE advantage of the distinguisher `B`.

This is the first of the three steps of `nma_security`; steps 2 and 3 (the `H₁` reprogramming and
the SelfTargetMSIS extraction) are handled elsewhere. The bound is stated on `toReal` because the
NMA advantages are `ℝ≥0∞` while MLWE advantage is `ℝ`. -/
theorem nma_keyswap_hop
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims)))
    (embed : (aHat : TqMatrix p.k p.l) → MlweEmbedding p prims aHat) :
    |(nmaAdvantage p prims hr maxAttempts (keygen0 p prims) main).toReal -
        (nmaAdvantage p prims hr maxAttempts (keygen1 p prims) main).toReal| ≤
      LearningWithErrors.advantage (mldsaMLWE p)
        (distinguisherB p prims hr maxAttempts main embed) := by
  -- The proof factors into three distributional equalities, each isolated as a `sorry` below:
  --  (H0) `nmaGame … keygen0` equals `game0 (mldsaMLWE) B` (real branch of the MLWE experiment),
  --  (H1) `nmaGame … keygen1` equals `game1 (mldsaMLWE) B` (uniform branch),
  --  (Hadv) `boolBiasAdvantage` of the MLWE experiment dominates `|game0.true − game1.true|`.
  -- Each requires nontrivial monad-rewriting plumbing that the abstract `embed`/`hr` make
  -- subtle; see the file-level `## Remaining obligations` note.
  sorry

end Hop

end NMA

/-! ## Remaining obligations (Phase 1)

The scaffold above is `sorry`-free except for the single distributional `sorry` inside
`NMA.nma_keyswap_hop`. Closing it — and wiring the result into `nma_security` — requires:

1. **`(H0)` real-branch identity.** `nmaGame … (keygen0)` equals
   `LearningWithErrors.game0 (mldsaMLWE) B` for `B = distinguisherB … embed`. This is a
   monad-rewriting fact: unfold `keygen0` (seed → `(ρ, s₁, s₂)`, `t = Â·s₁+s₂`), recognise
   `Â = ExpandA(ρ)` via `embed`, and match it against `mldsaMLWE.distr` followed by `B`. The
   `embed`/`expandSeed` plumbing makes the matrix and the secrets jointly sampled in `keygen0`
   but independently in `distr`; reconciling the two distributions is the crux. **Difficulty:
   high** (multi-day): needs a precise characterisation of how `ExpandS ∘ expandSeed` and
   `ExpandA ∘ (expandSeed).1` sample `(Â, s₁, s₂)`, i.e. the *honest sampling assumption* that
   the paper folds into the ROM. It almost certainly needs an added hypothesis (see item 4).

2. **`(H1)` uniform-branch identity.** `nmaGame … (keygen1)` equals
   `LearningWithErrors.game1 (mldsaMLWE) B`. Easier than `(H0)` because both sample `t`
   uniformly and independently of `(Â, s₁, s₂)`; still needs the `embed` reconciliation for the
   matrix. **Difficulty: medium.**

3. **`(Hadv)` bias domination.** From `(H0)`/`(H1)`,
   `|game0.true − game1.true| ≤ experiment.boolBiasAdvantage`. Use
   `SPMF.boolBiasAdvantage_eq_boolDistAdvantage_coin_branch` (or its `ProbComp` analogue) plus
   `ProbComp.boolDistAdvantage_*`. **Difficulty: low–medium**, mostly mechanical once the games
   are identified as the two branches of `experiment`.

4. **`mldsaMLWE` ↔ the abstract `mlwe` of `nma_security`.** `nma_security` quantifies over an
   *abstract* `mlwe : LearningWithErrors.Problem …` and an *abstract*
   `hr : GenerableRelation …` whose `gen` need not be `keyGenFromSeed`. The hop here is proven
   against the *concrete* `mldsaMLWE` and `keygen0 = keyGenFromSeed`. Bridging requires either
   (a) a hypothesis `hr.gen = keygen0` (the FS scheme is instantiated with the ML-DSA keygen),
   and (b) a hypothesis relating `mldsaMLWE` to `mlwe` (e.g. `mlwe = mldsaMLWE`, or an advantage
   inequality). **These are statement-level facts not currently available**; `nma_security`'s
   hypotheses are *insufficient* to connect its abstract `mlwe`/`hr` to ML-DSA keygen without an
   added bridge hypothesis. This is flagged, not silently patched.

5. **`MlweEmbedding` existence.** `distinguisherB` consumes a total `embed` producing, for every
   `Â`, a seed `ρ` with `ExpandA(ρ) = Â`. `ExpandA` is not surjective in general, so such an
   `embed` does *not* exist for the deterministic `expandA`. The honest fix is the ROM modeling:
   state MLWE over seeds with `ExpandA` a random oracle, making the matrix *defined as*
   `ExpandA(ρ)` for the sampled `ρ`. Phase 2 should reshape `mldsaMLWE`/`distinguisherB` to
   sample `ρ` (not `Â`) and set `Â := ExpandA(ρ)`, eliminating `MlweEmbedding` entirely.

The concrete next step is item 5 (re-seed-base the MLWE problem), which then makes items 1–2
tractable, followed by item 4 as an explicit added hypothesis to `nma_security` (a statement
change to negotiate with the maintainers).
-/

end MLDSA
