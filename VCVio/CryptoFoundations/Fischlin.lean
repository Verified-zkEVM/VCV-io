/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.Coercions.Add
import Mathlib.Data.FinEnum
import Mathlib.Data.Nat.Choose.Basic

/-!
# Fischlin Transform

This file defines the Fischlin transform (CRYPTO 2005), which converts a Σ-protocol
into a signature scheme (non-interactive proof of knowledge) in the random oracle model
with *online (straight-line) extraction*.

Unlike the Fiat-Shamir transform, which requires a rewinding extractor (via the forking lemma),
the Fischlin transform enables extraction by simply observing the prover's hash queries.
This comes at the cost of a more complex prover that performs a "proof-of-work" search
over the challenge space, and a slight completeness error.

## Parameters

* `ρ` — number of parallel repetitions
* `b` — hash output bit-length (random oracle range is `Fin (2^b)`)
* `S` — maximum allowed sum of hash values in a valid proof (paper notation)

## References

* Marc Fischlin, "Communication-Efficient Non-Interactive Proofs of Knowledge
  with Online Extractors", CRYPTO 2005.
-/

universe u v

open OracleComp OracleSpec

/-! ## Type Definitions -/

/-- Input to the Fischlin random oracle. Defined as a structure rather than a nested product
to give fast `DecidableEq` synthesis (avoiding deep product-type unfolding). -/
structure FischlinROInput (X PC Ω P : Type) (ρ : ℕ) (M : Type) where
  stmt : X
  msg : M
  comList : List PC
  rep : Fin ρ
  chal : Ω
  resp : P
  deriving DecidableEq

variable (X PC Ω P : Type) (ρ b : ℕ) (M : Type) in
/-- The random oracle specification for the Fischlin transform.
Domain: `FischlinROInput` (statement, message, commitment list, index, challenge, response).
Range: `Fin (2^b)` (b-bit hash values). -/
abbrev fischlinROSpec :=
  FischlinROInput X PC Ω P ρ M →ₒ Fin (2 ^ b)

variable (PC Ω P : Type) (ρ : ℕ) in
/-- A Fischlin proof consists of one `(commitment, challenge, response)` triple
per parallel repetition. -/
abbrev FischlinProof := Fin ρ → PC × Ω × P

/-! ## Prover Search -/

/-- Recursive search over a list of challenges for one Fischlin repetition.

For each challenge `ω`, computes the sigma protocol response and queries the hash oracle.
Exits early if a hash value of `0` is found (the ideal "proof of work" result).
Otherwise, tracks the `(challenge, response)` pair with the minimal hash value.

This models the sequential search in Construction 1 of the Fischlin paper:
the prover queries `H` on each input and keeps the best. -/
private def fischlinSearchAux {X W PC SC Ω P M : Type} {p : X → W → Bool} {ρ b : ℕ}
    (σ : SigmaProtocol X W PC SC Ω P p)
    (pk : X) (sk : W) (sc : SC) (msg : M) (comList : List PC) (i : Fin ρ)
    : List Ω → Option (Ω × P × Fin (2 ^ b)) →
      OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M) (Option (Ω × P))
  | [], best => return best.map fun (ω, resp, _) => (ω, resp)
  | ω :: rest, best => do
    let resp ← σ.respond pk sk sc ω
    let h ← query (spec := unifSpec + fischlinROSpec X PC Ω P ρ b M)
      (Sum.inr ⟨pk, msg, comList, i, ω, resp⟩)
    if h.val = 0 then return some (ω, resp)
    else
      let newBest := match best with
        | none => some (ω, resp, h)
        | some (ω', resp', h') =>
          if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h')
      fischlinSearchAux σ pk sk sc msg comList i rest newBest

/-! ## Main Definition -/

variable {X W PC SC Ω P : Type}
    {p : X → W → Bool} [SampleableType X] [SampleableType W]
    [DecidableEq X] [DecidableEq PC] [DecidableEq Ω] [DecidableEq P]
    [FinEnum Ω] [Inhabited Ω] [Inhabited P] [SampleableType Ω]

/-- The Fischlin transform applied to a Σ-protocol and a generable relation produces
a signature scheme in the random oracle model.

**Signing**: generates `ρ` independent commitments, then for each repetition searches
through all challenges `ω ∈ Ω` (via `FinEnum.toList`) to find the `(ω, response)` pair
whose hash value is minimal, exiting early at hash `0`.

**Verification**: re-hashes each `(commitment, challenge, response)` triple, checks
sigma-protocol verification for each repetition, and verifies that the sum of hash
values is at most `S`. -/
def Fischlin (σ : SigmaProtocol X W PC SC Ω P p)
    (hr : GenerableRelation X W p) (ρ b S : ℕ) (M : Type)
    [DecidableEq M] :
    SignatureAlg (OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M))
      (M := M) (PK := X) (SK := W) (S := FischlinProof PC Ω P ρ) where
  keygen := hr.gen
  sign := fun pk sk msg => do
    let commits ← Fin.mOfFn ρ fun _ => σ.commit pk sk
    let comVec : Fin ρ → PC := fun i => (commits i).1
    let comList := List.ofFn comVec
    Fin.mOfFn ρ fun i => do
      let sc_i := (commits i).2
      let result ← fischlinSearchAux σ pk sk sc_i msg comList i
        (FinEnum.toList Ω) none
      match result with
      | some (ω, resp) => return (comVec i, ω, resp)
      | none => return (comVec i, default, default)
  verify := fun pk msg π => do
    let comVec : Fin ρ → PC := fun i => (π i).1
    let comList := List.ofFn comVec
    let results ← Fin.mOfFn ρ fun i => do
      let (_, ω_i, resp_i) := π i
      let h_i ← query (spec := unifSpec + fischlinROSpec X PC Ω P ρ b M)
        (Sum.inr ⟨pk, msg, comList, i, ω_i, resp_i⟩)
      return (σ.verify pk (comVec i) ω_i resp_i, h_i.val)
    let allVerified := (List.finRange ρ).all fun i => (results i).1
    let hashSum := (List.finRange ρ).foldl (fun acc i => acc + (results i).2) 0
    return (allVerified && decide (hashSum ≤ S))
  exec comp :=
    let roSpec := fischlinROSpec X PC Ω P ρ b M
    let ro : QueryImpl roSpec (StateT roSpec.QueryCache ProbComp) := randomOracle
    let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT roSpec.QueryCache ProbComp)
    StateT.run' (simulateQ (idImpl + ro) comp) ∅
  lift_probComp := monadLift
  exec_lift_probComp c := by
    sorry

namespace Fischlin

variable {X W PC SC Ω P : Type} {p : X → W → Bool}
  [SampleableType X] [SampleableType W]
  [DecidableEq X] [DecidableEq PC] [DecidableEq Ω] [DecidableEq P]
  [FinEnum Ω] [Inhabited Ω] [Inhabited P] [SampleableType Ω]

variable (σ : SigmaProtocol X W PC SC Ω P p) (hr : GenerableRelation X W p)
  (ρ b S : ℕ) (M : Type) [DecidableEq M]

open ENNReal

/-! ### Completeness -/

/-- Completeness error bound for the Fischlin transform (Fischlin 2005, Lemma 1).

Given `ρ` repetitions, `b`-bit hashes, max sum `S`, and challenge space size `t`:
the error is `ρ · ((2^b - ⌊S/ρ⌋ - 1) / 2^b)^t`.

Derivation: by a union/pigeonhole bound over repetitions, if the sum of minimum
hash values exceeds `S`, at least one minimum exceeds `⌊S/ρ⌋`. The probability
that the minimum of `t` independent uniform samples from `Fin (2^b)` exceeds `k`
is `((2^b - k - 1) / 2^b)^t`.

For `S = 0` this simplifies to `ρ · ((2^b - 1) / 2^b)^t`. -/
noncomputable def completenessError (ρ b S t : ℕ) : ℝ≥0∞ :=
  (ρ : ℝ≥0∞) * ((↑(2 ^ b - (S / ρ + 1)) : ℝ≥0∞) / ↑(2 ^ b)) ^ t

/-- Almost completeness of the Fischlin transform: if the underlying Σ-protocol is
perfectly complete, then the signature scheme verifies with probability at least
`1 - completenessError ρ b S t` where `t = FinEnum.card Ω` is the challenge space size.

Unlike the Fiat-Shamir transform (which is perfectly complete), the Fischlin transform
has a non-zero completeness error because the prover's proof-of-work search may fail
to find hash values whose sum is at most `S`. -/
theorem almostComplete (hc : σ.PerfectlyComplete) (msg : M) :
    Pr[= true | (Fischlin σ hr ρ b S M).exec do
      let (pk, sk) ← (Fischlin σ hr ρ b S M).keygen
      let sig ← (Fischlin σ hr ρ b S M).sign pk sk msg
      (Fischlin σ hr ρ b S M).verify pk msg sig]
    ≥ 1 - completenessError ρ b S (FinEnum.card Ω) := by sorry

/-! ### Online Extraction / Knowledge Soundness -/

/-- A cheating prover (knowledge soundness adversary) for the Fischlin transform.
The adversary receives a statement and message, has access to both the random oracle
and internal randomness (`unifSpec`), and attempts to produce a valid Fischlin proof
without knowing the witness.

The Σ-protocol `σ` is not referenced in the structure itself (only in the
extraction and verification steps of the experiment), so it enters the
theorem statements via hypotheses like `σ.SpeciallySound`. -/
structure KnowledgeSoundnessAdv where
  run : X → M → OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M)
    (FischlinProof PC Ω P ρ)

/-- Online extractor for the Fischlin transform (Fischlin 2005, Construction 2).

Given statement `x`, a proof `π`, and the log of all hash oracle queries made by
the prover, the extractor searches for two accepting transcripts at the same
commitment with different challenges, then invokes the Σ-protocol's `extract`
function. Returns `none` if no such collision is found in the log.

The key property enabling this extractor is `UniqueResponses`: given the same
`(statement, commitment, challenge)`, there is at most one valid response.
So finding a second valid query at a different challenge gives a proper
input pair for the Σ-protocol extractor. -/
noncomputable def onlineExtract
    (x : X) (π : FischlinProof PC Ω P ρ)
    (log : QueryLog (fischlinROSpec X PC Ω P ρ b M)) : ProbComp (Option W) :=
  let _ := σ.extract
  sorry

/-- Soundness error bound for the Fischlin transform (Fischlin 2005, Theorem 2).

For `Q` total hash oracle queries, `ρ` repetitions, `b`-bit hashes, and max sum `S`:
the error is `(Q + 1) · (S + 1) · C(S + ρ - 1, ρ - 1) / 2^(bρ)`.

For `S = 0` this simplifies to `(Q + 1) / 2^(bρ)`. -/
noncomputable def knowledgeSoundnessError (Q ρ b S : ℕ) : ℝ≥0∞ :=
  (↑(Q + 1) : ℝ≥0∞) * ↑((S + 1) * Nat.choose (S + ρ - 1) (ρ - 1)) /
    ((↑(2 ^ b) : ℝ≥0∞) ^ ρ)

/-- The knowledge soundness experiment for the Fischlin transform.

Runs a cheating prover with a logged random oracle, then checks:
1. Whether the Fischlin verifier accepts the produced proof.
2. Whether the online extractor successfully recovers a valid witness.

Returns `true` (the "bad event") when verification succeeds but extraction fails
to produce a valid witness.

The `prover` argument is the raw function rather than `KnowledgeSoundnessAdv`
to keep type inference tractable with `sorry` bodies. -/
noncomputable def knowledgeSoundnessExp
    (prover : X → M →
      OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M) (FischlinProof PC Ω P ρ))
    (x : X) (msg : M) : ProbComp Bool :=
  let _ := Fischlin σ hr ρ b S M
  sorry

/-- Knowledge soundness of the Fischlin transform via online (straight-line) extraction
(Fischlin 2005, Theorem 2).

If the Σ-protocol is specially sound with unique responses, then for any cheating prover
making at most `Q` hash queries, the probability that the verifier accepts but the
online extractor fails to recover a valid witness is at most
`(Q + 1) · (S + 1) · C(S + ρ - 1, ρ - 1) / 2^(bρ)`.

Unlike the Fiat-Shamir transform, this extraction is **straight-line** (no rewinding),
which enables a tight security reduction. -/
theorem knowledgeSoundness
    (hss : σ.SpeciallySound) (hur : σ.UniqueResponses)
    (adv : KnowledgeSoundnessAdv ρ b M)
    (Q : ℕ) (x : X) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M adv.run x msg]
      ≤ knowledgeSoundnessError Q ρ b S := by sorry

/-! ### EUF-CMA Security -/

/-- EUF-CMA security of the Fischlin signature scheme with a tight reduction
(Fischlin 2005, Corollary 1).

If the Σ-protocol is specially sound with unique responses, then the advantage of any
EUF-CMA adversary making at most `Q` hash queries is bounded by the knowledge
soundness error `(Q + 1) · (S + 1) · C(S + ρ - 1, ρ - 1) / 2^(bρ)`.

This bound is **tight** (no forking-lemma loss), unlike the Fiat-Shamir transform
where the reduction incurs an `O(Q / |Ω|)` overhead via rewinding. The reduction
time is `O(T)` where `T` is the adversary's running time. -/
theorem euf_cma_tight
    (hss : σ.SpeciallySound) (hur : σ.UniqueResponses)
    (adv : SignatureAlg.unforgeableAdv (Fischlin σ hr ρ b S M))
    (Q : ℕ) :
    adv.advantage ≤ knowledgeSoundnessError Q ρ b S := by sorry

end Fischlin
