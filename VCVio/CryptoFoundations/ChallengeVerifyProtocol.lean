/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import VCVio.EvalDist.TVDist

/-!
# Challenge-Verify Protocols

This file defines `ChallengeVerifyProtocol`, a monad-generic abstraction for public-coin
commit–challenge–response protocols, together with the standard security properties:
completeness, special soundness, and honest-verifier zero-knowledge (HVZK).

It is a close relative of `VCVio.CryptoFoundations.SigmaProtocol.SigmaProtocol`. The difference is
that the prover's computations live in an *arbitrary* monad `m` carrying probability semantics,
rather than being fixed to `ProbComp`. Taking `m := ProbComp` recovers the usual Σ-protocol whose
only randomness is uniform sampling, but a general `m` lets the prover and challenge sampler
additionally query oracles — for instance a hash / Merkle oracle, as needed when realizing the
Kilian transformation (`VCVio.CryptoFoundations.Kilian`) as a succinct interactive argument.

The challenge sampler `sampleChal` is a first-class field and is left fully abstract: it need not be
uniform.

## Type Parameters

- `Stmt`: statement (public input)
- `Wit`: witness
- `Commit`: public commitment (revealed to the verifier)
- `PrvState`: private prover state (retained between commit and respond)
- `Chal`: verifier challenge
- `Resp`: prover response
- `rel`: the relation proven by the protocol
- `m`: the monad in which the prover and challenge sampler run

## Probability assumptions

Probability reasoning is expressed through the standard `MonadLiftT` lifts introduced in the
`EvalDist` layer: `MonadLiftT m SPMF` (for `evalDist` / `Pr[…]` / `tvDist`), `MonadLiftT m SetM`
(for `support`), and the bridge class `EvalDistCompatible m` tying the two together.
-/

universe u v

/-- A challenge-verify protocol for statements in `Stmt` and witnesses in `Wit`,
where `rel : Stmt → Wit → Bool` is the proposition proven by the protocol.
Commitments are split into a public part `Commit` (revealed to the verifier) and a
private part `PrvState` (retained by the prover). Verifier challenges are drawn from `Chal`
via the `sampleChal` computation. Prover responses are in `Resp`.

The prover's computations live in an arbitrary monad `m` carrying probability semantics. Taking
`m := ProbComp` recovers the usual notion of a Σ-protocol whose only randomness is uniform
sampling, but a general `m` lets the prover and challenge sampler additionally query oracles.

We leave properties like special soundness as separate definitions for better modularity. -/
structure ChallengeVerifyProtocol
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool)
    (m : Type → Type) where
  /-- Generate a commitment to prove knowledge of a valid witness. -/
  commit (stmt : Stmt) (wit : Wit) : m (Commit × PrvState)
  /-- Given a previous private state, respond to the challenge. -/
  respond (stmt : Stmt) (wit : Wit) (prvState : PrvState) (chal : Chal) : m Resp
  /-- Deterministic verification: check that the response satisfies the challenge. -/
  verify (stmt : Stmt) (commit : Commit) (chal : Chal) (resp : Resp) : Bool
  /-- Sample a verifier challenge. Over `ProbComp` this is generally uniform selection `$ᵗ Chal`. -/
  sampleChal : m Chal

namespace ChallengeVerifyProtocol

variable {m : Type → Type} [Monad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
  {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section complete

/-- A protocol is perfectly complete if the honest prover always convinces the verifier
on valid statement-witness pairs. -/
def PerfectlyComplete (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m) :
    Prop :=
  ∀ x w, rel x w = true →
    Pr[= true | do
      let (pc, sc) ← σ.commit x w
      let ω ← σ.sampleChal
      let π ← σ.respond x w sc ω
      return σ.verify x pc ω π] = 1

end complete

section speciallySound

/-- Special soundness at a particular statement, relative to an extractor `extract` that recovers a
witness from two accepting transcripts: given two accepting transcripts with the same commitment but
different challenges, the extracted witness is valid.

The extractor is taken as a parameter rather than being a field of `ChallengeVerifyProtocol`, since
a protocol's interaction (`commit`/`respond`/`verify`/`sampleChal`) is independent of any particular
witness-extraction strategy. -/
def SpeciallySoundAt (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (extract : Chal → Resp → Chal → Resp → m Wit) (x : Stmt) : Prop :=
  ∀ pc ω₁ ω₂ p₁ p₂, ω₁ ≠ ω₂ →
    σ.verify x pc ω₁ p₁ = true → σ.verify x pc ω₂ p₂ = true →
    ∀ w ∈ support (extract ω₁ p₁ ω₂ p₂), rel x w = true

/-- A protocol is specially sound (relative to `extract`) if `SpeciallySoundAt` holds for all
statements. -/
def SpeciallySound (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (extract : Chal → Resp → Chal → Resp → m Wit) : Prop :=
  ∀ x, SpeciallySoundAt σ extract x

omit [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [LawfulMonadLiftT m SetM]
  [EvalDistCompatible m] in
/-- Special soundness immediately validates any witness returned by the extractor from two accepting
transcripts with the same statement and commitment and with distinct challenges. -/
theorem extract_sound_of_speciallySoundAt
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    {extract : Chal → Resp → Chal → Resp → m Wit} {x : Stmt}
    (hss : σ.SpeciallySoundAt extract x)
    {pc : Commit} {ω₁ ω₂ : Chal} {p₁ p₂ : Resp} (hω : ω₁ ≠ ω₂)
    (hv₁ : σ.verify x pc ω₁ p₁ = true) (hv₂ : σ.verify x pc ω₂ p₂ = true)
    {w : Wit} (hw : w ∈ support (extract ω₁ p₁ ω₂ p₂)) :
    rel x w = true :=
  hss pc ω₁ ω₂ p₁ p₂ hω hv₁ hv₂ w hw

end speciallySound

section hvzk

/-- The honest prover's transcript distribution. -/
def realTranscript (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (x : Stmt) (w : Wit) :
    m (Commit × Chal × Resp) := do
  let (pc, sc) ← σ.commit x w
  let ω ← σ.sampleChal
  let π ← σ.respond x w sc ω
  return (pc, ω, π)

/-- Honest-verifier zero-knowledge: the real transcript distribution is within total variation
distance `ζ_zk` of the simulated one, produced by `simTranscript` given only the statement `x`.

The `sim` field only produces a public commitment; for HVZK we need a full transcript simulator
`Stmt → m (Commit × Chal × Resp)`, which we take as a parameter. -/
def HVZK (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (simTranscript : Stmt → m (Commit × Chal × Resp)) (ζ_zk : ℝ) : Prop :=
  ∀ x w, rel x w = true →
    tvDist (σ.realTranscript x w) (simTranscript x) ≤ ζ_zk

/-- Exact honest-verifier zero-knowledge: the real transcript distribution equals the
simulated one. -/
def PerfectHVZK (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (simTranscript : Stmt → m (Commit × Chal × Resp)) : Prop :=
  ∀ x w, rel x w = true →
    𝒟[σ.realTranscript x w] = 𝒟[simTranscript x]

omit [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  [EvalDistCompatible m] in
/-- The perfect HVZK property is equivalent to the approximate HVZK property with `ζ_zk = 0`. -/
@[grind =]
lemma perfectHVZK_iff_hvzk_zero
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m)
    (simTranscript : Stmt → m (Commit × Chal × Resp)) :
    σ.PerfectHVZK simTranscript ↔ σ.HVZK simTranscript 0 := by
  constructor
  · intro h
    dsimp [HVZK]
    intro x w hx
    have hzero : tvDist (σ.realTranscript x w) (simTranscript x) = 0 := by
      simpa using
        (tvDist_eq_zero_iff (σ.realTranscript x w) (simTranscript x)).2 (h x w hx)
    exact le_of_eq hzero
  · intro h
    dsimp [HVZK] at h
    intro x w hx
    have hzero : tvDist (σ.realTranscript x w) (simTranscript x) = 0 :=
      le_antisymm (h x w hx) (by
        simpa using (tvDist_nonneg (σ.realTranscript x w) (simTranscript x)))
    simpa using (tvDist_eq_zero_iff (σ.realTranscript x w) (simTranscript x)).mp hzero

end hvzk

section uniqueResponses

/-- A protocol has unique responses if for any statement, commitment, and challenge there is at most
one valid response. This property is required by transforms such as Fischlin and holds for most
common Σ-protocols (Schnorr, Guillou-Quisquater, etc.). -/
def UniqueResponses (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m) : Prop :=
  ∀ x pc ω p₁ p₂,
    σ.verify x pc ω p₁ = true → σ.verify x pc ω p₂ = true → p₁ = p₂

end uniqueResponses

end ChallengeVerifyProtocol
