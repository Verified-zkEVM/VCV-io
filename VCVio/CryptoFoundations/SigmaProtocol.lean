/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.TVDist
import VCVio.CryptoFoundations.IdenSchemeWithAbort

/-!
# Sigma Protocol

This file defines a structure type for Σ-protocols, along with standard
security properties: completeness, special soundness, and honest-verifier
zero-knowledge (HVZK).

## Type Parameters

- `Stmt`: statement (public key)
- `Wit`: witness (secret key)
- `Commit`: public commitment
- `PrvState`: private prover state (retained between commit and respond)
- `Chal`: verifier challenge (drawn uniformly)
- `Resp`: prover response
- `rel`: the relation proven by the protocol

## Coercion to `IdenSchemeWithAbort`

Every `SigmaProtocol` can be viewed as a non-aborting `IdenSchemeWithAbort` via
`SigmaProtocol.toIdenSchemeWithAbort`, which wraps `respond` with `some`.
-/

universe u v

open OracleSpec OracleComp

/-- A sigma protocol for statements in `Stmt` and witnesses in `Wit`,
where `rel : Stmt → Wit → Bool` is the proposition proven by the Σ-protocol.
Commitments are split into a public part `Commit` (revealed to the verifier) and a
private part `PrvState` (retained by the prover). Verifier challenges are drawn uniformly
from `Chal`. Prover responses are in `Resp`.

We leave properties like special soundness as separate definitions for better modularity. -/
structure SigmaProtocol
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool) where
  /-- Generate a commitment to prove knowledge of a valid witness. -/
  commit (stmt : Stmt) (wit : Wit) : ProbComp (Commit × PrvState)
  /-- Given a previous private state, respond to the challenge. -/
  respond (stmt : Stmt) (wit : Wit) (prvState : PrvState) (chal : Chal) : ProbComp Resp
  /-- Deterministic verification: check that the response satisfies the challenge. -/
  verify (stmt : Stmt) (commit : Commit) (chal : Chal) (resp : Resp) : Bool
  /-- Simulate public commitment generation while only knowing the statement. -/
  sim (stmt : Stmt) : ProbComp Commit
  /-- Extract a witness to the statement from two accepting transcripts. -/
  extract (chal₁ : Chal) (resp₁ : Resp) (chal₂ : Chal) (resp₂ : Resp) : ProbComp Wit

namespace SigmaProtocol

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section complete

variable [SampleableType Chal] [unifSpec.Fintype] [unifSpec.Inhabited]

/-- A Σ-protocol is perfectly complete if the honest prover always convinces the verifier
on valid statement-witness pairs. -/
def PerfectlyComplete (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) : Prop :=
  ∀ x w, rel x w = true →
    Pr[= true | do
      let (pc, sc) ← σ.commit x w
      let ω ← $ᵗ Chal
      let π ← σ.respond x w sc ω
      return σ.verify x pc ω π] = 1

end complete

section speciallySound

/-- Special soundness at a particular statement: given two accepting transcripts with the same
commitment but different challenges, the extracted witness is valid. -/
def SpeciallySoundAt (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (x : Stmt) : Prop :=
  ∀ pc ω₁ ω₂ p₁ p₂, ω₁ ≠ ω₂ →
    σ.verify x pc ω₁ p₁ = true → σ.verify x pc ω₂ p₂ = true →
    ∀ w ∈ support (σ.extract ω₁ p₁ ω₂ p₂), rel x w = true

/-- A Σ-protocol is specially sound if `SpeciallySoundAt` holds for all statements. -/
def SpeciallySound (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) : Prop :=
  ∀ x, SpeciallySoundAt σ x

/-- Special soundness immediately validates any witness returned by the Σ-protocol extractor from
two accepting transcripts with the same statement and commitment and with distinct challenges. -/
theorem extract_sound_of_speciallySoundAt
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) {x : Stmt}
    (hss : σ.SpeciallySoundAt x)
    {pc : Commit} {ω₁ ω₂ : Chal} {p₁ p₂ : Resp} (hω : ω₁ ≠ ω₂)
    (hv₁ : σ.verify x pc ω₁ p₁ = true) (hv₂ : σ.verify x pc ω₂ p₂ = true)
    {w : Wit} (hw : w ∈ support (σ.extract ω₁ p₁ ω₂ p₂)) :
    rel x w = true :=
  hss pc ω₁ ω₂ p₁ p₂ hω hv₁ hv₂ w hw

end speciallySound

section hvzk

variable [SampleableType Chal] [unifSpec.Fintype] [unifSpec.Inhabited]

/-- The honest prover's transcript distribution for a Σ-protocol. -/
def realTranscript (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (x : Stmt) (w : Wit) :
    ProbComp (Commit × Chal × Resp) := do
  let (pc, sc) ← σ.commit x w
  let ω ← $ᵗ Chal
  let π ← σ.respond x w sc ω
  return (pc, ω, π)

/-- Honest-verifier zero-knowledge: the real transcript distribution is within total variation
distance `ζ_zk` of the simulated one.

The real transcript is `σ.realTranscript x w`.
The simulated transcript is produced by `simTranscript` given only the statement `x`.

Note: the `sim` field of `SigmaProtocol` only produces a public commitment. For HVZK we need
a full transcript simulator `Stmt → ProbComp (Commit × Chal × Resp)`. We parameterize by this
simulator. -/
def HVZK (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) (ζ_zk : ℝ) : Prop :=
  ∀ x w, rel x w = true →
    tvDist (σ.realTranscript x w) (simTranscript x) ≤ ζ_zk

/-- Exact honest-verifier zero-knowledge: the real transcript distribution equals the
simulated one. -/
def PerfectHVZK (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) : Prop :=
  ∀ x w, rel x w = true →
    evalDist (σ.realTranscript x w) = evalDist (simTranscript x)

/-- The perfect HVZK property is equivalent to the approximate HVZK property with `ζ_zk = 0`. -/
@[grind =]
lemma perfectHVZK_iff_hvzk_zero
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) :
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

/-- A Σ-protocol has unique responses if for any statement, commitment, and challenge,
there is at most one valid response. This property is required by the Fischlin transform
and holds for most common Σ-protocols (Schnorr, Guillou-Quisquater, etc.). -/
def UniqueResponses (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) : Prop :=
  ∀ x pc ω p₁ p₂,
    σ.verify x pc ω p₁ = true → σ.verify x pc ω p₂ = true → p₁ = p₂

end uniqueResponses

section toIdenSchemeWithAbort

/-- Every `SigmaProtocol` can be viewed as a non-aborting `IdenSchemeWithAbort` by wrapping
the response in `some`. The `sim` and `extract` fields are not part of
`IdenSchemeWithAbort` and are dropped. -/
def toIdenSchemeWithAbort (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) :
    IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel where
  commit := σ.commit
  respond := fun stmt wit prvState chal => some <$> σ.respond stmt wit prvState chal
  verify := σ.verify

instance : Coe (SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel) :=
  ⟨toIdenSchemeWithAbort⟩

end toIdenSchemeWithAbort

end SigmaProtocol
