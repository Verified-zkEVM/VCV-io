/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.ExecutionMethod
import VCVio.OracleComp.EvalDist

/-!
# Sigma Protocol

This file defines a structure type for Σ-protocols, along with standard
security properties: completeness, special soundness, and honest-verifier
zero-knowledge (HVZK).
-/

universe u v

open OracleSpec OracleComp

/-- A sigma protocol for statements in `S` and witnesses in `W`,
where `p : X → W → Bool` is the proposition that is proven by the Σ-protocol.
Commitments are split into private and public parts in `PC` and `SC` resp.
Verifier challenges are assumed to be drawn uniformly from `Ω`.
Provers final proof responses are in `P`.

We have two types for the commitments in order to allow for a public part in `PC`
and secret part in `SC`. Only the commitment in `PC` is revealed to the verifier,
but the `prove` function may still use `SC` in generating a proof.

We leave properties like special soundness as seperate definitions for better modularity. -/
structure SigmaProtocol
    (S W PC SC Ω P : Type) (p : S → W → Bool) where
  /-- Given a statement `s`, make a commitment to prove that you have a valid witness `w`. -/
  commit (s : S) (w : W) : ProbComp (PC × SC)
  /-- Given a previous secret commitment `sc`, repond to the challenge `ω`-/
  respond (s : S) (w : W) (sc : SC) (ω : Ω) : ProbComp P
  /-- Deterministic function to check that the proof `p` satisfies the challenge `ω`. -/
  verify (s : S) (pc : PC) (ω : Ω) (p : P) : Bool
  /-- Simulate public commitment generation while only knowing the statement. -/
  sim (s : S) : ProbComp PC
  /-- Extract a witness to the statement from two proofs. -/
  extract (ω₁ : Ω) (p₁ : P) (ω₂ : Ω) (p₂ : P) : ProbComp W

namespace SigmaProtocol

variable {S W PC SC Ω P : Type} {p : S → W → Bool}

section complete

variable [SampleableType Ω] [unifSpec.Fintype] [unifSpec.Inhabited]

/-- A Σ-protocol is perfectly complete if the honest prover always convinces the verifier
on valid statement-witness pairs. -/
def PerfectlyComplete (σ : SigmaProtocol S W PC SC Ω P p) : Prop :=
  ∀ x w, p x w = true →
    Pr[= true | do
      let (pc, sc) ← σ.commit x w
      let ω ← $ᵗ Ω
      let π ← σ.respond x w sc ω
      return σ.verify x pc ω π] = 1

end complete

section speciallySound

/-- Special soundness at a particular statement: given two accepting transcripts with the same
commitment but different challenges, the extracted witness is valid. -/
def SpeciallySoundAt (σ : SigmaProtocol S W PC SC Ω P p) (x : S) : Prop :=
  ∀ pc ω₁ ω₂ p₁ p₂, ω₁ ≠ ω₂ →
    σ.verify x pc ω₁ p₁ = true → σ.verify x pc ω₂ p₂ = true →
    ∀ w ∈ support (σ.extract ω₁ p₁ ω₂ p₂), p x w = true

/-- A Σ-protocol is specially sound if `SpeciallySoundAt` holds for all statements. -/
def SpeciallySound (σ : SigmaProtocol S W PC SC Ω P p) : Prop :=
  ∀ x, SpeciallySoundAt σ x

end speciallySound

section hvzk

variable [SampleableType Ω] [unifSpec.Fintype] [unifSpec.Inhabited]

/-- Honest-verifier zero-knowledge: the real transcript distribution equals the simulated one.

The real transcript is `(pc, ω, respond x w sc ω)` with `(pc, sc) ← commit x w` and `ω ← $ᵗ Ω`.
The simulated transcript is produced by `simTranscript` given only the statement `x`.

Note: the `sim` field of `SigmaProtocol` only produces a public commitment `PC`. For HVZK we need
a full transcript simulator `S → ProbComp (PC × Ω × P)`. We parameterize by this simulator. -/
def HVZK (σ : SigmaProtocol S W PC SC Ω P p)
    (simTranscript : S → ProbComp (PC × Ω × P)) : Prop :=
  ∀ x w, p x w = true →
    evalDist (do
      let (pc, sc) ← σ.commit x w
      let ω ← $ᵗ Ω
      let π ← σ.respond x w sc ω
      return (pc, ω, π)) =
    evalDist (simTranscript x)

end hvzk

section uniqueResponses

/-- A Σ-protocol has unique responses if for any statement, commitment, and challenge,
there is at most one valid response. This property is required by the Fischlin transform
and holds for most common Σ-protocols (Schnorr, Guillou-Quisquater, etc.). -/
def UniqueResponses (σ : SigmaProtocol S W PC SC Ω P p) : Prop :=
  ∀ x pc ω p₁ p₂,
    σ.verify x pc ω p₁ = true → σ.verify x pc ω p₂ = true → p₁ = p₂

end uniqueResponses

end SigmaProtocol
