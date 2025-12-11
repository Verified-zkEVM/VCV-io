/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.ExecutionMethod

/-!
# Sigma Protocol

This file defines a structure type for Σ-protocols.
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
structure SigmaAlg
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

namespace SigmaAlg

section complete

end complete

section speciallySound

end speciallySound

end SigmaAlg
