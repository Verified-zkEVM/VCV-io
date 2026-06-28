/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import VCVio.CryptoFoundations.VectorCommitment.Basic
import VCVio.CryptoFoundations.ChallengeVerifyProtocol
import VCVio.OracleComp.ProbComp

/-!


# The Kilian Transformation

This file is to describe the Kilian transformation ([Kilian '92], [SNARGs book Chapter 20]).
This transformation converts a Probabilistically Checkable Proof (PCP)
into an succinct interactive argument/Sigma protocol using Merkle trees.
This can then be made non-interactive using the Fiat-Shamir transformation,
(these two transformations together are referred to by the SNARGs book as
the "Micali transformation" [Micali '00]).

The majority of the Kilian paper is actually a beautiful way to make the classic GMW graph-coloring
zero-knowledge proof more efficient while keeping zero knowledge by implementing a
"notarized envelope" primitive. But I think this file should just focus on the succinctness part.
-/

open OracleComp OracleSpec

namespace PCP

/-- The oracle specification for a PCP proof string of length `length` over the alphabet `Symbol`:
  a single oracle indexed by positions `Fin length`, where querying position `i` returns the
  `i`-th symbol of the proof. -/
def spec (Symbol : Type) (length : ℕ) : OracleSpec (Fin length) :=
  fun _ => Symbol

end PCP

/-- A **Probabilistically Checkable Proof (PCP)** system for a relation `rel : Stmt → Wit → Prop`.

  The honest prover turns a statement and witness into a proof string of `length` symbols over the
  alphabet `Symbol`.

  The verifier draws random coins of type `Coins` (sampled by `sampleCoins`); *given* its coins it
  is the deterministic oracle computation `Verifier stmt coins`, which adaptively queries positions
  of the proof string (modeled by `PCP.spec Symbol length`) and outputs a single accept/reject bit.

  Separating the coins from the proof queries — rather than folding both into a single
  `OracleComp (unifSpec + PCP.spec …)` — matches the public-coin structure used by the Kilian
  transformation: the verifier *sends* its coins, and the prover then simulates `Verifier stmt
  coins` to learn exactly which positions to open. -/
structure PCP (Stmt Wit : Type) (rel : Stmt → Wit → Prop) where
  Symbol : Type
  [finSymbol : Fintype Symbol]
  length : ℕ
  Coins : Type
  sampleCoins : ProbComp Coins
  Prover : Stmt → Wit → ProbComp (List.Vector Symbol length)
  Verifier : Stmt → Coins → OracleComp (PCP.spec Symbol length) Bool

namespace PCP

open scoped NNReal

variable {Stmt Wit : Type} {rel : Stmt → Wit → Prop}

/-- Run the PCP verifier on statement `stmt` with fixed coins `coins` against a concrete proof
  string `proof`, answering each oracle query for position `i` with `proof.get i`. Since the coins
  are fixed and the proof is concrete, the result is a deterministic accept/reject bit. -/
def runVerifier (pcp : PCP Stmt Wit rel) (stmt : Stmt) (coins : pcp.Coins)
    (proof : List.Vector pcp.Symbol pcp.length) : Bool :=
  Id.run <| simulateQ
    (fun i => pure (proof.get i) : QueryImpl (PCP.spec pcp.Symbol pcp.length) Id)
    (pcp.Verifier stmt coins)

/-- A PCP system satisfies **correctness** with error `correctnessError` if for every
  statement/witness pair `(stmt, wit)` in the relation, the honest verifier accepts a proof
  produced by the honest prover with probability at least `1 - correctnessError`. -/
noncomputable def correctness (pcp : PCP Stmt Wit rel) (correctnessError : ℝ≥0) : Prop :=
  ∀ stmt : Stmt,
  ∀ wit : Wit,
    rel stmt wit →
      Pr[ fun accept => accept | do
          let proof ← pcp.Prover stmt wit
          let coins ← pcp.sampleCoins
          return pcp.runVerifier stmt coins proof] ≥ 1 - correctnessError

/-- A PCP system satisfies **perfect correctness** if it satisfies correctness with no error. -/
noncomputable def perfectCorrectness (pcp : PCP Stmt Wit rel) : Prop :=
  pcp.correctness 0

/-- A PCP system satisfies **soundness** with error `soundnessError` if for every statement `stmt`
  outside the language (i.e. with no valid witness), and every adversarially chosen proof string,
  the verifier accepts with probability at most `soundnessError`.

  Since the verifier's only source of randomness is its own coin tosses, it suffices to quantify
  over fixed proof strings: a randomized malicious prover is a convex combination of these, so it
  can do no better than the best fixed proof. -/
noncomputable def soundness (pcp : PCP Stmt Wit rel) (soundnessError : ℝ≥0) : Prop :=
  ∀ stmt : Stmt,
    (¬ ∃ wit : Wit, rel stmt wit) →
  ∀ proof : List.Vector pcp.Symbol pcp.length,
    Pr[ fun accept => accept | do
        let coins ← pcp.sampleCoins
        return pcp.runVerifier stmt coins proof] ≤ soundnessError

/-- A PCP system satisfies **perfect soundness** if it satisfies soundness with no error, i.e. the
  verifier never accepts a proof for a statement outside the language. -/
noncomputable def perfectSoundness (pcp : PCP Stmt Wit rel) : Prop :=
  pcp.soundness 0

-- TODO: Definition 19.1.3. straightline knowledge soundness error with extraction time

end PCP

section KilianTransformation

variable {Stmt Wit : Type} {rel : Stmt → Wit → Prop}

/-- **The Kilian transformation.**

Turn a `PCP` into a (public-coin) succinct `ChallengeVerifyProtocol`, the interactive argument at
the heart of Kilian's protocol, parameterized by an arbitrary batch-opening vector commitment `bovc`
over the PCP's symbol alphabet (e.g. the inductive Merkle tree of
`VCVio.CryptoFoundations.VectorCommitment.MerkleTree`):

1. the prover commits to its PCP proof string with `bovc.commit` (`commit`);
2. the verifier sends random coins (`sampleChal := pcp.sampleCoins`);
3. the prover simulates `pcp.Verifier stmt coins` against its committed proof to learn exactly which
   positions the verifier reads, and opens *exactly* that set in one shot with `bovc.openBatch`,
   returning the claimed `(position, value)` pairs alongside the batch opening (`respond`);
4. the verifier checks the batch opening against the commitment with `bovc.verifyBatch`, then
   replays `pcp.Verifier stmt coins`, answering each position query from the claimed values, accepts
   iff
   the batch opening verifies, every queried position was claimed, and the PCP verifier accepts
   (`verify`).

A batch-opening commitment is the natural primitive here: Kilian opens a whole set of positions at
once, so a construction that amortizes work across that set (a shared-path Merkle proof, say) is
exactly what makes the argument succinct.

Modeling choices for this definition (correctness/soundness are deferred):

- Positions of the proof string are the commitment indices `Fin pcp.length`; the value at a position
  is a PCP symbol.
- The whole transformation runs in the commitment's monad `m`; the prover's PCP randomness is pulled
  in via `MonadLiftT ProbComp m`. Taking `m := ProbComp` with a standard-model Merkle commitment
  recovers the usual deterministic-verification formulation.
- `Resp` is the claimed `(position, value)` pairs together with a single batch opening. Succinctness
  is what makes Kilian interesting: only the positions the verifier actually queries are opened, and
  `verify` rejects (via the `none` branch of the lookup) if it ever reads an unclaimed position.
- `boolRel` is the `Bool`-valued relation of the resulting protocol; relating it to `pcp.rel` is
  part of the deferred security analysis. -/
noncomputable def KilianTransformation
    (pcp : PCP Stmt Wit rel) [DecidableEq pcp.Symbol]
    {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment m (Fin pcp.length) pcp.Symbol Commit State BatchOpening)
    (boolRel : Stmt → Wit → Bool) :
    ChallengeVerifyProtocol Stmt Wit
      Commit                                                  -- Commit: the vector commitment
      State                                                   -- PrvState: the opener's state
      pcp.Coins                                               -- Chal: the verifier's coins
      (List (Fin pcp.length × pcp.Symbol) × BatchOpening)     -- Resp: claims + batch opening
      boolRel m where
  commit stmt wit := do
    let proof ← pcp.Prover stmt wit
    bovc.commit proof.get
  sampleChal := liftM pcp.sampleCoins
  respond stmt _wit st coins := do
    -- Simulate the verifier against the committed proof, logging the positions it reads.
    let logImpl : QueryImpl (PCP.spec pcp.Symbol pcp.length) (StateT (List (Fin pcp.length)) Id) :=
      fun i => do modify (i :: ·); pure (bovc.decode st i)
    let queried : List (Fin pcp.length) :=
      ((Id.run ((simulateQ logImpl (pcp.Verifier stmt coins)).run [])).2).dedup
    -- Open exactly the queried positions as a single batch, alongside the claimed values.
    let op ← bovc.openBatch st queried
    return (queried.map (fun i => (i, bovc.decode st i)), op)
  verify stmt c coins resp :=
    -- Check the batch opening, then replay the verifier answering each position from its claimed
    -- value; an unclaimed position fails the run, as does a batch opening that does not verify.
    let (claims, op) := resp
    let answerImpl : QueryImpl (PCP.spec pcp.Symbol pcp.length) (OptionT Id) :=
      fun i => match claims.find? (fun e => decide (e.1 = i)) with
        | none => failure
        | some (_, sym) => pure sym
    bovc.verifyBatch c claims op &&
      decide (Id.run (simulateQ answerImpl (pcp.Verifier stmt coins)).run = some true)

end KilianTransformation
