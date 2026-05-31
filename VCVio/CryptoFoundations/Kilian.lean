/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
import VCVio.CryptoFoundations.ChallengeVerifyProtocol

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
  alphabet `Symbol`. The verifier is a probabilistic oracle computation: it may toss random coins
  (modeled by `unifSpec`) and adaptively query positions of the proof string (modeled by
  `PCP.spec Symbol length`), and outputs a single accept/reject bit. -/
structure PCP (Stmt Wit : Type) (rel : Stmt → Wit → Prop) where
  Symbol : Type
  [finSymbol : Fintype Symbol]
  length : ℕ
  Prover : Stmt → Wit → ProbComp (List.Vector Symbol length)
  Verifier : Stmt → OracleComp (unifSpec + PCP.spec Symbol length) Bool

namespace PCP

open scoped NNReal

variable {Stmt Wit : Type} {rel : Stmt → Wit → Prop}

/-- Run the PCP verifier on statement `stmt` against a concrete proof string `proof`, answering
  each oracle query for position `i` with `proof.get i` and leaving the verifier's coin tosses as
  an ordinary probabilistic computation. -/
noncomputable def runVerifier (pcp : PCP Stmt Wit rel) (stmt : Stmt)
    (proof : List.Vector pcp.Symbol pcp.length) : ProbComp Bool :=
  simulateQ (QueryImpl.id' unifSpec +
      (fun i => pure (proof.get i) : QueryImpl (PCP.spec pcp.Symbol pcp.length) ProbComp))
    (pcp.Verifier stmt)

/-- A PCP system satisfies **correctness** with error `correctnessError` if for every
  statement/witness pair `(stmt, wit)` in the relation, the honest verifier accepts a proof
  produced by the honest prover with probability at least `1 - correctnessError`. -/
noncomputable def correctness (pcp : PCP Stmt Wit rel) (correctnessError : ℝ≥0) : Prop :=
  ∀ stmt : Stmt,
  ∀ wit : Wit,
    rel stmt wit →
      Pr[ fun accept => accept | do
          let proof ← pcp.Prover stmt wit
          pcp.runVerifier stmt proof] ≥ 1 - correctnessError

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
    Pr[ fun accept => accept | pcp.runVerifier stmt proof] ≤ soundnessError

/-- A PCP system satisfies **perfect soundness** if it satisfies soundness with no error, i.e. the
  verifier never accepts a proof for a statement outside the language. -/
noncomputable def perfectSoundness (pcp : PCP Stmt Wit rel) : Prop :=
  pcp.soundness 0

-- TODO: Definition 19.1.3. straightline knowledge soundness error with extraction time

end PCP

section KilianTransformation

/-!
The Kilian transformation turns a `PCP` into a succinct public-coin interactive argument, which we
model as a `ChallengeVerifyProtocol` (this PR's own commit–challenge–response abstraction, see
`VCVio.CryptoFoundations.ChallengeVerifyProtocol`).

The intended instantiation:

- `Commit` is a Merkle root committing to the PCP proof string (built with the inductive Merkle
  tree of `VCVio.CryptoFoundations.MerkleTree.Inductive.Defs`);
- `PrvState` retains the full proof string together with the Merkle tree, so the prover can open
  queried positions;
- `Chal` is the verifier's randomness, which (via `pcp.Verifier`) determines the queried positions;
- `Resp` carries the opened symbols together with their Merkle authentication paths;
- `verify` checks each authentication path against the committed root and then runs the PCP
  verifier's decision on the opened symbols;
- the prover runs in a monad with access to the Merkle/hash oracle, which is exactly why
  `ChallengeVerifyProtocol` is parameterized over an arbitrary monad `m` rather than fixed to
  `ProbComp`.

`PCP.rel` is `Stmt → Wit → Prop`, whereas `ChallengeVerifyProtocol` uses a `Bool`-valued relation;
the construction will fix a decidable bridge between the two.

TODO: construct the transformation and prove that PCP correctness/soundness lift to completeness and
(knowledge) soundness of the resulting `ChallengeVerifyProtocol`.
-/

end KilianTransformation
