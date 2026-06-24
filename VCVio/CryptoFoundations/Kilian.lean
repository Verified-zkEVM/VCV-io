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

open OracleComp OracleSpec BinaryTree InductiveMerkleTree

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

/-- Build the leaf data of a Merkle tree of skeleton `s` from a function assigning a value to each
leaf position. -/
def leafDataOfFn {α : Type _} : (s : Skeleton) → (SkeletonLeafIndex s → α) → LeafData α s
  | Skeleton.leaf, f => LeafData.leaf (f SkeletonLeafIndex.ofLeaf)
  | Skeleton.internal _ _, f =>
      LeafData.internal
        (leafDataOfFn _ fun i => f (SkeletonLeafIndex.ofLeft i))
        (leafDataOfFn _ fun i => f (SkeletonLeafIndex.ofRight i))

variable {Stmt Wit : Type} {rel : Stmt → Wit → Prop}

/-- **The Kilian transformation.**

Turn a `PCP` into a (public-coin) succinct `ChallengeVerifyProtocol`, the interactive argument at
the heart of Kilian's protocol:

1. the prover Merkle-commits to its PCP proof string (`commit`);
2. the verifier sends random coins (`sampleChal := pcp.sampleCoins`);
3. the prover simulates `pcp.Verifier stmt coins` against its proof to learn exactly which positions
   the verifier reads, and opens *only those* leaves with their Merkle authentication paths
   (`respond`);
4. the verifier replays `pcp.Verifier stmt coins`, answering each position query from the prover's
   opening while checking that opening's authentication path against the committed root, and accepts
   iff every queried position was opened authentically and the PCP verifier accepts (`verify`).

Modeling choices for this definition (correctness/soundness are deferred):

- The committed proof string is laid out on a caller-supplied Merkle skeleton `s` via the
  position-to-leaf equivalence `e : Fin pcp.length ≃ SkeletonLeafIndex s`.
- `hashFn` is the (collision-resistant) two-to-one hash compressing the tree; the construction is in
  the standard-model / CRH formulation, so hashing is the pure function `hashFn` and `verify` is
  deterministic.
- `Resp` is the *partial* opening map: `resp i = some (symbol, path)` exactly for the positions the
  prover opens, and `none` elsewhere. Succinctness is what makes Kilian interesting: only the
  positions the verifier actually queries are opened, and `verify` rejects (via the `none` branch)
  if it ever reads an unopened position.
- `boolRel` is the `Bool`-valued relation of the resulting protocol; relating it to `pcp.rel` is
  part of the deferred security analysis.

The monad is `ProbComp` (the prover's only randomness is the PCP prover's).

TODOs:

- Instead of a Merkle Tree, create an abstract vector commitment interface
- Make `KilianTransformation` monadic over the vector commitment's monad.

-/
noncomputable def KilianTransformation
    (pcp : PCP Stmt Wit rel) [DecidableEq pcp.Symbol]
    (s : Skeleton) (e : Fin pcp.length ≃ SkeletonLeafIndex s)
    (hashFn : pcp.Symbol → pcp.Symbol → pcp.Symbol)
    (boolRel : Stmt → Wit → Bool) :
    ChallengeVerifyProtocol Stmt Wit
      pcp.Symbol                                          -- Commit: the Merkle root
      (FullData pcp.Symbol s)                             -- PrvState: the committed tree
      pcp.Coins                                           -- Chal: the verifier's coins
      ((i : Fin pcp.length) → Option (pcp.Symbol × List.Vector pcp.Symbol (e i).depth))  -- Resp
      boolRel ProbComp where
  commit stmt wit := do
    let proof ← pcp.Prover stmt wit
    let tree := buildMerkleTreeWithHash (leafDataOfFn s fun i => proof.get (e.symm i)) hashFn
    return (tree.getRootValue, tree)
  sampleChal := pcp.sampleCoins
  respond stmt _wit tree coins := do
    -- Simulate the verifier against the committed proof, logging the positions it reads.
    let logImpl : QueryImpl (PCP.spec pcp.Symbol pcp.length) (StateT (List (Fin pcp.length)) Id) :=
      fun i => do modify (i :: ·); pure (tree.toLeafData.get (e i))
    let queried : List (Fin pcp.length) :=
      (Id.run ((simulateQ logImpl (pcp.Verifier stmt coins)).run [])).2
    -- Open exactly the queried positions, each with its authentication path.
    return fun j =>
      if j ∈ queried then some (tree.toLeafData.get (e j), generateProof tree (e j)) else none
  verify stmt root coins resp :=
    -- Replay the verifier, answering each position from its opening while checking the
    -- authentication path; an unopened or mis-authenticated position fails the whole run.
    let answerImpl : QueryImpl (PCP.spec pcp.Symbol pcp.length) (OptionT Id) :=
      fun i => match resp i with
        | none => failure
        | some (sym, path) =>
            if getPutativeRootWithHash (e i) sym path hashFn = root then pure sym else failure
    decide (Id.run (simulateQ answerImpl (pcp.Verifier stmt coins)).run = some true)

end KilianTransformation
