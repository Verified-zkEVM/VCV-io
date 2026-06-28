/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import VCVio.CryptoFoundations.VectorCommitment.Basic
import VCVio.CryptoFoundations.ChallengeVerifyProtocol.Basic
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.Tracing

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

/-- A **Probabilistically Checkable Proof (PCP)** system for a relation `rel : Stmt → Wit → Prop`.

  The honest prover turns a statement and witness into a proof string of `length` symbols over the
  alphabet `Symbol`.

  The verifier draws random coins of type `Coins` (sampled by `sampleCoins`); *given* its coins it
  is the deterministic oracle computation `Verifier stmt coins`, which adaptively queries positions
  of the proof string (modeled by `Fin length →ₒ Symbol`) and outputs a single accept/reject bit.

  Separating the coins from the proof queries — rather than folding both into a single
  `OracleComp (unifSpec + (Fin length →ₒ Symbol))` — matches the public-coin structure used by the
  Kilian transformation: the verifier *sends* its coins, and the prover then simulates `Verifier
  stmt coins` to learn exactly which positions to open. -/
structure PCP (Stmt Wit : Type) (rel : Stmt → Wit → Prop) where
  Symbol : Type
  [finSymbol : Fintype Symbol]
  length : ℕ
  Coins : Type
  sampleCoins : ProbComp Coins
  Prover : Stmt → Wit → ProbComp (List.Vector Symbol length)
  Verifier : Stmt → Coins → OracleComp (Fin length →ₒ Symbol) Bool

namespace PCP

open scoped NNReal

variable {Stmt Wit : Type} {rel : Stmt → Wit → Prop}

/-- Run the PCP verifier on statement `stmt` with fixed coins `coins` against a concrete proof
  string `proof`, answering each oracle query for position `i` with `proof.get i`. Since the coins
  are fixed and the proof is concrete, the result is a deterministic accept/reject bit. -/
def runVerifier (pcp : PCP Stmt Wit rel) (stmt : Stmt) (coins : pcp.Coins)
    (proof : List.Vector pcp.Symbol pcp.length) : Bool :=
  Id.run <| simulateQ (QueryImpl.ofListVector proof) (pcp.Verifier stmt coins)

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

section ReadLog

/-! ## Read-log of a deterministic oracle computation

`pathLog so comp` is the list of inputs that `comp` queries, in the order it reads them, when its
oracles are answered by the handler `so`. It is the input-only specialization of the generic writer
trace `QueryImpl.withTraceAppendBefore`: each queried input is `tell`-ed before being answered. The
Kilian prover uses it to discover exactly which proof positions the verifier reads. -/

universe u

variable {ι : Type u} {spec : OracleSpec ι}

/-- The inputs a deterministic computation queries when its oracles are answered by `so`, in the
order they are read: each queried input is `tell`-ed to the writer before being answered. -/
def pathLog (so : QueryImpl spec Id) {α : Type u} (comp : OracleComp spec α) : List ι :=
  (simulateQ (so.withTraceAppendBefore (fun t => [t])) comp).run.2

/-- A query records its input at the head of the read-log and then continues: the writer trace
`tell`s `[t]` before answering, so the input is prepended. -/
theorem pathLog_query (so : QueryImpl spec Id) {α : Type u} (t : spec.Domain)
    (oa : spec.Range t → OracleComp spec α) :
    pathLog so (liftM (spec.query t) >>= oa) = t :: pathLog so (oa (so t)) := by
  unfold pathLog
  simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.withTraceAppendBefore_apply,
    WriterT.run_bind', WriterT.run_tell]
  rfl

end ReadLog

section AnswerFunctions

/-! ## The verifier's claim-lookup handler

The honest parties answer the deterministic PCP verifier with reusable pieces of the generic
`QueryImpl` library: purely with `QueryImpl.ofFn f` (answer query `i` with `f i`), and — when the
prover needs the positions read — with `pathLog` (the read-log built on
`QueryImpl.withTraceAppendBefore`). `claimAnswer` below is the verifier's own per-query handler: a
failing lookup against the prover's claimed `(position, value)` pairs. -/

variable {Sym : Type} {len : ℕ}

/-- Look up a position among the claimed `(position, value)` pairs, failing if absent. This is the
verifier's per-query handler in `KilianTransformation.verify`. -/
def claimAnswer (claims : List (Fin len × Sym)) : QueryImpl (Fin len →ₒ Sym) (OptionT Id) :=
  fun i => match claims.find? (fun e => decide (e.1 = i)) with
    | none => failure
    | some (_, sym) => pure sym

end AnswerFunctions

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
    let queried : List (Fin pcp.length) :=
      (pathLog (bovc.decode st) (pcp.Verifier stmt coins)).dedup
    -- Open exactly the queried positions as a single batch, alongside the claimed values.
    let op ← bovc.openBatch st queried
    return (queried.map (fun i => (i, bovc.decode st i)), op)
  verify stmt c coins resp :=
    -- Check the batch opening, then replay the verifier answering each position from its claimed
    -- value; an unclaimed position fails the run, as does a batch opening that does not verify.
    let (claims, op) := resp
    bovc.verifyBatch c claims op &&
      decide (Id.run (simulateQ (claimAnswer claims) (pcp.Verifier stmt coins)).run = some true)

end KilianTransformation

section ReplayInfrastructure

/-! ## Deterministic replay infrastructure

The completeness of the Kilian transformation rests on a deterministic fact about the verifier:
the prover's logging simulation (which records the positions the verifier reads), the verifier's
own replay against the prover's openings, and the bare PCP run on the committed proof are all the
*same* deterministic computation answered consistently. These lemmas package that fact for a fixed
answer function `f : Fin len → Sym` on the PCP oracle. -/

variable {Sym : Type} {len : ℕ}

/-- Looking up a present position among `(i, f i)` claims returns its value. -/
theorem find?_claims (f : Fin len → Sym) (t : Fin len) :
    ∀ L : List (Fin len), t ∈ L →
      (L.map (fun i => (i, f i))).find? (fun e => decide (e.1 = t)) = some (t, f t)
  | a :: L, h => by
    simp only [List.map_cons, List.find?_cons]
    rcases eq_or_ne a t with rfl | hat
    · simp
    · rw [show decide (a = t) = false from by simpa using hat]
      exact find?_claims f t L ((List.mem_cons.1 h).resolve_left (fun h' => hat h'.symm))

/-- The verifier's per-query handler answers a claimed position with its value. -/
theorem claimAnswer_map (f : Fin len → Sym) (L : List (Fin len)) (t : Fin len) (ht : t ∈ L) :
    claimAnswer (L.map (fun i => (i, f i))) t = (pure (f t) : OptionT Id Sym) := by
  simp only [claimAnswer, find?_claims f t L ht]

/-- **Replay lemma.** If the claims answer every position the verifier reads (under `f`) with `f`'s
value, the verifier's `OptionT` replay never fails and reproduces the pure run. -/
theorem claimAnswer_run (f : Fin len → Sym) (claims : List (Fin len × Sym)) {β}
    (comp : OracleComp (Fin len →ₒ Sym) β) :
    (∀ t ∈ pathLog f comp, claimAnswer claims t = (pure (f t) : OptionT Id Sym)) →
      (simulateQ (claimAnswer claims) comp).run
        = some (evalWithAnswerFn (QueryImpl.ofFn f) comp) := by
  induction comp using OracleComp.inductionOn with
  | pure x => intro _; rfl
  | query_bind t oa ih =>
    intro h
    have ht : claimAnswer claims t = (pure (f t) : OptionT Id Sym) :=
      h t (by rw [pathLog_query]; exact List.mem_cons_self ..)
    have hq : evalWithAnswerFn (QueryImpl.ofFn f) (liftM ((Fin len →ₒ Sym).query t)) = f t := by
      change simulateQ (QueryImpl.ofFn f) (liftM ((Fin len →ₒ Sym).query t)) = f t
      rw [simulateQ_spec_query]; rfl
    simp only [simulateQ_bind, simulateQ_spec_query, ht, evalWithAnswerFn_bind, hq]
    exact ih (f t) (fun t' ht' => h t' (by rw [pathLog_query]; exact List.mem_cons_of_mem _ ht'))

end ReplayInfrastructure

section Completeness

variable {Stmt Wit : Type} {rel : Stmt → Wit → Prop}

/-- **Deterministic completeness core.** For a fixed honestly committed state `st` and coins, the
Kilian verifier accepts the honest prover's response, provided:

* `hcov` — the opened set `queried` covers every position the PCP verifier reads against the
  committed values (it does, since the prover opens exactly the logged positions);
* `hbatch` — the batch opening verifies (vector-commitment correctness); and
* `haccept` — the PCP verifier accepts the committed proof (PCP completeness).

The novel content is the `claimAnswer_run` replay: the verifier's failing `OptionT` replay against
the openings reproduces the bare PCP run, so it accepts exactly when the PCP run does. -/
theorem KilianTransformation_verify_eq_true
    (pcp : PCP Stmt Wit rel) [DecidableEq pcp.Symbol]
    {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment m (Fin pcp.length) pcp.Symbol Commit State BatchOpening)
    (boolRel : Stmt → Wit → Bool)
    (x : Stmt) (c : Commit) (st : State) (coins : pcp.Coins) (op : BatchOpening)
    (queried : List (Fin pcp.length))
    (hcov : pathLog (bovc.decode st) (pcp.Verifier x coins) ⊆ queried)
    (hbatch : bovc.verifyBatch c (queried.map fun i => (i, bovc.decode st i)) op = true)
    (haccept : evalWithAnswerFn (QueryImpl.ofFn (bovc.decode st)) (pcp.Verifier x coins) = true) :
    (KilianTransformation pcp bovc boolRel).verify x c coins
      (queried.map (fun i => (i, bovc.decode st i)), op) = true := by
  have hreplay := claimAnswer_run (bovc.decode st)
    (queried.map fun i => (i, bovc.decode st i)) (pcp.Verifier x coins)
    (fun t ht => claimAnswer_map (bovc.decode st) queried t (hcov ht))
  change (bovc.verifyBatch c (queried.map fun i => (i, bovc.decode st i)) op
      && decide (Id.run ((simulateQ (claimAnswer (queried.map fun i => (i, bovc.decode st i)))
        (pcp.Verifier x coins)).run) = some true)) = true
  rw [hbatch, hreplay, haccept]; rfl

end Completeness
