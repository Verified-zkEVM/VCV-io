/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import VCVio.CryptoFoundations.VectorCommitment.Basic
import VCVio.CryptoFoundations.ChallengeVerifyProtocol.Basic
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.LoggingOracle
import ToMathlib.Data.List.Lookup

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

/-- A **Probabilistically Checkable Proof (PCP)** system for a relation `rel : Stmt → Wit → Bool`.

  The honest prover turns a statement and witness into a proof string of `length` symbols over the
  alphabet `Symbol`.

  The verifier draws random coins of type `Coins` (sampled by `sampleCoins`); *given* its coins it
  is the deterministic oracle computation `Verifier stmt coins`, which adaptively queries positions
  of the proof string (modeled by `Fin length →ₒ Symbol`) and outputs a single accept/reject bit.

  Separating the coins from the proof queries — rather than folding both into a single
  `OracleComp (unifSpec + (Fin length →ₒ Symbol))` — matches the public-coin structure used by the
  Kilian transformation: the verifier *sends* its coins, and the prover then simulates `Verifier
  stmt coins` to learn exactly which positions to open. -/
structure PCP (Stmt Wit : Type) where
  Symbol : Type
  [finSymbol : Fintype Symbol]
  length : ℕ
  Coins : Type
  sampleCoins : ProbComp Coins
  Prover : Stmt → Wit → ProbComp (List.Vector Symbol length)
  Verifier : Stmt → Coins → OracleComp (Fin length →ₒ Symbol) Bool

namespace PCP

open scoped NNReal

variable {Stmt Wit : Type}

/-- Run the PCP verifier on statement `stmt` with fixed coins `coins` against a concrete proof
  string `proof`, answering each oracle query for position `i` with `proof.get i`. Since the coins
  are fixed and the proof is concrete, the result is a deterministic accept/reject bit. -/
def runVerifier (pcp : PCP Stmt Wit) (stmt : Stmt) (coins : pcp.Coins)
    (proof : List.Vector pcp.Symbol pcp.length) : Bool :=
  Id.run <| simulateQ (QueryImpl.ofListVector proof) (pcp.Verifier stmt coins)

/-- A PCP system satisfies **correctness** with error `correctnessError` if for every
  statement/witness pair `(stmt, wit)` in the relation, the honest verifier accepts a proof
  produced by the honest prover with probability at least `1 - correctnessError`. -/
noncomputable def correctness (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    (correctnessError : ℝ≥0) : Prop :=
  ∀ stmt : Stmt,
  ∀ wit : Wit,
    rel stmt wit →
      Pr[ fun accept => accept | do
          let proof ← pcp.Prover stmt wit
          let coins ← pcp.sampleCoins
          return pcp.runVerifier stmt coins proof] ≥ 1 - correctnessError

/-- A PCP system satisfies **perfect correctness** if it satisfies correctness with no error. -/
noncomputable def perfectCorrectness (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool) : Prop :=
  pcp.correctness rel 0

/-- A PCP system satisfies **soundness** with error `soundnessError` if for every statement `stmt`
  outside the language (i.e. with no valid witness), and every adversarially chosen proof string,
  the verifier accepts with probability at most `soundnessError`.

  Since the verifier's only source of randomness is its own coin tosses, it suffices to quantify
  over fixed proof strings: a randomized malicious prover is a convex combination of these, so it
  can do no better than the best fixed proof. -/
noncomputable def soundness (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ stmt : Stmt,
    (¬ ∃ wit : Wit, rel stmt wit) →
  ∀ proof : List.Vector pcp.Symbol pcp.length,
    Pr[ fun accept => accept | do
        let coins ← pcp.sampleCoins
        return pcp.runVerifier stmt coins proof] ≤ soundnessError

/-- A PCP system satisfies **perfect soundness** if it satisfies soundness with no error, i.e. the
  verifier never accepts a proof for a statement outside the language. -/
noncomputable def perfectSoundness (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool) : Prop :=
  pcp.soundness rel 0

-- TODO: Definition 19.1.3. straightline knowledge soundness error with extraction time

end PCP

section ReadLog

/-! ## Read-log of a deterministic oracle computation

`pathLog so comp` is the list of inputs that `comp` queries, in the order it reads them, when its
oracles are answered by the handler `so`. It is the input-only projection of the generic query log
produced by `QueryImpl.withLogging`: each query/response pair `⟨t, u⟩` is recorded, and `pathLog`
keeps only the inputs `t`. The Kilian prover uses it to discover exactly which proof positions the
verifier reads. -/

universe u

variable {ι : Type u} {spec : OracleSpec ι}

/-- The inputs a deterministic computation queries when its oracles are answered by `so`, in the
order they are read: the `QueryImpl.withLogging` query log with each entry's response discarded. -/
def pathLog (so : QueryImpl spec Id) {α : Type u} (comp : OracleComp spec α) : List ι :=
  ((simulateQ so.withLogging comp).run.2).map Sigma.fst

/-- A query records its input at the head of the read-log and then continues: `withLogging` appends
`⟨t, so t⟩` for the query, so projecting to inputs prepends `t`. -/
theorem pathLog_query (so : QueryImpl spec Id) {α : Type u} (t : spec.Domain)
    (oa : spec.Range t → OracleComp spec α) :
    pathLog so (liftM (spec.query t) >>= oa) = t :: pathLog so (oa (so t)) := by
  unfold pathLog
  simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.withLogging_apply,
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

variable {ι Sym : Type*}

/-- Implement oracle by
looking up an input among the claimed `(input, value)` pairs, failing if absent. This is the
verifier's per-query handler in `KilianTransformation.verify`. It is `QueryImpl.ofFn?` over the
association-list lookup `claims.lookup`, using that `QueryImpl spec Option` is `QueryImpl spec
(OptionT Id)`. -/
def claimAnswer [BEq ι] (claims : List (ι × Sym)) : QueryImpl (ι →ₒ Sym) (OptionT Id) :=
  QueryImpl.ofFn? (claims.lookup ·)

end AnswerFunctions

section KilianTransformation

variable {Stmt Wit : Type}

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
    (pcp : PCP Stmt Wit) [BEq pcp.Symbol]
    {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment m (Fin pcp.length) pcp.Symbol Commit State BatchOpening)
    (rel : Stmt → Wit → Bool) :
    ChallengeVerifyProtocol Stmt Wit
      Commit                                                  -- Commit: the vector commitment
      State                                                   -- PrvState: the opener's state
      pcp.Coins                                               -- Chal: the verifier's coins
      (List (Fin pcp.length × pcp.Symbol) × BatchOpening)     -- Resp: claims + batch opening
      rel m where
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
      (Id.run (simulateQ (claimAnswer claims) (pcp.Verifier stmt coins)).run == some true)

end KilianTransformation

section ReplayInfrastructure

/-! ## Deterministic replay infrastructure

The completeness of the Kilian transformation rests on a deterministic fact about the verifier:
the prover's logging simulation (which records the inputs the verifier reads), the verifier's own
replay against the prover's openings, and the bare run on the answer function are all the *same*
deterministic computation answered consistently. These lemmas package that fact for a fixed answer
function `f : ι → Sym` on a single-oracle spec `ι →ₒ Sym`. -/

universe u

variable {ι Sym : Type u} [BEq ι] [LawfulBEq ι]

/-- The verifier's per-query handler answers a claimed input with its value. -/
theorem claimAnswer_map (f : ι → Sym) (L : List ι) (t : ι) (ht : t ∈ L) :
    claimAnswer (L.map (fun i => (i, f i))) t = (pure (f t) : OptionT Id Sym) := by
  simp only [claimAnswer, QueryImpl.ofFn?, List.map_lookup f t L ht]
  rfl

omit [LawfulBEq ι] in
/-- **Replay lemma.** If the claims answer every input the verifier reads (under `f`) with `f`'s
value, the verifier's `OptionT` replay never fails and reproduces the pure run. -/
theorem claimAnswer_run (f : ι → Sym) (claims : List (ι × Sym)) {β : Type u}
    (comp : OracleComp (ι →ₒ Sym) β) :
    (∀ t ∈ pathLog f comp, claimAnswer claims t = (pure (f t) : OptionT Id Sym)) →
      (simulateQ (claimAnswer claims) comp).run
        = some (evalWithAnswerFn (QueryImpl.ofFn f) comp) := by
  induction comp using OracleComp.inductionOn with
  | pure x => intro _; rfl
  | query_bind t oa ih =>
    intro h
    have ht : claimAnswer claims t = (pure (f t) : OptionT Id Sym) :=
      h t (by rw [pathLog_query]; exact List.mem_cons_self ..)
    have hq : evalWithAnswerFn (QueryImpl.ofFn f) (liftM ((ι →ₒ Sym).query t)) = f t := by
      change simulateQ (QueryImpl.ofFn f) (liftM ((ι →ₒ Sym).query t)) = f t
      rw [simulateQ_spec_query]; rfl
    simp only [simulateQ_bind, simulateQ_spec_query, ht, evalWithAnswerFn_bind, hq]
    exact ih (f t) (fun t' ht' => h t' (by rw [pathLog_query]; exact List.mem_cons_of_mem _ ht'))

end ReplayInfrastructure

section Completeness

variable {Stmt Wit : Type} {rel : Stmt → Wit → Bool}

/-- **Deterministic completeness core.** For a fixed honestly committed state `st` and coins, the
Kilian verifier accepts the honest prover's response, provided:

* `hcov` — the opened set `queried` covers every position the PCP verifier reads against the
  committed values (it does, since the prover opens exactly the logged positions);
* `hbatch` — the batch opening verifies (vector-commitment correctness); and
* `haccept` — the PCP verifier accepts the committed proof (PCP completeness).

The novel content is the `claimAnswer_run` replay: the verifier's failing `OptionT` replay against
the openings reproduces the bare PCP run, so it accepts exactly when the PCP run does. -/
theorem KilianTransformation_verify_eq_true
    (pcp : PCP Stmt Wit) [BEq pcp.Symbol]
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
      && (Id.run ((simulateQ (claimAnswer (queried.map fun i => (i, bovc.decode st i)))
        (pcp.Verifier x coins)).run) == some true)) = true
  rw [hbatch, hreplay, haccept]; rfl

/-- Running the PCP verifier on a concrete proof string is the same as evaluating it with the
answer function that reads each position out of that string. This bridges the `runVerifier`
vocabulary of PCP correctness with the `evalWithAnswerFn` form consumed by the deterministic
core. -/
theorem runVerifier_eq_evalWithAnswerFn
    (pcp : PCP Stmt Wit) (stmt : Stmt) (coins : pcp.Coins)
    (proof : List.Vector pcp.Symbol pcp.length) :
    pcp.runVerifier stmt coins proof
      = evalWithAnswerFn (QueryImpl.ofFn proof.get) (pcp.Verifier stmt coins) :=
  rfl

/-- Ordinary PCP completeness (`pcp.perfectCorrectness`) delivers the acceptance condition consumed
by `KilianTransformation_perfectlyComplete`, namely that every proof the honest prover can produce
in `m` passes the PCP verifier on every challenge it can sample in `m`.

Two side conditions bridge the gap between PCP completeness (stated over `ProbComp`) and the ambient
monad `m`:

* `hrel` — the protocol's boolean relation refines the PCP relation, so a valid protocol instance
  is a valid PCP instance;
* `hlift` — lifting a `ProbComp` into `m` does not enlarge its support. This is the coherence of
  the public-randomness lift; it cannot be derived from the bare `MonadLiftT ProbComp m` (the lift
  could *a priori* interpret sampling differently from `ProbComp`), so it is required explicitly.
  It holds by `rfl` for `m := ProbComp` and for any faithful lift. -/
theorem perfectCorrectness_accepts_liftedProver
    (pcp : PCP Stmt Wit)
    {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (rel : Stmt → Wit → Bool)
    (hlift : ∀ {β : Type} (mx : ProbComp β), support (liftM mx : m β) ⊆ support mx)
    (hpcp : pcp.perfectCorrectness rel) :
    ∀ x w, rel x w →
      ∀ proof ∈ support (liftM (pcp.Prover x w) : m (List.Vector pcp.Symbol pcp.length)),
      ∀ coins ∈ support (liftM pcp.sampleCoins : m pcp.Coins),
        pcp.runVerifier x coins proof = true := by
  intro x w hxw proof hproof coins hcoins
  unfold PCP.perfectCorrectness PCP.correctness at hpcp
  have hpr := hpcp x w hxw
  simp only [ENNReal.coe_zero, tsub_zero, ge_iff_le] at hpr
  have h1 := le_antisymm probEvent_le_one hpr
  rw [probEvent_eq_one_iff] at h1
  refine h1.2 _ ?_
  rw [mem_support_bind_iff]
  refine ⟨pcp.runVerifier x coins proof, ?_, by rw [support_pure]; rfl⟩
  rw [mem_support_bind_iff]
  refine ⟨proof, hlift _ hproof, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨coins, hlift _ hcoins, by rw [support_pure]; rfl⟩

/-- Perfect PCP completeness already forces the honest prover and coin sampler never to fail: any
positive failure probability inside `do proof ← Prover; coins ← sampleCoins; …` would pull the
acceptance probability below one. So the never-failing of these honest `ProbComp` computations is
*derived* from `pcp.perfectCorrectness`, never assumed — there is no need to take it as a separate
hypothesis. -/
theorem neverFail_of_perfectCorrectness
    (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    (hpcp : pcp.perfectCorrectness rel) {x : Stmt} {w : Wit} (hxw : rel x w) :
    NeverFail (pcp.Prover x w) ∧ NeverFail pcp.sampleCoins := by
  unfold PCP.perfectCorrectness PCP.correctness at hpcp
  have hpr := hpcp x w hxw
  simp only [ENNReal.coe_zero, tsub_zero, ge_iff_le] at hpr
  have h1 := le_antisymm probEvent_le_one hpr
  rw [probEvent_eq_one_iff] at h1
  obtain ⟨hinner, -⟩ := (probFailure_bind_eq_zero_iff _ _).mp h1.1
  obtain ⟨hProverF, hRest⟩ := (probFailure_bind_eq_zero_iff _ _).mp hinner
  refine ⟨⟨hProverF⟩, ?_⟩
  have hne : (support (pcp.Prover x w)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ne_eq, ← probFailure_eq_one_iff, hProverF]
    exact zero_ne_one
  obtain ⟨proof, hproof⟩ := hne
  exact ⟨((probFailure_bind_eq_zero_iff _ _).mp (hRest proof hproof)).1⟩

/-- **Perfect completeness of the Kilian transformation.** If the underlying batch-opening vector
commitment is complete (perfectly correct) and faithfully decodes its committed vector, and the PCP
is complete (its honest prover's proof is accepted on every sampled coin set), then the resulting
interactive argument is perfectly complete: the honest prover always convinces the verifier.

The hypotheses isolate the moving parts:

* `hbovc` — the batch-opening vector commitment is complete: an honest commitment opens its
  decoded claims to a batch opening that verifies;
* `hdecode` — the committer's state decodes to exactly the vector it committed to;
* `hpcp` — the PCP is complete (`pcp.perfectCorrectness`); together with `hfaithful` (lifting
  `ProbComp` into `m` preserves the distribution) this gives, via
  `perfectCorrectness_accepts_liftedProver`, that the honest proof is accepted on every sampled coin
  set, and (via `neverFail_of_perfectCorrectness`) that the honest prover and sampler never fail;
* `hCommit` / `hOpen` — the commitment's own operations never fail. These are genuinely independent:
  perfect correctness of `bovc` is vacuous if `openBatch` always fails, so it cannot supply them.

The deterministic content lives in `KilianTransformation_verify_eq_true`; here we lift it across the
probabilistic structure, showing the transcript distribution is supported entirely on `true`. -/
theorem KilianTransformation_perfectlyComplete
    (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool) [BEq pcp.Symbol]
    {m : Type → Type} [Monad m] [LawfulMonad m] [MonadLiftT ProbComp m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    {Commit State BatchOpening : Type}
    (bovc : BatchOpeningVectorCommitment m (Fin pcp.length) pcp.Symbol Commit State BatchOpening)
    (hbovc : bovc.PerfectlyCorrect)
    (hdecode : ∀ (data : Fin pcp.length → pcp.Symbol) (c : Commit) (st : State),
      (c, st) ∈ support (bovc.commit data) → bovc.decode st = data)
    (hpcp : pcp.perfectCorrectness rel)
    (hfaithful : ∀ {β : Type} (mx : ProbComp β), 𝒟[(liftM mx : m β)] = 𝒟[mx])
    (hCommit : ∀ data, NeverFail (bovc.commit data))
    (hOpen : ∀ st is, NeverFail (bovc.openBatch st is)) :
    (KilianTransformation pcp bovc rel).PerfectlyComplete := by
  have hlift : ∀ {β : Type} (mx : ProbComp β), support (liftM mx : m β) ⊆ support mx := by
    intro β mx z hz
    rw [mem_support_iff_evalDist_apply_ne_zero] at hz ⊢
    rwa [hfaithful mx] at hz
  have transport : ∀ {β : Type} (mx : ProbComp β), NeverFail mx → NeverFail (liftM mx : m β) := by
    intro β mx h
    rw [neverFail_iff]
    unfold probFailure
    rw [hfaithful mx]
    exact (neverFail_iff _).mp h
  have hAccept := perfectCorrectness_accepts_liftedProver pcp rel hlift hpcp
  intro x w hxw
  rw [probOutput_eq_one_iff_forall]
  refine ⟨?_, ?_⟩
  · -- The honest transcript never fails: prover/sampler by completeness, the rest by hCommit/hOpen.
    obtain ⟨hProver0, hSample0⟩ := neverFail_of_perfectCorrectness pcp rel hpcp hxw
    have hProver := transport _ hProver0
    have hSample := transport _ hSample0
    rw [← neverFail_iff]
    simp only [KilianTransformation, neverFail_bind_iff, hProver, hSample, hCommit, hOpen,
      NeverFail.instPure, implies_true, and_self]
  · -- Every honest transcript makes the verifier accept.
    intro y hy
    simp only [KilianTransformation, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hy
    obtain ⟨⟨pc, sc⟩, ⟨proof, hproof, hcommit⟩, coins, hcoins, _, ⟨op, hop, rfl⟩, rfl⟩ :=
      hy
    have hdec : bovc.decode sc = proof.get := hdecode proof.get pc sc hcommit
    refine KilianTransformation_verify_eq_true pcp bovc rel x pc sc coins op _
      (List.subset_dedup _) ?_ ?_
    · exact hbovc proof.get _ pc sc hcommit op hop
    · rw [hdec, ← runVerifier_eq_evalWithAnswerFn]
      exact hAccept x w hxw proof hproof coins hcoins

end Completeness
