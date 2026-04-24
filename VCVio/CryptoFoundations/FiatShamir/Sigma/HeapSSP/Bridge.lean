/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Games
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.HeapSSP.Advantage
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.StateProjection

/-!
# Bridge between `unforgeableExp` and `cmaReal.runProb` (HeapSSP)

Ties the existing `SignatureAlg.unforgeableAdv`-based EUF-CMA experiment
for the Fiat-Shamir scheme to the HeapSSP `cmaReal` game
(`Sigma/HeapSSP/Games.lean`). Contributes hops H1 and H2 of the SSP plan:

* **H1 (drop-fresh)**: wraps
  `SignatureAlg.unforgeableAdv.advantage_le_unforgeableExpNoFresh` for
  the FS scheme. Independent of the internal state representation.
* **H2 (`unforgeableExp` ↔ `cmaReal.runProb`)**: expresses the
  unforgeability experiment as `cmaReal.runState`-with-post-check, with
  the signed-message log read off `cmaReal`'s `.inl .log` heap cell.

The `cmaReal.impl` is monolithic (single
`QueryImpl cmaSpec (StateT (Heap CmaCells) …)`), so the
`pkSpec`-factoring helper lemmas are phrased directly on
`(cmaReal.impl (Sum.inr ()))` rather than on a dedicated sub-handler.
-/

universe u v

open OracleSpec OracleComp ProbComp VCVio.HeapSSP

namespace FiatShamir.HeapSSP

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit]
variable [SampleableType Chal]

/-! ### HeapSSP-side adversary -/

/-- Candidate-producing part of the HeapSSP CMA adversary after the public
key is fixed. This is the source adversary's `main` computation lifted into
`cmaSpec`, before the final Fiat-Shamir verification query. -/
@[reducible] noncomputable def postKeygenCandidateAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)) :=
  (liftM (adv.main pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)))

/-- Candidate-producing HeapSSP adversary. It fetches the lazy public key
from `pkSpec`, then runs the source adversary, but deliberately does not run
the final Fiat-Shamir verifier. Factoring the game this way lets H3 count
only the adversary's live hash queries; verification is a no-sign-cost suffix. -/
@[reducible] noncomputable def candidateAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) (Stmt × (M × (Commit × Resp))) := do
  let pk ← (((cmaSpec M Commit Chal Resp Stmt).query (Sum.inr ())) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Stmt)
  let out ← postKeygenCandidateAdv (σ := σ) (hr := hr) (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk
  pure (pk, out)

/-- Lift a CMA-style `unforgeableAdv` for the Fiat-Shamir scheme into an
adversary against the HeapSSP `cmaReal` game.

The wrapper:
1. Issues a `pkSpec` query to obtain the public key from `cmaReal`'s
   lazily-sampled keypair (stored in the `.inr .keypair` cell).
2. Lifts the source adversary's `main pk` into `OracleComp cmaSpec ...`
   via the canonical `(unifSpec + roSpec) + signSpec ⊂ₒ cmaSpec`
   `SubSpec` embedding.
3. Runs FS verification, which issues one further `roSpec` query
   through the same RO cache (in `.inr .roCache`).
4. Returns the forgery paired with the verification bit. The freshness
   post-check is read off `cmaReal`'s log cell externally
   (see `cmaRealRun`). -/
@[reducible] noncomputable def signedAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) ((M × (Commit × Resp)) × Bool) := do
  let pk ← (((cmaSpec M Commit Chal Resp Stmt).query (Sum.inr ())) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Stmt)
  let (msg, sig) ← (liftM (adv.main pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)))
  let verified ← (liftM
    ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
      pk msg sig) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure ((msg, sig), verified)

/-- Instrument a `cmaSpec` computation with a local list of signing-query
messages while forwarding every query to the surrounding `cmaSpec`.

This is deliberately adversary-side logging: it records the signing queries
visible in the syntax of the adversary computation, not the package's private
heap log. Keeping this log in the output lets the H3 Boolean-output bridge
reason about freshness without a separate final-state event theorem. -/
@[reducible] noncomputable def cmaSignLogImpl :
    QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (List M) (OracleComp (cmaSpec M Commit Chal Resp Stmt)))
  | Sum.inl (Sum.inl (Sum.inl n)) => do
      let r ← (((cmaSpec M Commit Chal Resp Stmt).query
        (Sum.inl (Sum.inl (Sum.inl n)))) :
          OracleComp (cmaSpec M Commit Chal Resp Stmt) (Fin (n + 1)))
      pure r
  | Sum.inl (Sum.inl (Sum.inr mc)) => do
      let r ← (((cmaSpec M Commit Chal Resp Stmt).query
        (Sum.inl (Sum.inl (Sum.inr mc)))) :
          OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)
      pure r
  | Sum.inl (Sum.inr m) => do
      let signed ← get
      let sig ← (((cmaSpec M Commit Chal Resp Stmt).query (Sum.inl (Sum.inr m))) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) (Commit × Resp))
      set (signed ++ [m])
      pure sig
  | Sum.inr () => do
      let pk ← (((cmaSpec M Commit Chal Resp Stmt).query (Sum.inr ())) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) Stmt)
      pure pk

/-- Log signing queries while producing the final candidate, but still before
running verification. The output carries the public key so that verification can
be attached later as an ordinary continuation. -/
@[reducible] noncomputable def signedCandidateAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt)
      ((Stmt × (M × (Commit × Resp))) × List M) := do
  (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) (Stmt := Stmt)) (candidateAdv σ hr M adv)).run []

/-- Freshness and verification check attached after candidate production. This
continuation performs the one verifier random-oracle query but no signing query,
so it does not contribute to the H3 sign-replacement cost. -/
@[reducible] noncomputable def verifyFreshComp
    (p : (Stmt × (M × (Commit × Resp))) × List M) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool := do
  let pk := p.1.1
  let out := p.1.2
  let signed := p.2
  let verified ← (liftM
    ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
      pk out.1 out.2) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure (!decide (out.1 ∈ signed) && verified)

/-- Freshness-preserving Boolean adversary for the HeapSSP CMA chain.

It first produces a locally signed-query-logged candidate, then performs the
final Fiat-Shamir verification as a suffix. This is semantically the same
Boolean event as running `signedAdv` under the logger, but the factored shape
keeps the verifier's single hash query out of the H3 cache-growth budget. -/
@[reducible] noncomputable def signedFreshAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool :=
  signedCandidateAdv σ hr M adv >>= verifyFreshComp (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)

/-! ### Query-bound transport for the HeapSSP CMA adversary wrappers -/

/-- Joint signing/hash query admissibility for `cmaSpec`.

Uniform and public-key queries are free, random-oracle queries require
positive hash budget, and signing queries require positive signing
budget. -/
def cmaSignHashCanQuery :
    (cmaSpec M Commit Chal Resp Stmt).Domain → ℕ × ℕ → Prop
  | .inl (.inl (.inl _)), _ => True
  | .inl (.inl (.inr _)), (_, qH') => 0 < qH'
  | .inl (.inr _), (qS', _) => 0 < qS'
  | .inr _, _ => True

/-- Joint signing/hash query budget update for `cmaSpec`.

Uniform and public-key queries leave the budget unchanged, random-oracle
queries decrement the hash coordinate, and signing queries decrement the
signing coordinate. -/
def cmaSignHashCost :
    (cmaSpec M Commit Chal Resp Stmt).Domain → ℕ × ℕ → ℕ × ℕ
  | .inl (.inl (.inl _)), b => b
  | .inl (.inl (.inr _)), (qS', qH') => (qS', qH' - 1)
  | .inl (.inr _), (qS', qH') => (qS' - 1, qH')
  | .inr _, b => b

/-- Joint signing/hash query bound for computations over `cmaSpec`.

Uniform and public-key queries are free, signing queries decrement the
first coordinate, and random-oracle queries decrement the second
coordinate. -/
def cmaSignHashQueryBound {α : Type}
    (oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (qS qH : ℕ) : Prop :=
  OracleComp.IsQueryBound oa (qS, qH)
    (cmaSignHashCanQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt))
    (cmaSignHashCost (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt))

omit [SampleableType Stmt] [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
@[simp]
lemma cmaSignHashQueryBound_query_bind_iff {α : Type}
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (oa : (cmaSpec M Commit Chal Resp Stmt).Range t →
      OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (qS qH : ℕ) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (liftM ((cmaSpec M Commit Chal Resp Stmt).query t) >>= oa) qS qH ↔
      cmaSignHashCanQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t (qS, qH) ∧
      ∀ u,
        cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt) (oa u)
          ((cmaSignHashCost (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt) t (qS, qH)).1)
          ((cmaSignHashCost (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt) t (qS, qH)).2) := by
  simpa [cmaSignHashQueryBound] using
    (OracleComp.isQueryBound_query_bind_iff
      (spec := cmaSpec M Commit Chal Resp Stmt) (α := α) (t := t)
      (mx := oa) (b := (qS, qH))
      (canQuery := cmaSignHashCanQuery (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
      (cost := cmaSignHashCost (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt)))

omit [SampleableType Stmt] [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
@[simp]
lemma cmaSignHashQueryBound_query_iff
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain) (qS qH : ℕ) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (liftM ((cmaSpec M Commit Chal Resp Stmt).query t)) qS qH ↔
      cmaSignHashCanQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t (qS, qH) := by
  simp [cmaSignHashQueryBound]

omit [DecidableEq M] [DecidableEq Commit]
  [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] in
lemma cmaSignHashQueryBound_pure {α : Type} (x : α) (qS qH : ℕ) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (pure x : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
      qS qH :=
  trivial

omit [SampleableType Stmt] [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
lemma cmaSignHashQueryBound_mono {α : Type}
    {oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α}
    {qS₁ qH₁ qS₂ qH₂ : ℕ}
    (h : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) oa qS₁ qH₁)
    (hS : qS₁ ≤ qS₂) (hH : qH₁ ≤ qH₂) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) oa qS₂ qH₂ := by
  induction oa using OracleComp.inductionOn generalizing qS₁ qH₁ qS₂ qH₂ with
  | pure x =>
      trivial
  | query_bind t cont ih =>
      rw [cmaSignHashQueryBound_query_bind_iff] at h ⊢
      rcases h with ⟨hcan, hcont⟩
      rcases t with ((n | mc) | m) | ⟨⟩
      · exact ⟨trivial, fun u => ih u (hcont u) hS hH⟩
      · exact ⟨Nat.lt_of_lt_of_le hcan hH, fun u =>
          ih u (hcont u) hS (Nat.sub_le_sub_right hH 1)⟩
      · exact ⟨Nat.lt_of_lt_of_le hcan hS, fun u =>
          ih u (hcont u) (Nat.sub_le_sub_right hS 1) hH⟩
      · exact ⟨trivial, fun u => ih u (hcont u) hS hH⟩

omit [SampleableType Stmt] [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
lemma cmaSignHashQueryBound_bind {α β : Type}
    {oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α}
    {ob : α → OracleComp (cmaSpec M Commit Chal Resp Stmt) β}
    {qS₁ qH₁ qS₂ qH₂ : ℕ}
    (h₁ : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) oa qS₁ qH₁)
    (h₂ : ∀ x, cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (ob x) qS₂ qH₂) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (oa >>= ob) (qS₁ + qS₂) (qH₁ + qH₂) := by
  induction oa using OracleComp.inductionOn generalizing qS₁ qH₁ with
  | pure x =>
      simpa [pure_bind] using
        cmaSignHashQueryBound_mono (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt) (oa := ob x) (h := h₂ x)
          (hS := by omega) (hH := by omega)
  | query_bind t cont ih =>
      rw [cmaSignHashQueryBound_query_bind_iff] at h₁
      rw [bind_assoc, cmaSignHashQueryBound_query_bind_iff]
      rcases h₁ with ⟨hcan, hcont⟩
      rcases t with ((n | mc) | m) | ⟨⟩
      · refine ⟨trivial, fun u => ?_⟩
        simpa [cmaSignHashCost] using ih u (hcont u)
      · refine ⟨Nat.add_pos_left hcan qH₂, fun u => ?_⟩
        have hrec := ih u (hcont u)
        have hEq : qH₁ - 1 + qH₂ = qH₁ + qH₂ - 1 := by
          calc
            qH₁ - 1 + qH₂ = qH₂ + (qH₁ - 1) := Nat.add_comm _ _
            _ = qH₂ + qH₁ - 1 :=
              (Nat.add_sub_assoc (Nat.succ_le_of_lt hcan) qH₂).symm
            _ = qH₁ + qH₂ - 1 := by rw [Nat.add_comm qH₂ qH₁]
        simpa [cmaSignHashCost, hEq] using hrec
      · refine ⟨Nat.add_pos_left hcan qS₂, fun u => ?_⟩
        have hrec := ih u (hcont u)
        have hEq : qS₁ - 1 + qS₂ = qS₁ + qS₂ - 1 := by
          calc
            qS₁ - 1 + qS₂ = qS₂ + (qS₁ - 1) := Nat.add_comm _ _
            _ = qS₂ + qS₁ - 1 :=
              (Nat.add_sub_assoc (Nat.succ_le_of_lt hcan) qS₂).symm
            _ = qS₁ + qS₂ - 1 := by rw [Nat.add_comm qS₂ qS₁]
        simpa [cmaSignHashCost, hEq] using hrec
      · refine ⟨trivial, fun u => ?_⟩
        simpa [cmaSignHashCost] using ih u (hcont u)

/-! ### Joint output of `cmaReal` -/

/-- Run `cmaReal` against `signedAdv` and pack the resulting forgery,
verification bit, and signed-message log into a single `ProbComp`.

The signed-message log lives in `cmaReal`'s `.inl .log` heap cell and
is the freshness witness that `unforgeableExp` carries in a `WriterT`
instead. -/
@[reducible] noncomputable def cmaRealRun
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    ProbComp ((M × (Commit × Resp)) × Bool × List M) := do
  let p ← (cmaReal M Commit Chal σ hr).runState (signedAdv σ hr M adv)
  pure (p.1.1, p.1.2, p.2 (Sum.inl .log))

/-! ### Fixed-key post-keygen experiment -/

/-- The post-keygen adversary/verification computation over the public
Fiat-Shamir oracle interface `unifSpec + roSpec + signSpec`, before it is
lifted into the HeapSSP `cmaSpec` by re-adding `pkSpec`. -/
@[reducible] noncomputable def postKeygenAdvBase
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) :
    OracleComp (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
        : OracleSpec _)
      ((M × (Commit × Resp)) × Bool) := do
  let (msg, sig) ← adv.main pk
  let verified ← liftM
    ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
      pk msg sig)
  pure ((msg, sig), verified)

/-- The public random-oracle runtime for the fixed-key post-keygen experiment,
viewed as a `QueryRuntime` with explicit cache state. -/
@[reducible] noncomputable def fsBaseRuntime :
    QueryRuntime (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) where
  impl := unifFwdImpl (M × Commit →ₒ Chal) +
    (randomOracle : QueryImpl (M × Commit →ₒ Chal) _)

/-- The public signing oracle for a fixed keypair, interpreted directly in the
explicit cache-state random-oracle runtime. -/
@[reducible] noncomputable def postKeygenSignCore (pk : Stmt) (sk : Wit) :
    QueryImpl (M →ₒ (Commit × Resp))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := by
  letI : HasQuery (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    (randomOracle : QueryImpl (M × Commit →ₒ Chal) _).toHasQuery
  exact
    (FiatShamir (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) σ hr M).sign
      pk sk

/-- The public post-keygen adversary handler with signing-query input logging.

Base queries (`unifSpec + roSpec`) run through the explicit cache-state runtime;
signing queries are handled by the fixed-key Fiat-Shamir signing oracle while
appending each queried message to a `StateT` list. -/
@[reducible] noncomputable def postKeygenAppendImpl (pk : Stmt) (sk : Wit) :
    QueryImpl (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
        : OracleSpec _)
      (StateT (List M)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) := by
  letI : HasQuery (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    (fsBaseRuntime (M := M) (Commit := Commit) (Chal := Chal)).toHasQuery
  let baseS : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT (List M)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
    (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
      (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)).liftTarget _
  exact baseS +
    QueryImpl.appendInputLog
      (postKeygenSignCore (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)

/-- Fixed-key specialization of the generic WriterT-to-StateT signing-log
bridge, in the explicit cache-state Fiat-Shamir runtime. -/
private theorem postKeygenWriterLog_eq_inputLog
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) :
    let runtime := fsBaseRuntime (M := M) (Commit := Commit) (Chal := Chal)
    letI : HasQuery (unifSpec + (M × Commit →ₒ Chal))
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := runtime.toHasQuery
    let so := postKeygenSignCore (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk
    let baseW : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
        (WriterT (QueryLog (M →ₒ (Commit × Resp)))
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
      (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
        (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)).liftTarget _
    let implW : QueryImpl (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
        : OracleSpec _)
        (WriterT (QueryLog (M →ₒ (Commit × Resp)))
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
      baseW + QueryImpl.withLogging so
    ((fun z : (M × (Commit × Resp)) × QueryLog (M →ₒ (Commit × Resp)) =>
        (z.1, z.2.map (fun e => e.1))) <$>
        ((simulateQ implW (adv.main pk)).run :
          StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
            ((M × (Commit × Resp)) × QueryLog (M →ₒ (Commit × Resp))))) =
      ((simulateQ
          (postKeygenAppendImpl (σ := σ) (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
          (adv.main pk)).run [] :
        StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
          ((M × (Commit × Resp)) × List M)) := by
  let runtime := fsBaseRuntime (M := M) (Commit := Commit) (Chal := Chal)
  letI : HasQuery (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := runtime.toHasQuery
  let so := postKeygenSignCore (σ := σ) (hr := hr) (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk
  simpa [postKeygenAppendImpl, runtime, so] using
    (QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
      (spec₀ := unifSpec + (M × Commit →ₒ Chal))
      (loggedSpec := (M →ₒ (Commit × Resp)))
      (m₀ := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)
      so (adv.main pk) ([] : List M))

/-- The fixed-key public post-keygen experiment in the explicit
`List M × QueryCache` stateful runtime. -/
@[reducible] noncomputable def postKeygenFreshProb
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) : ProbComp Bool := by
  letI : HasQuery (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    (randomOracle : QueryImpl (M × Commit →ₒ Chal) _).toHasQuery
  exact
    (((simulateQ
        (postKeygenAppendImpl (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
        (adv.main pk)).run [] >>= fun z => do
          let msg := z.1.1
          let sig := z.1.2
          let signed := z.2
          let verified ←
            (FiatShamir (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) σ hr M).verify
              pk msg sig
          pure (!decide (msg ∈ signed) && verified)).run' ∅)

/-! ### Bridge equalities

Factor out the lazy keygen step: the first query issued by `signedAdv`
is the `pkSpec` one, so on the empty initial heap `cmaReal.impl` runs
`hr.gen` and installs the keypair in the `.inr .keypair` cell. Every
subsequent query sees the same keypair. -/

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The `pkSpec` branch of `cmaReal.impl` on a heap with `.keypair = none`
calls `hr.gen` and updates the `.keypair` cell. -/
private lemma cmaReal_impl_pkSpec_none_run
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (hkp : h (Sum.inr .keypair) = none) :
    (((cmaReal M Commit Chal σ hr).impl (Sum.inr () :
        (cmaSpec M Commit Chal Resp Stmt).Domain))).run h =
      hr.gen >>= fun ps : Stmt × Wit =>
        pure (ps.1, h.update (Sum.inr .keypair) (some (ps.1, ps.2))) := by
  simp only [cmaReal, StateT.run_mk, hkp]
  rfl

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The `pkSpec` branch of `cmaReal.impl` on a heap with `.keypair = some (pk, sk)`
returns the public key without touching the heap. -/
private lemma cmaReal_impl_pkSpec_some_run
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (pk : Stmt) (sk : Wit)
    (hkp : h (Sum.inr .keypair) = some (pk, sk)) :
    (((cmaReal M Commit Chal σ hr).impl (Sum.inr () :
        (cmaSpec M Commit Chal Resp Stmt).Domain))).run h =
      pure (pk, h) := by
  simp only [cmaReal, StateT.run_mk, hkp]
  rfl

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Threading a continuation `f` through the `pkSpec` branch of
`cmaReal.impl` on an empty-keypair heap extracts the `hr.gen` step. -/
private lemma cmaReal_impl_pkSpec_bind_run_none {α : Type}
    (f : Stmt → StateT (Heap (CmaCells M Commit Chal Stmt Wit))
      (OracleComp unifSpec) α)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (hkp : h (Sum.inr .keypair) = none) :
    ((cmaReal M Commit Chal σ hr).impl
        (Sum.inr () : (cmaSpec M Commit Chal Resp Stmt).Domain) >>= f) h =
      hr.gen >>= fun ps : Stmt × Wit =>
        (f ps.1).run (h.update (Sum.inr .keypair) (some (ps.1, ps.2))) := by
  change ((cmaReal M Commit Chal σ hr).impl
      (Sum.inr () : (cmaSpec M Commit Chal Resp Stmt).Domain)).run h >>=
    (fun vs => (f vs.1).run vs.2) = _
  rw [cmaReal_impl_pkSpec_none_run (σ := σ) (hr := hr) (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) h hkp]
  simp

/-- The "post-keygen" portion of `signedAdv`: the adversary's main routine
followed by FS verification, with `pk` already fixed. All queries are
through `cmaSpec`; the `pkSpec` summand is never touched again. -/
@[reducible] noncomputable def postKeygenAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) ((M × (Commit × Resp)) × Bool) := do
  let (msg, sig) ← (liftM (adv.main pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)))
  let verified ← (liftM
    ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
      pk msg sig) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure ((msg, sig), verified)

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
lemma fiatShamir_verify_cmaSignHashQueryBound
    (pk : Stmt) (msg : M) (sig : Commit × Resp)
    (qS qH : ℕ) (hQ : 0 < qH) :
    cmaSignHashQueryBound (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt := Stmt)
      (liftM
        ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
          pk msg sig) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
      qS qH := by
  rcases sig with ⟨c, resp⟩
  simpa [FiatShamir, cmaSignHashCanQuery] using
    (cmaSignHashQueryBound_query_iff (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt)
      (t := Sum.inl (Sum.inl (Sum.inr (msg, c)))) qS qH).2 hQ

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
private theorem liftAdv_cmaSignHashQueryBound
    {α : Type}
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp))) α)
    (qS qH : ℕ)
    (hQ : signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := oa) qS qH) :
    cmaSignHashQueryBound (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt := Stmt)
      (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) qS qH := by
  induction oa using OracleComp.inductionOn generalizing qS qH with
  | pure x =>
      simp [cmaSignHashQueryBound]
  | query_bind t cont ih =>
      simp only [signHashQueryBound, OracleComp.isQueryBound_query_bind_iff] at hQ
      rcases hQ with ⟨hcan, hcont⟩
      rcases t with (n | mc) | m
      · simp only [liftM_bind]
        change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt)
          (liftM ((cmaSpec M Commit Chal Resp Stmt).query
              (Sum.inl (Sum.inl (Sum.inl n)))) >>= fun u =>
            (liftM (cont u) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) α))
          qS qH
        rw [cmaSignHashQueryBound_query_bind_iff]
        exact ⟨trivial, fun u => by
          simpa [cmaSignHashQueryBound] using ih u qS qH (hcont u)⟩
      · simp only [liftM_bind]
        change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt)
          (liftM ((cmaSpec M Commit Chal Resp Stmt).query
              (Sum.inl (Sum.inl (Sum.inr mc)))) >>= fun u =>
            (liftM (cont u) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) α))
          qS qH
        rw [cmaSignHashQueryBound_query_bind_iff]
        exact ⟨hcan, fun u => by
          simpa [cmaSignHashQueryBound] using ih u qS (qH - 1) (hcont u)⟩
      · simp only [liftM_bind]
        change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt)
          (liftM ((cmaSpec M Commit Chal Resp Stmt).query (Sum.inl (Sum.inr m))) >>=
            fun u =>
            (liftM (cont u) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) α))
          qS qH
        rw [cmaSignHashQueryBound_query_bind_iff]
        exact ⟨hcan, fun u => by
          simpa [cmaSignHashQueryBound] using ih u (qS - 1) qH (hcont u)⟩

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
theorem postKeygenCandidateAdv_cmaSignHashQueryBound
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (qS qH : ℕ)
    (hQ : signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (postKeygenCandidateAdv σ hr M adv pk) qS qH :=
  liftAdv_cmaSignHashQueryBound (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (oa := adv.main pk) qS qH hQ

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
theorem candidateAdv_cmaSignHashQueryBound
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (candidateAdv σ hr M adv) qS qH := by
  rw [candidateAdv]
  rw [cmaSignHashQueryBound, OracleComp.isQueryBound_query_bind_iff]
  refine ⟨trivial, fun pk => ?_⟩
  simpa [cmaSignHashQueryBound, postKeygenCandidateAdv] using
    postKeygenCandidateAdv_cmaSignHashQueryBound (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk qS qH (hQ pk)

private noncomputable def postVerifyComp
    (pk : Stmt) (x : M × (Commit × Resp)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) ((M × (Commit × Resp)) × Bool) := do
  let verified ← (liftM
    ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
      pk x.1 x.2) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure (x, verified)

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
private theorem liftAdv_bind_verify_cmaSignHashQueryBound
    (pk : Stmt)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
      (M × (Commit × Resp)))
    (qS qH : ℕ)
    (hQ : signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := oa) qS qH) :
    cmaSignHashQueryBound (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt := Stmt)
      ((liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp))) >>=
        postVerifyComp (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) pk)
      qS (qH + 1) := by
  induction oa using OracleComp.inductionOn generalizing qS qH with
  | pure x =>
      rcases x with ⟨msg, sig⟩
      simpa [postVerifyComp, cmaSignHashQueryBound] using
        fiatShamir_verify_cmaSignHashQueryBound (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) pk msg sig qS (qH + 1)
          (Nat.succ_pos qH)
  | query_bind t cont ih =>
      simp only [signHashQueryBound, OracleComp.isQueryBound_query_bind_iff] at hQ
      rcases hQ with ⟨hcan, hcont⟩
      rcases t with (n | mc) | m
      · simp only [liftM_bind, bind_assoc]
        change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt)
          (liftM ((cmaSpec M Commit Chal Resp Stmt).query
              (Sum.inl (Sum.inl (Sum.inl n)))) >>= fun u =>
            ((liftM (cont u) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp))) >>=
              postVerifyComp (σ := σ) (hr := hr) (M := M)
                (Commit := Commit) (Chal := Chal) (Resp := Resp) pk))
          qS (qH + 1)
        rw [cmaSignHashQueryBound_query_bind_iff]
        refine ⟨trivial, fun u => ?_⟩
        simpa [cmaSignHashQueryBound] using ih u qS qH (hcont u)
      · simp only [liftM_bind, bind_assoc]
        change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt)
          (liftM ((cmaSpec M Commit Chal Resp Stmt).query
              (Sum.inl (Sum.inl (Sum.inr mc)))) >>= fun u =>
            ((liftM (cont u) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp))) >>=
              postVerifyComp (σ := σ) (hr := hr) (M := M)
                (Commit := Commit) (Chal := Chal) (Resp := Resp) pk))
          qS (qH + 1)
        rw [cmaSignHashQueryBound_query_bind_iff]
        refine ⟨Nat.succ_pos qH, fun u => ?_⟩
        have hEq : qH - 1 + 1 = qH := Nat.sub_add_cancel hcan
        simpa [cmaSignHashQueryBound, hEq] using ih u qS (qH - 1) (hcont u)
      · simp only [liftM_bind, bind_assoc]
        change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt)
          (liftM ((cmaSpec M Commit Chal Resp Stmt).query (Sum.inl (Sum.inr m))) >>=
            fun u =>
            ((liftM (cont u) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp))) >>=
              postVerifyComp (σ := σ) (hr := hr) (M := M)
                (Commit := Commit) (Chal := Chal) (Resp := Resp) pk))
          qS (qH + 1)
        rw [cmaSignHashQueryBound_query_bind_iff]
        refine ⟨hcan, fun u => ?_⟩
        simpa [cmaSignHashQueryBound] using ih u (qS - 1) qH (hcont u)

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
theorem postKeygenAdv_cmaSignHashQueryBound
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (qS qH : ℕ)
    (hQ : signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (postKeygenAdv σ hr M adv pk) qS (qH + 1) := by
  simpa [postKeygenAdv, postVerifyComp] using
    liftAdv_bind_verify_cmaSignHashQueryBound (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) (σ := σ) (hr := hr)
      (pk := pk) (oa := adv.main pk) (qS := qS) (qH := qH) hQ

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
theorem signedAdv_cmaSignHashQueryBound
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (signedAdv σ hr M adv) qS (qH + 1) := by
  rw [signedAdv]
  rw [cmaSignHashQueryBound, OracleComp.isQueryBound_query_bind_iff]
  refine ⟨trivial, fun pk => ?_⟩
  simpa [cmaSignHashQueryBound, postKeygenAdv] using
    postKeygenAdv_cmaSignHashQueryBound (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk qS qH (hQ pk)

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
theorem cmaSignLogImpl_cmaSignHashQueryBound
    {α : Type}
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (signed : List M) (qS qH : ℕ)
    (hA : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) A qS qH) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      ((simulateQ (cmaSignLogImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt)) A).run signed) qS qH := by
  induction A using OracleComp.inductionOn generalizing qS qH signed with
  | pure x =>
      simp [simulateQ_pure, cmaSignHashQueryBound]
  | query_bind t cont ih =>
      rw [cmaSignHashQueryBound_query_bind_iff] at hA
      rcases hA with ⟨hcan, hcont⟩
      rcases t with ((n | mc) | m) | ⟨⟩
      · rw [simulateQ_query_bind, StateT.run_bind]
        simp only [add_apply_inl, OracleQuery.input_query, bind_pure, monadLift_self,
          StateT.run_monadLift, bind_pure_comp, bind_map_left]
        change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt)
          (liftM ((cmaSpec M Commit Chal Resp Stmt).query (Sum.inl (Sum.inl (Sum.inl n)))) >>=
            fun u => (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) (cont u)).run signed)
          qS qH
        rw [cmaSignHashQueryBound_query_bind_iff]
        refine ⟨trivial, fun u => ?_⟩
        simpa [cmaSignHashQueryBound] using ih u signed qS qH (hcont u)
      · rw [simulateQ_query_bind, StateT.run_bind]
        simp only [add_apply_inl, add_apply_inr, OracleQuery.input_query, bind_pure,
          monadLift_self, StateT.run_monadLift, bind_pure_comp, bind_map_left]
        change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt)
          (liftM ((cmaSpec M Commit Chal Resp Stmt).query (Sum.inl (Sum.inl (Sum.inr mc)))) >>=
            fun u => (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) (cont u)).run signed)
          qS qH
        rw [cmaSignHashQueryBound_query_bind_iff]
        refine ⟨hcan, fun u => ?_⟩
        simpa [cmaSignHashQueryBound] using ih u signed qS (qH - 1) (hcont u)
      · rw [simulateQ_query_bind, StateT.run_bind]
        simp only [add_apply_inl, add_apply_inr, OracleQuery.input_query, monadLift_self]
        change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt)
          (liftM ((cmaSpec M Commit Chal Resp Stmt).query (Sum.inl (Sum.inr m))) >>=
            fun sig => (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) (cont sig)).run (signed ++ [m]))
          qS qH
        rw [cmaSignHashQueryBound_query_bind_iff]
        refine ⟨hcan, fun sig => ?_⟩
        simpa [cmaSignHashQueryBound] using ih sig (signed ++ [m]) (qS - 1) qH (hcont sig)
      · rw [simulateQ_query_bind, StateT.run_bind]
        simp only [add_apply_inr, OracleQuery.input_query, bind_pure, monadLift_self,
          StateT.run_monadLift, bind_pure_comp, bind_map_left]
        change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt)
          (liftM ((cmaSpec M Commit Chal Resp Stmt).query (Sum.inr ())) >>=
            fun pk => (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) (cont pk)).run signed)
          qS qH
        rw [cmaSignHashQueryBound_query_bind_iff]
        refine ⟨trivial, fun pk => ?_⟩
        simpa [cmaSignHashQueryBound] using ih pk signed qS qH (hcont pk)

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal]
  [DecidableEq M] [DecidableEq Commit] in
theorem signedCandidateAdv_cmaSignHashQueryBound
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (signedCandidateAdv σ hr M adv) qS qH := by
  unfold signedCandidateAdv
  exact cmaSignLogImpl_cmaSignHashQueryBound (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (candidateAdv σ hr M adv) [] qS qH
    (candidateAdv_cmaSignHashQueryBound (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv qS qH hQ)

omit [SampleableType Stmt] [SampleableType Wit]
  [DecidableEq Commit] [SampleableType Chal] in
theorem verifyFreshComp_cmaSignHashQueryBound
    (p : (Stmt × (M × (Commit × Resp))) × List M) (qS : ℕ) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (verifyFreshComp (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) p) qS 1 := by
  rcases p with ⟨⟨pk, msg, sig⟩, signed⟩
  simpa [verifyFreshComp, cmaSignHashQueryBound] using
    fiatShamir_verify_cmaSignHashQueryBound (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) pk msg sig qS 1
      (Nat.succ_pos 0)

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal]
  [DecidableEq Commit] in
theorem signedFreshAdv_cmaSignHashQueryBound
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (signedFreshAdv σ hr M adv) qS (qH + 1) := by
  unfold signedFreshAdv
  simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using
    cmaSignHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (oa := signedCandidateAdv σ hr M adv)
      (ob := verifyFreshComp (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (qS₁ := qS) (qH₁ := qH) (qS₂ := 0) (qH₂ := 1)
      (signedCandidateAdv_cmaSignHashQueryBound (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv qS qH hQ)
      (fun p => verifyFreshComp_cmaSignHashQueryBound (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) p 0)

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The first `pkSpec` query in `signedAdv` forces `cmaReal` to run its lazy
keygen, installing a stable `some (pk, sk)` in the `.inr .keypair` cell.
The rest of `signedAdv` (adversary's main + FS verification) never
touches `pkSpec`, so we can factor the keygen out as a top-level
`hr.gen` bind. -/
private lemma cmaRealRun_eq_keygen_bind
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    cmaRealRun σ hr M adv =
      (hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
        (simulateQ (cmaReal M Commit Chal σ hr).impl
            (postKeygenAdv σ hr M adv ps.1)).run
          (Heap.empty.update (Sum.inr .keypair) (some (ps.1, ps.2))) >>=
          fun p => pure (p.1.1, p.1.2, p.2 (Sum.inl .log)) := by
  unfold cmaRealRun signedAdv Package.runState postKeygenAdv
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, StateT.run]
  -- `cmaReal.init = pure Heap.empty` definitionally; reduce the outer init.
  change ((pure (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)) :
      OracleComp unifSpec _) >>= fun h₀ => _) >>= _ = _
  simp only [pure_bind]
  rw [cmaReal_impl_pkSpec_bind_run_none (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) _ _ rfl]
  simp only [bind_assoc]
  rfl

/-- Hop **H2** (freshness-preserving): running the syntactically logged
Boolean adversary through `cmaReal` matches the original Fiat-Shamir
EUF-CMA experiment.

The top-level proof reduces to matching:

1. the `pkSpec` handler (lazy vs eager keygen), captured by
   `cmaRealRun_eq_keygen_bind` above;
2. the RO cache handler (`.inr .roCache` in the heap vs
   `Context.randomOracle` in `runtime`);
3. the signing handler (runs FS signing through the same RO cache vs
   `signingOracle pk sk` in a `WriterT` log);
4. the verify call (one further `Hash (msg, c)` through the same cache);
5. the signing-query log produced by `cmaSignLogImpl` against the
   `WriterT` log in `SignatureAlg.unforgeableExp`.

Kept as `sorry` pending the full distributional proof; the body should reuse
the generic WriterT/StateT input-log bridge
`QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog` from
`QueryTracking/LoggingOracle.lean`. -/
theorem cmaRealFreshAdvantage_eq_unforgeableExp
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    Pr[= true | (cmaReal M Commit Chal σ hr).runProb (signedFreshAdv σ hr M adv)] =
      adv.advantage (FiatShamir.runtime M) := by
  sorry

/-! ### H1 + H2 composition -/

/-- H2 in inequality form: the CMA advantage is bounded by the probability
that `cmaReal` accepts the freshness-preserving Boolean adversary. Entry
point for the rest of the HeapSSP hop chain
(`cmaReal → cmaSim → nma → Fork`). -/
theorem cma_advantage_le_runProb_cmaRealFresh
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    adv.advantage (FiatShamir.runtime M) ≤
      Pr[= true | (cmaReal M Commit Chal σ hr).runProb (signedFreshAdv σ hr M adv)] := by
  rw [cmaRealFreshAdvantage_eq_unforgeableExp]

end FiatShamir.HeapSSP
