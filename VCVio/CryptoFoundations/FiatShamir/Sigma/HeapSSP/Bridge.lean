/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Facts
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.HeapSSP.Advantage
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateProjection
import VCVio.OracleComp.SimSemantics.WriterT

/-!
# Bridge between `unforgeableExp` and `cmaReal.runProb` (HeapSSP)

Ties the existing `SignatureAlg.unforgeableAdv`-based EUF-CMA experiment
for the Fiat-Shamir scheme to the HeapSSP `cmaReal` game
(`Sigma/HeapSSP/Games.lean`). Contributes hops H1 and H2 of the HeapSSP chain:

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
          have hpos : 1 ≤ qH₁ := Nat.succ_le_of_lt hcan
          omega
        simpa [cmaSignHashCost, hEq] using hrec
      · refine ⟨Nat.add_pos_left hcan qS₂, fun u => ?_⟩
        have hrec := ih u (hcont u)
        have hEq : qS₁ - 1 + qS₂ = qS₁ + qS₂ - 1 := by
          have hpos : 1 ≤ qS₁ := Nat.succ_le_of_lt hcan
          omega
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
implemented by an explicit cache-state `QueryImpl`. -/
@[reducible] noncomputable def fsBaseImpl :
    QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := by
  letI : DecidableEq (M × Commit) := inferInstance
  exact unifFwdImpl (M × Commit →ₒ Chal) +
    (randomOracle : QueryImpl (M × Commit →ₒ Chal) _)

/-- The Fiat-Shamir runtime-with-cache semantics is the explicit cache-state implementation
`fsBaseImpl`, observed from the chosen initial cache. -/
lemma runtimeWithCache_evalDist_eq_fsBaseImpl
    (cache : (M × Commit →ₒ Chal).QueryCache)
    {α : Type}
    (oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α) :
    (FiatShamir.runtimeWithCache M cache).evalDist oa =
      evalDist ((simulateQ
        (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)) oa).run'
        cache) := by
  unfold FiatShamir.runtimeWithCache ProbCompRuntime.evalDist
    SPMFSemantics.evalDist SemanticsVia.denote fsBaseImpl
  unfold SPMFSemantics.withStateOracle unifFwdImpl simulateQ' evalDist
  have hbase :
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)
        = (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := by
    funext t
    simp [QueryImpl.liftTarget_apply, HasQuery.toQueryImpl]
  rw [hbase]
  dsimp
  congr 6
  funext a b
  exact Subsingleton.elim _ _

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
    (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).toHasQuery
  let baseS : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT (List M)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
    (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
      (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)).liftTarget _
  exact baseS +
    QueryImpl.appendInputLog
      (postKeygenSignCore (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)

private abbrev postKeygenSpec (M Commit Chal Resp : Type) :=
  (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp))) : OracleSpec _)

private abbrev postKeygenCache (M Commit Chal : Type) :=
  (M × Commit →ₒ Chal).QueryCache

private abbrev postKeygenState (M Commit Chal : Type) :=
  List M × postKeygenCache M Commit Chal

private abbrev cmaPostKeygenState
    (M Commit Chal Stmt Wit : Type) :=
  List M × Heap (CmaCells M Commit Chal Stmt Wit)

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
  [SampleableType Stmt] [SampleableType Wit] in
private lemma postKeygenSpec_liftM_query_eq_cmaSpec_query
    (t : (postKeygenSpec M Commit Chal Resp).Domain) :
    (liftM (liftM ((postKeygenSpec M Commit Chal Resp).query t) :
      OracleComp (postKeygenSpec M Commit Chal Resp)
        ((postKeygenSpec M Commit Chal Resp).Range t)) :
      OracleComp (cmaSpec M Commit Chal Resp Stmt)
        ((postKeygenSpec M Commit Chal Resp).Range t)) =
    (liftM ((cmaSpec M Commit Chal Resp Stmt).query (Sum.inl t)) :
      OracleComp (cmaSpec M Commit Chal Resp Stmt)
        ((postKeygenSpec M Commit Chal Resp).Range t)) := by
  rcases t with (n | mc) | m <;> rfl

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
  [SampleableType Stmt] [SampleableType Wit] in
private lemma roSpec_liftM_query_eq_cmaSpec_query
    (mc : M × Commit) :
    (liftM (liftM ((M × Commit →ₒ Chal).query mc) :
      OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal) :
      OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal) =
    (liftM ((cmaSpec M Commit Chal Resp Stmt).query
      (Sum.inl (Sum.inl (Sum.inr mc)))) :
      OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal) := by
  rfl

private def cmaPostKeygenProj
    (s : cmaPostKeygenState M Commit Chal Stmt Wit) :
    postKeygenState M Commit Chal :=
  (s.1, s.2 (Sum.inr .roCache))

private def cmaPostKeygenInv
    (pk : Stmt) (sk : Wit)
    (s : cmaPostKeygenState M Commit Chal Stmt Wit) : Prop :=
  s.2 (Sum.inr .keypair) = some (pk, sk)

private noncomputable def postKeygenAppendProdImpl (pk : Stmt) (sk : Wit) :
    QueryImpl (postKeygenSpec M Commit Chal Resp)
      (StateT (postKeygenState M Commit Chal) ProbComp) := fun t =>
  StateT.mk fun (signed, cache) =>
    match t with
    | Sum.inl (Sum.inl n) => do
        let r ← (unifSpec.query n : ProbComp (Fin (n + 1)))
        pure (r, (signed, cache))
    | Sum.inl (Sum.inr mc) => do
        let (r, cache') ←
          ((randomOracle : QueryImpl (M × Commit →ₒ Chal)
            (StateT (postKeygenCache M Commit Chal) ProbComp)) mc).run cache
        pure (r, (signed, cache'))
    | Sum.inr m => do
        let (sig, cache') ←
          (postKeygenSignCore (σ := σ) (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk m).run cache
        pure (sig, (signed ++ [m], cache'))

private noncomputable def cmaRealAppendProdImpl :
    QueryImpl (postKeygenSpec M Commit Chal Resp)
      (StateT (cmaPostKeygenState M Commit Chal Stmt Wit) ProbComp) := fun t =>
  StateT.mk fun (signed, h) =>
    match t with
    | Sum.inl (Sum.inl n) => do
        let r ← (unifSpec.query n : ProbComp (Fin (n + 1)))
        pure (r, (signed, h))
    | Sum.inl (Sum.inr mc) => do
        let (r, h') ←
          ((cmaReal M Commit Chal σ hr).impl
            (Sum.inl (Sum.inl (Sum.inr mc)) :
              (cmaSpec M Commit Chal Resp Stmt).Domain)).run h
        pure (r, (signed, h'))
    | Sum.inr m => do
        let (sig, h') ←
          ((cmaReal M Commit Chal σ hr).impl
            (Sum.inl (Sum.inr m) :
              (cmaSpec M Commit Chal Resp Stmt).Domain)).run h
        pure (sig, (signed ++ [m], h'))

private noncomputable def cmaRealLoggedProdImpl :
    QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (cmaPostKeygenState M Commit Chal Stmt Wit) ProbComp) :=
  ((cmaReal M Commit Chal σ hr).impl.stateTMapBase
    (cmaSignLogImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt))).flattenStateT

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealLoggedProdImpl_left_eq_cmaRealAppendProdImpl
    (t : (postKeygenSpec M Commit Chal Resp).Domain) :
    cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) (Sum.inl t) =
      cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) t := by
  ext st
  rcases st with ⟨signed, h⟩
  rcases t with (n | mc) | m
  · simp [cmaRealLoggedProdImpl, cmaRealAppendProdImpl, cmaSignLogImpl,
      QueryImpl.stateTMapBase, QueryImpl.flattenStateT, cmaReal]
  · cases hcache : h (Sum.inr InnerCell.roCache) mc with
    | some ch =>
        simp [cmaRealLoggedProdImpl, cmaRealAppendProdImpl, cmaSignLogImpl,
          QueryImpl.stateTMapBase, QueryImpl.flattenStateT, cmaReal, hcache]
    | none =>
        simp [cmaRealLoggedProdImpl, cmaRealAppendProdImpl, cmaSignLogImpl,
          QueryImpl.stateTMapBase, QueryImpl.flattenStateT, cmaReal, hcache,
          Heap.update]
  · simp [cmaRealLoggedProdImpl, cmaRealAppendProdImpl, cmaSignLogImpl,
      QueryImpl.stateTMapBase, QueryImpl.flattenStateT, cmaReal, StateT.run_bind]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealLoggedProdImpl_liftAdv_run {α : Type}
    (oa : OracleComp (postKeygenSpec M Commit Chal Resp) α)
    (st : cmaPostKeygenState M Commit Chal Stmt Wit) :
    (simulateQ (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run st =
      (simulateQ (cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp)) oa).run st := by
  simpa using congrArg (fun x => x.run st)
    (QueryImpl.simulateQ_liftM_eq_of_query
      (impl := cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (impl₁ := cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (h := fun t =>
        by
          rw [postKeygenSpec_liftM_query_eq_cmaSpec_query
            (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
            (Stmt := Stmt) (t := t)]
          change simulateQ
              (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
                (Commit := Commit) (Chal := Chal) (Resp := Resp))
              (liftM ((cmaSpec M Commit Chal Resp Stmt).query (Sum.inl t))) =
            cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
              (Commit := Commit) (Chal := Chal) (Resp := Resp) t
          rw [simulateQ_spec_query]
          exact cmaRealLoggedProdImpl_left_eq_cmaRealAppendProdImpl
            (σ := σ) (hr := hr) (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) t)
      (oa := oa))

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealLoggedProdImpl_postKeygenCandidateAdv_run
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (st : cmaPostKeygenState M Commit Chal Stmt Wit) :
    (simulateQ (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (postKeygenCandidateAdv (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk)).run st =
    (simulateQ (cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp)) (adv.main pk)).run st := by
  simpa [postKeygenCandidateAdv] using
    cmaRealLoggedProdImpl_liftAdv_run (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (oa := adv.main pk) st

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealLoggedProdImpl_pkSpec_bind_run_none {α : Type}
    (f : Stmt → StateT (cmaPostKeygenState M Commit Chal Stmt Wit) ProbComp α)
    (signed : List M)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (hkp : h (Sum.inr .keypair) = none) :
    ((cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp)
        (Sum.inr ()) >>= f) (signed, h)) =
      hr.gen >>= fun ps : Stmt × Wit =>
        (f ps.1).run
          (signed, h.update (Sum.inr .keypair) (some (ps.1, ps.2))) := by
  change (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (Sum.inr ())).run (signed, h) >>= (fun z => (f z.1).run z.2) = _
  simp [cmaRealLoggedProdImpl, cmaSignLogImpl, QueryImpl.stateTMapBase,
    QueryImpl.flattenStateT, cmaReal, hkp]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealLoggedProdImpl_pkSpec_bind_output_none {α : Type}
    (f : Stmt → cmaPostKeygenState M Commit Chal Stmt Wit → ProbComp α)
    (signed : List M)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (hkp : h (Sum.inr .keypair) = none) :
    ((cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp)
        (Sum.inr ())).run (signed, h) >>= fun z => f z.1 z.2) =
      hr.gen >>= fun ps : Stmt × Wit =>
        f ps.1 (signed, h.update (Sum.inr .keypair) (some (ps.1, ps.2))) := by
  simp [cmaRealLoggedProdImpl, cmaSignLogImpl, QueryImpl.stateTMapBase,
    QueryImpl.flattenStateT, cmaReal, hkp]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealAppendProdImpl_project_step
    (pk : Stmt) (sk : Wit)
    (t : (postKeygenSpec M Commit Chal Resp).Domain)
    (st : cmaPostKeygenState M Commit Chal Stmt Wit)
    (hst : cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk st) :
    Prod.map id (cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit)) <$>
        (cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) t).run st =
      (postKeygenAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk t).run
        (cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
          (Stmt := Stmt) (Wit := Wit) st) := by
  rcases st with ⟨signed, h⟩
  simp only [cmaPostKeygenInv] at hst
  rcases t with (n | mc) | m
  · simp [cmaRealAppendProdImpl, postKeygenAppendProdImpl, cmaPostKeygenProj]
  · cases hcache : h (Sum.inr InnerCell.roCache) mc with
    | some ch =>
        simp [cmaRealAppendProdImpl, postKeygenAppendProdImpl, cmaPostKeygenProj,
          cmaReal, hcache]
    | none =>
        simp [cmaRealAppendProdImpl, postKeygenAppendProdImpl, cmaPostKeygenProj,
          cmaReal, hcache, Heap.update, uniformSampleImpl]
  · conv_lhs =>
      simp [cmaRealAppendProdImpl, cmaPostKeygenProj, cmaReal, hst]
    conv_rhs =>
      simp [postKeygenAppendProdImpl, cmaPostKeygenProj, postKeygenSignCore,
        FiatShamir, uniformSampleImpl]
    refine bind_congr fun cp => ?_
    cases hcache : h (Sum.inr InnerCell.roCache) (m, cp.1) with
    | some ch =>
        simp
    | none =>
        simp [Heap.update]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealAppendProdImpl_preserves_inv
    (pk : Stmt) (sk : Wit)
    (t : (postKeygenSpec M Commit Chal Resp).Domain)
    (st : cmaPostKeygenState M Commit Chal Stmt Wit)
    (hst : cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk st) :
    ∀ z ∈ support ((cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) t).run st),
      cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) pk sk z.2 := by
  rcases st with ⟨signed, h⟩
  simp only [cmaPostKeygenInv] at hst ⊢
  rcases t with (n | mc) | m
  · intro z hz
    have hz' := by
      simpa [cmaRealAppendProdImpl] using hz
    rcases hz' with ⟨r, _hr, rfl⟩
    exact hst
  · intro z hz
    have hz' := by
      simpa [cmaRealAppendProdImpl] using hz
    rcases hz' with ⟨y, hy, rfl⟩
    exact cmaReal_impl_preserves_keypair_some (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (PrvState := PrvState)
      (σ := σ) (hr := hr)
      (t := (Sum.inl (Sum.inl (Sum.inr mc)) :
        (cmaSpec M Commit Chal Resp Stmt).Domain))
      pk sk h hst y hy
  · intro z hz
    have hz' := by
      simpa [cmaRealAppendProdImpl] using hz
    rcases hz' with ⟨y, hy, rfl⟩
    exact cmaReal_impl_preserves_keypair_some (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (PrvState := PrvState)
      (σ := σ) (hr := hr)
      (t := (Sum.inl (Sum.inr m) :
        (cmaSpec M Commit Chal Resp Stmt).Domain))
      pk sk h hst y hy

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealAppendProdImpl_project_run {α : Type}
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp (postKeygenSpec M Commit Chal Resp) α)
    (st : cmaPostKeygenState M Commit Chal Stmt Wit)
    (hst : cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk st) :
    Prod.map id (cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit)) <$>
        (simulateQ (cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp)) oa).run st =
      (simulateQ (postKeygenAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk) oa).run
        (cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
          (Stmt := Stmt) (Wit := Wit) st) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (impl₁ := cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp))
    (impl₂ := postKeygenAppendProdImpl (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
    (inv := cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk)
    (proj := cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit))
    (hinv := fun t s hs =>
      cmaRealAppendProdImpl_preserves_inv (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        pk sk t s hs)
    (hproj := fun t s hs =>
      cmaRealAppendProdImpl_project_step (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        pk sk t s hs)
    oa st hst

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Fixed-key specialization of the generic WriterT-to-StateT signing-log
bridge, in the explicit cache-state Fiat-Shamir runtime. -/
private theorem postKeygenWriterLog_eq_inputLog
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) :
    let runtime := fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
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
  let runtime := fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
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

/-- Fixed-key public post-keygen experiment in the WriterT signing-log form.

The final Boolean event is phrased using the list of queried signing inputs,
so it is definitionally aligned with `postKeygenFreshProb` after applying
`postKeygenWriterLog_eq_inputLog`. -/
@[reducible] noncomputable def postKeygenFreshWriterComp
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) :
    OracleComp (unifSpec + (M × Commit →ₒ Chal)) Bool := by
  letI : DecidableEq M := Classical.decEq _
  letI : DecidableEq (Commit × Resp) := Classical.decEq _
  let so :=
    (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).signingOracle
      pk sk
  let baseW : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (WriterT (QueryLog (M →ₒ (Commit × Resp)))
        (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
    (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
      (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))).liftTarget _
  let implW : QueryImpl (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
      : OracleSpec _)
      (WriterT (QueryLog (M →ₒ (Commit × Resp)))
        (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
    baseW + so
  exact do
    let ((msg, sig), log) ← (simulateQ implW (adv.main pk)).run
    let verified ←
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
        pk msg sig
    pure (!log.wasQueried msg && verified)

@[reducible] noncomputable def postKeygenFreshWriterProb
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) : ProbComp Bool := by
  let runtime := fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
  letI : HasQuery (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := runtime.toHasQuery
  let so := postKeygenSignCore (σ := σ) (hr := hr) (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk
  let baseW : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (WriterT (QueryLog (M →ₒ (Commit × Resp)))
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
    runtime.liftTarget _
  let implW : QueryImpl (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
      : OracleSpec _)
      (WriterT (QueryLog (M →ₒ (Commit × Resp)))
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
    baseW + QueryImpl.withLogging so
  letI : HasQuery (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    (randomOracle : QueryImpl (M × Commit →ₒ Chal) _).toHasQuery
  exact
    (((fun z : (M × (Commit × Resp)) × QueryLog (M →ₒ (Commit × Resp)) =>
        (z.1, z.2.map (fun e => e.1))) <$>
        ((simulateQ implW (adv.main pk)).run :
          StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
            ((M × (Commit × Resp)) × QueryLog (M →ₒ (Commit × Resp))))) >>= fun z => do
        let msg := z.1.1
        let sig := z.1.2
        let signed := z.2
        let verified ←
          (FiatShamir (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) σ hr M).verify
            pk msg sig
        pure (!decide (msg ∈ signed) && verified)).run' ∅

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

private noncomputable def postKeygenVerifyProd
    (pk : Stmt) (x : M × (Commit × Resp)) :
    StateT (postKeygenState M Commit Chal) ProbComp Bool :=
  StateT.mk fun (signed, cache) => do
    let msg := x.1
    let sig := x.2
    let (ch, cache') ←
      ((randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT (postKeygenCache M Commit Chal) ProbComp)) (msg, sig.1)).run cache
    pure (!decide (msg ∈ signed) && σ.verify pk sig.1 ch sig.2, (signed, cache'))

private noncomputable def postKeygenFreshProdProb
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) : ProbComp Bool :=
  ((simulateQ
      (postKeygenAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
      (adv.main pk) >>=
    postKeygenVerifyProd (σ := σ) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) pk).run'
    (([] : List M), (∅ : postKeygenCache M Commit Chal)))

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma postKeygenAppendProdImpl_eq_flattenStateT
    (pk : Stmt) (sk : Wit) :
    postKeygenAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk =
      (postKeygenAppendImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk).flattenStateT := by
  funext t
  rcases t with (n | mc) | m
  · ext st
    rcases st with ⟨signed, cache⟩
    conv_lhs =>
      simp [postKeygenAppendProdImpl]
    conv_rhs =>
      simp [postKeygenAppendImpl]
    change _ =
      (((fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).liftTarget
          (StateT (List M) (StateT (postKeygenCache M Commit Chal) ProbComp))).flattenStateT
        (Sum.inl n)).run (signed, cache)
    rw [QueryImpl.flattenStateT_liftTarget_apply_run]
    simp [fsBaseImpl, unifFwdImpl]
  · ext st
    rcases st with ⟨signed, cache⟩
    conv_lhs =>
      simp [postKeygenAppendProdImpl]
    conv_rhs =>
      simp [postKeygenAppendImpl]
    change _ =
      (((fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).liftTarget
          (StateT (List M) (StateT (postKeygenCache M Commit Chal) ProbComp))).flattenStateT
        (Sum.inr mc)).run (signed, cache)
    rw [QueryImpl.flattenStateT_liftTarget_apply_run]
    simp [fsBaseImpl, unifFwdImpl, randomOracle]
  · ext st
    rcases st with ⟨signed, cache⟩
    simp [postKeygenAppendProdImpl, postKeygenAppendImpl, QueryImpl.flattenStateT,
      postKeygenSignCore, StateT.run_get, StateT.run_set, StateT.run_monadLift,
      StateT.run_bind]

omit [SampleableType Stmt] [SampleableType Wit] in
private theorem postKeygenFreshProdProb_eq_postKeygenFreshProb
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) :
    postKeygenFreshProdProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk =
    postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk := by
  unfold postKeygenFreshProdProb postKeygenFreshProb postKeygenVerifyProd
  rw [postKeygenAppendProdImpl_eq_flattenStateT (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk]
  rw [StateT.run'_eq, StateT.run_bind]
  rw [OracleComp.simulateQ_flattenStateT_run]
  simp [StateT.run'_eq, StateT.run_bind, FiatShamir, randomOracle]

private noncomputable def cmaRealPostKeygenVerifyProd
    (pk : Stmt) (x : M × (Commit × Resp)) :
    StateT (cmaPostKeygenState M Commit Chal Stmt Wit) ProbComp Bool :=
  StateT.mk fun (signed, h) => do
    let msg := x.1
    let sig := x.2
    let (ch, h') ←
      ((cmaReal M Commit Chal σ hr).impl
        (Sum.inl (Sum.inl (Sum.inr (msg, sig.1))) :
          (cmaSpec M Commit Chal Resp Stmt).Domain)).run h
    pure (!decide (msg ∈ signed) && σ.verify pk sig.1 ch sig.2, (signed, h'))

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaReal_verifyFreshComp_run'_eq
    (pk : Stmt) (x : M × (Commit × Resp)) (signed : List M)
    (h : Heap (CmaCells M Commit Chal Stmt Wit)) :
    (simulateQ (cmaReal M Commit Chal σ hr).impl
        (verifyFreshComp (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp)
          ((pk, x), signed))).run' h =
      (cmaRealPostKeygenVerifyProd (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk x).run'
        (signed, h) := by
  rcases x with ⟨msg, sig⟩
  rcases sig with ⟨c, resp⟩
  have hquery :
      simulateQ (cmaReal M Commit Chal σ hr).impl
          (liftM (liftM ((M × Commit →ₒ Chal).query (msg, c)) :
            OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal) :
            OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal) =
        (cmaReal M Commit Chal σ hr).impl
          (Sum.inl (Sum.inl (Sum.inr (msg, c))) :
            (cmaSpec M Commit Chal Resp Stmt).Domain) := by
    rw [roSpec_liftM_query_eq_cmaSpec_query (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (mc := (msg, c))]
    change simulateQ (cmaReal M Commit Chal σ hr).impl
        (liftM ((cmaSpec M Commit Chal Resp Stmt).query
          (Sum.inl (Sum.inl (Sum.inr (msg, c)))))) =
      (cmaReal M Commit Chal σ hr).impl
        (Sum.inl (Sum.inl (Sum.inr (msg, c))) :
          (cmaSpec M Commit Chal Resp Stmt).Domain)
    rw [simulateQ_spec_query]
  cases hcache : h (Sum.inr InnerCell.roCache) (msg, c) with
  | some ch =>
      conv_lhs =>
        simp [verifyFreshComp, StateT.run'_eq, FiatShamir]
      conv_rhs =>
        simp [cmaRealPostKeygenVerifyProd, StateT.run'_eq]
      rw [show (simulateQ (cmaReal M Commit Chal σ hr).impl
            (liftM (liftM ((M × Commit →ₒ Chal).query (msg, c)) :
              OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run h =
          ((cmaReal M Commit Chal σ hr).impl
            (Sum.inl (Sum.inl (Sum.inr (msg, c))) :
              (cmaSpec M Commit Chal Resp Stmt).Domain)).run h
        from congrArg (fun q => q.run h) hquery]
      simp [cmaReal, hcache]
  | none =>
      conv_lhs =>
        simp [verifyFreshComp, StateT.run'_eq, FiatShamir]
      conv_rhs =>
        simp [cmaRealPostKeygenVerifyProd, StateT.run'_eq]
      rw [show (simulateQ (cmaReal M Commit Chal σ hr).impl
            (liftM (liftM ((M × Commit →ₒ Chal).query (msg, c)) :
              OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run h =
          ((cmaReal M Commit Chal σ hr).impl
            (Sum.inl (Sum.inl (Sum.inr (msg, c))) :
              (cmaSpec M Commit Chal Resp Stmt).Domain)).run h
        from congrArg (fun q => q.run h) hquery]
      simp [cmaReal, hcache, Heap.update]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealPostKeygenVerifyProd_project
    (pk : Stmt) (x : M × (Commit × Resp))
    (st : cmaPostKeygenState M Commit Chal Stmt Wit) :
    Prod.map id (cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit)) <$>
        (cmaRealPostKeygenVerifyProd (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) pk x).run st =
      (postKeygenVerifyProd (σ := σ) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk x).run
        (cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
          (Stmt := Stmt) (Wit := Wit) st) := by
  rcases st with ⟨signed, h⟩
  rcases x with ⟨msg, sig⟩
  rcases sig with ⟨c, resp⟩
  cases hcache : h (Sum.inr InnerCell.roCache) (msg, c) with
  | some ch =>
      simp [cmaRealPostKeygenVerifyProd, postKeygenVerifyProd,
        cmaPostKeygenProj, cmaReal, hcache]
  | none =>
      simp [cmaRealPostKeygenVerifyProd, postKeygenVerifyProd,
        cmaPostKeygenProj, cmaReal, hcache, Heap.update, uniformSampleImpl]

omit [SampleableType Stmt] [SampleableType Wit] in
private theorem cmaRealPostKeygenFreshProdProb_eq_postKeygenFreshProdProb
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) :
    ((simulateQ (cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp)) (adv.main pk) >>=
        cmaRealPostKeygenVerifyProd (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) pk).run'
      (([] : List M), Heap.empty.update (Sum.inr .keypair) (some (pk, sk)))) =
      postKeygenFreshProdProb (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk := by
  unfold postKeygenFreshProdProb
  let initHeap : cmaPostKeygenState M Commit Chal Stmt Wit :=
    (([] : List M), Heap.empty.update (Sum.inr .keypair) (some (pk, sk)))
  have hinit :
      cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) pk sk initHeap := by
    simp [initHeap, cmaPostKeygenInv, Heap.update]
  have hrun :=
    OracleComp.map_run_simulateQ_bind_eq_of_query_map_eq_inv'
      (impl₁ := cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (impl₂ := postKeygenAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
      (inv := cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) pk sk)
      (proj := cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit))
      (hinv := fun t s hs =>
        cmaRealAppendProdImpl_preserves_inv (σ := σ) (hr := hr)
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
          pk sk t s hs)
      (hproj := fun t s hs =>
        cmaRealAppendProdImpl_project_step (σ := σ) (hr := hr)
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
          pk sk t s hs)
      (oa := adv.main pk)
      (k₁ := cmaRealPostKeygenVerifyProd (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk)
      (k₂ := postKeygenVerifyProd (σ := σ) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk)
      (hk := fun x s _hs =>
        cmaRealPostKeygenVerifyProd_project (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) pk x s)
      (s := initHeap) hinit
  have hrun' := congrArg (fun p => Prod.fst <$> p) hrun
  simpa [StateT.run'_eq, initHeap, cmaPostKeygenProj] using hrun'

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The fixed-key WriterT signing-log normal form agrees with the input-log
StateT normal form. -/
private theorem postKeygenFreshWriterProb_eq_postKeygenFreshProb
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) :
    postKeygenFreshWriterProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk =
    postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk := by
  unfold postKeygenFreshWriterProb postKeygenFreshProb
  let runtime := fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
  letI : HasQuery (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := runtime.toHasQuery
  let so := postKeygenSignCore (σ := σ) (hr := hr) (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk
  letI : HasQuery (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    (randomOracle : QueryImpl (M × Commit →ₒ Chal) _).toHasQuery
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
  let mappedW : StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      ((M × (Commit × Resp)) × List M) :=
    (fun z : (M × (Commit × Resp)) × QueryLog (M →ₒ (Commit × Resp)) =>
      (z.1, z.2.map (fun e => e.1))) <$> ((simulateQ implW (adv.main pk)).run :
        StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
          ((M × (Commit × Resp)) × QueryLog (M →ₒ (Commit × Resp))))
  let appendS : StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      ((M × (Commit × Resp)) × List M) :=
    (simulateQ (postKeygenAppendImpl (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
      (adv.main pk)).run []
  let kont : ((M × (Commit × Resp)) × List M) →
      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp Bool := fun z => do
    let msg := z.1.1
    let sig := z.1.2
    let signed := z.2
    let verified ←
      (FiatShamir (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) σ hr M).verify
        pk msg sig
    pure (!decide (msg ∈ signed) && verified)
  have hlog : mappedW = appendS := by
    simpa [mappedW, appendS, implW, baseW, postKeygenAppendImpl, runtime, so] using
      (postKeygenWriterLog_eq_inputLog (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk)
  change (mappedW >>= kont).run' (∅ : (M × Commit →ₒ Chal).QueryCache) =
    (appendS >>= kont).run' (∅ : (M × Commit →ₒ Chal).QueryCache)
  rw [hlog]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Interpreting the base random-oracle runtime through the WriterT signing
oracle gives the explicit cache-state WriterT handler with logged fixed-key
signing. -/
private lemma fsBaseImpl_writerTMapBase_signingOracle_eq
    (pk : Stmt) (sk : Wit) :
    let baseW : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
        (WriterT (QueryLog (M →ₒ (Commit × Resp)))
          (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
      (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))).liftTarget _
    let implW : QueryImpl (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
        : OracleSpec _)
        (WriterT (QueryLog (M →ₒ (Commit × Resp)))
          (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
      baseW +
        (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).signingOracle
          pk sk
    let baseS : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
        (WriterT (QueryLog (M →ₒ (Commit × Resp)))
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
      (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).liftTarget _
    let implS : QueryImpl (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
        : OracleSpec _)
        (WriterT (QueryLog (M →ₒ (Commit × Resp)))
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
      baseS +
        QueryImpl.withLogging
          (postKeygenSignCore (σ := σ) (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
    (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).writerTMapBase implW =
      implS := by
  funext t
  rcases t with (n | mc) | m
  · ext cache
    simp [QueryImpl.writerTMapBase, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, fsBaseImpl, unifFwdImpl]
  · ext cache
    simp [QueryImpl.writerTMapBase, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, fsBaseImpl, unifFwdImpl, randomOracle]
  · ext cache
    simp [QueryImpl.writerTMapBase, SignatureAlg.signingOracle,
      QueryImpl.withLogging_apply, postKeygenSignCore, FiatShamir,
      fsBaseImpl, randomOracle, StateT.run_bind, roSim.run_liftM]

omit [SampleableType Stmt] [SampleableType Wit] in
private theorem simulateQ_fsBaseImpl_postKeygenFreshWriterComp_run'_eq
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) :
    (simulateQ (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal))
        (postKeygenFreshWriterComp (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk)).run'
        (∅ : (M × Commit →ₒ Chal).QueryCache) =
      postKeygenFreshWriterProb (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk := by
  unfold postKeygenFreshWriterComp postKeygenFreshWriterProb
  let baseW : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (WriterT (QueryLog (M →ₒ (Commit × Resp)))
        (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
    (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
      (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))).liftTarget _
  let implW : QueryImpl (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
      : OracleSpec _)
      (WriterT (QueryLog (M →ₒ (Commit × Resp)))
        (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
    baseW +
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).signingOracle
        pk sk
  let baseS : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (WriterT (QueryLog (M →ₒ (Commit × Resp)))
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
    (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).liftTarget _
  let implS : QueryImpl (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
      : OracleSpec _)
      (WriterT (QueryLog (M →ₒ (Commit × Resp)))
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
    baseS +
      QueryImpl.withLogging
        (postKeygenSignCore (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
  have hmap :
      (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).writerTMapBase implW =
        implS := by
    simpa [baseW, implW, baseS, implS] using
      (fsBaseImpl_writerTMapBase_signingOracle_eq (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  rw [QueryImpl.simulateQ_writerTMapBase_run
    (outer := fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal))
    (inner := implW) (oa := adv.main pk)]
  rw [hmap]
  letI : DecidableEq (Commit × Resp) := Classical.decEq _
  conv_lhs =>
    simp [implS, baseS, fsBaseImpl, postKeygenSignCore, FiatShamir,
      randomOracle, QueryLog.wasQueried_eq_decide_mem_map_fst, StateT.run_bind]
  conv_rhs =>
    simp [implS, baseS, fsBaseImpl, postKeygenSignCore, FiatShamir,
      randomOracle, QueryLog.wasQueried_eq_decide_mem_map_fst, StateT.run_bind]
  refine bind_congr fun a => ?_
  congr 1
  funext ch
  congr 1
  by_cases hmem : a.1.1.1 ∈ List.map (fun e => e.fst) a.1.2
  · simp [hmem]
  · simp [hmem]

omit [SampleableType Stmt] [SampleableType Wit] in
private theorem runtime_evalDist_postKeygenFreshWriterComp_eq
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) (sk : Wit) :
    (FiatShamir.runtime M).evalDist
        (postKeygenFreshWriterComp (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk) =
      evalDist (postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk) := by
  rw [FiatShamir.runtime_eq_runtimeWithCache_empty (M := M)]
  rw [runtimeWithCache_evalDist_eq_fsBaseImpl (M := M) (Commit := Commit)
    (Chal := Chal) (cache := (∅ : (M × Commit →ₒ Chal).QueryCache))]
  rw [simulateQ_fsBaseImpl_postKeygenFreshWriterComp_run'_eq (σ := σ)
    (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) adv pk sk]
  rw [postKeygenFreshWriterProb_eq_postKeygenFreshProb (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk]

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M] [DecidableEq Commit] in
/-- The public EUF-CMA experiment factors into keygen followed by the fixed-key
WriterT post-keygen computation. -/
private theorem unforgeableExp_eq_runtime_bind_postKeygenFreshWriterComp
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    SignatureAlg.unforgeableExp (FiatShamir.runtime M) adv =
      (FiatShamir.runtime M).evalDist
        ((liftM (hr.gen : ProbComp (Stmt × Wit))) >>= fun ps =>
          postKeygenFreshWriterComp (σ := σ) (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2) := by
  unfold SignatureAlg.unforgeableExp postKeygenFreshWriterComp
  simp [FiatShamir]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Public EUF-CMA advantage in the shared fixed-key post-keygen normal form. -/
private theorem unforgeableAdvantage_eq_keygen_postKeygenFreshProb
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    adv.advantage (FiatShamir.runtime M) =
      Pr[= true | ((hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
        postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2)] := by
  unfold SignatureAlg.unforgeableAdv.advantage
  rw [unforgeableExp_eq_runtime_bind_postKeygenFreshWriterComp (σ := σ)
    (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) adv]
  rw [FiatShamir.runtime_evalDist_bind_liftComp (M := M)
    (oa := (hr.gen : ProbComp (Stmt × Wit)))
    (rest := fun ps =>
      postKeygenFreshWriterComp (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2)]
  change
    Pr[= true | (evalDist (hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
      (FiatShamir.runtime M).evalDist
        (postKeygenFreshWriterComp (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2))] =
    Pr[= true | evalDist (((hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
      postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2) :
      ProbComp Bool)]
  rw [evalDist_bind]
  apply congrArg (fun p => Pr[= true | p])
  refine bind_congr fun ps => ?_
  rw [runtime_evalDist_postKeygenFreshWriterComp_eq (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2]

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

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealRunState_signedCandidateAdv_eq
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    (cmaReal M Commit Chal σ hr).runState (signedCandidateAdv σ hr M adv) =
      (fun z : (Stmt × (M × (Commit × Resp))) ×
          cmaPostKeygenState M Commit Chal Stmt Wit =>
        ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp))
          (candidateAdv σ hr M adv)).run
          (([] : List M), Heap.empty) := by
  unfold Package.runState signedCandidateAdv
  change ((pure (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)) :
      OracleComp unifSpec _) >>= fun h₀ =>
        (simulateQ (cmaReal M Commit Chal σ hr).impl
          ((simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
            (candidateAdv σ hr M adv)).run ([] : List M))).run h₀) = _
  simp only [pure_bind]
  rw [OracleComp.simulateQ_stateTMapBase_run_eq_map_flattenStateT
    (outer := (cmaReal M Commit Chal σ hr).impl)
    (inner := cmaSignLogImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (oa := candidateAdv σ hr M adv) (s := ([] : List M))
    (q := (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)))]
  rfl

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealRunProb_signedFreshAdv_eq_keygen_bind
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    (cmaReal M Commit Chal σ hr).runProb (signedFreshAdv σ hr M adv) =
      (hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
        ((simulateQ (cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
              (Commit := Commit) (Chal := Chal) (Resp := Resp)) (adv.main ps.1) >>=
            cmaRealPostKeygenVerifyProd (σ := σ) (hr := hr) (M := M)
              (Commit := Commit) (Chal := Chal) (Resp := Resp) ps.1).run'
          (([] : List M),
            Heap.empty.update (Sum.inr .keypair) (some (ps.1, ps.2)))) := by
  rw [show (cmaReal M Commit Chal σ hr).runProb (signedFreshAdv σ hr M adv) =
      (cmaReal M Commit Chal σ hr).run (signedFreshAdv σ hr M adv) from rfl]
  rw [signedFreshAdv]
  rw [Package.run_bind]
  rw [cmaRealRunState_signedCandidateAdv_eq (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv]
  simp only [simulateQ_bind, add_apply_inr, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, bind_pure_comp, simulateQ_map, StateT.run_bind,
    StateT.run_map, map_bind, Functor.map_map, simulateQ_pure, StateT.run'_eq,
    bind_assoc, bind_map_left, Prod.mk.eta]
  let cont : Stmt → cmaPostKeygenState M Commit Chal Stmt Wit → ProbComp Bool :=
    fun pk st =>
      (simulateQ (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp))
          (postKeygenCandidateAdv (σ := σ) (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk)).run st >>= fun z =>
        (simulateQ (cmaReal M Commit Chal σ hr).impl
          (liftM
            ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
              pk z.1.1 z.1.2) :
            OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)).run z.2.2 >>=
          pure ∘ fun a => !decide (z.1.1 ∈ z.2.1) && a.1
  change ((cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (Sum.inr ())).run (([] : List M), Heap.empty) >>= fun z =>
        cont z.1 z.2) = _
  rw [cmaRealLoggedProdImpl_pkSpec_bind_output_none (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (f := cont)
    (signed := ([] : List M)) (h := Heap.empty) rfl]
  apply bind_congr
  intro ps
  dsimp [cont]
  rw [cmaRealLoggedProdImpl_postKeygenCandidateAdv_run (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (adv := adv) (pk := ps.1)
    (st := (([] : List M),
      Heap.empty.update (Sum.inr .keypair) (some (ps.1, ps.2))))]
  apply bind_congr
  intro z
  simpa [verifyFreshComp, StateT.run'_eq, FiatShamir] using
    cmaReal_verifyFreshComp_run'_eq (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (pk := ps.1) (x := z.1) (signed := z.2.1) (h := z.2.2)

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Hop **H2** (freshness-preserving): running the syntactically logged
Boolean adversary through `cmaReal` matches the original Fiat-Shamir
EUF-CMA experiment. -/
theorem cmaRealFreshAdvantage_eq_unforgeableExp
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    Pr[= true | (cmaReal M Commit Chal σ hr).runProb (signedFreshAdv σ hr M adv)] =
      adv.advantage (FiatShamir.runtime M) := by
  rw [cmaRealRunProb_signedFreshAdv_eq_keygen_bind (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv]
  rw [unforgeableAdvantage_eq_keygen_postKeygenFreshProb (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv]
  apply congrArg (fun p => Pr[= true | p])
  refine bind_congr fun ps => ?_
  rw [cmaRealPostKeygenFreshProdProb_eq_postKeygenFreshProdProb (σ := σ)
    (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) adv ps.1 ps.2]
  rw [postKeygenFreshProdProb_eq_postKeygenFreshProb (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2]

/-! ### H1 + H2 composition -/

omit [SampleableType Stmt] [SampleableType Wit] in
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
