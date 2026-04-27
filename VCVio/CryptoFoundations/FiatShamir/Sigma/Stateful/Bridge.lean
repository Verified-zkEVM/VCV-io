/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Games
import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Bridge helpers for the stateful Fiat-Shamir CMA games

This file contains the adversary wrappers and query-bound bookkeeping that
connect the public `SignatureAlg.unforgeableAdv` interface to the direct
`QueryImpl.Stateful` CMA games.
-/

universe u v

open OracleSpec OracleComp ProbComp

namespace FiatShamir.Stateful

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit]
variable [SampleableType Chal]

/-! ## Local type abbreviations -/

/-- Fiat-Shamir signature scheme over the public random-oracle interface used by
the source CMA adversary. -/
abbrev SourceSigAlg :=
  _root_.FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M

/-- Source EUF-CMA adversary type for the Fiat-Shamir signature scheme. -/
abbrev SourceAdv :=
  SignatureAlg.unforgeableAdv (SourceSigAlg (σ := σ) (hr := hr) (M := M))

/-- Source post-keygen CMA oracle interface: public Fiat-Shamir queries plus
signing queries. -/
abbrev SourceCmaSpec :=
  (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp))) : OracleSpec _)

/-- Computations over the source post-keygen CMA oracle interface. -/
abbrev SourceCmaComp (α : Type) :=
  OracleComp (SourceCmaSpec (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)) α

/-! ## Adversary wrappers -/

/-- Candidate-producing part of the CMA adversary after the public key is fixed. -/
@[reducible] noncomputable def postKeygenCandidateAdv
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt)
      (M × (Commit × Resp)) :=
  (liftM (adv.main pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt)
      (M × (Commit × Resp)))

/-- Candidate-producing adversary with the public key fetched from the game. -/
@[reducible] noncomputable def candidateAdv
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt)
      (Stmt × (M × (Commit × Resp))) := do
  let pk ← (((cmaSpec M Commit Chal Resp Stmt).query .pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Stmt)
  let out ← postKeygenCandidateAdv (σ := σ) (hr := hr) (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk
  pure (pk, out)

/-- Lift a CMA-style Fiat-Shamir adversary into the named CMA game interface. -/
@[reducible] noncomputable def signedAdv
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt)
      ((M × (Commit × Resp)) × Bool) := do
  let pk ← (((cmaSpec M Commit Chal Resp Stmt).query .pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Stmt)
  let (msg, sig) ← (liftM (adv.main pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt)
      (M × (Commit × Resp)))
  let verified ← (liftM
    ((SourceSigAlg (σ := σ) (hr := hr) (M := M)).verify
      pk msg sig) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure ((msg, sig), verified)

/-- Log signing queries while forwarding every query to the surrounding CMA interface. -/
@[reducible] noncomputable def cmaSignLogImpl :
    QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (List M) (OracleComp (cmaSpec M Commit Chal Resp Stmt)))
  | .unif n => do
      let r ← (((cmaSpec M Commit Chal Resp Stmt).query (.unif n)) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) (Fin (n + 1)))
      pure r
  | .ro mc => do
      let r ← (((cmaSpec M Commit Chal Resp Stmt).query (.ro mc)) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)
      pure r
  | .sign m => do
      let signed ← get
      let sig ← (((cmaSpec M Commit Chal Resp Stmt).query (.sign m)) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) (Commit × Resp))
      set (signed ++ [m])
      pure sig
  | .pk => do
      let pk ← (((cmaSpec M Commit Chal Resp Stmt).query .pk) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) Stmt)
      pure pk

/-- Log signing queries while producing the final candidate, before verification. -/
@[reducible] noncomputable def signedCandidateAdv
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt)
      ((Stmt × (M × (Commit × Resp))) × List M) := do
  (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) (Stmt := Stmt)) (candidateAdv σ hr M adv)).run []

/-- Freshness and verification check attached after candidate production. -/
@[reducible] noncomputable def verifyFreshComp
    (p : (Stmt × (M × (Commit × Resp))) × List M) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool := do
  let pk := p.1.1
  let out := p.1.2
  let signed := p.2
  let verified ← (liftM
    ((SourceSigAlg (σ := σ) (hr := hr) (M := M)).verify
      pk out.1 out.2) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure (!decide (out.1 ∈ signed) && verified)

/-- Freshness-preserving Boolean adversary for the direct stateful CMA chain. -/
@[reducible] noncomputable def signedFreshAdv
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool :=
  signedCandidateAdv σ hr M adv >>= verifyFreshComp (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)

/-! ## Fixed-key post-keygen runtime -/

/-- The public post-keygen adversary/verification computation before it is
interpreted by the explicit random-oracle cache runtime. -/
@[reducible] noncomputable def postKeygenAdvBase
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) :
    SourceCmaComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      ((M × (Commit × Resp)) × Bool) := do
  let (msg, sig) ← adv.main pk
  let verified ← liftM
    ((SourceSigAlg (σ := σ) (hr := hr) (M := M)).verify
      pk msg sig)
  pure ((msg, sig), verified)

/-- Verification suffix attached after the fixed-key adversary produces a candidate. -/
private noncomputable def postVerifyComp
    (pk : Stmt) (x : M × (Commit × Resp)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt)
      ((M × (Commit × Resp)) × Bool) := do
  let verified ← (liftM
    ((SourceSigAlg (σ := σ) (hr := hr) (M := M)).verify
      pk x.1 x.2) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure (x, verified)

/-- Fixed-key adversary and verification computation over the named CMA interface. -/
@[reducible] noncomputable def postKeygenAdv
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt)
      ((M × (Commit × Resp)) × Bool) :=
  (postKeygenCandidateAdv (σ := σ) (hr := hr) (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk) >>=
    postVerifyComp (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) pk

/-- The public random-oracle runtime implemented by an explicit cache-state
`QueryImpl`. -/
@[reducible] noncomputable def fsBaseImpl :
    QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := by
  letI : DecidableEq (M × Commit) := inferInstance
  exact unifFwdImpl (M × Commit →ₒ Chal) +
    (randomOracle : QueryImpl (M × Commit →ₒ Chal) _)

/-- The Fiat-Shamir runtime-with-cache semantics is the explicit cache-state
implementation `fsBaseImpl`, observed from the chosen initial cache. -/
lemma runtimeWithCache_evalDist_eq_fsBaseImpl
    (cache : (M × Commit →ₒ Chal).QueryCache)
    {α : Type}
    (oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α) :
    (_root_.FiatShamir.runtimeWithCache M cache).evalDist oa =
      𝒟[(simulateQ
        (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)) oa).run'
        cache] := by
  unfold _root_.FiatShamir.runtimeWithCache ProbCompRuntime.evalDist
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
    (_root_.FiatShamir (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) σ hr M).sign
      pk sk

/-- The public post-keygen adversary handler with signing-query input logging.

Base queries run through the explicit cache-state runtime; signing queries are
handled by the fixed-key Fiat-Shamir signing oracle while appending each queried
message to a `StateT` list. -/
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

/-! ## Joint output of `cmaReal` -/

/-- Run the direct stateful `cmaReal` game against `signedAdv` and pack the
forgery, verification bit, and signed-message log into one probability
computation. -/
@[reducible] noncomputable def cmaRealRun
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    ProbComp ((M × (Commit × Resp)) × Bool × List M) := do
  let p ← (cmaReal M Commit Chal σ hr).runState
    (cmaInit M Commit Chal Stmt Wit) (signedAdv σ hr M adv)
  pure (p.1.1, p.1.2, p.2.1.1)

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The initial public-key query in `signedAdv` factors `cmaRealRun` through
the key generator and a fixed-key post-keygen run. -/
private lemma cmaRealRun_eq_keygen_bind
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    cmaRealRun σ hr M adv =
      (hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
        (cmaReal M Commit Chal σ hr).runState
          ((([] : List M), (∅ : RoCache M Commit Chal),
            (some (ps.1, ps.2) : Option (Stmt × Wit))), false)
          (postKeygenAdv σ hr M adv ps.1) >>=
          fun p => pure (p.1.1, p.1.2, p.2.1.1) := by
  unfold cmaRealRun signedAdv postKeygenAdv postKeygenCandidateAdv postVerifyComp
  simp only [QueryImpl.Stateful.runState, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind, bind_assoc]
  rw [show
      (id <$> cmaReal M Commit Chal σ hr CmaQuery.pk).run
          (cmaInit M Commit Chal Stmt Wit) =
        ((hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
          pure (ps.1,
            ((([] : List M), (∅ : RoCache M Commit Chal),
              (some (ps.1, ps.2) : Option (Stmt × Wit))), false))) by
    simp [cmaReal, cmaInit, StateT.run, StateT.mk]]
  simp only [bind_assoc, pure_bind]

/-! ## Joint signing/hash query bounds -/

/-- A named CMA query is costly for H3 exactly when it targets the signing
oracle. -/
def IsCostlyQuery : (cmaSpec M Commit Chal Resp Stmt).Domain → Prop
  | .sign _ => True
  | _ => False

instance : DecidablePred (IsCostlyQuery (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) := fun t =>
  match t with
  | .unif _ => isFalse fun h => h
  | .ro _ => isFalse fun h => h
  | .sign _ => isTrue trivial
  | .pk => isFalse fun h => h

/-- A named CMA query is a hash query exactly when it targets the random
oracle. -/
def IsHashQuery : (cmaSpec M Commit Chal Resp Stmt).Domain → Prop
  | .ro _ => True
  | _ => False

instance : DecidablePred (IsHashQuery (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) := fun t =>
  match t with
  | .unif _ => isFalse fun h => h
  | .ro _ => isTrue trivial
  | .sign _ => isFalse fun h => h
  | .pk => isFalse fun h => h

/-- Joint signing/hash query admissibility for the named CMA interface. -/
def cmaSignHashCanQuery :
    (cmaSpec M Commit Chal Resp Stmt).Domain → ℕ × ℕ → Prop
  | .unif _, _ => True
  | .ro _, (_, qH') => 0 < qH'
  | .sign _, (qS', _) => 0 < qS'
  | .pk, _ => True

/-- Joint signing/hash query budget update for the named CMA interface. -/
def cmaSignHashCost :
    (cmaSpec M Commit Chal Resp Stmt).Domain → ℕ × ℕ → ℕ × ℕ
  | .unif _, b => b
  | .ro _, (qS', qH') => (qS', qH' - 1)
  | .sign _, (qS', qH') => (qS' - 1, qH')
  | .pk, b => b

/-- Joint signing/hash query bound for computations over the named CMA interface. -/
def cmaSignHashQueryBound {α : Type}
    (oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (qS qH : ℕ) : Prop :=
  OracleComp.IsQueryBound oa (qS, qH)
    (cmaSignHashCanQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt))
    (cmaSignHashCost (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt))

omit [SampleableType Stmt] [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- Query-bind form of the joint signing/hash query bound. -/
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
  apply OracleComp.isQueryBound_query_bind_iff

omit [SampleableType Stmt] [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- A single named CMA query is joint-bounded exactly when the current
signing/hash budget admits that query. -/
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
/-- Pure computations do not consume signing or hash query budget. -/
lemma cmaSignHashQueryBound_pure {α : Type} (x : α) (qS qH : ℕ) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (pure x : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
      qS qH :=
  trivial

omit [SampleableType Stmt] [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- The joint signing/hash query bound is monotone in both budget
coordinates. -/
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
      cases t with
      | unif n => exact ⟨trivial, fun u => ih u (hcont u) hS hH⟩
      | ro mc => exact ⟨Nat.lt_of_lt_of_le hcan hH, fun u =>
          ih u (hcont u) hS (Nat.sub_le_sub_right hH 1)⟩
      | sign m => exact ⟨Nat.lt_of_lt_of_le hcan hS, fun u =>
          ih u (hcont u) (Nat.sub_le_sub_right hS 1) hH⟩
      | pk => exact ⟨trivial, fun u => ih u (hcont u) hS hH⟩

omit [SampleableType Stmt] [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- A bind is joint-bounded by the sum of the budgets for its prefix and
continuations. -/
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
      cases t with
      | unif n =>
          refine ⟨trivial, fun u => ?_⟩
          simpa [cmaSignHashCost] using ih u (hcont u)
      | ro mc =>
          refine ⟨Nat.add_pos_left hcan qH₂, fun u => ?_⟩
          have hrec := ih u (hcont u)
          have hEq : qH₁ - 1 + qH₂ = qH₁ + qH₂ - 1 := by
            have hpos : 1 ≤ qH₁ := Nat.succ_le_of_lt hcan
            omega
          simpa [cmaSignHashCost, hEq] using hrec
      | sign m =>
          refine ⟨Nat.add_pos_left hcan qS₂, fun u => ?_⟩
          have hrec := ih u (hcont u)
          have hEq : qS₁ - 1 + qS₂ = qS₁ + qS₂ - 1 := by
            have hpos : 1 ≤ qS₁ := Nat.succ_le_of_lt hcan
            omega
          simpa [cmaSignHashCost, hEq] using hrec
      | pk =>
          refine ⟨trivial, fun u => ?_⟩
          simpa [cmaSignHashCost] using ih u (hcont u)

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
/-- Fiat-Shamir verification consumes exactly one random-oracle query and no
signing queries in the named CMA interface. -/
lemma fiatShamir_verify_cmaSignHashQueryBound
    (pk : Stmt) (msg : M) (sig : Commit × Resp)
    (qS qH : ℕ) (hQ : 0 < qH) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (liftM
        ((_root_.FiatShamir
          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
          pk msg sig) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
      qS qH := by
  rcases sig with ⟨c, resp⟩
  simpa [_root_.FiatShamir, cmaSignHashCanQuery] using
    (cmaSignHashQueryBound_query_iff (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt)
      (t := CmaQuery.ro (M := M) (Commit := Commit) (msg, c)) qS qH).2 hQ

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
/-- Lifting a source post-keygen CMA computation into the named CMA interface
preserves its joint signing/hash query bound. -/
private theorem liftAdv_cmaSignHashQueryBound
    {α : Type}
    (oa : SourceCmaComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) α)
    (qS qH : ℕ)
    (hQ : signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := oa) qS qH) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) qS qH := by
  induction oa using OracleComp.inductionOn generalizing qS qH with
  | pure x =>
      simp [cmaSignHashQueryBound]
  | query_bind t cont ih =>
      simp only [signHashQueryBound, OracleComp.isQueryBoundP_query_bind_iff] at hQ
      rcases hQ with ⟨hinr, hinl⟩
      rcases t with (n | mc) | m
      all_goals simp only [Bool.false_eq_true, not_false_eq_true, true_or, add_apply_inl,
        add_apply_inr, ↓reduceIte, true_and, not_true_eq_false, false_or] at hinr hinl
      · exact ⟨trivial, fun u => by simpa using ih u qS qH ⟨hinr u, hinl u⟩⟩
      · exact ⟨hinl.1, fun u => by simpa using ih u qS (qH - 1) ⟨hinr u, hinl.2 u⟩⟩
      · exact ⟨hinr.1, fun u => by simpa using ih u (qS - 1) qH ⟨hinr.2 u, hinl u⟩⟩

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
/-- The fixed-key candidate adversary inherits the source adversary's joint
signing/hash query bound. -/
theorem postKeygenCandidateAdv_cmaSignHashQueryBound
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
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
/-- Fetching the public key before running the candidate adversary does not
consume signing or hash budget. -/
theorem candidateAdv_cmaSignHashQueryBound
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
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

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
/-- Adding the final Fiat-Shamir verification suffix increases only the hash
budget by one. -/
private theorem liftAdv_bind_verify_cmaSignHashQueryBound
    (pk : Stmt)
    (oa : SourceCmaComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (M × (Commit × Resp)))
    (qS qH : ℕ)
    (hQ : signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := oa) qS qH) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
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
      simp only [signHashQueryBound, OracleComp.isQueryBoundP_query_bind_iff] at hQ
      rcases hQ with ⟨hcan, hcont⟩
      rcases t with (n | mc) | m
      all_goals simp only [Bool.false_eq_true, not_false_eq_true, true_or, add_apply_inl,
        add_apply_inr, ↓reduceIte, true_and, not_true_eq_false, false_or] at hcan hcont
      · refine ⟨trivial, fun u => ?_⟩
        simpa [cmaSignHashQueryBound] using ih u qS qH ⟨hcan u, hcont u⟩
      · refine ⟨Nat.succ_pos qH, fun u => ?_⟩
        have hEq : qH - 1 + 1 = qH := Nat.sub_add_cancel hcont.1
        simpa [cmaSignHashQueryBound, hEq] using ih u qS (qH - 1) ⟨hcan u, hcont.2 u⟩
      · refine ⟨hcan.1, fun u => ?_⟩
        simpa [cmaSignHashQueryBound] using ih u (qS - 1) qH ⟨hcan.2 u, hcont u⟩

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
/-- The fixed-key adversary followed by verification is bounded by the source
adversary budget plus one verifier hash query. -/
theorem postKeygenAdv_cmaSignHashQueryBound
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
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
/-- The lifted CMA adversary with its initial public-key query is bounded by the
source adversary budget plus one verifier hash query. -/
theorem signedAdv_cmaSignHashQueryBound
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
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
/-- Logging signing inputs while forwarding all queries preserves the joint
signing/hash query bound. -/
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
      cases t with
      | unif n =>
          rw [simulateQ_query_bind, StateT.run_bind]
          simp only [OracleQuery.input_query, bind_pure, monadLift_self,
            StateT.run_monadLift, bind_pure_comp, bind_map_left]
          change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt)
            (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.unif n)) >>=
              fun u => (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) (cont u)).run signed)
            qS qH
          rw [cmaSignHashQueryBound_query_bind_iff]
          refine ⟨trivial, fun u => ?_⟩
          simpa [cmaSignHashQueryBound] using ih u signed qS qH (hcont u)
      | ro mc =>
          rw [simulateQ_query_bind, StateT.run_bind]
          simp only [OracleQuery.input_query, bind_pure, monadLift_self,
            StateT.run_monadLift, bind_pure_comp, bind_map_left]
          change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt)
            (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.ro mc)) >>=
              fun u => (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) (cont u)).run signed)
            qS qH
          rw [cmaSignHashQueryBound_query_bind_iff]
          refine ⟨hcan, fun u => ?_⟩
          simpa [cmaSignHashQueryBound] using ih u signed qS (qH - 1) (hcont u)
      | sign m =>
          rw [simulateQ_query_bind, StateT.run_bind]
          simp only [OracleQuery.input_query, monadLift_self]
          change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt)
            (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.sign m)) >>=
              fun sig => (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) (cont sig)).run (signed ++ [m]))
            qS qH
          rw [cmaSignHashQueryBound_query_bind_iff]
          refine ⟨hcan, fun sig => ?_⟩
          simpa [cmaSignHashQueryBound] using ih sig (signed ++ [m]) (qS - 1) qH (hcont sig)
      | pk =>
          rw [simulateQ_query_bind, StateT.run_bind]
          simp only [OracleQuery.input_query, bind_pure, monadLift_self,
            StateT.run_monadLift, bind_pure_comp, bind_map_left]
          change cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt)
            (liftM ((cmaSpec M Commit Chal Resp Stmt).query .pk) >>=
              fun pk => (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) (cont pk)).run signed)
            qS qH
          rw [cmaSignHashQueryBound_query_bind_iff]
          refine ⟨trivial, fun pk => ?_⟩
          simpa [cmaSignHashQueryBound] using ih pk signed qS qH (hcont pk)

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal]
  [DecidableEq M] [DecidableEq Commit] in
/-- The signed-candidate wrapper has the same joint signing/hash query bound as
the source adversary. -/
theorem signedCandidateAdv_cmaSignHashQueryBound
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
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
/-- The freshness-verification continuation consumes one hash query and no
signing queries. -/
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
/-- The final freshness-preserving Boolean adversary is bounded by the source
adversary budget plus one verifier hash query. -/
theorem signedFreshAdv_cmaSignHashQueryBound
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
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

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
/-- Extract the predicate-targeted H3 signing-query bound from the joint
named-CMA sign/hash budget. -/
theorem cmaSignHashQueryBound_to_costly {α : Type}
    {A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α}
    {qS qH : ℕ}
    (hA : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) A qS qH) :
    A.IsQueryBoundP
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt)) qS := by
  rw [OracleComp.isQueryBoundP_def]
  refine OracleComp.IsQueryBound.proj
    (B := ℕ × ℕ) (B' := ℕ)
    (proj := fun b : ℕ × ℕ => b.1)
    (oa := A) (b := (qS, qH))
    (canQuery := cmaSignHashCanQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (cost := cmaSignHashCost (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (canQuery' := fun t b => ¬ IsCostlyQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) t ∨ 0 < b)
    (cost' := fun t b => if IsCostlyQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) t then b - 1 else b)
    ?_ ?_ ?_
  · intro t b hcan
    cases t with
    | unif n => exact Or.inl (fun h => h)
    | ro mc => exact Or.inl (fun h => h)
    | sign m => exact Or.inr hcan
    | pk => exact Or.inl (fun h => h)
  · intro t b hcan
    cases t <;> simp [cmaSignHashCanQuery, cmaSignHashCost, IsCostlyQuery] at hcan ⊢
  · simpa [cmaSignHashQueryBound] using hA

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
/-- Extract the predicate-targeted H3 hash-query bound from the joint named-CMA
sign/hash budget. -/
theorem cmaSignHashQueryBound_to_hash {α : Type}
    {A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α}
    {qS qH : ℕ}
    (hA : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) A qS qH) :
    A.IsQueryBoundP
      (IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt)) qH := by
  rw [OracleComp.isQueryBoundP_def]
  refine OracleComp.IsQueryBound.proj
    (B := ℕ × ℕ) (B' := ℕ)
    (proj := fun b : ℕ × ℕ => b.2)
    (oa := A) (b := (qS, qH))
    (canQuery := cmaSignHashCanQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (cost := cmaSignHashCost (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (canQuery' := fun t b => ¬ IsHashQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) t ∨ 0 < b)
    (cost' := fun t b => if IsHashQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) t then b - 1 else b)
    ?_ ?_ ?_
  · intro t b hcan
    cases t with
    | unif n => exact Or.inl (fun h => h)
    | ro mc => exact Or.inr hcan
    | sign m => exact Or.inl (fun h => h)
    | pk => exact Or.inl (fun h => h)
  · intro t b hcan
    cases t <;> simp [cmaSignHashCanQuery, cmaSignHashCost, IsHashQuery] at hcan ⊢
  · simpa [cmaSignHashQueryBound] using hA

end FiatShamir.Stateful
