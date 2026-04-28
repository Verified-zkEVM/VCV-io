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
import VCVio.OracleComp.QueryTracking.SubSpec

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
noncomputable def postVerifyComp
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

/-! ## Fixed-key post-keygen probability normal form -/

/-- Fixed-key post-keygen experiment in the full direct CMA state.

The keypair is installed before the adversary runs, and the final freshness
check reads the signed-message log from the resulting `CmaState`. This is the
canonical normal form used by the stateful CMA chain. -/
@[reducible] noncomputable def postKeygenFreshProb
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) (sk : Wit) : ProbComp Bool := by
  exact
    (simulateQ (cmaRealSourceFullSum M Commit Chal σ hr)
      (postKeygenAdvBase (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk)).run
      ((([] : List M), (∅ : RoCache M Commit Chal),
        (some (pk, sk) : Option (Stmt × Wit))), false) >>= fun z =>
      let out := z.1.1
      let verified := z.1.2
      let signed := z.2.1.1
      pure (!decide (out.1 ∈ signed) && verified)

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
lemma cmaRealRun_eq_keygen_bind
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

omit [SampleableType Stmt] [SampleableType Wit] in
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

/-- Joint signing/hash query bound for computations over the named CMA interface. -/
def cmaSignHashQueryBound {α : Type}
    (oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (qS qH : ℕ) : Prop :=
  oa.IsQueryBoundP
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt)) qS ∧
    oa.IsQueryBoundP
      (IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt)) qH

omit [SampleableType Stmt] [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- Query-bind form of the joint signing/hash query bound. -/
@[simp]
private lemma cmaSignHashQueryBound_query_bind_iff {α : Type}
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (oa : (cmaSpec M Commit Chal Resp Stmt).Range t →
      OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (qS qH : ℕ) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)
      (liftM ((cmaSpec M Commit Chal Resp Stmt).query t) >>= oa) qS qH ↔
      ((¬ IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt) t ∨ 0 < qS) ∧
        (¬ IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt) t ∨ 0 < qH)) ∧
      ∀ u,
        cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (oa u)
          (if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt) t then qS - 1 else qS)
          (if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt) t then qH - 1 else qH) := by
  cases t with
  | unif n =>
      simp only [cmaSignHashQueryBound, IsCostlyQuery, IsHashQuery,
        OracleComp.isQueryBoundP_query_bind_iff, not_false_eq_true, true_or,
        if_false, true_and]
      constructor
      · intro h u
        exact ⟨h.1 u, h.2 u⟩
      · intro h
        exact ⟨fun u => (h u).1, fun u => (h u).2⟩
  | ro mc =>
      simp only [cmaSignHashQueryBound, IsCostlyQuery, IsHashQuery,
        OracleComp.isQueryBoundP_query_bind_iff, not_false_eq_true, true_or,
        not_true_eq_false, false_or, if_true, if_false, true_and]
      constructor
      · intro h
        exact ⟨h.2.1, fun u => ⟨h.1 u, h.2.2 u⟩⟩
      · intro h
        exact ⟨fun u => (h.2 u).1, h.1, fun u => (h.2 u).2⟩
  | sign m =>
      simp only [cmaSignHashQueryBound, IsCostlyQuery, IsHashQuery,
        OracleComp.isQueryBoundP_query_bind_iff, not_false_eq_true, true_or,
        not_true_eq_false, false_or, if_true, if_false, true_and, Prod.forall]
      constructor
      · intro h
        exact ⟨⟨h.1.1, trivial⟩, fun a b => ⟨h.1.2 a b, h.2 a b⟩⟩
      · intro h
        exact ⟨⟨h.1.1, fun a b => (h.2 a b).1⟩, fun a b => (h.2 a b).2⟩
  | pk =>
      simp only [cmaSignHashQueryBound, IsCostlyQuery, IsHashQuery,
        OracleComp.isQueryBoundP_query_bind_iff, not_false_eq_true, true_or,
        if_false, true_and]
      constructor
      · intro h u
        exact ⟨h.1 u, h.2 u⟩
      · intro h
        exact ⟨fun u => (h u).1, fun u => (h u).2⟩

omit [SampleableType Stmt] [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- A bind is joint-bounded by the sum of the budgets for its prefix and
continuations. -/
private lemma cmaSignHashQueryBound_bind {α β : Type}
    {oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α}
    {ob : α → OracleComp (cmaSpec M Commit Chal Resp Stmt) β}
    {qS₁ qH₁ qS₂ qH₂ : ℕ}
    (h₁ : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) oa qS₁ qH₁)
    (h₂ : ∀ x, cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (ob x) qS₂ qH₂) :
    cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (oa >>= ob) (qS₁ + qS₂) (qH₁ + qH₂) := by
  exact ⟨isQueryBoundP_bind h₁.1 (fun x _ => (h₂ x).1),
    isQueryBoundP_bind h₁.2 (fun x _ => (h₂ x).2)⟩

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] in
/-- Fiat-Shamir verification consumes exactly one random-oracle query and no
signing queries in the named CMA interface. -/
private lemma fiatShamir_verify_cmaSignHashQueryBound
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
  simpa [_root_.FiatShamir] using
    (cmaSignHashQueryBound_query_bind_iff (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt)
      (t := CmaQuery.ro (M := M) (Commit := Commit) (msg, c))
      (oa := fun x => pure x) qS qH).2
      ⟨⟨by simp [IsCostlyQuery], by simpa [IsHashQuery] using hQ⟩,
        by simp [cmaSignHashQueryBound]⟩

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
  rw [signHashQueryBound] at hQ
  constructor
  · simpa [OracleComp.liftComp_eq_liftM] using
      OracleComp.IsQueryBoundP.liftComp_subSpec
        (superSpec := cmaSpec M Commit Chal Resp Stmt)
        (q := IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        (hpq := by
          intro t
          rcases t with (n | mc) | m <;> simp [IsCostlyQuery])
        hQ.1
  · simpa [OracleComp.liftComp_eq_liftM] using
      OracleComp.IsQueryBoundP.liftComp_subSpec
        (superSpec := cmaSpec M Commit Chal Resp Stmt)
        (q := IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        (hpq := by
          intro t
          rcases t with (n | mc) | m <;> simp [IsHashQuery])
        hQ.2

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
  constructor
  · exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step hA.1
      (fun t s => by
        cases t <;>
          simp [cmaSignLogImpl, IsCostlyQuery, StateT.run_monadLift,
            StateT.run_get, StateT.run_set, monadLift_self, bind_pure_comp])
      signed
  · exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step hA.2
      (fun t s => by
        cases t <;>
          simp [cmaSignLogImpl, IsHashQuery, StateT.run_monadLift,
            StateT.run_get, StateT.run_set, monadLift_self, bind_pure_comp])
      signed

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M] [SampleableType Chal]
  [DecidableEq Commit] in
/-- Candidate production, with signing queries logged before final verification,
preserves the source adversary signing/hash query budget. -/
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
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt)
    (candidateAdv σ hr M adv) [] qS qH (by
      rw [candidateAdv]
      rw [cmaSignHashQueryBound_query_bind_iff]
      refine ⟨⟨by simp [IsCostlyQuery], by simp [IsHashQuery]⟩, fun pk => ?_⟩
      simpa [cmaSignHashQueryBound, postKeygenCandidateAdv] using
        liftAdv_cmaSignHashQueryBound (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt)
          (oa := adv.main pk) qS qH (hQ pk))

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
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        adv qS qH hQ)
      (fun p => by
        rcases p with ⟨⟨pk, msg, sig⟩, signed⟩
        simpa [verifyFreshComp, cmaSignHashQueryBound] using
          fiatShamir_verify_cmaSignHashQueryBound (σ := σ) (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) pk msg sig 0 1
            (Nat.succ_pos 0))

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal]
  [DecidableEq Commit] in
/-- Predicate-targeted signing-query bound for the final freshness-preserving
CMA adversary. -/
theorem signedFreshAdv_isQueryBoundP_costly
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    (signedFreshAdv σ hr M adv).IsQueryBoundP
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt)) qS :=
  (signedFreshAdv_cmaSignHashQueryBound (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      adv qS qH hQ).1

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M] [SampleableType Chal]
  [DecidableEq Commit] in
/-- Predicate-targeted signing-query bound for candidate production before the
final verification suffix. -/
theorem signedCandidateAdv_isQueryBoundP_costly
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    (signedCandidateAdv σ hr M adv).IsQueryBoundP
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt)) qS :=
  (signedCandidateAdv_cmaSignHashQueryBound (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      adv qS qH hQ).1

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M] [SampleableType Chal]
  [DecidableEq Commit] in
/-- Predicate-targeted hash-query bound for candidate production before the
final verification suffix. -/
theorem signedCandidateAdv_isQueryBoundP_hash
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    (signedCandidateAdv σ hr M adv).IsQueryBoundP
      (IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt)) qH :=
  (signedCandidateAdv_cmaSignHashQueryBound (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      adv qS qH hQ).2

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal]
  [DecidableEq Commit] in
/-- Predicate-targeted hash-query bound for the final freshness-preserving CMA
adversary. The extra query is the final Fiat-Shamir verification. -/
theorem signedFreshAdv_isQueryBoundP_hash
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    (signedFreshAdv σ hr M adv).IsQueryBoundP
      (IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt)) (qH + 1) :=
  (signedFreshAdv_cmaSignHashQueryBound (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      adv qS qH hQ).2

end FiatShamir.Stateful
