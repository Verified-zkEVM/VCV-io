/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import VCVio.CryptoFoundations.FiatShamir.QueryBounds

/-!
# CMA-to-NMA reduction for Fiat-Shamir on Σ-protocols

This file contains the managed-RO NMA adversary construction used by the
stateful Fiat-Shamir theorem chain and the public Sigma security theorem.

The construction is the standard "simulated CMA" adversary: run the CMA
adversary's main computation, replace signing queries with simulator
transcripts, program the managed random-oracle cache on each simulated
signature, and return the final forgery together with that cache. The query
bound below shows that live NMA random-oracle queries are exactly the source
adversary's live hash queries; simulator-programmed signing queries are
absorbed into the managed cache.

The quantitative CMA-to-NMA theorem itself lives in
`Sigma/Stateful/Chain.lean`, so the public proof path has a single stateful
source of truth.
-/

universe u v

open OracleComp OracleSpec

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type}
    [Fintype Chal] [Finite Commit] [Finite Resp]
    [Inhabited Chal] [Inhabited Commit] [Inhabited Resp]
    {rel : Stmt → Wit → Bool}

variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

/-! ### Simulator handler components -/

abbrev fsRoSpec (M Commit Chal : Type) : OracleSpec (ℕ ⊕ (M × Commit)) :=
  unifSpec + (M × Commit →ₒ Chal)

abbrev cmaOracleSpec (M Commit Chal Resp : Type) :
    OracleSpec ((ℕ ⊕ (M × Commit)) ⊕ M) :=
  fsRoSpec M Commit Chal + (M →ₒ (Commit × Resp))

noncomputable def simulatedNmaFwd
    [DecidableEq M] [DecidableEq Commit] :
    QueryImpl (fsRoSpec M Commit Chal)
      (StateT (fsRoSpec M Commit Chal).QueryCache
        (OracleComp (fsRoSpec M Commit Chal))) :=
  (HasQuery.toQueryImpl (spec := fsRoSpec M Commit Chal)
    (m := OracleComp (fsRoSpec M Commit Chal))).liftTarget _

noncomputable def simulatedNmaUnifSim
    [DecidableEq M] [DecidableEq Commit] :
    QueryImpl unifSpec
      (StateT (fsRoSpec M Commit Chal).QueryCache
        (OracleComp (fsRoSpec M Commit Chal))) :=
  fun n => simulatedNmaFwd (M := M) (Commit := Commit) (Chal := Chal) (.inl n)

noncomputable def simulatedNmaRoSim
    [DecidableEq M] [DecidableEq Commit] :
    QueryImpl (M × Commit →ₒ Chal)
      (StateT (fsRoSpec M Commit Chal).QueryCache
        (OracleComp (fsRoSpec M Commit Chal))) := fun mc => do
  let cache ← get
  match cache (.inr mc) with
  | some v => pure v
  | none => do
      let v ← simulatedNmaFwd (M := M) (Commit := Commit) (Chal := Chal) (.inr mc)
      modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)

noncomputable def simulatedNmaBaseSim
    [DecidableEq M] [DecidableEq Commit] :
    QueryImpl (fsRoSpec M Commit Chal)
      (StateT (fsRoSpec M Commit Chal).QueryCache
        (OracleComp (fsRoSpec M Commit Chal))) :=
  simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal) +
    simulatedNmaRoSim (M := M) (Commit := Commit) (Chal := Chal)

noncomputable def simulatedNmaSigSim
    [DecidableEq M] [DecidableEq Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (M →ₒ (Commit × Resp))
      (StateT (fsRoSpec M Commit Chal).QueryCache
        (OracleComp (fsRoSpec M Commit Chal))) := fun msg => do
  let (c, ω, s) ← simulateQ
    (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))
    (simTranscript pk)
  modifyGet fun cache =>
    match cache (.inr (msg, c)) with
    | some _ => ((c, s), cache)
    | none => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)

noncomputable def simulatedNmaImpl
    [DecidableEq M] [DecidableEq Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (fsRoSpec M Commit Chal).QueryCache
        (OracleComp (fsRoSpec M Commit Chal))) :=
  simulatedNmaBaseSim (M := M) (Commit := Commit) (Chal := Chal) +
    simulatedNmaSigSim (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simTranscript pk

omit [SampleableType Stmt] [SampleableType Wit] in
/-- CMA-to-NMA reduction at the managed-RO interface.

Builds a `managedRoNmaAdv` from a CMA adversary `adv` and an HVZK
simulator `simTranscript`: runs `adv.main pk` under a handler that
forwards live RO queries (with cache side-effects), handles signing
queries by sampling from `simTranscript` and programming the cache,
and returns the final cache together with the forgery.

This is the concrete-interface reduction entering the replay-forking lemma. -/
noncomputable def simulatedNmaAdv
    [DecidableEq M] [DecidableEq Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M) :=
  ⟨fun pk => (simulateQ
    (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simTranscript pk)
    (adv.main pk)).run ∅⟩

omit [Finite Commit] [Finite Resp] [Fintype Chal] [Inhabited Chal] [Inhabited Commit] in
omit [SampleableType Stmt] [SampleableType Wit] in
private theorem simulatedNmaFwd_run_hashQueryBound
    [DecidableEq M] [DecidableEq Commit]
    (t : (fsRoSpec M Commit Chal).Domain) (s : (fsRoSpec M Commit Chal).QueryCache) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulatedNmaFwd (M := M) (Commit := Commit) (Chal := Chal) t).run s)
      (match t with | .inl _ => 0 | .inr _ => 1) := by
  cases t with
  | inl n =>
      simpa [simulatedNmaFwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply] using
        nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
          ((nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
            (.inl n) 0).2 trivial)
          fun u => show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := pure (u, s)) 0 from trivial
  | inr mc =>
      simpa [simulatedNmaFwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply] using
        nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
          ((nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
            (.inr mc) 1).2 (Nat.succ_pos 0))
          fun u => show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := pure (u, s)) 0 from trivial

omit [Finite Commit] [Finite Resp] [Fintype Chal] [Inhabited Chal] [Inhabited Commit] in
omit [SampleableType Stmt] [SampleableType Wit] in
private theorem simulatedNmaRoSim_run_hashQueryBound
    [DecidableEq M] [DecidableEq Commit]
    (mc : M × Commit) (s : (fsRoSpec M Commit Chal).QueryCache) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulatedNmaRoSim (M := M) (Commit := Commit) (Chal := Chal) mc).run s) 1 := by
  cases hs : s (.inr mc) with
  | some v => simp [simulatedNmaRoSim, hs, nmaHashQueryBound]
  | none =>
      simpa [simulatedNmaRoSim, hs, nmaHashQueryBound, isQueryBoundP_map_iff] using
        simulatedNmaFwd_run_hashQueryBound (M := M) (.inr mc) s

omit [Fintype Chal] [Finite Commit] [Finite Resp] [Inhabited Resp] [Inhabited Commit] in
omit [SampleableType Stmt] [SampleableType Wit] in
private theorem simulatedNmaSigSim_run_hashQueryBound
    [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    (msg : M) (s : (fsRoSpec M Commit Chal).QueryCache) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulatedNmaSigSim (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) simTranscript pk msg).run s) 0 := by
  have : Fintype Chal := Fintype.ofFinite Chal
  let : IsUniformSpec ((M × Commit →ₒ Chal) : OracleSpec _) :=
    IsUniformSpec.ofFintypeInhabited _
  simpa [simulatedNmaSigSim, nmaHashQueryBound] using
    (OracleComp.isQueryBoundP_map_iff
      (oa := (simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))
        (simTranscript pk)).run s)
      (f := fun a : (Commit × Chal × Resp) × (fsRoSpec M Commit Chal).QueryCache =>
        match a.2 (.inr (msg, a.1.1)) with
        | some _ => ((a.1.1, a.1.2.2), a.2)
        | none => ((a.1.1, a.1.2.2),
            QueryCache.cacheQuery a.2 (.inr (msg, a.1.1)) a.1.2.1))
      (n := 0)).2
      (OracleComp.IsQueryBoundP.simulateQ_run_of_step (p := fun _ : ℕ => False)
        (OracleComp.isQueryBoundP_false _ _) (fun _ h _ => h.elim)
        (fun n _ s' => by
          simpa [simulatedNmaUnifSim, nmaHashQueryBound] using
            simulatedNmaFwd_run_hashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (.inl n) s') s)

omit [Finite Commit] [Finite Resp] [Fintype Chal] [Inhabited Chal] in
omit [SampleableType Stmt] [SampleableType Wit] in
/-- Hash-query bound for `simulatedNmaAdv`: if the CMA adversary makes at most
`qS` signing-oracle queries and `qH` random-oracle queries, the NMA reduction
makes at most `qH` live hash queries. The `qS` signing queries are absorbed
into the managed cache rather than issued live. -/
theorem simulatedNmaAdv_hashQueryBound
    [DecidableEq M] [DecidableEq Commit] [Finite Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    [Finite Resp]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulatedNmaAdv (σ := σ) (hr := hr) (M := M)
        (simTranscript := simTranscript) (adv := adv)).main pk) qH := by
  have : Fintype Chal := Fintype.ofFinite Chal
  have : Fintype Resp := Fintype.ofFinite Resp
  have : Fintype Commit := Fintype.ofFinite Commit
  let : IsUniformSpec ((M × Commit →ₒ Chal) : OracleSpec _) :=
    IsUniformSpec.ofFintypeInhabited _
  intro pk
  change nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
    (oa := (simulateQ (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simTranscript pk) (adv.main pk)).run ∅) qH
  unfold nmaHashQueryBound simulatedNmaImpl
  refine OracleComp.IsQueryBoundP.simulateQ_run_add_inl_of_step
    (fun _ => Bool.false_ne_true) (hQ pk).2 ?_ ?_ ?_ ∅
  · rintro (_ | mc) hp s'
    · simp at hp
    · exact simulatedNmaRoSim_run_hashQueryBound (M := M) mc s'
  · rintro (n | _) hnp s'
    · exact simulatedNmaFwd_run_hashQueryBound (M := M) (.inl n) s'
    · simp at hnp
  · intro msg s'
    exact simulatedNmaSigSim_run_hashQueryBound (M := M) (Resp := Resp) simTranscript pk msg s'

end FiatShamir
