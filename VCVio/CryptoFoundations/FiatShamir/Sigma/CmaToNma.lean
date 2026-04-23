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

This file contains the managed-RO NMA adversary construction shared by the
HeapSSP Fiat-Shamir theorem chain and the public Sigma security theorem.

The construction is the standard "simulated CMA" adversary: run the CMA
adversary's main computation, replace signing queries with simulator
transcripts, program the managed random-oracle cache on each simulated
signature, and return the final forgery together with that cache. The query
bound below shows that live NMA random-oracle queries are exactly the source
adversary's live hash queries; simulator-programmed signing queries are
absorbed into the managed cache.

The quantitative CMA-to-NMA theorem itself lives in
`Sigma/HeapSSP/Chain.lean`, so the public proof path has a single HeapSSP
source of truth.
-/

universe u v

open OracleComp OracleSpec

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

omit [SampleableType Stmt] [SampleableType Wit] in
/-- CMA-to-NMA reduction at the managed-RO interface.

Builds a `managedRoNmaAdv` from a CMA adversary `adv` and an HVZK
simulator `simTranscript`: runs `adv.main pk` under a handler that
forwards live RO queries (with cache side-effects), handles signing
queries by sampling from `simTranscript` and programming the cache,
and returns the final cache together with the forgery.

This is the concrete-interface reduction entering the replay-forking lemma. -/
def simulatedNmaAdv
    [DecidableEq M] [DecidableEq Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M) :=
  let spec := unifSpec + (M × Commit →ₒ Chal)
  let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
    fun n => fwd (.inl n)
  let roSim : QueryImpl (M × Commit →ₒ Chal)
      (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none => do
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  let baseSim : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    unifSim + roSim
  let sigSim : Stmt → QueryImpl (M →ₒ (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun pk msg => do
    let (c, ω, s) ← simulateQ unifSim (simTranscript pk)
    modifyGet fun cache =>
      match cache (.inr (msg, c)) with
      | some _ => ((c, s), cache)
      | none => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)
  ⟨fun pk => (simulateQ (baseSim + sigSim pk) (adv.main pk)).run ∅⟩

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Hash-query bound for `simulatedNmaAdv`: if the CMA adversary makes at most
`qS` signing-oracle queries and `qH` random-oracle queries, the NMA reduction
makes at most `qH` live hash queries. The `qS` signing queries are absorbed
into the managed cache rather than issued live. -/
theorem simulatedNmaAdv_hashQueryBound
    [DecidableEq M] [DecidableEq Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulatedNmaAdv (σ := σ) (hr := hr) (M := M)
        (simTranscript := simTranscript) (adv := adv)).main pk) qH := by
  letI : Fintype Chal := Fintype.ofFinite Chal
  let spec := unifSpec + (M × Commit →ₒ Chal)
  let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
    fun n => fwd (.inl n)
  let roSim : QueryImpl (M × Commit →ₒ Chal)
      (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none => do
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  let baseSim : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    unifSim + roSim
  let sigSim : Stmt → QueryImpl (M →ₒ (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun pk msg => do
    let (c, ω, s) ← simulateQ unifSim (simTranscript pk)
    modifyGet fun cache =>
      match cache (.inr (msg, c)) with
      | some _ => ((c, s), cache)
      | none => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)
  let nmaAdv := simulatedNmaAdv (σ := σ) (hr := hr) (M := M)
    (simTranscript := simTranscript) (adv := adv)
  intro pk
  let stepBudget :
      (spec + (M →ₒ (Commit × Resp))).Domain → ℕ × ℕ → ℕ := fun t _ =>
    match t with
    | .inl (.inl _) => 0
    | .inl (.inr _) => 1
    | .inr _ => 0
  have hbind :
      ∀ {α β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β} {Q₁ Q₂ : ℕ},
        nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁ →
        (∀ x, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := ob x) Q₂) →
        nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := oa >>= ob) (Q₁ + Q₂) := by
    intro α β oa ob Q₁ Q₂ h1 h2
    exact nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal) h1 h2
  have hfwd :
      ∀ (t : spec.Domain) (s : spec.QueryCache),
        nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (fwd t).run s) (match t with
            | .inl _ => 0
            | .inr _ => 1) := by
    intro t s
    cases t with
    | inl n =>
        simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
          OracleComp.liftM_run_StateT] using
          (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
            (show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (oa := liftM (spec.query (.inl n))) 0 by
                exact
                  (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
                    (.inl n) 0).2 trivial)
            (fun u =>
              show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := pure (u, s)) 0 by
                  trivial))
    | inr mc =>
        simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
          OracleComp.liftM_run_StateT] using
          (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
            (show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (oa := liftM (spec.query (.inr mc))) 1 by
                exact
                  (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
                    (.inr mc) 1).2 (Nat.succ_pos 0))
            (fun u =>
              show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := pure (u, s)) 0 by
                  trivial))
  have hro :
      ∀ (mc : M × Commit) (s : spec.QueryCache),
        nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (roSim mc).run s) 1 := by
    intro mc s
    cases hs : s (.inr mc) with
    | some v =>
        simp [roSim, hs, nmaHashQueryBound]
    | none =>
        simpa [roSim, hs] using
          ((OracleComp.isQueryBound_map_iff
              (oa := (fwd (.inr mc)).run s)
              (f := fun a : Chal × spec.QueryCache =>
                (a.1, a.2.cacheQuery (.inr mc) a.1))
              (b := 1)
              (canQuery := fun t b => match t with
                | .inl _ => True
                | .inr _ => 0 < b)
              (cost := fun t b => match t with
                | .inl _ => b
                | .inr _ => b - 1)).2
            (hfwd (.inr mc) s))
  have hsig :
      ∀ (msg : M) (s : spec.QueryCache),
        nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (sigSim pk msg).run s) 0 := by
    intro msg s
    have hsource : OracleComp.IsQueryBound
        (simTranscript pk) () (fun _ _ => True) (fun _ _ => ()) := by
      induction simTranscript pk using OracleComp.inductionOn with
      | pure x =>
          trivial
      | query_bind t mx ih =>
          simp [OracleComp.isQueryBound_query_bind_iff, ih]
    have htranscript :
        nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (simulateQ unifSim (simTranscript pk)).run s) 0 := by
      simpa [nmaHashQueryBound] using
        (OracleComp.IsQueryBound.simulateQ_run_of_step
          (h := hsource) (combine := Nat.add) (mapBudget := fun _ => 0)
          (stepBudget := fun _ _ => 0) (impl := unifSim)
          (hbind := by
            intro γ δ oa' ob b₁ b₂ h1 h2
            have h1' :
                nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := oa') b₁ := by
              simpa [nmaHashQueryBound] using h1
            have h2' : ∀ x,
                nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := ob x) b₂ := by
              intro x
              simpa [nmaHashQueryBound] using h2 x
            simpa [nmaHashQueryBound] using
              (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
                (oa := oa') (ob := ob) (Q₁ := b₁) (Q₂ := b₂) h1' h2')
          )
          (hstep := by
            intro t b s' ht
            simpa [unifSim] using hfwd (.inl t) s')
          (hcombine := by
            intro t b ht
            simp)
          (s := s))
    simpa [sigSim, nmaHashQueryBound] using
      ((OracleComp.isQueryBound_map_iff
          (oa := (simulateQ unifSim (simTranscript pk)).run s)
          (f := fun a : (Commit × Chal × Resp) × spec.QueryCache =>
            match a.2 (.inr (msg, a.1.1)) with
            | some _ => ((a.1.1, a.1.2.2), a.2)
            | none =>
            ((a.1.1, a.1.2.2),
              QueryCache.cacheQuery a.2 (.inr (msg, a.1.1)) a.1.2.1))
          (b := 0)
          (canQuery := fun t b => match t with
            | .inl _ => True
            | .inr _ => 0 < b)
          (cost := fun t b => match t with
            | .inl _ => b
            | .inr _ => b - 1)).2 htranscript)
  have hstep :
      ∀ t b s,
        (match t, b with
          | .inl (.inl _), _ => True
          | .inl (.inr _), (_, qH') => 0 < qH'
          | .inr _, (qS', _) => 0 < qS') →
        nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := ((baseSim + sigSim pk) t).run s) (stepBudget t b) := by
    intro t b s ht
    rcases b with ⟨qS', qH'⟩
    cases t with
    | inl t =>
        cases t with
        | inl n =>
            simpa [baseSim, stepBudget] using hfwd (.inl n) s
        | inr mc =>
            simpa [baseSim, stepBudget] using hro mc s
    | inr msg =>
        simpa [stepBudget] using hsig msg s
  have hcombine :
      ∀ t b,
        (match t, b with
          | .inl (.inl _), _ => True
          | .inl (.inr _), (_, qH') => 0 < qH'
          | .inr _, (qS', _) => 0 < qS') →
        Nat.add (stepBudget t b)
          (Prod.snd (match t, b with
            | .inl (.inl _), b' => b'
            | .inl (.inr _), (qS', qH') => (qS', qH' - 1)
            | .inr _, (qS', qH') => (qS' - 1, qH'))) =
          Prod.snd b := by
    intro t b ht
    rcases b with ⟨qS', qH'⟩
    cases t with
    | inl t =>
        cases t with
        | inl n =>
            simp [stepBudget]
        | inr mc =>
            simp [stepBudget] at ht ⊢
            omega
    | inr msg =>
        simp [stepBudget]
  simpa [nmaAdv, simulatedNmaAdv, nmaHashQueryBound, signHashQueryBound] using
    (OracleComp.IsQueryBound.simulateQ_run_of_step
      (h := hQ pk) (combine := Nat.add) (mapBudget := Prod.snd)
      (stepBudget := stepBudget) (impl := baseSim + sigSim pk)
      (hbind := by
        intro γ δ oa' ob b₁ b₂ h1 h2
        have h1' :
            nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (oa := oa') b₁ := by
          simpa [nmaHashQueryBound] using h1
        have h2' : ∀ x,
            nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (oa := ob x) b₂ := by
          intro x
          simpa [nmaHashQueryBound] using h2 x
        simpa [nmaHashQueryBound] using
          (hbind (oa := oa') (ob := ob) (Q₁ := b₁) (Q₂ := b₂) h1' h2')
      )
      (hstep := by
        intro t b s ht
        rcases b with ⟨qS', qH'⟩
        cases t with
        | inl t =>
            cases t with
            | inl n =>
                simpa [nmaHashQueryBound, baseSim, stepBudget] using hfwd (.inl n) s
            | inr mc =>
                simpa [nmaHashQueryBound, baseSim, stepBudget] using hro mc s
        | inr msg =>
            simpa [nmaHashQueryBound, stepBudget] using hsig msg s)
      (hcombine := by
        intro t b ht
        rcases b with ⟨qS', qH'⟩
        cases t with
        | inl t =>
            cases t with
            | inl n =>
                simp [stepBudget]
            | inr mc =>
                simp [stepBudget] at ht ⊢
                omega
        | inr msg =>
            simp [stepBudget])
      (s := ∅))

end FiatShamir
