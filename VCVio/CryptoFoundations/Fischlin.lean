/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.HasQuery
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryRuntime
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.BundledSemantics
import Mathlib.Data.FinEnum
import Mathlib.Data.Nat.Choose.Basic

/-!
# Fischlin Transform

This file defines the Fischlin transform (CRYPTO 2005), which converts a Σ-protocol
into a signature scheme (non-interactive proof of knowledge) in the random oracle model
with *online (straight-line) extraction*.

Unlike the Fiat-Shamir transform, which requires a rewinding extractor (via the forking lemma),
the Fischlin transform enables extraction by simply observing the prover's hash queries.
This comes at the cost of a more complex prover that performs a "proof-of-work" search
over the challenge space, and a slight completeness error.

## Parameters

* `ρ` — number of parallel repetitions
* `b` — hash output bit-length (random oracle range is `Fin (2^b)`)
* `S` — maximum allowed sum of hash values in a valid proof (paper notation)

## References

* Marc Fischlin, "Communication-Efficient Non-Interactive Proofs of Knowledge
  with Online Extractors", CRYPTO 2005.
-/

universe u v

open OracleComp OracleSpec

/-! ## Type Definitions -/

/-- Input to the Fischlin random oracle. Defined as a structure rather than a nested product
to give fast `DecidableEq` synthesis (avoiding deep product-type unfolding). -/
structure FischlinROInput (X PC Ω P : Type) (ρ : ℕ) (M : Type) where
  stmt : X
  msg : M
  comList : List PC
  rep : Fin ρ
  chal : Ω
  resp : P
  deriving DecidableEq

variable (X PC Ω P : Type) (ρ b : ℕ) (M : Type) in
/-- The random oracle specification for the Fischlin transform.
Domain: `FischlinROInput` (statement, message, commitment list, index, challenge, response).
Range: `Fin (2^b)` (b-bit hash values). -/
abbrev fischlinROSpec :=
  FischlinROInput X PC Ω P ρ M →ₒ Fin (2 ^ b)

variable (PC Ω P : Type) (ρ : ℕ) in
/-- A Fischlin proof consists of one `(commitment, challenge, response)` triple
per parallel repetition. -/
abbrev FischlinProof := Fin ρ → PC × Ω × P

/-! ## Prover Search -/

/-- Recursive search over a list of challenges for one Fischlin repetition.

For each challenge `ω`, computes the sigma protocol response and queries the hash oracle.
Exits early if a hash value of `0` is found (the ideal "proof of work" result).
Otherwise, tracks the `(challenge, response)` pair with the minimal hash value.

This models the sequential search in Construction 1 of the Fischlin paper:
the prover queries `H` on each input and keeps the best. -/
private def fischlinSearchAux {X W PC SC Ω P M : Type} {p : X → W → Bool} {ρ b : ℕ}
    {m : Type → Type v} [Monad m]
    (σ : SigmaProtocol X W PC SC Ω P p)
    [MonadLiftT ProbComp m] [HasQuery (fischlinROSpec X PC Ω P ρ b M) m]
    (pk : X) (sk : W) (sc : SC) (msg : M) (comList : List PC) (i : Fin ρ) :
    List Ω → Option (Ω × P × Fin (2 ^ b)) → m (Option (Ω × P))
  | [], best => return best.map fun (ω, resp, _) => (ω, resp)
  | ω :: rest, best => do
    let resp ← σ.respond pk sk sc ω
    let h ← HasQuery.query (spec := (fischlinROSpec X PC Ω P ρ b M))
      ⟨pk, msg, comList, i, ω, resp⟩
    if h.val = 0 then return some (ω, resp)
    else
      let newBest := match best with
        | none => some (ω, resp, h)
        | some (ω', resp', h') =>
          if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h')
      fischlinSearchAux σ pk sk sc msg comList i rest newBest

/-! ## Main Definition -/

variable {X W PC SC Ω P : Type}
    {p : X → W → Bool} [SampleableType X] [SampleableType W]
    [DecidableEq X] [DecidableEq PC] [DecidableEq Ω] [DecidableEq P]
    [FinEnum Ω] [Inhabited Ω] [Inhabited P] [SampleableType Ω]

/-- The Fischlin transform applied to a Σ-protocol and a generable relation produces
a signature scheme in the random oracle model.

**Signing**: generates `ρ` independent commitments, then for each repetition searches
through all challenges `ω ∈ Ω` (via `FinEnum.toList`) to find the `(ω, response)` pair
whose hash value is minimal, exiting early at hash `0`.

**Verification**: re-hashes each `(commitment, challenge, response)` triple, checks
sigma-protocol verification for each repetition, and verifies that the sum of hash
values is at most `S`. -/
def Fischlin
    {m : Type → Type v} [Monad m]
    (σ : SigmaProtocol X W PC SC Ω P p)
    (hr : GenerableRelation X W p) (ρ b S : ℕ) (M : Type)
    [DecidableEq M] [MonadLiftT ProbComp m]
    [HasQuery (fischlinROSpec X PC Ω P ρ b M) m] :
    SignatureAlg m
      (M := M) (PK := X) (SK := W) (S := FischlinProof PC Ω P ρ) where
  keygen := liftM hr.gen
  sign := fun pk sk msg => do
    let commits : Fin ρ → PC × SC ←
      Fin.mOfFn ρ fun _ => σ.commit pk sk
    let comVec : Fin ρ → PC := fun i => (commits i).1
    let comList := List.ofFn comVec
    Fin.mOfFn ρ fun i => do
      let sc_i := (commits i).2
      let result ←
        fischlinSearchAux
          σ pk sk sc_i msg comList i (FinEnum.toList Ω)
          (none : Option (Ω × P × Fin (2 ^ b)))
      match result with
      | some (ω, resp) => return (comVec i, ω, resp)
      | none => return (comVec i, default, default)
  verify := fun pk msg π => do
    let comVec : Fin ρ → PC := fun i => (π i).1
    let comList := List.ofFn comVec
    let results ← Fin.mOfFn ρ fun i => do
      let (_, ω_i, resp_i) := π i
      let h_i ← HasQuery.query (spec := (fischlinROSpec X PC Ω P ρ b M))
        ⟨pk, msg, comList, i, ω_i, resp_i⟩
      pure (σ.verify pk (comVec i) ω_i resp_i, h_i.val)
    let allVerified := (List.finRange ρ).all fun i => (results i).1
    let hashSum := (List.finRange ρ).foldl (fun acc i => acc + (results i).2) 0
    pure (allVerified && decide (hashSum ≤ S))

namespace Fischlin

variable {X W PC SC Ω P : Type} {p : X → W → Bool}
  [SampleableType X] [SampleableType W]
  [DecidableEq X] [DecidableEq PC] [DecidableEq Ω] [DecidableEq P]
  [FinEnum Ω] [Inhabited Ω] [Inhabited P] [SampleableType Ω]

variable (σ : SigmaProtocol X W PC SC Ω P p) (hr : GenerableRelation X W p)
  (ρ b S : ℕ) (M : Type) [DecidableEq M]

open ENNReal

/-- Runtime bundle for the Fischlin random-oracle world. -/
noncomputable def runtime
    (ρ b : ℕ) (M : Type) [DecidableEq M] :
    ProbCompRuntime (OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (fischlinROSpec X PC Ω P ρ b M)
        (StateT (fischlinROSpec X PC Ω P ρ b M).QueryCache ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

section costAccounting

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [HasEvalSet m]
  [MonadLiftT ProbComp m]

/-- Fischlin's inner search, instantiated in a concrete unit-cost runtime. -/
private def fischlinSearchAuxWithUnitCost
    {X W PC SC Ω P M : Type} {p : X → W → Bool} {ρ b : ℕ}
    {m : Type → Type v} [Monad m] [MonadLiftT ProbComp m]
    (σ : SigmaProtocol X W PC SC Ω P p)
    (runtime : QueryRuntime (fischlinROSpec X PC Ω P ρ b M) m)
    (pk : X) (sk : W) (sc : SC) (msg : M) (comList : List PC) (i : Fin ρ)
    (challenges : List Ω) (best : Option (Ω × P × Fin (2 ^ b))) :
    AddWriterT ℕ m (Option (Ω × P)) :=
  match challenges with
  | [] => pure (best.map fun (ω, resp, _) => (ω, resp))
  | ω :: rest => do
      let resp ← monadLift (σ.respond pk sk sc ω)
      AddWriterT.addTell (M := m) 1
      let h ← monadLift (runtime.impl ⟨pk, msg, comList, i, ω, resp⟩)
      if h.val = 0 then
        pure (some (ω, resp))
      else
        let newBest := match best with
          | none => some (ω, resp, h)
          | some (ω', resp', h') =>
            if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h')
        fischlinSearchAuxWithUnitCost σ runtime pk sk sc msg comList i rest newBest

omit [SampleableType X] [SampleableType W]
  [DecidableEq X] [DecidableEq PC] [DecidableEq Ω] [DecidableEq P]
  [FinEnum Ω] [Inhabited Ω] [Inhabited P] [SampleableType Ω]
  [DecidableEq M] [HasEvalSet m] in
private lemma fischlinSearchAux_eq_withUnitCost
    (runtime : QueryRuntime (fischlinROSpec X PC Ω P ρ b M) m)
    (pk : X) (sk : W) (sc : SC) (msg : M) (comList : List PC) (i : Fin ρ)
    (challenges : List Ω) (best : Option (Ω × P × Fin (2 ^ b))) :
    letI := runtime.withUnitCost.toHasQuery
    fischlinSearchAux
      (m := AddWriterT ℕ m) σ pk sk sc msg comList i challenges best =
      fischlinSearchAuxWithUnitCost
        (σ := σ) (runtime := runtime) (pk := pk) (sk := sk) (sc := sc) (msg := msg)
        (comList := comList) (i := i) challenges best := by
  induction challenges generalizing best with
  | nil =>
      simp [fischlinSearchAux, fischlinSearchAuxWithUnitCost]
  | cons ω rest ih =>
      simp [fischlinSearchAux, fischlinSearchAuxWithUnitCost,
        QueryRuntime.withUnitCost_impl, liftM, MonadLiftT.monadLift, ih]

omit [SampleableType X] [SampleableType W]
  [DecidableEq X] [DecidableEq PC] [DecidableEq Ω] [DecidableEq P]
  [FinEnum Ω] [Inhabited Ω] [Inhabited P] [SampleableType Ω]
  [DecidableEq M] in
private lemma fischlinSearchAuxWithUnitCost_queryBoundedAboveBy
    (runtime : QueryRuntime (fischlinROSpec X PC Ω P ρ b M) m)
    (pk : X) (sk : W) (sc : SC) (msg : M) (comList : List PC) (i : Fin ρ)
    (challenges : List Ω) (best : Option (Ω × P × Fin (2 ^ b))) :
    AddWriterT.QueryBoundedAboveBy
      (fischlinSearchAuxWithUnitCost
        (σ := σ) (runtime := runtime) (pk := pk) (sk := sk) (sc := sc) (msg := msg)
        (comList := comList) (i := i) challenges best)
      challenges.length := by
  induction challenges generalizing best with
  | nil =>
      exact AddWriterT.queryBoundedAboveBy_pure
        (m := m) ((best.map fun (ω, resp, _) => (ω, resp)) : Option (Ω × P))
  | cons ω rest ih =>
      let hashStep : P → AddWriterT ℕ m (Option (Ω × P)) := fun resp =>
        (AddWriterT.addTell (M := m) 1 : AddWriterT ℕ m PUnit) >>= fun _ =>
          (monadLift (runtime.impl ⟨pk, msg, comList, i, ω, resp⟩) :
            AddWriterT ℕ m (Fin (2 ^ b))) >>= fun h =>
              if h.val = 0 then
                pure (some (ω, resp))
              else
                fischlinSearchAuxWithUnitCost σ runtime pk sk sc msg comList i rest
                  (match best with
                  | none => some (ω, resp, h)
                  | some (ω', resp', h') =>
                      if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h'))
      change AddWriterT.QueryBoundedAboveBy
        ((monadLift (σ.respond pk sk sc ω) : AddWriterT ℕ m P) >>= hashStep)
        (rest.length + 1)
      refine AddWriterT.queryBoundedAboveBy_mono
        (AddWriterT.queryBoundedAboveBy_bind (n₁ := 0) (n₂ := 1 + rest.length)
          (AddWriterT.queryBoundedAboveBy_monadLift (m := m) (σ.respond pk sk sc ω))
          (fun resp => ?_))
        (by omega)
      refine AddWriterT.queryBoundedAboveBy_mono
        (AddWriterT.queryBoundedAboveBy_bind (n₁ := 1) (n₂ := rest.length)
          (AddWriterT.queryBoundedAboveBy_addTell 1)
          (fun _ => ?_))
        (by omega)
      refine AddWriterT.queryBoundedAboveBy_mono
        (AddWriterT.queryBoundedAboveBy_bind (n₁ := 0) (n₂ := rest.length)
          (AddWriterT.queryBoundedAboveBy_monadLift (m := m)
            (runtime.impl ⟨pk, msg, comList, i, ω, resp⟩))
          (fun h => ?_))
        (by omega)
      by_cases hh : h.val = 0
      · simpa [hashStep, hh] using
          AddWriterT.queryBoundedAboveBy_mono
            (AddWriterT.queryBoundedAboveBy_pure ((some (ω, resp)) : Option (Ω × P)))
            (Nat.zero_le rest.length)
      · let newBest : Option (Ω × P × Fin (2 ^ b)) := match best with
          | none => some (ω, resp, h)
          | some (ω', resp', h') =>
              if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h')
        simpa [hashStep, hh, newBest] using ih (best := newBest)

section

omit [DecidableEq X] [DecidableEq PC] [DecidableEq Ω] [DecidableEq P]
  [SampleableType Ω]

/-- Fischlin verification makes at most `ρ` random-oracle queries under unit-cost
instrumentation. -/
theorem verify_usesAtMostRhoQueries
    (runtime : QueryRuntime (fischlinROSpec X PC Ω P ρ b M) m)
    (pk : X) (msg : M) (π : FischlinProof PC Ω P ρ) :
    Queries[ (Fischlin σ hr ρ b S M).verify pk msg π in runtime ] ≤ ρ := by
  let step : Fin ρ → AddWriterT ℕ m (Bool × ℕ) := fun i => do
    let (_, ω_i, resp_i) := π i
    AddWriterT.addTell (M := m) 1
    let h_i ← monadLift (runtime.impl ⟨pk, msg, List.ofFn fun j => (π j).1, i, ω_i, resp_i⟩)
    pure (σ.verify pk (π i).1 ω_i resp_i, h_i.val)
  have hstep : ∀ i, AddWriterT.QueryBoundedAboveBy (step i) 1 := by
    intro i
    change AddWriterT.QueryBoundedAboveBy
      (do
        AddWriterT.addTell (M := m) 1
        let h_i ← monadLift (runtime.impl
          ⟨pk, msg, List.ofFn fun j => (π j).1, i, (π i).2.1, (π i).2.2⟩)
        pure (σ.verify pk (π i).1 (π i).2.1 (π i).2.2, h_i.val))
      1
    apply AddWriterT.queryBoundedAboveBy_bind (n₁ := 1) (n₂ := 0)
    · exact AddWriterT.queryBoundedAboveBy_addTell 1
    · intro _
      apply AddWriterT.queryBoundedAboveBy_bind (n₁ := 0) (n₂ := 0)
      · exact AddWriterT.queryBoundedAboveBy_monadLift
          (runtime.impl ⟨pk, msg, List.ofFn fun j => (π j).1, i, (π i).2.1, (π i).2.2⟩)
      · intro _
        exact AddWriterT.queryBoundedAboveBy_pure _
  change AddWriterT.QueryBoundedAboveBy
      (HasQuery.withUnitCost
        (fun [HasQuery (fischlinROSpec X PC Ω P ρ b M) (AddWriterT ℕ m)] =>
          (Fischlin (m := AddWriterT ℕ m) σ hr ρ b S M).verify pk msg π)
        runtime)
      ρ
  simpa [Fischlin, HasQuery.withUnitCost, QueryRuntime.withUnitCost_impl, AddWriterT.addTell, step]
    using
      (AddWriterT.queryBoundedAboveBy_bind
        (oa := Fin.mOfFn ρ step)
        (f := fun results => pure
          (((List.finRange ρ).all fun i => (results i).1) &&
            decide ((List.finRange ρ).foldl (fun acc i => acc + (results i).2) 0 ≤ S)))
        (n₁ := ρ) (n₂ := 0)
        (by
          simpa using
            (AddWriterT.queryBoundedAboveBy_fin_mOfFn (n := ρ) (k := 1) hstep))
        (fun _ => AddWriterT.queryBoundedAboveBy_pure _))

/-- Fischlin verification makes at least `ρ` random-oracle queries under unit-cost
instrumentation. -/
theorem verify_usesAtLeastRhoQueries
    (runtime : QueryRuntime (fischlinROSpec X PC Ω P ρ b M) m)
    (pk : X) (msg : M) (π : FischlinProof PC Ω P ρ) :
    Queries[ (Fischlin σ hr ρ b S M).verify pk msg π in runtime ] ≥ ρ := by
  let step : Fin ρ → AddWriterT ℕ m (Bool × ℕ) := fun i => do
    let (_, ω_i, resp_i) := π i
    AddWriterT.addTell (M := m) 1
    let h_i ← monadLift (runtime.impl ⟨pk, msg, List.ofFn fun j => (π j).1, i, ω_i, resp_i⟩)
    pure (σ.verify pk (π i).1 ω_i resp_i, h_i.val)
  have hstep : ∀ i, AddWriterT.QueryBoundedBelowBy (step i) 1 := by
    intro i
    change AddWriterT.QueryBoundedBelowBy
      (do
        AddWriterT.addTell (M := m) 1
        let h_i ← monadLift (runtime.impl
          ⟨pk, msg, List.ofFn fun j => (π j).1, i, (π i).2.1, (π i).2.2⟩)
        pure (σ.verify pk (π i).1 (π i).2.1 (π i).2.2, h_i.val))
      1
    apply AddWriterT.queryBoundedBelowBy_bind (n₁ := 1) (n₂ := 0)
    · exact AddWriterT.queryBoundedBelowBy_addTell 1
    · intro _
      apply AddWriterT.queryBoundedBelowBy_bind (n₁ := 0) (n₂ := 0)
      · exact AddWriterT.queryBoundedBelowBy_monadLift
          (runtime.impl ⟨pk, msg, List.ofFn fun j => (π j).1, i, (π i).2.1, (π i).2.2⟩)
      · intro _
        exact AddWriterT.queryBoundedBelowBy_pure _
  change AddWriterT.QueryBoundedBelowBy
      (HasQuery.withUnitCost
        (fun [HasQuery (fischlinROSpec X PC Ω P ρ b M) (AddWriterT ℕ m)] =>
          (Fischlin (m := AddWriterT ℕ m) σ hr ρ b S M).verify pk msg π)
        runtime)
      ρ
  simpa [Fischlin, HasQuery.withUnitCost, QueryRuntime.withUnitCost_impl, AddWriterT.addTell, step]
    using
      (AddWriterT.queryBoundedBelowBy_bind
        (oa := Fin.mOfFn ρ step)
        (f := fun results => pure
          (((List.finRange ρ).all fun i => (results i).1) &&
            decide ((List.finRange ρ).foldl (fun acc i => acc + (results i).2) 0 ≤ S)))
        (n₁ := ρ) (n₂ := 0)
        (by
          simpa using
            (AddWriterT.queryBoundedBelowBy_fin_mOfFn (n := ρ) (k := 1) hstep))
        (fun _ => AddWriterT.queryBoundedBelowBy_pure _))

/-- Fischlin signing makes at most `ρ * |Ω|` random-oracle queries under unit-cost
instrumentation. -/
theorem sign_usesAtMostRhoCardOmegaQueries
    (runtime : QueryRuntime (fischlinROSpec X PC Ω P ρ b M) m)
    (pk : X) (sk : W) (msg : M) :
    Queries[ (Fischlin σ hr ρ b S M).sign pk sk msg in runtime ] ≤ ρ * FinEnum.card Ω := by
  let repStep : (Fin ρ → PC × SC) → Fin ρ → AddWriterT ℕ m (PC × Ω × P) := fun commits i => do
    let comVec : Fin ρ → PC := fun j => (commits j).1
    let comList := List.ofFn comVec
    let sc_i := (commits i).2
    let result ←
      fischlinSearchAuxWithUnitCost
        (σ := σ) (runtime := runtime) (pk := pk) (sk := sk) (sc := sc_i) (msg := msg)
        (comList := comList) (i := i)
        (FinEnum.toList Ω) (none : Option (Ω × P × Fin (2 ^ b)))
    match result with
    | some (ω, resp) => pure (comVec i, ω, resp)
    | none => pure (comVec i, default, default)
  have hlen : (FinEnum.toList Ω).length = FinEnum.card Ω := by
    simp [FinEnum.toList]
  have hrep : ∀ commits i,
      AddWriterT.QueryBoundedAboveBy (repStep commits i) (FinEnum.card Ω) := by
    intro commits i
    have hsearch :
        AddWriterT.QueryBoundedAboveBy
          (fischlinSearchAuxWithUnitCost
            (σ := σ) (runtime := runtime) (pk := pk) (sk := sk) (sc := (commits i).2)
            (msg := msg) (comList := List.ofFn fun j => (commits j).1) (i := i)
            (FinEnum.toList Ω) (none : Option (Ω × P × Fin (2 ^ b))))
          (FinEnum.toList Ω).length := by
      simpa using
        (fischlinSearchAuxWithUnitCost_queryBoundedAboveBy
          (σ := σ) (runtime := runtime) (pk := pk) (sk := sk) (sc := (commits i).2)
          (msg := msg) (comList := List.ofFn fun j => (commits j).1) (i := i)
          (challenges := FinEnum.toList Ω) (best := none))
    let finish : Option (Ω × P) → AddWriterT ℕ m (PC × Ω × P)
      | some (ω, resp) => pure (((fun j => (commits j).1) i), ω, resp)
      | none => pure (((fun j => (commits j).1) i), default, default)
    have hcont :
        ∀ result : Option (Ω × P), AddWriterT.QueryBoundedAboveBy (finish result) 0 := by
      intro result
      cases result with
      | none =>
          simpa [finish] using AddWriterT.queryBoundedAboveBy_pure
            (m := m) ((((fun j => (commits j).1) i), default, default) : PC × Ω × P)
      | some pair =>
          rcases pair with ⟨ω, resp⟩
          simpa [finish] using AddWriterT.queryBoundedAboveBy_pure
            (m := m) ((((fun j => (commits j).1) i), ω, resp) : PC × Ω × P)
    exact AddWriterT.queryBoundedAboveBy_mono
      (AddWriterT.queryBoundedAboveBy_bind (n₁ := (FinEnum.toList Ω).length) (n₂ := 0)
        hsearch hcont)
      (by simp [hlen])
  let commitComp : AddWriterT ℕ m (Fin ρ → PC × SC) :=
    Fin.mOfFn ρ fun _ => (liftM (σ.commit pk sk) : AddWriterT ℕ m (PC × SC))
  have hcommit :
      AddWriterT.QueryBoundedAboveBy commitComp 0 := by
    have hstep :
        AddWriterT.QueryBoundedAboveBy
          (liftM (σ.commit pk sk) : AddWriterT ℕ m (PC × SC)) 0 := by
      simpa [WriterT.liftM_def] using
        (AddWriterT.queryBoundedAboveBy_monadLift
          (monadLift (σ.commit pk sk) : m (PC × SC)))
    simpa [commitComp] using
      (AddWriterT.queryBoundedAboveBy_fin_mOfFn (n := ρ) (k := 0)
        (f := fun _ => (liftM (σ.commit pk sk) : AddWriterT ℕ m (PC × SC)))
        (fun _ => hstep))
  suffices
      AddWriterT.QueryBoundedAboveBy
        (commitComp >>= fun commits => Fin.mOfFn ρ (repStep commits))
        (ρ * FinEnum.card Ω) by
    have hsign :
        HasQuery.withUnitCost
          (fun [HasQuery (fischlinROSpec X PC Ω P ρ b M) (AddWriterT ℕ m)] =>
            (Fischlin (m := AddWriterT ℕ m) σ hr ρ b S M).sign pk sk msg)
          runtime =
          (commitComp >>= fun commits => Fin.mOfFn ρ (repStep commits)) := by
      simp only [Fischlin, HasQuery.withUnitCost, repStep, commitComp]
      refine congrArg
        (fun k => commitComp >>= k) ?_
      funext commits
      refine congrArg
        (fun f : Fin ρ → AddWriterT ℕ m (PC × Ω × P) => Fin.mOfFn ρ f) ?_
      funext i
      let finish : AddWriterT ℕ m (Option (Ω × P)) → AddWriterT ℕ m (PC × Ω × P) := fun oa => do
        let result ← oa
        match result with
        | some (ω, resp) => pure (((fun j => (commits j).1) i), ω, resp)
        | none => pure (((fun j => (commits j).1) i), default, default)
      simpa [finish] using congrArg finish
        (fischlinSearchAux_eq_withUnitCost
          (σ := σ) (runtime := runtime) (pk := pk) (sk := sk) (sc := (commits i).2)
          (msg := msg) (comList := List.ofFn fun j => (commits j).1) (i := i)
          (challenges := FinEnum.toList Ω) (best := none))
    simpa [HasQuery.UsesAtMostQueries, hsign] using this
  simpa [Nat.zero_add] using
    (AddWriterT.queryBoundedAboveBy_bind (n₁ := 0) (n₂ := ρ * FinEnum.card Ω) hcommit
      (fun commits =>
        AddWriterT.queryBoundedAboveBy_fin_mOfFn (n := ρ) (k := FinEnum.card Ω)
          (fun i => hrep commits i)))

end

end costAccounting

/-! ### Completeness -/

/-- Completeness error bound for the Fischlin transform (Fischlin 2005, Lemma 1).

Given `ρ` repetitions, `b`-bit hashes, max sum `S`, and challenge space size `t`:
the error is `ρ · ((2^b - ⌊S/ρ⌋ - 1) / 2^b)^t`.

Derivation: by a union/pigeonhole bound over repetitions, if the sum of minimum
hash values exceeds `S`, at least one minimum exceeds `⌊S/ρ⌋`. The probability
that the minimum of `t` independent uniform samples from `Fin (2^b)` exceeds `k`
is `((2^b - k - 1) / 2^b)^t`.

For `S = 0` this simplifies to `ρ · ((2^b - 1) / 2^b)^t`.
The intended regime is `0 < ρ`; theorem statements below make that explicit. -/
noncomputable def completenessError (ρ b S t : ℕ) : ℝ≥0∞ :=
  (ρ : ℝ≥0∞) * ((↑(2 ^ b - (S / ρ + 1)) : ℝ≥0∞) / ↑(2 ^ b)) ^ t

/-- Almost completeness of the Fischlin transform: if the underlying Σ-protocol is
perfectly complete, then the signature scheme verifies with probability at least
`1 - completenessError ρ b S t` where `t = FinEnum.card Ω` is the challenge space size.

Unlike the Fiat-Shamir transform (which is perfectly complete), the Fischlin transform
has a non-zero completeness error because the prover's proof-of-work search may fail
to find hash values whose sum is at most `S`. -/
theorem almostComplete (hρ : 0 < ρ) (hc : σ.PerfectlyComplete) (msg : M) :
    Pr[= true | (runtime ρ b M).evalDist do
      let (pk, sk) ←
        (Fischlin (m := OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M))
          σ hr ρ b S M).keygen
      let sig ←
        (Fischlin (m := OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M))
          σ hr ρ b S M).sign pk sk msg
      (Fischlin (m := OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M))
        σ hr ρ b S M).verify pk msg sig]
    ≥ 1 - completenessError ρ b S (FinEnum.card Ω) := by sorry

/-! ### Online Extraction / Knowledge Soundness -/

/-- Structural query bound: the computation makes at most `Q` total hash oracle queries
(`Sum.inr` queries), with no restriction on `unifSpec` queries (`Sum.inl`). -/
def ROQueryBound {α : Type} (oa : OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M) α)
    (Q : ℕ) : Prop :=
  OracleComp.IsQueryBound oa Q
    (fun t b => match t with | .inl _ => True | .inr _ => 0 < b)
    (fun t b => match t with | .inl _ => b | .inr _ => b - 1)

/-- A cheating prover (knowledge soundness adversary) for the Fischlin transform.
The adversary receives a statement and message, has access to both the random oracle
and internal randomness (`unifSpec`), and attempts to produce a valid Fischlin proof
without knowing the witness.

The Σ-protocol `σ` is not referenced in the structure itself (only in the
extraction and verification steps of the experiment), so it enters the
theorem statements via hypotheses like `σ.SpeciallySound`. -/
structure KnowledgeSoundnessAdv where
  run : X → M → OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M)
    (FischlinProof PC Ω P ρ)

/-- Online extractor for the Fischlin transform (Fischlin 2005, Construction 2).

Given statement `x`, a proof `π`, and the log of all hash oracle queries made by
the prover, the extractor searches for two accepting transcripts at the same
commitment with different challenges, then invokes the Σ-protocol's `extract`
function. Returns `none` if no such collision is found in the log.

The key property enabling this extractor is `UniqueResponses`: given the same
`(statement, commitment, challenge)`, there is at most one valid response.
So finding a second valid query at a different challenge gives a proper
input pair for the Σ-protocol extractor. -/
noncomputable def onlineExtract
    (x : X) (π : FischlinProof PC Ω P ρ)
    (log : QueryLog (fischlinROSpec X PC Ω P ρ b M)) : ProbComp (Option W) :=
  let comList := List.ofFn fun i => (π i).1
  let findWitness : Fin ρ → Option (Ω × P × Ω × P) := fun i =>
    let (com_i, ω_i, _resp_i) := π i
    log.findSome? fun ⟨entry, _⟩ =>
      if entry.stmt == x && entry.comList == comList && entry.rep == i
          && σ.verify x com_i entry.chal entry.resp
          && decide (entry.chal ≠ ω_i) then
        some (ω_i, (π i).2.2, entry.chal, entry.resp)
      else none
  match (List.finRange ρ).findSome? findWitness with
  | some (ω₁, p₁, ω₂, p₂) => some <$> σ.extract ω₁ p₁ ω₂ p₂
  | none => return none

/-- Soundness error bound for the Fischlin transform (Fischlin 2005, Theorem 2).

For `Q` total hash oracle queries, `ρ` repetitions, `b`-bit hashes, and max sum `S`:
the error is `(Q + 1) · (S + 1) · C(S + ρ - 1, ρ - 1) / 2^(bρ)`.

For `S = 0` this simplifies to `(Q + 1) / 2^(bρ)`.
The intended regime is `0 < ρ`; theorem statements below make that explicit. -/
noncomputable def knowledgeSoundnessError (Q ρ b S : ℕ) : ℝ≥0∞ :=
  (↑(Q + 1) : ℝ≥0∞) * ↑((S + 1) * Nat.choose (S + ρ - 1) (ρ - 1)) /
    ((↑(2 ^ b) : ℝ≥0∞) ^ ρ)

/-- The knowledge soundness experiment for the Fischlin transform.

Runs a cheating prover with a logged random oracle, then checks:
1. Whether the Fischlin verifier accepts the produced proof.
2. Whether the online extractor returns a witness satisfying the relation.

Returns `true` (the "bad event") when verification succeeds but the extracted
output is either `none` or an invalid witness.

The `prover` argument is the raw function rather than `KnowledgeSoundnessAdv`
to keep type inference tractable with `sorry` bodies. -/
noncomputable def knowledgeSoundnessExp
    (prover : X → M →
      OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M) (FischlinProof PC Ω P ρ))
    (x : X) (msg : M) : ProbComp Bool :=
  let roSpec := fischlinROSpec X PC Ω P ρ b M
  let ro : QueryImpl roSpec (StateT roSpec.QueryCache ProbComp) := randomOracle
  let loggedRO := ro.withLogging
  let idImpl := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (WriterT (QueryLog roSpec) (StateT roSpec.QueryCache ProbComp))
  do
    let ((π, roLog), cache) ← (simulateQ (idImpl + loggedRO) (prover x msg)).run |>.run ∅
    let idImpl' := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT roSpec.QueryCache ProbComp)
    let (verified, _) ←
      (simulateQ (idImpl' + ro)
        ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec X PC Ω P ρ b M))
          σ hr ρ b S M).verify x msg π)).run cache
    let extracted ← onlineExtract σ ρ b M x π roLog
    return (verified && !(match extracted with | some w => p x w | none => false))

/-- Knowledge soundness of the Fischlin transform via online (straight-line) extraction
(Fischlin 2005, Theorem 2).

If the Σ-protocol is specially sound with unique responses, then for any cheating prover
making at most `Q` hash queries, the probability that the verifier accepts but the
online extractor fails to recover a valid witness is at most
`(Q + 1) · (S + 1) · C(S + ρ - 1, ρ - 1) / 2^(bρ)`.

Unlike the Fiat-Shamir transform, this extraction is **straight-line** (no rewinding),
which enables a tight security reduction. -/
theorem knowledgeSoundness
    (hss : σ.SpeciallySound) (hur : σ.UniqueResponses)
    (adv : KnowledgeSoundnessAdv ρ b M)
    (Q : ℕ) (hρ : 0 < ρ)
    (hQ : ∀ x msg, ROQueryBound ρ b M (adv.run x msg) Q)
    (x : X) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M adv.run x msg]
      ≤ knowledgeSoundnessError Q ρ b S := by sorry

/-! ### EUF-CMA Security

A tight EUF-CMA corollary for the Fischlin signature scheme requires an explicit
simulation of signing queries inside a hard-relation experiment. The previous
placeholder theorem overclaimed by bounding forgery probability solely by the
knowledge-soundness error, so we intentionally leave that corollary unstated
until the signing-simulation reduction is formalized. -/

end Fischlin
