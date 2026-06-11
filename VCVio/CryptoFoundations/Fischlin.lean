/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryCost
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
import Mathlib.Data.FinEnum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Fin

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
structure FischlinROInput (Stmt Commit Chal Resp : Type) (ρ : ℕ) (M : Type) where
  stmt : Stmt
  msg : M
  comList : List Commit
  rep : Fin ρ
  chal : Chal
  resp : Resp
  deriving DecidableEq

/-- The random oracle specification for the Fischlin transform.
Domain: `FischlinROInput` (statement, message, commitment list, index, challenge, response).
Range: `Fin (2^b)` (b-bit hash values). -/
abbrev fischlinROSpec (Stmt Commit Chal Resp : Type) (ρ b : ℕ) (M : Type) :=
  FischlinROInput Stmt Commit Chal Resp ρ M →ₒ Fin (2 ^ b)

/-- A Fischlin proof consists of one `(commitment, challenge, response)` triple
per parallel repetition. -/
abbrev FischlinProof (Commit Chal Resp : Type) (ρ : ℕ) := Fin ρ → Commit × Chal × Resp

/-! ## Prover Search -/

/-- Recursive search over a list of challenges for one Fischlin repetition.

For each challenge `ω`, computes the sigma protocol response and queries the hash oracle.
Exits early if a hash value of `0` is found (the ideal "proof of work" result).
Otherwise, tracks the `(challenge, response)` pair with the minimal hash value.

This models the sequential search in Construction 1 of the Fischlin paper:
the prover queries `H` on each input and keeps the best. -/
private def fischlinSearchAux {Stmt Wit Commit PrvState Chal Resp M : Type}
    {rel : Stmt → Wit → Bool} {ρ b : ℕ}
    {m : Type → Type v} [Monad m]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    [MonadLiftT ProbComp m] [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M) m]
    (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M) (comList : List Commit) (i : Fin ρ) :
    List Chal → Option (Chal × Resp × Fin (2 ^ b)) → m (Option (Chal × Resp))
  | [], best => return best.map fun (ω, resp, _) => (ω, resp)
  | ω :: rest, best => do
    let resp ← σ.respond pk sk sc ω
    let h ← HasQuery.query (spec := (fischlinROSpec Stmt Commit Chal Resp ρ b M))
      ⟨pk, msg, comList, i, ω, resp⟩
    if h.val = 0 then return some (ω, resp)
    else
      let newBest := match best with
        | none => some (ω, resp, h)
        | some (ω', resp', h') =>
          if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h')
      fischlinSearchAux σ pk sk sc msg comList i rest newBest

/-! ## Main Definition -/

variable {Stmt Wit Commit PrvState Chal Resp : Type}
    {rel : Stmt → Wit → Bool}

section mainDefinition

variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]

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
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) (ρ b S : ℕ) (M : Type)
    [DecidableEq M] [MonadLiftT ProbComp m]
    [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M) m] :
    SignatureAlg m
      (M := M) (PK := Stmt) (SK := Wit) (S := FischlinProof Commit Chal Resp ρ) where
  keygen := liftM hr.gen
  sign := fun pk sk msg => do
    let commits : Fin ρ → Commit × PrvState ←
      Fin.mOfFn ρ fun _ => σ.commit pk sk
    let comVec : Fin ρ → Commit := fun i => (commits i).1
    let comList := List.ofFn comVec
    Fin.mOfFn ρ fun i => do
      let sc_i := (commits i).2
      let result ←
        fischlinSearchAux
          σ pk sk sc_i msg comList i (FinEnum.toList Chal)
          (none : Option (Chal × Resp × Fin (2 ^ b)))
      match result with
      | some (ω, resp) => return (comVec i, ω, resp)
      | none => return (comVec i, default, default)
  verify := fun pk msg π => do
    let comVec : Fin ρ → Commit := fun i => (π i).1
    let comList := List.ofFn comVec
    let results ← Fin.mOfFn ρ fun i => do
      let (_, ω_i, resp_i) := π i
      let h_i ← HasQuery.query (spec := (fischlinROSpec Stmt Commit Chal Resp ρ b M))
        ⟨pk, msg, comList, i, ω_i, resp_i⟩
      pure (σ.verify pk (comVec i) ω_i resp_i, h_i.val)
    let allVerified := (List.finRange ρ).all fun i => (results i).1
    let hashSum := (List.finRange ρ).foldl (fun acc i => acc + (results i).2) 0
    pure (allVerified && decide (hashSum ≤ S))

end mainDefinition

namespace Fischlin

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

open ENNReal

section runtime

variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [SampleableType Chal]

/-- Runtime bundle for the Fischlin random-oracle world. -/
noncomputable def runtime
    (ρ b : ℕ) (M : Type) [DecidableEq M] :
    ProbCompRuntime (OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (StateT (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

end runtime

section costAccounting

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) (ρ b : ℕ) (M : Type)

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

/-- Fischlin's inner search, instantiated in a concrete unit-cost runtime. -/
private def fischlinSearchAuxWithUnitCost
    {Stmt Wit Commit PrvState Chal Resp M : Type} {rel : Stmt → Wit → Bool} {ρ b : ℕ}
    {m : Type → Type v} [Monad m] [MonadLiftT ProbComp m]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M) (comList : List Commit) (i : Fin ρ)
    (challenges : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b))) :
    AddWriterT ℕ m (Option (Chal × Resp)) :=
  match challenges with
  | [] => pure (best.map fun (ω, resp, _) => (ω, resp))
  | ω :: rest => do
      let resp ← monadLift (σ.respond pk sk sc ω)
      AddWriterT.addTell (M := m) 1
      let h ← monadLift (runtime ⟨pk, msg, comList, i, ω, resp⟩)
      if h.val = 0 then
        pure (some (ω, resp))
      else
        let newBest := match best with
          | none => some (ω, resp, h)
          | some (ω', resp', h') =>
            if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h')
        fischlinSearchAuxWithUnitCost σ runtime pk sk sc msg comList i rest newBest

private lemma fischlinSearchAux_eq_withUnitCost
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M) (comList : List Commit) (i : Fin ρ)
    (challenges : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b))) :
    let _ : HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M) (AddWriterT ℕ m) :=
      runtime.withUnitCost.toHasQuery
    fischlinSearchAux
      (m := AddWriterT ℕ m) σ pk sk sc msg comList i challenges best =
      fischlinSearchAuxWithUnitCost σ
        (runtime := runtime) (pk := pk) (sk := sk) (sc := sc) (msg := msg)
        (comList := comList) (i := i) challenges best := by
  induction challenges generalizing best with
  | nil =>
      simp [fischlinSearchAux, fischlinSearchAuxWithUnitCost]
  | cons ω rest ih =>
      simp [fischlinSearchAux, fischlinSearchAuxWithUnitCost,
        QueryImpl.withUnitCost_apply, liftM, MonadLiftT.monadLift, ih]

private lemma fischlinSearchAuxWithUnitCost_queryBoundedAboveBy
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M) (comList : List Commit) (i : Fin ρ)
    (challenges : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b))) :
    AddWriterT.QueryBoundedAboveBy
      (fischlinSearchAuxWithUnitCost σ
        (runtime := runtime) (pk := pk) (sk := sk) (sc := sc) (msg := msg)
        (comList := comList) (i := i) challenges best)
      challenges.length := by
  induction challenges generalizing best with
  | nil =>
      exact AddWriterT.queryBoundedAboveBy_pure
        (m := m) ((best.map fun (ω, resp, _) => (ω, resp)) : Option (Chal × Resp))
  | cons ω rest ih =>
      let hashStep : Resp → AddWriterT ℕ m (Option (Chal × Resp)) := fun resp =>
        (AddWriterT.addTell (M := m) 1 : AddWriterT ℕ m PUnit) >>= fun _ =>
          (monadLift (runtime ⟨pk, msg, comList, i, ω, resp⟩) :
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
        ((monadLift (σ.respond pk sk sc ω) : AddWriterT ℕ m Resp) >>= hashStep)
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
            (runtime ⟨pk, msg, comList, i, ω, resp⟩))
          (fun h => ?_))
        (by omega)
      by_cases hh : h.val = 0
      · simpa [hashStep, hh] using
          AddWriterT.queryBoundedAboveBy_mono
            (AddWriterT.queryBoundedAboveBy_pure ((some (ω, resp)) : Option (Chal × Resp)))
            (Nat.zero_le rest.length)
      · let newBest : Option (Chal × Resp × Fin (2 ^ b)) := match best with
          | none => some (ω, resp, h)
          | some (ω', resp', h') =>
              if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h')
        simpa [hashStep, hh, newBest] using ih (best := newBest)

/-- Fischlin's inner search, instantiated in a weighted additive-cost runtime. -/
private def fischlinSearchAuxWithAddCost
    {κ : Type} [AddMonoid κ]
    {Stmt Wit Commit PrvState Chal Resp M : Type} {rel : Stmt → Wit → Bool} {ρ b : ℕ}
    {m : Type → Type v} [Monad m] [MonadLiftT ProbComp m]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M) (comList : List Commit) (i : Fin ρ)
    (challenges : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b)))
    (costFn : (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain → κ) :
    AddWriterT κ m (Option (Chal × Resp)) :=
  match challenges with
  | [] => pure (best.map fun (ω, resp, _) => (ω, resp))
  | ω :: rest => do
      let resp ← monadLift (σ.respond pk sk sc ω)
      AddWriterT.addTell (M := m) (costFn ⟨pk, msg, comList, i, ω, resp⟩)
      let h ← monadLift (runtime ⟨pk, msg, comList, i, ω, resp⟩)
      if h.val = 0 then
        pure (some (ω, resp))
      else
        let newBest := match best with
          | none => some (ω, resp, h)
          | some (ω', resp', h') =>
            if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h')
        fischlinSearchAuxWithAddCost σ runtime pk sk sc msg comList i rest newBest costFn

private lemma fischlinSearchAux_eq_withAddCost
    {κ : Type} [AddMonoid κ]
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M) (comList : List Commit) (i : Fin ρ)
    (challenges : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b)))
    (costFn : (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain → κ) :
    let _ : HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M) (AddWriterT κ m) :=
      runtime.withAddCost costFn |>.toHasQuery
    fischlinSearchAux
      (m := AddWriterT κ m) σ pk sk sc msg comList i challenges best =
      fischlinSearchAuxWithAddCost σ
        (runtime := runtime) (pk := pk) (sk := sk) (sc := sc) (msg := msg)
        (comList := comList) (i := i) challenges best costFn := by
  induction challenges generalizing best with
  | nil =>
      simp [fischlinSearchAux, fischlinSearchAuxWithAddCost]
  | cons ω rest ih =>
      simp [fischlinSearchAux, fischlinSearchAuxWithAddCost,
        QueryImpl.withAddCost_apply, liftM, MonadLiftT.monadLift, ih]

private lemma fischlinSearchAuxWithAddCost_pathwiseCostAtMost
    {κ : Type} [AddCommMonoid κ] [PartialOrder κ] [IsOrderedAddMonoid κ]
    [CanonicallyOrderedAdd κ]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M) (comList : List Commit) (i : Fin ρ)
    (challenges : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b)))
    (costFn : (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain → κ) {w : κ}
    (hcost : ∀ t, costFn t ≤ w) :
    AddWriterT.PathwiseCostAtMost
      (fischlinSearchAuxWithAddCost σ
        (runtime := runtime) (pk := pk) (sk := sk) (sc := sc) (msg := msg)
        (comList := comList) (i := i) challenges best costFn)
      (challenges.length • w) := by
  induction challenges generalizing best with
  | nil =>
      simpa using
        (AddWriterT.pathwiseCostAtMost_pure
          (m := m) ((best.map fun (ω, resp, _) => (ω, resp)) : Option (Chal × Resp)))
  | cons chal rest ih =>
      let hashStep : Resp → AddWriterT κ m (Option (Chal × Resp)) := fun resp =>
        (AddWriterT.addTell (M := m) (costFn ⟨pk, msg, comList, i, chal, resp⟩) :
          AddWriterT κ m PUnit) >>= fun _ =>
          (monadLift (runtime ⟨pk, msg, comList, i, chal, resp⟩) :
            AddWriterT κ m (Fin (2 ^ b))) >>= fun h =>
              if h.val = 0 then
                pure (some (chal, resp))
              else
                fischlinSearchAuxWithAddCost σ runtime pk sk sc msg comList i rest
                  (match best with
                  | none => some (chal, resp, h)
                  | some (ω', resp', h') =>
                      if h.val < h'.val then some (chal, resp, h) else some (ω', resp', h'))
                  costFn
      change AddWriterT.PathwiseCostAtMost
        ((monadLift (σ.respond pk sk sc chal) : AddWriterT κ m Resp) >>= hashStep)
        ((rest.length + 1) • w)
      have hstep : ∀ resp, AddWriterT.PathwiseCostAtMost (hashStep resp) (w + rest.length • w) := by
        intro resp
        have htell :
            AddWriterT.PathwiseCostAtMost
              (AddWriterT.addTell (M := m) (costFn ⟨pk, msg, comList, i, chal, resp⟩))
              w :=
          AddWriterT.pathwiseCostAtMost_mono
            (AddWriterT.pathwiseCostAtMost_addTell
              (m := m) (costFn ⟨pk, msg, comList, i, chal, resp⟩))
            (hcost _)
        refine AddWriterT.pathwiseCostAtMost_bind (w₁ := w) (w₂ := rest.length • w) htell ?_
        intro _
        have hhash :
            AddWriterT.PathwiseCostAtMost
              (((monadLift (runtime ⟨pk, msg, comList, i, chal, resp⟩) :
                    AddWriterT κ m (Fin (2 ^ b))) >>= fun h =>
                  if h.val = 0 then
                    pure (some (chal, resp))
                  else
                    fischlinSearchAuxWithAddCost σ runtime pk sk sc msg comList i rest
                      (match best with
                      | none => some (chal, resp, h)
                      | some (ω', resp', h') =>
                          if h.val < h'.val then some (chal, resp, h) else some (ω', resp', h'))
                      costFn))
              (0 + rest.length • w) := by
          refine AddWriterT.pathwiseCostAtMost_bind (w₁ := 0) (w₂ := rest.length • w)
            (AddWriterT.pathwiseCostAtMost_monadLift
              (m := m) (runtime ⟨pk, msg, comList, i, chal, resp⟩)) ?_
          intro h
          by_cases hh : h.val = 0
          · simpa [hh] using
              AddWriterT.pathwiseCostAtMost_mono
                (AddWriterT.pathwiseCostAtMost_pure ((some (chal, resp)) : Option (Chal × Resp)))
                (zero_le)
          · let newBest : Option (Chal × Resp × Fin (2 ^ b)) := match best with
              | none => some (chal, resp, h)
              | some (ω', resp', h') =>
                  if h.val < h'.val then some (chal, resp, h) else some (ω', resp', h')
            simpa [hh, newBest] using ih (best := newBest)
        exact AddWriterT.pathwiseCostAtMost_mono hhash (by simp [zero_add])
      simpa [succ_nsmul'] using
        (AddWriterT.pathwiseCostAtMost_bind (w₁ := 0) (w₂ := w + rest.length • w)
          (AddWriterT.pathwiseCostAtMost_monadLift (m := m) (σ.respond pk sk sc chal))
          hstep)

section verifyCostAccounting

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
variable [FinEnum Chal] [Inhabited Chal] [Inhabited Resp]
  (hr : GenerableRelation Stmt Wit rel) (S : ℕ)
  [DecidableEq M] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

/-- Fischlin verification makes at most `ρ` random-oracle queries under unit-cost
instrumentation. -/
theorem verify_usesAtMostRhoQueries
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (msg : M) (π : FischlinProof Commit Chal Resp ρ) :
    Queries[ (Fischlin σ hr ρ b S M).verify pk msg π in runtime ] ≤ ρ := by
  classical
  let _ : SampleableType Chal := inferInstance
  let step : Fin ρ → AddWriterT ℕ m (Bool × ℕ) := fun i => do
    let (_, ω_i, resp_i) := π i
    AddWriterT.addTell (M := m) 1
    let h_i ← monadLift (runtime ⟨pk, msg, List.ofFn fun j => (π j).1, i, ω_i, resp_i⟩)
    pure (σ.verify pk (π i).1 ω_i resp_i, h_i.val)
  have hstep : ∀ i, AddWriterT.QueryBoundedAboveBy (step i) 1 := by
    intro i
    change AddWriterT.QueryBoundedAboveBy
      (do
        AddWriterT.addTell (M := m) 1
        let h_i ← monadLift (runtime
          ⟨pk, msg, List.ofFn fun j => (π j).1, i, (π i).2.1, (π i).2.2⟩)
        pure (σ.verify pk (π i).1 (π i).2.1 (π i).2.2, h_i.val))
      1
    apply AddWriterT.queryBoundedAboveBy_bind (n₁ := 1) (n₂ := 0)
    · exact AddWriterT.queryBoundedAboveBy_addTell 1
    · intro _
      apply AddWriterT.queryBoundedAboveBy_bind (n₁ := 0) (n₂ := 0)
      · exact AddWriterT.queryBoundedAboveBy_monadLift
          (runtime ⟨pk, msg, List.ofFn fun j => (π j).1, i, (π i).2.1, (π i).2.2⟩)
      · intro _
        exact AddWriterT.queryBoundedAboveBy_pure _
  change AddWriterT.QueryBoundedAboveBy
      (HasQuery.Program.withUnitCost
        (fun [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M) (AddWriterT ℕ m)] =>
          (Fischlin (m := AddWriterT ℕ m) σ hr ρ b S M).verify pk msg π)
        runtime)
      ρ
  simpa [Fischlin, HasQuery.Program.withUnitCost, QueryImpl.withUnitCost_apply,
    AddWriterT.addTell, step]
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
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (msg : M) (π : FischlinProof Commit Chal Resp ρ) :
    Queries[ (Fischlin σ hr ρ b S M).verify pk msg π in runtime ] ≥ ρ := by
  classical
  let _ : SampleableType Chal := inferInstance
  let step : Fin ρ → AddWriterT ℕ m (Bool × ℕ) := fun i => do
    let (_, ω_i, resp_i) := π i
    AddWriterT.addTell (M := m) 1
    let h_i ← monadLift (runtime ⟨pk, msg, List.ofFn fun j => (π j).1, i, ω_i, resp_i⟩)
    pure (σ.verify pk (π i).1 ω_i resp_i, h_i.val)
  have hstep : ∀ i, AddWriterT.QueryBoundedBelowBy (step i) 1 := by
    intro i
    change AddWriterT.QueryBoundedBelowBy
      (do
        AddWriterT.addTell (M := m) 1
        let h_i ← monadLift (runtime
          ⟨pk, msg, List.ofFn fun j => (π j).1, i, (π i).2.1, (π i).2.2⟩)
        pure (σ.verify pk (π i).1 (π i).2.1 (π i).2.2, h_i.val))
      1
    apply AddWriterT.queryBoundedBelowBy_bind (n₁ := 1) (n₂ := 0)
    · exact AddWriterT.queryBoundedBelowBy_addTell 1
    · intro _
      apply AddWriterT.queryBoundedBelowBy_bind (n₁ := 0) (n₂ := 0)
      · exact AddWriterT.queryBoundedBelowBy_monadLift
          (runtime ⟨pk, msg, List.ofFn fun j => (π j).1, i, (π i).2.1, (π i).2.2⟩)
      · intro _
        exact AddWriterT.queryBoundedBelowBy_pure _
  change AddWriterT.QueryBoundedBelowBy
      (HasQuery.Program.withUnitCost
        (fun [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M) (AddWriterT ℕ m)] =>
          (Fischlin (m := AddWriterT ℕ m) σ hr ρ b S M).verify pk msg π)
        runtime)
      ρ
  simpa [Fischlin, HasQuery.Program.withUnitCost, QueryImpl.withUnitCost_apply,
    AddWriterT.addTell, step]
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

end verifyCostAccounting

section signCostAccounting

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
variable [FinEnum Chal] [Inhabited Chal] [Inhabited Resp]
  (hr : GenerableRelation Stmt Wit rel) (S : ℕ)
  [DecidableEq M] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

/-- Fischlin signing makes at most `ρ * |Ω|` random-oracle queries under unit-cost
instrumentation. -/
theorem sign_usesAtMostRhoCardOmegaQueries
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (sk : Wit) (msg : M) :
    Queries[ (Fischlin σ hr ρ b S M).sign pk sk msg in runtime ] ≤ ρ * FinEnum.card Chal := by
  classical
  let _ : SampleableType Chal := inferInstance
  let repStep : (Fin ρ → Commit × PrvState) → Fin ρ → AddWriterT ℕ m (Commit × Chal × Resp) :=
      fun commits i => do
    let comVec : Fin ρ → Commit := fun j => (commits j).1
    let comList := List.ofFn comVec
    let sc_i := (commits i).2
    let result ←
      fischlinSearchAuxWithUnitCost σ
        (runtime := runtime) (pk := pk) (sk := sk) (sc := sc_i) (msg := msg)
        (comList := comList) (i := i)
        (FinEnum.toList Chal) (none : Option (Chal × Resp × Fin (2 ^ b)))
    match result with
    | some (ω, resp) => pure (comVec i, ω, resp)
    | none => pure (comVec i, default, default)
  have hlen : (FinEnum.toList Chal).length = FinEnum.card Chal := by
    simp [FinEnum.toList]
  have hrep : ∀ commits i,
      AddWriterT.QueryBoundedAboveBy (repStep commits i) (FinEnum.card Chal) := by
    intro commits i
    let comVec : Fin ρ → Commit := fun j => (commits j).1
    let comList := List.ofFn comVec
    have hsearch :
        AddWriterT.QueryBoundedAboveBy
          (fischlinSearchAuxWithUnitCost σ
            (runtime := runtime) (pk := pk) (sk := sk) (sc := (commits i).2)
            (msg := msg) (comList := comList) (i := i)
            (FinEnum.toList Chal) (none : Option (Chal × Resp × Fin (2 ^ b))))
          (FinEnum.toList Chal).length := by
      simpa using
        (fischlinSearchAuxWithUnitCost_queryBoundedAboveBy
          σ (runtime := runtime) (pk := pk) (sk := sk) (sc := (commits i).2)
          (msg := msg) (comList := comList) (i := i)
          (challenges := FinEnum.toList Chal) (best := none))
    let finish : Option (Chal × Resp) → AddWriterT ℕ m (Commit × Chal × Resp)
      | some (ω, resp) => pure (comVec i, ω, resp)
      | none => pure (comVec i, default, default)
    have hcont :
        ∀ result : Option (Chal × Resp), AddWriterT.QueryBoundedAboveBy (finish result) 0 := by
      intro result
      cases result with
      | none =>
          simpa [finish] using AddWriterT.queryBoundedAboveBy_pure
            (m := m) ((comVec i, default, default) : Commit × Chal × Resp)
      | some pair =>
          rcases pair with ⟨ω, resp⟩
          simpa [finish] using AddWriterT.queryBoundedAboveBy_pure
            (m := m) ((comVec i, ω, resp) : Commit × Chal × Resp)
    exact AddWriterT.queryBoundedAboveBy_mono
      (AddWriterT.queryBoundedAboveBy_bind (n₁ := (FinEnum.toList Chal).length) (n₂ := 0)
        hsearch hcont)
      (by simp [hlen])
  let commitComp : AddWriterT ℕ m (Fin ρ → Commit × PrvState) :=
    Fin.mOfFn ρ fun _ => (liftM (σ.commit pk sk) : AddWriterT ℕ m (Commit × PrvState))
  have hcommit :
      AddWriterT.QueryBoundedAboveBy commitComp 0 := by
    have hstep :
        AddWriterT.QueryBoundedAboveBy
          (liftM (σ.commit pk sk) : AddWriterT ℕ m (Commit × PrvState)) 0 := by
      simpa [WriterT.liftM_def] using
        (AddWriterT.queryBoundedAboveBy_monadLift
          (monadLift (σ.commit pk sk) : m (Commit × PrvState)))
    simpa [commitComp] using
      (AddWriterT.queryBoundedAboveBy_fin_mOfFn (n := ρ) (k := 0)
        (f := fun _ => (liftM (σ.commit pk sk) : AddWriterT ℕ m (Commit × PrvState)))
        (fun _ => hstep))
  suffices
      AddWriterT.QueryBoundedAboveBy
        (commitComp >>= fun commits => Fin.mOfFn ρ (repStep commits))
        (ρ * FinEnum.card Chal) by
    have hsign :
        HasQuery.Program.withUnitCost
          (fun [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M) (AddWriterT ℕ m)] =>
            (Fischlin (m := AddWriterT ℕ m) σ hr ρ b S M).sign pk sk msg)
          runtime =
          (commitComp >>= fun commits => Fin.mOfFn ρ (repStep commits)) := by
      simp only [Fischlin, HasQuery.Program.withUnitCost, repStep, commitComp]
      refine congrArg
        (fun k => commitComp >>= k) ?_
      funext commits
      refine congrArg
        (fun f : Fin ρ → AddWriterT ℕ m (Commit × Chal × Resp) => Fin.mOfFn ρ f) ?_
      funext i
      let comVec : Fin ρ → Commit := fun j => (commits j).1
      let comList := List.ofFn comVec
      let finish : AddWriterT ℕ m (Option (Chal × Resp)) →
          AddWriterT ℕ m (Commit × Chal × Resp) := fun oa => do
        let result ← oa
        match result with
        | some (ω, resp) => pure (comVec i, ω, resp)
        | none => pure (comVec i, default, default)
      simpa [finish] using congrArg finish
        (fischlinSearchAux_eq_withUnitCost
          σ (runtime := runtime) (pk := pk) (sk := sk) (sc := (commits i).2)
          (msg := msg) (comList := comList) (i := i)
          (challenges := FinEnum.toList Chal) (best := none))
    simpa [HasQuery.UsesAtMostQueries, hsign] using this
  simpa [Nat.zero_add] using
    (AddWriterT.queryBoundedAboveBy_bind (n₁ := 0) (n₂ := ρ * FinEnum.card Chal) hcommit
      (fun commits =>
        AddWriterT.queryBoundedAboveBy_fin_mOfFn (n := ρ) (k := FinEnum.card Chal)
          (fun i => hrep commits i)))

/-- Fischlin signing has weighted query cost at most `ρ • (|Ω| • w)` whenever every random-oracle
query carries cost at most `w`. -/
theorem sign_usesWeightedQueryCostAtMost
    {κ : Type} [AddCommMonoid κ] [PartialOrder κ] [IsOrderedAddMonoid κ]
    [CanonicallyOrderedAdd κ]
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain → κ) (w : κ)
    (hcost : ∀ t, costFn t ≤ w) :
    QueryCost[ (Fischlin σ hr ρ b S M).sign pk sk msg in runtime by costFn ] ≤
      ρ • (FinEnum.card Chal • w) := by
  classical
  let _ : SampleableType Chal := inferInstance
  have hlen : (FinEnum.toList Chal).length = FinEnum.card Chal := by
    simp [FinEnum.toList]
  let repStep : (Fin ρ → Commit × PrvState) → Fin ρ → AddWriterT κ m (Commit × Chal × Resp) :=
      fun commits i => do
    let comVec : Fin ρ → Commit := fun j => (commits j).1
    let comList := List.ofFn comVec
    let sc_i := (commits i).2
    let result ←
      fischlinSearchAuxWithAddCost σ
        (runtime := runtime) (pk := pk) (sk := sk) (sc := sc_i) (msg := msg)
        (comList := comList) (i := i)
        (FinEnum.toList Chal) (none : Option (Chal × Resp × Fin (2 ^ b))) costFn
    match result with
    | some (ω, resp) => pure (comVec i, ω, resp)
    | none => pure (comVec i, default, default)
  have hrep : ∀ commits i,
      AddWriterT.PathwiseCostAtMost (repStep commits i) (FinEnum.card Chal • w) := by
    intro commits i
    let comVec : Fin ρ → Commit := fun j => (commits j).1
    let comList := List.ofFn comVec
    have hsearch :
        AddWriterT.PathwiseCostAtMost
          (fischlinSearchAuxWithAddCost σ
            (runtime := runtime) (pk := pk) (sk := sk) (sc := (commits i).2)
            (msg := msg) (comList := comList) (i := i)
            (FinEnum.toList Chal) (none : Option (Chal × Resp × Fin (2 ^ b))) costFn)
          ((FinEnum.toList Chal).length • w) :=
      fischlinSearchAuxWithAddCost_pathwiseCostAtMost
        σ (κ := κ) (runtime := runtime) (pk := pk) (sk := sk) (sc := (commits i).2)
        (msg := msg) (comList := comList) (i := i)
        (challenges := FinEnum.toList Chal) (best := none) (costFn := costFn) (w := w)
        (hcost := hcost)
    let finish : Option (Chal × Resp) → AddWriterT κ m (Commit × Chal × Resp)
      | some (ω, resp) => pure (comVec i, ω, resp)
      | none => pure (comVec i, default, default)
    have hcont :
        ∀ result : Option (Chal × Resp), AddWriterT.PathwiseCostAtMost (finish result) 0 := by
      intro result
      cases result with
      | none =>
          simpa [finish] using AddWriterT.pathwiseCostAtMost_pure
            (m := m) ((comVec i, default, default) : Commit × Chal × Resp)
      | some pair =>
          rcases pair with ⟨ω, resp⟩
          simpa [finish] using AddWriterT.pathwiseCostAtMost_pure
            (m := m) ((comVec i, ω, resp) : Commit × Chal × Resp)
    refine AddWriterT.pathwiseCostAtMost_mono
      (AddWriterT.pathwiseCostAtMost_bind (w₁ := (FinEnum.toList Chal).length • w) (w₂ := 0)
        hsearch hcont) ?_
    simp [hlen]
  let commitComp : AddWriterT κ m (Fin ρ → Commit × PrvState) :=
    Fin.mOfFn ρ fun _ => (liftM (σ.commit pk sk) : AddWriterT κ m (Commit × PrvState))
  have hcommit :
      AddWriterT.PathwiseCostAtMost commitComp 0 := by
    have hstep :
        AddWriterT.PathwiseCostAtMost
          (liftM (σ.commit pk sk) : AddWriterT κ m (Commit × PrvState)) 0 := by
      simpa [WriterT.liftM_def] using
        (AddWriterT.pathwiseCostAtMost_monadLift
          (m := m) (monadLift (σ.commit pk sk) : m (Commit × PrvState)))
    simpa [commitComp] using
      (AddWriterT.pathwiseCostAtMost_fin_mOfFn (n := ρ) (k := 0)
        (f := fun _ => (liftM (σ.commit pk sk) : AddWriterT κ m (Commit × PrvState)))
        (fun _ => hstep))
  suffices
      AddWriterT.PathwiseCostAtMost
        (commitComp >>= fun commits => Fin.mOfFn ρ (repStep commits))
        (ρ • (FinEnum.card Chal • w)) by
    have hsign :
        HasQuery.Program.withAddCost
          (fun [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M) (AddWriterT κ m)] =>
            (Fischlin (m := AddWriterT κ m) σ hr ρ b S M).sign pk sk msg)
          runtime costFn =
          (commitComp >>= fun commits => Fin.mOfFn ρ (repStep commits)) := by
      simp only [Fischlin, HasQuery.Program.withAddCost, repStep, commitComp]
      refine congrArg
        (fun k => commitComp >>= k) ?_
      funext commits
      refine congrArg
        (fun f : Fin ρ → AddWriterT κ m (Commit × Chal × Resp) => Fin.mOfFn ρ f) ?_
      funext i
      let comVec : Fin ρ → Commit := fun j => (commits j).1
      let comList := List.ofFn comVec
      let finish : AddWriterT κ m (Option (Chal × Resp)) →
          AddWriterT κ m (Commit × Chal × Resp) := fun oa => do
        let result ← oa
        match result with
        | some (ω, resp) => pure (comVec i, ω, resp)
        | none => pure (comVec i, default, default)
      simpa [finish] using congrArg finish
        (fischlinSearchAux_eq_withAddCost
          σ (runtime := runtime) (pk := pk) (sk := sk) (sc := (commits i).2)
          (msg := msg) (comList := comList) (i := i)
          (challenges := FinEnum.toList Chal) (best := none) (costFn := costFn))
    simpa [HasQuery.UsesCostAtMost, hsign] using this
  simpa [zero_add] using
    (AddWriterT.pathwiseCostAtMost_bind (w₁ := 0) (w₂ := ρ • (FinEnum.card Chal • w)) hcommit
      (fun commits =>
        AddWriterT.pathwiseCostAtMost_fin_mOfFn (n := ρ) (k := FinEnum.card Chal • w)
          (fun i => hrep commits i)))

end signCostAccounting

section expectedWeightedQueryCost

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
variable [FinEnum Chal] [Inhabited Chal] [Inhabited Resp]
  (hr : GenerableRelation Stmt Wit rel) (S : ℕ)
  [DecidableEq M] [MonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

/-- Fischlin signing has expected weighted query cost at most `ρ • (|Ω| • w)` whenever every
random-oracle query is weighted by at most `w`. -/
theorem sign_expectedQueryCost_le
    {κ : Type} [AddCommMonoid κ] [PartialOrder κ] [IsOrderedAddMonoid κ]
    [CanonicallyOrderedAdd κ]
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain → κ) (w : κ)
    (val : κ → ENNReal) (hcost : ∀ t, costFn t ≤ w) (hval : Monotone val) :
    ExpectedQueryCost[
      (Fischlin σ hr ρ b S M).sign pk sk msg in runtime by costFn via val
    ] ≤ val (ρ • (FinEnum.card Chal • w)) := by
  exact HasQuery.expectedQueryCost_le_of_usesCostAtMost
    (sign_usesWeightedQueryCostAtMost
      (σ := σ) (hr := hr) (ρ := ρ) (b := b) (S := S) (M := M)
      (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
      (costFn := costFn) (w := w) hcost)
    hval

end expectedWeightedQueryCost

section expectedQueries

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
variable [FinEnum Chal] [Inhabited Chal] [Inhabited Resp]
  (hr : GenerableRelation Stmt Wit rel) (S : ℕ)
  [DecidableEq M] [MonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

/-- Fischlin signing has expected query count at most `ρ * |Ω|` in the unit-cost runtime model.

This is the expectation-level counterpart of
[`Fischlin.sign_usesAtMostRhoCardOmegaQueries`]. -/
theorem sign_expectedQueries_le_rhoCardOmega
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (sk : Wit) (msg : M) :
    ExpectedQueries[ (Fischlin σ hr ρ b S M).sign pk sk msg in runtime ]
      ≤ ρ * FinEnum.card Chal := by
  simpa [Nat.cast_mul] using HasQuery.expectedQueries_le_of_usesAtMostQueries
    (sign_usesAtMostRhoCardOmegaQueries
      (σ := σ) (hr := hr) (ρ := ρ) (b := b) (S := S) (M := M)
      (runtime := runtime) (pk := pk) (sk := sk) (msg := msg))

end expectedQueries

section expectedQueriesPMF

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
variable [FinEnum Chal] [Inhabited Chal] [Inhabited Resp]
  (hr : GenerableRelation Stmt Wit rel) (S : ℕ)
  [DecidableEq M] [MonadLiftT m PMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

/-- Fischlin verification has expected query count exactly `ρ` in the unit-cost runtime model. -/
theorem verify_expectedQueries_eq_rho
    (runtime : QueryImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M) m)
    (pk : Stmt) (msg : M) (π : FischlinProof Commit Chal Resp ρ) :
    ExpectedQueries[ (Fischlin σ hr ρ b S M).verify pk msg π in runtime ] = ρ := by
  apply HasQuery.expectedQueries_eq_of_usesAtMostQueries_of_usesAtLeastQueries
  · exact verify_usesAtMostRhoQueries
      (σ := σ) (hr := hr) (ρ := ρ) (b := b) (S := S) (M := M)
      (runtime := runtime) (pk := pk) (msg := msg) π
  · exact verify_usesAtLeastRhoQueries
      (σ := σ) (hr := hr) (ρ := ρ) (b := b) (S := S) (M := M)
      (runtime := runtime) (pk := pk) (msg := msg) π

end expectedQueriesPMF

end costAccounting

/-! ### Completeness -/

/-- Pigeonhole over repetitions: if the total of `ρ` per-repetition values exceeds `S`, then at
least one value exceeds `⌊S/ρ⌋`. Vacuous when `ρ = 0` (the empty sum is `0`, so `S < 0` is
impossible). This is the combinatorial heart of the Fischlin completeness union bound. -/
private lemma exists_div_lt_of_sum_lt {ρ : ℕ} (f : Fin ρ → ℕ) (S : ℕ)
    (h : S < ∑ i, f i) : ∃ i, S / ρ < f i := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hsum : ∑ i, f i ≤ ∑ _i : Fin ρ, S / ρ := Finset.sum_le_sum fun i _ => hcon i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact absurd (lt_of_lt_of_le h hsum) (not_lt.mpr (Nat.mul_div_le S ρ))

/-- Single-sample tail probability for the Fischlin random oracle: a uniform `Fin (2^b)` draw
exceeds threshold `k` with probability `(2^b - (k+1)) / 2^b`. The count of values exceeding `k`
is `2^b - (k+1)` (truncating to `0` once `k+1 > 2^b`), out of `2^b` total. -/
private lemma probEvent_val_gt_uniformSample (b k : ℕ) :
    Pr[fun (x : Fin (2 ^ b)) => k < x.val | ($ᵗ (Fin (2 ^ b)))]
      = (↑(2 ^ b - (k + 1)) : ℝ≥0∞) / ↑(2 ^ b) := by
  haveI : NeZero (2 ^ b) := ⟨Nat.two_pow_pos b |>.ne'⟩
  rw [probEvent_uniformSample]
  simp only [Fintype.card_fin]
  norm_cast
  congr 1
  set n := 2 ^ b with hn
  have hn_pos : 0 < n := Nat.two_pow_pos b
  set kFin : Fin n := ⟨min k (n - 1), by omega⟩
  have hconv : (Finset.univ.filter (fun x : Fin n => k < x.val)) = Finset.Ioi kFin := by
    rw [← Finset.filter_lt_eq_Ioi]
    ext ⟨x, hx⟩
    simp [Fin.lt_def, kFin]
    omega
  rw [hconv, Fin.card_Ioi]
  congr 1
  simp only [kFin]
  omega

/-- Min-tracking search over `t` fresh uniform `Fin (2^b)` samples, with early-exit when a
sample hits `0`. This is the pure-probability model of the Fischlin prover's per-repetition
hash minimisation: the random oracle, queried at `t` fresh distinct inputs, behaves as `t`
independent uniform draws. -/
private def minUnifAux (b : ℕ) : ℕ → Option (Fin (2 ^ b)) → ProbComp (Option (Fin (2 ^ b)))
  | 0,     best => pure best
  | n + 1, best => do
      let h ← $ᵗ (Fin (2 ^ b))
      if h.val = 0 then pure (some h)
      else minUnifAux b n (some (match best with
        | none    => h
        | some h' => if h.val < h'.val then h else h'))

/-- The running minimum (as an `Option`) exceeds the threshold `k`. -/
private def minGt (k : ℕ) {b : ℕ} : Option (Fin (2 ^ b)) → Prop
  | none   => True
  | some m => k < m.val

/-- Tail bound for the min-tracking search from an arbitrary starting `best`: the running
minimum exceeds `k` with probability `q^t` (scaled by whether the seed `best` already exceeds
`k`), where `q = (2^b - (k+1)) / 2^b`. Proved by induction on the sample count `t`. -/
private lemma minUnifAux_probEvent_gt (b k t : ℕ) (best : Option (Fin (2 ^ b))) :
    Pr[fun o => minGt k o | minUnifAux b t best]
      = (if (∀ m, best = some m → k < m.val) then (1 : ℝ≥0∞) else 0)
        * ((↑(2 ^ b - (k + 1)) : ℝ≥0∞) / ↑(2 ^ b)) ^ t := by
  induction t generalizing best with
  | zero =>
      cases best with
      | none =>
          simp [minUnifAux, minGt, probEvent_pure_eq_indicator, Set.indicator]
      | some m =>
          simp [minUnifAux, minGt, probEvent_pure_eq_indicator, Set.indicator]
  | succ n ih =>
      rw [minUnifAux, probEvent_bind_eq_tsum]
      set q : ℝ≥0∞ := (↑(2 ^ b - (k + 1)) : ℝ≥0∞) / ↑(2 ^ b) with hq
      have hbody : ∀ x : Fin (2 ^ b),
          probEvent
            (if (x : ℕ) = 0 then pure (some x)
            else minUnifAux b n (some (match best with
              | none => x | some h' => if (x : ℕ) < (h' : ℕ) then x else h')))
            (fun o => minGt k o)
          = (if (x : ℕ) = 0 then (0 : ℝ≥0∞)
             else if k < (match best with
              | none => x | some h' => if (x : ℕ) < (h' : ℕ) then x else h').val then 1 else 0)
            * q ^ n := by
        intro x
        by_cases hx : (x : ℕ) = 0
        · simp only [hx, if_true]
          rw [probEvent_pure_eq_indicator]
          simp only [minGt, Set.indicator, Set.mem_setOf_eq, hx]
          simp
        · simp only [hx, if_false]
          rw [ih]
          congr 1
          simp only [Option.some.injEq, forall_eq']
      rw [tsum_congr (fun x => by rw [hbody x, ← mul_assoc])]
      rw [ENNReal.tsum_mul_right]
      rw [pow_succ]
      rw [mul_comm (q ^ n) q, ← mul_assoc]
      congr 1
      rcases best with _ | b0
      · rw [if_pos (by simp), one_mul, hq, ← probEvent_val_gt_uniformSample b k,
          probEvent_eq_tsum_ite]
        refine tsum_congr fun i => ?_
        by_cases hi : (i : ℕ) = 0 <;> by_cases hk : k < (i : ℕ) <;> simp [hi, hk]
      · simp only [Option.some.injEq, forall_eq']
        by_cases hb : k < (b0 : ℕ)
        · rw [if_pos hb, one_mul, hq, ← probEvent_val_gt_uniformSample b k,
            probEvent_eq_tsum_ite]
          refine tsum_congr fun i => ?_
          by_cases hi : (i : ℕ) = 0 <;> by_cases hk : k < (i : ℕ) <;>
            by_cases hib : (i : ℕ) < (b0 : ℕ) <;> simp [hi, hk, hib] <;> omega
        · rw [if_neg hb, zero_mul]
          rw [show (∑' (i : Fin (2 ^ b)), Pr[= i | $ᵗ Fin (2 ^ b)] *
              if (i : ℕ) = 0 then (0 : ℝ≥0∞)
              else if k < ((if (i : ℕ) < (b0 : ℕ) then i else b0) : Fin (2 ^ b)).val then 1 else 0)
              = ∑' (_ : Fin (2 ^ b)), (0 : ℝ≥0∞) from ?_]
          · simp
          · refine tsum_congr fun i => ?_
            by_cases hi : (i : ℕ) = 0 <;> by_cases hib : (i : ℕ) < (b0 : ℕ) <;>
              simp [hi, hib] <;> omega

/-- Tail bound for the min-tracking search started fresh (`best = none`): the running minimum
exceeds `k` with probability exactly `q^t`. This is the per-repetition factor in the Fischlin
completeness union bound. -/
private lemma minUnifAux_probEvent_gt_none (b k t : ℕ) :
    Pr[fun o => minGt k o | minUnifAux b t none]
      = ((↑(2 ^ b - (k + 1)) : ℝ≥0∞) / ↑(2 ^ b)) ^ t := by
  rw [minUnifAux_probEvent_gt, if_pos (by simp), one_mul]

section security

variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (ρ b S : ℕ) (M : Type) [DecidableEq M]

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

/-! ### Model game `G` for the completeness analysis

The random-oracle game is analysed via an equivalent *pure-probability* model `G`. In `G`,
each random-oracle query of the prover's search is replaced by a fresh uniform draw from
`Fin (2^b)` (justified because every query in `sign` is at a distinct fresh input, hence a
cache miss), and the verifier reads the kept hash value directly from the search result rather
than re-querying (a cache hit returning the same value). -/

/-- Pure-probability copy of `fischlinSearchAux`: each random-oracle query is replaced by a fresh
uniform draw from `Fin (2^b)`, and the full best triple `(challenge, response, hash)` is kept
(on early exit at hash `0`, the current `(ω, resp, h)` is returned). -/
private def fischlinUnifSearch {Stmt Wit Commit PrvState Chal Resp : Type}
    {rel : Stmt → Wit → Bool} {b : ℕ}
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (sk : Wit) (sc : PrvState) :
    List Chal → Option (Chal × Resp × Fin (2 ^ b)) →
      ProbComp (Option (Chal × Resp × Fin (2 ^ b)))
  | [], best => pure best
  | ω :: rest, best => do
    let resp ← σ.respond pk sk sc ω
    let h ← $ᵗ (Fin (2 ^ b))
    if h.val = 0 then pure (some (ω, resp, h))
    else
      let newBest := match best with
        | none => some (ω, resp, h)
        | some (ω', resp', h') =>
          if h.val < h'.val then some (ω, resp, h) else some (ω', resp', h')
      fischlinUnifSearch σ pk sk sc rest newBest

/-- **Per-repetition tail bound.** The probability that `fischlinUnifSearch`'s kept hash exceeds
`k` is at most the corresponding `minUnifAux` tail probability. The `σ.respond` draws are
discarded by the hash projection, and they can only lose probability mass through failure, so the
hash-only model `minUnifAux` dominates. Proved by induction on the challenge list. -/
private lemma fischlinUnifSearch_probEvent_minGt_le
    {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool} {b : ℕ}
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (sk : Wit) (sc : PrvState) (k : ℕ)
    (cs : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b))) :
    Pr[fun o => minGt k (o.map (fun t => t.2.2)) | fischlinUnifSearch σ pk sk sc cs best]
      ≤ Pr[fun o => minGt k o | minUnifAux b cs.length (best.map (fun t => t.2.2))] := by
  induction cs generalizing best with
  | nil =>
      simp only [fischlinUnifSearch, minUnifAux]
      rw [probEvent_pure_eq_indicator, probEvent_pure_eq_indicator]
      refine le_of_eq ?_
      by_cases h : minGt k (Option.map (fun t => t.2.2) best) <;>
        simp [Set.indicator, Set.mem_setOf_eq, h]
  | cons ω rest ih =>
      simp only [fischlinUnifSearch, minUnifAux]
      refine probEvent_bind_le_of_forall_le (fun resp _ => ?_)
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum (fun h => ?_)
      refine mul_le_mul' le_rfl ?_
      by_cases hh : h.val = 0
      · simp only [hh, if_true]
        rw [probEvent_pure_eq_indicator, probEvent_pure_eq_indicator]
        refine le_of_eq ?_
        simp [Set.indicator, Set.mem_setOf_eq, minGt]
      · simp only [hh, if_false]
        refine le_trans (ih _) (le_of_eq ?_)
        congr 1
        cases best with
        | none => simp [Option.map]
        | some t =>
            obtain ⟨ω', resp', h'⟩ := t
            by_cases hlt : h.val < h'.val <;> simp [Option.map, hlt]

/-- The pure-probability model game `G` for Fischlin completeness.

Mirrors `keygen >>= sign >>= verify`, but the prover's per-repetition search uses
`fischlinUnifSearch` (fresh uniform draws) and the verifier reads the kept hash value
directly from the search result instead of re-querying the random oracle. Returns the verdict
`allVerified && (hashSum ≤ S)`. -/
private noncomputable def modelGame : ProbComp Bool := do
  let (pk, sk) ← hr.gen
  let commits : Fin ρ → Commit × PrvState ← Fin.mOfFn ρ fun _ => σ.commit pk sk
  let comVec : Fin ρ → Commit := fun i => (commits i).1
  let bests : Fin ρ → Option (Chal × Resp × Fin (2 ^ b)) ←
    Fin.mOfFn ρ fun i =>
      fischlinUnifSearch σ pk sk (commits i).2 (FinEnum.toList Chal)
        (none : Option (Chal × Resp × Fin (2 ^ b)))
  let allVerified := (List.finRange ρ).all fun i =>
    match bests i with
    | some (ω, resp, _) => σ.verify pk (comVec i) ω resp
    | none => σ.verify pk (comVec i) default default
  let hashSum := (List.finRange ρ).foldl
    (fun acc i => acc + (match bests i with | some (_, _, h) => h.val | none => 0)) 0
  pure (allVerified && decide (hashSum ≤ S))

/-- **B1 (random-oracle surgery).** The Fischlin random-oracle completeness game has the same
probability of accepting as the pure-probability model game `modelGame`.

Every random-oracle query made during `sign` is at a distinct, fresh `FischlinROInput` (the
challenge field ranges over the duplicate-free `FinEnum.toList Chal`, and the repetition index
field separates repetitions), so each is a cache miss whose answer is a fresh uniform sample —
matching `fischlinUnifSearch`. The chosen transcript's hash was cached during `sign`, so the
verifier's re-query is a cache hit returning that same value, matching the model's direct read. -/
private lemma fischlin_game_eq_model (msg : M) :
    Pr[= true | (runtime ρ b M).evalDist do
      let (pk, sk) ←
        (Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).keygen
      let sig ←
        (Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).sign pk sk msg
      (Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
        σ hr ρ b S M).verify pk msg sig]
      = Pr[= true | modelGame σ hr ρ b S] := by
  sorry

/-- Marginalizing a single coordinate `i` out of an independent product `Fin.mOfFn n g`:
the probability that the `i`-th component satisfies `p` is at most the probability that the
single computation `g i` satisfies `p`. The other coordinates integrate out to mass `≤ 1`,
so the inequality may be strict when those computations can fail. -/
private lemma probEvent_mOfFn_coord_le {α : Type} (n : ℕ) (g : Fin n → ProbComp α)
    (i : Fin n) (p : α → Prop) :
    Pr[fun v => p (v i) | Fin.mOfFn n g] ≤ Pr[fun x => p x | g i] := by
  classical
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rw [Fin.mOfFn]
      refine Fin.cases ?_ (fun j => ?_) i
      · -- coordinate `0`: the head `a ← g 0` determines `v 0`; the tail integrates to `≤ 1`.
        rw [probEvent_bind_eq_tsum]
        calc ∑' a, Pr[= a | g 0]
                * Pr[fun v => p (v 0) | Fin.mOfFn n (fun j => g j.succ) >>=
                    fun rest => (pure (Fin.cons a rest) : ProbComp (Fin (n+1) → α))]
            ≤ ∑' a, Pr[= a | g 0] * (if p a then (1 : ℝ≥0∞) else 0) := by
                refine ENNReal.tsum_le_tsum (fun a => mul_le_mul' le_rfl ?_)
                refine probEvent_bind_le_of_forall_le (fun rest _ => ?_)
                rw [probEvent_pure_eq_indicator]
                by_cases hp : p a <;>
                  simp [Set.indicator, Set.mem_setOf_eq, Fin.cons_zero, hp]
          _ = Pr[fun x => p x | g 0] := by
                rw [probEvent_eq_tsum_ite]
                refine tsum_congr (fun a => ?_)
                split <;> simp_all
      · -- coordinate `j+1`: `v (j+1) = rest j`; peel the head and recurse on the tail.
        rw [probEvent_bind_eq_tsum]
        calc ∑' a, Pr[= a | g 0]
                * Pr[fun v => p (v j.succ) | Fin.mOfFn n (fun j => g j.succ) >>=
                    fun rest => (pure (Fin.cons a rest) : ProbComp (Fin (n+1) → α))]
            ≤ ∑' a, Pr[= a | g 0] * Pr[fun x => p x | g j.succ] := by
                refine ENNReal.tsum_le_tsum (fun a => mul_le_mul' le_rfl ?_)
                refine le_trans (le_of_eq ?_) (ih (fun j => g j.succ) j)
                rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
                refine tsum_congr (fun rest => ?_)
                rw [probEvent_pure_eq_indicator]
                by_cases hp : p (rest j) <;>
                  simp [Set.indicator, Set.mem_setOf_eq, Fin.cons_succ, hp]
          _ ≤ Pr[fun x => p x | g j.succ] := by
                rw [ENNReal.tsum_mul_right]
                exact le_trans (mul_le_mul' tsum_probOutput_le_one le_rfl)
                  (le_of_eq (one_mul _))

/-- Support membership for the pure-probability search: any kept triple `(ω, resp, h)` has its
challenge drawn from the search list `cs` (or from the seed `best`), and its response in the
support of `σ.respond pk sk sc ω`. This lets perfect completeness apply to the chosen transcript. -/
private lemma fischlinUnifSearch_mem_support {Stmt Wit Commit PrvState Chal Resp : Type}
    {rel : Stmt → Wit → Bool} {b : ℕ}
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (sk : Wit) (sc : PrvState) :
    ∀ (cs : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b)))
      (ω : Chal) (resp : Resp) (h : Fin (2 ^ b)),
      (∀ ω' resp' h', some (ω', resp', h') = best →
        resp' ∈ support (σ.respond pk sk sc ω')) →
      some (ω, resp, h) ∈ support (fischlinUnifSearch σ pk sk sc cs best) →
      resp ∈ support (σ.respond pk sk sc ω) := by
  intro cs
  induction cs with
  | nil =>
      intro best ω resp h hbest hmem
      simp only [fischlinUnifSearch, support_pure, Set.mem_singleton_iff] at hmem
      exact hbest ω resp h hmem
  | cons ω₀ rest ih =>
      intro best ω resp h hbest hmem
      simp only [fischlinUnifSearch, mem_support_bind_iff] at hmem
      obtain ⟨resp₀, hresp₀, h₀, _, hmem⟩ := hmem
      by_cases hh : h₀.val = 0
      · simp only [hh, if_true, support_pure, Set.mem_singleton_iff] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        exact hresp₀
      · simp only [hh, if_false] at hmem
        refine ih _ ω resp h (fun ω' resp' h' heq => ?_) hmem
        cases hb : best with
        | none =>
            rw [hb] at heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl, rfl⟩ := heq
            exact hresp₀
        | some t =>
            obtain ⟨ωt, respt, ht⟩ := t
            rw [hb] at heq
            by_cases hlt : h₀.val < ht.val
            · simp only [hlt, if_true, Option.some.injEq, Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl, rfl⟩ := heq
              exact hresp₀
            · simp only [hlt, if_false, Option.some.injEq, Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl, rfl⟩ := heq
              exact hbest _ _ _ hb.symm

/-- Coordinatewise support membership for an independent product `Fin.mOfFn n g`: every value
in its support has each component in the support of the corresponding factor. -/
private lemma mem_support_mOfFn {α : Type} (n : ℕ) (g : Fin n → ProbComp α)
    (v : Fin n → α) (hv : v ∈ support (Fin.mOfFn n g)) (i : Fin n) :
    v i ∈ support (g i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rw [Fin.mOfFn, mem_support_bind_iff] at hv
      obtain ⟨a, ha, hv⟩ := hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨rest, hrest, hv⟩ := hv
      simp only [support_pure, Set.mem_singleton_iff] at hv
      subst hv
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · rw [Fin.cons_succ]
        exact ih (fun j => g j.succ) rest hrest j

/-- Pointwise corollary of perfect completeness: on a valid `(pk, sk)` pair, for any commitment
`(pc, sc)` in the support of `σ.commit`, any challenge `ω`, and any response `resp` in the support
of `σ.respond _ _ sc ω`, the verifier accepts. Extracted from the `Pr[= true | …] = 1` statement
via `probEvent_eq_one_iff` (the uniform challenge ranges over all of `Chal`). -/
private lemma verify_of_perfectlyComplete
    {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
    [SampleableType Chal]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hc : σ.PerfectlyComplete) (pk : Stmt) (sk : Wit) (hrel : rel pk sk = true)
    (pc : Commit) (sc : PrvState) (hpc : (pc, sc) ∈ support (σ.commit pk sk))
    (ω : Chal) (resp : Resp) (hresp : resp ∈ support (σ.respond pk sk sc ω)) :
    σ.verify pk pc ω resp = true := by
  have h1 := (probOutput_eq_one_iff_forall _ true |>.mp (hc pk sk hrel)).2
  have hmem : (σ.verify pk pc ω resp) ∈ support (do
      let (pc, sc) ← σ.commit pk sk
      let ω ← $ᵗ Chal
      let π ← σ.respond pk sk sc ω
      return σ.verify pk pc ω π) := by
    rw [mem_support_bind_iff]
    refine ⟨(pc, sc), hpc, ?_⟩
    rw [mem_support_bind_iff]
    refine ⟨ω, mem_support_uniformSample Chal, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨resp, hresp, by simp⟩
  exact h1 _ hmem

/-- The accumulating `foldl` used for the hash-sum in `modelGame` is the `Finset.univ` sum of the
per-repetition contributions. -/
private lemma foldl_add_finRange_eq_sum {ρ : ℕ} (g : Fin ρ → ℕ) :
    (List.finRange ρ).foldl (fun acc i => acc + g i) 0 = ∑ i : Fin ρ, g i := by
  have h : ∀ (l : List (Fin ρ)) (c : ℕ),
      l.foldl (fun acc i => acc + g i) c = c + (l.map g).sum := by
    intro l
    induction l with
    | nil => intro c; simp
    | cons a t ih => intro c; rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring
  rw [h, Nat.zero_add, Fin.sum_univ_def]

/-- On a valid, perfectly-complete instance, the per-repetition verifier branch always accepts:
the search over a non-empty challenge list returns `some (ω, resp, _)` whose response verifies
(perfect completeness applied to the chosen transcript). The `none` branch never arises. -/
private lemma fischlinUnifSearch_match_verify
    {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool} {b : ℕ}
    [SampleableType Chal] [Inhabited Chal] [Inhabited Resp]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hc : σ.PerfectlyComplete) (pk : Stmt) (sk : Wit) (hrel : rel pk sk = true)
    (pc : Commit) (sc : PrvState) (hpc : (pc, sc) ∈ support (σ.commit pk sk))
    (cs : List Chal) (hcs : cs ≠ [])
    (o : Option (Chal × Resp × Fin (2 ^ b)))
    (ho : o ∈ support (fischlinUnifSearch σ pk sk sc cs none)) :
    (match o with
      | some (ω, resp, _) => σ.verify pk pc ω resp
      | none => σ.verify pk pc default default) = true := by
  -- A search over a non-empty list with seed `none` keeps a `some` triple.
  have hsome : ∀ (cs : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b))),
      cs ≠ [] → ∀ o ∈ support (fischlinUnifSearch σ pk sk sc cs best), o.isSome := by
    intro cs
    induction cs with
    | nil => intro best hcs; exact absurd rfl hcs
    | cons ω₀ rest ih =>
        intro best _ o ho
        simp only [fischlinUnifSearch, mem_support_bind_iff] at ho
        obtain ⟨resp₀, _, h₀, _, ho⟩ := ho
        by_cases hh : h₀.val = 0
        · simp only [hh, if_true, support_pure, Set.mem_singleton_iff] at ho
          subst ho; rfl
        · simp only [hh, if_false] at ho
          rcases rest with _ | ⟨ω₁, rest'⟩
          · simp only [fischlinUnifSearch, support_pure, Set.mem_singleton_iff] at ho
            subst ho
            cases best with
            | none => rfl
            | some t =>
                obtain ⟨ω', resp', h'⟩ := t
                by_cases hlt : h₀.val < h'.val <;> simp [hlt]
          · exact ih _ (by simp) o ho
  have hisSome := hsome cs none hcs o ho
  cases o with
  | none => exact absurd hisSome (by simp)
  | some t =>
      obtain ⟨ω, resp, h⟩ := t
      have hresp : resp ∈ support (σ.respond pk sk sc ω) :=
        fischlinUnifSearch_mem_support σ pk sk sc cs none ω resp h
          (fun ω' resp' h' heq => by simp at heq) ho
      exact verify_of_perfectlyComplete σ hc pk sk hrel pc sc hpc ω resp hresp

/-- **B2 (probability bound).** The model game rejects with probability at most
`completenessError ρ b S (FinEnum.card Chal)`.

When the relation holds (guaranteed by `hr.gen_sound`) and the Σ-protocol is perfectly complete,
every honest transcript verifies, so rejection happens exactly when the sum of per-repetition
minimum hashes exceeds `S`. By pigeonhole some repetition's minimum exceeds `⌊S/ρ⌋`, and a union
bound over the `ρ` repetitions together with the per-repetition tail bound
`minUnifAux_probEvent_gt_none` yields the result. -/
private lemma model_reject_le (hρ : 0 < ρ) (hc : σ.PerfectlyComplete) (msg : M) :
    1 - Pr[= true | modelGame σ hr ρ b S]
      ≤ completenessError ρ b S (FinEnum.card Chal) := by
  -- Every `ProbComp` is `NeverFail`, so `1 - Pr[= true]` is exactly `Pr[= false]`.
  have hfalse : 1 - Pr[= true | modelGame σ hr ρ b S]
      = Pr[= false | modelGame σ hr ρ b S] := by
    rw [probOutput_false_eq_sub, probFailure_eq_zero' inferInstance, tsub_zero]
  rw [hfalse, ← probEvent_not_eq_probOutput]
  rw [modelGame]
  -- Peel the key-generation and commitment phases; on the support `rel pk sk` holds.
  refine probEvent_bind_le_of_forall_le (fun pksk hpksk => ?_)
  obtain ⟨pk, sk⟩ := pksk
  have hrel : rel pk sk = true := hr.gen_sound pk sk hpksk
  simp only
  refine probEvent_bind_le_of_forall_le (fun commits hcommits => ?_)
  sorry

/-- Almost completeness of the Fischlin transform: if the underlying Σ-protocol is
perfectly complete, then the signature scheme verifies with probability at least
`1 - completenessError ρ b S t` where `t = FinEnum.card Chal` is the challenge space size.

Unlike the Fiat-Shamir transform (which is perfectly complete), the Fischlin transform
has a non-zero completeness error because the prover's proof-of-work search may fail
to find hash values whose sum is at most `S`. -/
theorem almostComplete (hρ : 0 < ρ) (hc : σ.PerfectlyComplete) (msg : M) :
    Pr[= true | (runtime ρ b M).evalDist do
      let (pk, sk) ←
        (Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).keygen
      let sig ←
        (Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).sign pk sk msg
      (Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
        σ hr ρ b S M).verify pk msg sig]
    ≥ 1 - completenessError ρ b S (FinEnum.card Chal) := by
  rw [ge_iff_le, fischlin_game_eq_model σ hr ρ b S M msg]
  have hbound := model_reject_le σ hr ρ b S M hρ hc msg
  set P : ℝ≥0∞ := Pr[= true | modelGame σ hr ρ b S] with hP
  -- From `1 - P ≤ e` and `P ≤ 1` conclude `1 - e ≤ P`.
  have hP1 : P ≤ 1 := probOutput_le_one
  rw [tsub_le_iff_right] at hbound ⊢
  rwa [add_comm] at hbound

/-! ### Online Extraction / Knowledge Soundness -/

/-- Structural query bound: the computation makes at most `Q` total hash oracle queries
(`Sum.inr` queries), with no restriction on `unifSpec` queries (`Sum.inl`).

Defined as the generic predicate-targeted query bound `IsQueryBoundP` with the predicate
selecting the right (random-oracle) component of the index sum. -/
def ROQueryBound {α : Type}
    (oa : OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M) α)
    (Q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP oa (· matches .inr _) Q

/-- A cheating prover (knowledge soundness adversary) for the Fischlin transform.
The adversary receives a statement and message, has access to both the random oracle
and internal randomness (`unifSpec`), and attempts to produce a valid Fischlin proof
without knowing the witness.

The Σ-protocol `σ` is not referenced in the structure itself (only in the
extraction and verification steps of the experiment), so it enters the
theorem statements via hypotheses like `σ.SpeciallySound`. -/
structure KnowledgeSoundnessAdv where
  run : Stmt → M → OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
    (FischlinProof Commit Chal Resp ρ)

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
    (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) : ProbComp (Option Wit) :=
  let comList := List.ofFn fun i => (π i).1
  let findWitness : Fin ρ → Option (Chal × Resp × Chal × Resp) := fun i =>
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
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) : ProbComp Bool :=
  let roSpec := fischlinROSpec Stmt Commit Chal Resp ρ b M
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
        ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).verify x msg π)).run cache
    let extracted ← onlineExtract σ ρ b M x π roLog
    return (verified && !(match extracted with | some w => rel x w | none => false))

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
    (x : Stmt) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M adv.run x msg]
      ≤ knowledgeSoundnessError Q ρ b S := by sorry

/-! ### EUF-CMA Security

A tight EUF-CMA corollary for the Fischlin signature scheme requires an explicit
simulation of signing queries inside a hard-relation experiment. The previous
placeholder theorem overclaimed by bounding forgery probability solely by the
knowledge-soundness error, so we intentionally leave that corollary unstated
until the signing-simulation reduction is formalized. -/

end security

end Fischlin
