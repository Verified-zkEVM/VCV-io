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
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryCost
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
import Mathlib.Data.FinEnum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.Order.Antidiag.Pi

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

/-- The full simulation implementation (`unifFwdImpl + randomOracle`) interpreting the Fischlin
random-oracle world into `StateT QueryCache ProbComp`. This is definitionally the implementation
used by the bundled `withStateOracle` runtime. -/
@[reducible] private noncomputable def fischlinImpl :
    QueryImpl (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
      (StateT (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache ProbComp) :=
  unifFwdImpl (fischlinROSpec Stmt Commit Chal Resp ρ b M)
    + randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- The Fischlin runtime denotes a surface computation by simulating it with `fischlinImpl`
starting from the empty cache and discarding the final cache. -/
private lemma runtime_evalDist_eq
    {α : Type} (mx : OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M) α) :
    (runtime ρ b M).evalDist mx = 𝒟[(simulateQ (fischlinImpl ρ b M) mx).run' ∅] := by
  unfold runtime ProbCompRuntime.evalDist SPMFSemantics.evalDist SemanticsVia.denote
  simp only [SPMFSemantics.withStateOracle]
  rfl

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- The Fischlin runtime commutes with binding a lifted `ProbComp` prefix. -/
private lemma runtime_evalDist_bind_liftComp
    {α β : Type} (oa : ProbComp α)
    (rest : α → OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M) β) :
    (runtime ρ b M).evalDist (liftM oa >>= rest) =
      𝒟[oa] >>= fun x => (runtime ρ b M).evalDist (rest x) := by
  classical
  rw [runtime_evalDist_eq]
  simp_rw [runtime_evalDist_eq]
  rw [simulateQ_bind,
    roSim.run'_liftM_bind
      (ro := randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)) (oa := oa)
      (rest := fun x => simulateQ (fischlinImpl ρ b M) (rest x)) (s := ∅)]
  rw [evalDist_bind]

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

/-- Freshness predicate: every random-oracle input record for repetition `i` whose challenge
field lies in the challenge list `cs` is absent from `cache`. This is the invariant carried
through the per-repetition search bridge: as the search queries successive challenges, each query
is a cache miss, and the freshly cached record (whose challenge is the current loop variable) does
not collide with the still-to-be-queried challenges because `FinEnum.toList Chal` is duplicate-free
and the repetition index `i` separates repetitions. -/
private def searchFresh
    (pk : Stmt) (msg : M) (comList : List Commit) (i : Fin ρ) (cs : List Chal)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) : Prop :=
  ∀ ω ∈ cs, ∀ resp : Resp,
    cache (⟨pk, msg, comList, i, ω, resp⟩ : FischlinROInput Stmt Commit Chal Resp ρ M) = none

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- **Per-repetition search bridge — output distribution.**

Running Fischlin's inner search `fischlinSearchAux` under the lazy random-oracle simulation
`simulateQ fischlinImpl` on a `cache` in which every record of repetition `i` with a challenge
from `cs` is fresh, has the same *output* distribution (discarding the final cache via `run'`) as
the pure-uniform search `fischlinUnifSearch`, projected to `Option (Chal × Resp)`.

Each random-oracle query is a cache miss, so it samples a fresh uniform `Fin (2^b)` — exactly the
`$ᵗ` draw of `fischlinUnifSearch`. Freshness is preserved across the recursion: after querying the
current challenge `ω`, the only new cache entry has challenge field `ω`, which differs from every
challenge still in `rest` because `FinEnum.toList Chal` is duplicate-free. -/
private lemma fischlinSearch_run'_eq (pk : Stmt) (sk : Wit) (sc : PrvState)
    (msg : M) (comList : List Commit) (i : Fin ρ) (cs : List Chal)
    (hcs : cs.Nodup)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hfresh : searchFresh ρ b M pk msg comList i cs cache) :
    𝒟[(simulateQ (fischlinImpl ρ b M)
        (fischlinSearchAux σ pk sk sc msg comList i cs best)).run' cache]
      = 𝒟[(fun r => r.map fun (ω, resp, _) => (ω, resp)) <$>
          fischlinUnifSearch σ pk sk sc cs best] := by
  induction cs generalizing best cache with
  | nil =>
      simp only [fischlinSearchAux, fischlinUnifSearch, simulateQ_pure, StateT.run']
      rfl
  | cons ω rest ih =>
      rw [fischlinSearchAux, fischlinUnifSearch, simulateQ_bind,
        roSim.run'_liftM_bind
          (ro := randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)),
        map_bind]
      rw [evalDist_bind, evalDist_bind]
      refine congrArg (𝒟[σ.respond pk sk sc ω] >>= ·) (funext fun resp => ?_)
      rw [simulateQ_bind, roSim.simulateQ_HasQuery_query]
      -- Cache miss at the fresh record `⟨pk,msg,comList,i,ω,resp⟩`.
      have hmiss :
          (randomOracle
              (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)
              ⟨pk, msg, comList, i, ω, resp⟩ >>= fun x =>
              simulateQ (fischlinImpl ρ b M)
                (if x.val = 0 then pure (some (ω, resp))
                else
                  fischlinSearchAux σ pk sk sc msg comList i rest
                    (match best with
                    | none => some (ω, resp, x)
                    | some (ω', resp', h') =>
                        if x.val < h'.val then some (ω, resp, x)
                        else some (ω', resp', h')))).run' cache
            = ($ᵗ Fin (2 ^ b)) >>= fun x =>
                (simulateQ (fischlinImpl ρ b M)
                  (if x.val = 0 then pure (some (ω, resp))
                  else
                    fischlinSearchAux σ pk sk sc msg comList i rest
                      (match best with
                      | none => some (ω, resp, x)
                      | some (ω', resp', h') =>
                          if x.val < h'.val then some (ω, resp, x)
                          else some (ω', resp', h')))).run'
                  (cache.cacheQuery ⟨pk, msg, comList, i, ω, resp⟩ x) := by
        have hc : cache (⟨pk, msg, comList, i, ω, resp⟩ :
            FischlinROInput Stmt Commit Chal Resp ρ M) = none :=
          hfresh ω (by simp) resp
        change Prod.fst <$>
            ((randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)
                ⟨pk, msg, comList, i, ω, resp⟩ >>= _).run cache) = _
        rw [StateT.run_bind,
          QueryImpl.withCaching_run_none (so := uniformSampleImpl) hc]
        simp only [uniformSampleImpl, map_bind, bind_map_left, StateT.run']
        rfl
      rw [hmiss, map_bind, evalDist_bind, evalDist_bind]
      refine congrArg (𝒟[$ᵗ Fin (2 ^ b)] >>= ·) (funext fun x => ?_)
      by_cases hx : x.val = 0
      · simp only [hx, if_true, simulateQ_pure, StateT.run', map_pure, Option.map_some]
        rfl
      · simp only [hx, if_false]
        -- Recurse: freshness is preserved for `rest` after caching the `ω` record.
        have hfresh' : searchFresh ρ b M pk msg comList i rest
            (cache.cacheQuery ⟨pk, msg, comList, i, ω, resp⟩ x) := by
          intro ω' hω' r
          have hne : (⟨pk, msg, comList, i, ω', r⟩ :
              FischlinROInput Stmt Commit Chal Resp ρ M)
              ≠ ⟨pk, msg, comList, i, ω, resp⟩ := by
            intro hEq
            have : ω' = ω := congrArg FischlinROInput.chal hEq
            exact (List.nodup_cons.mp hcs).1 (this ▸ hω')
          exact (QueryCache.cacheQuery_of_ne cache x hne).trans
            (hfresh ω' (List.mem_cons_of_mem _ hω') r)
        exact ih (List.nodup_cons.mp hcs).2 _ _ hfresh'

/-- The random-oracle record that the Fischlin verifier re-queries for the transcript projected
from a search result `p : Option (Chal × Resp)`. On `none` (an unreachable branch when the
challenge list is nonempty, since the search always keeps a best) we return a dummy `default`
record; it is never consulted in the games below. -/
private def searchRecord (pk : Stmt) (msg : M) (comList : List Commit) (i : Fin ρ)
    [Inhabited Chal] [Inhabited Resp]
    (p : Option (Chal × Resp)) : FischlinROInput Stmt Commit Chal Resp ρ M :=
  match p with
  | some (ω, resp) => ⟨pk, msg, comList, i, ω, resp⟩
  | none => ⟨pk, msg, comList, i, default, default⟩

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp] [DecidableEq M]
  [FinEnum Chal] [SampleableType Chal] in
/-- Reading the final cache at the record of a kept best `o` returns `o`'s hash, provided the
cache already stores that hash for the corresponding record. A `none` best maps to a `none` read
under the dummy default record (this branch is unreachable for nonempty challenge lists). -/
private lemma searchRecord_cache_eq
    (pk : Stmt) (msg : M) (comList : List Commit) (i : Fin ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (o : Option (Chal × Resp × Fin (2 ^ b)))
    (hdef : o = none → cache (⟨pk, msg, comList, i, default, default⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = none)
    (ho : ∀ ω resp h, o = some (ω, resp, h) →
      cache (⟨pk, msg, comList, i, ω, resp⟩ : FischlinROInput Stmt Commit Chal Resp ρ M)
        = some h) :
    cache (searchRecord ρ M pk msg comList i (o.map fun t => (t.1, t.2.1)))
      = o.map fun t => t.2.2 := by
  cases o with
  | none =>
      simp only [Option.map_none, searchRecord]
      exact hdef rfl
  | some t =>
      obtain ⟨ω, resp, h⟩ := t
      simp only [Option.map_some, searchRecord]
      exact ho ω resp h rfl

omit [FinEnum Chal] [SampleableType Chal] in
/-- **Per-repetition search bridge — joint output and cached hash.**
Cache-carrying refinement of `fischlinSearch_run'_eq`: running the search under the lazy
random-oracle simulation, the joint distribution of the projected transcript together with the
final cache's value at that transcript's record equals the pure-uniform search's transcript paired
with its kept hash (wrapped in `some`).

The proof mirrors `fischlinSearch_run'_eq`. The extra content is the cache value at the chosen
record: on early exit the record was just cached with the returned hash (`cacheQuery_self`); on the
recursive branch the chosen record lies in `rest`, was cached deeper, and the freshly cached `ω`
record is distinct, so `cacheQuery_of_ne` preserves the deeper value. -/
private lemma fischlinSearch_run_cache_eq (pk : Stmt) (sk : Wit) (sc : PrvState)
    (msg : M) (comList : List Commit) (i : Fin ρ) (cs : List Chal)
    (hcs : cs.Nodup)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hfresh : searchFresh ρ b M pk msg comList i cs cache)
    (hdef : best = none → cache (⟨pk, msg, comList, i, default, default⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = none)
    (hbest : ∀ ω resp h, best = some (ω, resp, h) →
      cache (⟨pk, msg, comList, i, ω, resp⟩ : FischlinROInput Stmt Commit Chal Resp ρ M)
        = some h) :
    𝒟[(fun p => (p.1, p.2 (searchRecord ρ M pk msg comList i p.1))) <$>
        (simulateQ (fischlinImpl ρ b M)
          (fischlinSearchAux σ pk sk sc msg comList i cs best)).run cache]
      = 𝒟[(fun r => (r.map (fun (ω, resp, _) => (ω, resp)),
            r.map (fun (_, _, h) => h))) <$>
          fischlinUnifSearch σ pk sk sc cs best] := by
  induction cs generalizing best cache with
  | nil =>
      simp only [fischlinSearchAux, fischlinUnifSearch, simulateQ_pure, StateT.run_pure,
        map_pure, map_pure]
      rw [searchRecord_cache_eq ρ b M pk msg comList i cache best hdef hbest]
  | cons ω rest ih =>
      rw [fischlinSearchAux, fischlinUnifSearch, simulateQ_bind, StateT.run_bind,
        roSim.run_liftM
          (ro := randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)),
        bind_map_left, map_bind, map_bind]
      rw [evalDist_bind, evalDist_bind]
      refine congrArg (𝒟[σ.respond pk sk sc ω] >>= ·) (funext fun resp => ?_)
      rw [simulateQ_bind, roSim.simulateQ_HasQuery_query, StateT.run_bind]
      -- Cache miss at the fresh record `⟨pk,msg,comList,i,ω,resp⟩`.
      have hc : cache (⟨pk, msg, comList, i, ω, resp⟩ :
          FischlinROInput Stmt Commit Chal Resp ρ M) = none :=
        hfresh ω (by simp) resp
      rw [QueryImpl.withCaching_run_none (so := uniformSampleImpl) hc]
      simp only [uniformSampleImpl, map_bind, bind_map_left]
      rw [evalDist_bind, evalDist_bind]
      refine congrArg (𝒟[$ᵗ Fin (2 ^ b)] >>= ·) (funext fun x => ?_)
      by_cases hx : x.val = 0
      · simp only [hx, if_true, simulateQ_pure, StateT.run_pure, map_pure, map_pure,
          Option.map_some, searchRecord, QueryCache.cacheQuery_self]
      · simp only [hx, if_false]
        -- Recurse: freshness preserved and the new best's record is now cached at `x`.
        have hfresh' : searchFresh ρ b M pk msg comList i rest
            (cache.cacheQuery ⟨pk, msg, comList, i, ω, resp⟩ x) := by
          intro ω' hω' r
          have hne : (⟨pk, msg, comList, i, ω', r⟩ :
              FischlinROInput Stmt Commit Chal Resp ρ M)
              ≠ ⟨pk, msg, comList, i, ω, resp⟩ := by
            intro hEq
            have : ω' = ω := congrArg FischlinROInput.chal hEq
            exact (List.nodup_cons.mp hcs).1 (this ▸ hω')
          exact (QueryCache.cacheQuery_of_ne cache x hne).trans
            (hfresh ω' (List.mem_cons_of_mem _ hω') r)
        -- The updated best is always `some`, so the `none`-case obligation is vacuous.
        have hdef' : (match best with
              | none => some (ω, resp, x)
              | some (ω', resp', h') =>
                  if x.val < h'.val then some (ω, resp, x) else some (ω', resp', h')) = none →
            (cache.cacheQuery ⟨pk, msg, comList, i, ω, resp⟩ x)
              (⟨pk, msg, comList, i, default, default⟩ :
                FischlinROInput Stmt Commit Chal Resp ρ M) = none := by
          intro hnone
          cases best with
          | none => exact absurd hnone (by simp)
          | some t =>
              obtain ⟨ω', resp', h'⟩ := t
              by_cases hlt : x.val < h'.val
              · simp only [hlt, if_true] at hnone; exact absurd hnone (by simp)
              · simp only [hlt, if_false] at hnone; exact absurd hnone (by simp)
        -- Per-element cache fact for the updated best `newBest`.
        have hbest' : ∀ a r hh,
            (match best with
              | none => some (ω, resp, x)
              | some (ω', resp', h') =>
                  if x.val < h'.val then some (ω, resp, x) else some (ω', resp', h'))
              = some (a, r, hh) →
            (cache.cacheQuery ⟨pk, msg, comList, i, ω, resp⟩ x)
              (⟨pk, msg, comList, i, a, r⟩ :
                FischlinROInput Stmt Commit Chal Resp ρ M) = some hh := by
          intro a r hh hmatch
          cases best with
          | none =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hmatch
              obtain ⟨rfl, rfl, rfl⟩ := hmatch
              exact QueryCache.cacheQuery_self _ _ _
          | some t =>
              obtain ⟨ω', resp', h'⟩ := t
              have hbe : cache (⟨pk, msg, comList, i, ω', resp'⟩ :
                  FischlinROInput Stmt Commit Chal Resp ρ M) = some h' :=
                hbest ω' resp' h' rfl
              by_cases hlt : x.val < h'.val
              · simp only [hlt, if_true, Option.some.injEq, Prod.mk.injEq] at hmatch
                obtain ⟨rfl, rfl, rfl⟩ := hmatch
                exact QueryCache.cacheQuery_self _ _ _
              · simp only [hlt, if_false, Option.some.injEq, Prod.mk.injEq] at hmatch
                obtain ⟨rfl, rfl, rfl⟩ := hmatch
                by_cases heq : (⟨pk, msg, comList, i, ω', resp'⟩ :
                    FischlinROInput Stmt Commit Chal Resp ρ M)
                    = ⟨pk, msg, comList, i, ω, resp⟩
                · rw [heq, hc] at hbe
                  exact absurd hbe (by simp)
                · rw [QueryCache.cacheQuery_of_ne cache x heq, hbe]
        exact ih (List.nodup_cons.mp hcs).2 _ _ hfresh' hdef' hbest'

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- Simulating a `Fin.mOfFn` of lifted `ProbComp` computations leaves the cache untouched: the
result is the pure-probability product paired with the unchanged cache. Lifted queries are
forwarded by `unifFwdImpl` without consulting or modifying the random-oracle cache. -/
private lemma run_mOfFn_liftM {α : Type} (n : ℕ) (g : Fin n → ProbComp α)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :
    (simulateQ (fischlinImpl ρ b M)
        (Fin.mOfFn n fun i => (liftM (g i) :
          OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M) α))).run cache
      = (fun v => (v, cache)) <$> Fin.mOfFn n g := by
  induction n generalizing cache with
  | zero => simp [Fin.mOfFn, StateT.run_pure]
  | succ n ih =>
      rw [Fin.mOfFn, Fin.mOfFn, simulateQ_bind, StateT.run_bind,
        roSim.run_liftM (ro := randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)),
        map_bind, bind_map_left]
      refine bind_congr (fun a => ?_)
      rw [simulateQ_bind, StateT.run_bind, ih, map_bind, bind_map_left]
      refine bind_congr (fun rest => ?_)
      rw [simulateQ_pure, StateT.run_pure, map_pure]

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- Simulating the verifier's `Fin.mOfFn` of random-oracle re-queries on a cache that already
stores every re-queried record is deterministic: each query is a cache hit returning the stored
value, leaving the cache untouched. The result is the pure product of the per-repetition outputs
`f i (hash i)`, where `hash i` is the value cached at record `i`. -/
private lemma run_mOfFn_query_hit {β : Type} (n : ℕ)
    (records : Fin n → (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain)
    (hash : Fin n → Fin (2 ^ b)) (f : Fin n → Fin (2 ^ b) → β)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hhit : ∀ i, cache (records i) = some (hash i)) :
    (simulateQ (fischlinImpl ρ b M)
        (Fin.mOfFn n fun i => do
          let h ← HasQuery.query (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M) (records i)
          pure (f i h))).run cache
      = pure ((fun i => f i (hash i)), cache) := by
  induction n with
  | zero =>
      simp only [Fin.mOfFn, simulateQ_pure, StateT.run_pure]
      congr 1
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      rw [Fin.mOfFn, simulateQ_bind, StateT.run_bind, simulateQ_bind,
        roSim.simulateQ_HasQuery_query, StateT.run_bind,
        QueryImpl.withCaching_run_some (so := uniformSampleImpl) (hhit 0),
        pure_bind, simulateQ_pure, StateT.run_pure, pure_bind,
        simulateQ_bind, StateT.run_bind,
        ih (fun j => records j.succ) (fun j => hash j.succ) (fun j => f j.succ)
          (fun j => hhit j.succ), pure_bind, simulateQ_pure, StateT.run_pure]
      congr 1
      refine Prod.ext ?_ rfl
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [Fin.cons_zero]
      · simp [Fin.cons_succ]

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- **Off-repetition cache preservation.** Running repetition `i`'s search under the lazy
random-oracle simulation only ever caches records whose `rep` field equals `i` (every query is at
`⟨pk, msg, comList, i, ω, resp⟩`). Hence for every outcome in the support, the final cache agrees
with the starting cache on all records of other repetitions. Proved by induction on the challenge
list; each step caches one `rep = i` record (`cacheQuery_of_ne`), and the `liftM (respond)` step
never touches the cache. -/
private lemma fischlinSearch_run_preserves_offrep (pk : Stmt) (sk : Wit) (sc : PrvState)
    (msg : M) (comList : List Commit) (i : Fin ρ) (cs : List Chal)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (a : Option (Chal × Resp))
    (cache' : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hmem : (a, cache') ∈ support
      ((simulateQ (fischlinImpl ρ b M)
        (fischlinSearchAux σ pk sk sc msg comList i cs best)).run cache))
    (r : FischlinROInput Stmt Commit Chal Resp ρ M) (hr : r.rep ≠ i) :
    cache' r = cache r := by
  induction cs generalizing best cache with
  | nil =>
      simp only [fischlinSearchAux, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rw [hmem.2]
  | cons ω rest ih =>
      rw [fischlinSearchAux, simulateQ_bind, StateT.run_bind,
        roSim.run_liftM (ro := randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)),
        bind_map_left, support_bind] at hmem
      simp only [Set.mem_iUnion] at hmem
      obtain ⟨resp, hresp, hmem⟩ := hmem
      rw [simulateQ_bind, roSim.simulateQ_HasQuery_query, StateT.run_bind] at hmem
      have hne : r ≠ (⟨pk, msg, comList, i, ω, resp⟩ :
          FischlinROInput Stmt Commit Chal Resp ρ M) := by
        intro hEq; exact hr (congrArg FischlinROInput.rep hEq)
      by_cases hc : cache (⟨pk, msg, comList, i, ω, resp⟩ :
          FischlinROInput Stmt Commit Chal Resp ρ M) = none
      · rw [QueryImpl.withCaching_run_none (so := uniformSampleImpl) hc] at hmem
        simp only [uniformSampleImpl, bind_map_left, support_bind,
          support_uniformSample, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion] at hmem
        obtain ⟨x, hxmem⟩ := hmem
        by_cases hx : x.val = 0
        · simp only [hx, if_true, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hxmem
          rw [hxmem.2, QueryCache.cacheQuery_of_ne cache x hne]
        · simp only [hx, if_false] at hxmem
          rw [ih _ _ hxmem, QueryCache.cacheQuery_of_ne cache x hne]
      · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hc
        rw [QueryImpl.withCaching_run_some (so := uniformSampleImpl) hu, pure_bind] at hmem
        by_cases hx : u.val = 0
        · simp only [hx, if_true, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rw [hmem.2]
        · simp only [hx, if_false] at hmem
          exact ih _ _ hmem

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
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

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- `fischlinUnifSearch` keeps a `some` best whenever it starts from one or the challenge list is
non-empty: in support, every outcome of a search seeded with a `some` best, or run over a non-empty
list, is itself `some`. -/
private lemma fischlinUnifSearch_isSome (pk : Stmt) (sk : Wit) (sc : PrvState) :
    ∀ (cs : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b))),
      (best.isSome = true ∨ cs ≠ []) →
      ∀ o ∈ support (fischlinUnifSearch σ pk sk sc cs best), o.isSome = true := by
  intro cs
  induction cs with
  | nil =>
      intro best hb o ho
      simp only [fischlinUnifSearch, support_pure, Set.mem_singleton_iff] at ho
      rcases hb with hb | hb
      · rw [ho]; exact hb
      · exact absurd rfl hb
  | cons ω rest ih =>
      intro best _ o ho
      simp only [fischlinUnifSearch, mem_support_bind_iff] at ho
      obtain ⟨resp, _, h, _, ho⟩ := ho
      by_cases hh : h.val = 0
      · simp only [hh, if_true, support_pure, Set.mem_singleton_iff] at ho
        rw [ho]; rfl
      · simp only [hh, if_false] at ho
        refine ih _ (Or.inl ?_) o ho
        cases best with
        | none => rfl
        | some t => obtain ⟨ω', resp', h'⟩ := t; by_cases hlt : h.val < h'.val <;> simp [hlt]

omit [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- **Vector off-repetition cache preservation.** Running a `Fin.mOfFn` family of searches indexed
by `e : Fin n → Fin ρ`, every support outcome's final cache agrees with the starting cache on all
records whose `rep` field is not in the image of `e`. Induction on `n`, combining the single-search
`fischlinSearch_run_preserves_offrep` for the head with the inductive hypothesis for the tail. -/
private lemma searchVec_run_preserves_offrep (n : ℕ) (e : Fin n → Fin ρ)
    (pk : Stmt) (sk : Wit) (msg : M) (sc : Fin n → PrvState) (comList : List Commit)
    (toSig : Fin n → Option (Chal × Resp) → Commit × Chal × Resp)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :
    ∀ p ∈ support ((simulateQ (fischlinImpl ρ b M)
        (Fin.mOfFn n fun j =>
          fischlinSearchAux σ pk sk (sc j) msg comList (e j) (FinEnum.toList Chal)
            (none : Option (Chal × Resp × Fin (2 ^ b))) >>= fun result =>
              pure (toSig j result))).run cache),
      ∀ (r : FischlinROInput Stmt Commit Chal Resp ρ M), (∀ j, r.rep ≠ e j) → p.2 r = cache r := by
  induction n generalizing cache with
  | zero =>
      intro p hp r _
      simp only [Fin.mOfFn, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hp
      rw [hp]
  | succ n ih =>
      intro p hp r hr
      rw [Fin.mOfFn, simulateQ_bind, StateT.run_bind, support_bind] at hp
      simp only [Set.mem_iUnion, exists_prop] at hp
      obtain ⟨⟨out0, c1⟩, hhead, hp⟩ := hp
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hhead
      simp only [Set.mem_iUnion, exists_prop] at hhead
      obtain ⟨⟨res0, c1'⟩, hsearch0, hpure0⟩ := hhead
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hpure0
      obtain ⟨_, rfl⟩ := hpure0
      have hhead_pres : c1 r = cache r :=
        fischlinSearch_run_preserves_offrep σ ρ b M pk sk (sc 0) msg comList (e 0)
          (FinEnum.toList Chal) none cache res0 c1 hsearch0 r (hr 0)
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hp
      simp only [Set.mem_iUnion, exists_prop] at hp
      obtain ⟨⟨outRest, cFinal⟩, htail, hcons⟩ := hp
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hcons
      obtain ⟨_, rfl⟩ := hcons
      have htail_pres : cFinal r = c1 r :=
        ih (fun j => e j.succ) (fun j => sc j.succ) (fun j => toSig j.succ) c1
          (outRest, cFinal) htail r (fun j => hr j.succ)
      change cFinal r = cache r
      rw [htail_pres, hhead_pres]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Distributional bind congruence: continuations with equal output distributions on the support of
`mx` yield bound computations with equal output distributions. -/
private lemma evalDist_bind_congr_dist {α β : Type} (mx : ProbComp α)
    {f g : α → ProbComp β} (h : ∀ x ∈ support mx, 𝒟[f x] = 𝒟[g x]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  refine evalDist_ext fun y => ?_
  exact probOutput_bind_congr fun x hx => by rw [probOutput_def, probOutput_def, h x hx]

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- Running a search packaged with a pure post-processing `f` under the lazy random-oracle
simulation factors the post-processing out of the cache: it acts only on the output component,
leaving the threaded cache untouched. -/
private lemma simulateQ_run_map_pure {α β : Type}
    (s : OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M) α) (f : α → β)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :
    (simulateQ (fischlinImpl ρ b M) (s >>= fun r => pure (f r))).run cache
      = (fun p => (f p.1, p.2)) <$> (simulateQ (fischlinImpl ρ b M) s).run cache := by
  rw [simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp]
  refine bind_congr fun p => ?_
  rw [simulateQ_pure, StateT.run_pure]; rfl

omit [SampleableType Chal] in
/-- **Search-vector cache coupling — generalized over an injective rep-index map.** This is the
inductive engine behind `searchVec_run_cache_eq`: the `Fin.mOfFn` of searches indexed by an
injective `e : Fin n → Fin ρ`, run on a cache fresh for every `e`-indexed record, couples the
transcript vector together with the final cache's value at each chosen record to the pure-uniform
`fischlinUnifSearch` vector paired with its kept hashes. Induction on `n`: the head search caches
its own record (`fischlinSearch_run_cache_eq`); the tail's records carry distinct reps (`e`
injective) so they stay fresh and never disturb the head's cached record
(`searchVec_run_preserves_offrep`), making the tail distribution independent of the head's cache. -/
private lemma searchVec_run_cache_eq_aux (n : ℕ) (e : Fin n → Fin ρ) (he : Function.Injective e)
    (pk : Stmt) (sk : Wit) (msg : M) (sc : Fin n → PrvState) (comList : List Commit)
    (toSig : Fin n → Option (Chal × Resp) → Commit × Chal × Resp)
    (htoSig : ∀ j o, (toSig j o).2.1 = (o.getD default).1 ∧ (toSig j o).2.2 = (o.getD default).2)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hfresh : ∀ j ω resp, cache (⟨pk, msg, comList, e j, ω, resp⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = none) :
    𝒟[(fun p : (Fin n → Commit × Chal × Resp) ×
            (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache =>
          (p.1, fun j => p.2 (⟨pk, msg, comList, e j, (p.1 j).2.1, (p.1 j).2.2⟩ :
            FischlinROInput Stmt Commit Chal Resp ρ M))) <$>
        (simulateQ (fischlinImpl ρ b M)
          (Fin.mOfFn n fun j =>
            fischlinSearchAux σ pk sk (sc j) msg comList (e j) (FinEnum.toList Chal)
                (none : Option (Chal × Resp × Fin (2 ^ b))) >>= fun result =>
              pure (toSig j result))).run cache]
      = 𝒟[(fun bests : Fin n → Option (Chal × Resp × Fin (2 ^ b)) =>
            (fun j => toSig j ((bests j).map fun t => (t.1, t.2.1)),
            fun j => (bests j).map (fun t => t.2.2))) <$>
          Fin.mOfFn n fun j =>
            fischlinUnifSearch σ pk sk (sc j) (FinEnum.toList Chal)
              (none : Option (Chal × Resp × Fin (2 ^ b)))] := by
  induction n generalizing cache with
  | zero =>
      simp only [Fin.mOfFn, simulateQ_pure, StateT.run_pure, map_pure]
      congr 1
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      rw [Fin.mOfFn, Fin.mOfFn, simulateQ_bind, StateT.run_bind, simulateQ_run_map_pure,
        bind_map_left]
      simp only [map_bind, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        map_pure]
      -- The reusable record identity: the record the verifier reads for `toSig 0 o` is exactly
      -- `searchRecord (e 0) o`.
      have hrec : ∀ o : Option (Chal × Resp),
          (⟨pk, msg, comList, e 0, (toSig 0 o).2.1, (toSig 0 o).2.2⟩ :
            FischlinROInput Stmt Commit Chal Resp ρ M)
            = searchRecord ρ M pk msg comList (e 0) o := by
        intro o
        obtain ⟨h1, h2⟩ := htoSig 0 o
        cases o with
        | none => rw [h1, h2]; rfl
        | some t => obtain ⟨ω, resp⟩ := t; rw [h1, h2]; rfl
      -- The tail's pure-uniform product and the shared continuation `G`.
      set Utail := Fin.mOfFn n fun i =>
          fischlinUnifSearch σ pk sk (sc i.succ) (FinEnum.toList Chal)
            (none : Option (Chal × Resp × Fin (2 ^ b))) with hUtail
      set G : Option (Chal × Resp) × Option (Fin (2 ^ b)) →
          ProbComp ((Fin (n + 1) → Commit × Chal × Resp) × (Fin (n + 1) → Option (Fin (2 ^ b)))) :=
        fun q => Utail >>= fun tb => pure
          (Fin.cons (toSig 0 q.1) (fun k => toSig k.succ ((tb k).map fun t => (t.1, t.2.1))),
            Fin.cons q.2 (fun k => (tb k).map fun t => t.2.2)) with hG
      -- Step 1: reduce the tail under each head outcome to `G` evaluated at the head's read.
      refine Eq.trans (evalDist_bind_congr_dist _ (fun a ha => ?_))
        (b := 𝒟[(simulateQ (fischlinImpl ρ b M)
            (fischlinSearchAux σ pk sk (sc 0) msg comList (e 0)
              (FinEnum.toList Chal) none)).run cache
          >>= fun a => G (a.1, a.2 (searchRecord ρ M pk msg comList (e 0) a.1))]) ?head
      · -- Inner equality at a fixed head outcome `a = (out0, c1)`.
        -- The head's output cache `a.2` is fresh on every tail record (its `rep` lies in
        -- `image (e ∘ succ)`, which avoids `e 0` by injectivity; the head only caches rep-`e 0`).
        have ha2fresh : ∀ (k : Fin n) (ω : Chal) (resp : Resp),
            a.2 (⟨pk, msg, comList, e k.succ, ω, resp⟩ :
              FischlinROInput Stmt Commit Chal Resp ρ M) = none := by
          intro k ω resp
          rw [fischlinSearch_run_preserves_offrep σ ρ b M pk sk (sc 0) msg comList (e 0)
            (FinEnum.toList Chal) none cache a.1 a.2 (by simpa using ha) _
            (fun h => Fin.succ_ne_zero k (he (by simpa using h.symm)).symm)]
          exact hfresh k.succ ω resp
        rw [hG]
        refine Eq.trans (evalDist_bind_congr_dist _ (fun a_1 ha_1 => ?_))
          (b := 𝒟[(simulateQ (fischlinImpl ρ b M)
                (Fin.mOfFn n fun i =>
                  fischlinSearchAux σ pk sk (sc i.succ) msg comList (e i.succ)
                      (FinEnum.toList Chal) none >>= fun result =>
                    pure (toSig i.succ result))).run a.2
              >>= fun a_1 => pure
                (Fin.cons (toSig 0 a.1) a_1.1,
                  Fin.cons (a.2 (searchRecord ρ M pk msg comList (e 0) a.1))
                    (fun k => a_1.2 (⟨pk, msg, comList, e k.succ, (a_1.1 k).2.1, (a_1.1 k).2.2⟩ :
                      FischlinROInput Stmt Commit Chal Resp ρ M)))]) ?tailmap
        · -- The per-`a_1` `pure` equality: split the read-vector and discharge the head read.
          refine congrArg evalDist (congrArg pure (Prod.ext rfl (funext fun j => ?_)))
          refine Fin.cases ?_ (fun k => ?_) j
          · exact (@Fin.cons_zero n (fun _ => Commit × Chal × Resp) (toSig 0 a.1) a_1.1) ▸
              hrec a.1 ▸
              searchVec_run_preserves_offrep σ ρ b M n (fun i => e i.succ) pk sk msg
                (fun i => sc i.succ) comList (fun i => toSig i.succ) a.2 a_1 ha_1
                (searchRecord ρ M pk msg comList (e 0) a.1)
                (fun j => by
                  rcases a.1 with _ | ⟨ω, resp⟩ <;>
                    exact fun h => Fin.succ_ne_zero j (he (by simpa [searchRecord] using h)).symm)
          · rfl
        case tailmap =>
          have hih := ih (fun i => e i.succ)
            (fun x y hxy => Fin.succ_injective n (he hxy))
            (fun i => sc i.succ) (fun i => toSig i.succ)
            (fun j o => htoSig j.succ o) a.2 ha2fresh
          -- The shared outer reconstruction map: prepend the head transcript and read.
          have key := evalDist_map_eq_of_evalDist_eq hih
            (fun p : (Fin n → Commit × Chal × Resp) × (Fin n → Option (Fin (2 ^ b))) =>
              ((Fin.cons (toSig 0 a.1) p.1 : Fin (n + 1) → Commit × Chal × Resp),
                (Fin.cons (a.2 (searchRecord ρ M pk msg comList (e 0) a.1)) p.2 :
                  Fin (n + 1) → Option (Fin (2 ^ b)))))
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp] at key ⊢
          exact key
      case head =>
        -- Couple the head search to the pure-uniform search via the per-repetition bridge, then
        -- recombine with the cache-independent continuation `G`.
        rw [← bind_map_left
          (f := fun a : Option (Chal × Resp) ×
              (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache =>
            (a.1, a.2 (searchRecord ρ M pk msg comList (e 0) a.1)))
          (g := G)]
        rw [evalDist_bind, evalDist_bind,
          fischlinSearch_run_cache_eq σ ρ b M pk sk (sc 0) msg comList (e 0)
            (FinEnum.toList Chal) FinEnum.nodup_toList none cache
            (fun ω _ resp => hfresh 0 ω resp) (fun _ => hfresh 0 default default)
            (fun ω resp h hb => absurd hb (by simp))]
        rw [← evalDist_bind, ← evalDist_bind, bind_map_left]
        refine congrArg evalDist (bind_congr (fun best0 => bind_congr (fun tb => ?_)))
        congr 1
        refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
        · refine Fin.cases ?_ (fun k => ?_) j <;> simp [Fin.cons_zero, Fin.cons_succ]
        · refine Fin.cases ?_ (fun k => ?_) j <;> simp [Fin.cons_zero, Fin.cons_succ]

omit [SampleableType Chal] in
/-- **Search-vector cache coupling.** Running the `ρ` per-repetition searches (each packaged into a
transcript by `toSig`) under the lazy random-oracle on a cache that is fresh for every record,
the joint distribution of the transcript vector together with the final cache's value at each
repetition's chosen record equals `Fin.mOfFn ρ fischlinUnifSearch`'s transcripts paired with their
kept hashes.

`comList` is a fixed parameter (the verifier and prover agree on `List.ofFn (commits ·.1)`). The
proof is a `Fin.mOfFn` induction: at each repetition the per-repetition bridge
`fischlinSearch_run_cache_eq` applies (the records are fresh, carrying this repetition's index), and
`fischlinSearch_run_preserves_offrep` shows the remaining repetitions never disturb the record just
cached. -/
private lemma searchVec_run_cache_eq (pk : Stmt) (sk : Wit) (msg : M)
    (commits : Fin ρ → Commit × PrvState)
    (comList : List Commit) (toSig : Fin ρ → Option (Chal × Resp) → Commit × Chal × Resp)
    (htoSig : ∀ i o, (toSig i o).2.1 = (o.getD default).1 ∧ (toSig i o).2.2 = (o.getD default).2)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hfresh : ∀ i ω resp, cache (⟨pk, msg, comList, i, ω, resp⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = none) :
    𝒟[(fun p : (Fin ρ → Commit × Chal × Resp) ×
            (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache =>
          (p.1, fun i => p.2 (⟨pk, msg, comList, i, (p.1 i).2.1, (p.1 i).2.2⟩ :
            FischlinROInput Stmt Commit Chal Resp ρ M))) <$>
        (simulateQ (fischlinImpl ρ b M)
          (Fin.mOfFn ρ fun i =>
            fischlinSearchAux σ pk sk (commits i).2 msg comList i (FinEnum.toList Chal)
                (none : Option (Chal × Resp × Fin (2 ^ b))) >>= fun result =>
              pure (toSig i result))).run cache]
      = 𝒟[(fun bests : Fin ρ → Option (Chal × Resp × Fin (2 ^ b)) =>
            (fun i => toSig i ((bests i).map fun t => (t.1, t.2.1)),
            fun i => (bests i).map (fun t => t.2.2))) <$>
          Fin.mOfFn ρ fun i =>
            fischlinUnifSearch σ pk sk (commits i).2 (FinEnum.toList Chal)
              (none : Option (Chal × Resp × Fin (2 ^ b)))] := by
  exact searchVec_run_cache_eq_aux σ ρ b M ρ id Function.injective_id pk sk msg
    (fun i => (commits i).2) comList toSig htoSig cache hfresh

omit [SampleableType Chal] in
/-- The verifier's `run'`, on a cache that stores every re-queried record, is the deterministic
verdict computed from the stored hashes. A direct corollary of `run_mOfFn_query_hit`. -/
private lemma verify_run'_of_hits (pk : Stmt) (msg : M)
    (sig : Fin ρ → Commit × Chal × Resp)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hash : Fin ρ → Fin (2 ^ b))
    (hhit : ∀ i, cache (⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = some (hash i)) :
    (simulateQ (fischlinImpl ρ b M)
      ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
        σ hr ρ b S M).verify pk msg sig)).run' cache
      = pure ((List.finRange ρ).all (fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) &&
          decide ((List.finRange ρ).foldl (fun acc i => acc + (hash i).val) 0 ≤ S)) := by
  simp only [Fischlin]
  rw [simulateQ_bind, StateT.run'_bind',
    run_mOfFn_query_hit (n := ρ)
      (records := fun i => ⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩)
      (hash := hash)
      (f := fun i h => (σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2, h.val))
      (cache := cache) (hhit := hhit)]
  simp only [pure_bind, simulateQ_pure, StateT.run'_pure']

omit [SampleableType Chal] in
/-- **Cross-repetition cache threading.** Given a key pair `(pk, sk)` and a vector of commitments
`commits`, simulating the `ρ` per-repetition searches of `sign` followed by the `ρ` verifier
re-queries under the lazy random-oracle on the empty cache produces the same `Bool` distribution as
`modelGame`'s combinatorial verdict computed from `fischlinUnifSearch`.

The searches thread the cache: repetition `i`'s records carry `rep = i`, so they never collide
across repetitions (`fischlinSearch_run_preserves_offrep`), and each search caches its own chosen
record with its kept hash (`fischlinSearch_run_cache_eq`); hence after all `ρ` searches the final
cache stores every chosen record. Each verifier re-query is then a cache hit returning that hash
(`verify_run'_of_hits`, built on `run_mOfFn_query_hit`), matching `modelGame`'s direct read, and the
`allVerified`/`hashSum` fold is identical. The residual is the `Fin.mOfFn`-vector coupling of the
per-repetition bridge with off-repetition preservation. -/
private lemma sign_verify_run_eq (pk : Stmt) (sk : Wit) (msg : M)
    (commits : Fin ρ → Commit × PrvState) :
    𝒟[(simulateQ (fischlinImpl ρ b M)
        (do
          let comVec : Fin ρ → Commit := fun i => (commits i).1
          let comList := List.ofFn comVec
          let sig ← Fin.mOfFn ρ fun i => do
            let result ←
              fischlinSearchAux σ pk sk (commits i).2 msg comList i (FinEnum.toList Chal)
                (none : Option (Chal × Resp × Fin (2 ^ b)))
            match result with
            | some (ω, resp) => pure ((comVec i, ω, resp) : Commit × Chal × Resp)
            | none => pure (comVec i, default, default)
          (Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
            σ hr ρ b S M).verify pk msg sig)).run' ∅]
      = 𝒟[do
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
          pure (allVerified && decide (hashSum ≤ S))] := by
  -- `toSig` packaging the search result into a transcript with the fixed commitment.
  set comVec : Fin ρ → Commit := fun i => (commits i).1 with hcomVec
  set toSig : Fin ρ → Option (Chal × Resp) → Commit × Chal × Resp :=
    fun i o => match o with
      | some (ω, resp) => (comVec i, ω, resp)
      | none => (comVec i, default, default) with htoSigDef
  have htoSig : ∀ i o, (toSig i o).2.1 = (o.getD default).1 ∧
      (toSig i o).2.2 = (o.getD default).2 := by
    intro i o; cases o with
    | none => exact ⟨rfl, rfl⟩
    | some t => obtain ⟨ω, resp⟩ := t; exact ⟨rfl, rfl⟩
  -- Recognize each search body's `match` as `pure ∘ toSig`.
  have hbody : ∀ (i : Fin ρ) (result : Option (Chal × Resp)),
      (match result with
        | some (ω, resp) => pure ((comVec i, ω, resp) : Commit × Chal × Resp)
        | none => pure (comVec i, default, default) :
        OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
          (Commit × Chal × Resp))
      = pure (toSig i result) := by
    intro i result
    cases result with
    | none => rfl
    | some t => obtain ⟨ω, resp⟩ := t; rfl
  simp only [hbody]
  rw [simulateQ_bind, StateT.run'_bind']
  -- The empty cache is fresh for every record.
  have hfreshEmpty : ∀ i ω resp, (∅ : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
      (⟨pk, msg, List.ofFn comVec, i, ω, resp⟩ :
        FischlinROInput Stmt Commit Chal Resp ρ M) = none := fun _ _ _ => rfl
  -- The search-vector cache coupling, specialized to this `toSig`/`comList`/empty cache.
  have hcouple := searchVec_run_cache_eq σ ρ b M pk sk msg commits (List.ofFn comVec) toSig htoSig
    ∅ hfreshEmpty
  -- Support extraction: each `sign` outcome is the `toSig`-image of some `bests` in the model's
  -- support, and its final cache reads off exactly that `bests`'s kept hashes.
  have hsupp : ∀ p ∈ support ((simulateQ (fischlinImpl ρ b M)
        (Fin.mOfFn ρ fun i => fischlinSearchAux σ pk sk (commits i).2 msg (List.ofFn comVec) i
          (FinEnum.toList Chal) (none : Option (Chal × Resp × Fin (2 ^ b))) >>= fun result =>
            pure (toSig i result))).run ∅),
      ∃ bests ∈ support (Fin.mOfFn ρ fun i =>
          fischlinUnifSearch σ pk sk (commits i).2 (FinEnum.toList Chal)
            (none : Option (Chal × Resp × Fin (2 ^ b)))),
        (p.1 = fun i => toSig i ((bests i).map fun t => (t.1, t.2.1))) ∧
        ∀ i, p.2 (⟨pk, msg, List.ofFn comVec, i, (p.1 i).2.1, (p.1 i).2.2⟩ :
          FischlinROInput Stmt Commit Chal Resp ρ M) = (bests i).map fun t => t.2.2 := by
    intro p hp
    have hmem := (mem_support_iff_of_evalDist_eq hcouple
      ((fun p => (p.1, fun i => p.2 (⟨pk, msg, List.ofFn comVec, i, (p.1 i).2.1, (p.1 i).2.2⟩ :
        FischlinROInput Stmt Commit Chal Resp ρ M))) p)).mp
      (by rw [support_map]; exact Set.mem_image_of_mem _ hp)
    rw [support_map, Set.mem_image] at hmem
    obtain ⟨bests, hbests, hbeq⟩ := hmem
    refine ⟨bests, hbests, ?_, ?_⟩
    · exact (Prod.ext_iff.mp hbeq).1.symm
    · intro i; exact congrFun (Prod.ext_iff.mp hbeq).2.symm i
  -- The verdict as a function of the transcript vector and the read-off hashes.
  set V : (Fin ρ → Commit × Chal × Resp) × (Fin ρ → Option (Fin (2 ^ b))) → Bool :=
    fun q => ((List.finRange ρ).all fun i => σ.verify pk (q.1 i).1 (q.1 i).2.1 (q.1 i).2.2) &&
      decide ((List.finRange ρ).foldl (fun acc i => acc + ((q.2 i).getD 0).val) 0 ≤ S) with hV
  -- Step 1: collapse the verifier to the deterministic verdict `V` read off the threaded cache.
  refine Eq.trans (evalDist_bind_congr_dist _ (fun p hp => ?step1))
    (b := 𝒟[(simulateQ (fischlinImpl ρ b M)
          (Fin.mOfFn ρ fun i => fischlinSearchAux σ pk sk (commits i).2 msg (List.ofFn comVec) i
            (FinEnum.toList Chal) (none : Option (Chal × Resp × Fin (2 ^ b))) >>= fun result =>
              pure (toSig i result))).run ∅
        >>= fun p => pure (V (p.1, fun i => p.2 (⟨pk, msg, List.ofFn comVec, i, (p.1 i).2.1,
          (p.1 i).2.2⟩ : FischlinROInput Stmt Commit Chal Resp ρ M)))]) ?step2
  case step2 =>
    rw [bind_pure_comp,
      ← Functor.map_map (g := V)
        (m := fun p : (Fin ρ → Commit × Chal × Resp) ×
            (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache =>
          (p.1, fun i => p.2 (⟨pk, msg, List.ofFn comVec, i, (p.1 i).2.1, (p.1 i).2.2⟩ :
            FischlinROInput Stmt Commit Chal Resp ρ M))),
      evalDist_map_eq_of_evalDist_eq hcouple V, map_eq_bind_pure_comp, bind_map_left]
    refine congrArg evalDist (bind_congr fun bests => ?_)
    simp only [Function.comp]
    refine congrArg pure ?_
    rw [hV]
    refine congr_arg₂ (· && ·) ?_ ?_
    · refine congrArg (fun f => (List.finRange ρ).all f) (funext fun i => ?_)
      dsimp only
      cases h : bests i with
      | none => simp only [Option.map_none]; rfl
      | some t => obtain ⟨ω, resp, hh⟩ := t; simp only [Option.map_some]; rfl
    · refine congrArg (fun n => decide (n ≤ S))
        (congrArg (fun g => List.foldl g 0 (List.finRange ρ))
          (funext fun acc => funext fun i => ?_))
      dsimp only
      cases h : bests i with
      | none => simp only [Option.map_none, Option.getD_none]; rfl
      | some t => obtain ⟨ω, resp, hh⟩ := t; simp only [Option.map_some, Option.getD_some]
  case step1 =>
    obtain ⟨bests, hbests, hp1, hreads⟩ := hsupp p hp
    -- The list of challenges is nonempty (`Chal` is inhabited).
    have hcsne : (FinEnum.toList Chal) ≠ [] := List.ne_nil_of_mem (FinEnum.mem_toList default)
    -- Each model best is `some` (the challenge list is nonempty), so the read is a genuine hit.
    have hbest_some : ∀ i, (bests i).isSome = true := fun i =>
      fischlinUnifSearch_isSome σ b pk sk (commits i).2 (FinEnum.toList Chal) none
        (Or.inr hcsne) (bests i) (mem_support_mOfFn ρ _ bests hbests i)
    -- `toSig`'s commitment field is always `comVec`.
    have htoSig1 : ∀ i o, (toSig i o).1 = comVec i := by
      intro i o; rw [htoSigDef]; cases o with
      | none => rfl
      | some t => obtain ⟨ω, resp⟩ := t; rfl
    -- The verifier re-queries exactly the cached records.
    have hcom : (fun j => (p.1 j).1) = comVec := by
      funext j; rw [hp1]; exact htoSig1 j _
    -- The hash read off the cache at each repetition's chosen record.
    set hash : Fin ρ → Fin (2 ^ b) := fun i => (bests i).get (hbest_some i) |>.2.2 with hhashDef
    have hhit : ∀ i, p.2 (⟨pk, msg, List.ofFn (fun j => (p.1 j).1), i, (p.1 i).2.1,
        (p.1 i).2.2⟩ : FischlinROInput Stmt Commit Chal Resp ρ M) = some (hash i) := by
      intro i
      rw [hcom, hreads i, hhashDef]
      rw [Option.eq_some_iff_get_eq.mpr ⟨hbest_some i, rfl⟩]
      rfl
    change 𝒟[(simulateQ (fischlinImpl ρ b M)
        ((Fischlin σ hr ρ b S M).verify pk msg p.1)).run' p.2] = _
    rw [verify_run'_of_hits σ hr ρ b S M pk msg p.1 p.2 hash hhit]
    refine congrArg (𝒟[pure ·]) ?_
    rw [hV]
    refine congr_arg₂ (· && ·) rfl ?_
    refine congrArg (fun n => decide (n ≤ S))
      (congrArg (fun g => List.foldl g 0 (List.finRange ρ)) (funext fun acc => funext fun i => ?_))
    refine congrArg (acc + ·) ?_
    rw [hreads i, hhashDef]
    cases h : bests i with
    | none => exact absurd (h ▸ hbest_some i) (by simp)
    | some t =>
        obtain ⟨ω, resp, hh⟩ := t
        simp only [h, Option.get_some, Option.map_some, Option.getD_some]

omit [SampleableType Chal] in
/-- **Residual: full-game distribution surgery.** After collapsing the random-oracle runtime to a
`StateT`-simulation on the empty cache (`runtime_evalDist_eq`), the entire Fischlin game
`keygen >>= sign >>= verify`, observed as a `ProbComp Bool` via `StateT.run'`, has the same
distribution as `modelGame`.

This is the assembly step on top of the proven per-repetition output bridge
`fischlinSearch_run'_eq`. It additionally requires threading the lazy cache across the `ρ`
repetitions of `Fin.mOfFn` (each repetition's queries carry the repetition index in their
`FischlinROInput.rep` field, so they never collide across repetitions, preserving freshness) and
the verifier cache-hit step (the chosen transcript's hash was cached during `sign`, so each
verifier re-query returns the recorded value, matching `modelGame`'s direct read of
`(bests i).2.2`).
These two cache-coupling steps require a cache-carrying refinement of `fischlinSearch_run'_eq`. -/
private lemma fischlin_game_run'_eq_modelGame (msg : M) :
    𝒟[StateT.run' (simulateQ (fischlinImpl ρ b M)
        (do
          let (pk, sk) ←
            (Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
              σ hr ρ b S M).keygen
          let sig ←
            (Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
              σ hr ρ b S M).sign pk sk msg
          (Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
            σ hr ρ b S M).verify pk msg sig)) ∅]
      = 𝒟[modelGame σ hr ρ b S] := by
  simp only [Fischlin, fischlinImpl, bind_assoc]
  rw [simulateQ_bind, roSim.run'_liftM_bind
    (ro := randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M))]
  rw [modelGame, evalDist_bind, evalDist_bind]
  refine bind_congr (fun pksk => ?_)
  obtain ⟨pk, sk⟩ := pksk
  simp only []
  rw [simulateQ_bind, StateT.run'_bind', run_mOfFn_liftM, bind_map_left, evalDist_bind,
    evalDist_bind]
  refine bind_congr (fun commits => ?_)
  exact sign_verify_run_eq σ hr ρ b S M pk sk msg commits

omit [SampleableType Chal] in
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
  rw [runtime_evalDist_eq]
  change Pr[= true | StateT.run' (simulateQ (fischlinImpl ρ b M) _) ∅] = _
  rw [probOutput_def, probOutput_def, fischlin_game_run'_eq_modelGame σ hr ρ b S M msg]

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
    o.isSome = true ∧
      ∀ ω resp h, o = some (ω, resp, h) → σ.verify pk pc ω resp = true := by
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
  refine ⟨hisSome, fun ω resp h heq => ?_⟩
  subst heq
  have hresp : resp ∈ support (σ.respond pk sk sc ω) :=
    fischlinUnifSearch_mem_support σ pk sk sc cs none ω resp h
      (fun ω' resp' h' heq => by simp at heq) ho
  exact verify_of_perfectlyComplete σ hc pk sk hrel pc sc hpc ω resp hresp

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [DecidableEq M] in
/-- **B2 (probability bound).** The model game rejects with probability at most
`completenessError ρ b S (FinEnum.card Chal)`.

When the relation holds (guaranteed by `hr.gen_sound`) and the Σ-protocol is perfectly complete,
every honest transcript verifies, so rejection happens exactly when the sum of per-repetition
minimum hashes exceeds `S`. By pigeonhole some repetition's minimum exceeds `⌊S/ρ⌋`, and a union
bound over the `ρ` repetitions together with the per-repetition tail bound
`minUnifAux_probEvent_gt_none` yields the result. -/
private lemma model_reject_le (_hρ : 0 < ρ) (hc : σ.PerfectlyComplete) (_msg : M) :
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
  -- Each commitment lies in the support of `σ.commit pk sk`.
  have hci : ∀ i, (commits i) ∈ support (σ.commit pk sk) :=
    fun i => mem_support_mOfFn ρ _ commits hcommits i
  -- The challenge list is non-empty, so the search always returns a verified triple.
  have hcs : (FinEnum.toList Chal) ≠ [] := by
    have : (default : Chal) ∈ FinEnum.toList Chal := FinEnum.mem_toList _
    intro h; rw [h] at this; exact absurd this (by simp)
  -- Per-coordinate minimum-hash contribution.
  set minH : (Fin ρ → Option (Chal × Resp × Fin (2 ^ b))) → Fin ρ → ℕ :=
    fun bs i => match bs i with | some (_, _, h) => h.val | none => 0 with hminH
  -- Reduce the rejection event to "the hash sum exceeds `S`".
  rw [bind_pure_comp, probEvent_map]
  set bestsComp := Fin.mOfFn ρ
    fun i => fischlinUnifSearch σ pk sk (commits i).2 (FinEnum.toList Chal) none with hbestsComp
  refine le_trans (probEvent_mono (q := fun bs => S < ∑ i, minH bs i)
    (fun bs hbs hfalse => ?_)) ?_
  · -- On the support, `allVerified = true`, so a `false` verdict means `S < hashSum`.
    have hbsi : ∀ i, (bs i) ∈
        support (fischlinUnifSearch σ pk sk (commits i).2 (FinEnum.toList Chal) none) :=
      fun i => mem_support_mOfFn ρ _ bs hbs i
    have hall : ((List.finRange ρ).all fun i =>
        match bs i with
        | some (ω, resp, _) => σ.verify pk (commits i).1 ω resp
        | none => σ.verify pk (commits i).1 default default) = true := by
      rw [List.all_eq_true]
      intro i _
      obtain ⟨hsome, hver⟩ := fischlinUnifSearch_match_verify σ hc pk sk hrel (commits i).1
        (commits i).2 (hci i) (FinEnum.toList Chal) hcs (bs i) (hbsi i)
      cases hbi : bs i with
      | none => rw [hbi] at hsome; simp at hsome
      | some t =>
          obtain ⟨ω, resp, h⟩ := t
          simpa using hver ω resp h hbi
    -- The verdict is `false`, and `allVerified = true`, hence the hash sum exceeds `S`.
    simp only [Function.comp_apply, hall, Bool.true_and,
      decide_eq_false_iff_not, not_le] at hfalse
    rw [foldl_add_finRange_eq_sum (minH bs)] at hfalse
    exact hfalse
  · -- Pigeonhole: a sum exceeding `S` forces some coordinate to exceed `⌊S/ρ⌋`.
    refine le_trans (probEvent_mono (q := fun bs => ∃ i ∈ Finset.univ, S / ρ < minH bs i)
      (fun bs _ hsum => ?_)) ?_
    · obtain ⟨i, hi⟩ := exists_div_lt_of_sum_lt (minH bs) S hsum
      exact ⟨i, Finset.mem_univ i, hi⟩
    -- Union bound over repetitions, then marginalize each coordinate.
    refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
    have hlen : (FinEnum.toList Chal).length = FinEnum.card Chal := by
      simp [FinEnum.toList]
    have hterm : ∀ i : Fin ρ,
        (probEvent bestsComp fun bs => S / ρ < minH bs i)
          ≤ ((↑(2 ^ b - (S / ρ + 1)) : ℝ≥0∞) / ↑(2 ^ b)) ^ FinEnum.card Chal := by
      intro i
      -- Marginalize coordinate `i` of the independent product.
      refine le_trans (probEvent_mOfFn_coord_le ρ _ i (fun o => S / ρ < minH (fun _ => o) i)) ?_
      -- Reading the projected hash dominates the search-result hash event.
      refine le_trans (probEvent_mono'' (q := fun o => minGt (S / ρ) (o.map (fun t => t.2.2)))
        (fun o ho => ?_)) ?_
      · -- `S/ρ < (match o ...)` implies `minGt (S/ρ) (o.map ·)` (true also on `none`).
        rcases o with _ | ⟨ω, resp, h⟩
        · simp [minGt]
        · simpa [minGt, minH, Option.map] using ho
      · refine le_trans (fischlinUnifSearch_probEvent_minGt_le σ pk sk (commits i).2 (S / ρ)
          (FinEnum.toList Chal) none) ?_
        rw [Option.map_none, minUnifAux_probEvent_gt_none, hlen]
    refine le_trans (Finset.sum_le_sum (fun i _ => hterm i)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, completenessError]
    rw [nsmul_eq_mul]

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

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- The deterministic log scan performed by `onlineExtract`: search the repetitions for a logged
random-oracle query at the proof's statement/commitment-list/repetition tags that verifies
against the proof's commitment with a challenge different from the proof's challenge.
Definitionally equal to the internal `findSome?` of `onlineExtract` (see
`onlineExtract_eq_match`). -/
private def fischlinFindWitness (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) :
    Option (Chal × Resp × Chal × Resp) :=
  let comList := List.ofFn fun i => (π i).1
  (List.finRange ρ).findSome? fun i =>
    let (com_i, ω_i, _resp_i) := π i
    log.findSome? fun ⟨entry, _⟩ =>
      if entry.stmt == x && entry.comList == comList && entry.rep == i
          && σ.verify x com_i entry.chal entry.resp
          && decide (entry.chal ≠ ω_i) then
        some (ω_i, (π i).2.2, entry.chal, entry.resp)
      else none

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- `onlineExtract` is exactly a match on `fischlinFindWitness`. -/
private lemma onlineExtract_eq_match (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) :
    onlineExtract σ ρ b M x π log =
      match fischlinFindWitness σ ρ b M x π log with
      | some (ω₁, p₁, ω₂, p₂) => some <$> σ.extract ω₁ p₁ ω₂ p₂
      | none => return none := rfl

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- If the scan fires, every element of the support of `onlineExtract` is `some` of a valid
witness (given special soundness and per-repetition verification of the final proof). -/
private lemma onlineExtract_support_of_findWitness_ne_none
    (hss : σ.SpeciallySound)
    {x : Stmt} {π : FischlinProof Commit Chal Resp ρ}
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    (hver : ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true)
    (hfw : fischlinFindWitness σ ρ b M x π log ≠ none) :
    ∀ e ∈ support (onlineExtract σ ρ b M x π log),
      ∃ w : Wit, e = some w ∧ rel x w = true := by
  intro e he
  obtain ⟨⟨ω₁, p₁, ω₂, p₂⟩, hfw'⟩ := Option.ne_none_iff_exists'.mp hfw
  have he' : e ∈ support (some <$> σ.extract ω₁ p₁ ω₂ p₂) := by
    rw [onlineExtract_eq_match, hfw'] at he
    exact he
  rw [support_map] at he'
  obtain ⟨w, hw, rfl⟩ := he'
  refine ⟨w, rfl, ?_⟩
  -- Unpack the scan hit: a repetition `i` and a log entry passing the filter.
  obtain ⟨i, hi, hfi⟩ := List.exists_of_findSome?_eq_some hfw'
  obtain ⟨⟨entry, hv⟩, he2, hfe⟩ := List.exists_of_findSome?_eq_some hfi
  dsimp only at hfe
  split at hfe
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨⟨hstmt, hcom⟩, hrep⟩, hverE⟩, hneq⟩ := hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at hfe
    obtain ⟨h1, h2, h3, h4⟩ := hfe
    subst h1; subst h2; subst h3; subst h4
    exact σ.extract_sound_of_speciallySoundAt (hss x) (Ne.symm hneq) (hver i) hverE hw
  · exact absurd hfe (by simp)

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- Every `some w` in the support of `onlineExtract` is a valid witness, given special soundness
and per-repetition verification of the final proof. -/
private lemma onlineExtract_some_valid
    (hss : σ.SpeciallySound)
    {x : Stmt} {π : FischlinProof Commit Chal Resp ρ}
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    (hver : ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true) :
    ∀ w : Wit, some w ∈ support (onlineExtract σ ρ b M x π log) → rel x w = true := by
  intro w hw
  by_cases hfw : fischlinFindWitness σ ρ b M x π log = none
  · -- The scan missed: the extractor returns `none`, so `some w` is not in the support.
    rw [onlineExtract_eq_match, hfw] at hw
    simp at hw
  · obtain ⟨w', hw', hrel⟩ :=
      onlineExtract_support_of_findWitness_ne_none σ ρ b M hss hver hfw _ hw
    cases Option.some.inj hw'
    exact hrel

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- If the extractor's scan finds nothing, then every log entry matching a repetition's
`(stmt, comList, rep)` tags and verifying against the proof's commitment carries exactly the
proof's challenge. -/
private lemma chal_pinned_of_findWitness_none
    {x : Stmt} {π : FischlinProof Commit Chal Resp ρ}
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    (hnone : fischlinFindWitness σ ρ b M x π log = none)
    (i : Fin ρ)
    (e : (_t : FischlinROInput Stmt Commit Chal Resp ρ M) × Fin (2 ^ b))
    (he : e ∈ log)
    (hstmt : e.1.stmt = x) (hcom : e.1.comList = List.ofFn fun j => (π j).1)
    (hrep : e.1.rep = i) (hverE : σ.verify x (π i).1 e.1.chal e.1.resp = true) :
    e.1.chal = (π i).2.1 := by
  by_contra hne
  rw [fischlinFindWitness, List.findSome?_eq_none_iff] at hnone
  have hi : log.findSome? (fun e' =>
      if e'.1.stmt == x && e'.1.comList == (List.ofFn fun j => (π j).1) && e'.1.rep == i
          && σ.verify x (π i).1 e'.1.chal e'.1.resp
          && decide (e'.1.chal ≠ (π i).2.1) then
        some ((π i).2.1, (π i).2.2, e'.1.chal, e'.1.resp)
      else none) = none := hnone i (List.mem_finRange i)
  rw [List.findSome?_eq_none_iff] at hi
  have hfe := hi e he
  rw [if_pos (by simp [hstmt, hcom, hrep, hverE, hne])] at hfe
  exact Option.some_ne_none _ hfe

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- Under `UniqueResponses`, if additionally the final proof verifies at repetition `i`, a
matching log entry carries exactly the proof's challenge *and response*. -/
private lemma resp_pinned_of_findWitness_none
    (hur : σ.UniqueResponses)
    {x : Stmt} {π : FischlinProof Commit Chal Resp ρ}
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    (hnone : fischlinFindWitness σ ρ b M x π log = none)
    (i : Fin ρ)
    (hveri : σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true)
    (e : (_t : FischlinROInput Stmt Commit Chal Resp ρ M) × Fin (2 ^ b))
    (he : e ∈ log)
    (hstmt : e.1.stmt = x) (hcom : e.1.comList = List.ofFn fun j => (π j).1)
    (hrep : e.1.rep = i) (hverE : σ.verify x (π i).1 e.1.chal e.1.resp = true) :
    e.1.chal = (π i).2.1 ∧ e.1.resp = (π i).2.2 := by
  have hchal : e.1.chal = (π i).2.1 :=
    chal_pinned_of_findWitness_none σ ρ b M hnone i e he hstmt hcom hrep hverE
  exact ⟨hchal, hur x (π i).1 (π i).2.1 e.1.resp (π i).2.2 (hchal ▸ hverE) hveri⟩

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

/-- The verification step of `knowledgeSoundnessExp`, as a standalone computation
(definitionally the same term). -/
private noncomputable def ksVerify (x : Stmt) (msg : M) (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :
    ProbComp (Bool × (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :=
  let roSpec := fischlinROSpec Stmt Commit Chal Resp ρ b M
  let ro : QueryImpl roSpec (StateT roSpec.QueryCache ProbComp) := randomOracle
  let idImpl' := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT roSpec.QueryCache ProbComp)
  (simulateQ (idImpl' + ro)
    ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
      σ hr ρ b S M).verify x msg π)).run cache

/-- The sampling phase of `knowledgeSoundnessExp` (prover run + verification), keeping the proof,
the random-oracle log, and the verdict, but discarding the extractor. -/
private noncomputable def ksSample
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) :
    ProbComp ((FischlinProof Commit Chal Resp ρ ×
      QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) × Bool) :=
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
    return ((π, roLog), verified)

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- If the scan fires (and the proof verifies per repetition), the "bad-output" map of the
extractor result never produces `true`. -/
private lemma probOutput_onlineExtract_bad_eq_zero
    (hss : σ.SpeciallySound)
    {x : Stmt} {π : FischlinProof Commit Chal Resp ρ}
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    (hver : ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true)
    (hfw : fischlinFindWitness σ ρ b M x π log ≠ none) :
    Pr[= true | do
      let e ← onlineExtract σ ρ b M x π log
      return !(match e with | some w => rel x w | none => false)] = 0 := by
  rw [probOutput_bind_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr fun e => ?_
  by_cases he : e ∈ support (onlineExtract σ ρ b M x π log)
  · obtain ⟨w, rfl, hrel⟩ :=
      onlineExtract_support_of_findWitness_ne_none σ ρ b M hss hver hfw e he
    simp [hrel]
  · simp [probOutput_eq_zero_of_not_mem_support he]

omit [SampleableType Chal] in
/-- **Bad-event bridge.** The bad event of the knowledge-soundness experiment is bounded by the
probability that the verifier accepts while the extractor's scan misses.

The hypothesis `hverSupp` isolates the remaining combinatorial fact about the Fischlin verifier:
any accepting run of the (simulated) verifier implies per-repetition Σ-verification of the proof
(the Σ-verification bits inside `Fischlin.verify` are deterministic, independent of the oracle
answers). -/
private lemma knowledgeSoundnessExp_bad_le_misses
    (hss : σ.SpeciallySound)
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M)
    (hverSupp : ∀ (π : FischlinProof Commit Chal Resp ρ)
      (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
      (c' : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache),
      (true, c') ∈ support (ksVerify σ hr ρ b S M x msg π cache) →
      ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M prover x msg] ≤
      Pr[fun out => out.2 = true ∧ fischlinFindWitness σ ρ b M x out.1.1 out.1.2 = none
        | ksSample σ hr ρ b S M prover x msg] := by
  simp only [knowledgeSoundnessExp, ksSample]
  rw [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl ?_
  obtain ⟨⟨π', roLog'⟩, cache'⟩ := a
  rw [probOutput_bind_eq_tsum_subtype, probEvent_bind_eq_tsum_subtype]
  refine ENNReal.tsum_le_tsum fun vc => mul_le_mul' le_rfl ?_
  obtain ⟨⟨v, c'⟩, hvc⟩ := vc
  cases v with
  | false =>
    have hzero : Pr[= true | do
        let _e ← onlineExtract σ ρ b M x π' roLog'
        return false] = 0 := by
      simp
    exact le_trans (le_of_eq hzero) zero_le'
  | true =>
    by_cases hfw : fischlinFindWitness σ ρ b M x π' roLog' = none
    · refine le_trans probOutput_le_one (le_of_eq ?_)
      rw [probEvent_pure]
      simp [hfw]
    · have hver := hverSupp π' cache' c' hvc
      have hzero := probOutput_onlineExtract_bad_eq_zero σ ρ b M hss hver hfw
      exact le_trans (le_of_eq hzero) zero_le'

/-- The lifted `unifSpec` forwarder on the logging stack, exactly as in
`knowledgeSoundnessExp`. -/
private noncomputable def idImplW {ι : Type} (hashSpec : OracleSpec ι) :
    QueryImpl unifSpec (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp)) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp))

/-- The logged random oracle, exactly as in `knowledgeSoundnessExp`. -/
private noncomputable def loggedROW {ι : Type} (hashSpec : OracleSpec ι) [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)] :
    QueryImpl hashSpec (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp)) :=
  (hashSpec.randomOracle).withLogging

/-- The combined logging implementation, exactly the `idImpl + loggedRO` of
`knowledgeSoundnessExp` and `ksSample`. -/
private noncomputable def compositeW {ι : Type} (hashSpec : OracleSpec ι) [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)] :
    QueryImpl (unifSpec + hashSpec)
      (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp)) :=
  idImplW hashSpec + loggedROW hashSpec

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The lifted unifSpec forwarder neither logs nor touches the cache. -/
private lemma idImplW_run_run {ι : Type} (hashSpec : OracleSpec ι)
    (i : unifSpec.Domain) (c : hashSpec.QueryCache) :
    ((idImplW hashSpec i).run).run c =
      (fun u => ((u, (∅ : QueryLog hashSpec)), c)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) i) := by
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Cache hit: the logged random oracle returns the cached value, logs it, leaves the cache. -/
private lemma loggedROW_run_run_some {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {t : hashSpec.Domain} {c : hashSpec.QueryCache} {u : hashSpec.Range t}
    (h : c t = some u) :
    ((loggedROW hashSpec t).run).run c = pure ((u, ([⟨t, u⟩] : QueryLog hashSpec)), c) := by
  rw [loggedROW, QueryImpl.run_withLogging_apply, StateT.run_bind,
    show hashSpec.randomOracle = QueryImpl.withCaching uniformSampleImpl from rfl,
    QueryImpl.withCaching_run_some _ h, pure_bind]
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Cache miss: the logged random oracle samples, caches the value, and logs it. -/
private lemma loggedROW_run_run_none {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {t : hashSpec.Domain} {c : hashSpec.QueryCache} (h : c t = none) :
    ((loggedROW hashSpec t).run).run c =
      (fun u => ((u, ([⟨t, u⟩] : QueryLog hashSpec)), c.cacheQuery t u)) <$>
        ($ᵗ hashSpec.Range t) := by
  rw [loggedROW, QueryImpl.run_withLogging_apply, StateT.run_bind,
    show hashSpec.randomOracle = QueryImpl.withCaching uniformSampleImpl from rfl,
    QueryImpl.withCaching_run_none _ h]
  rw [show uniformSampleImpl (spec := hashSpec) t = ($ᵗ hashSpec.Range t) from rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind, map_eq_bind_pure_comp]
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Master log↔cache correspondence.** For any run of the Fischlin-style logging composite
from cache `cache₀` (and an empty ambient log), every support outcome `((a, log), cache')`
satisfies: the cache only grows, every logged entry is in the final cache with the same value,
and every final cache entry was either logged or already present in `cache₀`. -/
private theorem mem_support_run_correspondence {ι : Type} {hashSpec : OracleSpec ι}
    [DecidableEq ι] [hashSpec.DecidableEq]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)] {α : Type}
    (oa : OracleComp (unifSpec + hashSpec) α)
    (cache₀ : hashSpec.QueryCache)
    (z : (α × QueryLog hashSpec) × hashSpec.QueryCache)
    (hz : z ∈ support (((simulateQ (compositeW hashSpec) oa).run).run cache₀)) :
    cache₀ ≤ z.2 ∧
      (∀ e ∈ z.1.2, z.2 e.1 = some e.2) ∧
      (∀ (t : hashSpec.Domain) (u : hashSpec.Range t), z.2 t = some u →
        (⟨t, u⟩ : (s : hashSpec.Domain) × hashSpec.Range s) ∈ z.1.2 ∨ cache₀ t = some u) := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
      simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨le_rfl, fun e he => ?_, fun t u hu => Or.inr hu⟩
      simp only [List.empty_eq, List.not_mem_nil] at he
  | query_bind t k ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        WriterT.run_bind', StateT.run_bind] at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨⟨⟨u, w₁⟩, c₁⟩, hp, hrest⟩ := hz
      rw [StateT.run_map, support_map] at hrest
      obtain ⟨⟨⟨a₂, w₂⟩, c₂⟩, hmem₂, hzeq⟩ := hrest
      subst hzeq
      obtain ⟨hmono, hT1, hT2⟩ := ih _ c₁ _ hmem₂
      cases t with
      | inl i =>
          change ((u, w₁), c₁) ∈ support (((idImplW hashSpec i).run).run cache₀) at hp
          rw [idImplW_run_run, support_map] at hp
          obtain ⟨v, hv, hpe⟩ := hp
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpe
          refine ⟨hmono, ?_, ?_⟩
          · intro e he
            simp only [Prod.map, id, List.empty_eq, List.nil_append] at he ⊢
            exact hT1 e he
          · intro t' u' hu'
            simp only [Prod.map, id, List.empty_eq, List.nil_append]
            exact hT2 t' u' hu'
      | inr j =>
          change ((u, w₁), c₁) ∈ support (((loggedROW hashSpec j).run).run cache₀) at hp
          cases hc : cache₀ j with
          | some u₀ =>
              rw [loggedROW_run_run_some hc, support_pure] at hp
              have hp' : ((u, w₁), c₁) = ((u₀, [⟨j, u₀⟩]), cache₀) := hp
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp'
              refine ⟨hmono, ?_, ?_⟩
              · intro e he
                simp only [Prod.map, id, List.cons_append, List.nil_append,
                  List.mem_cons] at he ⊢
                rcases he with rfl | he
                · exact hmono hc
                · exact hT1 e he
              · intro t' u' hu'
                simp only [Prod.map, id, List.cons_append, List.nil_append, List.mem_cons]
                rcases hT2 t' u' hu' with h | h
                · exact Or.inl (Or.inr h)
                · exact Or.inr h
          | none =>
              rw [loggedROW_run_run_none hc, support_map] at hp
              obtain ⟨v, hv, hpe⟩ := hp
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpe
              refine ⟨le_trans (QueryCache.le_cacheQuery _ hc) hmono, ?_, ?_⟩
              · intro e he
                simp only [Prod.map, id, List.cons_append, List.nil_append,
                  List.mem_cons] at he ⊢
                rcases he with rfl | he
                · exact hmono (QueryCache.cacheQuery_self cache₀ j u)
                · exact hT1 e he
              · intro t' u' hu'
                simp only [Prod.map, id, List.cons_append, List.nil_append, List.mem_cons]
                rcases hT2 t' u' hu' with h | h
                · exact Or.inl (Or.inr h)
                · by_cases ht : t' = j
                  · subst ht
                    rw [QueryCache.cacheQuery_self] at h
                    exact Or.inl (Or.inl (by rw [Option.some.injEq] at h; rw [h]))
                  · rw [QueryCache.cacheQuery_of_ne _ _ ht] at h
                    exact Or.inr h

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Every logged entry is in the final cache with the same value (run from `∅`). -/
private theorem log_subset_cache {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α)
    {z : (α × QueryLog hashSpec) × hashSpec.QueryCache}
    (hz : z ∈ support (((simulateQ (compositeW hashSpec) oa).run).run ∅)) :
    ∀ e ∈ z.1.2, z.2 e.1 = some e.2 :=
  (mem_support_run_correspondence oa ∅ z hz).2.1

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Every final cache entry was logged (run from `∅`). -/
private theorem cache_subset_log {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α)
    {z : (α × QueryLog hashSpec) × hashSpec.QueryCache}
    (hz : z ∈ support (((simulateQ (compositeW hashSpec) oa).run).run ∅)) :
    ∀ (t : hashSpec.Domain) (u : hashSpec.Range t), z.2 t = some u →
      (⟨t, u⟩ : (s : hashSpec.Domain) × hashSpec.Range s) ∈ z.1.2 := fun t u hu =>
  ((mem_support_run_correspondence oa ∅ z hz).2.2 t u hu).resolve_right (by simp)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Each domain point has a unique logged value (run from `∅`). -/
private theorem log_unique {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α)
    {z : (α × QueryLog hashSpec) × hashSpec.QueryCache}
    (hz : z ∈ support (((simulateQ (compositeW hashSpec) oa).run).run ∅)) :
    ∀ (t : hashSpec.Domain) (u₁ u₂ : hashSpec.Range t),
      (⟨t, u₁⟩ : (s : hashSpec.Domain) × hashSpec.Range s) ∈ z.1.2 →
      (⟨t, u₂⟩ : (s : hashSpec.Domain) × hashSpec.Range s) ∈ z.1.2 → u₁ = u₂ := by
  intro t u₁ u₂ h₁ h₂
  have e₁ := log_subset_cache oa hz ⟨t, u₁⟩ h₁
  have e₂ := log_subset_cache oa hz ⟨t, u₂⟩ h₂
  exact Option.some.inj (e₁.symm.trans e₂)

/-- The cache-side pinning predicate: every cached record carrying the proof's
statement/commitment-list tags whose challenge–response pair verifies (at its own repetition
index) carries exactly the proof's challenge at that repetition. The `msg` field of the record
is not inspected, mirroring the extractor's log scan. -/
private def CachePinned (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) : Prop :=
  ∀ (r : FischlinROInput Stmt Commit Chal Resp ρ M) (u : Fin (2 ^ b)),
    cache r = some u → r.stmt = x → r.comList = (List.ofFn fun j => (π j).1) →
    σ.verify x (π r.rep).1 r.chal r.resp = true → r.chal = (π r.rep).2.1

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- **Log↔cache transfer.** Under the log↔cache correspondence, the extractor's scan misses
iff the cache-side pinning predicate holds. -/
private theorem fischlinFindWitness_eq_none_iff_cachePinned
    (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    {cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache}
    (hT1 : ∀ e ∈ log, cache e.1 = some e.2)
    (hT2 : ∀ (t : FischlinROInput Stmt Commit Chal Resp ρ M) (u : Fin (2 ^ b)),
      cache t = some u →
        (⟨t, u⟩ : (_s : FischlinROInput Stmt Commit Chal Resp ρ M) × Fin (2 ^ b)) ∈ log) :
    fischlinFindWitness σ ρ b M x π log = none ↔ CachePinned σ ρ b M x π cache := by
  constructor
  · -- scan-none → cache predicate, via cached ⇒ logged ⇒ pinning.
    intro hnone r u hru hstmt hcom hver
    exact chal_pinned_of_findWitness_none σ ρ b M hnone r.rep ⟨r, u⟩ (hT2 r u hru)
      hstmt hcom rfl hver
  · -- cache predicate → scan-none, via logged ⇒ cached ⇒ predicate applies.
    intro hpin
    rw [fischlinFindWitness, List.findSome?_eq_none_iff]
    intro i _hi
    rw [List.findSome?_eq_none_iff]
    intro e he
    dsimp only
    split
    · rename_i hcond
      exfalso
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨⟨hstmt, hcom⟩, hrep⟩, hver⟩, hne⟩ := hcond
      apply hne
      have hpinned := hpin e.1 e.2 (hT1 e he) hstmt hcom (by rw [hrep]; exact hver)
      rw [hpinned, hrep]
    · rfl

/-- The number of hash-value tuples `v : Fin ρ → Fin (2^b)` whose entries sum to at most `S`.

This counts the "small-sum" verifier-accepting hash assignments: a Fischlin proof is accepted only
when `∑ᵢ H(…,ωᵢ,respᵢ) ≤ S`, so this finite set is the target the prover's fresh random-oracle
answers must hit. It is bounded by `(S+1)·C(S+ρ-1, ρ-1)` (stars-and-bars). -/
def smallSumCount (ρ b S : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : Fin ρ → Fin (2 ^ b) => ∑ i, (v i).val ≤ S)).card

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Stars-and-bars bound.** The number of hash-value tuples summing to at most `S` is at most
`(S+1)·C(S+ρ-1, ρ-1)`.

Each `Fin (2^b)`-valued tuple injects into a `Fin ρ → ℕ` tuple with the same (bounded) sum; the
number of such natural tuples with sum exactly `s` is `C(s+ρ-1, ρ-1)`, which is monotone in `s`, so
summing over the `S+1` values `s = 0, …, S` gives the stated bound. -/
private lemma smallSumCount_le :
    smallSumCount ρ b S ≤ (S + 1) * Nat.choose (S + ρ - 1) (ρ - 1) := by
  classical
  -- Per-fiber count: tuples `Fin ρ → ℕ` summing to exactly `s` number `C(ρ+s-1, s)`.
  have hfiber : ∀ s : ℕ, (Finset.univ.piAntidiag s : Finset (Fin ρ → ℕ)).card
      = (ρ + s - 1).choose s := by
    intro s
    rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ, Finset.card_univ,
      Sym.card_sym_eq_choose, Fintype.card_fin]
  -- The `Fin.val` image of a small-sum hash tuple lands in the union of exact-sum natural tuples.
  set T : Finset (Fin ρ → ℕ) :=
    (Finset.range (S + 1)).biUnion (fun s => Finset.univ.piAntidiag s) with hT
  have hmap : (Finset.univ.filter (fun v : Fin ρ → Fin (2 ^ b) => ∑ i, (v i).val ≤ S)).image
      (fun v i => (v i).val) ⊆ T := by
    intro g hg
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨v, hv, rfl⟩ := hg
    simp only [hT, Finset.mem_biUnion, Finset.mem_range, Finset.mem_piAntidiag,
      Finset.mem_univ, implies_true, and_true]
    exact ⟨∑ i, (v i).val, by omega, rfl⟩
  -- The image has the same cardinality (the map `v ↦ Fin.val ∘ v` is injective).
  have hinj : Set.InjOn (fun v : Fin ρ → Fin (2 ^ b) => fun i => (v i).val)
      ↑(Finset.univ.filter (fun v : Fin ρ → Fin (2 ^ b) => ∑ i, (v i).val ≤ S)) := by
    intro v₁ _ v₂ _ h
    funext i
    exact Fin.val_injective (congrFun h i)
  rw [smallSumCount, ← Finset.card_image_of_injOn hinj]
  refine le_trans (Finset.card_le_card hmap) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  rw [Finset.sum_congr rfl (fun s _ => hfiber s)]
  -- Each fiber count is at most `C(S+ρ-1, ρ-1)`; there are `S+1` of them.
  refine le_trans (Finset.sum_le_card_nsmul _ _ ((S + ρ - 1).choose (ρ - 1)) (fun s hs => ?_)) ?_
  · rw [Finset.mem_range] at hs
    rcases Nat.eq_zero_or_pos ρ with hρ0 | hρpos
    · subst hρ0
      rcases Nat.eq_zero_or_pos s with rfl | hspos
      · simp
      · rw [Nat.choose_eq_zero_of_lt (by omega : 0 + s - 1 < s)]; exact Nat.zero_le _
    · have h1 : (ρ + s - 1).choose s = (ρ + s - 1).choose (ρ - 1) := by
        rw [← Nat.choose_symm (by omega)]; congr 1; omega
      rw [h1]; exact Nat.choose_le_choose _ (by omega)
  · rw [Finset.card_range, smul_eq_mul]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Each output tuple of `n` IID uniform draws is equally likely, with probability
`(Fintype.card α)⁻¹ ^ n`. -/
private lemma probOutput_mOfFn_uniformSample {α : Type} [SampleableType α] [Fintype α]
    (n : ℕ) (w : Fin n → α) :
    Pr[= w | Fin.mOfFn n (fun _ => ($ᵗ α : ProbComp α))]
      = (Fintype.card α : ℝ≥0∞)⁻¹ ^ n := by
  letI : DecidableEq α := Classical.decEq α
  induction n with
  | zero =>
    have hw : w = Fin.elim0 := funext fun i => i.elim0
    simp [Fin.mOfFn, hw]
  | succ n ih =>
    have hcond : ∀ (a : α) (r : Fin n → α),
        w = Fin.cons a r ↔ r = Fin.tail w ∧ a = w 0 := by
      intro a r
      constructor
      · rintro rfl
        simp
      · rintro ⟨rfl, rfl⟩
        exact (Fin.cons_self_tail w).symm
    rw [Fin.mOfFn]
    simp only [probOutput_bind_eq_tsum, probOutput_pure, ih, probOutput_uniformSample,
      hcond, ite_and, mul_ite, mul_one, mul_zero, tsum_ite_eq]
    rw [pow_succ']

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The probability that `n` IID uniform draws land in a (decidable) target set is exactly the
size of the target set over `(Fintype.card α) ^ n`. -/
private lemma probEvent_mOfFn_uniformSample {α : Type} [SampleableType α] [Fintype α]
    (n : ℕ) (p : (Fin n → α) → Prop) [DecidablePred p] :
    Pr[p | Fin.mOfFn n (fun _ => ($ᵗ α : ProbComp α))]
      = ((Finset.univ.filter p).card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ n := by
  rw [probEvent_eq_sum_filter_univ]
  simp only [probOutput_mOfFn_uniformSample, Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv, ENNReal.inv_pow]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Untouched slot completes with probability exactly `μ`.** The probability that `ρ` fresh
uniform `Fin (2^b)` draws sum to at most `S` is exactly `smallSumCount ρ b S / (2^b)^ρ`. -/
private lemma probEvent_sum_le_mOfFn_uniform :
    Pr[fun v => ∑ i, (v i).val ≤ S | Fin.mOfFn ρ (fun _ => $ᵗ (Fin (2 ^ b)))]
      = (smallSumCount ρ b S : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ ρ := by
  rw [probEvent_mOfFn_uniformSample, Fintype.card_fin, smallSumCount]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Conditional tail.** Given a revealed partial sum `T ≤ S`, the probability that `k` fresh
uniform draws bring the total to at most `S` is exactly `smallSumCount k b (S - T) / (2^b)^k`.
This is the per-slot completion probability with some coordinates already revealed, used by the
potential-function step of the knowledge-soundness bound. -/
private lemma probEvent_add_sum_le_mOfFn_uniform (k T : ℕ) (hT : T ≤ S) :
    Pr[fun v => T + ∑ i, (v i).val ≤ S | Fin.mOfFn k (fun _ => $ᵗ (Fin (2 ^ b)))]
      = (smallSumCount k b (S - T) : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ k := by
  have hfilter :
      (Finset.univ.filter (fun v : Fin k → Fin (2 ^ b) => T + ∑ i, (v i).val ≤ S))
        = (Finset.univ.filter (fun v : Fin k → Fin (2 ^ b) => ∑ i, (v i).val ≤ S - T)) :=
    Finset.filter_congr fun v _ => by omega
  rw [probEvent_mOfFn_uniformSample k
      (fun v : Fin k → Fin (2 ^ b) => T + ∑ i, (v i).val ≤ S),
    Fintype.card_fin, smallSumCount, hfilter]

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- **Mixed-cache query vector.** Simulating a `Fin.mOfFn` of random-oracle re-queries at
pairwise distinct records on a cache that stores exactly the `hits`-marked records: each hit
reads its cached value deterministically; each miss draws a fresh uniform `Fin (2^b)` (and
caches it, which never collides with the remaining records by injectivity). The output
distribution is the independent per-index product `pure (hit value) / $ᵗ Fin (2^b)`. The
all-hit special case is `run_mOfFn_query_hit`. -/
private lemma run'_mOfFn_query_mixed {β : Type} (n : ℕ)
    (records : Fin n → (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain)
    (hinj : Function.Injective records)
    (hits : Fin n → Option (Fin (2 ^ b)))
    (f : Fin n → Fin (2 ^ b) → β)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hcache : ∀ i, cache (records i) = hits i) :
    𝒟[(simulateQ (fischlinImpl ρ b M)
        (Fin.mOfFn n fun i => do
          let h ← HasQuery.query (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M) (records i)
          pure (f i h))).run' cache]
      = 𝒟[(fun u => fun i => f i (u i)) <$>
          Fin.mOfFn n fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)] := by
  induction n generalizing cache with
  | zero =>
      simp only [Fin.mOfFn, simulateQ_pure, StateT.run'_pure', map_pure]
      exact congrArg (fun z => 𝒟[(pure z : ProbComp (Fin 0 → β))]) (funext fun i => i.elim0)
  | succ n ih =>
      -- Tail step, shared by both branches: with head answer `x` and any cache `c` storing
      -- `hits ∘ Fin.succ` at the tail records, the tail simulation matches the model tail.
      have hstep : ∀ (x : Fin (2 ^ b))
          (c : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache),
          (∀ j : Fin n, c (records j.succ) = hits j.succ) →
          𝒟[(simulateQ (fischlinImpl ρ b M)
              (Fin.mOfFn n (fun j => do
                let h ← HasQuery.query (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)
                  (records j.succ)
                pure (f j.succ h)) >>= fun rest => pure (Fin.cons (f 0 x) rest))).run' c]
            = 𝒟[(fun u : Fin n → Fin (2 ^ b) => fun i : Fin (n + 1) =>
                  f i ((Fin.cons x u : Fin (n + 1) → Fin (2 ^ b)) i)) <$>
                Fin.mOfFn n fun j =>
                  match hits j.succ with
                  | some h => (pure h : ProbComp (Fin (2 ^ b)))
                  | none => $ᵗ Fin (2 ^ b)] := by
        intro x c hc
        rw [bind_pure_comp, simulateQ_map, StateT.run'_map']
        refine (evalDist_map_eq_of_evalDist_eq
          (ih (fun j => records j.succ)
            (fun j₁ j₂ hj => Fin.succ_injective n (hinj hj))
            (fun j => hits j.succ) (fun j => f j.succ) c hc)
          (Fin.cons (α := fun _ => β) (f 0 x))).trans ?_
        rw [Functor.map_map]
        refine congrArg evalDist (congrArg (· <$> _) ?_)
        funext u i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [Fin.cons_zero]
        · simp [Fin.cons_succ]
      -- Freshness of tail records is preserved by caching the head record (distinct records).
      have hcache' : ∀ (x : Fin (2 ^ b)) (j : Fin n),
          (cache.cacheQuery (records 0) x) (records j.succ) = hits j.succ := by
        intro x j
        have hne : records j.succ ≠ records 0 := fun hEq => Fin.succ_ne_zero j (hinj hEq)
        exact (QueryCache.cacheQuery_of_ne cache x hne).trans (hcache j.succ)
      cases hh : hits 0 with
      | some h0 =>
          have hc0 : cache (records 0) = some h0 := by rw [hcache 0, hh]
          simp only [Fin.mOfFn]
          rw [simulateQ_bind, StateT.run'_bind', simulateQ_bind,
            roSim.simulateQ_HasQuery_query, StateT.run_bind,
            QueryImpl.withCaching_run_some (so := uniformSampleImpl) hc0]
          simp only [pure_bind, simulateQ_pure, StateT.run_pure]
          rw [hstep h0 cache (fun j => hcache j.succ)]
          simp only [hh, pure_bind, bind_pure_comp, Functor.map_map]
      | none =>
          have hc0 : cache (records 0) = none := by rw [hcache 0, hh]
          simp only [Fin.mOfFn]
          rw [simulateQ_bind, StateT.run'_bind', simulateQ_bind,
            roSim.simulateQ_HasQuery_query, StateT.run_bind,
            QueryImpl.withCaching_run_none (so := uniformSampleImpl) hc0]
          simp only [uniformSampleImpl, bind_map_left, pure_bind, simulateQ_pure,
            StateT.run_pure, bind_assoc]
          simp only [hh, map_bind]
          rw [evalDist_bind, evalDist_bind]
          refine congrArg (𝒟[$ᵗ Fin (2 ^ b)] >>= ·) (funext fun x => ?_)
          rw [hstep x (cache.cacheQuery (records 0) x) (hcache' x)]
          simp only [map_pure, bind_pure_comp]

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- Same as `run'_mOfFn_query_mixed`, packaged with a pure verdict post-processing `V` of the
per-repetition results, matching the shape of `Fischlin`'s verifier. -/
private lemma run'_mOfFn_query_mixed_bind {β γ : Type} (n : ℕ)
    (records : Fin n → (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain)
    (hinj : Function.Injective records)
    (hits : Fin n → Option (Fin (2 ^ b)))
    (f : Fin n → Fin (2 ^ b) → β) (V : (Fin n → β) → γ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hcache : ∀ i, cache (records i) = hits i) :
    𝒟[(simulateQ (fischlinImpl ρ b M)
        ((Fin.mOfFn n fun i => do
          let h ← HasQuery.query (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M) (records i)
          pure (f i h)) >>= fun results => pure (V results))).run' cache]
      = 𝒟[(Fin.mOfFn n fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)) >>= fun u => pure (V fun i => f i (u i))] := by
  rw [bind_pure_comp V, simulateQ_map, StateT.run'_map']
  refine (evalDist_map_eq_of_evalDist_eq
    (run'_mOfFn_query_mixed ρ b M n records hinj hits f cache hcache) V).trans ?_
  rw [Functor.map_map, bind_pure_comp]

omit [SampleableType Chal] in
/-- **Mixed-cache verify run.** The Fischlin verifier's `run'` on a cache storing exactly the
`hits`-marked records: re-queries at hit records read the cached hash; misses sample fresh
uniforms. The `ρ` records are pairwise distinct (their `rep` field is the repetition index),
so within one verify run each record is queried exactly once. -/
private lemma verify_run'_mixed (pk : Stmt) (msg : M)
    (sig : Fin ρ → Commit × Chal × Resp)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hits : Fin ρ → Option (Fin (2 ^ b)))
    (hcache : ∀ i, cache (⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = hits i) :
    𝒟[(simulateQ (fischlinImpl ρ b M)
        ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).verify pk msg sig)).run' cache]
      = 𝒟[(Fin.mOfFn ρ fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)) >>= fun u =>
          pure (((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) &&
            decide ((List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 ≤ S))] := by
  refine (run'_mOfFn_query_mixed_bind ρ b M ρ
    (records := fun i =>
      ⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩)
    (hinj := fun i j h => congrArg FischlinROInput.rep h)
    (hits := hits)
    (f := fun i h => (σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2, h.val))
    (V := fun results => ((List.finRange ρ).all fun i => (results i).1) &&
      decide ((List.finRange ρ).foldl (fun acc i => acc + (results i).2) 0 ≤ S))
    cache hcache).trans ?_
  rfl

/-- The number of hash-value tuples extending the cached `hits` with total sum at most `S`.

Counts full tuples `v : Fin ρ → Fin (2^b)` that agree with every cached hit and have small sum;
each such tuple corresponds to exactly one assignment of the miss positions. For
`hits = fun _ => none` this is `smallSumCount ρ b S` (see `partialSmallSumCount_none`). -/
private def partialSmallSumCount (ρ b : ℕ) (hits : Fin ρ → Option (Fin (2 ^ b))) (S : ℕ) : ℕ :=
  (Finset.univ.filter fun v : Fin ρ → Fin (2 ^ b) =>
    (∀ i h, hits i = some h → v i = h) ∧ ∑ i, (v i).val ≤ S).card

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- With no cached hits, the partial small-sum count is the full small-sum count. -/
private lemma partialSmallSumCount_none :
    partialSmallSumCount ρ b (fun _ => none) S = smallSumCount ρ b S := by
  unfold partialSmallSumCount smallSumCount
  congr 1
  refine Finset.filter_congr fun v _ => ?_
  simp

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Output probabilities of an independent product `Fin.mOfFn` multiply coordinatewise. -/
private lemma probOutput_mOfFn {α : Type} [Finite α] (n : ℕ)
    (g : Fin n → ProbComp α) (v : Fin n → α) :
    Pr[= v | Fin.mOfFn n g] = ∏ i, Pr[= v i | g i] := by
  letI : Fintype α := Fintype.ofFinite α
  letI : DecidableEq α := Classical.decEq α
  induction n with
  | zero =>
      have hv : v = Fin.elim0 := funext fun i => i.elim0
      subst hv
      simp [Fin.mOfFn, probOutput_pure]
  | succ n ih =>
      simp only [Fin.mOfFn]
      rw [probOutput_bind_eq_sum_fintype]
      have hinner : ∀ a : α,
          Pr[= v | Fin.mOfFn n (fun i => g i.succ) >>= fun rest => pure (Fin.cons a rest)]
            = if a = v 0 then Pr[= Fin.tail v | Fin.mOfFn n fun i => g i.succ] else 0 := by
        intro a
        rw [probOutput_bind_eq_sum_fintype]
        have hiff : ∀ rest : Fin n → α,
            (v = Fin.cons a rest) ↔ (a = v 0 ∧ rest = Fin.tail v) := by
          intro rest
          constructor
          · intro hEq
            refine ⟨by rw [hEq, Fin.cons_zero], funext fun k => ?_⟩
            have := congrFun hEq k.succ
            rw [Fin.cons_succ] at this
            exact this.symm
          · rintro ⟨rfl, rfl⟩
            exact (Fin.cons_self_tail v).symm
        by_cases ha : a = v 0
        · rw [if_pos ha]
          subst ha
          simp only [probOutput_pure, hiff, true_and]
          simp [mul_ite]
        · rw [if_neg ha]
          refine Finset.sum_eq_zero fun rest _ => ?_
          rw [probOutput_pure, if_neg (fun hEq => ha ((hiff rest).mp hEq).1), mul_zero]
      simp only [hinner, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ (v 0)
        (fun a => Pr[= a | g 0] * Pr[= Fin.tail v | Fin.mOfFn n fun i => g i.succ]),
        if_pos (Finset.mem_univ _), ih, Fin.prod_univ_succ]
      rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Sum the per-repetition fold into a `Finset.sum`. -/
private lemma foldl_add_eq_sum (u : Fin ρ → Fin (2 ^ b)) :
    (List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 = ∑ i, (u i).val := by
  have hgen : ∀ (l : List (Fin ρ)) (init : ℕ),
      l.foldl (fun acc i => acc + (u i).val) init = init + (l.map fun i => (u i).val).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a l ihl => intro init; simp [ihl, Nat.add_assoc]
  rw [hgen, Nat.zero_add, ← List.ofFn_eq_map, List.sum_ofFn]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The product of per-coordinate hit/miss probabilities: zero unless `u` extends the hits,
in which case it is `(2^b)⁻¹` per miss. -/
private lemma prob_extend_hits (hits : Fin ρ → Option (Fin (2 ^ b))) (u : Fin ρ → Fin (2 ^ b)) :
    Pr[= u | Fin.mOfFn ρ fun i =>
        match hits i with
        | some h => (pure h : ProbComp (Fin (2 ^ b)))
        | none => $ᵗ Fin (2 ^ b)]
      = if ∀ i h, hits i = some h → u i = h
          then (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹ ^ (Finset.univ.filter fun i : Fin ρ => hits i = none).card
          else 0 := by
  rw [probOutput_mOfFn]
  by_cases hcomp : ∀ i h, hits i = some h → u i = h
  · rw [if_pos hcomp]
    have hfactor : ∀ i : Fin ρ,
        Pr[= u i | (match hits i with
          | some h => (pure h : ProbComp (Fin (2 ^ b)))
          | none => $ᵗ Fin (2 ^ b))]
          = if hits i = none then (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹ else 1 := by
      intro i
      cases hh : hits i with
      | none =>
          simp only [if_true]
          rw [probOutput_uniformSample, Fintype.card_fin]
      | some h =>
          have hu : u i = h := hcomp i h hh
          rw [probOutput_pure, if_pos hu, if_neg (Option.some_ne_none h)]
    rw [Finset.prod_congr rfl fun i _ => hfactor i, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one]
  · rw [if_neg hcomp]
    push Not at hcomp
    obtain ⟨i, h, hh, hne⟩ := hcomp
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [hh]
    rw [probOutput_pure, if_neg hne]

omit [SampleableType Chal] in
/-- **The ψ leaf (exact).** The probability that the Fischlin verifier accepts on a cache
storing exactly the `hits`-marked records is EXACTLY the σ-verification indicator times the
number of hit-compatible small-sum hash tuples over the miss-space volume `(2^b)^#misses`.

For `hits = fun _ => none` (the all-fresh case) the bound specializes to
`smallSumCount ρ b S / (2^b)^ρ` via `partialSmallSumCount_none`. -/
private lemma verify_probOutput_true_mixed (pk : Stmt) (msg : M)
    (sig : Fin ρ → Commit × Chal × Resp)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hits : Fin ρ → Option (Fin (2 ^ b)))
    (hcache : ∀ i, cache (⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = hits i) :
    Pr[= true | (simulateQ (fischlinImpl ρ b M)
        ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).verify pk msg sig)).run' cache]
      = (if ((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) = true
          then 1 else 0) *
        (partialSmallSumCount ρ b hits S : ℝ≥0∞) /
          (((2 ^ b : ℕ) : ℝ≥0∞)) ^ (Finset.univ.filter fun i : Fin ρ => hits i = none).card := by
  rw [probOutput_def, verify_run'_mixed σ hr ρ b S M pk msg sig cache hits hcache,
    ← probOutput_def, probOutput_bind_eq_sum_fintype]
  by_cases haV :
      ((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) = true
  · -- σ-verification accepted: the verdict is exactly the small-sum event.
    have hterm : ∀ u : Fin ρ → Fin (2 ^ b),
        Pr[= u | Fin.mOfFn ρ fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)] *
          Pr[= true | (pure
            (((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) &&
              decide ((List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 ≤ S)) :
            ProbComp Bool)]
          = if (∀ i h, hits i = some h → u i = h) ∧ ∑ i, (u i).val ≤ S
              then (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹ ^
                (Finset.univ.filter fun i : Fin ρ => hits i = none).card
              else 0 := by
      intro u
      rw [prob_extend_hits ρ b hits u, probOutput_pure, foldl_add_eq_sum ρ b u, haV]
      by_cases h3 : ∀ i h, hits i = some h → u i = h <;>
        by_cases h2 : (∑ i, (u i).val) ≤ S <;>
        simp [h3, h2]
    rw [Finset.sum_congr rfl fun u _ => hterm u, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, if_pos haV, one_mul, div_eq_mul_inv, ← ENNReal.inv_pow]
    rfl
  · -- σ-verification rejected: the verdict is constantly `false`.
    have haV' :
        ((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) = false :=
      Bool.eq_false_iff.mpr haV
    have hterm0 : ∀ u : Fin ρ → Fin (2 ^ b),
        Pr[= u | Fin.mOfFn ρ fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)] *
          Pr[= true | (pure
            (((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) &&
              decide ((List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 ≤ S)) :
            ProbComp Bool)]
          = 0 := by
      intro u
      rw [haV', probOutput_pure]
      simp
    rw [Finset.sum_congr rfl fun u _ => hterm0 u, Finset.sum_const_zero, if_neg haV, zero_mul,
      ENNReal.zero_div]

omit [SampleableType Chal] in
/-- **Accepting verify runs Σ-verify every repetition.** Any `(true, _)` outcome in the support
of the simulated Fischlin verifier implies the per-repetition Σ-protocol checks of the proof:
the Σ-verification bits inside `verify` are deterministic and independent of the oracle
answers, so a `false` bit forces acceptance probability zero. Discharges the `hverSupp`
hypothesis of `knowledgeSoundnessExp_bad_le_misses`. -/
private lemma ksVerify_true_support_allVerified (x : Stmt) (msg : M)
    (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (c' : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (h : (true, c') ∈ support (ksVerify σ hr ρ b S M x msg π cache)) :
    ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true := by
  intro i
  by_contra hne
  have hall : ((List.finRange ρ).all fun j => σ.verify x (π j).1 (π j).2.1 (π j).2.2) ≠ true :=
    fun hAll => hne (List.all_eq_true.mp hAll i (List.mem_finRange i))
  have hmem : true ∈ support ((simulateQ (fischlinImpl ρ b M)
      ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
        σ hr ρ b S M).verify x msg π)).run' cache) := by
    rw [StateT.run', support_map]
    exact ⟨(true, c'), h, rfl⟩
  have hpos := probOutput_pos _ _ hmem
  rw [verify_probOutput_true_mixed σ hr ρ b S M x msg π cache
    (fun j => cache (⟨x, msg, List.ofFn (fun k => (π k).1), j, (π j).2.1, (π j).2.2⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M)) (fun j => rfl),
    if_neg hall, zero_mul, ENNReal.zero_div] at hpos
  exact lt_irrefl 0 hpos

omit [SampleableType Chal] in
/-- `knowledgeSoundnessExp_bad_le_misses` with the verifier-determinism hypothesis discharged:
the knowledge-soundness bad event is bounded by the probability that the verifier accepts
while the extractor's scan misses. -/
private lemma knowledgeSoundnessExp_bad_le_misses' (hss : σ.SpeciallySound)
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M prover x msg] ≤
      Pr[fun out => out.2 = true ∧ fischlinFindWitness σ ρ b M x out.1.1 out.1.2 = none
        | ksSample σ hr ρ b S M prover x msg] :=
  knowledgeSoundnessExp_bad_le_misses σ hr ρ b S M hss prover x msg
    (fun π cache c' h => ksVerify_true_support_allVerified σ hr ρ b S M x msg π cache c' h)

/-- Number of unrevealed coordinates of a partial hash assignment. -/
private def missCard {ρ b : ℕ} (g : Fin ρ → Option (Fin (2 ^ b))) : ℕ :=
  (Finset.univ.filter fun i => g i = none).card

/-- Per-slot potential: the current conditional completion probability of a slot given the
revealed coordinates `g`. An untouched slot has potential exactly
`μ = smallSumCount ρ b S / (2^b)^ρ` (`slotPsi_none`), and revealing one fresh uniform
coordinate is a martingale step (`slotPsi_tower`). -/
private noncomputable def slotPsi (ρ b S : ℕ) (g : Fin ρ → Option (Fin (2 ^ b))) : ℝ≥0∞ :=
  (partialSmallSumCount ρ b g S : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ (missCard g)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Fiberwise decomposition: summing the extension counts over the possible values of a fresh
coordinate recovers the count for the unextended assignment (tower property at the level of
counting). -/
private lemma sum_partialSmallSumCount_update (g : Fin ρ → Option (Fin (2 ^ b))) (i : Fin ρ)
    (hi : g i = none) :
    ∑ u : Fin (2 ^ b), partialSmallSumCount ρ b (Function.update g i (some u)) S
      = partialSmallSumCount ρ b g S := by
  classical
  rw [partialSmallSumCount, Finset.card_eq_sum_card_fiberwise
    (f := fun v : Fin ρ → Fin (2 ^ b) => v i) (t := Finset.univ)
    (fun v _ => Finset.mem_univ _)]
  refine (Finset.sum_congr rfl fun u _ => ?_).symm
  rw [partialSmallSumCount, Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun v _ => ?_
  constructor
  · rintro ⟨⟨hext, hsum⟩, hvi⟩
    refine ⟨fun j h hj => ?_, hsum⟩
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self] at hj
      cases hj
      exact hvi
    · rw [Function.update_of_ne hji] at hj
      exact hext j h hj
  · rintro ⟨hext, hsum⟩
    have hvi : v i = u := hext i u (by rw [Function.update_self])
    refine ⟨⟨fun j h hj => ?_, hsum⟩, hvi⟩
    by_cases hji : j = i
    · subst hji; rw [hi] at hj; cases hj
    · exact hext j h (by rw [Function.update_of_ne hji]; exact hj)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Revealing a fresh coordinate decreases the miss count by exactly one. -/
private lemma missCard_update {ρ' b' : ℕ} (g : Fin ρ' → Option (Fin (2 ^ b'))) (i : Fin ρ')
    (u : Fin (2 ^ b')) (hi : g i = none) :
    missCard g = missCard (Function.update g i (some u)) + 1 := by
  classical
  unfold missCard
  have hset : (Finset.univ.filter fun j : Fin ρ' => Function.update g i (some u) j = none)
      = (Finset.univ.filter fun j : Fin ρ' => g j = none).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    by_cases hji : j = i
    · subst hji; simp [Function.update_self]
    · simp [hji]
  have hmem : i ∈ Finset.univ.filter fun j : Fin ρ' => g j = none :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  rw [hset, Finset.card_erase_of_mem hmem]
  have hpos : 0 < (Finset.univ.filter fun j : Fin ρ' => g j = none).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  omega

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Fresh slot = μ.** The potential of an untouched slot is exactly
`smallSumCount ρ b S / (2^b)^ρ`. -/
private lemma slotPsi_none :
    slotPsi ρ b S (fun _ => none)
      = (smallSumCount ρ b S : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ ρ := by
  unfold slotPsi
  rw [partialSmallSumCount_none ρ b S]
  congr 1
  simp [missCard]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Tower identity.** Averaging the slot potential over a uniformly revealed fresh
coordinate recovers the current slot potential: the per-slot potential is a martingale under
revealing one coordinate. With `g = fun _ => none` this is the open-step identity. -/
private lemma slotPsi_tower (g : Fin ρ → Option (Fin (2 ^ b))) (i : Fin ρ) (hi : g i = none) :
    (∑ u : Fin (2 ^ b), slotPsi ρ b S (Function.update g i (some u)))
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      = slotPsi ρ b S g := by
  classical
  have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
  have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmem : i ∈ Finset.univ.filter fun j : Fin ρ => g j = none :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have h1 : 1 ≤ missCard g := Finset.card_pos.mpr ⟨i, hmem⟩
  have hmiss : ∀ u : Fin (2 ^ b),
      missCard (Function.update g i (some u)) = missCard g - 1 := by
    intro u
    have := missCard_update g i u hi
    omega
  have hm : missCard g - 1 + 1 = missCard g := by omega
  unfold slotPsi
  simp only [hmiss, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_partialSmallSumCount_update ρ b S g i hi,
    mul_assoc,
    ← ENNReal.mul_inv (Or.inl (pow_ne_zero _ hD0)) (Or.inl (ENNReal.pow_ne_top hDtop)),
    ← pow_succ, hm]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Each extending tuple is determined by its values on the unrevealed coordinates, so the
partial count is at most `(2^b)^missCard g`. -/
private lemma partialSmallSumCount_le_pow (g : Fin ρ → Option (Fin (2 ^ b))) :
    partialSmallSumCount ρ b g S ≤ (2 ^ b) ^ missCard g := by
  classical
  have hle : partialSmallSumCount ρ b g S
      ≤ Fintype.card
          ({j // j ∈ Finset.univ.filter fun j : Fin ρ => g j = none} → Fin (2 ^ b)) := by
    rw [partialSmallSumCount, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun v j => v j.1) (fun v _ => Finset.mem_univ _) ?_
    intro v hv w hw hvw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hw
    funext j
    by_cases hj : g j = none
    · exact congrFun hvw ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    · obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hj
      rw [hv.1 j h hh, hw.1 j h hh]
  refine hle.trans (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, missCard]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The slot potential is a probability: `slotPsi ρ b S g ≤ 1`. -/
private lemma slotPsi_le_one (g : Fin ρ → Option (Fin (2 ^ b))) : slotPsi ρ b S g ≤ 1 := by
  unfold slotPsi
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  calc (partialSmallSumCount ρ b g S : ℝ≥0∞)
      ≤ (((2 ^ b) ^ missCard g : ℕ) : ℝ≥0∞) :=
        Nat.cast_le.mpr (partialSmallSumCount_le_pow ρ b S g)
    _ = ((2 ^ b : ℕ) : ℝ≥0∞) ^ missCard g := by push_cast; rfl

/-- Update one coordinate of one slot of a multi-slot state. -/
private def updateSlot {ρ' b' : ℕ} {K : Type} [DecidableEq K]
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) (k₀ : K) (i₀ : Fin ρ')
    (u : Fin (2 ^ b')) : K → Fin ρ' → Option (Fin (2 ^ b')) :=
  Function.update st k₀ (Function.update (st k₀) i₀ (some u))

/-- Multi-slot potential: the sum of the live slots' potentials over the touched keys. -/
private noncomputable def Phi (ρ b S : ℕ) {K : Type} (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b))) (dead : K → Prop) [DecidablePred dead] : ℝ≥0∞ :=
  ∑ k ∈ keys, if dead k then 0 else slotPsi ρ b S (st k)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma updateSlot_apply_ne {ρ' b' : ℕ} {K : Type} [DecidableEq K]
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) (k₀ : K) (i₀ : Fin ρ')
    (u : Fin (2 ^ b')) {k : K} (hk : k ≠ k₀) : updateSlot st k₀ i₀ u k = st k :=
  Function.update_of_ne hk _ _

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma updateSlot_apply_self {ρ' b' : ℕ} {K : Type} [DecidableEq K]
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) (k₀ : K) (i₀ : Fin ρ')
    (u : Fin (2 ^ b')) : updateSlot st k₀ i₀ u k₀ = Function.update (st k₀) i₀ (some u) :=
  Function.update_self _ _ _

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Extend = martingale.** Querying a fresh coordinate of a live, already-open slot leaves
the expected potential unchanged. -/
private lemma Phi_extend {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∈ keys) (hdead : ¬dead k₀) (hi : st k₀ i₀ = none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S keys (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      = Phi ρ b S keys st dead := by
  classical
  have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
  have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsplit : ∀ u : Fin (2 ^ b),
      Phi ρ b S keys (updateSlot st k₀ i₀ u) dead
        = slotPsi ρ b S (Function.update (st k₀) i₀ (some u))
          + ∑ k ∈ keys.erase k₀, if dead k then 0 else slotPsi ρ b S (st k) := by
    intro u
    rw [Phi, ← Finset.add_sum_erase _ _ hk, if_neg hdead, updateSlot_apply_self]
    congr 1
    refine Finset.sum_congr rfl fun k hk' => ?_
    rw [updateSlot_apply_ne st k₀ i₀ u (Finset.ne_of_mem_erase hk')]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, ENNReal.add_div, slotPsi_tower ρ b S (st k₀) i₀ hi,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
    ENNReal.mul_div_cancel_right hD0 hDtop, Phi, ← Finset.add_sum_erase _ _ hk,
    if_neg hdead]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Open, live case (equality).** Opening a fresh slot at a live key adds exactly
`μ = slotPsi ρ b S (fun _ => none)` to the expected potential. Requires the slot's state to be
untouched (`hfresh`) — exactly the invariant that untouched keys carry all-`none` states. -/
private lemma Phi_open_eq {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∉ keys) (hdead : ¬dead k₀) (hfresh : st k₀ = fun _ => none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      = Phi ρ b S keys st dead + slotPsi ρ b S (fun _ => none) := by
  classical
  have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
  have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsplit : ∀ u : Fin (2 ^ b),
      Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead
        = slotPsi ρ b S (Function.update (st k₀) i₀ (some u)) + Phi ρ b S keys st dead := by
    intro u
    rw [Phi, Finset.sum_insert hk, if_neg hdead, updateSlot_apply_self]
    congr 1
    refine Finset.sum_congr rfl fun k hk' => ?_
    rw [updateSlot_apply_ne st k₀ i₀ u (fun h => hk (h ▸ hk'))]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, ENNReal.add_div,
    slotPsi_tower ρ b S (st k₀) i₀ (by rw [hfresh]), hfresh,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
    ENNReal.mul_div_cancel_right hD0 hDtop, add_comm]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Open, general case (inequality).** Opening a fresh slot adds at most `μ` to the
expected potential (a dead key contributes nothing). -/
private lemma Phi_open_le {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∉ keys) (hfresh : st k₀ = fun _ => none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      ≤ Phi ρ b S keys st dead + slotPsi ρ b S (fun _ => none) := by
  classical
  by_cases hdead : dead k₀
  · have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
    have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hsplit : ∀ u : Fin (2 ^ b),
        Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead
          = Phi ρ b S keys st dead := by
      intro u
      rw [Phi, Finset.sum_insert hk, if_pos hdead, zero_add]
      refine Finset.sum_congr rfl fun k hk' => ?_
      rw [updateSlot_apply_ne st k₀ i₀ u (fun h => hk (h ▸ hk'))]
    simp only [hsplit]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
      ENNReal.mul_div_cancel_right hD0 hDtop]
    exact le_self_add
  · exact le_of_eq (Phi_open_eq ρ b S keys st dead k₀ i₀ hk hdead hfresh)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Kill.** Any step that only grows the dead set (state and keys unchanged) can only
decrease the potential. -/
private lemma Phi_mono_dead {K : Type} (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead dead' : K → Prop) [DecidablePred dead] [DecidablePred dead']
    (h : ∀ k, dead k → dead' k) :
    Phi ρ b S keys st dead' ≤ Phi ρ b S keys st dead := by
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : dead' k
  · simp [hk]
  · rw [if_neg hk, if_neg fun hd => hk (h k hd)]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Extend, deadness-agnostic (inequality).** Querying a fresh coordinate of an already-open
slot cannot increase the expected potential, whether or not the key is dead. -/
private lemma Phi_extend_le {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∈ keys) (hi : st k₀ i₀ = none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S keys (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      ≤ Phi ρ b S keys st dead := by
  classical
  by_cases hdead : dead k₀
  · have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
    have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hconst : ∀ u : Fin (2 ^ b),
        Phi ρ b S keys (updateSlot st k₀ i₀ u) dead = Phi ρ b S keys st dead := by
      intro u
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hkk : k = k₀
      · subst hkk; simp [hdead]
      · rw [updateSlot_apply_ne st k₀ i₀ u hkk]
    simp only [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
      ENNReal.mul_div_cancel_right hD0 hDtop]
  · exact le_of_eq (Phi_extend ρ b S keys st dead k₀ i₀ hk hdead hi)

/-- Expected payoff of a probabilistic computation against a nonnegative payoff function. -/
private noncomputable def EP {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, Pr[= x | mx] * f x

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma EP_pure {α : Type} (x : α) (f : α → ℝ≥0∞) :
    EP (pure x : ProbComp α) f = f x := by
  unfold EP
  rw [tsum_eq_single x]
  · rw [probOutput_pure_self, one_mul]
  · intro y hy
    rw [probOutput_pure_eq_indicator]
    simp [Set.indicator, hy]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma EP_bind {α β : Type} (mx : ProbComp α) (my : α → ProbComp β) (f : β → ℝ≥0∞) :
    EP (mx >>= my) f = ∑' x, Pr[= x | mx] * EP (my x) f := by
  unfold EP
  calc ∑' y, Pr[= y | mx >>= my] * f y
      = ∑' y, ∑' x, Pr[= x | mx] * Pr[= y | my x] * f y := by
        refine tsum_congr fun y => ?_
        rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right]
    _ = ∑' x, ∑' y, Pr[= x | mx] * Pr[= y | my x] * f y := ENNReal.tsum_comm
    _ = ∑' x, Pr[= x | mx] * ∑' y, Pr[= y | my x] * f y := by
        refine tsum_congr fun x => ?_
        simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma EP_bind_le_const {α β : Type} {mx : ProbComp α} {my : α → ProbComp β}
    {f : β → ℝ≥0∞} {C : ℝ≥0∞} (h : ∀ x, EP (my x) f ≤ C) :
    EP (mx >>= my) f ≤ C := by
  rw [EP_bind]
  calc ∑' x, Pr[= x | mx] * EP (my x) f
      ≤ ∑' x, Pr[= x | mx] * C := ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = (∑' x, Pr[= x | mx]) * C := ENNReal.tsum_mul_right
    _ ≤ 1 * C := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = C := one_mul C

/-- The lazy random-oracle simulation for a constant-range hash spec: forward `unifSpec`
queries, lazily sample-and-cache hash queries. Abstract analogue of `fischlinImpl`. -/
@[reducible] private noncomputable def roImpl (b' : ℕ) (T : Type) [DecidableEq T] :
    QueryImpl (unifSpec + (T →ₒ Fin (2 ^ b')))
      (StateT (T →ₒ Fin (2 ^ b')).QueryCache ProbComp) :=
  unifFwdImpl (T →ₒ Fin (2 ^ b')) + randomOracle (spec := T →ₒ Fin (2 ^ b'))

/-- **Coupling invariant** between the random-oracle cache and the ghost slot state of the
supermartingale induction.

* `cached_iff`: the slot state is exactly the cache transported along `(key, coord)`
  (well-defined when `(key, coord)` is injective).
* `untouched`: keys outside `keys` carry the all-`none` slot state. -/
private structure INV (ρ' b' : ℕ) {T K : Type} (key : T → K) (coord : T → Fin ρ')
    (cache : (T →ₒ Fin (2 ^ b')).QueryCache) (keys : Finset K)
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) : Prop where
  cached_iff : ∀ (t : T) (u : Fin (2 ^ b')),
    cache t = some u ↔ st (key t) (coord t) = some u
  untouched : ∀ k ∉ keys, st k = fun _ => none

namespace INV

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- A cache miss at `s` means the corresponding slot coordinate is unrevealed. -/
private lemma slot_none {ρ' b' : ℕ} {T K : Type} {key : T → K} {coord : T → Fin ρ'}
    {cache : (T →ₒ Fin (2 ^ b')).QueryCache} {keys : Finset K}
    {st : K → Fin ρ' → Option (Fin (2 ^ b'))}
    (hINV : INV ρ' b' key coord cache keys st) {s : T}
    (hs : cache s = none) : st (key s) (coord s) = none := by
  cases h : st (key s) (coord s) with
  | none => rfl
  | some u =>
      have hc := (hINV.cached_iff s u).mpr h
      rw [hs] at hc
      exact absurd hc (by simp)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Invariant preservation at a cache miss.** Caching a fresh record `s ↦ u` updates the
ghost state by writing `u` into slot `key s`, coordinate `coord s`, and marking `key s`
as touched. -/
private lemma cacheQuery {ρ' b' : ℕ} {T K : Type} [DecidableEq T] [DecidableEq K]
    {key : T → K} {coord : T → Fin ρ'}
    {cache : (T →ₒ Fin (2 ^ b')).QueryCache} {keys : Finset K}
    {st : K → Fin ρ' → Option (Fin (2 ^ b'))}
    (hinj : ∀ t₁ t₂, key t₁ = key t₂ → coord t₁ = coord t₂ → t₁ = t₂)
    (hINV : INV ρ' b' key coord cache keys st) (s : T) (hs : cache s = none)
    (u : Fin (2 ^ b')) :
    INV ρ' b' key coord (cache.cacheQuery s u) (insert (key s) keys)
      (updateSlot st (key s) (coord s) u) := by
  constructor
  · intro t' u'
    by_cases hts : t' = s
    · subst hts
      rw [QueryCache.cacheQuery_self, updateSlot_apply_self, Function.update_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hts]
      by_cases hkey : key t' = key s
      · have hcoord : coord t' ≠ coord s := fun hc => hts (hinj t' s hkey hc)
        rw [hkey, updateSlot_apply_self, Function.update_of_ne hcoord, ← hkey]
        exact hINV.cached_iff t' u'
      · rw [updateSlot_apply_ne st _ _ u hkey]
        exact hINV.cached_iff t' u'
  · intro k hk
    have hk1 : k ≠ key s := fun h => hk (h ▸ Finset.mem_insert_self _ _)
    have hk2 : k ∉ keys := fun h => hk (Finset.mem_insert_of_mem h)
    rw [updateSlot_apply_ne st _ _ u hk1]
    exact hINV.untouched k hk2

end INV

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **The main supermartingale induction.** Running `oa` under the lazy random-oracle
simulation from any cache coupled (via `INV`) to ghost state `(keys, st)`, the expected
terminal payoff is at most `q·μ + Φ + μ`, where `μ = slotPsi ρ b S (fun _ => none)` is the
untouched-slot potential, `Φ` is the current multi-slot potential, and `q` bounds the number
of hash queries.

* Each cache hit / `unifSpec` query leaves the potential unchanged.
* Each cache miss is a martingale step on an open slot (`Phi_extend_le`) or opens a fresh
  slot, paying `+μ` once per query (`Phi_open_le`) — telescoping into the `q·μ` term.
* The final `+μ` pays for the one extra slot the consumer's leaf may inspect (the proof's
  own `comList` slot, possibly never queried). -/
private theorem main_induction {T K : Type} [DecidableEq T]
    (key : T → K) (coord : T → Fin ρ)
    (hinj : ∀ t₁ t₂, key t₁ = key t₂ → coord t₁ = coord t₂ → t₁ = t₂)
    (dead : (T →ₒ Fin (2 ^ b)).QueryCache → K → Prop)
    [∀ c, DecidablePred (dead c)]
    (hdead_mono : ∀ c (t : T) (u : Fin (2 ^ b)) k, dead c k → dead (c.cacheQuery t u) k)
    {α : Type} (leaf : α → (T →ₒ Fin (2 ^ b)).QueryCache → ℝ≥0∞)
    (hleaf : ∀ (a : α) cache keys st, INV ρ b key coord cache keys st →
      leaf a cache ≤ Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none))
    (oa : OracleComp (unifSpec + (T →ₒ Fin (2 ^ b))) α) :
    ∀ (q : ℕ), IsQueryBoundP oa (· matches .inr _) q →
    ∀ cache keys st, INV ρ b key coord cache keys st →
    EP ((simulateQ (roImpl b T) oa).run cache) (fun z => leaf z.1 z.2)
      ≤ (q : ℝ≥0∞) * slotPsi ρ b S (fun _ => none)
        + Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro q _ cache keys st hINV
      rw [simulateQ_pure, StateT.run_pure, EP_pure]
      exact (hleaf x cache keys st hINV).trans (add_le_add le_add_self le_rfl)
  | query_bind t mx ih =>
      intro q hq cache keys st hINV
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hrest⟩ := hq
      rw [simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      rcases t with n | s
      · -- unifSpec query: forwarded, cache unchanged, budget unchanged
        have hbud : (if (Sum.inl n : ℕ ⊕ T) matches Sum.inr _ then q - 1 else q) = q :=
          if_neg (by simp)
        rw [hbud] at hrest
        change EP ((unifFwdImpl (T →ₒ Fin (2 ^ b)) n).run cache >>=
            fun p : unifSpec.Range n × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2) (fun z => leaf z.1 z.2) ≤ _
        have hrun : ((unifFwdImpl (T →ₒ Fin (2 ^ b)) n).run cache >>=
            fun p : unifSpec.Range n × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2)
            = (HasQuery.query (spec := unifSpec) (m := ProbComp) n) >>=
              fun a => (simulateQ (roImpl b T) (mx a)).run cache := by
          simp only [unifFwdImpl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
          rw [OracleComp.liftM_run_StateT, bind_assoc]
          simp only [pure_bind]
        rw [hrun]
        exact EP_bind_le_const fun a => ih a q (hrest a) cache keys st hINV
      · -- hash query
        have hp : ((Sum.inr s : ℕ ⊕ T) matches Sum.inr _) := rfl
        have hq0 : 0 < q := hcan.resolve_left (by simp)
        have hbud : (if (Sum.inr s : ℕ ⊕ T) matches Sum.inr _ then q - 1 else q) = q - 1 :=
          if_pos hp
        rw [hbud] at hrest
        have hμ : ((q - 1 : ℕ) : ℝ≥0∞) * slotPsi ρ b S (fun _ => none)
            + slotPsi ρ b S (fun _ => none)
            = (q : ℝ≥0∞) * slotPsi ρ b S (fun _ => none) := by
          have hcast : ((q - 1 : ℕ) : ℝ≥0∞) + 1 = (q : ℝ≥0∞) := by
            exact_mod_cast Nat.succ_pred_eq_of_pos hq0
          rw [← hcast, add_mul, one_mul]
        change EP ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
            fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2) (fun z => leaf z.1 z.2) ≤ _
        rcases hc : cache s with _ | u
        · -- cache miss: fresh uniform sample, potential step
          have hrun : ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
              fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
                (simulateQ (roImpl b T) (mx p.1)).run p.2)
              = ($ᵗ Fin (2 ^ b)) >>= fun u =>
                  (simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u) := by
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hc, bind_map_left]
            rfl
          rw [hrun]
          set μ := slotPsi ρ b S (fun _ => none) with hμdef
          set k₀ := key s with hk₀
          set i₀ := coord s with hi₀
          have hIH : ∀ u : Fin (2 ^ b),
              EP ((simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u))
                  (fun z => leaf z.1 z.2)
                ≤ ((q - 1 : ℕ) : ℝ≥0∞) * μ
                  + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache) + μ := by
            intro u
            refine (ih u (q - 1) (hrest u) (cache.cacheQuery s u) (insert k₀ keys)
              (updateSlot st k₀ i₀ u) (hINV.cacheQuery hinj s hc u)).trans ?_
            exact add_le_add (add_le_add le_rfl
              (Phi_mono_dead ρ b S _ _ _ _ (hdead_mono cache s u))) le_rfl
          have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
            Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
          have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
          rw [EP_bind]
          calc ∑' u, Pr[= u | $ᵗ Fin (2 ^ b)]
                  * EP ((simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u))
                      (fun z => leaf z.1 z.2)
              ≤ ∑' u, Pr[= u | $ᵗ Fin (2 ^ b)]
                  * (((q - 1 : ℕ) : ℝ≥0∞) * μ
                    + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache) + μ) :=
                ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (hIH u)
            _ = ∑ u : Fin (2 ^ b), ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
                  * (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ
                    + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache)) := by
                rw [tsum_fintype]
                refine Finset.sum_congr rfl fun u _ => ?_
                rw [probOutput_uniformSample, Fintype.card_fin, add_right_comm]
            _ = ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
                  * ((2 ^ b) • (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ)
                    + ∑ u : Fin (2 ^ b),
                        Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache)) := by
                rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
                  Finset.card_univ, Fintype.card_fin]
            _ = (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ)
                  + (∑ u : Fin (2 ^ b),
                      Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache))
                    / ((2 ^ b : ℕ) : ℝ≥0∞) := by
                rw [mul_add, nsmul_eq_mul, ← mul_assoc,
                  ENNReal.inv_mul_cancel hD0 hDtop, one_mul, mul_comm
                    (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹, ← div_eq_mul_inv]
            _ ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := ?_
          rw [hμ]
          by_cases hkmem : k₀ ∈ keys
          · -- extend an already-open slot: martingale step
            rw [Finset.insert_eq_self.mpr hkmem]
            have hstep := Phi_extend_le ρ b S keys st (dead cache) k₀ i₀ hkmem
              (hINV.slot_none hc)
            calc (q : ℝ≥0∞) * μ + (∑ u : Fin (2 ^ b),
                    Phi ρ b S keys (updateSlot st k₀ i₀ u) (dead cache))
                    / ((2 ^ b : ℕ) : ℝ≥0∞)
                ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) :=
                  add_le_add le_rfl hstep
              _ ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := le_self_add
          · -- open a fresh slot: pay one μ
            have hstep := Phi_open_le ρ b S keys st (dead cache) k₀ i₀ hkmem
              (hINV.untouched k₀ hkmem)
            calc (q : ℝ≥0∞) * μ + (∑ u : Fin (2 ^ b),
                    Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache))
                    / ((2 ^ b : ℕ) : ℝ≥0∞)
                ≤ (q : ℝ≥0∞) * μ + (Phi ρ b S keys st (dead cache) + μ) :=
                  add_le_add le_rfl hstep
              _ = (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := by
                  rw [add_assoc]
        · -- cache hit: no sampling, state unchanged, budget decremented
          have hrun : ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
              fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
                (simulateQ (roImpl b T) (mx p.1)).run p.2)
              = (simulateQ (roImpl b T) (mx u)).run cache := by
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hc, pure_bind]
          rw [hrun]
          refine (ih u (q - 1) (hrest u) cache keys st hINV).trans ?_
          exact add_le_add (add_le_add (mul_le_mul'
            (Nat.cast_le.mpr (Nat.sub_le q 1)) le_rfl) le_rfl) le_rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Initial-state specialization.** From the empty cache with no touched keys (`Φ = 0`),
the expected leaf payoff telescopes to exactly `(q + 1) · μ` — the
`(Q + 1) · smallSumCount / (2^b)^ρ` headline constant of `knowledgeSoundness_badEvent_le`
(via `slotPsi_none`). -/
private theorem main_induction_init {T K : Type} [DecidableEq T]
    (key : T → K) (coord : T → Fin ρ)
    (hinj : ∀ t₁ t₂, key t₁ = key t₂ → coord t₁ = coord t₂ → t₁ = t₂)
    (dead : (T →ₒ Fin (2 ^ b)).QueryCache → K → Prop)
    [∀ c, DecidablePred (dead c)]
    (hdead_mono : ∀ c (t : T) (u : Fin (2 ^ b)) k, dead c k → dead (c.cacheQuery t u) k)
    {α : Type} (leaf : α → (T →ₒ Fin (2 ^ b)).QueryCache → ℝ≥0∞)
    (hleaf : ∀ (a : α) cache keys st, INV ρ b key coord cache keys st →
      leaf a cache ≤ Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none))
    (oa : OracleComp (unifSpec + (T →ₒ Fin (2 ^ b))) α)
    (q : ℕ) (hq : IsQueryBoundP oa (· matches .inr _) q) :
    EP ((simulateQ (roImpl b T) oa).run ∅) (fun z => leaf z.1 z.2)
      ≤ ((q + 1 : ℕ) : ℝ≥0∞) * slotPsi ρ b S (fun _ => none) := by
  classical
  have hINV : INV ρ b key coord ∅ (∅ : Finset K) (fun _ _ => none) :=
    ⟨fun t u => by rw [QueryCache.empty_apply], fun _ _ => rfl⟩
  refine (main_induction ρ b S key coord hinj dead hdead_mono leaf hleaf oa q hq
    ∅ ∅ (fun _ _ => none) hINV).trans (le_of_eq ?_)
  rw [Phi, Finset.sum_empty, add_zero, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- Weakened coupling invariant for the multi-record setting, relative to the deadness
predicate `dd` of the current cache. Unlike `INV`, the cache→state direction is restricted
to relevant records at live slots, and the state→cache direction only requires *some*
relevant record witnessing each revealed cell. -/
private structure INV' (ρ' b' : ℕ) {T K : Type} (relevant : T → Prop) (key : T → K)
    (coord : T → Fin ρ') (dd : K → Prop)
    (cache : (T →ₒ Fin (2 ^ b')).QueryCache) (keys : Finset K)
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) : Prop where
  cached_imp : ∀ (t : T) (u : Fin (2 ^ b')), relevant t → ¬ dd (key t) →
    cache t = some u → st (key t) (coord t) = some u
  revealed_has_record : ∀ (k : K) (i : Fin ρ') (u : Fin (2 ^ b')), ¬ dd k →
    st k i = some u → ∃ t, relevant t ∧ key t = k ∧ coord t = i ∧ cache t = some u
  untouched : ∀ k ∉ keys, st k = fun _ => none

namespace INV'

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Inert step.** Caching a record that is irrelevant, or whose slot is (or becomes)
dead, preserves `INV'` with the ghost state unchanged. Covers the irrelevant, already-dead,
and kill cases of the generalized induction. -/
private lemma cacheQuery_inert {ρ' b' : ℕ} {T K : Type} [DecidableEq T]
    {relevant : T → Prop} {key : T → K} {coord : T → Fin ρ'} {dd dd' : K → Prop}
    {cache : (T →ₒ Fin (2 ^ b')).QueryCache} {keys : Finset K}
    {st : K → Fin ρ' → Option (Fin (2 ^ b'))}
    (hINV : INV' ρ' b' relevant key coord dd cache keys st)
    (hmono : ∀ k, dd k → dd' k)
    (s : T) (hs : cache s = none) (u : Fin (2 ^ b'))
    (hinert : relevant s → dd' (key s)) :
    INV' ρ' b' relevant key coord dd' (cache.cacheQuery s u) keys st := by
  constructor
  · intro t u₀ hrel hlive hcache
    by_cases hts : t = s
    · subst hts
      exact absurd (hinert hrel) hlive
    · rw [QueryCache.cacheQuery_of_ne _ _ hts] at hcache
      exact hINV.cached_imp t u₀ hrel (fun hd => hlive (hmono _ hd)) hcache
  · intro k i u₀ hlive hst
    obtain ⟨t, htrel, htk, hti, htc⟩ :=
      hINV.revealed_has_record k i u₀ (fun hd => hlive (hmono _ hd)) hst
    have hts : t ≠ s := fun h => by rw [h, hs] at htc; simp at htc
    exact ⟨t, htrel, htk, hti, by
      rw [QueryCache.cacheQuery_of_ne _ _ hts]; exact htc⟩
  · exact hINV.untouched

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Reveal step.** Caching a relevant record at a fresh cell updates the ghost state by
writing the sampled value into the cell and marking the key as touched, preserving `INV'`. -/
private lemma cacheQuery_reveal {ρ' b' : ℕ} {T K : Type} [DecidableEq T] [DecidableEq K]
    {relevant : T → Prop} {key : T → K} {coord : T → Fin ρ'} {dd dd' : K → Prop}
    {cache : (T →ₒ Fin (2 ^ b')).QueryCache} {keys : Finset K}
    {st : K → Fin ρ' → Option (Fin (2 ^ b'))}
    (hINV : INV' ρ' b' relevant key coord dd cache keys st)
    (hmono : ∀ k, dd k → dd' k)
    (s : T) (hs : cache s = none) (hrel : relevant s)
    (hstn : st (key s) (coord s) = none) (u : Fin (2 ^ b')) :
    INV' ρ' b' relevant key coord dd' (cache.cacheQuery s u) (insert (key s) keys)
      (updateSlot st (key s) (coord s) u) := by
  constructor
  · intro t u₀ htrel hlive hcache
    by_cases hts : t = s
    · subst hts
      rw [QueryCache.cacheQuery_self] at hcache
      rw [updateSlot_apply_self, Function.update_self]
      exact hcache
    · rw [QueryCache.cacheQuery_of_ne _ _ hts] at hcache
      have hold := hINV.cached_imp t u₀ htrel (fun hd => hlive (hmono _ hd)) hcache
      by_cases hkey : key t = key s
      · by_cases hcoord : coord t = coord s
        · exfalso
          rw [hkey, hcoord, hstn] at hold
          simp at hold
        · rw [hkey, updateSlot_apply_self, Function.update_of_ne hcoord, ← hkey]
          exact hold
      · rw [updateSlot_apply_ne st _ _ u hkey]
        exact hold
  · intro k i u₀ hlive hst
    by_cases hk : k = key s
    · subst hk
      by_cases hi : i = coord s
      · subst hi
        rw [updateSlot_apply_self, Function.update_self] at hst
        refine ⟨s, hrel, rfl, rfl, ?_⟩
        rw [QueryCache.cacheQuery_self]
        exact hst
      · rw [updateSlot_apply_self, Function.update_of_ne hi] at hst
        obtain ⟨t, htrel, htk, hti, htc⟩ :=
          hINV.revealed_has_record (key s) i u₀ (fun hd => hlive (hmono _ hd)) hst
        have hts : t ≠ s := fun h => hi (by rw [← hti, h])
        exact ⟨t, htrel, htk, hti, by
          rw [QueryCache.cacheQuery_of_ne _ _ hts]; exact htc⟩
    · rw [updateSlot_apply_ne st _ _ u hk] at hst
      obtain ⟨t, htrel, htk, hti, htc⟩ :=
        hINV.revealed_has_record k i u₀ (fun hd => hlive (hmono _ hd)) hst
      have hts : t ≠ s := fun h => hk (by rw [← htk, h])
      exact ⟨t, htrel, htk, hti, by
        rw [QueryCache.cacheQuery_of_ne _ _ hts]; exact htc⟩
  · intro k hk
    have hk1 : k ≠ key s := fun h => hk (h ▸ Finset.mem_insert_self _ _)
    have hk2 : k ∉ keys := fun h => hk (Finset.mem_insert_of_mem h)
    rw [updateSlot_apply_ne st _ _ u hk1]
    exact hINV.untouched k hk2

end INV'

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **The generalized supermartingale induction (multi-record cells).** As
`main_induction`, but instead of joint injectivity of `(key, coord)`, only the *relevant*
records matter, and within a cell relevant records are separated by an abstract challenge
tag `chalOf` (`hcell`). Caching a second relevant record at an already-revealed cell kills
the slot (`hdead_kill`); all other relevant/live cache misses are martingale reveal steps;
irrelevant and dead-slot misses leave the potential unchanged. The bound is unchanged:
`q·μ + Φ + μ`. -/
private theorem main_induction_gen {T K C : Type} [DecidableEq T]
    (relevant : T → Prop)
    (key : T → K) (coord : T → Fin ρ) (chalOf : T → C)
    (hcell : ∀ t₁ t₂, relevant t₁ → relevant t₂ → key t₁ = key t₂ → coord t₁ = coord t₂ →
      chalOf t₁ = chalOf t₂ → t₁ = t₂)
    (dead : (T →ₒ Fin (2 ^ b)).QueryCache → K → Prop)
    [∀ c, DecidablePred (dead c)]
    (hdead_mono : ∀ c (t : T) (u : Fin (2 ^ b)) k, dead c k → dead (c.cacheQuery t u) k)
    (hdead_kill : ∀ (cache : (T →ₒ Fin (2 ^ b)).QueryCache) (t t' : T) (u u' : Fin (2 ^ b)),
      relevant t → relevant t' → key t = key t' → coord t = coord t' →
      chalOf t ≠ chalOf t' → cache t' = some u' → dead (cache.cacheQuery t u) (key t))
    {α : Type} (leaf : α → (T →ₒ Fin (2 ^ b)).QueryCache → ℝ≥0∞)
    (hleaf : ∀ (a : α) cache keys st,
      INV' ρ b relevant key coord (dead cache) cache keys st →
      leaf a cache ≤ Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none))
    (oa : OracleComp (unifSpec + (T →ₒ Fin (2 ^ b))) α) :
    ∀ (q : ℕ), IsQueryBoundP oa (· matches .inr _) q →
    ∀ cache keys st, INV' ρ b relevant key coord (dead cache) cache keys st →
    EP ((simulateQ (roImpl b T) oa).run cache) (fun z => leaf z.1 z.2)
      ≤ (q : ℝ≥0∞) * slotPsi ρ b S (fun _ => none)
        + Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro q _ cache keys st hINV
      rw [simulateQ_pure, StateT.run_pure, EP_pure]
      exact (hleaf x cache keys st hINV).trans (add_le_add le_add_self le_rfl)
  | query_bind t mx ih =>
      intro q hq cache keys st hINV
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hrest⟩ := hq
      rw [simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      rcases t with n | s
      · -- unifSpec query: forwarded, cache unchanged, budget unchanged
        have hbud : (if (Sum.inl n : ℕ ⊕ T) matches Sum.inr _ then q - 1 else q) = q :=
          if_neg (by simp)
        rw [hbud] at hrest
        change EP ((unifFwdImpl (T →ₒ Fin (2 ^ b)) n).run cache >>=
            fun p : unifSpec.Range n × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2) (fun z => leaf z.1 z.2) ≤ _
        have hrun : ((unifFwdImpl (T →ₒ Fin (2 ^ b)) n).run cache >>=
            fun p : unifSpec.Range n × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2)
            = (HasQuery.query (spec := unifSpec) (m := ProbComp) n) >>=
              fun a => (simulateQ (roImpl b T) (mx a)).run cache := by
          simp only [unifFwdImpl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
          rw [OracleComp.liftM_run_StateT, bind_assoc]
          simp only [pure_bind]
        rw [hrun]
        exact EP_bind_le_const fun a => ih a q (hrest a) cache keys st hINV
      · -- hash query
        have hp : ((Sum.inr s : ℕ ⊕ T) matches Sum.inr _) := rfl
        have hq0 : 0 < q := hcan.resolve_left (by simp)
        have hbud : (if (Sum.inr s : ℕ ⊕ T) matches Sum.inr _ then q - 1 else q) = q - 1 :=
          if_pos hp
        rw [hbud] at hrest
        have hμ : ((q - 1 : ℕ) : ℝ≥0∞) * slotPsi ρ b S (fun _ => none)
            + slotPsi ρ b S (fun _ => none)
            = (q : ℝ≥0∞) * slotPsi ρ b S (fun _ => none) := by
          have hcast : ((q - 1 : ℕ) : ℝ≥0∞) + 1 = (q : ℝ≥0∞) := by
            exact_mod_cast Nat.succ_pred_eq_of_pos hq0
          rw [← hcast, add_mul, one_mul]
        change EP ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
            fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2) (fun z => leaf z.1 z.2) ≤ _
        rcases hc : cache s with _ | u
        · -- cache miss: fresh uniform sample
          have hrun : ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
              fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
                (simulateQ (roImpl b T) (mx p.1)).run p.2)
              = ($ᵗ Fin (2 ^ b)) >>= fun u =>
                  (simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u) := by
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hc, bind_map_left]
            rfl
          rw [hrun]
          by_cases hlive : relevant s ∧ ¬ dead cache (key s) ∧ st (key s) (coord s) = none
          · -- REVEAL: relevant record at a fresh cell of a live slot — martingale step
            obtain ⟨hrel, hdd, hstn⟩ := hlive
            set μ := slotPsi ρ b S (fun _ => none) with hμdef
            set k₀ := key s with hk₀
            set i₀ := coord s with hi₀
            have hIH : ∀ u : Fin (2 ^ b),
                EP ((simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u))
                    (fun z => leaf z.1 z.2)
                  ≤ ((q - 1 : ℕ) : ℝ≥0∞) * μ
                    + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache) + μ := by
              intro u
              refine (ih u (q - 1) (hrest u) (cache.cacheQuery s u) (insert k₀ keys)
                (updateSlot st k₀ i₀ u)
                (hINV.cacheQuery_reveal (hdead_mono cache s u) s hc hrel hstn u)).trans ?_
              exact add_le_add (add_le_add le_rfl
                (Phi_mono_dead ρ b S _ _ _ _ (hdead_mono cache s u))) le_rfl
            have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
              Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
            have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
            rw [EP_bind]
            calc ∑' u, Pr[= u | $ᵗ Fin (2 ^ b)]
                    * EP ((simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u))
                        (fun z => leaf z.1 z.2)
                ≤ ∑' u, Pr[= u | $ᵗ Fin (2 ^ b)]
                    * (((q - 1 : ℕ) : ℝ≥0∞) * μ
                      + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache) + μ) :=
                  ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (hIH u)
              _ = ∑ u : Fin (2 ^ b), ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
                    * (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ
                      + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache)) := by
                  rw [tsum_fintype]
                  refine Finset.sum_congr rfl fun u _ => ?_
                  rw [probOutput_uniformSample, Fintype.card_fin, add_right_comm]
              _ = ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
                    * ((2 ^ b) • (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ)
                      + ∑ u : Fin (2 ^ b),
                          Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache)) := by
                  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
                    Finset.card_univ, Fintype.card_fin]
              _ = (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ)
                    + (∑ u : Fin (2 ^ b),
                        Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache))
                      / ((2 ^ b : ℕ) : ℝ≥0∞) := by
                  rw [mul_add, nsmul_eq_mul, ← mul_assoc,
                    ENNReal.inv_mul_cancel hD0 hDtop, one_mul, mul_comm
                      (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹, ← div_eq_mul_inv]
              _ ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := ?_
            rw [hμ]
            by_cases hkmem : k₀ ∈ keys
            · -- extend an already-open slot: martingale step
              rw [show insert k₀ keys = keys from Finset.insert_eq_self.mpr hkmem]
              have hstep := Phi_extend_le ρ b S keys st (dead cache) k₀ i₀ hkmem hstn
              calc (q : ℝ≥0∞) * μ + (∑ u : Fin (2 ^ b),
                      Phi ρ b S keys (updateSlot st k₀ i₀ u) (dead cache))
                      / ((2 ^ b : ℕ) : ℝ≥0∞)
                  ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) :=
                    add_le_add le_rfl hstep
                _ ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := le_self_add
            · -- open a fresh slot: pay one μ
              have hstep := Phi_open_le ρ b S keys st (dead cache) k₀ i₀ hkmem
                (hINV.untouched k₀ hkmem)
              calc (q : ℝ≥0∞) * μ + (∑ u : Fin (2 ^ b),
                      Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache))
                      / ((2 ^ b : ℕ) : ℝ≥0∞)
                  ≤ (q : ℝ≥0∞) * μ + (Phi ρ b S keys st (dead cache) + μ) :=
                    add_le_add le_rfl hstep
                _ = (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := by
                    rw [add_assoc]
          · -- INERT: irrelevant record, dead slot, or kill — ghost state unchanged,
            -- potential non-increasing, average over the sampled value is trivial.
            have hinert : ∀ u : Fin (2 ^ b),
                relevant s → dead (cache.cacheQuery s u) (key s) := by
              intro u hrel
              by_cases hdd : dead cache (key s)
              · exact hdead_mono cache s u _ hdd
              · rcases hcv : st (key s) (coord s) with _ | u'
                · exact absurd ⟨hrel, hdd, hcv⟩ hlive
                · -- KILL: the cell was revealed by an earlier relevant record `t'`;
                  -- by `hcell` its challenge tag differs, so `hdead_kill` applies.
                  obtain ⟨t', ht'rel, ht'k, ht'i, ht'c⟩ :=
                    hINV.revealed_has_record (key s) (coord s) u' hdd hcv
                  have hts : t' ≠ s := fun h => by
                    rw [h, hc] at ht'c; simp at ht'c
                  have hchal : chalOf s ≠ chalOf t' := fun h =>
                    hts.symm (hcell s t' hrel ht'rel ht'k.symm ht'i.symm h)
                  exact hdead_kill cache s t' u u' hrel ht'rel ht'k.symm ht'i.symm
                    hchal ht'c
            refine EP_bind_le_const fun u => ?_
            refine (ih u (q - 1) (hrest u) (cache.cacheQuery s u) keys st
              (hINV.cacheQuery_inert (hdead_mono cache s u) s hc u (hinert u))).trans ?_
            exact add_le_add (add_le_add
              (mul_le_mul' (Nat.cast_le.mpr (Nat.sub_le q 1)) le_rfl)
              (Phi_mono_dead ρ b S _ _ _ _ (hdead_mono cache s u))) le_rfl
        · -- cache hit: no sampling, state unchanged, budget decremented
          have hrun : ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
              fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
                (simulateQ (roImpl b T) (mx p.1)).run p.2)
              = (simulateQ (roImpl b T) (mx u)).run cache := by
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hc, pure_bind]
          rw [hrun]
          refine (ih u (q - 1) (hrest u) cache keys st hINV).trans ?_
          exact add_le_add (add_le_add (mul_le_mul'
            (Nat.cast_le.mpr (Nat.sub_le q 1)) le_rfl) le_rfl) le_rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Initial-state specialization of `main_induction_gen`: from the empty cache the
expected leaf payoff is at most `(q + 1)·μ`. -/
private theorem main_induction_gen_init {T K C : Type} [DecidableEq T]
    (relevant : T → Prop)
    (key : T → K) (coord : T → Fin ρ) (chalOf : T → C)
    (hcell : ∀ t₁ t₂, relevant t₁ → relevant t₂ → key t₁ = key t₂ → coord t₁ = coord t₂ →
      chalOf t₁ = chalOf t₂ → t₁ = t₂)
    (dead : (T →ₒ Fin (2 ^ b)).QueryCache → K → Prop)
    [∀ c, DecidablePred (dead c)]
    (hdead_mono : ∀ c (t : T) (u : Fin (2 ^ b)) k, dead c k → dead (c.cacheQuery t u) k)
    (hdead_kill : ∀ (cache : (T →ₒ Fin (2 ^ b)).QueryCache) (t t' : T) (u u' : Fin (2 ^ b)),
      relevant t → relevant t' → key t = key t' → coord t = coord t' →
      chalOf t ≠ chalOf t' → cache t' = some u' → dead (cache.cacheQuery t u) (key t))
    {α : Type} (leaf : α → (T →ₒ Fin (2 ^ b)).QueryCache → ℝ≥0∞)
    (hleaf : ∀ (a : α) cache keys st,
      INV' ρ b relevant key coord (dead cache) cache keys st →
      leaf a cache ≤ Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none))
    (oa : OracleComp (unifSpec + (T →ₒ Fin (2 ^ b))) α)
    (q : ℕ) (hq : IsQueryBoundP oa (· matches .inr _) q) :
    EP ((simulateQ (roImpl b T) oa).run ∅) (fun z => leaf z.1 z.2)
      ≤ ((q + 1 : ℕ) : ℝ≥0∞) * slotPsi ρ b S (fun _ => none) := by
  classical
  have hINV : INV' ρ b relevant key coord (dead ∅) ∅ (∅ : Finset K)
      (fun _ _ => none) := by
    refine ⟨fun t u _ _ hcc => ?_, fun k i u _ hst => ?_, fun _ _ => rfl⟩
    · rw [QueryCache.empty_apply] at hcc
      simp at hcc
    · simp at hst
  refine (main_induction_gen ρ b S relevant key coord chalOf hcell dead hdead_mono
    hdead_kill leaf hleaf oa q hq ∅ ∅ (fun _ _ => none) hINV).trans (le_of_eq ?_)
  rw [Phi, Finset.sum_empty, add_zero, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

omit [SampleableType Chal] in
/-- **Online-extraction reduction (Fischlin 2005, Theorem 2 core).** The Fischlin
knowledge-soundness bad event — the verifier accepts the cheating prover's proof yet the online
extractor recovers no
valid witness — occurs with probability at most `(Q+1)` (one slot per logged hash query, plus the
trivial slot) times the chance that a fresh tuple of `ρ` independent random-oracle answers lands in
the small-sum target set, namely `smallSumCount ρ b S / (2^b)^ρ`.

Argument sketch: special soundness with unique responses (`hss`, `hur`) implies that whenever the
extractor fails, every repetition's accepting transcript is pinned to a single logged query, so the
prover must have hit a small-sum assignment of `ρ` *fresh* uniform hash values without a second
accepting query at a different challenge. Union-bounding over the `≤ Q` logged queries and the
small-sum target set, and using independence of the `ρ` fresh answers, gives the denominator
`(2^b)^ρ`. -/
private lemma knowledgeSoundness_badEvent_le
    (hss : σ.SpeciallySound) (hur : σ.UniqueResponses)
    (adv : KnowledgeSoundnessAdv ρ b M) (Q : ℕ) (hρ : 0 < ρ)
    (hQ : ∀ x msg, ROQueryBound ρ b M (adv.run x msg) Q) (x : Stmt) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M adv.run x msg]
      ≤ (↑(Q + 1) : ℝ≥0∞) * ↑(smallSumCount ρ b S) / ((↑(2 ^ b) : ℝ≥0∞) ^ ρ) := by
  sorry

omit [SampleableType Chal] in
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
      ≤ knowledgeSoundnessError Q ρ b S := by
  refine le_trans (knowledgeSoundness_badEvent_le σ hr ρ b S M hss hur adv Q hρ hQ x msg) ?_
  rw [knowledgeSoundnessError]
  -- Monotonicity: replace the small-sum count by its stars-and-bars upper bound.
  gcongr
  exact_mod_cast smallSumCount_le ρ b S

/-! ### EUF-CMA Security

A tight EUF-CMA corollary for the Fischlin signature scheme requires an explicit
simulation of signing queries inside a hard-relation experiment. The previous
placeholder theorem overclaimed by bounding forgery probability solely by the
knowledge-soundness error, so we intentionally leave that corollary unstated
until the signing-simulation reduction is formalized. -/

end security

end Fischlin
