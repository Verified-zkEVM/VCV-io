/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import VCVio.CryptoFoundations.Fischlin.Defs

/-!
# Fischlin Transform: Query-Cost Accounting

Query-complexity accounting for the Fischlin transform: bounds on the number of
random-oracle queries made by `verify` and `sign`, their weighted query cost,
and the corresponding expected-query bounds.
-/

universe u v

open OracleComp OracleSpec

namespace Fischlin

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

open ENNReal

section costAccounting

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp) (ρ b : ℕ) (M : Type)

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

/-- Fischlin's inner search, instantiated in a concrete unit-cost runtime. -/
private def fischlinSearchAuxWithUnitCost
    {Stmt Wit Commit PrvState Chal Resp M : Type} {rel : Stmt → Wit → Bool} {ρ b : ℕ}
    {m : Type → Type v} [Monad m] [MonadLiftT ProbComp m]
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
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
      rfl

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
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
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
      rfl

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

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
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

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
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

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
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

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
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

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
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

end Fischlin
