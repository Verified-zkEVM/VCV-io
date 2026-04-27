/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Spec
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.StateT

/-!
# Stateful Fiat-Shamir CMA games

Direct `QueryImpl.Stateful` versions of the Fiat-Shamir CMA/NMA games.
These handlers use ordinary product states rather than heap packages.
-/

universe u

open OracleSpec OracleComp ProbComp

namespace FiatShamir.Stateful

variable (M : Type) [DecidableEq M]
variable (Commit : Type) [DecidableEq Commit]
variable (Chal : Type) [SampleableType Chal]
variable {Stmt Wit : Type} {rel : Stmt → Wit → Bool}
variable {Resp PrvState : Type}

/-! ## `nma`: no-message-attack game -/

/-- The no-message-attack game as a direct stateful handler.

State: random-oracle cache, lazily sampled keypair, and bad flag. -/
noncomputable def nma
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl.Stateful unifSpec (nmaSpec M Commit Chal Stmt)
      (NmaState M Commit Chal Stmt Wit)
  | .unif n => StateT.mk fun s => do
      let r ← (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
      pure (r, s)
  | .ro mc => StateT.mk fun s =>
      let cache := s.1
      match cache mc with
      | some r => pure (r, s)
      | none => do
          let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
          pure (r, (cache.cacheQuery mc r, s.2.1, s.2.2))
  | .prog mch => StateT.mk fun s =>
      let mc : M × Commit := (mch.1, mch.2.1)
      let ch : Chal := mch.2.2
      let cache := s.1
      match cache mc with
      | some _ => pure ((), (cache, s.2.1, true))
      | none => pure ((), (cache.cacheQuery mc ch, s.2.1, s.2.2))
  | .pk => StateT.mk fun s =>
      match s.2.1 with
      | some (pk, _) => pure (pk, s)
      | none => do
          let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
          pure (pk, (s.1, some (pk, sk), s.2.2))

/-! ## `cmaToNma`: CMA-to-NMA reduction -/

/-- Forward the public, non-signing CMA queries to the shared NMA interface.

This component has no private state. Its imports are intentionally the same
ambient `nmaSpec` used by the signing simulator, so adversarial RO queries and
programming queries interact through one inner random-oracle cache. -/
noncomputable def cmaPublicForward :
    QueryImpl.Stateful (nmaSpec M Commit Chal Stmt) (cmaPublicSpec M Commit Chal Stmt) PUnit
  | .unif n => StateT.mk fun u => do
      let r ← (((nmaSpec M Commit Chal Stmt).query (.unif n)) :
        OracleComp (nmaSpec M Commit Chal Stmt) (Fin (n + 1)))
      pure (r, u)
  | .ro mc => StateT.mk fun u => do
      let r ← (((nmaSpec M Commit Chal Stmt).query (.ro mc)) :
        OracleComp (nmaSpec M Commit Chal Stmt) Chal)
      pure (r, u)
  | .pk => StateT.mk fun u => do
      let pk ← (((nmaSpec M Commit Chal Stmt).query .pk) :
        OracleComp (nmaSpec M Commit Chal Stmt) Stmt)
      pure (pk, u)

/-- Signing part of the CMA-to-NMA reduction.

State: signed-message log. Signing queries sample the HVZK simulator and
program the random oracle through the shared NMA interface. -/
noncomputable def cmaSignSim
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl.Stateful (nmaSpec M Commit Chal Stmt) (signSpec M Commit Resp)
      (OuterState M)
  | m => StateT.mk fun log => do
      let pk ← (((nmaSpec M Commit Chal Stmt).query .pk) :
        OracleComp (nmaSpec M Commit Chal Stmt) Stmt)
      let (c, ch, π) ← (liftM (simT pk) :
        OracleComp (nmaSpec M Commit Chal Stmt) (Commit × Chal × Resp))
      let _ ← (((nmaSpec M Commit Chal Stmt).query (.prog (m, c, ch))) :
        OracleComp (nmaSpec M Commit Chal Stmt) Unit)
      pure ((c, π), log ++ [m])

/-- The CMA-to-NMA reduction as a route-based direct stateful handler.

Public queries are forwarded by a stateless component; signing queries are
handled by a stateful component that owns the signed-message log. Both components
share the same `nmaSpec` imports on purpose. -/
noncomputable def cmaToNma
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl.Stateful (nmaSpec M Commit Chal Stmt) (cmaSpec M Commit Chal Resp Stmt)
      (OuterState M) :=
  QueryImpl.Stateful.parRouteWith
    (cmaToNmaFrame M) (cmaRoute M Commit Chal Resp Stmt).toExportRoute
    (cmaPublicForward M Commit Chal) (cmaSignSim M Commit Chal simT)

/-! ## `cmaSim`: simulated CMA game -/

/-- The simulated CMA game, linked through the direct CMA frame. -/
noncomputable abbrev cmaSim
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl.Stateful unifSpec (cmaSpec M Commit Chal Resp Stmt)
      (CmaState M Commit Chal Stmt Wit) :=
  (cmaToNma M Commit Chal simT).linkWith
    (cmaFrame M Commit Chal Stmt Wit) (nma M Commit Chal hr)

/-! ## `cmaReal`: real CMA game -/

/-- The real CMA game as a direct stateful handler.

On signing queries, this runs the real Sigma protocol and appends the message
to the signed log. The bad flag is preserved and never set by real signing. -/
noncomputable def cmaReal
    (sigma : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl.Stateful unifSpec (cmaSpec M Commit Chal Resp Stmt)
      (CmaState M Commit Chal Stmt Wit)
  | .unif n => StateT.mk fun s => do
      let r ← (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
      pure (r, s)
  | .ro mc => StateT.mk fun s =>
      let log := s.1.1
      let cache := s.1.2.1
      let keypair := s.1.2.2
      let bad := s.2
      match cache mc with
      | some r => pure (r, s)
      | none => do
          let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
          pure (r, ((log, cache.cacheQuery mc r, keypair), bad))
  | .sign m => StateT.mk fun s => do
      let log := s.1.1
      let cache := s.1.2.1
      let keypair := s.1.2.2
      let bad := s.2
      let (pk, sk, keypair₁) ← match keypair with
        | some (pk, sk) =>
            (pure (pk, sk, keypair) :
              OracleComp unifSpec (Stmt × Wit × Option (Stmt × Wit)))
        | none => do
            let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
            pure (pk, sk, some (pk, sk))
      let (c, prvSt) ← (liftM (sigma.commit pk sk) :
        OracleComp unifSpec (Commit × PrvState))
      let (ch, cache₁) ← match cache (m, c) with
        | some r =>
            (pure (r, cache) : OracleComp unifSpec (Chal × RoCache M Commit Chal))
        | none => do
            let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
            pure (r, cache.cacheQuery (m, c) r)
      let π ← (liftM (sigma.respond pk sk prvSt ch) : OracleComp unifSpec Resp)
      pure ((c, π), ((log ++ [m], cache₁, keypair₁), bad))
  | .pk => StateT.mk fun s =>
      let log := s.1.1
      let cache := s.1.2.1
      let keypair := s.1.2.2
      let bad := s.2
      match keypair with
      | some (pk, _) => pure (pk, s)
      | none => do
          let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
          pure (pk, ((log, cache, some (pk, sk)), bad))

end FiatShamir.Stateful
