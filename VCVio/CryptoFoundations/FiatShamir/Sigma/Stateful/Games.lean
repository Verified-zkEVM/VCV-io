/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Spec
import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
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

/-- Public part of the no-message-attack game.

State: random-oracle cache, lazily sampled keypair, and bad flag. -/
noncomputable def nmaPublic
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl.Stateful unifSpec (cmaPublicSpec M Commit Chal Stmt)
      (NmaState M Commit Chal Stmt Wit)
  | .unif n => StateT.mk fun s => do
      let r ← (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
      pure (r, s)
  | .ro mc => StateT.mk fun s => do
      let cache := s.1
      match cache mc with
      | some r => pure (r, s)
      | none => do
          let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
          pure (r, (cache.cacheQuery mc r, s.2.1, s.2.2))
  | .pk => StateT.mk fun s =>
      match s.2.1 with
      | some (pk, _) => pure (pk, s)
      | none => do
          let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
          pure (pk, (s.1, some (pk, sk), s.2.2))

/-- Programmable random-oracle part of the no-message-attack game. -/
noncomputable def nmaProgram :
    QueryImpl.Stateful unifSpec (progSpec M Commit Chal)
      (NmaState M Commit Chal Stmt Wit)
  | mch => StateT.mk fun s =>
      let mc : M × Commit := (mch.1, mch.2.1)
      let ch : Chal := mch.2.2
      let cache := s.1
      match cache mc with
      | some _ => pure ((), (cache, s.2.1, true))
      | none => pure ((), (cache.cacheQuery mc ch, s.2.1, s.2.2))

/-- The no-message-attack game as a direct stateful handler. -/
noncomputable def nma
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl.Stateful unifSpec (nmaSpec M Commit Chal Stmt)
      (NmaState M Commit Chal Stmt Wit)
  | .unif n => nmaPublic M Commit Chal hr (.unif n)
  | .ro mc => nmaPublic M Commit Chal hr (.ro mc)
  | .pk => nmaPublic M Commit Chal hr .pk
  | .prog mch => nmaProgram M Commit Chal mch

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
      let (c, ch, π) ← OracleComp.liftComp (simT pk) (nmaSpec M Commit Chal Stmt)
      let _ ← (((nmaSpec M Commit Chal Stmt).query (.prog (m, c, ch))) :
        OracleComp (nmaSpec M Commit Chal Stmt) Unit)
      pure ((c, π), log ++ [m])

/-- The CMA-to-NMA reduction as a direct stateful handler.

Public queries are forwarded to the NMA interface; signing queries are handled
by the simulator component that owns the signed-message log. Both paths share
the same `nmaSpec` imports on purpose. -/
noncomputable def cmaToNma
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl.Stateful (nmaSpec M Commit Chal Stmt) (cmaSpec M Commit Chal Resp Stmt)
      (OuterState M)
  | .unif n => StateT.mk fun log => do
      let r ← (((nmaSpec M Commit Chal Stmt).query (.unif n)) :
        OracleComp (nmaSpec M Commit Chal Stmt) (Fin (n + 1)))
      pure (r, log)
  | .ro mc => StateT.mk fun log => do
      let r ← (((nmaSpec M Commit Chal Stmt).query (.ro mc)) :
        OracleComp (nmaSpec M Commit Chal Stmt) Chal)
      pure (r, log)
  | .pk => StateT.mk fun log => do
      let pk ← (((nmaSpec M Commit Chal Stmt).query .pk) :
        OracleComp (nmaSpec M Commit Chal Stmt) Stmt)
      pure (pk, log)
  | .sign m => cmaSignSim M Commit Chal simT m

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

/-- The public random-oracle runtime as an explicit cache-state `QueryImpl`.

This handler is shared by the fixed-key public post-keygen experiment and the
direct named CMA game. -/
@[reducible] noncomputable def fsBaseImpl :
    QueryImpl (unifSpec + roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp) :=
  unifFwdImpl (roSpec M Commit Chal) +
    (randomOracle : QueryImpl (roSpec M Commit Chal) _)

/-- Fixed-key real Fiat-Shamir signing over the shared random-oracle cache. -/
@[reducible] noncomputable def cmaRealFixedSign
    (sigma : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (pk : Stmt) (sk : Wit) :
    QueryImpl (signSpec M Commit Resp)
      (StateT (RoCache M Commit Chal) ProbComp) := by
  letI : HasQuery (roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp) :=
    (randomOracle : QueryImpl (roSpec M Commit Chal) _).toHasQuery
  exact
    (_root_.FiatShamir (m := StateT (RoCache M Commit Chal) ProbComp) sigma hr M).sign
      pk sk

/-- Source-query part of the real CMA game over the full direct CMA state. -/
noncomputable def cmaRealSourceFull
    (sigma : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl.Stateful unifSpec (cmaSourceSpec M Commit Chal Resp)
      (CmaState M Commit Chal Stmt Wit)
  | .unif n => StateT.mk fun s => do
      let log := s.1.1
      let cache := s.1.2.1
      let keypair := s.1.2.2
      let bad := s.2
      let r ← (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
      pure (r, ((log, cache, keypair), bad))
  | .ro mc => StateT.mk fun s =>
      let log := s.1.1
      let cache := s.1.2.1
      let keypair := s.1.2.2
      let bad := s.2
      match cache mc with
      | some r => pure (r, ((log, cache, keypair), bad))
      | none => do
          let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
          pure (r, ((log, cache.cacheQuery mc r, keypair), bad))
  | .sign m => StateT.mk fun s => do
      let log := s.1.1
      let cache := s.1.2.1
      let keypair := s.1.2.2
      let bad := s.2
      match keypair with
      | some (pk, sk) => do
          let (c, prv) ← sigma.commit pk sk
          match cache (m, c) with
          | some ch => do
              let π ← sigma.respond pk sk prv ch
              pure ((c, π), ((log ++ [m], cache, some (pk, sk)), bad))
          | none => do
              let ch ← (($ᵗ Chal) : OracleComp unifSpec Chal)
              let π ← sigma.respond pk sk prv ch
              pure ((c, π), ((log ++ [m], cache.cacheQuery (m, c) ch, some (pk, sk)), bad))
      | none => do
          let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
          let (c, prv) ← sigma.commit pk sk
          match cache (m, c) with
          | some ch => do
              let π ← sigma.respond pk sk prv ch
              pure ((c, π), ((log ++ [m], cache, some (pk, sk)), bad))
          | none => do
              let ch ← (($ᵗ Chal) : OracleComp unifSpec Chal)
              let π ← sigma.respond pk sk prv ch
              pure ((c, π), ((log ++ [m], cache.cacheQuery (m, c) ch, some (pk, sk)), bad))

/-- Source-query part of the real CMA game over the concrete sum interface used
by `SignatureAlg.unforgeableAdv`. -/
noncomputable def cmaRealSourceFullSum
    (sigma : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl.Stateful unifSpec
      ((unifSpec + roSpec M Commit Chal) + signSpec M Commit Resp)
      (CmaState M Commit Chal Stmt Wit)
  | .inl (.inl n) => cmaRealSourceFull M Commit Chal sigma hr (.unif n)
  | .inl (.inr mc) => cmaRealSourceFull M Commit Chal sigma hr (.ro mc)
  | .inr m => cmaRealSourceFull M Commit Chal sigma hr (.sign m)

/-- The real CMA game as a direct stateful handler.

On signing queries, this runs the real Sigma protocol and appends the message
to the signed log. The bad flag is preserved and never set by real signing. -/
noncomputable def cmaReal
    (sigma : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl.Stateful unifSpec (cmaSpec M Commit Chal Resp Stmt)
      (CmaState M Commit Chal Stmt Wit)
  | .unif n => cmaRealSourceFull M Commit Chal sigma hr (.unif n)
  | .ro mc => cmaRealSourceFull M Commit Chal sigma hr (.ro mc)
  | .sign m => cmaRealSourceFull M Commit Chal sigma hr (.sign m)
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
