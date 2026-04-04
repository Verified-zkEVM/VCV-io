/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ElGamal.Basic
import VCVio.OracleComp.QueryTracking.QueryRuntime
import VCVio.OracleComp.QueryTracking.ResourceProfile

/-!
# ElGamal Reduction Cost Accounting

This file expresses the one-time ElGamal DDH reduction against an explicit adversary interface and
its induced resource profile.

The key idea is to reify the two procedures of a one-time IND-CPA adversary,
`chooseMessages` and `distinguish`, as an oracle interface. The ElGamal reduction can then be
written once as open code over that interface, independently of any particular adversary
implementation. This is the right level for reduction-cost theorems: the reduction body exposes
its own intrinsic overhead and its interface usage before those external calls are instantiated by
concrete adversaries.
-/

open OracleSpec OracleComp ENNReal

namespace elGamalAsymmEnc

section IND_CPA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

local instance : Inhabited G := ⟨0⟩

/-- Interface operations exposed by a one-time IND-CPA adversary. -/
inductive OneTimeINDCPAOp (PK State C : Type)
  | chooseMessages (pk : PK)
  | distinguish (state : State) (c : C)

/-- Oracle interface obtained by reifying the two phases of a one-time IND-CPA adversary. -/
def oneTimeINDCPASpec (M PK State C : Type) : OracleSpec (OneTimeINDCPAOp PK State C)
  | .chooseMessages _ => M × M × State
  | .distinguish _ _ => Bool

/-- Coarse capability names used in the structured resource profile of the reduction. -/
inductive OneTimeINDCPACapability
  | chooseMessages
  | distinguish
  deriving DecidableEq

namespace OneTimeINDCPACapability

/-- Structured resource charge assigned to each adversary-interface operation. -/
noncomputable def profileCost {ω : Type} [AddMonoid ω] {PK State C : Type} :
    OneTimeINDCPAOp PK State C → ResourceProfile ω OneTimeINDCPACapability
  | .chooseMessages _ => ResourceProfile.single chooseMessages
  | .distinguish _ _ => ResourceProfile.single distinguish

/-- Structured resource profile of the one-time ElGamal DDH reduction body.

The profile consists of:
- intrinsic overhead `intrinsic`,
- one call to `chooseMessages`,
- one call to `distinguish`. -/
noncomputable def reductionProfile {ω : Type} [AddMonoid ω] (intrinsic : ω) :
    ResourceProfile ω OneTimeINDCPACapability :=
  ResourceProfile.ofIntrinsic (κ := OneTimeINDCPACapability) intrinsic
    + ResourceProfile.single chooseMessages
    + ResourceProfile.single distinguish

end OneTimeINDCPACapability

/-- Open version of the one-time ElGamal DDH reduction body.

This is the usual DDH reduction, but written against the reified one-time IND-CPA adversary
interface instead of a concrete adversary structure. It samples the challenge bit internally and
uses the externally provided `chooseMessages` and `distinguish` procedures for the two adversary
phases. -/
def IND_CPA_OneTime_DDHReduction_open
    {State : Type} (_gen A B T : G)
    [HasQuery (oneTimeINDCPASpec G G State (G × G)) ProbComp] :
    ProbComp Bool := do
  let (m₁, m₂, st) ← HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G))
    (.chooseMessages A)
  let bit ← ($ᵗ Bool : ProbComp Bool)
  let c : G × G := (B, T + if bit then m₁ else m₂)
  let bit' ← HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G))
    (.distinguish st c)
  pure (bit == bit')

/-- Resource-profile-instrumented form of [`IND_CPA_OneTime_DDHReduction_open`].

The writer log records the reduction's own intrinsic overhead together with one symbolic use of
each external adversary capability. The adversary calls themselves remain in the base `ProbComp`
semantics and are lifted into the writer monad without contributing additional writer cost. -/
noncomputable def IND_CPA_OneTime_DDHReduction_openCost
    {State ω : Type} [AddMonoid ω]
    (intrinsic : ω) (_gen A B T : G)
    [HasQuery (oneTimeINDCPASpec G G State (G × G)) ProbComp] :
    AddWriterT (ResourceProfile ω OneTimeINDCPACapability) ProbComp Bool := do
  AddWriterT.addTell (ResourceProfile.ofIntrinsic (κ := OneTimeINDCPACapability) intrinsic)
  AddWriterT.addTell (ResourceProfile.single OneTimeINDCPACapability.chooseMessages)
  let (m₁, m₂, st) ← liftM <|
    HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G)) (m := ProbComp)
      (.chooseMessages A)
  let bit ← liftM ($ᵗ Bool : ProbComp Bool)
  let c : G × G := (B, T + if bit then m₁ else m₂)
  AddWriterT.addTell (ResourceProfile.single OneTimeINDCPACapability.distinguish)
  let bit' ← liftM <|
    HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G)) (m := ProbComp)
      (.distinguish st c)
  pure (bit == bit')

/-- Runtime that interprets the reified one-time IND-CPA interface using a concrete adversary. -/
def oneTimeINDCPARuntime {gen : G}
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    QueryRuntime (oneTimeINDCPASpec G G adv.State (G × G)) ProbComp where
  impl
    | .chooseMessages pk => adv.chooseMessages pk
    | .distinguish st c => adv.distinguish st c

/-- Instantiating the open reduction with a concrete adversary recovers the existing closed DDH
reduction `IND_CPA_OneTime_DDHReduction` from `Examples.ElGamal.Basic`. -/
@[simp]
lemma IND_CPA_OneTime_DDHReduction_open_inRuntime
    {gen : G}
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (g A B T : G) :
    HasQuery.inRuntime
      (IND_CPA_OneTime_DDHReduction_open
        (State := adv.State) g A B T)
      (oneTimeINDCPARuntime (gen := gen) adv)
      = IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv g A B T := by
  rfl

end IND_CPA

end elGamalAsymmEnc
