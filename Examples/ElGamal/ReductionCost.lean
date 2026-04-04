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

@[simp] lemma eval_reductionProfile {ω : Type} [AddCommMonoid ω]
    (intrinsic : ω) (weights : OneTimeINDCPACapability → ω) :
    (reductionProfile intrinsic).eval weights =
      intrinsic + weights chooseMessages + weights distinguish := by
  simp [reductionProfile, add_assoc, add_left_comm, add_comm]

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
  let (m₁, m₂, st) ← monadLift <|
    HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G)) (m := ProbComp)
      (.chooseMessages A)
  let bit ← monadLift ($ᵗ Bool : ProbComp Bool)
  let c : G × G := (B, T + if bit then m₁ else m₂)
  AddWriterT.addTell (ResourceProfile.single OneTimeINDCPACapability.distinguish)
  let bit' ← monadLift <|
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

section OpenCostTheorems

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G]

/-- The open, resource-profile-instrumented DDH reduction has a fixed exact pathwise profile:
intrinsic overhead plus one use each of `chooseMessages` and `distinguish`. -/
lemma IND_CPA_OneTime_DDHReduction_openCost_pathwiseHasCost
    {State ω : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω) (g A B T : G)
    [HasQuery (oneTimeINDCPASpec G G State (G × G)) ProbComp] :
    AddWriterT.PathwiseHasCost
      (IND_CPA_OneTime_DDHReduction_openCost
        (State := State) (ω := ω) intrinsic g A B T)
      (OneTimeINDCPACapability.reductionProfile intrinsic) := by
  unfold IND_CPA_OneTime_DDHReduction_openCost
  have h :
      AddWriterT.PathwiseHasCost
        ((do
          AddWriterT.addTell (ResourceProfile.ofIntrinsic (κ := OneTimeINDCPACapability) intrinsic)
          AddWriterT.addTell
            (ResourceProfile.single (ω := ω) OneTimeINDCPACapability.chooseMessages)
          let (m₁, m₂, st) ← monadLift <|
            HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G)) (m := ProbComp)
              (.chooseMessages A)
          let bit ← monadLift ($ᵗ Bool : ProbComp Bool)
          have c : G × G := (B, T + if bit then m₁ else m₂)
          AddWriterT.addTell
            (ResourceProfile.single (ω := ω) OneTimeINDCPACapability.distinguish)
          let bit' ← monadLift <|
            HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G)) (m := ProbComp)
              (.distinguish st c)
          pure (bit == bit')) :
          AddWriterT (ResourceProfile ω OneTimeINDCPACapability) ProbComp Bool)
        (ResourceProfile.ofIntrinsic (κ := OneTimeINDCPACapability) intrinsic +
          (ResourceProfile.single (ω := ω) OneTimeINDCPACapability.chooseMessages +
            ResourceProfile.single (ω := ω) OneTimeINDCPACapability.distinguish)) := by
    refine AddWriterT.pathwiseHasCost_bind
      (m := ProbComp)
      (ω := ResourceProfile ω OneTimeINDCPACapability)
      (w₁ := ResourceProfile.ofIntrinsic (κ := OneTimeINDCPACapability) intrinsic)
      (w₂ := ResourceProfile.single (ω := ω) OneTimeINDCPACapability.chooseMessages +
        ResourceProfile.single (ω := ω) OneTimeINDCPACapability.distinguish)
      ?_ (fun _ ↦ ?_)
    · exact AddWriterT.pathwiseHasCost_addTell
        (m := ProbComp)
        (ResourceProfile.ofIntrinsic (κ := OneTimeINDCPACapability) intrinsic)
    · refine AddWriterT.pathwiseHasCost_bind
        (m := ProbComp)
        (ω := ResourceProfile ω OneTimeINDCPACapability)
        (w₁ := ResourceProfile.single (ω := ω) OneTimeINDCPACapability.chooseMessages)
        (w₂ := ResourceProfile.single (ω := ω) OneTimeINDCPACapability.distinguish)
        ?_ (fun _ ↦ ?_)
      · exact AddWriterT.pathwiseHasCost_addTell
          (m := ProbComp)
          (ResourceProfile.single (ω := ω) OneTimeINDCPACapability.chooseMessages)
      · refine AddWriterT.pathwiseHasCost_bind_zero_left
          (m := ProbComp)
          (ω := ResourceProfile ω OneTimeINDCPACapability)
          ?_ (fun msgs ↦ ?_)
        · exact AddWriterT.pathwiseHasCost_probCompLift
            (m := ProbComp)
            (ω := ResourceProfile ω OneTimeINDCPACapability)
            (x := HasQuery.query
              (spec := oneTimeINDCPASpec G G State (G × G))
              (m := ProbComp)
              (.chooseMessages A))
        · rcases msgs with ⟨m₁, m₂, st⟩
          refine AddWriterT.pathwiseHasCost_bind_zero_left
            (m := ProbComp)
            (ω := ResourceProfile ω OneTimeINDCPACapability)
            ?_ (fun bit ↦ ?_)
          · exact AddWriterT.pathwiseHasCost_probCompLift
              (m := ProbComp)
              (ω := ResourceProfile ω OneTimeINDCPACapability)
              (x := ($ᵗ Bool : ProbComp Bool))
          · refine AddWriterT.pathwiseHasCost_bind_zero_right
              (m := ProbComp)
              (ω := ResourceProfile ω OneTimeINDCPACapability)
              ?_ (fun _ ↦ by
                refine AddWriterT.pathwiseHasCost_bind_zero_left
                  (m := ProbComp)
                  (ω := ResourceProfile ω OneTimeINDCPACapability)
                  ?_ (fun bit' ↦ ?_)
                · exact AddWriterT.pathwiseHasCost_probCompLift
                    (m := ProbComp)
                    (ω := ResourceProfile ω OneTimeINDCPACapability)
                    (x := HasQuery.query
                      (spec := oneTimeINDCPASpec G G State (G × G))
                      (m := ProbComp)
                      (.distinguish st (B, T + if bit then m₁ else m₂)))
                · exact AddWriterT.pathwiseHasCost_pure
                    (m := ProbComp)
                    (ω := ResourceProfile ω OneTimeINDCPACapability)
                    (bit == bit'))
            · exact AddWriterT.pathwiseHasCost_addTell
                (m := ProbComp)
                (ResourceProfile.single (ω := ω) OneTimeINDCPACapability.distinguish)
  rw [OneTimeINDCPACapability.reductionProfile, add_assoc]
  exact h

end OpenCostTheorems

/-- Closed, resource-profile-instrumented form of the one-time ElGamal DDH reduction. -/
noncomputable def IND_CPA_OneTime_DDHReduction_costed
    {gen : G} {ω : Type} [AddMonoid ω]
    (intrinsic : ω)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    G → G → G → G →
      AddWriterT (ResourceProfile ω OneTimeINDCPACapability) ProbComp Bool :=
  fun g A B T => by
    letI := (oneTimeINDCPARuntime (gen := gen) adv).toHasQuery
    exact IND_CPA_OneTime_DDHReduction_openCost
      (State := adv.State) (ω := ω) intrinsic g A B T

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

/-- Instantiating the open costed reduction with a concrete adversary preserves the exact pathwise
resource profile proved for the open reduction body. -/
lemma IND_CPA_OneTime_DDHReduction_costed_pathwiseHasCost
    {gen : G} {ω : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (g A B T : G) :
    AddWriterT.PathwiseHasCost
      (IND_CPA_OneTime_DDHReduction_costed
        (F := F) (G := G) (gen := gen) (ω := ω) intrinsic adv g A B T)
      (OneTimeINDCPACapability.reductionProfile intrinsic) := by
  letI := (oneTimeINDCPARuntime (gen := gen) adv).toHasQuery
  simpa [IND_CPA_OneTime_DDHReduction_costed] using
    (IND_CPA_OneTime_DDHReduction_openCost_pathwiseHasCost
      (State := adv.State) (ω := ω) intrinsic g A B T)

end IND_CPA

end elGamalAsymmEnc
