/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ElGamal.Basic
import VCVio.CryptoFoundations.Asymptotics.ReductionCost
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

/-- Interpret the coarse reduction capabilities using concrete resource profiles.

This packages the cost transform "plug the profile for `chooseMessages` and `distinguish` into the
open reduction body" as a function on capability names. -/
noncomputable def instantiateProfile {ω κ : Type} [AddMonoid ω]
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ) :
    OneTimeINDCPACapability → ResourceProfile ω κ :=
  profile

/-- Cost transform induced by the open one-time ElGamal DDH reduction body. -/
noncomputable def reductionTransform {ω κ : Type} [AddCommMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ) :
    ResourceProfile ω κ :=
  (reductionProfile intrinsic).instantiate (instantiateProfile profile)

@[simp] lemma reductionTransform_eq {ω κ : Type} [AddCommMonoid ω]
    (intrinsic : ω) (profile : OneTimeINDCPACapability → ResourceProfile ω κ) :
    reductionTransform intrinsic profile =
      ResourceProfile.ofIntrinsic (κ := κ) intrinsic
        + profile chooseMessages
        + profile distinguish := by
  simp [reductionTransform, reductionProfile, instantiateProfile, add_assoc]

@[simp] lemma instantiate_reductionTransform {ω κ κ' : Type} [AddCommMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ)
    (impl : κ → ResourceProfile ω κ') :
    (reductionTransform intrinsic profile).instantiate impl =
      reductionTransform intrinsic (fun k ↦ (profile k).instantiate impl) := by
  simp [reductionTransform, instantiateProfile, ResourceProfile.instantiate_assoc]

@[simp] lemma eval_reductionProfile {ω : Type} [AddCommMonoid ω]
    (intrinsic : ω) (weights : OneTimeINDCPACapability → ω) :
    (reductionProfile intrinsic).eval weights =
      intrinsic + weights chooseMessages + weights distinguish := by
  simp [reductionProfile, add_assoc, add_left_comm, add_comm]

@[simp] lemma eval_reductionTransform {ω κ : Type} [AddCommMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ)
    (weights : κ → ω) :
    (reductionTransform intrinsic profile).eval weights =
      intrinsic
        + (profile chooseMessages).eval weights
        + (profile distinguish).eval weights := by
  simp [reductionTransform_eq, add_assoc, add_left_comm, add_comm]

@[simp] lemma reductionTransform_ofIntrinsic {ω κ : Type} [AddCommMonoid ω]
    (intrinsic chooseCost distinguishCost : ω) :
    reductionTransform (κ := κ) intrinsic
      (fun
        | chooseMessages => ResourceProfile.ofIntrinsic (κ := κ) chooseCost
        | distinguish => ResourceProfile.ofIntrinsic (κ := κ) distinguishCost) =
      ResourceProfile.ofIntrinsic (κ := κ) (intrinsic + chooseCost + distinguishCost) := by
  ext <;> simp [reductionTransform_eq, add_assoc, add_left_comm, add_comm]

/-- The ElGamal reduction transform is monotone in the procedure-cost profile assigned to the
source adversary. -/
lemma monotone_reductionTransform {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω]
    [IsOrderedAddMonoid ω] (intrinsic : ω) :
    Monotone (reductionTransform (κ := κ) intrinsic) := by
  intro profile₁ profile₂ hprofile
  rw [reductionTransform_eq, reductionTransform_eq]
  simpa [add_assoc, add_left_comm, add_comm] using
    add_le_add_left
      (add_le_add (hprofile chooseMessages) (hprofile distinguish))
      (ResourceProfile.ofIntrinsic (κ := κ) intrinsic)

end OneTimeINDCPACapability

/-- Asymptotic cost assignment for the two procedures of a one-time IND-CPA adversary. -/
abbrev OneTimeINDCPAProfile (ω κ : Type) :=
  OneTimeINDCPACapability → ResourceProfile ω κ

/-- Assemble the asymptotic procedure costs of a one-time IND-CPA adversary into a single
interface-profile bound indexed by the two reified capabilities. -/
def oneTimeINDCPAProfileCost
    {gen : G} {ω κ : Type}
    (chooseCost distinguishCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → ResourceProfile ω κ) :
    AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProfile ω κ :=
  fun adv n op =>
    match op with
    | .chooseMessages => chooseCost adv n
    | .distinguish => distinguishCost adv n

/-- Cost model for the DDH reduction obtained by instantiating the open reduction transform with
the asymptotic procedure-cost profile of the source adversary. -/
noncomputable def oneTimeDDHReductionCost
    {gen : G} {ω κ : Type} [AddCommMonoid ω]
    (intrinsic : ω)
    (advCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProfile ω κ) :
    AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → ResourceProfile ω κ :=
  fun adv n =>
    OneTimeINDCPACapability.reductionTransform intrinsic (advCost adv n)

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

/-- Resource-profile-instrumented form of [`IND_CPA_OneTime_DDHReduction_open`] with a concrete
profile assigned to each reified adversary capability. -/
noncomputable def IND_CPA_OneTime_DDHReduction_openProfiled
    {State ω κ : Type} [AddMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ)
    (_gen A B T : G)
    [HasQuery (oneTimeINDCPASpec G G State (G × G)) ProbComp] :
    AddWriterT (ResourceProfile ω κ) ProbComp Bool := do
  AddWriterT.addTell (ResourceProfile.ofIntrinsic (κ := κ) intrinsic)
  AddWriterT.addTell (profile OneTimeINDCPACapability.chooseMessages)
  let (m₁, m₂, st) ← monadLift <|
    HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G)) (m := ProbComp)
      (.chooseMessages A)
  let bit ← monadLift ($ᵗ Bool : ProbComp Bool)
  let c : G × G := (B, T + if bit then m₁ else m₂)
  AddWriterT.addTell (profile OneTimeINDCPACapability.distinguish)
  let bit' ← monadLift <|
    HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G)) (m := ProbComp)
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
    AddWriterT (ResourceProfile ω OneTimeINDCPACapability) ProbComp Bool :=
  IND_CPA_OneTime_DDHReduction_openProfiled
    (State := State) (ω := ω) (κ := OneTimeINDCPACapability) intrinsic
    (fun k ↦ ResourceProfile.single (ω := ω) k)
    _gen A B T

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
intrinsic overhead together with the profiles assigned to `chooseMessages` and
`distinguish`. -/
lemma IND_CPA_OneTime_DDHReduction_openProfiled_pathwiseHasCost
    {State ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ)
    (g A B T : G)
    [HasQuery (oneTimeINDCPASpec G G State (G × G)) ProbComp] :
    AddWriterT.PathwiseHasCost
      (IND_CPA_OneTime_DDHReduction_openProfiled
        (State := State) (ω := ω) (κ := κ) intrinsic profile g A B T)
      (OneTimeINDCPACapability.reductionTransform intrinsic profile) := by
  unfold IND_CPA_OneTime_DDHReduction_openProfiled
  have h :
      AddWriterT.PathwiseHasCost
        ((do
          AddWriterT.addTell (ResourceProfile.ofIntrinsic (κ := κ) intrinsic)
          AddWriterT.addTell (profile OneTimeINDCPACapability.chooseMessages)
          let (m₁, m₂, st) ← monadLift <|
            HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G)) (m := ProbComp)
              (.chooseMessages A)
          let bit ← monadLift ($ᵗ Bool : ProbComp Bool)
          have c : G × G := (B, T + if bit then m₁ else m₂)
          AddWriterT.addTell (profile OneTimeINDCPACapability.distinguish)
          let bit' ← monadLift <|
            HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G)) (m := ProbComp)
              (.distinguish st c)
          pure (bit == bit')) :
          AddWriterT (ResourceProfile ω κ) ProbComp Bool)
        (ResourceProfile.ofIntrinsic (κ := κ) intrinsic +
          (profile OneTimeINDCPACapability.chooseMessages +
            profile OneTimeINDCPACapability.distinguish)) := by
    refine AddWriterT.pathwiseHasCost_bind
      (m := ProbComp)
      (ω := ResourceProfile ω κ)
      (w₁ := ResourceProfile.ofIntrinsic (κ := κ) intrinsic)
      (w₂ := profile OneTimeINDCPACapability.chooseMessages +
        profile OneTimeINDCPACapability.distinguish)
      ?_ (fun _ ↦ ?_)
    · exact AddWriterT.pathwiseHasCost_addTell
        (m := ProbComp)
        (ResourceProfile.ofIntrinsic (κ := κ) intrinsic)
    · refine AddWriterT.pathwiseHasCost_bind
        (m := ProbComp)
        (ω := ResourceProfile ω κ)
        (w₁ := profile OneTimeINDCPACapability.chooseMessages)
        (w₂ := profile OneTimeINDCPACapability.distinguish)
        ?_ (fun _ ↦ ?_)
      · exact AddWriterT.pathwiseHasCost_addTell
          (m := ProbComp)
          (profile OneTimeINDCPACapability.chooseMessages)
      · refine AddWriterT.pathwiseHasCost_bind_zero_left
          (m := ProbComp)
          (ω := ResourceProfile ω κ)
          ?_ (fun msgs ↦ ?_)
        · exact AddWriterT.pathwiseHasCost_probCompLift
            (m := ProbComp)
            (ω := ResourceProfile ω κ)
            (x := HasQuery.query
              (spec := oneTimeINDCPASpec G G State (G × G))
              (m := ProbComp)
              (.chooseMessages A))
        · rcases msgs with ⟨m₁, m₂, st⟩
          refine AddWriterT.pathwiseHasCost_bind_zero_left
            (m := ProbComp)
            (ω := ResourceProfile ω κ)
            ?_ (fun bit ↦ ?_)
          · exact AddWriterT.pathwiseHasCost_probCompLift
              (m := ProbComp)
              (ω := ResourceProfile ω κ)
              (x := ($ᵗ Bool : ProbComp Bool))
          · refine AddWriterT.pathwiseHasCost_bind_zero_right
              (m := ProbComp)
              (ω := ResourceProfile ω κ)
              ?_ (fun _ ↦ by
                refine AddWriterT.pathwiseHasCost_bind_zero_left
                  (m := ProbComp)
                  (ω := ResourceProfile ω κ)
                  ?_ (fun bit' ↦ ?_)
                · exact AddWriterT.pathwiseHasCost_probCompLift
                    (m := ProbComp)
                    (ω := ResourceProfile ω κ)
                    (x := HasQuery.query
                      (spec := oneTimeINDCPASpec G G State (G × G))
                      (m := ProbComp)
                      (.distinguish st (B, T + if bit then m₁ else m₂)))
                · exact AddWriterT.pathwiseHasCost_pure
                    (m := ProbComp)
                    (ω := ResourceProfile ω κ)
                    (bit == bit'))
            · exact AddWriterT.pathwiseHasCost_addTell
                (m := ProbComp)
                (profile OneTimeINDCPACapability.distinguish)
  rw [OneTimeINDCPACapability.reductionTransform_eq]
  exact ⟨by simpa only [add_assoc] using h.1, by simpa only [add_assoc] using h.2⟩

/-- The symbolic capability-counting theorem is the specialization of
[`IND_CPA_OneTime_DDHReduction_openProfiled_pathwiseHasCost`] where each capability is charged by
its own singleton resource profile. -/
lemma IND_CPA_OneTime_DDHReduction_openCost_pathwiseHasCost
    {State ω : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω) (g A B T : G)
    [HasQuery (oneTimeINDCPASpec G G State (G × G)) ProbComp] :
    AddWriterT.PathwiseHasCost
      (IND_CPA_OneTime_DDHReduction_openCost
        (State := State) (ω := ω) intrinsic g A B T)
      (OneTimeINDCPACapability.reductionProfile intrinsic) := by
  simpa [IND_CPA_OneTime_DDHReduction_openCost] using
    (IND_CPA_OneTime_DDHReduction_openProfiled_pathwiseHasCost
      (State := State) (ω := ω) (κ := OneTimeINDCPACapability)
      intrinsic (fun k ↦ ResourceProfile.single (ω := ω) k) g A B T)

end OpenCostTheorems

/-- Closed, resource-profile-instrumented form of the one-time ElGamal DDH reduction obtained by
instantiating the profiled open reduction with a concrete adversary. -/
noncomputable def IND_CPA_OneTime_DDHReduction_profiled
    {gen : G} {ω κ : Type} [AddMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    G → G → G → G → AddWriterT (ResourceProfile ω κ) ProbComp Bool :=
  fun g A B T => by
    letI := (oneTimeINDCPARuntime (gen := gen) adv).toHasQuery
    exact IND_CPA_OneTime_DDHReduction_openProfiled
      (State := adv.State) (ω := ω) (κ := κ) intrinsic profile g A B T

/-- Closed, resource-profile-instrumented form of the one-time ElGamal DDH reduction. -/
noncomputable def IND_CPA_OneTime_DDHReduction_costed
    {gen : G} {ω : Type} [AddMonoid ω]
    (intrinsic : ω)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    G → G → G → G →
      AddWriterT (ResourceProfile ω OneTimeINDCPACapability) ProbComp Bool :=
  IND_CPA_OneTime_DDHReduction_profiled
    (F := F) (G := G) (gen := gen) (ω := ω) (κ := OneTimeINDCPACapability)
    intrinsic (fun k ↦ ResourceProfile.single (ω := ω) k) adv

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

/-- Cost-transform theorem for the closed one-time ElGamal DDH reduction.

If `profile` assigns resource profiles to the two adversary capabilities `chooseMessages` and
`distinguish`, then the instantiated reduction has exact pathwise cost equal to the reduction
transform applied to those capability profiles. -/
lemma IND_CPA_OneTime_DDHReduction_profiled_pathwiseHasCost
    {gen : G} {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (g A B T : G) :
    AddWriterT.PathwiseHasCost
      (IND_CPA_OneTime_DDHReduction_profiled
        (F := F) (G := G) (gen := gen) (ω := ω) (κ := κ) intrinsic profile adv g A B T)
      (OneTimeINDCPACapability.reductionTransform intrinsic profile) := by
  letI := (oneTimeINDCPARuntime (gen := gen) adv).toHasQuery
  simpa [IND_CPA_OneTime_DDHReduction_profiled] using
    (IND_CPA_OneTime_DDHReduction_openProfiled_pathwiseHasCost
      (State := adv.State) (ω := ω) (κ := κ) intrinsic profile g A B T)

/-- The asymptotic model [`oneTimeDDHReductionCost`] matches the exact pathwise cost of the
instantiated DDH reduction when evaluated at the procedure-cost profile chosen for security
parameter `n`. -/
lemma IND_CPA_OneTime_DDHReduction_modeledCost_pathwiseHasCost
    {gen : G} {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (advCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProfile ω κ)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (n : ℕ) (g A B T : G) :
    AddWriterT.PathwiseHasCost
      (IND_CPA_OneTime_DDHReduction_profiled
        (F := F) (G := G) (gen := gen) (ω := ω) (κ := κ)
        intrinsic (advCost adv n) adv g A B T)
      (oneTimeDDHReductionCost (F := F) (G := G) (gen := gen) intrinsic advCost adv n) := by
  simpa [oneTimeDDHReductionCost] using
    (IND_CPA_OneTime_DDHReduction_profiled_pathwiseHasCost
      (F := F) (G := G) (gen := gen) (ω := ω) (κ := κ)
      intrinsic (advCost adv n) adv g A B T)

/-- Scalar-cost specialization of
[`IND_CPA_OneTime_DDHReduction_profiled_pathwiseHasCost`].

If the reified adversary procedures `chooseMessages` and `distinguish` are assigned scalar
intrinsic costs `chooseCost` and `distinguishCost`, then the whole reduction has exact pathwise
cost `intrinsic + chooseCost + distinguishCost`. -/
lemma IND_CPA_OneTime_DDHReduction_intrinsicProfile_pathwiseHasCost
    {gen : G} {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic chooseCost distinguishCost : ω)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (g A B T : G) :
    AddWriterT.PathwiseHasCost
      (IND_CPA_OneTime_DDHReduction_profiled
        (F := F) (G := G) (gen := gen) (ω := ω) (κ := κ)
        intrinsic
        (fun
          | OneTimeINDCPACapability.chooseMessages =>
              ResourceProfile.ofIntrinsic (κ := κ) chooseCost
          | OneTimeINDCPACapability.distinguish =>
              ResourceProfile.ofIntrinsic (κ := κ) distinguishCost)
        adv g A B T)
      (ResourceProfile.ofIntrinsic (κ := κ) (intrinsic + chooseCost + distinguishCost)) := by
  simpa [OneTimeINDCPACapability.reductionTransform_ofIntrinsic, add_assoc] using
    (IND_CPA_OneTime_DDHReduction_profiled_pathwiseHasCost
      (F := F) (G := G) (gen := gen) (ω := ω) (κ := κ)
      intrinsic
      (fun
        | OneTimeINDCPACapability.chooseMessages =>
            ResourceProfile.ofIntrinsic (κ := κ) chooseCost
        | OneTimeINDCPACapability.distinguish =>
            ResourceProfile.ofIntrinsic (κ := κ) distinguishCost)
      adv g A B T)

/-- Cost-aware reduction packaging for the one-time ElGamal DDH reduction.

The source cost object is a two-procedure adversary profile, and the target cost object is the
closed reduction cost obtained by instantiating the open reduction transform with that profile. -/
noncomputable def oneTimeDDHReductionWithCost
    {gen : G} {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (advCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProfile ω κ) :
    SecurityGame.ReductionWithCost advCost
      (oneTimeDDHReductionCost (F := F) (G := G) (gen := gen) intrinsic advCost) where
  reduce := id
  transform _ profile := OneTimeINDCPACapability.reductionTransform intrinsic profile
  monotone_transform _ := OneTimeINDCPACapability.monotone_reductionTransform intrinsic
  cost_bound _ _ := by simp [oneTimeDDHReductionCost, OneTimeINDCPACapability.reductionTransform_eq]

/-- Image lemma for the one-time ElGamal DDH reduction at the level of asymptotic cost classes. -/
theorem efficientFor_oneTimeDDHReduction
    {gen : G} {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (advCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProfile ω κ)
    {isEff : (ℕ → OneTimeINDCPAProfile ω κ) → Prop}
    {isEff' : (ℕ → ResourceProfile ω κ) → Prop}
    {adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)}
    (hadv : SecurityGame.EfficientFor advCost isEff adv)
    (hmap : ∀ bound, isEff bound →
      isEff' (fun n ↦ OneTimeINDCPACapability.reductionTransform intrinsic (bound n))) :
    SecurityGame.EfficientFor
      (oneTimeDDHReductionCost (F := F) (G := G) (gen := gen) intrinsic advCost)
      isEff' adv := by
  refine
    SecurityGame.ReductionWithCost.efficientFor_image
      (R := oneTimeDDHReductionWithCost (F := F) (G := G) (gen := gen) intrinsic advCost)
      hadv ?_
  intro bound hbound
  simpa [oneTimeDDHReductionWithCost] using hmap bound hbound

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
    (IND_CPA_OneTime_DDHReduction_profiled_pathwiseHasCost
      (F := F) (G := G) (gen := gen) (ω := ω) (κ := OneTimeINDCPACapability)
      intrinsic (fun k ↦ ResourceProfile.single (ω := ω) k) adv g A B T)

end IND_CPA

end elGamalAsymmEnc
