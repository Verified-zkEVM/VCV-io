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

/-- Cost transform induced by the open one-time ElGamal DDH reduction body. -/
noncomputable def reductionTransform {ω κ : Type} [AddCommMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ) :
    ResourceProfile ω κ :=
  (reductionProfile intrinsic).instantiate profile

@[simp] lemma reductionTransform_eq {ω κ : Type} [AddCommMonoid ω]
    (intrinsic : ω) (profile : OneTimeINDCPACapability → ResourceProfile ω κ) :
    reductionTransform intrinsic profile =
      ResourceProfile.ofIntrinsic (κ := κ) intrinsic
        + profile chooseMessages
        + profile distinguish := by
  simp [reductionTransform, reductionProfile, add_assoc]

@[simp] lemma instantiate_reductionTransform {ω κ κ' : Type} [AddCommMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ)
    (impl : κ → ResourceProfile ω κ') :
    (reductionTransform intrinsic profile).instantiate impl =
      reductionTransform intrinsic (fun k ↦ (profile k).instantiate impl) := by
  simp [reductionTransform, ResourceProfile.instantiate_assoc]

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
        | .chooseMessages => ResourceProfile.ofIntrinsic (κ := κ) chooseCost
        | .distinguish => ResourceProfile.ofIntrinsic (κ := κ) distinguishCost) =
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
structure OneTimeINDCPAProcedureCost (ω κ : Type) where
  chooseMessages : ResourceProfile ω κ
  distinguish : ResourceProfile ω κ

namespace OneTimeINDCPAProcedureCost

variable {ω κ : Type}

/-- Convert the two-field adversary procedure cost object into the capability-indexed profile used
to instrument the open reduction body. -/
def toProfile (cost : OneTimeINDCPAProcedureCost ω κ) :
    OneTimeINDCPACapability → ResourceProfile ω κ
  | .chooseMessages => cost.chooseMessages
  | .distinguish => cost.distinguish

@[simp] lemma toProfile_chooseMessages (cost : OneTimeINDCPAProcedureCost ω κ) :
    cost.toProfile .chooseMessages = cost.chooseMessages := rfl

@[simp] lemma toProfile_distinguish (cost : OneTimeINDCPAProcedureCost ω κ) :
    cost.toProfile .distinguish = cost.distinguish := rfl

instance [LE (ResourceProfile ω κ)] : LE (OneTimeINDCPAProcedureCost ω κ) where
  le cost₁ cost₂ :=
    cost₁.chooseMessages ≤ cost₂.chooseMessages ∧ cost₁.distinguish ≤ cost₂.distinguish

instance [Preorder (ResourceProfile ω κ)] : Preorder (OneTimeINDCPAProcedureCost ω κ) where
  le_refl cost := ⟨le_rfl, le_rfl⟩
  le_trans cost₁ cost₂ cost₃ h₁₂ h₂₃ :=
    ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₁₂.2 h₂₃.2⟩

/-- Closed resource-profile transform induced by the one-time ElGamal DDH reduction. -/
noncomputable def reductionTransform {ω κ : Type} [AddCommMonoid ω]
    (intrinsic : ω)
    (cost : OneTimeINDCPAProcedureCost ω κ) :
    ResourceProfile ω κ :=
  OneTimeINDCPACapability.reductionTransform intrinsic cost.toProfile

@[simp] lemma reductionTransform_eq {ω κ : Type} [AddCommMonoid ω]
    (intrinsic : ω) (cost : OneTimeINDCPAProcedureCost ω κ) :
    reductionTransform intrinsic cost =
      ResourceProfile.ofIntrinsic (κ := κ) intrinsic
        + cost.chooseMessages
        + cost.distinguish := by
  simp [reductionTransform, OneTimeINDCPACapability.reductionTransform_eq]

/-- The ElGamal reduction transform is monotone in the procedure-cost object assigned to the
source adversary. -/
lemma monotone_reductionTransform {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω]
    [IsOrderedAddMonoid ω] (intrinsic : ω) :
    Monotone (reductionTransform (κ := κ) intrinsic) := by
  intro cost₁ cost₂ hcost
  rw [reductionTransform_eq, reductionTransform_eq]
  simpa [add_assoc, add_left_comm, add_comm] using
    add_le_add_left (add_le_add hcost.1 hcost.2)
      (ResourceProfile.ofIntrinsic (κ := κ) intrinsic)

end OneTimeINDCPAProcedureCost

/-- Assemble the asymptotic procedure costs of a one-time IND-CPA adversary into a single
two-field cost object recording the `chooseMessages` and `distinguish` procedure bounds. -/
def oneTimeINDCPAProcedureCostModel
    {gen : G} {ω κ : Type}
    (chooseCost distinguishCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → ResourceProfile ω κ) :
    AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProcedureCost ω κ :=
  fun adv n => ⟨chooseCost adv n, distinguishCost adv n⟩

/-- Cost model for the DDH reduction obtained by instantiating the open reduction transform with
the asymptotic procedure-cost profile of the source adversary. -/
noncomputable def oneTimeDDHReductionCost
    {gen : G} {ω κ : Type} [AddCommMonoid ω]
    (intrinsic : ω)
    (advCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProcedureCost ω κ) :
    AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → ResourceProfile ω κ :=
  fun adv n =>
    OneTimeINDCPAProcedureCost.reductionTransform intrinsic (advCost adv n)

/-- Closure of a target asymptotic cost class under the one-time ElGamal DDH reduction transform.

This is the hypothesis that whenever a source adversary has an admissible asymptotic bound on the
pair of procedure costs `(chooseMessages, distinguish)`, applying the reduction transform yields an
admissible asymptotic bound on the closed DDH reduction cost. -/
abbrev OneTimeDDHReductionClosedUnder
    {ω κ : Type} [AddCommMonoid ω] (intrinsic : ω)
    (isEff : (ℕ → OneTimeINDCPAProcedureCost ω κ) → Prop)
    (isEff' : (ℕ → ResourceProfile ω κ) → Prop) : Prop :=
  SecurityGame.CostClassMap isEff isEff'
    (fun _ cost ↦ OneTimeINDCPAProcedureCost.reductionTransform intrinsic cost)

/-- Open version of the one-time ElGamal DDH reduction body.

This is the usual DDH reduction, but written against the reified one-time IND-CPA adversary
interface instead of a concrete adversary structure. It samples the challenge bit internally and
uses the externally provided `chooseMessages` and `distinguish` procedures for the two adversary
phases.

**Design note on cost tracking.** Because the adversary queries are embedded via `HasQuery` rather
than as first-class `OracleComp` queries, `IsPerIndexQueryBound` cannot directly count them.
The cost accounting therefore uses `AddWriterT`-based instrumentation (see
`IND_CPA_OneTime_DDHReduction_openProfiled`), where `addTell` is placed at each query site and the
resulting pathwise cost is proved exact on support. The canonical cost theorem is
`IND_CPA_OneTime_DDHReduction_openProfiled_pathwiseCostEqOnSupport`. -/
def IND_CPA_OneTime_DDHReduction_open
    {State : Type} (_gen A B T : G)
    [HasQuery (oneTimeINDCPASpec G G State (G × G)) ProbComp] :
    ProbComp Bool := do
  let (m₁, m₂, st) ← HasQuery.query (spec := oneTimeINDCPASpec G G State (G × G))
    (.chooseMessages A)
  let bit ← ($ᵗ Bool)
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

/-- **Canonical cost theorem.** Every reachable execution of the open, resource-profile-instrumented
DDH reduction carries the same resource profile: the reduction's intrinsic overhead together with
the profiles assigned to `chooseMessages` and `distinguish`.

This theorem is intentionally phrased as exactness on support. If the reified adversary interface
has empty support, the reduction has no reachable executions, so the meaningful statement is that
all reachable paths, if any, incur the displayed profile.

All other cost theorems in this file (`_profiled_`, `_modeledCost_`, `_intrinsicProfile_`,
`_costed_`) are specializations of this result. -/
lemma IND_CPA_OneTime_DDHReduction_openProfiled_pathwiseCostEqOnSupport
    {State ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ)
    (g A B T : G)
    [HasQuery (oneTimeINDCPASpec G G State (G × G)) ProbComp] :
    AddWriterT.PathwiseCostEqOnSupport
      (IND_CPA_OneTime_DDHReduction_openProfiled
        (State := State) (ω := ω) (κ := κ) intrinsic profile g A B T)
      (OneTimeINDCPACapability.reductionTransform intrinsic profile) := by
  unfold IND_CPA_OneTime_DDHReduction_openProfiled
  have h :
      AddWriterT.PathwiseCostEqOnSupport
        ((do
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
          pure (bit == bit')) :
          AddWriterT (ResourceProfile ω κ) ProbComp Bool)
        (ResourceProfile.ofIntrinsic (κ := κ) intrinsic +
          (profile OneTimeINDCPACapability.chooseMessages +
            profile OneTimeINDCPACapability.distinguish)) := by
    refine AddWriterT.pathwiseCostEqOnSupport_bind
      (m := ProbComp)
      (ω := ResourceProfile ω κ)
      (w₁ := ResourceProfile.ofIntrinsic (κ := κ) intrinsic)
      (w₂ := profile OneTimeINDCPACapability.chooseMessages +
        profile OneTimeINDCPACapability.distinguish)
      ?_ (fun _ ↦ ?_)
    · exact AddWriterT.pathwiseCostEqOnSupport_addTell
        (m := ProbComp)
        (ResourceProfile.ofIntrinsic (κ := κ) intrinsic)
    · refine AddWriterT.pathwiseCostEqOnSupport_bind
        (m := ProbComp)
        (ω := ResourceProfile ω κ)
        (w₁ := profile OneTimeINDCPACapability.chooseMessages)
        (w₂ := profile OneTimeINDCPACapability.distinguish)
        ?_ (fun _ ↦ ?_)
      · exact AddWriterT.pathwiseCostEqOnSupport_addTell
          (m := ProbComp)
          (profile OneTimeINDCPACapability.chooseMessages)
      · refine AddWriterT.pathwiseCostEqOnSupport_bind_zero_left
          (m := ProbComp)
          (ω := ResourceProfile ω κ)
          ?_ (fun msgs ↦ ?_)
        · exact AddWriterT.pathwiseCostEqOnSupport_probCompLift
            (m := ProbComp)
            (ω := ResourceProfile ω κ)
            (x := HasQuery.query
              (spec := oneTimeINDCPASpec G G State (G × G))
              (m := ProbComp)
              (.chooseMessages A))
        · rcases msgs with ⟨m₁, m₂, st⟩
          refine AddWriterT.pathwiseCostEqOnSupport_bind_zero_left
            (m := ProbComp)
            (ω := ResourceProfile ω κ)
            ?_ (fun bit ↦ ?_)
          · exact AddWriterT.pathwiseCostEqOnSupport_probCompLift
              (m := ProbComp)
              (ω := ResourceProfile ω κ)
              (x := ($ᵗ Bool))
          · refine AddWriterT.pathwiseCostEqOnSupport_bind_zero_right
              (m := ProbComp)
              (ω := ResourceProfile ω κ)
              ?_ (fun _ ↦ by
                let c : G × G := (B, T + if bit then m₁ else m₂)
                refine AddWriterT.pathwiseCostEqOnSupport_bind_zero_left
                  (m := ProbComp)
                  (ω := ResourceProfile ω κ)
                  ?_ (fun bit' ↦ ?_)
                · exact AddWriterT.pathwiseCostEqOnSupport_probCompLift
                    (m := ProbComp)
                    (ω := ResourceProfile ω κ)
                    (x := HasQuery.query
                      (spec := oneTimeINDCPASpec G G State (G × G))
                      (m := ProbComp)
                      (.distinguish st c))
                · exact AddWriterT.pathwiseCostEqOnSupport_pure
                    (m := ProbComp)
                    (ω := ResourceProfile ω κ)
                    (bit == bit'))
            · exact AddWriterT.pathwiseCostEqOnSupport_addTell
                (m := ProbComp)
                (profile OneTimeINDCPACapability.distinguish)
  rw [OneTimeINDCPACapability.reductionTransform_eq]
  simpa only [add_assoc] using h

/-- The symbolic capability-counting theorem is the specialization of
[`IND_CPA_OneTime_DDHReduction_openProfiled_pathwiseCostEqOnSupport`].
Each capability is charged by its own singleton resource profile. -/
lemma IND_CPA_OneTime_DDHReduction_openCost_pathwiseCostEqOnSupport
    {State ω : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω) (g A B T : G)
    [HasQuery (oneTimeINDCPASpec G G State (G × G)) ProbComp] :
    AddWriterT.PathwiseCostEqOnSupport
      (IND_CPA_OneTime_DDHReduction_openCost
        (State := State) (ω := ω) intrinsic g A B T)
      (OneTimeINDCPACapability.reductionProfile intrinsic) := by
  simpa [IND_CPA_OneTime_DDHReduction_openCost] using
    (IND_CPA_OneTime_DDHReduction_openProfiled_pathwiseCostEqOnSupport
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
      = IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv g A B T := rfl

/-- Cost-transform theorem for the closed one-time ElGamal DDH reduction.

If `profile` assigns resource profiles to the two adversary capabilities `chooseMessages` and
`distinguish`, then the instantiated reduction has exact pathwise cost equal to the reduction
transform applied to those capability profiles. -/
lemma IND_CPA_OneTime_DDHReduction_profiled_pathwiseCostEqOnSupport
    {gen : G} {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (profile : OneTimeINDCPACapability → ResourceProfile ω κ)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (g A B T : G) :
    AddWriterT.PathwiseCostEqOnSupport
      (IND_CPA_OneTime_DDHReduction_profiled
        (F := F) (G := G) (gen := gen) (ω := ω) (κ := κ) intrinsic profile adv g A B T)
      (OneTimeINDCPACapability.reductionTransform intrinsic profile) := by
  letI := (oneTimeINDCPARuntime (gen := gen) adv).toHasQuery
  simpa [IND_CPA_OneTime_DDHReduction_profiled] using
    (IND_CPA_OneTime_DDHReduction_openProfiled_pathwiseCostEqOnSupport
      (State := adv.State) (ω := ω) (κ := κ) intrinsic profile g A B T)

/-- The asymptotic model [`oneTimeDDHReductionCost`] matches the exact pathwise cost.
Immediate from `IND_CPA_OneTime_DDHReduction_profiled_pathwiseCostEqOnSupport`. -/
lemma IND_CPA_OneTime_DDHReduction_modeledCost_pathwiseCostEqOnSupport
    {gen : G} {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (advCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProcedureCost ω κ)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (n : ℕ) (g A B T : G) :
    AddWriterT.PathwiseCostEqOnSupport
      (IND_CPA_OneTime_DDHReduction_profiled
        (F := F) (G := G) (gen := gen) (ω := ω) (κ := κ)
        intrinsic (advCost adv n).toProfile adv g A B T)
      (oneTimeDDHReductionCost (F := F) (G := G) (gen := gen) intrinsic advCost adv n) := by
  simpa [oneTimeDDHReductionCost] using
    IND_CPA_OneTime_DDHReduction_profiled_pathwiseCostEqOnSupport
      (F := F) (G := G) (gen := gen) (ω := ω) (κ := κ)
      intrinsic (advCost adv n).toProfile adv g A B T

/-- Scalar-cost specialization: when both procedures have pure-intrinsic costs, the total
pathwise cost collapses to `intrinsic + chooseCost + distinguishCost`.
Immediate from `IND_CPA_OneTime_DDHReduction_profiled_pathwiseCostEqOnSupport`. -/
lemma IND_CPA_OneTime_DDHReduction_intrinsicProfile_pathwiseCostEqOnSupport
    {gen : G} {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic chooseCost distinguishCost : ω)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (g A B T : G) :
    AddWriterT.PathwiseCostEqOnSupport
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
    IND_CPA_OneTime_DDHReduction_profiled_pathwiseCostEqOnSupport
      (F := F) (G := G) (gen := gen) (ω := ω) (κ := κ)
      intrinsic
      (fun
        | OneTimeINDCPACapability.chooseMessages =>
            ResourceProfile.ofIntrinsic (κ := κ) chooseCost
        | OneTimeINDCPACapability.distinguish =>
            ResourceProfile.ofIntrinsic (κ := κ) distinguishCost)
      adv g A B T

/-- Cost-aware reduction packaging for the one-time ElGamal DDH reduction.

For each security parameter `n`, the source cost object is a profile assigning one resource bound
to `chooseMessages` and one resource bound to `distinguish`. The target cost object is the closed
resource profile of the DDH reduction obtained by plugging that two-procedure profile into
[`OneTimeINDCPACapability.reductionTransform`].

Operationally, this packages the statement that the one-time ElGamal DDH reduction contributes its
own intrinsic overhead and makes exactly one call to each adversary procedure. The adversary map is
`id` because this declaration isolates only the cost-transform part of the reduction theorem; the
same extracted one-time adversary is viewed through a different cost model on the target side. -/
noncomputable def oneTimeDDHReductionWithCost
    {gen : G} {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (advCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProcedureCost ω κ) :
    SecurityGame.ReductionWithCost advCost
      (oneTimeDDHReductionCost (F := F) (G := G) (gen := gen) intrinsic advCost) where
  reduce := id
  transform _ cost := OneTimeINDCPAProcedureCost.reductionTransform intrinsic cost
  monotone_transform _ := OneTimeINDCPAProcedureCost.monotone_reductionTransform intrinsic
  cost_bound _ _ := by simp [oneTimeDDHReductionCost]

/-- Efficiency preservation for the one-time ElGamal DDH reduction.

Assume `adv` is efficient with respect to a source class `isEff` of asymptotic procedure-cost
bounds. Concretely, this means that for each security parameter `n`, there is a bound on the cost
of `adv.chooseMessages` and a bound on the cost of `adv.distinguish`, packaged together as a value
of [`OneTimeINDCPAProcedureCost`].

Assume also that [`OneTimeDDHReductionClosedUnder`] holds for `intrinsic`, `isEff`, and `isEff'`.
In concrete terms, this says that the target class `isEff'` is closed under the ElGamal reduction
transform, which adds the reduction's own intrinsic overhead `intrinsic` and then charges one use
of the `chooseMessages` bound and one use of the `distinguish` bound.

Then the DDH reduction built from `adv` is efficient with respect to the closed cost model
[`oneTimeDDHReductionCost`]. This is the cost side of the usual cryptographic reduction claim:
an efficient IND-CPA adversary induces an efficient DDH adversary, with explicit accounting for
how the reduction transforms adversary runtime. -/
theorem efficientFor_oneTimeDDHReduction
    {gen : G} {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (advCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProcedureCost ω κ)
    {isEff : (ℕ → OneTimeINDCPAProcedureCost ω κ) → Prop}
    {isEff' : (ℕ → ResourceProfile ω κ) → Prop}
    {adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)}
    (hadv : SecurityGame.EfficientFor advCost isEff adv)
    (hmap : OneTimeDDHReductionClosedUnder intrinsic isEff isEff') :
    SecurityGame.EfficientFor
      (oneTimeDDHReductionCost (F := F) (G := G) (gen := gen) intrinsic advCost)
      isEff' adv := by
  have hmap' :
      SecurityGame.CostClassMap isEff isEff'
        (oneTimeDDHReductionWithCost
          (F := F) (G := G) (gen := gen) intrinsic advCost).transform := by
    simpa [oneTimeDDHReductionWithCost, OneTimeDDHReductionClosedUnder] using hmap
  refine
    SecurityGame.ReductionWithCost.efficientFor_image
      (R := oneTimeDDHReductionWithCost (F := F) (G := G) (gen := gen) intrinsic advCost)
      hadv hmap'

/-- Asymptotic one-time IND-CPA security game for ElGamal, viewed over the reified one-time
adversary type.

The security parameter is ignored because the underlying one-time game is parameter-free; it is
retained only so the declaration fits the generic [`SecurityGame`] interface. -/
noncomputable def oneTimeINDCPASecurityGame
    {gen : G} [DecidableEq G] :
    SecurityGame (AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) where
  advantage adv _ :=
    ENNReal.ofReal <|
      |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (encAlg := elGamalAsymmEnc F G gen) adv|

/-- Asymptotic DDH security game induced by the one-time ElGamal reduction, still indexed by the
source one-time adversary type.

This packages the target-side game that appears in the ElGamal reduction proof:
apply the one-time IND-CPA adversary to the concrete DDH reduction
[`IND_CPA_OneTime_DDHReduction`] and measure the resulting DDH distinguishing advantage. -/
noncomputable def oneTimeDDHReductionSecurityGame
    {gen : G} [DecidableEq G] :
    SecurityGame (AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) where
  advantage adv _ :=
    ENNReal.ofReal <|
      DiffieHellman.ddhDistAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)

/-- The one-time ElGamal IND-CPA game and the DDH reduction game have the same asymptotic
advantage function. This is the security-side analogue of the exact reduction theorem from
`Examples.ElGamal.Basic`. -/
lemma oneTimeINDCPASecurityGame_advantage_eq_oneTimeDDHReductionSecurityGame_advantage
    {gen : G} [DecidableEq G]
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (n : ℕ) :
    (oneTimeINDCPASecurityGame (F := F) (G := G) (gen := gen)).advantage adv n =
      (oneTimeDDHReductionSecurityGame (F := F) (G := G) (gen := gen)).advantage adv n := by
  apply congrArg ENNReal.ofReal
  calc
    |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (encAlg := elGamalAsymmEnc F G gen) adv| =
      2 * DiffieHellman.ddhGuessAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) :=
          elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage
            (F := F) (G := G) (gen := gen) hg adv
    _ =
      DiffieHellman.ddhDistAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) := by
          symm
          exact DiffieHellman.ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage
            (F := F) (g := gen)
            (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)

/-- Cost-aware security reduction for the one-time ElGamal DDH argument.

If the DDH reduction game is secure against adversaries whose transformed cost profiles lie in the
target class `isEff'`, and if `isEff'` is closed under the ElGamal reduction transform, then the
one-time IND-CPA game is secure against adversaries whose two-procedure cost profiles lie in the
source class `isEff`.

The bijectivity hypothesis `hg` is the same group-theoretic assumption used in the underlying
one-time ElGamal DDH proof from `Examples.ElGamal.Basic`: it identifies uniform scalar samples
with uniform samples from the subgroup generated by `gen`, which is what makes the random DDH
branch perfectly hide the challenge bit. -/
theorem oneTimeINDCPA_secureAgainst_of_ddh_secureAgainst_withCost
    {gen : G} [DecidableEq G]
    {ω κ : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (hg : Function.Bijective (· • gen : F → G))
    (intrinsic : ω)
    (advCost :
      AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen) → ℕ → OneTimeINDCPAProcedureCost ω κ)
    {isEff : (ℕ → OneTimeINDCPAProcedureCost ω κ) → Prop}
    {isEff' : (ℕ → ResourceProfile ω κ) → Prop}
    (hmap : OneTimeDDHReductionClosedUnder intrinsic isEff isEff')
    (hsecure :
      (oneTimeDDHReductionSecurityGame (F := F) (G := G) (gen := gen)).secureAgainst
        (SecurityGame.EfficientFor
          (oneTimeDDHReductionCost (F := F) (G := G) (gen := gen) intrinsic advCost) isEff')) :
    (oneTimeINDCPASecurityGame (F := F) (G := G) (gen := gen)).secureAgainst
      (SecurityGame.EfficientFor advCost isEff) := by
  refine SecurityGame.secureAgainst_of_reduction_withCost
    (R := oneTimeDDHReductionWithCost (F := F) (G := G) (gen := gen) intrinsic advCost)
    ?_ hmap hsecure
  intro adv n
  simpa using le_of_eq
    (oneTimeINDCPASecurityGame_advantage_eq_oneTimeDDHReductionSecurityGame_advantage
      (F := F) (G := G) (gen := gen) hg adv n)

/-- Instantiating the open costed reduction with a concrete adversary preserves the exact pathwise
resource profile proved for the open reduction body.
Immediate from `IND_CPA_OneTime_DDHReduction_profiled_pathwiseCostEqOnSupport`. -/
lemma IND_CPA_OneTime_DDHReduction_costed_pathwiseCostEqOnSupport
    {gen : G} {ω : Type} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    (intrinsic : ω)
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (g A B T : G) :
    AddWriterT.PathwiseCostEqOnSupport
      (IND_CPA_OneTime_DDHReduction_costed
        (F := F) (G := G) (gen := gen) (ω := ω) intrinsic adv g A B T)
      (OneTimeINDCPACapability.reductionProfile intrinsic) := by
  letI := (oneTimeINDCPARuntime (gen := gen) adv).toHasQuery
  simpa [IND_CPA_OneTime_DDHReduction_costed] using
    (IND_CPA_OneTime_DDHReduction_profiled_pathwiseCostEqOnSupport
      (F := F) (G := G) (gen := gen) (ω := ω) (κ := OneTimeINDCPACapability)
      intrinsic (fun k ↦ ResourceProfile.single (ω := ω) k) adv g A B T)

end IND_CPA

end elGamalAsymmEnc
