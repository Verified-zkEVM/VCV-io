/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.IND_CPA.Oracle
import VCVio.CryptoFoundations.AsymmEncAlg.IND_CPA.OneTime

/-!
# Asymmetric Encryption Schemes: Generic IND-CPA Lifts

This file contains the generic step-adversary extraction and the planned one-time-to-many-time
IND-CPA lift.
-/

open OracleSpec OracleComp ENNReal

universe u v w

namespace AsymmEncAlg

variable {M PK SK C : Type}

section MultiQueryToOneTime

variable [DecidableEq M] [DecidableEq C]
variable {encAlg' : AsymmEncAlg ProbComp M PK SK C} [Inhabited M]

/-- Result of running the generic step-adversary prefix simulation. Either the oracle adversary
has already terminated, or we have paused exactly at the target fresh LR query and captured the
messages plus the continuation waiting for the challenge ciphertext. -/
private inductive IND_CPA_StepResult (α : Type)
  | done (a : α) : IND_CPA_StepResult α
  | paused (mm : M × M) (cont : C → OracleComp encAlg'.IND_CPA_oracleSpec α) :
      IND_CPA_StepResult α

/-- Prefix simulation for the generic step adversary. Starting from counter value `n ≤ k`, it
answers the first `k - n` fresh LR queries with the left branch, stops at the next fresh LR
query, and records the continuation. -/
private def IND_CPA_stepPrefix
    (pk : PK) (k : ℕ) {α : Type} :
    OracleComp encAlg'.IND_CPA_oracleSpec α →
      StateT encAlg'.IND_CPA_CountedState ProbComp (IND_CPA_StepResult (encAlg' := encAlg') α) :=
  OracleComp.construct
    (C := fun (_ : OracleComp encAlg'.IND_CPA_oracleSpec α) =>
      StateT encAlg'.IND_CPA_CountedState ProbComp
        (IND_CPA_StepResult (encAlg' := encAlg') α))
    (fun a => pure (.done a))
    (fun t oa rec => by
      cases t with
      | inl tu =>
          exact do
            let u ← liftM (query (spec := unifSpec) tu)
            rec u
      | inr mm =>
          exact do
            let st ← get
            match st.1 mm with
            | some c => rec c
            | none =>
                if hlt : st.2 < k then
                  let c ← liftM (encAlg'.encrypt pk mm.1)
                  let cache' := st.1.cacheQuery mm c
                  set (cache', st.2 + 1)
                  rec c
                else
                  pure (.paused mm oa))

/-- State carried by the generic extracted one-time adversary for the `k`-th adjacent hybrid
gap. If the original oracle adversary already terminated before issuing the target fresh query,
we store its final guess. Otherwise we store the paused continuation and counted cache state. -/
private inductive IND_CPA_StepState
  | done (guess : Bool) : IND_CPA_StepState
  | paused (pk : PK) (mm : M × M) (st : encAlg'.IND_CPA_CountedState)
      (cont : C → OracleComp encAlg'.IND_CPA_oracleSpec Bool) : IND_CPA_StepState

/-- Generic extraction of the one-time adversary for the `k`-th fresh LR query. -/
def IND_CPA_stepAdversary
    (adversary : encAlg'.IND_CPA_adversary) (k : ℕ) : IND_CPA_Adv encAlg' where
  State := IND_CPA_StepState (encAlg' := encAlg')
  chooseMessages pk := do
    let ⟨res, st⟩ ← (IND_CPA_stepPrefix (encAlg' := encAlg') pk k (adversary pk)).run (∅, 0)
    match res with
    | .done guess => pure (default, default, .done guess)
    | .paused mm cont => pure (mm.1, mm.2, .paused pk mm st cont)
  distinguish state c := do
    match state with
    | .done guess => pure guess
    | .paused pk mm st cont =>
        let st' := (st.1.cacheQuery mm c, st.2 + 1)
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c)).run' st'

/-- Planned semantic bridge: resuming the paused prefix simulation with the chosen branch should
match the corresponding counted LR hybrid on the same sample space. This is the core local
decomposition lemma needed for the generic step-adversary proof. -/
private lemma IND_CPA_stepPrefix_resume_eq_hybridLR
    (pk : PK) (k : ℕ) (branch : Bool) {α : Type}
    (oa : OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState)
    (hst : st.2 ≤ k) :
    evalDist
      (do
        let ⟨res, st'⟩ ← (IND_CPA_stepPrefix (encAlg' := encAlg') pk k oa).run st
        match res with
        | .done a => pure a
        | .paused mm cont =>
            let c ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
            let st'' := (st'.1.cacheQuery mm c, st'.2 + 1)
            (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c)).run' st'') =
      evalDist
        ((simulateQ
            (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (if branch then k + 1 else k))
            oa).run' st) := by
  sorry

/-- Planned game-level bridge for the extracted step adversary: its one-time IND-CPA game is the
uniform-bit branch between adjacent LR hybrids. This is the theorem that converts the local prefix
decomposition above into a clean hybrid-gap statement. -/
private lemma IND_CPA_stepAdversary_game_eq_hybridBranch
    (adversary : encAlg'.IND_CPA_adversary) (k : ℕ) :
    evalDist
      (IND_CPA_OneTime_Game_ProbComp (encAlg := encAlg')
        (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k)) =
      evalDist
        (do
          let bit ← ($ᵗ Bool : ProbComp Bool)
          let z ← if bit then encAlg'.IND_CPA_LR_hybridGame adversary (k + 1)
                   else encAlg'.IND_CPA_LR_hybridGame adversary k
          pure (bit == z)) := by
  sorry

end MultiQueryToOneTime

section MultiQueryHybridLift

variable [DecidableEq M] [DecidableEq C]
variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

/-- Planned adjacent-gap characterization for the extracted step adversary. Once
`IND_CPA_stepAdversary_game_eq_hybridBranch` is proved, this is just the one-time analogue of
`IND_CPA_signedAdvantageReal_eq_lrDiff_half`. -/
theorem IND_CPA_stepAdversary_signedAdvantageReal_eq_hybridDiff_half
    [Inhabited M] [DecidableEq C]
    (adversary : encAlg'.IND_CPA_adversary) (k : ℕ) :
    IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg')
      (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k) =
      ((Pr[= true | encAlg'.IND_CPA_LR_hybridGame adversary (k + 1)]).toReal -
        (Pr[= true | encAlg'.IND_CPA_LR_hybridGame adversary k]).toReal) / 2 := by
  -- Proof plan:
  -- 1. rewrite the one-time game via `IND_CPA_stepAdversary_game_eq_hybridBranch`
  -- 2. apply `probOutput_uniformBool_branch_toReal_sub_half`
  -- 3. simplify the branch order to the stated adjacent hybrid difference
  sorry

/-- Planned generic one-time-to-many-time lift: bounded multi-query IND-CPA advantage is at most
the sum of the extracted one-time signed advantages over the first `q` fresh LR queries. -/
theorem IND_CPA_advantage_toReal_le_sum_step_signedAdvantageReal_abs
    [Inhabited M] [DecidableEq C]
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ)
    (hq : adversary.MakesAtMostQueries q) :
    (IND_CPA_advantage (encAlg := encAlg') adversary).toReal ≤
      Finset.sum (Finset.range q) (fun k =>
        |IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg')
          (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k)|) := by
  -- Proof plan:
  -- 1. bound `IND_CPA_advantage.toReal` by `|IND_CPA_signedAdvantageReal|`
  -- 2. rewrite the signed real advantage as half the LR endpoint gap
  -- 3. telescope across the LR hybrid family using the bounded endpoint theorem
  -- 4. replace each adjacent hybrid gap by the corresponding step-adversary signed advantage
  -- 5. finish by triangle inequality
  sorry

/-- Planned uniform corollary of the generic lift. If every extracted one-time adversary has
signed real advantage at most `ε`, then any `q`-query oracle adversary has IND-CPA advantage at
most `q * ε`. -/
theorem IND_CPA_advantage_toReal_le_q_mul_of_oneTime_signedAdvantageReal_bound
    [Inhabited M] [DecidableEq C]
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ) (ε : ℝ)
    (hq : adversary.MakesAtMostQueries q) (hε : 0 ≤ ε)
    (hstep : ∀ adv : IND_CPA_Adv encAlg',
      |IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg') adv| ≤ ε) :
    (IND_CPA_advantage (encAlg := encAlg') adversary).toReal ≤ q * ε := by
  -- Proof plan:
  -- 1. apply `IND_CPA_advantage_toReal_le_sum_step_signedAdvantageReal_abs`
  -- 2. bound each summand with `hstep`
  -- 3. simplify the resulting finite sum to `q * ε`
  sorry

end MultiQueryHybridLift

end AsymmEncAlg
