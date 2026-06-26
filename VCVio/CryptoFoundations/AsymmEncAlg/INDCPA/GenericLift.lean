/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.Oracle
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime
import ToMathlib.Control.StateT

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

variable [DecidableEq M]
variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

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
private def IND_CPA_stepPrefix (pk : PK) (k : ℕ) {α : Type} :
    OracleComp encAlg'.IND_CPA_oracleSpec α →
      StateT encAlg'.IND_CPA_CountedState ProbComp (IND_CPA_StepResult (encAlg' := encAlg') α) :=
  OracleComp.construct
    (C := fun (_ : OracleComp encAlg'.IND_CPA_oracleSpec α) =>
      StateT encAlg'.IND_CPA_CountedState ProbComp
        (IND_CPA_StepResult (encAlg' := encAlg') α))
    (fun a => pure (.done a))
    (fun t oa rec =>
      match t with
      | .inl tu => do rec (←$[0..tu])
      | .inr mm =>
          do
            let st ← get
            match st.1 mm with
            | some c => rec c
            | none =>
                if st.2 < k then
                  let c ← encAlg'.encrypt pk mm.1
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
def IND_CPA_stepAdversary [Inhabited M] (adversary : encAlg'.IND_CPA_adversary) (k : ℕ) :
    IND_CPA_Adv encAlg' where
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

/-- Unfold `IND_CPA_stepPrefix` on a pure computation. -/
private lemma IND_CPA_stepPrefix_pure (pk : PK) (k : ℕ) {α : Type} (a : α) :
    IND_CPA_stepPrefix (encAlg' := encAlg') pk k (pure a) = pure (.done a) := rfl

/-- Unfold `IND_CPA_stepPrefix` through a query to the uniform side of the oracle spec. -/
private lemma IND_CPA_stepPrefix_query_inl (pk : PK) (k : ℕ) {α : Type} (tu : unifSpec.Domain)
    (mx : encAlg'.IND_CPA_oracleSpec.Range (Sum.inl tu) →
      OracleComp encAlg'.IND_CPA_oracleSpec α) :
    IND_CPA_stepPrefix (encAlg' := encAlg') pk k
        (encAlg'.IND_CPA_oracleSpec.query (Sum.inl tu) >>= mx) =
      (do
        let u ← $[0..tu]
        IND_CPA_stepPrefix (encAlg' := encAlg') pk k (mx u)) := rfl

/-- Unfold `IND_CPA_stepPrefix` through an LR challenge query. -/
private lemma IND_CPA_stepPrefix_query_inr (pk : PK) (k : ℕ) {α : Type} (mm : M × M)
    (mx : encAlg'.IND_CPA_oracleSpec.Range (Sum.inr mm) →
      OracleComp encAlg'.IND_CPA_oracleSpec α) :
    IND_CPA_stepPrefix (encAlg' := encAlg') pk k
        (encAlg'.IND_CPA_oracleSpec.query (Sum.inr mm) >>= mx) =
      (do
        let st ← get
        match st.1 mm with
        | some c =>
            IND_CPA_stepPrefix (encAlg' := encAlg') pk k (mx c)
        | none =>
            if st.2 < k then do
              let c ← (encAlg'.encrypt pk mm.1)
              let cache' := st.1.cacheQuery mm c
              set (cache', st.2 + 1)
              IND_CPA_stepPrefix (encAlg' := encAlg') pk k (mx c)
            else
              pure (.paused mm mx)) := rfl

/-- Once the counter has already crossed `k`, the `k` and `k + 1` counted hybrids agree. -/
private lemma IND_CPA_hybridLR_counted_run'_evalDist_eq_above (pk : PK) (k : ℕ) {α : Type}
    (oa : OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) (hst : k + 1 ≤ st.2) :
    𝒟[(simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) oa).run' st] =
      𝒟[(simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (k + 1)) oa).run' st] := by
  simp only [StateT.run', evalDist_map]
  exact congrArg (Prod.fst <$> ·) <| evalDist_ext fun z =>
    OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run_eq_of_impl_eq_preservesInv
      (impl₁ := encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k)
      (impl₂ := encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (k + 1))
      (Inv := fun s => k + 1 ≤ s.2) (oa := oa)
      (himpl_eq := IND_CPA_hybridLR_counted_run_eq_of_le (encAlg' := encAlg') pk k)
      (hpres₂ := fun t s hs z hz => by
        have := IND_CPA_hybridLR_counted_counter_le (encAlg' := encAlg') pk (k + 1) t s z hz
        omega)
      (s := st) (hs := hst) (z := z)

/-- Once the counter has already crossed `k`, the `k` and `if branch then k + 1 else k` counted
hybrids agree: when `branch` selects the higher index this is the adjacent-hybrid step, otherwise
both indices coincide. -/
private lemma IND_CPA_hybridLR_counted_run'_evalDist_eq_branch (pk : PK) (k : ℕ) (branch : Bool)
    {α : Type} (oa : OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) (hst : k + 1 ≤ st.2) :
    𝒟[(simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) oa).run' st] =
      𝒟[(simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (if branch then k + 1 else k))
          oa).run' st] := by
  cases branch
  · rfl
  · exact IND_CPA_hybridLR_counted_run'_evalDist_eq_above (encAlg' := encAlg') pk k oa st hst

/-- Unfold one counted LR hybrid step on a uniform query, exposing the uniform sample followed by
the continuation run on the unchanged counted state. -/
private lemma IND_CPA_queryImpl_hybridLR_counted_run'_inl (pk : PK) (leftUntil : ℕ) {α : Type}
    (tu : unifSpec.Domain)
    (oa : encAlg'.IND_CPA_oracleSpec.Range (.inl tu) → OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) :
    (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
        (encAlg'.IND_CPA_oracleSpec.query (.inl tu) >>= oa)).run' st =
      (do
        let u ← ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu))
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)).run' st) := by
  have hrun :
      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
          (encAlg'.IND_CPA_oracleSpec.query (.inl tu) >>= oa)).run st =
        (($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu)) >>= fun u =>
          (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)).run st) := by
    rw [simulateQ_query_bind, StateT.run_bind]
    change
      (($ᵗ (unifSpec.Range tu) :
          StateT encAlg'.IND_CPA_CountedState ProbComp (unifSpec.Range tu)).run st >>= fun p =>
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa p.1)).run p.2) = _
    rw [StateT.run_liftM]
    simp
  rw [StateT.run'_eq, hrun]
  simp [StateT.run'_eq]

/-- Unfold one counted LR hybrid step on a fresh (cache-miss) LR query, exposing the encryption
of the selected branch followed by the continuation run on the incremented cache. -/
private lemma IND_CPA_queryImpl_hybridLR_counted_run'_inr_none (pk : PK) (leftUntil : ℕ) {α : Type}
    (mm : M × M) (oa : C → OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) (hcache : st.1 mm = none) :
    (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
        (encAlg'.IND_CPA_oracleSpec.query (.inr mm) >>= oa)).run' st =
      (do
        let c ← encAlg'.encrypt pk (if st.2 < leftUntil then mm.1 else mm.2)
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
          (oa c)).run' (st.1.cacheQuery mm c, st.2 + 1)) := by
  have hrun :
      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
          (encAlg'.IND_CPA_oracleSpec.query (.inr mm) >>= oa)).run st =
        (do
          let c ← encAlg'.encrypt pk (if st.2 < leftUntil then mm.1 else mm.2)
          (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
            (oa c)).run (st.1.cacheQuery mm c, st.2 + 1)) := by
    rw [simulateQ_query_bind, StateT.run_bind]
    change
      ((encAlg'.IND_CPA_hybridChallengeOracleLR_counted pk leftUntil mm).run st >>= fun u =>
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u.1)).run u.2) = _
    rw [IND_CPA_hybridChallengeOracleLR_counted_run_none (encAlg' := encAlg') pk leftUntil mm st
      hcache]
    simp
  rw [StateT.run'_eq, hrun]
  simp [StateT.run'_eq]

/-- Unfold one counted LR hybrid step on a cached (cache-hit) LR query: the cache is reused and the
continuation runs unchanged on the same state. -/
private lemma IND_CPA_queryImpl_hybridLR_counted_run'_inr_some (pk : PK) (leftUntil : ℕ) {α : Type}
    (mm : M × M) (c : C) (oa : C → OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) (hcache : st.1 mm = some c) :
    (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
        (encAlg'.IND_CPA_oracleSpec.query (.inr mm) >>= oa)).run' st =
      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa c)).run' st := by
  have hrun :
      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
          (encAlg'.IND_CPA_oracleSpec.query (.inr mm) >>= oa)).run st =
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa c)).run st := by
    rw [simulateQ_query_bind, StateT.run_bind]
    change
      ((encAlg'.IND_CPA_hybridChallengeOracleLR_counted pk leftUntil mm).run st >>= fun u =>
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u.1)).run u.2) = _
    rw [IND_CPA_hybridChallengeOracleLR_counted_run_some (encAlg' := encAlg') pk leftUntil mm c st
      hcache]
    rfl
  rw [StateT.run'_eq, hrun]
  simp [StateT.run'_eq]

/-- Planned semantic bridge: resuming the paused prefix simulation with the chosen branch should
match the corresponding counted LR hybrid on the same sample space. This is the core local
decomposition lemma needed for the generic step-adversary proof. -/
private lemma IND_CPA_stepPrefix_resume_eq_hybridLR (pk : PK) (k : ℕ) (branch : Bool) {α : Type}
    (oa : OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) (hst : st.2 ≤ k) :
    𝒟[(do
        let ⟨res, st'⟩ ← (IND_CPA_stepPrefix (encAlg' := encAlg') pk k oa).run st
        match res with
        | .done a => pure a
        | .paused mm cont =>
            let c ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
            let st'' := (st'.1.cacheQuery mm c, st'.2 + 1)
            (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c)).run' st'')] =
      𝒟[(simulateQ
            (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (if branch then k + 1 else k))
            oa).run' st] := by
  revert st hst
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro st hst
      simp [IND_CPA_stepPrefix_pure]
  | query_bind t oa ih =>
      intro st hst
      cases t with
      | inl tu =>
          refine evalDist_ext fun x => ?_
          rw [IND_CPA_stepPrefix_query_inl, IND_CPA_queryImpl_hybridLR_counted_run'_inl
            (encAlg' := encAlg') pk (if branch then k + 1 else k) tu oa st]
          simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
          exact probOutput_bind_congr' ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu)) x
            fun u => (evalDist_ext_iff.mp (ih u st hst)) x
      | inr mm =>
          rcases hcache : st.1 mm with _ | c
          · by_cases hlt : st.2 < k
            · refine evalDist_ext fun x => ?_
              rw [IND_CPA_stepPrefix_query_inr]
              simp only [hcache, hlt, StateT.run_bind, StateT.run_get, StateT.run_set,
                ↓reduceIte, pure_bind, bind_assoc, StateT.run_liftM]
              rw [IND_CPA_queryImpl_hybridLR_counted_run'_inr_none (encAlg' := encAlg') pk
                  (if branch then k + 1 else k) mm oa st hcache,
                if_pos (show st.2 < if branch then k + 1 else k by cases branch <;> simp_all)]
              exact probOutput_bind_congr' (encAlg'.encrypt pk mm.1) x
                fun c => (evalDist_ext_iff.mp (ih c (st.1.cacheQuery mm c, st.2 + 1) (by omega))) x
            · have hEq : st.2 = k := by omega
              refine evalDist_ext fun x => ?_
              rw [IND_CPA_stepPrefix_query_inr]
              simp only [hcache, hlt, StateT.run_bind, StateT.run_get, StateT.run_pure,
                if_false, pure_bind]
              rw [IND_CPA_queryImpl_hybridLR_counted_run'_inr_none (encAlg' := encAlg') pk
                  (if branch then k + 1 else k) mm oa st hcache,
                show (if st.2 < if branch then k + 1 else k then mm.1 else mm.2) =
                  (if branch then mm.1 else mm.2) by cases branch <;> simp [hEq]]
              exact probOutput_bind_congr' (encAlg'.encrypt pk (if branch then mm.1 else mm.2)) x
                fun c => (evalDist_ext_iff.mp (IND_CPA_hybridLR_counted_run'_evalDist_eq_branch
                  (encAlg' := encAlg') pk k branch (oa c)
                  (st.1.cacheQuery mm c, st.2 + 1) (by omega))) x
          · refine evalDist_ext fun x => ?_
            rw [IND_CPA_stepPrefix_query_inr]
            simp only [hcache, StateT.run_bind, StateT.run_get, pure_bind]
            rw [IND_CPA_queryImpl_hybridLR_counted_run'_inr_some (encAlg' := encAlg') pk
              (if branch then k + 1 else k) mm c oa st hcache]
            exact (evalDist_ext_iff.mp (ih c st hst)) x

/-- Planned game-level bridge for the extracted step adversary: its one-time IND-CPA game is the
uniform-bit branch between adjacent LR hybrids. This is the theorem that converts the local prefix
decomposition above into a clean hybrid-gap statement. -/
private lemma IND_CPA_stepAdversary_game_eq_hybridBranch [Inhabited M]
    (adversary : encAlg'.IND_CPA_adversary) (k : ℕ) :
    𝒟[IND_CPA_OneTime_Game_ProbComp (encAlg := encAlg')
        (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k)] =
      𝒟[do
          let bit ← ($ᵗ Bool)
          let z ← if bit then encAlg'.IND_CPA_LR_hybridGame adversary (k + 1)
                   else encAlg'.IND_CPA_LR_hybridGame adversary k
          pure (bit == z)] := by
  refine evalDist_ext fun x => ?_
  refine probOutput_bind_congr' ($ᵗ Bool) x fun bit => ?_
  change Pr[= x | do
      let (pk, _sk) ← encAlg'.keygen
      let (m₁, m₂, state) ←
        (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k).chooseMessages pk
      let c ← encAlg'.encrypt pk (if bit then m₁ else m₂)
      let b' ← (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k).distinguish state c
      pure (bit == b')] =
    Pr[= x | do
      let z ← if bit then encAlg'.IND_CPA_LR_hybridGame adversary (k + 1)
               else encAlg'.IND_CPA_LR_hybridGame adversary k
      pure (bit == z)]
  simp only [IND_CPA_LR_hybridGame, monad_norm,
    ← apply_ite (f := fun g => encAlg'.keygen >>= g)]
  refine probOutput_bind_congr' encAlg'.keygen x fun pk_sk => ?_
  simp only [IND_CPA_stepAdversary, monad_norm,
    apply_ite (f := fun h : PK × SK → ProbComp Bool => h pk_sk),
    ← apply_ite (f := fun n => (do
      let b' ← (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk_sk.1 n)
        (adversary pk_sk.1)).run' (∅, 0)
      pure (bit == b') : ProbComp Bool))]
  change (𝒟[_]) x = (𝒟[_]) x
  congr 1
  have hresume := IND_CPA_stepPrefix_resume_eq_hybridLR (encAlg' := encAlg')
    pk_sk.1 k bit (adversary pk_sk.1) (∅, 0) (Nat.zero_le k)
  dsimp at hresume
  refine evalDist_ext fun y => ?_
  refine Eq.trans ?_ (probOutput_map_eq_of_evalDist_eq hresume (bit == ·) y)
  simp only [monad_norm]
  refine probOutput_bind_congr'
    ((IND_CPA_stepPrefix (encAlg' := encAlg') pk_sk.1 k (adversary pk_sk.1)).run (∅, 0)) y
    fun ⟨res, _st⟩ => ?_
  cases res <;> simp

end MultiQueryToOneTime

section MultiQueryHybridLift

variable [DecidableEq M]
variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

/-- Planned adjacent-gap characterization for the extracted step adversary. Once
`IND_CPA_stepAdversary_game_eq_hybridBranch` is proved, this is just the one-time analogue of
`IND_CPA_signedAdvantageReal_eq_lrDiff_half`. -/
theorem IND_CPA_stepAdversary_signedAdvantageReal_eq_hybridDiff_half
    [Inhabited M]
    (adversary : encAlg'.IND_CPA_adversary) (k : ℕ) :
    IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg')
      (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k) =
      ((Pr[= true | encAlg'.IND_CPA_LR_hybridGame adversary (k + 1)]).toReal -
        (Pr[= true | encAlg'.IND_CPA_LR_hybridGame adversary k]).toReal) / 2 := by
  unfold IND_CPA_OneTime_signedAdvantageReal
  rw [show
      (Pr[= true | IND_CPA_OneTime_Game_ProbComp (encAlg := encAlg')
        (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k)]).toReal =
      (Pr[= true | do
        let bit ← ($ᵗ Bool)
        let z ← if bit then encAlg'.IND_CPA_LR_hybridGame adversary (k + 1)
                 else encAlg'.IND_CPA_LR_hybridGame adversary k
        pure (bit == z)]).toReal from congrArg ENNReal.toReal <|
          (evalDist_ext_iff.mp
            (IND_CPA_stepAdversary_game_eq_hybridBranch (encAlg' := encAlg') adversary k)) true]
  exact probOutput_uniformBool_branch_toReal_sub_half
    (encAlg'.IND_CPA_LR_hybridGame adversary (k + 1))
    (encAlg'.IND_CPA_LR_hybridGame adversary k)

/-- Planned generic one-time-to-many-time lift: bounded multi-query IND-CPA advantage is at most
the sum of the extracted one-time signed advantages over the first `q` fresh LR queries. -/
theorem IND_CPA_advantage_toReal_le_sum_step_signedAdvantageReal_abs
    [Inhabited M] [Finite C] [Inhabited C]
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ)
    (hq : adversary.MakesAtMostQueries q) :
    (IND_CPA_advantage (encAlg := encAlg') adversary).toReal ≤
      Finset.sum (Finset.range q) (fun k =>
        |IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg')
          (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k)|) := by
  let H : ℕ → ℝ := fun i ↦ (Pr[= true | encAlg'.IND_CPA_LR_hybridGame adversary i]).toReal
  have hleft : (Pr[= true | encAlg'.IND_CPA_LR_experiment adversary true]).toReal = H q :=
    congrArg ENNReal.toReal
      (encAlg'.IND_CPA_LR_hybridGame_q_probOutput_eq_left_of_MakesAtMostQueries adversary q hq).symm
  have hright : (Pr[= true | encAlg'.IND_CPA_LR_experiment adversary false]).toReal = H 0 :=
    congrArg ENNReal.toReal (encAlg'.IND_CPA_LR_hybridGame_zero_probOutput_eq_right adversary).symm
  have htri : |H q - H 0| ≤ Finset.sum (Finset.range q) (fun i ↦ |H (i + 1) - H i|) := by
    rw [← Finset.sum_range_sub H q]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsteps : ∀ i ∈ Finset.range q, |(H (i + 1) - H i) / 2| =
      |IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg')
        (IND_CPA_stepAdversary (encAlg' := encAlg') adversary i)| := fun i _ ↦
    congrArg abs (IND_CPA_stepAdversary_signedAdvantageReal_eq_hybridDiff_half
      (encAlg' := encAlg') adversary i).symm
  refine le_trans
    (IND_CPA_advantage_toReal_le_abs_signedAdvantageReal (encAlg' := encAlg') adversary) ?_
  rw [IND_CPA_signedAdvantageReal_eq_lrDiff_half (encAlg' := encAlg') adversary, hleft, hright,
    ← Finset.sum_congr rfl hsteps]
  simp only [abs_div, ← Finset.sum_div]
  gcongr

/-- Planned uniform corollary of the generic lift. If every extracted one-time adversary has
signed real advantage at most `ε`, then any `q`-query oracle adversary has IND-CPA advantage at
most `q * ε`. -/
theorem IND_CPA_advantage_toReal_le_q_mul_of_oneTime_signedAdvantageReal_bound
    [Inhabited M] [Finite C] [Inhabited C]
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ) (ε : ℝ)
    (hq : adversary.MakesAtMostQueries q)
    (hstep : ∀ adv : IND_CPA_Adv encAlg',
      |IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg') adv| ≤ ε) :
    (IND_CPA_advantage (encAlg := encAlg') adversary).toReal ≤ q * ε := by
  refine le_trans
    (IND_CPA_advantage_toReal_le_sum_step_signedAdvantageReal_abs
      (encAlg' := encAlg') adversary q hq)
    ((Finset.sum_le_sum fun k _ =>
      hstep (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k)).trans ?_)
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end MultiQueryHybridLift

end AsymmEncAlg
