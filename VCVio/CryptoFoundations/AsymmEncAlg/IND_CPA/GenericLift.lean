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
def IND_CPA_stepAdversary [Inhabited M]
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

/-- Unfold `IND_CPA_stepPrefix` on a pure computation. -/
private lemma IND_CPA_stepPrefix_pure (pk : PK) (k : ℕ) {α : Type} (a : α) :
    IND_CPA_stepPrefix (encAlg' := encAlg') pk k (pure a) = pure (.done a) := by
  simp [IND_CPA_stepPrefix]

/-- Unfold `IND_CPA_stepPrefix` through a query to the uniform side of the oracle spec. -/
private lemma IND_CPA_stepPrefix_query_inl (pk : PK) (k : ℕ) {α : Type}
    (tu : unifSpec.Domain)
    (mx : encAlg'.IND_CPA_oracleSpec.Range (Sum.inl tu) →
      OracleComp encAlg'.IND_CPA_oracleSpec α) :
    IND_CPA_stepPrefix (encAlg' := encAlg') pk k
        (liftM (query (spec := encAlg'.IND_CPA_oracleSpec) (Sum.inl tu)) >>= mx) =
      (do
        let u ← liftM (query (spec := unifSpec) tu)
        IND_CPA_stepPrefix (encAlg' := encAlg') pk k (mx u)) := by
  simp [IND_CPA_stepPrefix]

/-- Unfold `IND_CPA_stepPrefix` through an LR challenge query. -/
private lemma IND_CPA_stepPrefix_query_inr (pk : PK) (k : ℕ) {α : Type}
    (mm : M × M)
    (mx : encAlg'.IND_CPA_oracleSpec.Range (Sum.inr mm) →
      OracleComp encAlg'.IND_CPA_oracleSpec α) :
    IND_CPA_stepPrefix (encAlg' := encAlg') pk k
        (liftM (query (spec := encAlg'.IND_CPA_oracleSpec) (Sum.inr mm)) >>= mx) =
      (do
        let st ← get
        match st.1 mm with
        | some c =>
            IND_CPA_stepPrefix (encAlg' := encAlg') pk k (mx c)
        | none =>
            if st.2 < k then do
              let c ← liftM (encAlg'.encrypt pk mm.1)
              let cache' := st.1.cacheQuery mm c
              set (cache', st.2 + 1)
              IND_CPA_stepPrefix (encAlg' := encAlg') pk k (mx c)
            else
              pure (.paused mm mx)) := by
  simp [IND_CPA_stepPrefix]

/-- Once the counter has already crossed `k`, the `k` and `k + 1` counted hybrids agree. -/
private lemma IND_CPA_hybridLR_counted_run'_evalDist_eq_above
    (pk : PK) (k : ℕ) {α : Type}
    (oa : OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState)
    (hst : st.2 ≥ k + 1) :
    evalDist ((simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) oa).run' st) =
      evalDist ((simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (k + 1)) oa).run' st) := by
  have hrun :
      evalDist ((simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) oa).run st) =
        evalDist ((simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (k + 1)) oa).run st) := by
    apply evalDist_ext
    intro z
    exact OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run_eq_of_impl_eq_preservesInv
      (impl₁ := encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k)
      (impl₂ := encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (k + 1))
      (Inv := fun s => s.2 ≥ k + 1)
      (oa := oa)
      (himpl_eq := fun t s hs =>
        IND_CPA_hybridLR_counted_run_eq_of_ge (encAlg' := encAlg') pk k t s hs)
      (hpres₂ := fun t s hs z hz => by
        have hle := IND_CPA_hybridLR_counted_counter_le (encAlg' := encAlg') pk (k + 1) t s z hz
        omega)
      (s := st) (hs := hst) (z := z)
  simp only [StateT.run', evalDist_map]
  exact congrArg (fun d => Prod.fst <$> d) hrun

private lemma IND_CPA_queryImpl_hybridLR_counted_run_inl
    (pk : PK) (leftUntil : ℕ) (tu : unifSpec.Domain)
    (st : encAlg'.IND_CPA_CountedState) :
    ((encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (.inl tu)).run st =
      (($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu)) >>= fun u => pure (u, st)) := by
  change
    (((liftM ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu))) :
        StateT encAlg'.IND_CPA_CountedState ProbComp (unifSpec.Range tu)).run st) = _
  exact
    (StateT.run_lift ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu)) st)

private lemma probComp_query_eq_uniform (tu : unifSpec.Domain) :
    (monadLift (query tu) : ProbComp (unifSpec.Range tu)) =
      ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu)) := by
  rfl

private lemma probOutput_bind_ignore_left {α β : Type} [DecidableEq β]
    (mx : ProbComp α) (y x : β) :
    Pr[= x | (do
      let _ ← mx
      pure y : ProbComp β)] =
    Pr[= x | (pure y : ProbComp β)] := by
  simp

private lemma IND_CPA_queryImpl_hybridLR_counted_run_inr_none
    (pk : PK) (leftUntil : ℕ) (mm : M × M)
    (st : encAlg'.IND_CPA_CountedState)
    (hcache : st.1 mm = none) :
    ((encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (.inr mm)).run st =
      (do
        let c ← encAlg'.encrypt pk (if st.2 < leftUntil then mm.1 else mm.2)
        pure (c, (st.1.cacheQuery mm c, st.2 + 1))) := by
  change (encAlg'.IND_CPA_hybridChallengeOracleLR_counted pk leftUntil mm).run st = _
  simpa using
    (IND_CPA_hybridChallengeOracleLR_counted_run_none
      (encAlg' := encAlg') pk leftUntil mm st hcache)

private lemma IND_CPA_queryImpl_hybridLR_counted_run_inr_some
    (pk : PK) (leftUntil : ℕ) (mm : M × M) (c : C)
    (st : encAlg'.IND_CPA_CountedState)
    (hcache : st.1 mm = some c) :
    ((encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (.inr mm)).run st =
      pure (c, st) := by
  change (encAlg'.IND_CPA_hybridChallengeOracleLR_counted pk leftUntil mm).run st = _
  simpa using
    (IND_CPA_hybridChallengeOracleLR_counted_run_some
      (encAlg' := encAlg') pk leftUntil mm c st hcache)

private lemma IND_CPA_hybridLR_simulateQ_query_inl
    (pk : PK) (leftUntil : ℕ) (tu : unifSpec.Domain)
    {α : Type}
    (oa : unifSpec.Range tu → OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) :
    ((encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil (.inl tu) >>= fun u =>
        simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)) st) =
      (($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu)) >>= fun u =>
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)).run st) := by
  change
    (((encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil (.inl tu) >>= fun u =>
        simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)).run st) = _)
  rw [StateT.run_bind, IND_CPA_queryImpl_hybridLR_counted_run_inl (encAlg' := encAlg') pk
    leftUntil tu st]
  simp

private lemma IND_CPA_hybridLR_simulateQ_query_inr_none
    (pk : PK) (leftUntil : ℕ) (mm : M × M)
    {α : Type}
    (oa : C → OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState)
    (hcache : st.1 mm = none) :
    ((encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil (.inr mm) >>= fun u =>
        simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)) st) =
      (do
        let c ← encAlg'.encrypt pk (if st.2 < leftUntil then mm.1 else mm.2)
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa c)).run
          (st.1.cacheQuery mm c, st.2 + 1)) := by
  change
    (((encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil (.inr mm) >>= fun u =>
        simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)).run st) = _)
  rw [StateT.run_bind, IND_CPA_queryImpl_hybridLR_counted_run_inr_none
    (encAlg' := encAlg') pk leftUntil mm st hcache]
  simp

private lemma IND_CPA_hybridLR_simulateQ_query_inr_some
    (pk : PK) (leftUntil : ℕ) (mm : M × M) (c : C)
    {α : Type}
    (oa : C → OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState)
    (hcache : st.1 mm = some c) :
    ((encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil (.inr mm) >>= fun u =>
        simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)) st) =
      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa c)).run st := by
  change
    (((encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil (.inr mm) >>= fun u =>
        simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)).run st) = _)
  rw [StateT.run_bind, IND_CPA_queryImpl_hybridLR_counted_run_inr_some
    (encAlg' := encAlg') pk leftUntil mm c st hcache]
  simp

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
  revert st hst
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro st hst
      simp [IND_CPA_stepPrefix_pure]
  | query_bind t oa ih =>
      intro st hst
      cases t with
      | inl tu =>
          apply evalDist_ext
          intro x
          rw [IND_CPA_stepPrefix_query_inl]
          have hleft :
              Pr[= x | do
                let __discr ←
                  (do
                    let u ← liftM (query (spec := unifSpec) tu)
                    IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa u)).run st
                match __discr.1 with
                | .done a => pure a
                | .paused mm cont =>
                    let c ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
                    (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c)).run'
                      (QueryCache.cacheQuery __discr.2.1 mm c, __discr.2.2 + 1)] =
              Pr[= x | do
                let u ← ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu))
                let __discr ← (IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa u)).run st
                match __discr.1 with
                | .done a => pure a
                | .paused mm cont =>
                    let c ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
                    (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c)).run'
                      (QueryCache.cacheQuery __discr.2.1 mm c, __discr.2.2 + 1)] := by
            simp [StateT.run_bind, probComp_query_eq_uniform]
          rw [hleft]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run']
          rw [IND_CPA_hybridLR_simulateQ_query_inl (encAlg' := encAlg') pk
            (if branch then k + 1 else k) tu oa st]
          simp [map_eq_bind_pure_comp, bind_assoc]
          change Pr[= x | do
              let u ← ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu))
              let __discr ← (IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa u)).run st
              match __discr.1 with
              | .done a => pure a
              | .paused mm cont =>
                  let c ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
                  (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c)).run'
                    (QueryCache.cacheQuery __discr.2.1 mm c, __discr.2.2 + 1)] =
            Pr[= x | do
              let u ← ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu))
              (simulateQ
                (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (if branch then k + 1 else k))
                (oa u)).run' st]
          refine probOutput_bind_congr'
            ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu)) x ?_
          intro u
          exact (evalDist_ext_iff.mp (ih u st hst)) x
      | inr mm =>
          rcases hcache : st.1 mm with _ | c
          · by_cases hlt : st.2 < k
            · apply evalDist_ext
              intro x
              rw [IND_CPA_stepPrefix_query_inr]
              have hleft :
                  Pr[= x | do
                    let __discr ←
                      (do
                        let st0 : encAlg'.IND_CPA_CountedState ← get
                        match st0.1 mm with
                        | some c => IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa c)
                        | none =>
                            if st0.2 < k then do
                              let c ← liftM (encAlg'.encrypt pk mm.1)
                              set (QueryCache.cacheQuery st0.1 mm c, st0.2 + 1)
                              IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa c)
                            else
                              pure (.paused mm oa)).run st
                    match __discr.1 with
                    | .done a => pure a
                    | .paused mm cont =>
                        let c ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
                        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c)).run'
                          (QueryCache.cacheQuery __discr.2.1 mm c, __discr.2.2 + 1)] =
                  Pr[= x | do
                    let c ← encAlg'.encrypt pk mm.1
                    let __discr ← (IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa c)).run
                      (QueryCache.cacheQuery st.1 mm c, st.2 + 1)
                    match __discr.1 with
                    | .done a => pure a
                    | .paused mm cont =>
                        let c' ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
                        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c')).run'
                          (QueryCache.cacheQuery __discr.2.1 mm c', __discr.2.2 + 1)] := by
                simp [hcache, hlt, StateT.run_bind, StateT.run_get, StateT.run_set]
              rw [hleft]
              simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
                OracleQuery.cont_query, id_map, StateT.run']
              rw [IND_CPA_hybridLR_simulateQ_query_inr_none (encAlg' := encAlg') pk
                (if branch then k + 1 else k) mm oa st hcache]
              have hkLt : st.2 < if branch then k + 1 else k := by
                cases hbranch : branch
                · simpa [hbranch] using hlt
                · have hkLt' : st.2 < k + 1 := by omega
                  simpa [hbranch] using hkLt'
              have hsel :
                  (if st.2 < if branch then k + 1 else k then mm.1 else mm.2) = mm.1 :=
                if_pos hkLt
              simp [map_eq_bind_pure_comp, bind_assoc]
              rw [hsel]
              refine probOutput_bind_congr' (encAlg'.encrypt pk mm.1) x ?_
              intro c
              exact (evalDist_ext_iff.mp
                (ih c (st.1.cacheQuery mm c, st.2 + 1) (by omega))) x
            · have hEq : st.2 = k := by omega
              apply evalDist_ext
              intro x
              rw [IND_CPA_stepPrefix_query_inr]
              have hleft :
                  Pr[= x | do
                    let __discr ←
                      (do
                        let st0 : encAlg'.IND_CPA_CountedState ← get
                        match st0.1 mm with
                        | some c => IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa c)
                        | none =>
                            if st0.2 < k then do
                              let c ← liftM (encAlg'.encrypt pk mm.1)
                              set (QueryCache.cacheQuery st0.1 mm c, st0.2 + 1)
                              IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa c)
                            else
                              pure (.paused mm oa)).run st
                    match __discr.1 with
                    | .done a => pure a
                    | .paused mm cont =>
                        let c ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
                        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c)).run'
                          (QueryCache.cacheQuery __discr.2.1 mm c, __discr.2.2 + 1)] =
                  Pr[= x | do
                    let c ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
                    (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (oa c)).run'
                      (QueryCache.cacheQuery st.1 mm c, st.2 + 1)] := by
                simp [hcache, hlt, StateT.run_bind, StateT.run_get, StateT.run_pure]
              rw [hleft]
              simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
                OracleQuery.cont_query, id_map, StateT.run']
              rw [IND_CPA_hybridLR_simulateQ_query_inr_none (encAlg' := encAlg') pk
                (if branch then k + 1 else k) mm oa st hcache]
              have hsel :
                  (if st.2 < if branch then k + 1 else k then mm.1 else mm.2) =
                    (if branch then mm.1 else mm.2) := by
                cases branch <;> simp [hEq]
              simp [map_eq_bind_pure_comp, bind_assoc]
              rw [hsel]
              refine probOutput_bind_congr' (encAlg'.encrypt pk (if branch then mm.1 else mm.2))
                x ?_
              intro c
              cases hbranch : branch
              · rfl
              · exact (evalDist_ext_iff.mp
                  (IND_CPA_hybridLR_counted_run'_evalDist_eq_above (encAlg' := encAlg') pk k
                    (oa c) (st.1.cacheQuery mm c, st.2 + 1) (by omega))) x
          · apply evalDist_ext
            intro x
            rw [IND_CPA_stepPrefix_query_inr]
            have hleft :
                Pr[= x | do
                  let __discr ←
                    (do
                      let st0 : encAlg'.IND_CPA_CountedState ← get
                      match st0.1 mm with
                      | some c => IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa c)
                      | none =>
                          if st0.2 < k then do
                            let c ← liftM (encAlg'.encrypt pk mm.1)
                            set (QueryCache.cacheQuery st0.1 mm c, st0.2 + 1)
                            IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa c)
                          else
                            pure (.paused mm oa)).run st
                  match __discr.1 with
                  | .done a => pure a
                  | .paused mm cont =>
                      let c' ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
                      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c')).run'
                        (QueryCache.cacheQuery __discr.2.1 mm c', __discr.2.2 + 1)] =
                Pr[= x | do
                  let __discr ← (IND_CPA_stepPrefix (encAlg' := encAlg') pk k (oa c)).run st
                  match __discr.1 with
                  | .done a => pure a
                  | .paused mm cont =>
                      let c' ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
                      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c')).run'
                        (QueryCache.cacheQuery __discr.2.1 mm c', __discr.2.2 + 1)] := by
              simp [hcache, StateT.run_bind, StateT.run_get]
            rw [hleft]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run']
            rw [IND_CPA_hybridLR_simulateQ_query_inr_some (encAlg' := encAlg') pk
              (if branch then k + 1 else k) mm c oa st hcache]
            simp [map_eq_bind_pure_comp]
            exact (evalDist_ext_iff.mp (ih c st hst)) x

/-- Planned game-level bridge for the extracted step adversary: its one-time IND-CPA game is the
uniform-bit branch between adjacent LR hybrids. This is the theorem that converts the local prefix
decomposition above into a clean hybrid-gap statement. -/
private lemma IND_CPA_stepAdversary_game_eq_hybridBranch [Inhabited M]
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
  apply evalDist_ext
  intro x
  refine probOutput_bind_congr' ($ᵗ Bool : ProbComp Bool) x ?_
  intro bit
  show Pr[= x | do
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
  cases bit <;> dsimp <;>
    simp only [IND_CPA_LR_hybridGame, bind_assoc] <;>
    (refine probOutput_bind_congr' encAlg'.keygen x ?_) <;>
    intro pk_sk <;>
    simp only [IND_CPA_stepAdversary, bind_assoc] <;>
    (show (evalDist _) x = (evalDist _) x) <;>
    congr 1
  · rename_i pk_sk
    have hresume := IND_CPA_stepPrefix_resume_eq_hybridLR (encAlg' := encAlg')
      pk_sk.1 k false (adversary pk_sk.1) (∅, 0) (Nat.zero_le k)
    dsimp at hresume
    apply evalDist_ext; intro y
    refine Eq.trans ?_ (probOutput_map_eq_of_evalDist_eq hresume (false == ·) y)
    simp only [map_eq_bind_pure_comp, bind_assoc]
    refine probOutput_bind_congr'
      ((IND_CPA_stepPrefix (encAlg' := encAlg') pk_sk.1 k (adversary pk_sk.1)).run (∅, 0)) y
      fun ⟨res, _st⟩ => ?_
    cases res with
    | done guess =>
        dsimp; simp only [pure_bind]
        exact probOutput_bind_ignore_left _ _ _
    | paused _ _ =>
        dsimp; simp only [map_eq_bind_pure_comp, Function.comp, pure_bind, bind_assoc]
  · rename_i pk_sk
    have hresume := IND_CPA_stepPrefix_resume_eq_hybridLR (encAlg' := encAlg')
      pk_sk.1 k true (adversary pk_sk.1) (∅, 0) (Nat.zero_le k)
    dsimp at hresume
    apply evalDist_ext; intro y
    refine Eq.trans ?_ (probOutput_map_eq_of_evalDist_eq hresume (true == ·) y)
    simp only [map_eq_bind_pure_comp, bind_assoc]
    refine probOutput_bind_congr'
      ((IND_CPA_stepPrefix (encAlg' := encAlg') pk_sk.1 k (adversary pk_sk.1)).run (∅, 0)) y
      fun ⟨res, _st⟩ => ?_
    cases res with
    | done guess =>
        dsimp; simp only [pure_bind]
        exact probOutput_bind_ignore_left _ _ _
    | paused _ _ =>
        dsimp; simp only [map_eq_bind_pure_comp, Function.comp, pure_bind, bind_assoc]

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
        let bit ← ($ᵗ Bool : ProbComp Bool)
        let z ← if bit then encAlg'.IND_CPA_LR_hybridGame adversary (k + 1)
                 else encAlg'.IND_CPA_LR_hybridGame adversary k
        pure (bit == z)]).toReal from by
          congr 1
          exact (evalDist_ext_iff.mp
            (IND_CPA_stepAdversary_game_eq_hybridBranch
              (encAlg' := encAlg') adversary k)) true]
  exact probOutput_uniformBool_branch_toReal_sub_half
    (encAlg'.IND_CPA_LR_hybridGame adversary (k + 1))
    (encAlg'.IND_CPA_LR_hybridGame adversary k)

/-- Planned generic one-time-to-many-time lift: bounded multi-query IND-CPA advantage is at most
the sum of the extracted one-time signed advantages over the first `q` fresh LR queries. -/
theorem IND_CPA_advantage_toReal_le_sum_step_signedAdvantageReal_abs
    [Inhabited M]
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ)
    (hq : adversary.MakesAtMostQueries q) :
    (IND_CPA_advantage (encAlg := encAlg') adversary).toReal ≤
      Finset.sum (Finset.range q) (fun k =>
        |IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg')
          (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k)|) := by
  let H : ℕ → ℝ := fun i =>
    (Pr[= true | encAlg'.IND_CPA_LR_hybridGame adversary i]).toReal
  have hleft :
      (Pr[= true | encAlg'.IND_CPA_LR_experiment adversary true]).toReal = H q := by
    unfold H
    congr 1
    symm
    exact encAlg'.IND_CPA_LR_hybridGame_q_probOutput_eq_left_of_MakesAtMostQueries adversary q hq
  have hright :
      (Pr[= true | encAlg'.IND_CPA_LR_experiment adversary false]).toReal = H 0 := by
    unfold H
    congr 1
    symm
    exact encAlg'.IND_CPA_LR_hybridGame_zero_probOutput_eq_right adversary
  have hsub :
      Finset.sum (Finset.range q) (fun i => H (i + 1)) -
        Finset.sum (Finset.range q) (fun i => H i) = H q - H 0 := by
    simpa using (Finset.sum_range_sub (f := H) q)
  have htel :
      Finset.sum (Finset.range q) (fun i => H (i + 1) - H i) = H q - H 0 := by
    simpa [Finset.sum_sub_distrib] using hsub
  have htri :
      |H q - H 0| ≤ Finset.sum (Finset.range q) (fun i => |H (i + 1) - H i|) := by
    rw [← htel]
    simpa using
      (Finset.abs_sum_le_sum_abs
        (s := Finset.range q)
        (f := fun i => H (i + 1) - H i))
  have habs_half :
      |(H q - H 0) / 2| = (1 / 2 : ℝ) * |H q - H 0| := by
    rw [show (H q - H 0) / 2 = (1 / 2 : ℝ) * (H q - H 0) by ring]
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have hterm_half :
      ∀ i : ℕ, |(H (i + 1) - H i) / 2| = (1 / 2 : ℝ) * |H (i + 1) - H i| := by
    intro i
    rw [show (H (i + 1) - H i) / 2 = (1 / 2 : ℝ) * (H (i + 1) - H i) by ring]
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have hsum_half :
      (1 / 2 : ℝ) * Finset.sum (Finset.range q) (fun i => |H (i + 1) - H i|) =
        Finset.sum (Finset.range q) (fun i => |(H (i + 1) - H i) / 2|) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    symm
    exact hterm_half i
  have hhalf :
      |(H q - H 0) / 2| ≤ Finset.sum (Finset.range q) (fun i => |(H (i + 1) - H i) / 2|) := by
    rw [habs_half]
    calc
      (1 / 2 : ℝ) * |H q - H 0|
          ≤ (1 / 2 : ℝ) * Finset.sum (Finset.range q) (fun i => |H (i + 1) - H i|) := by
              exact mul_le_mul_of_nonneg_left htri (by positivity)
      _ = Finset.sum (Finset.range q) (fun i => |(H (i + 1) - H i) / 2|) := hsum_half
  have hsteps :
      Finset.sum (Finset.range q) (fun i =>
        |(H (i + 1) - H i) / 2|) =
      Finset.sum (Finset.range q) (fun i =>
        |IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg')
          (IND_CPA_stepAdversary (encAlg' := encAlg') adversary i)|) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    symm
    rw [IND_CPA_stepAdversary_signedAdvantageReal_eq_hybridDiff_half
      (encAlg' := encAlg') adversary i]
  refine le_trans
    (IND_CPA_advantage_toReal_le_abs_signedAdvantageReal
      (encAlg' := encAlg') adversary) ?_
  rw [IND_CPA_signedAdvantageReal_eq_lrDiff_half (encAlg' := encAlg') adversary, hleft, hright]
  calc
    |(H q - H 0) / 2|
        ≤ Finset.sum (Finset.range q) (fun i => |(H (i + 1) - H i) / 2|) := hhalf
    _ = Finset.sum (Finset.range q) (fun i =>
          |IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg')
            (IND_CPA_stepAdversary (encAlg' := encAlg') adversary i)|) := hsteps

/-- Planned uniform corollary of the generic lift. If every extracted one-time adversary has
signed real advantage at most `ε`, then any `q`-query oracle adversary has IND-CPA advantage at
most `q * ε`. -/
theorem IND_CPA_advantage_toReal_le_q_mul_of_oneTime_signedAdvantageReal_bound
    [Inhabited M]
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ) (ε : ℝ)
    (hq : adversary.MakesAtMostQueries q) (_hε : 0 ≤ ε)
    (hstep : ∀ adv : IND_CPA_Adv encAlg',
      |IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg') adv| ≤ ε) :
    (IND_CPA_advantage (encAlg := encAlg') adversary).toReal ≤ q * ε := by
  refine le_trans
    (IND_CPA_advantage_toReal_le_sum_step_signedAdvantageReal_abs
      (encAlg' := encAlg') adversary q hq) ?_
  calc
    Finset.sum (Finset.range q) (fun k =>
          |IND_CPA_OneTime_signedAdvantageReal (encAlg := encAlg')
            (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k)|)
        ≤ Finset.sum (Finset.range q) (fun _ => ε) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact hstep (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k)
    _ = q * ε := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end MultiQueryHybridLift

end AsymmEncAlg
