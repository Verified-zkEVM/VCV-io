/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.Defs
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Asymmetric Encryption Schemes: IND-CPA Oracle Games

This file contains the oracle-based IND-CPA interface together with the counted left/right hybrid
machinery used in generic multi-query proofs.
-/

open OracleSpec OracleComp ENNReal

universe u v w

namespace AsymmEncAlg

variable {M PK SK C : Type}

section IND_CPA_Oracle

variable [DecidableEq M]

/-- Oracle-based multi-query IND-CPA game. The adversary gets oracle access to an encryption
oracle that encrypts one of two challenge messages depending on a hidden bit. -/
def IND_CPA_oracleSpec (_encAlg : AsymmEncAlg ProbComp M PK SK C) :=
  unifSpec + (M × M →ₒ C)

/-- An oracle IND-CPA adversary chooses challenge messages by querying the LR oracle and returns
a final Boolean guess. -/
def IND_CPA_adversary (encAlg : AsymmEncAlg ProbComp M PK SK C) :=
  PK → OracleComp encAlg.IND_CPA_oracleSpec Bool

/-- An IND-CPA adversary `MakesAtMostQueries q` when it issues at most `q` total fresh queries
to the challenge oracle, regardless of public key. Uniform-sampling queries are unrestricted. -/
def IND_CPA_adversary.MakesAtMostQueries {encAlg : AsymmEncAlg ProbComp M PK SK C}
    (adversary : encAlg.IND_CPA_adversary) (q : ℕ) : Prop :=
  ∀ pk, (adversary pk).IsQueryBound q
    (fun t n => match t with | .inl _ => True | .inr _ => 0 < n)
    (fun t n => match t with | .inl _ => n | .inr _ => n - 1)

/-- Cache state for the cached left/right oracle implementations. -/
abbrev IND_CPA_Cache (_encAlg : AsymmEncAlg ProbComp M PK SK C) :=
  (M × M →ₒ C).QueryCache

private def IND_CPA_queryImplFromChallenge
    (encAlg : AsymmEncAlg ProbComp M PK SK C)
    {σ : Type}
    (challenge : QueryImpl (M × M →ₒ C) (StateT σ ProbComp)) :
    QueryImpl encAlg.IND_CPA_oracleSpec (StateT σ ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + challenge

private def IND_CPA_cachedChallengeOracle
    (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (pk : PK) (select : M × M → M) :
    QueryImpl (M × M →ₒ C) (StateT encAlg.IND_CPA_Cache ProbComp) := fun mm => do
  let cache ← get
  match cache mm with
  | some c => return c
  | none =>
      let c ← encAlg.encrypt pk (select mm)
      set (cache.cacheQuery mm c)
      return c

/-- Cached LR-oracle implementation for IND-CPA: repeated challenge queries are answered from the
cache, and fresh ones encrypt the selected branch. -/
def IND_CPA_queryImpl' (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (pk : PK) (b : Bool) : QueryImpl encAlg.IND_CPA_oracleSpec
      (StateT encAlg.IND_CPA_Cache ProbComp) :=
  IND_CPA_queryImplFromChallenge encAlg
    (IND_CPA_cachedChallengeOracle encAlg pk
      (fun mm => if b then mm.1 else mm.2))

/-- Oracle IND-CPA experiment with caching on the LR oracle. -/
def IND_CPA_experiment {encAlg : AsymmEncAlg ProbComp M PK SK C}
    (adversary : encAlg.IND_CPA_adversary) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (pk, _sk) ← encAlg.keygen
  let b' ← (simulateQ (encAlg.IND_CPA_queryImpl' pk b) (adversary pk)).run' ∅
  return (b == b')

/-- Deterministic left/right endpoint IND-CPA experiment: all fresh LR queries use the branch
selected by `b`, and the adversary's final guess is returned directly. -/
def IND_CPA_LR_experiment {encAlg : AsymmEncAlg ProbComp M PK SK C}
    (adversary : encAlg.IND_CPA_adversary) (b : Bool) : ProbComp Bool := do
  let (pk, _sk) ← encAlg.keygen
  (simulateQ (encAlg.IND_CPA_queryImpl' pk b) (adversary pk)).run' ∅

variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

/-- Cached IND-CPA state extended with a query counter. -/
abbrev IND_CPA_CountedState (_encAlg : AsymmEncAlg ProbComp M PK SK C) :=
  _encAlg.IND_CPA_Cache × ℕ

private def IND_CPA_countedChallengeOracle
    (pk : PK) (select : ℕ → M × M → M) :
    QueryImpl (M × M →ₒ C)
      (StateT encAlg'.IND_CPA_CountedState ProbComp) := fun mm => do
  let st ← get
  match st.1 mm with
  | some c => return c
  | none =>
      let c ← encAlg'.encrypt pk (select st.2 mm)
      let cache' := st.1.cacheQuery mm c
      set (cache', st.2 + 1)
      return c

private lemma IND_CPA_countedChallengeOracle_run_eq_of_select_eq
    (pk : PK) (select₁ select₂ : ℕ → M × M → M) (mm : M × M)
    (st : encAlg'.IND_CPA_CountedState)
    (h : select₁ st.2 mm = select₂ st.2 mm) :
    (IND_CPA_countedChallengeOracle (encAlg' := encAlg') pk select₁ mm).run st =
      (IND_CPA_countedChallengeOracle (encAlg' := encAlg') pk select₂ mm).run st := by
  simp only [IND_CPA_countedChallengeOracle, StateT.run_bind, StateT.run_get, pure_bind, h]

/-- The real IND-CPA challenge oracle, but with an explicit counter that increments on cache
misses. -/
def IND_CPA_challengeOracle'_counted
    (pk : PK) (b : Bool) :
    QueryImpl (M × M →ₒ C)
      (StateT encAlg'.IND_CPA_CountedState ProbComp) :=
  IND_CPA_countedChallengeOracle (encAlg' := encAlg') pk
    (fun _ mm => if b then mm.1 else mm.2)

/-- The cached real IND-CPA query implementation, extended with an explicit query counter. -/
def IND_CPA_queryImpl'_counted
    (pk : PK) (b : Bool) : QueryImpl encAlg'.IND_CPA_oracleSpec
      (StateT encAlg'.IND_CPA_CountedState ProbComp) :=
  IND_CPA_queryImplFromChallenge encAlg'
    (IND_CPA_challengeOracle'_counted (encAlg' := encAlg') pk b)

/-- Counted left/right hybrid oracle: the first `leftUntil` fresh LR queries use the left
message and all later fresh queries use the right message. Repeated queries are answered from
the cache. -/
def IND_CPA_hybridChallengeOracleLR_counted
    (pk : PK) (leftUntil : ℕ) :
    QueryImpl (M × M →ₒ C)
      (StateT encAlg'.IND_CPA_CountedState ProbComp) :=
  IND_CPA_countedChallengeOracle (encAlg' := encAlg') pk
    (fun n mm => if n < leftUntil then mm.1 else mm.2)

/-- Full counted query implementation for the generic left-prefix/right-suffix hybrid family. -/
def IND_CPA_queryImpl_hybridLR_counted
    (pk : PK) (leftUntil : ℕ) : QueryImpl encAlg'.IND_CPA_oracleSpec
      (StateT encAlg'.IND_CPA_CountedState ProbComp) :=
  IND_CPA_queryImplFromChallenge encAlg'
    (IND_CPA_hybridChallengeOracleLR_counted (encAlg' := encAlg') pk leftUntil)

/-- The generic left/right hybrid family: the first `leftUntil` fresh LR queries use the left
branch, and all later fresh queries use the right branch. -/
def IND_CPA_LR_hybridGame
    (adversary : encAlg'.IND_CPA_adversary) (leftUntil : ℕ) : ProbComp Bool := do
  let (pk, _sk) ← encAlg'.keygen
  (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (adversary pk)).run'
    (∅, 0)

/-- One-step counter monotonicity for the counted real IND-CPA implementation. -/
lemma IND_CPA_queryImpl'_counted_counter_le_succ
    (pk : PK) (b : Bool)
    (t : encAlg'.IND_CPA_oracleSpec.Domain)
    (st : encAlg'.IND_CPA_CountedState)
    (p : encAlg'.IND_CPA_oracleSpec.Range t × encAlg'.IND_CPA_CountedState)
    (hp : p ∈ support ((encAlg'.IND_CPA_queryImpl'_counted pk b t).run st)) :
    p.2.2 ≤ st.2 + 1 := by
  cases t with
  | inl tu =>
      simp only [IND_CPA_queryImpl'_counted, IND_CPA_queryImplFromChallenge,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        liftM, monadLift] at hp
      change p ∈ support ((StateT.lift _).run st) at hp
      rw [StateT.run_lift, mem_support_bind_iff] at hp
      obtain ⟨a, _, ha⟩ := hp
      rw [mem_support_pure_iff] at ha
      have hst : p.2 = st := congrArg Prod.snd ha
      simp [hst]
  | inr mm =>
      have hp' : p ∈ support ((encAlg'.IND_CPA_challengeOracle'_counted pk b mm).run st) := by
        simpa [IND_CPA_queryImpl'_counted, IND_CPA_queryImplFromChallenge] using hp
      clear hp
      revert hp'
      rcases hcache : st.1 mm with _ | c <;> intro hp
      · simp only [IND_CPA_challengeOracle'_counted, IND_CPA_countedChallengeOracle, hcache,
          StateT.run_bind, StateT.run_get, pure_bind] at hp
        change (_ : (ofFn fun _ ↦ C).Range mm × encAlg'.IND_CPA_CountedState) ∈ _ at hp
        simp only [StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
          Set.mem_singleton_iff] at hp
        obtain ⟨c, _, ⟨i, hi, hp⟩⟩ := hp
        simp only [StateT.run_set, support_pure, Set.mem_singleton_iff] at hi
        subst hi
        simp only [hp]
        omega
      · simp only [IND_CPA_challengeOracle'_counted, IND_CPA_countedChallengeOracle, hcache,
          StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure] at hp
        have := congrArg (fun x => x.2.2) hp
        simp at this
        omega

private lemma IND_CPA_countedChallengeOracle_proj_eq_cached
    (pk : PK)
    (selectCount : ℕ → M × M → M)
    (select : M × M → M)
    (hselect : ∀ n mm, selectCount n mm = select mm)
    (mm : M × M) (st : encAlg'.IND_CPA_CountedState) :
    Prod.map id Prod.fst <$>
      (IND_CPA_countedChallengeOracle (encAlg' := encAlg') pk selectCount mm).run st =
      (IND_CPA_cachedChallengeOracle encAlg' pk select mm).run st.1 := by
  rcases st with ⟨cache, n⟩
  rcases hcache : cache mm with _ | c
  · have hcounted :
        Prod.map id Prod.fst <$>
          (IND_CPA_countedChallengeOracle (encAlg' := encAlg') pk selectCount mm).run
            (cache, n) =
        (do
          let c ← encAlg'.encrypt pk (select mm)
          pure (c, cache.cacheQuery mm c) : ProbComp _) := by
      simp [IND_CPA_countedChallengeOracle, hcache, StateT.run_bind, StateT.run_get,
        StateT.run_set, hselect n mm]
    have hcached :
        (IND_CPA_cachedChallengeOracle encAlg' pk select mm).run cache =
        (do
          let c ← encAlg'.encrypt pk (select mm)
          pure (c, cache.cacheQuery mm c) : ProbComp _) := by
      simp [IND_CPA_cachedChallengeOracle, hcache,
        StateT.run_bind, StateT.run_get, pure_bind]
    exact hcounted.trans hcached.symm
  · simp [IND_CPA_countedChallengeOracle, IND_CPA_cachedChallengeOracle, hcache,
      StateT.run_bind, StateT.run_get, pure_bind]

/-- Projecting away the counter from the counted real IND-CPA implementation recovers the
ordinary cached real implementation. -/
lemma IND_CPA_queryImpl'_counted_proj_eq_queryImpl'
    (pk : PK) (b : Bool)
    (t : encAlg'.IND_CPA_oracleSpec.Domain)
    (st : encAlg'.IND_CPA_CountedState) :
    Prod.map id Prod.fst <$> (encAlg'.IND_CPA_queryImpl'_counted pk b t).run st =
      ((encAlg'.IND_CPA_queryImpl' pk b) t).run st.1 := by
  cases t with
  | inl tu =>
      simp only [IND_CPA_queryImpl'_counted, IND_CPA_queryImpl', IND_CPA_queryImplFromChallenge,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
      change Prod.map id Prod.fst <$> (StateT.lift _).run st = (StateT.lift _).run st.1
      simp [StateT.run_lift, Prod.map, Functor.map_map]
  | inr mm =>
      simpa [IND_CPA_queryImpl'_counted, IND_CPA_queryImpl', IND_CPA_queryImplFromChallenge]
        using
          (IND_CPA_countedChallengeOracle_proj_eq_cached (encAlg' := encAlg') pk
            (fun _ mm => if b then mm.1 else mm.2)
            (fun mm => if b then mm.1 else mm.2)
            (by intro n mm; rfl) mm st)

/-- The `leftUntil = 0` left/right hybrid is exactly the all-right endpoint game once the
counter is projected away. -/
lemma IND_CPA_queryImpl_hybridLR_counted_proj_eq_queryImpl'_false
    (pk : PK)
    (t : encAlg'.IND_CPA_oracleSpec.Domain)
    (st : encAlg'.IND_CPA_CountedState) :
    Prod.map id Prod.fst <$> (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk 0 t).run st =
      ((encAlg'.IND_CPA_queryImpl' pk false) t).run st.1 := by
  cases t with
  | inl tu =>
      simp only [IND_CPA_queryImpl_hybridLR_counted, IND_CPA_queryImpl',
        IND_CPA_queryImplFromChallenge,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
      change Prod.map id Prod.fst <$> (StateT.lift _).run st = (StateT.lift _).run st.1
      simp [StateT.run_lift, Prod.map, Functor.map_map]
  | inr mm =>
      simpa [IND_CPA_queryImpl_hybridLR_counted, IND_CPA_queryImpl',
        IND_CPA_queryImplFromChallenge] using
          (IND_CPA_countedChallengeOracle_proj_eq_cached (encAlg' := encAlg') pk
            (fun n mm => if n < 0 then mm.1 else mm.2)
            (fun mm => mm.2)
            (by intro n mm; simp) mm st)

/-- If a counted IND-CPA hybrid implementation agrees with the counted real implementation
through the first `q` fresh LR queries, then any adversary making at most `q` LR queries sees
the same output distribution as in the real IND-CPA game. -/
theorem IND_CPA_run'_evalDist_eq_queryImpl'_of_bounded_eq
    (implCounted : PK → Bool → ℕ →
      QueryImpl encAlg'.IND_CPA_oracleSpec (StateT encAlg'.IND_CPA_CountedState ProbComp))
    (hsame : ∀ (pk : PK) (b : Bool) (realUntil : ℕ)
      (t : encAlg'.IND_CPA_oracleSpec.Domain) (st : encAlg'.IND_CPA_CountedState),
      (match t with | .inl _ => True | .inr _ => st.2 < realUntil) →
      (encAlg'.IND_CPA_queryImpl'_counted pk b t).run st =
        (implCounted pk b realUntil t).run st)
    (pk : PK) (b : Bool) (q : ℕ)
    {α : Type} (comp : OracleComp encAlg'.IND_CPA_oracleSpec α)
    (budget : ℕ)
    (hbound : comp.IsQueryBound budget
      (fun t n => match t with | .inl _ => True | .inr _ => 0 < n)
      (fun t n => match t with | .inl _ => n | .inr _ => n - 1))
    (cache : (M × M →ₒ C).QueryCache) (n : ℕ) (hn : n + budget ≤ q) :
    evalDist ((simulateQ (implCounted pk b q) comp).run' (cache, n)) =
      evalDist ((simulateQ (encAlg'.IND_CPA_queryImpl' pk b) comp).run' cache) := by
  set canQuery : encAlg'.IND_CPA_oracleSpec.Domain → ℕ → Prop :=
    fun t n => match t with | .inl _ => True | .inr _ => 0 < n
  set cost : encAlg'.IND_CPA_oracleSpec.Domain → ℕ → ℕ :=
    fun t n => match t with | .inl _ => n | .inr _ => n - 1
  have hbound' : comp.IsQueryBound budget canQuery cost := by
    refine (isQueryBound_congr
      (oa := comp)
      (canQuery₁ := fun t n => match t with | .inl _ => True | .inr _ => 0 < n)
      (canQuery₂ := canQuery)
      (cost₁ := fun t n => match t with | .inl _ => n | .inr _ => n - 1)
      (cost₂ := cost)
      (hcan := ?_) (hcost := ?_)).1 ?_
    · intro t n
      cases t <;> simp [canQuery]
    · intro t n
      cases t <;> simp [cost]
    · exact hbound
  have hrun :
      evalDist ((simulateQ (implCounted pk b q) comp).run (cache, n)) =
      evalDist ((simulateQ (encAlg'.IND_CPA_queryImpl'_counted pk b) comp).run (cache, n)) := by
    apply evalDist_ext
    intro z
    exact OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run_eq_of_impl_eq_queryBound
      (impl₁ := implCounted pk b q)
      (impl₂ := encAlg'.IND_CPA_queryImpl'_counted pk b)
      (Inv := fun st budget => st.2 + budget ≤ q)
      (canQuery := canQuery)
      (cost := cost)
      (oa := comp) (budget := budget) (hbound := hbound')
      (himpl_eq := by
        intro t st budget hInv hcan
        symm
        exact hsame pk b q t st (by
          cases t with
          | inl _ => trivial
          | inr _ =>
              have hpos : 0 < budget := by simpa [canQuery] using hcan
              omega))
      (hpres₂ := by
        intro t st budget hInv hcan z hz
        cases t with
        | inl tu =>
            simp only [IND_CPA_queryImpl'_counted, IND_CPA_queryImplFromChallenge,
              QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
              liftM, monadLift] at hz
            change z ∈ support ((StateT.lift _).run st) at hz
            rw [StateT.run_lift, mem_support_bind_iff] at hz
            obtain ⟨a, _, ha⟩ := hz
            rw [mem_support_pure_iff] at ha
            have hst : z.2 = st := congrArg Prod.snd ha
            simpa [cost, hst] using hInv
        | inr mm =>
            have hsucc :=
              encAlg'.IND_CPA_queryImpl'_counted_counter_le_succ pk b (Sum.inr mm) st z hz
            have hpos : 0 < budget := by simpa [canQuery] using hcan
            have hle' : z.2.2 + (budget - 1) ≤ q := by
              omega
            simpa [cost] using hle')
      (s := (cache, n)) (hs := hn) (z := z)
  have hcounted_run' :
      evalDist ((simulateQ (implCounted pk b q) comp).run' (cache, n)) =
      evalDist ((simulateQ (encAlg'.IND_CPA_queryImpl'_counted pk b) comp).run'
        (cache, n)) := by
    simp only [StateT.run']
    simpa [evalDist_map] using congrArg (fun p => Prod.fst <$> p) hrun
  have hreal_run' :
      evalDist ((simulateQ (encAlg'.IND_CPA_queryImpl'_counted pk b) comp).run'
        (cache, n)) =
      evalDist ((simulateQ (encAlg'.IND_CPA_queryImpl' pk b) comp).run' cache) := by
    simpa using congrArg evalDist
      (OracleComp.run'_simulateQ_eq_of_query_map_eq
        (impl₁ := encAlg'.IND_CPA_queryImpl'_counted pk b)
        (impl₂ := encAlg'.IND_CPA_queryImpl' pk b)
        (proj := Prod.fst)
        (hproj := encAlg'.IND_CPA_queryImpl'_counted_proj_eq_queryImpl' pk b)
        comp (cache, n))
  exact hcounted_run'.trans hreal_run'

/-- A counted IND-CPA hybrid game agrees with the real IND-CPA experiment whenever the hybrid
implementation matches the real counted implementation on all states that stay below the query
budget. -/
theorem IND_CPA_countedGame_eq_game_of_MakesAtMostQueries
    (implCounted : PK → Bool → ℕ →
      QueryImpl encAlg'.IND_CPA_oracleSpec (StateT encAlg'.IND_CPA_CountedState ProbComp))
    (hsame : ∀ (pk : PK) (b : Bool) (realUntil : ℕ)
      (t : encAlg'.IND_CPA_oracleSpec.Domain) (st : encAlg'.IND_CPA_CountedState),
      (match t with | .inl _ => True | .inr _ => st.2 < realUntil) →
      (encAlg'.IND_CPA_queryImpl'_counted pk b t).run st =
        (implCounted pk b realUntil t).run st)
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ)
    (hq : adversary.MakesAtMostQueries q) :
    (Pr[= true | do
      let b ← ($ᵗ Bool)
      let (pk, _sk) ← encAlg'.keygen
      let b' ← (simulateQ (implCounted pk b q) (adversary pk)).run' (∅, 0)
      pure (b == b')]).toReal =
    (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal := by
  congr 1
  have hinner : ∀ (pk : PK) (b : Bool),
      evalDist ((simulateQ (implCounted pk b q) (adversary pk)).run' (∅, 0)) =
      evalDist ((simulateQ (encAlg'.IND_CPA_queryImpl' pk b) (adversary pk)).run' ∅) := by
    intro pk b
    exact IND_CPA_run'_evalDist_eq_queryImpl'_of_bounded_eq
      (encAlg' := encAlg')
      implCounted hsame pk b q (adversary pk) q (hq pk) ∅ 0 (by omega)
  simp only [IND_CPA_experiment, probOutput_bind_eq_tsum]
  refine tsum_congr fun b => ?_
  congr 1
  refine tsum_congr fun ⟨pk, _sk⟩ => ?_
  congr 1
  refine tsum_congr fun b' => ?_
  congr 1
  exact (evalDist_ext_iff.mp (hinner pk b)) b'

/-- `ℝ≥0∞`-valued IND-CPA signed advantage, aligned with the oracle IND-CPA experiment. -/
noncomputable def IND_CPA_advantage {encAlg : AsymmEncAlg ProbComp M PK SK C}
    (adversary : encAlg.IND_CPA_adversary) : ℝ≥0∞ :=
  Pr[= true | IND_CPA_experiment adversary] - 1 / 2

end IND_CPA_Oracle

section MultiQueryHybrid

variable [DecidableEq M]
variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

/-- The `leftUntil = 0` LR-hybrid is the all-right endpoint game. -/
theorem IND_CPA_LR_hybridGame_zero_evalDist_eq_right
    (adversary : encAlg'.IND_CPA_adversary) :
    evalDist (encAlg'.IND_CPA_LR_hybridGame adversary 0) =
      evalDist (encAlg'.IND_CPA_LR_experiment adversary false) := by
  simp only [IND_CPA_LR_hybridGame, IND_CPA_LR_experiment, evalDist_bind]
  congr 1
  funext ⟨pk, _sk⟩
  simpa using congrArg evalDist
    (OracleComp.run'_simulateQ_eq_of_query_map_eq
      (impl₁ := encAlg'.IND_CPA_queryImpl_hybridLR_counted pk 0)
      (impl₂ := encAlg'.IND_CPA_queryImpl' pk false)
      (proj := Prod.fst)
      (hproj := encAlg'.IND_CPA_queryImpl_hybridLR_counted_proj_eq_queryImpl'_false pk)
      (adversary pk) (∅, 0))

/-- If an adversary makes at most `q` fresh LR queries, then the `leftUntil = q` LR-hybrid is the
all-left endpoint game. -/
theorem IND_CPA_LR_hybridGame_q_evalDist_eq_left_of_MakesAtMostQueries
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ)
    (hq : adversary.MakesAtMostQueries q) :
    evalDist (encAlg'.IND_CPA_LR_hybridGame adversary q) =
      evalDist (encAlg'.IND_CPA_LR_experiment adversary true) := by
  simp only [IND_CPA_LR_hybridGame, IND_CPA_LR_experiment, evalDist_bind]
  congr 1
  funext ⟨pk, _sk⟩
  exact IND_CPA_run'_evalDist_eq_queryImpl'_of_bounded_eq
    (encAlg' := encAlg')
    (implCounted := fun pk b realUntil =>
      if b then encAlg'.IND_CPA_queryImpl_hybridLR_counted pk realUntil
      else encAlg'.IND_CPA_queryImpl_hybridLR_counted pk 0)
    (hsame := by
      intro pk b realUntil t st hcond
      cases t with
      | inl _ =>
          cases b <;>
            simp [IND_CPA_queryImpl'_counted, IND_CPA_queryImpl_hybridLR_counted,
              IND_CPA_queryImplFromChallenge]
      | inr mm =>
          have hcond' : st.2 < realUntil := by simpa using hcond
          rcases hcache : st.1 mm with _ | c
          · cases b <;>
              simp only [IND_CPA_queryImpl'_counted, IND_CPA_challengeOracle'_counted,
                IND_CPA_queryImpl_hybridLR_counted, IND_CPA_hybridChallengeOracleLR_counted,
                IND_CPA_queryImplFromChallenge, QueryImpl.add_apply_inr,
                Bool.false_eq_true, ite_true, ite_false] <;>
              exact IND_CPA_countedChallengeOracle_run_eq_of_select_eq pk _ _ mm st
                (by simp [hcond'])
          · cases b <;>
              simp only [IND_CPA_queryImpl'_counted, IND_CPA_challengeOracle'_counted,
                IND_CPA_queryImpl_hybridLR_counted, IND_CPA_hybridChallengeOracleLR_counted,
                IND_CPA_queryImplFromChallenge, QueryImpl.add_apply_inr,
                Bool.false_eq_true, ite_true, ite_false] <;>
              exact IND_CPA_countedChallengeOracle_run_eq_of_select_eq pk _ _ mm st
                (by simp [hcond']))
    pk true q (adversary pk) q (hq pk) ∅ 0 (by omega)

/-- The `leftUntil = 0` LR-hybrid has the same success probability as the all-right endpoint. -/
theorem IND_CPA_LR_hybridGame_zero_probOutput_eq_right
    (adversary : encAlg'.IND_CPA_adversary) :
    Pr[= true | encAlg'.IND_CPA_LR_hybridGame adversary 0] =
      Pr[= true | encAlg'.IND_CPA_LR_experiment adversary false] :=
  (evalDist_ext_iff.mp
    (IND_CPA_LR_hybridGame_zero_evalDist_eq_right (encAlg' := encAlg') adversary)) true

/-- If an adversary makes at most `q` fresh LR queries, then the `leftUntil = q` LR-hybrid has
the same success probability as the all-left endpoint. -/
theorem IND_CPA_LR_hybridGame_q_probOutput_eq_left_of_MakesAtMostQueries
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ)
    (hq : adversary.MakesAtMostQueries q) :
    Pr[= true | encAlg'.IND_CPA_LR_hybridGame adversary q] =
      Pr[= true | encAlg'.IND_CPA_LR_experiment adversary true] :=
  (evalDist_ext_iff.mp
    (IND_CPA_LR_hybridGame_q_evalDist_eq_left_of_MakesAtMostQueries
      (encAlg' := encAlg') adversary q hq)) true

/-- The standard random-bit IND-CPA experiment is the uniform-bit branch over the all-left and
all-right endpoint games. -/
private lemma IND_CPA_experiment_probOutput_eq_branch
    (adversary : encAlg'.IND_CPA_adversary) :
    Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary] =
      Pr[= true | do
        let bit ← ($ᵗ Bool)
        let z ← if bit then encAlg'.IND_CPA_LR_experiment adversary true
                 else encAlg'.IND_CPA_LR_experiment adversary false
        pure (bit == z)] := by
  unfold IND_CPA_experiment IND_CPA_LR_experiment
  refine probOutput_bind_congr' ($ᵗ Bool) true ?_
  intro bit
  cases bit <;> simp

/-- Signed real IND-CPA advantage `Pr[win] - 1/2` for the oracle IND-CPA experiment. -/
noncomputable def IND_CPA_signedAdvantageReal (adversary : encAlg'.IND_CPA_adversary) : ℝ :=
  (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal - 1 / 2

/-- The signed real IND-CPA advantage is half the left/right endpoint gap. -/
theorem IND_CPA_signedAdvantageReal_eq_lrDiff_half
    (adversary : encAlg'.IND_CPA_adversary) :
    IND_CPA_signedAdvantageReal (encAlg' := encAlg') adversary =
      ((Pr[= true | encAlg'.IND_CPA_LR_experiment adversary true]).toReal -
        (Pr[= true | encAlg'.IND_CPA_LR_experiment adversary false]).toReal) / 2 := by
  unfold IND_CPA_signedAdvantageReal
  rw [show (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal =
      (Pr[= true | do
        let bit ← ($ᵗ Bool)
        let z ← if bit then encAlg'.IND_CPA_LR_experiment adversary true
                 else encAlg'.IND_CPA_LR_experiment adversary false
        pure (bit == z)]).toReal from by
          congr 1
          exact IND_CPA_experiment_probOutput_eq_branch (encAlg' := encAlg') adversary]
  exact probOutput_uniformBool_branch_toReal_sub_half
    (encAlg'.IND_CPA_LR_experiment adversary true)
    (encAlg'.IND_CPA_LR_experiment adversary false)

/-- Telescoping identity for adjacent hybrid differences over a finite game sequence. -/
private lemma sum_hybridDiff_eq_trueProb_sub (games : ℕ → ProbComp Bool) (q : ℕ) :
    Finset.sum (Finset.range q)
      (fun i => (Pr[= true | games i]).toReal - (Pr[= true | games (i + 1)]).toReal) =
      (Pr[= true | games 0]).toReal - (Pr[= true | games q]).toReal := by
  let f : ℕ → ℝ := fun i => (Pr[= true | games i]).toReal
  have hsub : Finset.sum (Finset.range q) (fun i => f (i + 1)) -
      Finset.sum (Finset.range q) (fun i => f i) = f q - f 0 := by
    simpa [f] using (Finset.sum_range_sub (f := f) q)
  have hneg := congrArg Neg.neg hsub
  calc
    Finset.sum (Finset.range q) (fun i => f i - f (i + 1))
        = -(Finset.sum (Finset.range q) (fun i => f (i + 1)) -
            Finset.sum (Finset.range q) (fun i => f i)) := by
              simp [Finset.sum_sub_distrib]
    _ = -(f q - f 0) := by simpa using hneg
    _ = f 0 - f q := by ring

/-- Generic telescoping identity for multi-query game-hopping:
if `games 0` is the target IND-CPA experiment and `games q` has success probability `1/2`,
then the signed IND-CPA advantage is the sum of adjacent hybrid differences. -/
theorem IND_CPA_signedAdvantageReal_eq_sum_hybridDiff
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ) (games : ℕ → ProbComp Bool)
    (h0 : (Pr[= true | games 0]).toReal =
      (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal)
    (hq : (Pr[= true | games q]).toReal = (1 / 2 : ℝ)) :
    IND_CPA_signedAdvantageReal (encAlg' := encAlg') adversary =
      Finset.sum (Finset.range q) (fun i =>
        (Pr[= true | games i]).toReal - (Pr[= true | games (i + 1)]).toReal) := by
  unfold IND_CPA_signedAdvantageReal
  calc
    (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal - 1 / 2
        = (Pr[= true | games 0]).toReal - (Pr[= true | games q]).toReal := by linarith
    _ = Finset.sum (Finset.range q)
          (fun i => (Pr[= true | games i]).toReal -
            (Pr[= true | games (i + 1)]).toReal) := by
          simpa using (sum_hybridDiff_eq_trueProb_sub (games := games) q).symm

/-- Generic multi-query bound: absolute signed IND-CPA advantage is at most the sum of absolute
adjacent hybrid gaps. -/
theorem IND_CPA_abs_signedAdvantageReal_le_sum_hybridDiff_abs
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ) (games : ℕ → ProbComp Bool)
    (h0 : (Pr[= true | games 0]).toReal =
      (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal)
    (hq : (Pr[= true | games q]).toReal = (1 / 2 : ℝ)) :
    |IND_CPA_signedAdvantageReal (encAlg' := encAlg') adversary| ≤
      Finset.sum (Finset.range q) (fun i =>
        |(Pr[= true | games i]).toReal - (Pr[= true | games (i + 1)]).toReal|) := by
  rw [IND_CPA_signedAdvantageReal_eq_sum_hybridDiff (encAlg' := encAlg') adversary q games h0 hq]
  simpa using
    (Finset.abs_sum_le_sum_abs
      (s := Finset.range q)
      (f := fun i => (Pr[= true | games i]).toReal -
        (Pr[= true | games (i + 1)]).toReal))

/-- Compatibility bridge to the existing `IND_CPA_advantage` API:
the `toReal` of the `ℝ≥0∞` signed advantage is bounded by the absolute signed real advantage. -/
theorem IND_CPA_advantage_toReal_le_abs_signedAdvantageReal
    (adversary : encAlg'.IND_CPA_adversary) :
    (IND_CPA_advantage (encAlg := encAlg') adversary).toReal ≤
      |IND_CPA_signedAdvantageReal (encAlg' := encAlg') adversary| := by
  unfold IND_CPA_advantage IND_CPA_signedAdvantageReal
  simpa using
    (ENNReal.toReal_sub_le_abs_toReal_sub
      (a := Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary])
      (b := (1 / 2 : ℝ≥0∞)))

/-- When the counter is above both thresholds, two hybrid LR counted oracles agree pointwise. -/
lemma IND_CPA_hybridLR_counted_run_eq_of_ge
    (pk : PK) (k : ℕ)
    (t : encAlg'.IND_CPA_oracleSpec.Domain)
    (st : encAlg'.IND_CPA_CountedState)
    (hst : st.2 ≥ k + 1) :
    (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k t).run st =
      (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (k + 1) t).run st := by
  cases t with
  | inl tu =>
      rfl
  | inr mm =>
      change (IND_CPA_countedChallengeOracle pk
          (fun n mm => if n < k then mm.1 else mm.2) mm).run st =
        (IND_CPA_countedChallengeOracle pk
          (fun n mm => if n < k + 1 then mm.1 else mm.2) mm).run st
      simp only [IND_CPA_countedChallengeOracle, StateT.run_bind, StateT.run_get, pure_bind]
      rcases st.1 mm with _ | c
      · simp only [show ¬(st.2 < k) from by omega, show ¬(st.2 < k + 1) from by omega,
          ite_false]
      · rfl

/-- Counter monotonicity for the hybrid LR counted oracle: the counter never decreases. -/
lemma IND_CPA_hybridLR_counted_counter_le
    (pk : PK) (k : ℕ)
    (t : encAlg'.IND_CPA_oracleSpec.Domain)
    (st : encAlg'.IND_CPA_CountedState)
    (p : encAlg'.IND_CPA_oracleSpec.Range t × encAlg'.IND_CPA_CountedState)
    (hp : p ∈ support ((encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k t).run st)) :
    st.2 ≤ p.2.2 := by
  cases t with
  | inl tu =>
      simp only [IND_CPA_queryImpl_hybridLR_counted, IND_CPA_queryImplFromChallenge,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        liftM, monadLift] at hp
      change p ∈ support ((StateT.lift _).run st) at hp
      rw [StateT.run_lift, mem_support_bind_iff] at hp
      obtain ⟨a, _, ha⟩ := hp
      rw [mem_support_pure_iff] at ha
      have hst : p.2 = st := congrArg Prod.snd ha
      simp [hst]
  | inr mm =>
      have hp' :
          p ∈ support ((IND_CPA_hybridChallengeOracleLR_counted (encAlg' := encAlg') pk k mm).run
            st) := by
        simpa [IND_CPA_queryImpl_hybridLR_counted, IND_CPA_queryImplFromChallenge] using hp
      clear hp
      revert hp'
      simp only [IND_CPA_hybridChallengeOracleLR_counted, IND_CPA_countedChallengeOracle]
      rcases hcache : st.1 mm with _ | c <;> intro hp
      · simp only [hcache, StateT.run_bind, StateT.run_get, pure_bind] at hp
        change (_ : (ofFn fun _ ↦ C).Range mm × encAlg'.IND_CPA_CountedState) ∈ _ at hp
        simp only [StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
          Set.mem_singleton_iff] at hp
        obtain ⟨c, _, ⟨i, hi, hp⟩⟩ := hp
        simp only [StateT.run_set, support_pure, Set.mem_singleton_iff] at hi
        subst hi
        simp only [hp]
        omega
      · simp only [hcache, StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure] at hp
        have := congrArg (fun x => x.2.2) hp
        simp at this
        omega

/-- Behavior of the hybrid challenge oracle on a cache miss. -/
lemma IND_CPA_hybridChallengeOracleLR_counted_run_none
    (pk : PK) (k : ℕ) (mm : M × M)
    (st : encAlg'.IND_CPA_CountedState)
    (hcache : st.1 mm = none) :
    (encAlg'.IND_CPA_hybridChallengeOracleLR_counted pk k mm).run st =
      (do
        let c ← encAlg'.encrypt pk (if st.2 < k then mm.1 else mm.2)
        pure (c, (st.1.cacheQuery mm c, st.2 + 1))) := by
  simp only [IND_CPA_hybridChallengeOracleLR_counted, IND_CPA_countedChallengeOracle,
    StateT.run_bind, StateT.run_get, pure_bind, hcache, StateT.run_set, StateT.run_pure]
  simp

/-- Behavior of the hybrid challenge oracle on a cache hit. -/
lemma IND_CPA_hybridChallengeOracleLR_counted_run_some
    (pk : PK) (k : ℕ) (mm : M × M) (c : C)
    (st : encAlg'.IND_CPA_CountedState)
    (hcache : st.1 mm = some c) :
    (encAlg'.IND_CPA_hybridChallengeOracleLR_counted pk k mm).run st =
      pure (c, st) := by
  simp only [IND_CPA_hybridChallengeOracleLR_counted, IND_CPA_countedChallengeOracle,
    StateT.run_bind, StateT.run_get, pure_bind, hcache, StateT.run_pure]

end MultiQueryHybrid

end AsymmEncAlg
