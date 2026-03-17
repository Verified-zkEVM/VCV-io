/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.Defs
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Asymmetric Encryption Schemes: IND-CPA

This file develops IND-CPA security for asymmetric encryption schemes at three levels:

- oracle-based multi-query adversaries against a cached left/right challenge oracle,
- two-phase one-time adversaries,
- generic left/right hybrid games and counted-query transport lemmas for multi-query proofs.

In addition to the basic game definitions, it contains:

- the generic embedding of one-time adversaries into the oracle IND-CPA interface,
- generic telescoping lemmas for hybrid arguments,
- a generic step-adversary extraction that isolates the next fresh LR query of an
  oracle adversary as a one-time challenge.
-/

open OracleSpec OracleComp ENNReal

universe u v w

namespace AsymmEncAlg

variable {m : Type → Type v} {M PK SK C : Type}
  (encAlg : AsymmEncAlg m M PK SK C)

section IND_CPA_Oracle

variable [DecidableEq M] [DecidableEq C]

/-- Oracle-based multi-query IND-CPA game. The adversary gets oracle access to an encryption
oracle that encrypts one of two challenge messages depending on a hidden bit.

API changes from the old version:
- `unifSpec ++ₒ` → `unifSpec +`
- `⟨fun (query () (m₁, m₂)) => ...⟩` → `fun (m₁, m₂) => ...`
- `idOracle ++ₛₒ` → `QueryImpl.ofLift ... .liftTarget ... +`
- `guard (b = b')` → `return (b == b')` (Bool-valued experiment) -/
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

/-- Cached LR-oracle implementation for IND-CPA: repeated challenge queries are answered from the
cache, and fresh ones encrypt the selected branch. -/
def IND_CPA_queryImpl' (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (pk : PK) (b : Bool) : QueryImpl encAlg.IND_CPA_oracleSpec
      (StateT ((M × M →ₒ C).QueryCache) ProbComp) :=
  have so : QueryImpl (M × M →ₒ C) ProbComp := fun (m₁, m₂) =>
    encAlg.encrypt pk (if b then m₁ else m₂)
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT ((M × M →ₒ C).QueryCache) ProbComp) + so.withCaching

/-- Uncached LR-oracle implementation for IND-CPA, useful when the caller manages caching or
counting separately. -/
def IND_CPA_queryImpl (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (pk : PK) (b : Bool) : QueryImpl encAlg.IND_CPA_oracleSpec
      (StateT ((M × M →ₒ C).QueryCache) ProbComp) :=
  have so : QueryImpl (M × M →ₒ C) ProbComp := fun (m₁, m₂) =>
    encAlg.encrypt pk (if b then m₁ else m₂)
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT ((M × M →ₒ C).QueryCache) ProbComp) +
    so.liftTarget (StateT ((M × M →ₒ C).QueryCache) ProbComp)

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
  (M × M →ₒ C).QueryCache × ℕ

omit [DecidableEq M] [DecidableEq C] in
private lemma IND_CPA_countedState_run_liftM_eq {α : Type}
    (st : encAlg'.IND_CPA_CountedState) (x : ProbComp α) :
    (liftM x : StateT encAlg'.IND_CPA_CountedState ProbComp α).run st =
      x >>= fun a => pure (a, st) := by
  simp

/-- The real IND-CPA challenge oracle, but with an explicit counter that increments on cache
misses. -/
def IND_CPA_challengeOracle'_counted
    (pk : PK) (b : Bool) :
    QueryImpl (M × M →ₒ C)
      (StateT encAlg'.IND_CPA_CountedState ProbComp) := fun mm => do
  let st ← get
  match st.1 mm with
  | some c => return c
  | none =>
      let c ← encAlg'.encrypt pk (if b then mm.1 else mm.2)
      let cache' := st.1.cacheQuery mm c
      set (cache', st.2 + 1)
      return c

/-- The cached real IND-CPA query implementation, extended with an explicit query counter. -/
def IND_CPA_queryImpl'_counted
    (pk : PK) (b : Bool) : QueryImpl encAlg'.IND_CPA_oracleSpec
      (StateT encAlg'.IND_CPA_CountedState ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT encAlg'.IND_CPA_CountedState ProbComp) +
    encAlg'.IND_CPA_challengeOracle'_counted pk b

/-- Counted left/right hybrid oracle: the first `leftUntil` fresh LR queries use the left
message and all later fresh queries use the right message. Repeated queries are answered from
the cache. -/
def IND_CPA_hybridChallengeOracleLR_counted
    (pk : PK) (leftUntil : ℕ) :
    QueryImpl (M × M →ₒ C)
      (StateT encAlg'.IND_CPA_CountedState ProbComp) := fun mm => do
  let st ← get
  match st.1 mm with
  | some c => return c
  | none =>
      let c ← encAlg'.encrypt pk (if st.2 < leftUntil then mm.1 else mm.2)
      let cache' := st.1.cacheQuery mm c
      set (cache', st.2 + 1)
      return c

/-- Full counted query implementation for the generic left-prefix/right-suffix hybrid family. -/
def IND_CPA_queryImpl_hybridLR_counted
    (pk : PK) (leftUntil : ℕ) : QueryImpl encAlg'.IND_CPA_oracleSpec
      (StateT encAlg'.IND_CPA_CountedState ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT encAlg'.IND_CPA_CountedState ProbComp) +
    encAlg'.IND_CPA_hybridChallengeOracleLR_counted pk leftUntil

/-- The generic left/right hybrid family: the first `leftUntil` fresh LR queries use the left
branch, and all later fresh queries use the right branch. -/
def IND_CPA_LR_hybridGame
    (adversary : encAlg'.IND_CPA_adversary) (leftUntil : ℕ) : ProbComp Bool := do
  let (pk, _sk) ← encAlg'.keygen
  (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (adversary pk)).run' (∅, 0)

omit [DecidableEq C] in
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
      simp only [IND_CPA_queryImpl'_counted, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        liftM, monadLift, StateT.instMonadLift] at hp
      rw [StateT.run_lift, mem_support_bind_iff] at hp
      obtain ⟨a, _, ha⟩ := hp
      rw [mem_support_pure_iff] at ha
      have hst : p.2 = st := congrArg Prod.snd ha
      simp [hst]
  | inr mm =>
      change p ∈ support ((encAlg'.IND_CPA_challengeOracle'_counted pk b mm).run st) at hp
      revert hp
      rcases hcache : st.1 mm with _ | c <;> intro hp
      · simp only [IND_CPA_challengeOracle'_counted, hcache,
          StateT.run_bind, StateT.run_get, pure_bind] at hp
        rw [mem_support_iff] at hp
        rw [← mem_support_iff] at hp
        simp only [StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
          Set.mem_singleton_iff] at hp
        obtain ⟨c, _, ⟨i, hi, hp⟩⟩ := hp
        simp only [StateT.run_set, support_pure,
          Set.mem_singleton_iff] at hi
        subst hi
        simp only [hp]
        omega
      · simp only [IND_CPA_challengeOracle'_counted, hcache,
          StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hp
        have := congrArg (fun x => x.2.2) hp
        simp at this
        omega

omit [DecidableEq C] in
/-- Projecting away the counter from the counted real IND-CPA implementation recovers the
ordinary cached real implementation. -/
lemma IND_CPA_queryImpl'_counted_proj_eq_queryImpl'
    (pk : PK) (b : Bool)
    (t : encAlg'.IND_CPA_oracleSpec.Domain)
    (st : encAlg'.IND_CPA_CountedState) :
    Prod.map id Prod.fst <$> (encAlg'.IND_CPA_queryImpl'_counted pk b t).run st =
      ((encAlg'.IND_CPA_queryImpl' pk b) t).run st.1 := by
  rcases st with ⟨cache, n⟩
  cases t with
  | inl tu =>
      simp [IND_CPA_queryImpl'_counted, IND_CPA_queryImpl']
  | inr mm =>
      rcases hcache : cache mm with _ | c
      · have hcounted :
            Prod.map id Prod.fst <$>
              (encAlg'.IND_CPA_challengeOracle'_counted pk b mm).run (cache, n) =
            (do
              let c ← encAlg'.encrypt pk (if b then mm.1 else mm.2)
              pure (c, cache.cacheQuery mm c) : ProbComp _) := by
          simp only [IND_CPA_challengeOracle'_counted, hcache,
            StateT.run_bind, StateT.run_get, pure_bind,
            IND_CPA_countedState_run_liftM_eq (encAlg' := encAlg') (st := (cache, n)),
            bind_assoc, StateT.run_pure]
          rw [map_bind]
          refine bind_congr fun c => ?_
          simp
        have hreal :
            ((encAlg'.IND_CPA_queryImpl' pk b) (Sum.inr mm)).run cache =
            (do
              let c ← encAlg'.encrypt pk (if b then mm.1 else mm.2)
              pure (c, cache.cacheQuery mm c) : ProbComp _) := by
          simp [IND_CPA_queryImpl', QueryImpl.withCaching_apply, hcache,
            StateT.run_bind, StateT.run_get, pure_bind]
        simpa [IND_CPA_queryImpl'_counted] using hcounted.trans hreal.symm
      · simp [IND_CPA_queryImpl'_counted, IND_CPA_challengeOracle'_counted,
          IND_CPA_queryImpl', QueryImpl.withCaching_apply, hcache,
          StateT.run_bind, StateT.run_get, pure_bind]

omit [DecidableEq C] in
/-- The `leftUntil = 0` left/right hybrid is exactly the all-right endpoint game once the
counter is projected away. -/
lemma IND_CPA_queryImpl_hybridLR_counted_proj_eq_queryImpl'_false
    (pk : PK)
    (t : encAlg'.IND_CPA_oracleSpec.Domain)
    (st : encAlg'.IND_CPA_CountedState) :
    Prod.map id Prod.fst <$> (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk 0 t).run st =
      ((encAlg'.IND_CPA_queryImpl' pk false) t).run st.1 := by
  rcases st with ⟨cache, n⟩
  cases t with
  | inl tu =>
      simp [IND_CPA_queryImpl_hybridLR_counted, IND_CPA_queryImpl']
  | inr mm =>
      rcases hcache : cache mm with _ | c
      · have hcounted :
            Prod.map id Prod.fst <$>
              (encAlg'.IND_CPA_hybridChallengeOracleLR_counted pk 0 mm).run (cache, n) =
            (do
              let c ← encAlg'.encrypt pk mm.2
              pure (c, cache.cacheQuery mm c) : ProbComp _) := by
          simp only [IND_CPA_hybridChallengeOracleLR_counted, hcache,
            StateT.run_bind, StateT.run_get, pure_bind, Nat.not_lt_zero,
            IND_CPA_countedState_run_liftM_eq (encAlg' := encAlg') (st := (cache, n)),
            bind_assoc, StateT.run_pure]
          rw [map_bind]
          refine bind_congr fun c => ?_
          simp
        have hreal :
            ((encAlg'.IND_CPA_queryImpl' pk false) (Sum.inr mm)).run cache =
            (do
              let c ← encAlg'.encrypt pk mm.2
              pure (c, cache.cacheQuery mm c) : ProbComp _) := by
          simp [IND_CPA_queryImpl', QueryImpl.withCaching_apply, hcache,
            StateT.run_bind, StateT.run_get, pure_bind]
        simpa [IND_CPA_queryImpl_hybridLR_counted] using hcounted.trans hreal.symm
      · simp [IND_CPA_queryImpl_hybridLR_counted, IND_CPA_hybridChallengeOracleLR_counted,
          IND_CPA_queryImpl', QueryImpl.withCaching_apply, hcache,
          StateT.run_bind, StateT.run_get, pure_bind]

omit [DecidableEq C] in
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
            simp only [IND_CPA_queryImpl'_counted, QueryImpl.add_apply_inl,
              QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
              liftM, monadLift, StateT.instMonadLift] at hz
            rw [StateT.run_lift, mem_support_bind_iff] at hz
            obtain ⟨a, _, ha⟩ := hz
            rw [mem_support_pure_iff] at ha
            have hst : z.2 = st := congrArg Prod.snd ha
            simpa [cost, hst] using hInv
        | inr mm =>
            have hsucc := encAlg'.IND_CPA_queryImpl'_counted_counter_le_succ pk b (Sum.inr mm) st z hz
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
      (OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq
        (impl₁ := encAlg'.IND_CPA_queryImpl'_counted pk b)
        (impl₂ := encAlg'.IND_CPA_queryImpl' pk b)
        (proj := Prod.fst)
        (hproj := encAlg'.IND_CPA_queryImpl'_counted_proj_eq_queryImpl' pk b)
        comp (cache, n))
  exact hcounted_run'.trans hreal_run'

omit [DecidableEq C] in
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
      let b ← ($ᵗ Bool : ProbComp Bool)
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

section IND_CPA_TwoPhase

variable {ι : Type} {spec : OracleSpec ι} [DecidableEq M] [DecidableEq C]

/-- Two-phase adversary for IND-CPA security.
Removed `AlternativeMonad` and `LawfulAlternative` requirements from the older API. -/
structure IND_CPA_Adv (encAlg : AsymmEncAlg m M PK SK C) where
  State : Type
  chooseMessages : PK → m (M × M × State)
  distinguish : State → C → m Bool

variable {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
  (adv : IND_CPA_Adv encAlg)

/-- One-time IND-CPA experiment for an asymmetric encryption algorithm:
sample keys, let the adversary choose challenge messages, encrypt one branch, and return whether
the adversary guessed the hidden bit. -/
def IND_CPA_OneTime_Game : ProbComp Bool :=
  encAlg.exec do
    let b : Bool ← encAlg.lift_probComp ($ᵗ Bool)
    let (pk, _) ← encAlg.keygen
    let (m₁, m₂, state) ← adv.chooseMessages pk
    let msg := if b then m₁ else m₂
    let c ← encAlg.encrypt pk msg
    let b' ← adv.distinguish state c
    return (b == b')

/-- Real-valued one-time IND-CPA advantage. -/
noncomputable def IND_CPA_OneTime_Advantage (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
    (adv : IND_CPA_Adv encAlg) : ℝ :=
  (IND_CPA_OneTime_Game (encAlg := encAlg) adv).boolBiasAdvantage

section OracleLift

variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

/-- One-time IND-CPA game specialized to `ProbComp` execution, without an outer `exec` wrapper.
This is the canonical target for generic one-query lifts into the oracle IND-CPA interface. -/
def IND_CPA_OneTime_Game_ProbComp (adv : IND_CPA_Adv encAlg') : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (pk, _) ← encAlg'.keygen
  let (m₁, m₂, state) ← adv.chooseMessages pk
  let msg := if b then m₁ else m₂
  let c ← encAlg'.encrypt pk msg
  let b' ← adv.distinguish state c
  return (b == b')

/-- Embed a two-phase one-time adversary into the oracle IND-CPA interface by issuing exactly
one LR challenge query. This construction is scheme-agnostic. -/
def IND_CPA_adversary_of_OneTime_raw (adv : IND_CPA_Adv encAlg') :
    PK → OracleComp (unifSpec + (M × M →ₒ C)) Bool := fun pk => do
  let (m₁, m₂, st) ←
    (OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + (M × M →ₒ C))
      (adv.chooseMessages pk))
  let c ← query (spec := unifSpec + (M × M →ₒ C)) (Sum.inr (m₁, m₂))
  OracleComp.liftComp (spec := unifSpec)
    (superSpec := unifSpec + (M × M →ₒ C))
    (adv.distinguish st c)

/-- Bundle the raw one-query embedding as an oracle IND-CPA adversary over `encAlg'`. -/
def IND_CPA_adversary_of_OneTime (adv : IND_CPA_Adv encAlg') :
    encAlg'.IND_CPA_adversary := by
  simpa [IND_CPA_adversary, IND_CPA_oracleSpec] using
    (IND_CPA_adversary_of_OneTime_raw (encAlg' := encAlg') adv)

/-- Proof obligation for the one-query lift: the oracle IND-CPA experiment with the embedded
adversary agrees with the direct one-time `ProbComp` game. -/
abbrev IND_CPA_experiment_adversary_of_OneTime_eq_oneTimeGameObligation
    [DecidableEq M] [DecidableEq C] (adv : IND_CPA_Adv encAlg') : Prop :=
  IND_CPA_experiment (encAlg := encAlg') (IND_CPA_adversary_of_OneTime (encAlg' := encAlg') adv) =
    IND_CPA_OneTime_Game_ProbComp (encAlg' := encAlg') adv

/-- `ℝ≥0∞` one-time signed IND-CPA advantage, aligned with `IND_CPA_advantage`. -/
noncomputable def IND_CPA_OneTime_AdvantageENN (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (adv : IND_CPA_Adv encAlg) : ℝ≥0∞ :=
  Pr[= true | IND_CPA_OneTime_Game_ProbComp (encAlg' := encAlg) adv] - 1 / 2

omit [DecidableEq M] [DecidableEq C] in
/-- Generic advantage equality for adversaries obtained from the one-query embedding,
once the game-equivalence obligation is discharged. -/
theorem IND_CPA_advantage_adversary_of_OneTime_eq_oneTimeAdvantageENN_of_obligation
    [DecidableEq M] [DecidableEq C]
    (adv : IND_CPA_Adv encAlg') :
    IND_CPA_experiment_adversary_of_OneTime_eq_oneTimeGameObligation
      (encAlg' := encAlg') adv →
    IND_CPA_advantage (encAlg := encAlg') (IND_CPA_adversary_of_OneTime (encAlg' := encAlg') adv) =
      IND_CPA_OneTime_AdvantageENN (encAlg := encAlg') adv := by
  intro hgame
  unfold IND_CPA_advantage IND_CPA_OneTime_AdvantageENN
  simpa using congrArg (fun p : ℝ≥0∞ => p - 1 / 2)
    (congrArg (fun g : ProbComp Bool => Pr[= true | g])
      hgame)

/-- Obligation form for reducing an arbitrary oracle IND-CPA adversary to a one-query
two-phase adversary. -/
abbrev IND_CPA_oneQueryFactorizationObligation [DecidableEq M] [DecidableEq C]
    (adversary : encAlg'.IND_CPA_adversary) : Prop :=
  ∃ adv : IND_CPA_Adv encAlg',
    adversary = IND_CPA_adversary_of_OneTime (encAlg' := encAlg') adv ∧
      IND_CPA_experiment_adversary_of_OneTime_eq_oneTimeGameObligation
        (encAlg' := encAlg') adv

omit [DecidableEq M] [DecidableEq C] in
/-- Generic one-query lift: if a multi-query oracle adversary factors through a one-query
two-phase adversary, then its IND-CPA advantage is exactly the corresponding one-time advantage. -/
theorem IND_CPA_advantage_eq_oneTimeAdvantageENN_of_oneQueryFactorization
    [DecidableEq M] [DecidableEq C]
    (adversary : encAlg'.IND_CPA_adversary)
    (hfactor : IND_CPA_oneQueryFactorizationObligation (encAlg' := encAlg') adversary) :
    ∃ adv : IND_CPA_Adv encAlg',
      IND_CPA_advantage (encAlg := encAlg') adversary =
        IND_CPA_OneTime_AdvantageENN (encAlg := encAlg') adv := by
  rcases hfactor with ⟨adv, rfl, hgame⟩
  exact ⟨adv, IND_CPA_advantage_adversary_of_OneTime_eq_oneTimeAdvantageENN_of_obligation
    (encAlg' := encAlg') adv hgame⟩

end OracleLift

section MultiQueryToOneTime

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

end MultiQueryToOneTime

section MultiQueryHybridLift

variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

omit [DecidableEq C] in
private lemma IND_CPA_LR_hybridGame_zero_evalDist_eq_right
    (adversary : encAlg'.IND_CPA_adversary) :
    evalDist (encAlg'.IND_CPA_LR_hybridGame adversary 0) =
      evalDist (encAlg'.IND_CPA_LR_experiment adversary false) := by
  simp only [IND_CPA_LR_hybridGame, IND_CPA_LR_experiment, evalDist_bind]
  congr 1
  funext ⟨pk, _sk⟩
  simpa using congrArg evalDist
    (OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq
      (impl₁ := encAlg'.IND_CPA_queryImpl_hybridLR_counted pk 0)
      (impl₂ := encAlg'.IND_CPA_queryImpl' pk false)
      (proj := Prod.fst)
      (hproj := encAlg'.IND_CPA_queryImpl_hybridLR_counted_proj_eq_queryImpl'_false pk)
      (adversary pk) (∅, 0))

omit [DecidableEq C] in
private lemma IND_CPA_LR_hybridGame_q_evalDist_eq_left_of_MakesAtMostQueries
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
          cases b <;> simp [IND_CPA_queryImpl'_counted, IND_CPA_queryImpl_hybridLR_counted]
      | inr mm =>
          rcases hcache : st.1 mm with _ | c
          · cases b <;>
              simp [IND_CPA_queryImpl'_counted, IND_CPA_challengeOracle'_counted,
                IND_CPA_queryImpl_hybridLR_counted, IND_CPA_hybridChallengeOracleLR_counted,
                hcache, hcond, IND_CPA_countedState_run_liftM_eq (encAlg' := encAlg') (st := st)]
          · cases b <;>
              simp [IND_CPA_queryImpl'_counted, IND_CPA_challengeOracle'_counted,
                IND_CPA_queryImpl_hybridLR_counted, IND_CPA_hybridChallengeOracleLR_counted, hcache])
    pk true q (adversary pk) q (hq pk) ∅ 0 (by omega)

omit [DecidableEq C] in
/-- The standard random-bit IND-CPA experiment is the uniform-bit branch over the all-left and
all-right endpoint games. -/
private lemma IND_CPA_experiment_probOutput_eq_branch
    (adversary : encAlg'.IND_CPA_adversary) :
    Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary] =
      Pr[= true | do
        let bit ← ($ᵗ Bool : ProbComp Bool)
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

omit [DecidableEq C] in
/-- The signed real IND-CPA advantage is half the left/right endpoint gap. -/
theorem IND_CPA_signedAdvantageReal_eq_lrDiff_half
    (adversary : encAlg'.IND_CPA_adversary) :
    IND_CPA_signedAdvantageReal (encAlg' := encAlg') adversary =
      ((Pr[= true | encAlg'.IND_CPA_LR_experiment adversary true]).toReal -
        (Pr[= true | encAlg'.IND_CPA_LR_experiment adversary false]).toReal) / 2 := by
  unfold IND_CPA_signedAdvantageReal
  rw [show (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal =
      (Pr[= true | do
        let bit ← ($ᵗ Bool : ProbComp Bool)
        let z ← if bit then encAlg'.IND_CPA_LR_experiment adversary true
                 else encAlg'.IND_CPA_LR_experiment adversary false
        pure (bit == z)]).toReal from by
          congr 1
          exact IND_CPA_experiment_probOutput_eq_branch (encAlg' := encAlg') adversary]
  exact probOutput_uniformBool_branch_toReal_sub_half
    (encAlg'.IND_CPA_LR_experiment adversary true)
    (encAlg'.IND_CPA_LR_experiment adversary false)

/-- Telescoping identity for adjacent hybrid differences over a finite game sequence. -/
lemma sum_hybridDiff_eq_trueProb_sub (games : ℕ → ProbComp Bool) (q : ℕ) :
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

omit [DecidableEq C] in
/-- Generic telescoping identity for multi-query game-hopping:
if `games 0` is the target IND-CPA experiment and `games q` has success probability `1/2`,
then IND-CPA advantage is the sum of adjacent hybrid differences. -/
theorem IND_CPA_advantage'_eq_sum_hybridDiff
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

omit [DecidableEq C] in
/-- Generic multi-query bound: absolute IND-CPA advantage is at most the sum of absolute
adjacent hybrid gaps. -/
theorem IND_CPA_advantage'_abs_le_sum_hybridDiff_abs
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ) (games : ℕ → ProbComp Bool)
    (h0 : (Pr[= true | games 0]).toReal =
      (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal)
    (hq : (Pr[= true | games q]).toReal = (1 / 2 : ℝ)) :
    |IND_CPA_signedAdvantageReal (encAlg' := encAlg') adversary| ≤
      Finset.sum (Finset.range q) (fun i =>
        |(Pr[= true | games i]).toReal - (Pr[= true | games (i + 1)]).toReal|) := by
  rw [IND_CPA_advantage'_eq_sum_hybridDiff (encAlg' := encAlg') adversary q games h0 hq]
  simpa using
    (Finset.abs_sum_le_sum_abs
      (s := Finset.range q)
      (f := fun i => (Pr[= true | games i]).toReal -
        (Pr[= true | games (i + 1)]).toReal))

omit [DecidableEq C] in
/-- Compatibility bridge to the existing `IND_CPA_advantage` API:
the `toReal` of the `ℝ≥0∞` signed advantage is bounded by the absolute signed real advantage. -/
theorem IND_CPA_advantage_toReal_le_abs_signedAdvantageReal
    [DecidableEq C]
    (adversary : encAlg'.IND_CPA_adversary) :
    (IND_CPA_advantage (encAlg := encAlg') adversary).toReal ≤
      |IND_CPA_signedAdvantageReal (encAlg' := encAlg') adversary| := by
  unfold IND_CPA_advantage IND_CPA_signedAdvantageReal
  simpa using
    (ENNReal.toReal_tsub_le_abs_toReal_sub
      (a := Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary])
      (b := (1 / 2 : ℝ≥0∞))
      (ha := probOutput_ne_top))

end MultiQueryHybridLift

end IND_CPA_TwoPhase

end AsymmEncAlg
