/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.IND_CPA
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.EvalDist.Bool
import VCVio.ProgramLogic.Tactics
import VCVioWidgets.GameHop.Panel

/-!
# ElGamal Encryption: Multi-query IND-CPA via DDH

This file defines ElGamal encryption over a module `Module F G` and proves
multi-query oracle IND-CPA security via a q-step hybrid argument reducing to DDH.

## Mathematical notation

We use additive / EC-style notation throughout:

| Textbook (multiplicative) | This file (additive)           |
|---------------------------|--------------------------------|
| `g^a`                     | `a • gen`                      |
| `g^a · g^b = g^{a+b}`    | `a • gen + b • gen`            |
| `(g^a)^b = g^{ab}`       | `b • (a • gen) = (b * a) • gen`|
| `m · g^{ab}`              | `m + (a * b) • gen`            |

Here `F` is the scalar field (e.g. `ZMod p`), `G` is the group of elements
(e.g. elliptic curve points), and `gen : G` is a fixed public generator.

## Proof structure

1. ElGamal definition and correctness.
2. Hybrid game family: the i-th game uses real ElGamal for the first i fresh LR oracle
   queries and random masking thereafter.
3. Key lemma (`IND_CPA_allRandomHalf`): the all-random hybrid (i = 0) has success probability
   exactly 1/2, because `randomMaskedCipher` produces a uniform distribution independent of the
   message (the component `msg + y` with `y ~ U(G)` is uniform in `G`).
4. Per-hop DDH reduction (`IND_CPA_stepDDHReduction`): a DDH adversary that embeds the DDH
   challenge into the k-th fresh query, so that the DDH-real branch equals hybrid k+1 and the
   DDH-random branch equals hybrid k.
5. Per-hop bound (`IND_CPA_stepDDH_hopBound`): the absolute difference between consecutive
   hybrid winning probabilities is at most twice the DDH advantage of the step-k reduction.
6. Query-bound bridge: the `q`-th hybrid equals the actual IND-CPA experiment for adversaries
   making at most `q` fresh LR queries.
7. Main theorem (`elGamal_IND_CPA_le_q_mul_ddh`): IND-CPA advantage ≤ `q * (2ε)` where `ε`
   bounds each per-hop DDH advantage.

## Query-bound hypothesis

The final theorem takes `hq : adversary.MakesAtMostQueries q`. This hypothesis is used to prove
that the `q`-th hybrid has the same winning probability as the actual IND-CPA experiment via the
generic counted-game bridge in `AsymmEncAlg`. The intermediate theorem
`elGamal_IND_CPA_bound_toReal` exposes that starting equality as a separate hypothesis `hstart`.
-/

show_panel_widgets [local VCVioWidgets.GameHop.GameHopPanel]

open OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

/-! ## 1. ElGamal definition and correctness -/

/-- ElGamal encryption over a module `Module F G` with generator `gen : G`.

Key generation samples a scalar `sk ← $ᵗ F` and returns `(sk • gen, sk)`.
Encryption of `msg` under public key `pk` samples `r ← $ᵗ F` and returns `(r • gen, msg + r • pk)`.
Decryption recovers `msg` as `c₂ - sk • c₁`. -/
@[simps!] def elgamalAsymmEnc (F G : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G]
    (gen : G) : AsymmEncAlg ProbComp
    (M := G) (PK := G) (SK := F) (C := G × G) where
  keygen := do
    let sk ← $ᵗ F
    return (sk • gen, sk)
  encrypt := fun pk msg => do
    let r ← $ᵗ F
    return (r • gen, msg + r • pk)
  decrypt := fun sk (c₁, c₂) =>
    return (some (c₂ - sk • c₁))
  __ := ExecutionMethod.default

namespace elgamalAsymmEnc

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

@[simp] lemma toExecutionMethod_eq :
    (elgamalAsymmEnc F G gen).toExecutionMethod = ExecutionMethod.default := rfl

/-- ElGamal decryption perfectly inverts encryption: `Dec(sk, Enc(pk, msg)) = msg`. -/
theorem correct [DecidableEq G] : (elgamalAsymmEnc F G gen).PerfectlyCorrect := by
  have hcancel : ∀ (msg : G) (sk r : F),
      msg + r • (sk • gen) - sk • (r • gen) = msg := by
    intro msg sk r
    have : r • (sk • gen) = sk • (r • gen) := by
      rw [← mul_smul, ← mul_smul, mul_comm]
    rw [this, add_sub_cancel_right]
  simp [AsymmEncAlg.PerfectlyCorrect, AsymmEncAlg.CorrectExp, elgamalAsymmEnc, hcancel]

/-! ## 2. Hybrid game infrastructure -/

section IND_CPA

variable [DecidableEq G]

abbrev IND_CPA_LRCache := (G × G →ₒ G × G).QueryCache

abbrev IND_CPA_HybridState := IND_CPA_LRCache (G := G) × ℕ

omit [AddCommGroup G] [SampleableType G] [DecidableEq G] in
private lemma hybridState_run_liftM_eq {α : Type}
    (st : IND_CPA_HybridState (G := G)) (x : ProbComp α) :
    (liftM x : StateT (IND_CPA_HybridState (G := G)) ProbComp α).run st =
      x >>= fun a => pure (a, st) := by
  simp

/-- A random-masked ciphertext `(r • gen, msg + y)` with independent `r ← $ᵗ F`, `y ← $ᵗ G`,
so the second component is information-theoretically independent of the message. -/
def randomMaskedCipher (msg : G) : ProbComp (G × G) := do
  let r ← $ᵗ F
  let y ← $ᵗ G
  return (r • gen, msg + y)

/-- The hybrid LR oracle: real ElGamal for the first `realUntil` fresh queries, then
`randomMaskedCipher`; repeated queries are served from cache. -/
def IND_CPA_hybridChallengeOracle (pk : G) (b : Bool) (realUntil : ℕ) :
    QueryImpl (G × G →ₒ G × G)
      (StateT (IND_CPA_HybridState (G := G)) ProbComp) := fun mm => do
  let st ← get
  match st.1 mm with
  | some c => return c
  | none =>
      let msg : G := if b then mm.1 else mm.2
      let c ← if st.2 < realUntil then
          (elgamalAsymmEnc F G gen).encrypt pk msg
        else
          randomMaskedCipher (F := F) (gen := gen) msg
      let cache' := st.1.cacheQuery mm c
      set (cache', st.2 + 1)
      return c

/-- Full query implementation for the hybrid game: uniform oracle passthrough on the left,
hybrid LR oracle on the right. -/
def IND_CPA_queryImpl_hybrid (pk : G) (b : Bool) (realUntil : ℕ) :
    QueryImpl (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec
      (StateT (IND_CPA_HybridState (G := G)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (IND_CPA_HybridState (G := G)) ProbComp) +
    IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b realUntil

/-- The `i`-th hybrid game: samples a challenge bit `b`, runs the adversary with the first
`realUntil` fresh LR queries answered by real ElGamal and the rest by random masking,
then checks if the adversary's guess matches `b`. -/
def IND_CPA_HybridGame
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (realUntil : ℕ) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (pk, _sk) ← (elgamalAsymmEnc F G gen).keygen
  let b' ← (simulateQ
      (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil)
      (adversary pk)).run' (∅, 0)
  return (b == b')

/-- The hybrid family indexed so that `HybridFamily q 0` is the all-real game (hybrid `q`)
and `HybridFamily q q` is the all-random game (hybrid `0`). -/
def IND_CPA_HybridFamily
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (q : ℕ) : ℕ → ProbComp Bool :=
  fun i => IND_CPA_HybridGame (F := F) (gen := gen) adversary (q - i)

@[simp] lemma IND_CPA_HybridFamily_zero
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (q : ℕ) :
    IND_CPA_HybridFamily (F := F) (gen := gen) adversary q 0 =
      IND_CPA_HybridGame (F := F) (gen := gen) adversary q := by
  simp [IND_CPA_HybridFamily]

@[simp] lemma IND_CPA_HybridFamily_q
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (q : ℕ) :
    IND_CPA_HybridFamily (F := F) (gen := gen) adversary q q =
      IND_CPA_HybridGame (F := F) (gen := gen) adversary 0 := by
  simp [IND_CPA_HybridFamily]

/-- The real IND-CPA experiment for ElGamal, packaged as a `ProbComp Bool`. -/
abbrev IND_CPA_game
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) : ProbComp Bool :=
  (elgamalAsymmEnc F G gen).IND_CPA_experiment adversary

/-! ## 3. All-random hybrid has probability 1/2 -/

open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational

omit [Fintype F] [DecidableEq F] in
lemma randomMaskedCipher_dist_indep (m₁ m₂ : G) :
    evalDist (randomMaskedCipher (F := F) (gen := gen) m₁) =
    evalDist (randomMaskedCipher (F := F) (gen := gen) m₂) := by
  apply evalDist_ext; intro ⟨c₁, c₂⟩
  simp only [randomMaskedCipher, probOutput_bind_eq_tsum, probOutput_pure, Prod.mk.injEq]
  congr 1; funext r; congr 1
  by_cases h : c₁ = r • gen
  · simp only [h, true_and]
    have hsum : ∀ msg : G,
        (∑' y, Pr[= y | $ᵗ G] * if c₂ = msg + y then 1 else 0) =
          Pr[= -msg + c₂ | $ᵗ G] := by
      intro msg
      rw [tsum_eq_single (-msg + c₂)]
      · have : msg + (-msg + c₂) = c₂ := by abel
        simp [this]
      · intro y hy
        have : c₂ ≠ msg + y := fun heq => hy (show y = -msg + c₂ by rw [heq]; abel)
        simp [this]
    rw [hsum, hsum]
    exact SampleableType.probOutput_selectElem_eq _ _
  · simp [h]

private lemma hybridChallengeOracle_allRandom_evalDist_eq
    (pk : G) (mm : G × G) (s : IND_CPA_HybridState (G := G)) :
    evalDist ((IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk true 0 mm).run s) =
    evalDist ((IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk false 0 mm).run s) := by
  simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind, StateT.run_get, pure_bind,
    Nat.not_lt_zero, ite_false]
  cases hs : s.1 mm with
  | some _ => rfl
  | none =>
    simp only [show ∀ (a b : G), (if (false : Bool) = true then a else b) = b
        from fun _ _ => if_neg (by decide), ite_true]
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    simp only [hybridState_run_liftM_eq (G := G),
      bind_assoc, pure_bind]
    rw [evalDist_bind, evalDist_bind]
    congr 1
    · exact randomMaskedCipher_dist_indep (F := F) (gen := gen) mm.1 mm.2

lemma IND_CPA_hybridOracle_allRandom_eqDist
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (pk : G) :
    RelTriple
      ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk true 0)
        (adversary pk)).run' (∅, 0))
      ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk false 0)
        (adversary pk)).run' (∅, 0))
      (EqRel _) := by
  rvcgen_step
  · intro t s
    cases t with
    | inl _ => rfl
    | inr mm => exact hybridChallengeOracle_allRandom_evalDist_eq (F := F) (gen := gen) pk mm s
  · rfl

/-- The all-random hybrid (no real encryptions) has success probability exactly `1/2`,
because `randomMaskedCipher` produces a distribution independent of the chosen message. -/
theorem IND_CPA_allRandomHalf
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) :
    Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary 0] = 1 / 2 := by
  simp only [IND_CPA_HybridGame,
    show ∀ (a b : Bool), (a == b) = decide (a = b) from by decide]
  have hassoc : ∀ b : Bool,
      ((elgamalAsymmEnc F G gen).keygen >>= fun x =>
        (simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) x.1 b 0)
          (adversary x.1)).run' (∅, 0) >>= fun b' =>
          pure (decide (b = b'))) =
      ((elgamalAsymmEnc F G gen).keygen >>= fun x =>
        (simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) x.1 b 0)
          (adversary x.1)).run' (∅, 0)) >>= fun b' =>
        pure (decide (b = b')) :=
    fun _ => (bind_assoc _ _ _).symm
  simp_rw [hassoc]
  exact probOutput_decide_eq_uniformBool_half _ (by
    simp only [evalDist_bind]
    congr 1; funext ⟨pk, _⟩
    by_equiv
    exact IND_CPA_hybridOracle_allRandom_eqDist (F := F) (gen := gen) adversary pk)

/-! ## 4. Per-hop DDH reduction -/

private def IND_CPA_stepDDHOracle
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G) :
    QueryImpl (G × G →ₒ G × G)
      (StateT (IND_CPA_HybridState (G := G)) ProbComp) := fun (m₁, m₂) => do
  let st ← get
  match st.1 (m₁, m₂) with
  | some c => return c
  | none =>
      let msg : G := if b then m₁ else m₂
      let c ←
        if st.2 < k then
          (elgamalAsymmEnc F G gen).encrypt pk msg
        else if st.2 = k then
          pure (x₂, msg + x₃)
        else
          randomMaskedCipher (F := F) (gen := gen) msg
      let cache' := st.1.cacheQuery (m₁, m₂) c
      set (cache', st.2 + 1)
      return c

private def IND_CPA_stepDDHQueryImpl
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G) :
    QueryImpl (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec
      (StateT (IND_CPA_HybridState (G := G)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (IND_CPA_HybridState (G := G)) ProbComp) +
    IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k x₂ x₃

/-- The per-hop DDH reduction: given a DDH challenge `(gen, pk, x₂, x₃)`, embeds it into
the `k`-th fresh LR query. When `x₃ = (a * b_scalar) • gen` (DDH-real), the simulation
matches hybrid `k+1`; when `x₃ = c • gen` for random `c` (DDH-random), it matches
hybrid `k` (requires `Function.Bijective (· • gen : F → G)`). -/
def IND_CPA_stepDDHReduction
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (k : ℕ) : DiffieHellman.DDHAdversary F G :=
  fun _g pk x₂ x₃ => do
    let b ← $ᵗ Bool
    let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃)
      (adversary pk)).run' (∅, 0)
    return (b == b')

/-! ## 5. Per-hop bound -/
private lemma hybridBranch_probOutput_eq
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (realUntil : ℕ) (lhs : F → Bool → ProbComp Bool)
    (h : ∀ a b,
      evalDist (lhs a b) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) (a • gen) b realUntil)
          (adversary (a • gen))).run' (∅, 0))) :
    Pr[= true | do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let a ← ($ᵗ F : ProbComp F)
      let z ← lhs a b
      pure (b == z)] =
    Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary realUntil] := by
  simp [IND_CPA_HybridGame, elgamalAsymmEnc]
  qvcgen_step rw congr' as ⟨b⟩
  qvcgen_step rw congr' as ⟨a⟩
  simpa using
    (probOutput_map_eq_of_evalDist_eq (f := fun z => b == z) (y := true) (h a b))

-- Mechanical StateT bookkeeping: the step DDH oracle agrees with the hybrid oracle
-- for queries past position k.
private lemma stepDDHOracle_eq_hybridChallenge_post_k
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G)
    (m₁ m₂ : G) (st : IND_CPA_HybridState (G := G)) (hgt : k < st.2) :
    (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k x₂ x₃ (m₁, m₂)).run st =
    (IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b (k + 1) (m₁, m₂)).run st := by
  simp only [IND_CPA_stepDDHOracle, IND_CPA_hybridChallengeOracle]
  rcases h : st.1 (m₁, m₂) with _ | c
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, h,
      if_neg (by omega : ¬ st.2 < k), if_neg (by omega : ¬ (st.2 = k)),
      if_neg (by omega : ¬ st.2 < k + 1)]
  · simp [StateT.run_bind, StateT.run_get, pure_bind, h]

private lemma stepDDHOracle_eq_hybridChallenge_post_k_rand
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G)
    (m₁ m₂ : G) (st : IND_CPA_HybridState (G := G)) (hgt : k < st.2) :
    (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k x₂ x₃ (m₁, m₂)).run st =
    (IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b k (m₁, m₂)).run st := by
  simp only [IND_CPA_stepDDHOracle, IND_CPA_hybridChallengeOracle]
  rcases h : st.1 (m₁, m₂) with _ | c
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, h,
      if_neg (by omega : ¬ st.2 < k), if_neg (by omega : ¬ (st.2 = k))]
  · simp [StateT.run_bind, StateT.run_get, pure_bind, h]

private lemma stepDDHQueryImpl_eq_hybridQueryImpl_post_k
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G) (realUntil : ℕ)
    (hrealUntil : realUntil = k ∨ realUntil = k + 1)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G)) (hgt : k < st.2) :
    (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃ t).run st =
    (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil t).run st := by
  cases t with
  | inl tu =>
      simp [IND_CPA_stepDDHQueryImpl, IND_CPA_queryImpl_hybrid]
  | inr mm =>
      obtain ⟨m₁, m₂⟩ := mm
      simp only [IND_CPA_stepDDHQueryImpl, IND_CPA_queryImpl_hybrid]
      rcases hrealUntil with h | h <;> simp only [h]
      · exact stepDDHOracle_eq_hybridChallenge_post_k_rand
          (F := F) (gen := gen) pk b k x₂ x₃ m₁ m₂ st hgt
      · exact stepDDHOracle_eq_hybridChallenge_post_k
          (F := F) (gen := gen) pk b k x₂ x₃ m₁ m₂ st hgt

private lemma hybridQueryImpl_counter_mono
    (pk : G) (b : Bool) (realUntil : ℕ)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G))
    (p : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Range t × IND_CPA_HybridState (G := G))
    (hp : p ∈ support ((IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil t).run st)) :
    st.2 ≤ p.2.2 := by
  cases t with
  | inl tu =>
      simp only [IND_CPA_queryImpl_hybrid, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        liftM, monadLift, StateT.instMonadLift] at hp
      rw [StateT.run_lift, mem_support_bind_iff] at hp
      obtain ⟨a, _, ha⟩ := hp
      rw [mem_support_pure_iff] at ha
      have h2 : p.2 = st := congrArg Prod.snd ha
      simp [h2]
  | inr mm =>
      obtain ⟨m₁, m₂⟩ := mm
      change p ∈ support ((IND_CPA_hybridChallengeOracle (F := F) (gen := gen)
        pk b realUntil (m₁, m₂)).run st) at hp
      revert hp
      rcases hcache : st.1 (m₁, m₂) with _ | c <;> intro hp
      · simp only [IND_CPA_hybridChallengeOracle, hcache, StateT.run_bind, StateT.run_get,
          pure_bind] at hp
        rw [mem_support_iff] at hp
        rw [← mem_support_iff] at hp
        split_ifs at hp <;>
          simp only [StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
            Set.mem_singleton_iff] at hp <;>
          (obtain ⟨c, _, ⟨i, hi, hp⟩⟩ := hp
           simp only [StateT.run_set, support_pure,
             Set.mem_singleton_iff] at hi
           subst hi
           simp only [hp]
           omega)
      · simp only [IND_CPA_hybridChallengeOracle, hcache,
          StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hp
        have := congrArg (fun x => x.2.2) hp
        simp at this
        omega

private lemma stepDDHQueryImpl_eq_hybridQueryImpl_pre_k
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G) (realUntil : ℕ)
    (hrealUntil : realUntil = k ∨ realUntil = k + 1)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G)) (hlt : st.2 < k) :
    (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃ t).run st =
    (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil t).run st := by
  cases t with
  | inl tu =>
      simp [IND_CPA_stepDDHQueryImpl, IND_CPA_queryImpl_hybrid]
  | inr mm =>
      obtain ⟨m₁, m₂⟩ := mm
      simp only [IND_CPA_stepDDHQueryImpl, IND_CPA_queryImpl_hybrid]
      rcases hrealUntil with h | h <;> simp only [h]
      · show (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k x₂ x₃
          (m₁, m₂)).run st =
          (IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b k
            (m₁, m₂)).run st
        simp only [IND_CPA_stepDDHOracle, IND_CPA_hybridChallengeOracle,
          StateT.run_bind, StateT.run_get, pure_bind]
        rcases hcache : st.1 (m₁, m₂) with _ | c
        · simp only [if_pos hlt]
        · simp only [StateT.run_pure]
      · show (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k x₂ x₃
          (m₁, m₂)).run st =
          (IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b (k + 1)
            (m₁, m₂)).run st
        simp only [IND_CPA_stepDDHOracle, IND_CPA_hybridChallengeOracle,
          StateT.run_bind, StateT.run_get, pure_bind]
        rcases hcache : st.1 (m₁, m₂) with _ | c
        · simp only [if_pos hlt, if_pos (show st.2 < k + 1 by omega)]
        · simp only [StateT.run_pure]

private lemma hybridQueryImpl_counter_le_succ
    (pk : G) (b : Bool) (realUntil : ℕ)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G))
    (p : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Range t × IND_CPA_HybridState (G := G))
    (hp : p ∈ support ((IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil t).run st)) :
    p.2.2 ≤ st.2 + 1 := by
  cases t with
  | inl tu =>
      simp only [IND_CPA_queryImpl_hybrid, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        liftM, monadLift, StateT.instMonadLift] at hp
      rw [StateT.run_lift, mem_support_bind_iff] at hp
      obtain ⟨a, _, ha⟩ := hp
      rw [mem_support_pure_iff] at ha
      have hst : p.2 = st := congrArg Prod.snd ha
      simp [hst]
  | inr mm =>
      change p ∈ support ((IND_CPA_hybridChallengeOracle (F := F) (gen := gen)
        pk b realUntil mm).run st) at hp
      revert hp
      rcases hcache : st.1 mm with _ | c <;> intro hp
      · simp only [IND_CPA_hybridChallengeOracle, hcache,
          StateT.run_bind, StateT.run_get, pure_bind] at hp
        rw [mem_support_iff] at hp
        rw [← mem_support_iff] at hp
        split_ifs at hp <;>
          (simp only [StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
            Set.mem_singleton_iff] at hp
           obtain ⟨c, _, ⟨i, hi, hp⟩⟩ := hp
           simp only [StateT.run_set, support_pure,
             Set.mem_singleton_iff] at hi
           subst hi
           simp only [hp]
           omega)
      · simp only [IND_CPA_hybridChallengeOracle, hcache,
          StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hp
        have := congrArg (fun x => x.2.2) hp
        simp at this
        omega
private lemma simulateQ_stepDDH_probOutput_eq_hybrid_post_k
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G) (realUntil : ℕ)
    (hrealUntil : realUntil = k ∨ realUntil = k + 1)
    {α : Type} (a : OracleComp (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec α) :
    ∀ (st : IND_CPA_HybridState (G := G)), k < st.2 →
    ∀ z : α × IND_CPA_HybridState (G := G),
    Pr[= z | (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃) a).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil) a).run st] := by
  intro st hgt z
  simpa using OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃)
    (impl₂ := IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil)
    (Inv := fun st : IND_CPA_HybridState (G := G) => k < st.2) (oa := a) (s := st) (z := z)
    (himpl_eq := fun t st hInv =>
      stepDDHQueryImpl_eq_hybridQueryImpl_post_k (F := F) (gen := gen) pk b k x₂ x₃
        realUntil hrealUntil t st hInv)
    (hpres₂ := fun t st hInv p hp =>
      Nat.lt_of_lt_of_le hInv
        (hybridQueryImpl_counter_mono (F := F) (gen := gen) pk b realUntil t st p hp))
    hgt
private lemma stepDDH_fresh_query_simulation_core
    (pk : G) (b : Bool) (k : ℕ) (realUntil : ℕ)
    (hrealUntil : realUntil = k ∨ realUntil = k + 1)
    {β α : Type} (sample : ProbComp β) (x₂ : β → G) (x₃ : β → G) (resp : β → G × G)
    (nextState : β → IND_CPA_HybridState (G := G))
    (oa : G × G → OracleComp (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec α)
    (hgt : ∀ s, k < (nextState s).2)
    (z : α × IND_CPA_HybridState (G := G)) :
    Pr[= z | do
      let s ← sample
      (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k (x₂ s) (x₃ s))
        (oa (resp s))).run (nextState s)] =
    Pr[= z | do
      let s ← sample
      (simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil)
        (oa (resp s))).run (nextState s)] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun s => ?_
  have hs := simulateQ_stepDDH_probOutput_eq_hybrid_post_k (F := F) (gen := gen) pk b k
    (x₂ s) (x₃ s) realUntil hrealUntil (oa (resp s)) (nextState s) (hgt s) z
  simpa using congrArg (fun p => Pr[= s | sample] * p) hs
private lemma stepDDH_simulation_deferred
    (pk : G) (b : Bool) (k realUntil : ℕ)
    (hrealUntil : realUntil = k ∨ realUntil = k + 1)
    {β α : Type} (sample : ProbComp β) (x₂ : β → G) (x₃ : β → G)
    (a : OracleComp (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec α)
    (hhybrid_miss : ∀ (m₁ m₂ : G) (st : IND_CPA_HybridState (G := G)),
      st.2 = k → st.1 (m₁, m₂) = none →
      (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil (Sum.inr (m₁, m₂))).run st =
        (do
          let s ← sample
          pure ((x₂ s, (if b = true then m₁ else m₂) + x₃ s),
            (st.1.cacheQuery (m₁, m₂) (x₂ s, (if b = true then m₁ else m₂) + x₃ s),
             st.2 + 1)) : ProbComp _)) :
    ∀ (st : IND_CPA_HybridState (G := G)), st.2 ≤ k →
    ∀ z : α × IND_CPA_HybridState (G := G),
    Pr[= z | do
        let s ← sample
        (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
          (x₂ s) (x₃ s)) a).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen)
        pk b realUntil) a).run st] := by
  intro st
  revert st
  induction a using OracleComp.inductionOn with
  | pure x =>
      intro st _ z
      simp
  | query_bind t oa ih =>
      intro st hle z
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      cases t with
      | inl tu =>
          simp_rw [show ∀ s : β,
              IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                (x₂ s) (x₃ s) (Sum.inl tu) =
              IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil
                (Sum.inl tu) from fun _ => rfl]
          qvcgen_step
          have hst : b_2.2 = st := by
            simp only [IND_CPA_queryImpl_hybrid, QueryImpl.add_apply_inl,
              QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
              liftM, monadLift, StateT.instMonadLift] at hb
            rw [StateT.run_lift, mem_support_bind_iff] at hb
            obtain ⟨a, _, ha⟩ := hb
            rw [mem_support_pure_iff] at ha
            exact congrArg Prod.snd ha
          subst hst
          exact ih b_2.1 _ hle z
      | inr mm =>
          obtain ⟨m₁, m₂⟩ := mm
          rcases Nat.lt_or_eq_of_le hle with hlt | heq
          · have hq : ∀ s : β,
                (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                  (x₂ s) (x₃ s) (Sum.inr (m₁, m₂))).run st =
                (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil
                  (Sum.inr (m₁, m₂))).run st := by
              intro s
              exact stepDDHQueryImpl_eq_hybridQueryImpl_pre_k (F := F) (gen := gen)
                pk b k (x₂ s) (x₃ s) realUntil hrealUntil (Sum.inr (m₁, m₂)) st hlt
            simp_rw [hq]
            qvcgen_step
            have hle' : b_2.2.2 ≤ k := by
              have hsucc := hybridQueryImpl_counter_le_succ (F := F) (gen := gen)
                pk b realUntil (Sum.inr (m₁, m₂)) st b_2 hb
              omega
            exact ih b_2.1 b_2.2 hle' z
          · rcases hcache : st.1 (m₁, m₂) with _ | c
            · have hstep : ∀ s : β,
                  (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                    (x₂ s) (x₃ s) (Sum.inr (m₁, m₂))).run st =
                  (pure ((x₂ s,
                      (if b = true then m₁ else m₂) + x₃ s),
                    (st.1.cacheQuery (m₁, m₂) (x₂ s,
                      (if b = true then m₁ else m₂) + x₃ s),
                     st.2 + 1)) : ProbComp _) := by
                intro s
                show (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k
                  (x₂ s) (x₃ s) (m₁, m₂)).run st = _
                simp only [IND_CPA_stepDDHOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache,
                  if_neg (show ¬ st.2 < k by omega),
                  if_pos heq, StateT.run_pure, StateT.run_set]
              have hhybrid := hhybrid_miss m₁ m₂ st heq hcache
              simp_rw [hstep, pure_bind]
              rw [hhybrid]
              simpa using
                stepDDH_fresh_query_simulation_core (F := F) (gen := gen) pk b k realUntil
                  hrealUntil sample x₂ x₃
                  (fun s => (x₂ s, (if b = true then m₁ else m₂) + x₃ s))
                  (fun s =>
                    (st.1.cacheQuery (m₁, m₂) (x₂ s,
                      (if b = true then m₁ else m₂) + x₃ s),
                     st.2 + 1))
                  oa
                  (fun _ => by simp [heq]) z
            · have hstep : ∀ s : β,
                  (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                    (x₂ s) (x₃ s) (Sum.inr (m₁, m₂))).run st =
                  (pure (c, st) : ProbComp _) := by
                intro s
                show (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k
                  (x₂ s) (x₃ s) (m₁, m₂)).run st = _
                simp only [IND_CPA_stepDDHOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, StateT.run_pure]
              have hhybrid :
                  (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil
                    (Sum.inr (m₁, m₂))).run st =
                  (pure (c, st) : ProbComp _) := by
                show (IND_CPA_hybridChallengeOracle (F := F) (gen := gen)
                  pk b realUntil (m₁, m₂)).run st = _
                simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, StateT.run_pure]
              simp_rw [hstep, hhybrid, pure_bind]
              exact ih c st hle z

-- Real simulation deferred: absorbing the DDH challenge scalar into real ElGamal encryption
private lemma stepDDH_real_simulation_deferred
    (pk : G) (b : Bool) (k : ℕ)
    {α : Type} (a : OracleComp (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec α) :
    ∀ (st : IND_CPA_HybridState (G := G)), st.2 ≤ k →
    ∀ z : α × IND_CPA_HybridState (G := G),
    Pr[= z | do
        let r ← ($ᵗ F : ProbComp F)
        (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
          (r • gen) (r • pk)) a).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen)
        pk b (k + 1)) a).run st] := by
  refine stepDDH_simulation_deferred (F := F) (gen := gen) pk b k (k + 1)
    (Or.inr rfl) ($ᵗ F : ProbComp F) (fun r => r • gen) (fun r => r • pk) a ?_
  intro m₁ m₂ st heq hcache
  show (IND_CPA_hybridChallengeOracle (F := F) (gen := gen)
    pk b (k + 1) (m₁, m₂)).run st = _
  simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
    StateT.run_get, pure_bind, hcache,
    show st.2 < k + 1 by omega, ite_true]
  simp only [elgamalAsymmEnc]
  simp only [hybridState_run_liftM_eq (G := G) (st := st), bind_assoc,
    StateT.run_pure, pure_bind, StateT.run_set]

-- Random simulation deferred: absorbing both DDH scalars into random masking
private lemma stepDDH_rand_simulation_deferred
    (pk : G) (b : Bool) (k : ℕ)
    {α : Type} (a : OracleComp (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec α) :
    ∀ (st : IND_CPA_HybridState (G := G)), st.2 ≤ k →
    ∀ z : α × IND_CPA_HybridState (G := G),
    Pr[= z | do
        let r ← ($ᵗ F : ProbComp F)
        let y ← ($ᵗ G : ProbComp G)
        (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
          (r • gen) y) a).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen)
        pk b k) a).run st] := by
  have hbase := stepDDH_simulation_deferred (F := F) (gen := gen) pk b k k
      (Or.inl rfl)
      (do
        let r ← ($ᵗ F : ProbComp F)
        let y ← ($ᵗ G : ProbComp G)
        pure (r, y))
      (fun p => p.1 • gen) (fun p => p.2) a (by
        intro m₁ m₂ st heq hcache
        show (IND_CPA_hybridChallengeOracle (F := F) (gen := gen)
          pk b k (m₁, m₂)).run st = _
        simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
          StateT.run_get, pure_bind, hcache,
          if_neg (show ¬ st.2 < k by omega)]
        simp only [randomMaskedCipher]
        simp only [hybridState_run_liftM_eq (G := G) (st := st), bind_assoc,
          StateT.run_pure, pure_bind, StateT.run_set])
  simpa [bind_assoc] using hbase

-- The DDH-real branch has the same success probability as hybrid k+1.
private lemma stepDDH_realBranch_probOutput_eq
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (k : ℕ) :
    Pr[= true | DiffieHellman.ddhExpReal gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)] =
    Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)] := by
  let lhsRun : F → Bool → ProbComp (Bool × IND_CPA_HybridState (G := G)) := fun a b => do
    let b_scalar ← ($ᵗ F : ProbComp F)
    let pk : G := a • gen
    let x₂ : G := b_scalar • gen
    let x₃ : G := (a * b_scalar) • gen
    (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃)
      (adversary pk)).run (∅, 0)
  have hsim_run :
      ∀ a b,
        evalDist (lhsRun a b) =
          evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) (a • gen) b (k + 1))
            (adversary (a • gen))).run (∅, 0)) := by
    intro a b
    let pk : G := a • gen
    change evalDist (do
      let b_scalar ← ($ᵗ F : ProbComp F)
      (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
        (b_scalar • gen) ((a * b_scalar) • gen)) (adversary pk)).run (∅, 0)) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b (k + 1))
          (adversary pk)).run (∅, 0))
    apply evalDist_ext
    intro z
    have hrw : ∀ r : F, r • pk = (a * r) • gen := by
      intro r
      rw [show pk = a • gen from rfl, ← mul_smul, mul_comm]
    simp_rw [← hrw]
    simpa [pk] using
      stepDDH_real_simulation_deferred (F := F) (gen := gen) (pk := pk) (b := b) (k := k)
        (a := adversary pk) (st := (∅, 0)) (by omega) (z := z)
  calc
    Pr[= true | DiffieHellman.ddhExpReal gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)] =
      Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let a ← ($ᵗ F : ProbComp F)
        let z ← Prod.fst <$> lhsRun a b
        pure (b == z)] := by
          simp [DiffieHellman.ddhExpReal, IND_CPA_stepDDHReduction, lhsRun,
            map_eq_bind_pure_comp, bind_assoc]
          qvcgen_step rw under 1
          qvcgen_step rw
    _ = Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)] := by
          refine hybridBranch_probOutput_eq (F := F) (gen := gen) adversary (k + 1)
            (fun a b => Prod.fst <$> lhsRun a b) ?_
          intro a b
          simpa [StateT.run'] using
            (evalDist_map_eq_of_evalDist_eq (f := Prod.fst) (hsim_run a b))

-- The DDH-random branch has the same success probability as hybrid k.
private lemma stepDDH_randBranch_probOutput_eq
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (k : ℕ) :
    Pr[= true | DiffieHellman.ddhExpRand gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)] =
    Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k] := by
  let lhsRun : F → Bool → ProbComp (Bool × IND_CPA_HybridState (G := G)) := fun a b => do
    let b_scalar ← ($ᵗ F : ProbComp F)
    let c ← ($ᵗ F : ProbComp F)
    let pk : G := a • gen
    let x₂ : G := b_scalar • gen
    (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ (c • gen))
      (adversary pk)).run (∅, 0)
  let lhsRun' : F → Bool → ProbComp (Bool × IND_CPA_HybridState (G := G)) := fun a b => do
    let b_scalar ← ($ᵗ F : ProbComp F)
    let y ← ($ᵗ G : ProbComp G)
    let pk : G := a • gen
    let x₂ : G := b_scalar • gen
    (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ y)
      (adversary pk)).run (∅, 0)
  have hbridge :
      ∀ a b, evalDist (lhsRun a b) = evalDist (lhsRun' a b) := by
    intro a b
    apply evalDist_ext
    intro z
    qvcgen_step rw congr' as ⟨b_scalar⟩
    exact probOutput_bind_bijective_uniform_cross (α := F) (β := G) (f := (· • gen)) hg
      (fun y => do
        let pk : G := a • gen
        let x₂ : G := b_scalar • gen
        (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ y)
          (adversary pk)).run (∅, 0))
      z
  have hsim_run :
      ∀ a b,
        evalDist (lhsRun' a b) =
          evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) (a • gen) b k)
            (adversary (a • gen))).run (∅, 0)) := by
    intro a b
    let pk : G := a • gen
    change evalDist (do
      let b_scalar ← ($ᵗ F : ProbComp F)
      let y ← ($ᵗ G : ProbComp G)
      (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
        (b_scalar • gen) y) (adversary pk)).run (∅, 0)) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b k)
          (adversary pk)).run (∅, 0))
    apply evalDist_ext
    intro z
    simpa [pk] using
      stepDDH_rand_simulation_deferred (F := F) (gen := gen) (pk := pk) (b := b) (k := k)
        (a := adversary pk) (st := (∅, 0)) (by omega) (z := z)
  have hmain_run :
      ∀ a b,
        evalDist (lhsRun a b) =
          evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) (a • gen) b k)
            (adversary (a • gen))).run (∅, 0)) := by
    intro a b
    exact (hbridge a b).trans (hsim_run a b)
  calc
    Pr[= true | DiffieHellman.ddhExpRand gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)] =
      Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let a ← ($ᵗ F : ProbComp F)
        let z ← Prod.fst <$> lhsRun a b
        pure (b == z)] := by
          simp [DiffieHellman.ddhExpRand, IND_CPA_stepDDHReduction, lhsRun,
            map_eq_bind_pure_comp, bind_assoc]
          qvcgen_step rw under 2
          qvcgen_step rw under 1
          qvcgen_step rw
    _ = Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k] := by
          refine hybridBranch_probOutput_eq (F := F) (gen := gen) adversary k
            (fun a b => Prod.fst <$> lhsRun a b) ?_
          intro a b
          simpa [StateT.run'] using
            (evalDist_map_eq_of_evalDist_eq (f := Prod.fst) (hmain_run a b))
private lemma ddhExp_stepDDHReduction_decomp_toReal
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (k : ℕ) :
    (Pr[= true |
      DiffieHellman.ddhExp gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal
        - 1 / 2 =
    ((Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)]).toReal -
      (Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k]).toReal) / 2 := by
  calc
    (Pr[= true |
      DiffieHellman.ddhExp gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal
        - 1 / 2
        =
        ((Pr[= true | DiffieHellman.ddhExpReal gen
            (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal -
          (Pr[= true | DiffieHellman.ddhExpRand gen
            (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal) / 2 := by
          exact DiffieHellman.ddhExp_probOutput_sub_half (F := F) gen
            (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)
    _ =
        ((Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)]).toReal -
          (Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k]).toReal) / 2 := by
          rw [stepDDH_realBranch_probOutput_eq (F := F) (gen := gen) adversary k,
              stepDDH_randBranch_probOutput_eq hg adversary k]

/-- Per-hop bound: the absolute difference between consecutive hybrid winning probabilities
is at most twice the DDH advantage of the step-`k` reduction. -/
lemma IND_CPA_stepDDH_hopBound
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (k : ℕ) :
    |(Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)]).toReal -
      (Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k]).toReal| ≤
      2 * |(Pr[= true |
          DiffieHellman.ddhExp gen
            (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal - 1 / 2| := by
  have h := ddhExp_stepDDHReduction_decomp_toReal hg adversary k
  have heq : (Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)]).toReal -
      (Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k]).toReal =
      2 * ((Pr[= true |
          DiffieHellman.ddhExp gen
            (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal - 1 / 2) := by
    linarith
  rw [heq, abs_mul, abs_of_nonneg (by positivity)]

/-! ## 6. Bridging hybrid game to real game via query bound -/

private lemma allReal_eq_hybrid_on_bounded
    (pk : G) (b : Bool) (realUntil : ℕ)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G)) (hlt : st.2 < realUntil) :
    (AsymmEncAlg.IND_CPA_queryImpl'_counted
      (encAlg' := elgamalAsymmEnc F G gen) pk b t).run st =
    (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil t).run st := by
  cases t with
  | inl _ => rfl
  | inr mm =>
      rcases hcache : st.1 mm with _ | c
      · simp [AsymmEncAlg.IND_CPA_queryImpl'_counted, AsymmEncAlg.IND_CPA_challengeOracle'_counted,
          IND_CPA_queryImpl_hybrid, IND_CPA_hybridChallengeOracle, hcache, hlt,
          hybridState_run_liftM_eq (G := G) (st := st)]
      · simp [AsymmEncAlg.IND_CPA_queryImpl'_counted, AsymmEncAlg.IND_CPA_challengeOracle'_counted,
          IND_CPA_queryImpl_hybrid, IND_CPA_hybridChallengeOracle, hcache]
/-! ## 7. Main theorem -/

/-- IND-CPA advantage is bounded by the sum of per-hop DDH advantages before collapsing to a
single `ε` bound. -/
theorem elGamal_IND_CPA_bound_toReal
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (q : ℕ)
    (hstart : (Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary q]).toReal =
      (Pr[= true | IND_CPA_game (gen := gen) adversary]).toReal) :
    ((elgamalAsymmEnc F G gen).IND_CPA_advantage adversary).toReal ≤
      Finset.sum (Finset.range q) (fun k =>
        2 * |(Pr[= true |
              DiffieHellman.ddhExp gen
                (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal
                - 1 / 2|) := by
  refine le_trans (AsymmEncAlg.IND_CPA_advantage_toReal_le_abs_signedAdvantageReal adversary) ?_
  refine le_trans
    (AsymmEncAlg.IND_CPA_advantage'_abs_le_sum_hybridDiff_abs
      adversary q (IND_CPA_HybridFamily (F := F) (gen := gen) adversary q)
      (by simp only [IND_CPA_HybridFamily_zero]; exact hstart)
      (by simp only [IND_CPA_HybridFamily_q];
          rw [IND_CPA_allRandomHalf]; simp)) ?_
  calc
    Finset.sum (Finset.range q) (fun i =>
          |(Pr[= true | IND_CPA_HybridFamily (F := F) (gen := gen) adversary q i]).toReal -
            (Pr[= true | IND_CPA_HybridFamily (F := F) (gen := gen) adversary q (i + 1)]).toReal|)
        ≤ Finset.sum (Finset.range q) (fun i =>
            2 * |(Pr[= true |
                  DiffieHellman.ddhExp gen
                    (IND_CPA_stepDDHReduction (F := F) (gen := gen)
                      adversary (q - 1 - i))]).toReal - 1 / 2|) :=
          Finset.sum_le_sum fun i hi => by
            simp only [IND_CPA_HybridFamily]
            have hlt : i < q := Finset.mem_range.mp hi
            have h1 : q - 1 - i + 1 = q - i := by omega
            have h2 : q - (i + 1) = q - 1 - i := by omega
            rw [h2]
            have hb := IND_CPA_stepDDH_hopBound hg adversary (q - 1 - i)
            rwa [h1] at hb
    _ = Finset.sum (Finset.range q) (fun i =>
            2 * |(Pr[= true |
                  DiffieHellman.ddhExp gen
                    (IND_CPA_stepDDHReduction (F := F) (gen := gen)
                      adversary i)]).toReal - 1 / 2|) :=
          Finset.sum_range_reflect
            (fun i => 2 * |(Pr[= true |
              DiffieHellman.ddhExp gen
                (IND_CPA_stepDDHReduction (F := F) (gen := gen)
                  adversary i)]).toReal - 1 / 2|)
            q

/-- **Main theorem.** If an adversary makes at most `q` LR queries and each per-hop DDH
reduction has advantage at most `ε`, then ElGamal has IND-CPA advantage at most `q * (2 * ε)`. -/
@[game_hop_root]
theorem elGamal_IND_CPA_le_q_mul_ddh
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (q : ℕ) (ε : ℝ)
    (hq : adversary.MakesAtMostQueries q)
    (hddh : ∀ k < q,
      |(Pr[= true | DiffieHellman.ddhExp gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal - 1 / 2| ≤ ε) :
    ((elgamalAsymmEnc F G gen).IND_CPA_advantage adversary).toReal ≤ q * (2 * ε) := by
  refine le_trans (elGamal_IND_CPA_bound_toReal hg adversary q ?_) ?_
  · simpa [IND_CPA_HybridGame, IND_CPA_game] using
      (AsymmEncAlg.IND_CPA_countedGame_eq_game_of_MakesAtMostQueries
        (encAlg' := elgamalAsymmEnc F G gen)
        (implCounted := fun pk b realUntil =>
          IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil)
        (hsame := by
          intro pk b realUntil t st hcond
          cases t with
          | inl _ => rfl
          | inr mm =>
              exact allReal_eq_hybrid_on_bounded
                (F := F) (gen := gen) pk b realUntil (Sum.inr mm) st hcond)
        adversary q hq)
  calc
    Finset.sum (Finset.range q) (fun k =>
          2 * |(Pr[= true |
                DiffieHellman.ddhExp gen
                  (IND_CPA_stepDDHReduction (F := F) (gen := gen)
                    adversary k)]).toReal - 1 / 2|)
        ≤ Finset.sum (Finset.range q) (fun _ => 2 * ε) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact mul_le_mul_of_nonneg_left (hddh k (Finset.mem_range.mp hk)) (by positivity)
    _ = q * (2 * ε) := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

#print axioms elGamal_IND_CPA_le_q_mul_ddh

end IND_CPA

end elgamalAsymmEnc
