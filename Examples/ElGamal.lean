/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.EvalDist.Bool
import VCVio.ProgramLogic.Tactics
import VCVioWidgets.GameHop.Command
import VCVioWidgets.GameHop.Examples.ElGamal

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
6. Main theorem (`elGamal_IND_CPA_le_q_mul_ddh`): IND-CPA advantage ≤ `q * (2ε)` where `ε`
   bounds each per-hop DDH advantage.

## Query-bound hypothesis

The main theorem takes `hstart`, which asserts that the `q`-th hybrid has the same winning
probability as the actual IND-CPA experiment. This holds for any adversary making at most `q`
distinct fresh LR oracle queries.
-/

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

/-- A random-masked ciphertext: `(r • gen, msg + y)` with independent `r ← $ᵗ F`, `y ← $ᵗ G`.
Unlike real ElGamal encryption, the second component is masked by a uniform group element
rather than `r • pk`, making it information-theoretically independent of the message. -/
def randomMaskedCipher (msg : G) : ProbComp (G × G) := do
  let r ← $ᵗ F
  let y ← $ᵗ G
  return (r • gen, msg + y)

/-- The hybrid LR oracle: uses real ElGamal encryption for the first `realUntil` fresh queries
and `randomMaskedCipher` for subsequent ones. Repeated queries are served from cache. -/
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

/-! ## 3a. DDH helper lemmas -/

omit [DecidableEq G] in
lemma probOutput_add_left_uniform (m x : G) :
    Pr[= x | (fun y : G => m + y) <$> ($ᵗ G)] = Pr[= x | $ᵗ G] := by
  have h : Pr[= m + (-m + x) | (fun y : G => m + y) <$> ($ᵗ G)] =
      Pr[= -m + x | $ᵗ G] :=
    probOutput_map_injective
      (mx := ($ᵗ G))
      (f := fun y : G => m + y)
      (hf := by intro a b hab; exact add_left_cancel hab)
      (x := -m + x)
  calc
    Pr[= x | (fun y : G => m + y) <$> ($ᵗ G)]
        = Pr[= m + (-m + x) | (fun y : G => m + y) <$> ($ᵗ G)] := by
          congr 1; abel
    _ = Pr[= -m + x | $ᵗ G] := h
    _ = Pr[= x | $ᵗ G] := by
          symm
          simpa [uniformSample] using
            (SampleableType.probOutput_selectElem_eq (β := G) x (-m + x))

omit [DecidableEq G] in
lemma probOutput_bind_add_left_uniform {β : Type} (m : G) (f : G → ProbComp β) (z : β) :
    Pr[= z | (do let y ← $ᵗ G; f (m + y))] =
      Pr[= z | (do let y ← $ᵗ G; f y)] := by
  have hleft :
      (do let y ← $ᵗ G; f (m + y)) = (((fun y : G => m + y) <$> ($ᵗ G)) >>= fun y => f y) := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [hleft, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun y => ?_
  rw [probOutput_add_left_uniform (G := G) m y]

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

def stepDDH_realBranchCore
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (k : ℕ) (a b_scalar : F) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let pk : G := a • gen
  let x₂ : G := b_scalar • gen
  let x₃ : G := (a * b_scalar) • gen
  let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃)
    (adversary pk)).run' (∅, 0)
  return (b == b')

def stepDDH_randBranchCore
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (k : ℕ) (a b_scalar : F) : ProbComp Bool := do
  let c ← $ᵗ F
  let b ← $ᵗ Bool
  let pk : G := a • gen
  let x₂ : G := b_scalar • gen
  let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ (c • gen))
    (adversary pk)).run' (∅, 0)
  return (b == b')

def stepDDH_realBranchGame
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (k : ℕ) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let a ← $ᵗ F
  let b_scalar ← $ᵗ F
  let pk : G := a • gen
  let x₂ : G := b_scalar • gen
  let x₃ : G := (a * b_scalar) • gen
  let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃)
    (adversary pk)).run' (∅, 0)
  return (b == b')

def stepDDH_randBranchGame
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (k : ℕ) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let a ← $ᵗ F
  let b_scalar ← $ᵗ F
  let c ← $ᵗ F
  let pk : G := a • gen
  let x₂ : G := b_scalar • gen
  let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ (c • gen))
    (adversary pk)).run' (∅, 0)
  return (b == b')

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

private lemma simulateQ_stepDDH_probOutput_eq_hybrid_post_k
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G) (realUntil : ℕ)
    (hrealUntil : realUntil = k ∨ realUntil = k + 1)
    {α : Type} (a : OracleComp (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec α) :
    ∀ (st : IND_CPA_HybridState (G := G)), k < st.2 →
    ∀ z : α × IND_CPA_HybridState (G := G),
    Pr[= z | (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃) a).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil) a).run st] := by
  induction a using OracleComp.inductionOn with
  | pure x =>
      intro st _ z
      simp
  | query_bind t oa ih =>
      intro st hgt z
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      have hq := stepDDHQueryImpl_eq_hybridQueryImpl_post_k (F := F) (gen := gen) pk b k x₂ x₃
        realUntil hrealUntil t st hgt
      rw [hq]
      qvcgen_step as ⟨p, hp⟩
      refine ih p.1 p.2 ?_ z
      exact Nat.lt_of_lt_of_le hgt
        (hybridQueryImpl_counter_mono (F := F) (gen := gen) pk b realUntil t st p hp)

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
          simp_rw [show ∀ r : F,
              IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                (r • gen) (r • pk) (Sum.inl tu) =
              IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b (k + 1)
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
          · have hq : ∀ r : F,
                (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                  (r • gen) (r • pk) (Sum.inr (m₁, m₂))).run st =
                (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b (k + 1)
                  (Sum.inr (m₁, m₂))).run st := by
              intro r
              show (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k
                (r • gen) (r • pk) (m₁, m₂)).run st =
                (IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b
                  (k + 1) (m₁, m₂)).run st
              simp only [IND_CPA_stepDDHOracle, IND_CPA_hybridChallengeOracle,
                StateT.run_bind, StateT.run_get, pure_bind]
              rcases hcache : st.1 (m₁, m₂) with _ | c
              · simp only [if_pos hlt, if_pos (show st.2 < k + 1 by omega)]
              · simp only [StateT.run_pure]
            simp_rw [hq]
            qvcgen_step
            have hle' : b_2.2.2 ≤ k := by
              change b_2 ∈ support ((IND_CPA_hybridChallengeOracle (F := F)
                (gen := gen) pk b (k + 1) (m₁, m₂)).run st) at hb
              revert hb
              rcases hcache : st.1 (m₁, m₂) with _ | c <;> intro hp
              · simp only [IND_CPA_hybridChallengeOracle, hcache,
                  StateT.run_bind, StateT.run_get, pure_bind] at hp
                rw [mem_support_iff] at hp
                rw [← mem_support_iff] at hp
                split_ifs at hp <;>
                  (simp only [StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion,
                    support_pure, Set.mem_singleton_iff] at hp
                   obtain ⟨ci, _, ⟨i, hi, hp⟩⟩ := hp
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
            exact ih b_2.1 b_2.2 hle' z
          · rcases hcache : st.1 (m₁, m₂) with _ | c
            · have hstep : ∀ r : F,
                  (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                    (r • gen) (r • pk) (Sum.inr (m₁, m₂))).run st =
                  (pure ((r • gen,
                      (if b = true then m₁ else m₂) + r • pk),
                    (st.1.cacheQuery (m₁, m₂) (r • gen,
                      (if b = true then m₁ else m₂) + r • pk),
                     st.2 + 1)) : ProbComp _) := by
                intro r
                show (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k
                  (r • gen) (r • pk) (m₁, m₂)).run st = _
                simp only [IND_CPA_stepDDHOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache,
                  if_neg (show ¬ st.2 < k by omega),
                  if_pos heq, StateT.run_pure, StateT.run_set]
              have hhybrid :
                  (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b (k + 1)
                    (Sum.inr (m₁, m₂))).run st =
                  (do let r ← ($ᵗ F : ProbComp F)
                      pure ((r • gen,
                          (if b = true then m₁ else m₂) + r • pk),
                        (st.1.cacheQuery (m₁, m₂) (r • gen,
                          (if b = true then m₁ else m₂) + r • pk),
                         st.2 + 1)) : ProbComp _) := by
                show (IND_CPA_hybridChallengeOracle (F := F) (gen := gen)
                  pk b (k + 1) (m₁, m₂)).run st = _
                simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache,
                  show st.2 < k + 1 by omega, ite_true]
                simp only [elgamalAsymmEnc]
                simp only [hybridState_run_liftM_eq (G := G) (st := st), bind_assoc,
                  StateT.run_pure, pure_bind, StateT.run_set]
              simp_rw [hstep, pure_bind]
              rw [hhybrid, bind_assoc]
              simp_rw [pure_bind]
              qvcgen_step rw congr' as ⟨r⟩
              exact simulateQ_stepDDH_probOutput_eq_hybrid_post_k (F := F)
                (gen := gen) pk b k (r • gen) (r • pk) (k + 1)
                (Or.inr rfl) (oa _) _ (by rw [heq]; omega) z
            · have hstep : ∀ r : F,
                  (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                    (r • gen) (r • pk)
                    (Sum.inr (m₁, m₂))).run st =
                  (pure (c, st) : ProbComp _) := by
                intro r
                show (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k
                  (r • gen) (r • pk) (m₁, m₂)).run st = _
                simp only [IND_CPA_stepDDHOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, StateT.run_pure]
              have hhybrid :
                  (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b (k + 1)
                    (Sum.inr (m₁, m₂))).run st =
                  (pure (c, st) : ProbComp _) := by
                show (IND_CPA_hybridChallengeOracle (F := F) (gen := gen)
                  pk b (k + 1) (m₁, m₂)).run st = _
                simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, StateT.run_pure]
              simp_rw [hstep, hhybrid, pure_bind]
              exact ih c st (by omega) z

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
          simp_rw [show ∀ (r : F) (y : G),
              IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                (r • gen) y (Sum.inl tu) =
              IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b k
                (Sum.inl tu) from fun _ _ => rfl]
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
          · have hq : ∀ (r : F) (y : G),
                (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                  (r • gen) y (Sum.inr (m₁, m₂))).run st =
                (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b k
                  (Sum.inr (m₁, m₂))).run st := by
              intro r y
              show (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k
                (r • gen) y (m₁, m₂)).run st =
                (IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b
                  k (m₁, m₂)).run st
              simp only [IND_CPA_stepDDHOracle, IND_CPA_hybridChallengeOracle,
                StateT.run_bind, StateT.run_get, pure_bind]
              rcases hcache : st.1 (m₁, m₂) with _ | c
              · simp only [if_pos hlt]
              · simp only [StateT.run_pure]
            simp_rw [hq]
            qvcgen_step
            have hle' : b_2.2.2 ≤ k := by
              change b_2 ∈ support ((IND_CPA_hybridChallengeOracle (F := F)
                (gen := gen) pk b k (m₁, m₂)).run st) at hb
              revert hb
              rcases hcache : st.1 (m₁, m₂) with _ | c <;> intro hp
              · simp only [IND_CPA_hybridChallengeOracle, hcache,
                  StateT.run_bind, StateT.run_get, pure_bind] at hp
                rw [mem_support_iff] at hp
                rw [← mem_support_iff] at hp
                split_ifs at hp <;>
                  (simp only [StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion,
                    support_pure, Set.mem_singleton_iff] at hp
                   obtain ⟨ci, _, ⟨i, hi, hp⟩⟩ := hp
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
            exact ih b_2.1 b_2.2 hle' z
          · rcases hcache : st.1 (m₁, m₂) with _ | c
            · have hstep : ∀ (r : F) (y : G),
                  (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                    (r • gen) y (Sum.inr (m₁, m₂))).run st =
                  (pure ((r • gen,
                      (if b = true then m₁ else m₂) + y),
                    (st.1.cacheQuery (m₁, m₂) (r • gen,
                      (if b = true then m₁ else m₂) + y),
                     st.2 + 1)) : ProbComp _) := by
                intro r y
                show (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k
                  (r • gen) y (m₁, m₂)).run st = _
                simp only [IND_CPA_stepDDHOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache,
                  if_neg (show ¬ st.2 < k by omega),
                  if_pos heq, StateT.run_pure, StateT.run_set]
              have hhybrid :
                  (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b k
                    (Sum.inr (m₁, m₂))).run st =
                  (do let r ← ($ᵗ F : ProbComp F)
                      let y ← ($ᵗ G : ProbComp G)
                      pure ((r • gen,
                          (if b = true then m₁ else m₂) + y),
                        (st.1.cacheQuery (m₁, m₂) (r • gen,
                          (if b = true then m₁ else m₂) + y),
                         st.2 + 1)) : ProbComp _) := by
                show (IND_CPA_hybridChallengeOracle (F := F) (gen := gen)
                  pk b k (m₁, m₂)).run st = _
                simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache,
                  if_neg (show ¬ st.2 < k by omega)]
                simp only [randomMaskedCipher]
                simp only [hybridState_run_liftM_eq (G := G) (st := st), bind_assoc,
                  StateT.run_pure, pure_bind, StateT.run_set]
              simp_rw [hstep, pure_bind]
              rw [hhybrid]
              simp_rw [bind_assoc, pure_bind]
              qvcgen_step rw congr' as ⟨r⟩
              qvcgen_step rw congr' as ⟨y⟩
              exact simulateQ_stepDDH_probOutput_eq_hybrid_post_k (F := F)
                (gen := gen) pk b k (r • gen) y k
                (Or.inl rfl) (oa ((r • gen, (if b = true then m₁ else m₂) + y))) _
                (by rw [heq]; omega) z
            · have hstep : ∀ (r : F) (y : G),
                  (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
                    (r • gen) y (Sum.inr (m₁, m₂))).run st =
                  (pure (c, st) : ProbComp _) := by
                intro r y
                show (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k
                  (r • gen) y (m₁, m₂)).run st = _
                simp only [IND_CPA_stepDDHOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, StateT.run_pure]
              have hhybrid :
                  (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b k
                    (Sum.inr (m₁, m₂))).run st =
                  (pure (c, st) : ProbComp _) := by
                show (IND_CPA_hybridChallengeOracle (F := F) (gen := gen)
                  pk b k (m₁, m₂)).run st = _
                simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, StateT.run_pure]
              simp_rw [hstep, hhybrid, pure_bind]
              exact ih c st hle z

-- The DDH-real branch has the same success probability as hybrid k+1.
private lemma stepDDH_realBranch_probOutput_eq
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (k : ℕ) :
    Pr[= true | stepDDH_realBranchGame (F := F) (gen := gen) adversary k] =
    Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)] := by
  let lhs : F → Bool → ProbComp Bool := fun a b => do
    let b_scalar ← ($ᵗ F : ProbComp F)
    let pk : G := a • gen
    let x₂ : G := b_scalar • gen
    let x₃ : G := (a * b_scalar) • gen
    (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃)
      (adversary pk)).run' (∅, 0)
  have hsim :
      ∀ a b,
        evalDist (lhs a b) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) (a • gen) b (k + 1))
          (adversary (a • gen))).run' (∅, 0)) := by
    intro a b
    let pk : G := a • gen
    have hsim_run :
        evalDist (do
          let b_scalar ← ($ᵗ F : ProbComp F)
          (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
            (b_scalar • gen) ((a * b_scalar) • gen)) (adversary pk)).run (∅, 0) :
            ProbComp (Bool × IND_CPA_HybridState (G := G))) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b (k + 1))
          (adversary pk)).run (∅, 0)) := by
      apply evalDist_ext
      intro z
      have hrw : ∀ r : F, r • pk = (a * r) • gen := by
        intro r
        rw [show pk = a • gen from rfl, ← mul_smul, mul_comm]
      simp_rw [← hrw]
      simpa [pk] using
        stepDDH_real_simulation_deferred (F := F) (gen := gen) (pk := pk) (b := b) (k := k)
          (a := adversary pk) (st := (∅, 0)) (by omega) (z := z)
    simpa [lhs, pk, StateT.run'] using
      (evalDist_map_eq_of_evalDist_eq (f := Prod.fst) hsim_run)
  simpa [stepDDH_realBranchGame, lhs] using
    hybridBranch_probOutput_eq (F := F) (gen := gen) adversary (k + 1) lhs hsim

omit [DecidableEq F] [DecidableEq G] in
private lemma probOutput_bind_uniform_smul_eq
    (hg : Function.Bijective (· • gen : F → G))
    {α : Type} (f : G → ProbComp α) (z : α) :
    Pr[= z | ($ᵗ F : ProbComp F) >>= fun c => f (c • gen)] =
    Pr[= z | ($ᵗ G : ProbComp G) >>= fun y => f y] := by
  haveI : Fintype G := Fintype.ofBijective _ hg
  have h : (($ᵗ F : ProbComp F) >>= fun c => f (c • gen)) =
      (((· • gen) <$> ($ᵗ F : ProbComp F)) >>= f) := by
    simp [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  rw [h, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  congr 1; funext y; congr 1
  exact probOutput_map_bijective_uniform_cross (α := F) (β := G) (· • gen) hg y

-- The DDH-random branch has the same success probability as hybrid k.
private lemma stepDDH_randBranch_probOutput_eq
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (k : ℕ) :
    Pr[= true | stepDDH_randBranchGame (F := F) (gen := gen) adversary k] =
    Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k] := by
  let lhs : F → Bool → ProbComp Bool := fun a b => do
    let b_scalar ← ($ᵗ F : ProbComp F)
    let c ← ($ᵗ F : ProbComp F)
    let pk : G := a • gen
    let x₂ : G := b_scalar • gen
    (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ (c • gen))
      (adversary pk)).run' (∅, 0)
  let lhs' : F → Bool → ProbComp Bool := fun a b => do
    let b_scalar ← ($ᵗ F : ProbComp F)
    let y ← ($ᵗ G : ProbComp G)
    let pk : G := a • gen
    let x₂ : G := b_scalar • gen
    (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ y)
      (adversary pk)).run' (∅, 0)
  have hbridge : ∀ a b, evalDist (lhs a b) = evalDist (lhs' a b) := by
    intro a b
    apply evalDist_ext
    intro z
    qvcgen_step rw congr' as ⟨b_scalar⟩
    exact probOutput_bind_uniform_smul_eq (gen := gen) hg
      (fun y => do
        let pk : G := a • gen
        let x₂ : G := b_scalar • gen
        (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ y)
          (adversary pk)).run' (∅, 0))
      z
  have hsim :
      ∀ a b,
        evalDist (lhs' a b) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) (a • gen) b k)
          (adversary (a • gen))).run' (∅, 0)) := by
    intro a b
    let pk : G := a • gen
    have hsim_run :
        evalDist (do
          let b_scalar ← ($ᵗ F : ProbComp F)
          let y ← ($ᵗ G : ProbComp G)
          (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k
            (b_scalar • gen) y) (adversary pk)).run (∅, 0) :
            ProbComp (Bool × IND_CPA_HybridState (G := G))) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b k)
          (adversary pk)).run (∅, 0)) := by
      apply evalDist_ext
      intro z
      simpa [pk] using
        stepDDH_rand_simulation_deferred (F := F) (gen := gen) (pk := pk) (b := b) (k := k)
          (a := adversary pk) (st := (∅, 0)) (by omega) (z := z)
    simpa [lhs', pk, StateT.run'] using
      (evalDist_map_eq_of_evalDist_eq (f := Prod.fst) hsim_run)
  have hmain :
      ∀ a b,
        evalDist (lhs a b) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) (a • gen) b k)
          (adversary (a • gen))).run' (∅, 0)) := by
    intro a b
    exact (hbridge a b).trans (hsim a b)
  simpa [stepDDH_randBranchGame, lhs] using
    hybridBranch_probOutput_eq (F := F) (gen := gen) adversary k lhs hmain

-- The DDH experiment decomposes into a mixture of real and random branches.
private lemma ddhExp_stepDDH_eq_mixture
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (k : ℕ) :
    Pr[= true | DiffieHellman.ddhExp gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)] =
    Pr[= true | do
      let d ← ($ᵗ Bool : ProbComp Bool)
      let z ← if d then
        stepDDH_realBranchGame (F := F) (gen := gen) adversary k
      else
        stepDDH_randBranchGame (F := F) (gen := gen) adversary k
      pure (d == z)] := by
  have hrepr :
      Pr[= true | DiffieHellman.ddhExp gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)] =
      Pr[= true | do
        let a ← $ᵗ F; let b_scalar ← $ᵗ F; let d ← $ᵗ Bool
        let z ← if d then
          stepDDH_realBranchCore (F := F) (gen := gen) adversary k a b_scalar
        else
          stepDDH_randBranchCore (F := F) (gen := gen) adversary k a b_scalar
        pure (d == z)] := by
    simp [DiffieHellman.ddhExp, IND_CPA_stepDDHReduction,
      stepDDH_realBranchCore, stepDDH_randBranchCore]
  have hswap₁ :
      Pr[= true | do
        let a ← $ᵗ F; let b_scalar ← $ᵗ F; let d ← $ᵗ Bool
        let z ← if d then
          stepDDH_realBranchCore (F := F) (gen := gen) adversary k a b_scalar
        else
          stepDDH_randBranchCore (F := F) (gen := gen) adversary k a b_scalar
        pure (d == z)] =
      Pr[= true | do
        let a ← $ᵗ F; let d ← ($ᵗ Bool : ProbComp Bool)
        let b_scalar ← $ᵗ F
        let z ← if d then
          stepDDH_realBranchCore (F := F) (gen := gen) adversary k a b_scalar
        else
          stepDDH_randBranchCore (F := F) (gen := gen) adversary k a b_scalar
        pure (d == z)] := by
    qvcgen_step
  have hswap₂ :
      Pr[= true | do
        let a ← $ᵗ F; let d ← ($ᵗ Bool : ProbComp Bool)
        let b_scalar ← $ᵗ F
        let z ← if d then
          stepDDH_realBranchCore (F := F) (gen := gen) adversary k a b_scalar
        else
          stepDDH_randBranchCore (F := F) (gen := gen) adversary k a b_scalar
        pure (d == z)] =
      Pr[= true | do
        let d ← ($ᵗ Bool : ProbComp Bool)
        let a ← $ᵗ F; let b_scalar ← $ᵗ F
        let z ← if d then
          stepDDH_realBranchCore (F := F) (gen := gen) adversary k a b_scalar
        else
          stepDDH_randBranchCore (F := F) (gen := gen) adversary k a b_scalar
        pure (d == z)] := by
    qvcgen_step
  have hfold :
      Pr[= true | do
        let d ← ($ᵗ Bool : ProbComp Bool)
        let a ← $ᵗ F; let b_scalar ← $ᵗ F
        let z ← if d then
          stepDDH_realBranchCore (F := F) (gen := gen) adversary k a b_scalar
        else
          stepDDH_randBranchCore (F := F) (gen := gen) adversary k a b_scalar
        pure (d == z)] =
      Pr[= true | do
        let d ← ($ᵗ Bool : ProbComp Bool)
        let z ← if d then
          stepDDH_realBranchGame (F := F) (gen := gen) adversary k
        else
          stepDDH_randBranchGame (F := F) (gen := gen) adversary k
        pure (d == z)] := by
    qvcgen_step rw congr' as ⟨d⟩
    cases d
    · simp [stepDDH_randBranchGame, stepDDH_randBranchCore,
        map_eq_bind_pure_comp, bind_assoc]
      qvcgen_step rw under 2
      qvcgen_step rw under 1
      qvcgen_step rw
    · simp [stepDDH_realBranchGame, stepDDH_realBranchCore,
        map_eq_bind_pure_comp, bind_assoc]
      qvcgen_step rw under 1
      qvcgen_step rw
  rw [hrepr, hswap₁, hswap₂, hfold]

private lemma ddhExp_stepDDHReduction_decomp_toReal
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (k : ℕ) :
    (Pr[= true |
      DiffieHellman.ddhExp gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal
        - 1 / 2 =
    ((Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)]).toReal -
      (Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k]).toReal) / 2 := by
  rw [ddhExp_stepDDH_eq_mixture (F := F) (gen := gen) adversary k]
  rw [probOutput_uniformBool_branch_toReal_sub_half]
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

private def IND_CPA_allRealChallengeOracle (pk : G) (b : Bool) :
    QueryImpl (G × G →ₒ G × G)
      (StateT (IND_CPA_HybridState (G := G)) ProbComp) := fun mm => do
  let st ← get
  match st.1 mm with
  | some c => return c
  | none =>
      let msg : G := if b then mm.1 else mm.2
      let c ← (elgamalAsymmEnc F G gen).encrypt pk msg
      let cache' := st.1.cacheQuery mm c
      set (cache', st.2 + 1)
      return c

private def IND_CPA_queryImpl_allReal (pk : G) (b : Bool) :
    QueryImpl (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec
      (StateT (IND_CPA_HybridState (G := G)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (IND_CPA_HybridState (G := G)) ProbComp) +
    IND_CPA_allRealChallengeOracle (F := F) (gen := gen) pk b

private lemma allReal_eq_hybrid_on_bounded
    (pk : G) (b : Bool) (realUntil : ℕ)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G)) (hlt : st.2 < realUntil) :
    (IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b t).run st =
    (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil t).run st := by
  cases t with
  | inl _ => rfl
  | inr mm =>
      simp only [IND_CPA_queryImpl_allReal, IND_CPA_queryImpl_hybrid]
      show (IND_CPA_allRealChallengeOracle (F := F) (gen := gen) pk b mm).run st =
        (IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b realUntil mm).run st
      simp only [IND_CPA_allRealChallengeOracle, IND_CPA_hybridChallengeOracle,
        StateT.run_bind, StateT.run_get, pure_bind]
      rcases hcache : st.1 mm with _ | c
      · simp only [if_pos hlt]
      · simp only [StateT.run_pure]

private lemma allReal_counter_mono
    (pk : G) (b : Bool)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G))
    (p : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Range t × IND_CPA_HybridState (G := G))
    (hp : p ∈ support ((IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b t).run st)) :
    st.2 ≤ p.2.2 := by
  have := hybridQueryImpl_counter_mono (F := F) (gen := gen) pk b (st.2 + 1)
    t st (p := p)
  rw [← allReal_eq_hybrid_on_bounded (F := F) (gen := gen) pk b (st.2 + 1) t st (by omega)] at this
  exact this hp

private lemma allReal_counter_le_succ
    (pk : G) (b : Bool)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G))
    (p : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Range t × IND_CPA_HybridState (G := G))
    (hp : p ∈ support ((IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b t).run st)) :
    p.2.2 ≤ st.2 + 1 := by
  cases t with
  | inl tu =>
      simp only [IND_CPA_queryImpl_allReal, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        liftM, monadLift, StateT.instMonadLift] at hp
      rw [StateT.run_lift, mem_support_bind_iff] at hp
      obtain ⟨a, _, ha⟩ := hp
      rw [mem_support_pure_iff] at ha
      have hst : p.2 = st := congrArg Prod.snd ha
      simp [hst]
  | inr mm =>
      change p ∈ support ((IND_CPA_allRealChallengeOracle (F := F) (gen := gen) pk b mm).run st) at hp
      revert hp
      rcases hcache : st.1 mm with _ | c <;> intro hp
      · simp only [IND_CPA_allRealChallengeOracle, hcache,
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
      · simp only [IND_CPA_allRealChallengeOracle, hcache,
          StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hp
        have := congrArg (fun x => x.2.2) hp
        simp at this
        omega

private lemma hybrid_q_probOutput_eq_allReal
    (pk : G) (b : Bool) (q : ℕ)
    {α : Type} (comp : OracleComp (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec α)
    (budget : ℕ)
    (hbound : comp.IsQueryBound budget
      (fun t n => match t with | .inl _ => True | .inr _ => 0 < n)
      (fun t n => match t with | .inl _ => n | .inr _ => n - 1)) :
    ∀ (st : IND_CPA_HybridState (G := G)), st.2 + budget ≤ q →
    ∀ z : α × IND_CPA_HybridState (G := G),
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b q) comp).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b) comp).run st] := by
  revert budget
  induction comp using OracleComp.inductionOn with
  | pure x =>
      intro budget hbound st _ z
      simp
  | query_bind t oa ih =>
      intro budget hbound st hle z
      rw [isQueryBound_query_bind_iff] at hbound
      rcases hbound with ⟨hcan, hcont⟩
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      cases t with
      | inl tu =>
          simp only [IND_CPA_queryImpl_hybrid, IND_CPA_queryImpl_allReal,
            QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
          qvcgen_step as ⟨p, hp⟩
          have hst : p.2 = st := by
            simp only [liftM, monadLift, StateT.instMonadLift] at hp
            rw [StateT.run_lift, mem_support_bind_iff] at hp
            obtain ⟨a, _, ha⟩ := hp
            rw [mem_support_pure_iff] at ha
            exact congrArg Prod.snd ha
          rw [hst]
          simpa using ih p.1 budget (hcont p.1) st hle z
      | inr mm =>
          have hlt : st.2 < q := by
            have hpos : 0 < budget := by simpa using hcan
            omega
          have hquery := allReal_eq_hybrid_on_bounded (F := F) (gen := gen) pk b q (Sum.inr mm) st hlt
          rw [← hquery]
          qvcgen_step as ⟨p, hp⟩
          have hle' : p.2.2 + (budget - 1) ≤ q := by
            have hsucc := allReal_counter_le_succ (F := F) (gen := gen)
              pk b (Sum.inr mm) st p hp
            omega
          simpa using ih p.1 (budget - 1) (hcont p.1) p.2 hle' z

private lemma proj_map_run_simulateQ_eq
    {ι' : Type} {spec' : OracleSpec ι'}
    {σ₁ σ₂ α : Type}
    (impl₁ : QueryImpl spec' (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec' (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ (t : spec'.Domain) (s : σ₁),
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (comp : OracleComp spec' α) (s : σ₁) :
    Prod.map id proj <$> (simulateQ impl₁ comp).run s =
      (simulateQ impl₂ comp).run (proj s) := by
  induction comp using OracleComp.inductionOn generalizing s with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      calc
        ((impl₁ t).run s >>= fun x =>
            Prod.map id proj <$> (simulateQ impl₁ (oa x.1)).run x.2)
            =
            ((impl₁ t).run s >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run (proj x.2)) := by
                  refine bind_congr fun x => ?_
                  simpa using ih x.1 x.2
        _ =
            ((Prod.map id proj <$> (impl₁ t).run s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  exact
                    (bind_map_left (m := ProbComp) (Prod.map id proj)
                      ((impl₁ t).run s)
                      (fun y => (simulateQ impl₂ (oa y.1)).run y.2)).symm
        _ =
            ((impl₂ t).run (proj s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  rw [hproj t s]

private lemma allReal_queryImpl_proj_eq_real
    (pk : G) (b : Bool)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G)) :
    Prod.map id Prod.fst <$>
      (IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b t).run st =
    (((elgamalAsymmEnc F G gen).IND_CPA_queryImpl' pk b) t).run st.1 := by
  rcases st with ⟨cache, n⟩
  cases t with
  | inl tu =>
      simp [IND_CPA_queryImpl_allReal, AsymmEncAlg.IND_CPA_queryImpl']
  | inr mm =>
      rcases hcache : cache mm with _ | c
      · have hallReal :
            Prod.map id Prod.fst <$>
              (IND_CPA_allRealChallengeOracle (F := F) (gen := gen) pk b mm).run (cache, n) =
            (do
              let c ← (elgamalAsymmEnc F G gen).encrypt pk (if b then mm.1 else mm.2)
              pure (c, cache.cacheQuery mm c) : ProbComp _) := by
          simp only [IND_CPA_allRealChallengeOracle, hcache,
            StateT.run_bind, StateT.run_get, pure_bind,
            hybridState_run_liftM_eq (G := G) (st := (cache, n)), bind_assoc,
            StateT.run_pure]
          rw [map_bind]
          refine bind_congr fun c => ?_
          simp
        have hreal :
            (((elgamalAsymmEnc F G gen).IND_CPA_queryImpl' pk b) (Sum.inr mm)).run cache =
            (do
              let c ← (elgamalAsymmEnc F G gen).encrypt pk (if b then mm.1 else mm.2)
              pure (c, cache.cacheQuery mm c) : ProbComp _) := by
          simp [AsymmEncAlg.IND_CPA_queryImpl', QueryImpl.withCaching_apply, hcache,
            StateT.run_bind, StateT.run_get, pure_bind]
        simpa [IND_CPA_queryImpl_allReal] using hallReal.trans hreal.symm
      · simp [IND_CPA_queryImpl_allReal, IND_CPA_allRealChallengeOracle,
          AsymmEncAlg.IND_CPA_queryImpl', QueryImpl.withCaching_apply, hcache,
          StateT.run_bind, StateT.run_get, pure_bind]

private lemma hybrid_q_run'_evalDist_eq_real
    (pk : G) (b : Bool) (q : ℕ)
    {α : Type} (comp : OracleComp (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec α)
    (budget : ℕ)
    (hbound : comp.IsQueryBound budget
      (fun t n => match t with | .inl _ => True | .inr _ => 0 < n)
      (fun t n => match t with | .inl _ => n | .inr _ => n - 1))
    (cache : IND_CPA_LRCache (G := G)) (n : ℕ) (hn : n + budget ≤ q) :
    evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b q)
      comp).run' (cache, n)) =
    evalDist ((simulateQ ((elgamalAsymmEnc F G gen).IND_CPA_queryImpl' pk b)
      comp).run' cache) := by
  have hrun :
      evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b q) comp).run
        (cache, n)) =
      evalDist ((simulateQ (IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b) comp).run
        (cache, n)) := by
    apply evalDist_ext
    intro z
    exact hybrid_q_probOutput_eq_allReal (F := F) (gen := gen) pk b q comp budget hbound
      (cache, n) hn z
  have hhybrid_run' :
      evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b q) comp).run'
        (cache, n)) =
      evalDist ((simulateQ (IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b) comp).run'
        (cache, n)) := by
    simp only [StateT.run']
    simpa [evalDist_map] using congrArg (fun p => Prod.fst <$> p) hrun
  have hrun_eq :
      Prod.map id Prod.fst <$>
        (simulateQ (IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b) comp).run (cache, n) =
      (simulateQ ((elgamalAsymmEnc F G gen).IND_CPA_queryImpl' pk b) comp).run cache :=
    proj_map_run_simulateQ_eq
      (impl₁ := IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b)
      (impl₂ := (elgamalAsymmEnc F G gen).IND_CPA_queryImpl' pk b)
      (proj := Prod.fst)
      (hproj := allReal_queryImpl_proj_eq_real (F := F) (gen := gen) pk b)
      comp (cache, n)
  have hallReal_run' :
      evalDist ((simulateQ (IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b) comp).run'
        (cache, n)) =
      evalDist ((simulateQ ((elgamalAsymmEnc F G gen).IND_CPA_queryImpl' pk b) comp).run'
        cache) := by
    have hrun'_eq :
        (simulateQ (IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b) comp).run' (cache, n) =
        (simulateQ ((elgamalAsymmEnc F G gen).IND_CPA_queryImpl' pk b) comp).run' cache := by
      have hmap := congrArg (fun p => Prod.fst <$> p) hrun_eq
      simpa [StateT.run', fst_map_prod_map] using hmap
    simpa using congrArg evalDist hrun'_eq
  exact hhybrid_run'.trans hallReal_run'

/-- The all-real hybrid (`realUntil = q`) has the same winning probability as the actual
IND-CPA experiment, for any adversary making at most `q` distinct fresh LR queries. -/
theorem IND_CPA_HybridGame_q_eq_game
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (q : ℕ)
    (hq : adversary.MakesAtMostQueries q) :
    (Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary q]).toReal =
    (Pr[= true | IND_CPA_game (gen := gen) adversary]).toReal := by
  congr 1
  have hinner : ∀ (pk : G) (b : Bool),
      evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b q)
        (adversary pk)).run' (∅, 0)) =
      evalDist ((simulateQ ((elgamalAsymmEnc F G gen).IND_CPA_queryImpl' pk b)
        (adversary pk)).run' ∅) :=
    fun pk b => hybrid_q_run'_evalDist_eq_real (F := F) (gen := gen)
      pk b q (adversary pk) q (hq pk) ∅ 0 (by omega)
  simp only [IND_CPA_HybridGame, IND_CPA_game, AsymmEncAlg.IND_CPA_experiment,
    probOutput_bind_eq_tsum]
  refine tsum_congr fun b => ?_
  congr 1
  refine tsum_congr fun ⟨pk, _sk⟩ => ?_
  congr 1
  refine tsum_congr fun b' => ?_
  congr 1
  exact (evalDist_ext_iff.mp (hinner pk b)) b'

/-! ## 7. Main theorem -/

/-- IND-CPA advantage is bounded by the sum of per-hop DDH advantages. This is the
"summed" form before collapsing to a single `ε` bound. -/
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

/-- **Main theorem.** For any adversary making at most `q` LR oracle queries, if every
per-hop DDH reduction has advantage at most `ε`, then the IND-CPA advantage of ElGamal
is at most `q * (2 * ε)`. -/
theorem elGamal_IND_CPA_le_q_mul_ddh
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (q : ℕ) (ε : ℝ)
    (hq : adversary.MakesAtMostQueries q)
    (hddh : ∀ k < q,
      |(Pr[= true | DiffieHellman.ddhExp gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal - 1 / 2| ≤ ε) :
    ((elgamalAsymmEnc F G gen).IND_CPA_advantage adversary).toReal ≤ q * (2 * ε) := by
  refine le_trans (elGamal_IND_CPA_bound_toReal hg adversary q
    (IND_CPA_HybridGame_q_eq_game (gen := gen) adversary q hq)) ?_
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

game_hop_widget VCVioWidgets.GameHop.Examples.ElGamal.hybridSequenceDiagram

#print axioms elGamal_IND_CPA_le_q_mul_ddh

end IND_CPA

end elgamalAsymmEnc
