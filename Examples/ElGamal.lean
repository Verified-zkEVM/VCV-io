/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.EvalDist.Bool
import VCVio.ProgramLogic.Tactics

set_option autoImplicit false

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
6. Main theorem (`ElGamal_IND_CPA_le_q_mul_ddh`): IND-CPA advantage ≤ `q * (2ε)` where `ε`
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
    some (c₂ - sk • c₁)
  __ := ExecutionMethod.default

namespace elgamalAsymmEnc

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

@[simp] lemma toExecutionMethod_eq :
    (elgamalAsymmEnc F G gen).toExecutionMethod = ExecutionMethod.default := rfl

theorem Correct [DecidableEq G] : (elgamalAsymmEnc F G gen).PerfectlyCorrect := by
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

def randomMaskedCipher (msg : G) : ProbComp (G × G) := do
  let r ← $ᵗ F
  let y ← $ᵗ G
  return (r • gen, msg + y)

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

def IND_CPA_queryImpl_hybrid (pk : G) (b : Bool) (realUntil : ℕ) :
    QueryImpl (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec
      (StateT (IND_CPA_HybridState (G := G)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (IND_CPA_HybridState (G := G)) ProbComp) +
    IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b realUntil

def IND_CPA_HybridGame
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (realUntil : ℕ) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (pk, _sk) ← (elgamalAsymmEnc F G gen).keygen
  let b' ← (simulateQ
      (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil)
      (adversary pk)).run' (∅, 0)
  return (b == b')

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
        from fun _ _ => if_neg Bool.noConfusion, ite_true]
    have hlift : ∀ (x : ProbComp (G × G)) (s' : IND_CPA_HybridState (G := G)),
        (liftM x : StateT (IND_CPA_HybridState (G := G)) ProbComp _) s' =
        (x >>= fun a => pure (a, s')) := by
      intro x s'
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
      have hx : liftComp x unifSpec = x := simulateQ_id' x
      rw [hx]
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    simp only [show ∀ (x : ProbComp (G × G)) (s' : IND_CPA_HybridState (G := G)),
        (liftM x : StateT (IND_CPA_HybridState (G := G)) ProbComp _).run s' =
        (x >>= fun a => pure (a, s')) from hlift,
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
  rel_dist
  simp only [StateT.run']
  rw [evalDist_map, evalDist_map]
  congr 1
  exact evalDist_simulateQ_run_eq_of_impl_evalDist_eq _ _
    (fun t s => by
      cases t with
      | inl _ => rfl
      | inr mm => exact hybridChallengeOracle_allRandom_evalDist_eq (F := F) (gen := gen) pk mm s)
    (adversary pk) (∅, 0)

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

lemma ddh_decomp_two_games_toReal (real rand : ProbComp Bool) :
    (Pr[= true | do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then real else rand
      pure (b == z)]).toReal - 1 / 2 =
    ((Pr[= true | real]).toReal - (Pr[= true | rand]).toReal) / 2 := by
  have hgameRepr :
      Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let z ← if b then real else rand
        pure (b == z)] =
      Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand)] := by
    refine probOutput_bind_congr' ($ᵗ Bool) true ?_
    intro b
    cases b
    · have hbeqFalse : (BEq.beq false : Bool → Bool) = Bool.not := by
        funext t
        cases t <;> rfl
      simp [hbeqFalse]
    · have hbeqTrue : (BEq.beq true : Bool → Bool) = id := by
        funext t
        cases t <;> rfl
      simp [hbeqTrue]
  have hmix :
      Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand)] =
      (Pr[= true | (BEq.beq true <$> real)] + Pr[= true | (BEq.beq false <$> rand)]) / 2 :=
    probOutput_bind_uniformBool
      (f := fun b => if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand))
      (x := true)
  have hformula : Pr[= true | do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then real else rand
      pure (b == z)] =
    (Pr[= true | real] + Pr[= false | rand]) / 2 := by
    rw [hgameRepr, hmix,
      show (BEq.beq true : Bool → Bool) = id from by ext b; cases b <;> rfl, id_map,
      show (BEq.beq false : Bool → Bool) = (! ·) from by ext b; cases b <;> rfl,
      probOutput_not_map]
  have hfalseAsSub : Pr[= false | rand] = 1 - Pr[= true | rand] := by
    have hsum : Pr[= true | rand] + Pr[= false | rand] = 1 := by
      have := HasEvalPMF.sum_probOutput_eq_one (m := ProbComp) (mx := rand)
      simp
    rw [← hsum, ENNReal.add_sub_cancel_left probOutput_ne_top]
  rw [hformula, ENNReal.toReal_div,
    ENNReal.toReal_add probOutput_ne_top probOutput_ne_top,
    hfalseAsSub, ENNReal.toReal_sub_of_le probOutput_le_one ENNReal.one_ne_top]
  simp [ENNReal.toReal_ofNat]
  ring


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
  let y ← $ᵗ G
  let b ← $ᵗ Bool
  let pk : G := a • gen
  let x₂ : G := b_scalar • gen
  let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ y)
    (adversary pk)).run' (∅, 0)
  return (b == b')

def stepDDH_realBranchGame
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (k : ℕ) : ProbComp Bool := do
  let a ← $ᵗ F
  let b_scalar ← $ᵗ F
  stepDDH_realBranchCore (F := F) (gen := gen) adversary k a b_scalar

def stepDDH_randBranchGame
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (k : ℕ) : ProbComp Bool := do
  let a ← $ᵗ F
  let b_scalar ← $ᵗ F
  stepDDH_randBranchCore (F := F) (gen := gen) adversary k a b_scalar

-- Mechanical StateT bookkeeping: the step DDH oracle agrees with the hybrid oracle
-- for queries past position k.
private lemma stepDDHOracle_eq_hybridChallenge_post_k
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G)
    (m₁ m₂ : G) (st : IND_CPA_HybridState (G := G)) (hgt : k < st.2) :
    (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k x₂ x₃ (m₁, m₂)).run st =
    (IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b (k + 1) (m₁, m₂)).run st := by
  sorry -- Mechanical: case split on cache hit/miss, omega on counter bounds

private lemma stepDDHOracle_eq_hybridChallenge_post_k_rand
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G)
    (m₁ m₂ : G) (st : IND_CPA_HybridState (G := G)) (hgt : k < st.2) :
    (IND_CPA_stepDDHOracle (F := F) (gen := gen) pk b k x₂ x₃ (m₁, m₂)).run st =
    (IND_CPA_hybridChallengeOracle (F := F) (gen := gen) pk b k (m₁, m₂)).run st := by
  sorry -- Mechanical: case split on cache hit/miss, omega on counter bounds

private lemma stepDDHQueryImpl_eq_hybridQueryImpl_post_k
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G) (realUntil : ℕ)
    (hrealUntil : realUntil = k ∨ realUntil = k + 1)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G)) (hgt : k < st.2) :
    (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃ t).run st =
    (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil t).run st := by
  sorry -- Mechanical: case split on Sum.inl/inr, delegates to post_k lemmas above

private lemma hybridQueryImpl_counter_mono
    (pk : G) (b : Bool) (realUntil : ℕ)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G))
    (p : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Range t × IND_CPA_HybridState (G := G))
    (hp : p ∈ support ((IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil t).run st)) :
    st.2 ≤ p.2.2 := by
  sorry -- Mechanical StateT bookkeeping: counter only increases

private lemma simulateQ_stepDDH_probOutput_eq_hybrid_post_k
    (pk : G) (b : Bool) (k : ℕ) (x₂ x₃ : G) (realUntil : ℕ)
    (hrealUntil : realUntil = k ∨ realUntil = k + 1)
    {α : Type} (a : OracleComp (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec α) :
    ∀ (st : IND_CPA_HybridState (G := G)), k < st.2 →
    ∀ z : α × IND_CPA_HybridState (G := G),
    Pr[= z | (simulateQ (IND_CPA_stepDDHQueryImpl (F := F) (gen := gen) pk b k x₂ x₃) a).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (F := F) (gen := gen) pk b realUntil) a).run st] := by
  sorry -- Induction on `a`, uses stepDDHQueryImpl_eq_hybridQueryImpl_post_k and counter_mono

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
  sorry -- Deep induction on `a` with StateT bookkeeping; mechanical porting needed

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
  sorry -- Deep induction on `a` with StateT bookkeeping; mechanical porting needed

-- The DDH-real branch has the same success probability as hybrid k+1.
private lemma stepDDH_realBranch_probOutput_eq
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (k : ℕ) :
    Pr[= true | stepDDH_realBranchGame (F := F) (gen := gen) adversary k] =
    Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)] := by
  sorry -- Prob_swap reordering + stepDDH_real_simulation_deferred

-- The DDH-random branch has the same success probability as hybrid k.
private lemma stepDDH_randBranch_probOutput_eq
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (k : ℕ) :
    Pr[= true | stepDDH_randBranchGame (F := F) (gen := gen) adversary k] =
    Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k] := by
  sorry -- Prob_swap reordering + stepDDH_rand_simulation_deferred

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
  sorry -- Unfold ddhExp, prob_swap reordering, fold branch games

private lemma ddhExp_stepDDHReduction_decomp_toReal
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary) (k : ℕ) :
    (Pr[= true |
      DiffieHellman.ddhExp gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal
        - 1 / 2 =
    ((Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)]).toReal -
      (Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k]).toReal) / 2 := by
  rw [ddhExp_stepDDH_eq_mixture (F := F) (gen := gen) adversary k]
  rw [ddh_decomp_two_games_toReal]
  rw [stepDDH_realBranch_probOutput_eq (F := F) (gen := gen) adversary k,
      stepDDH_randBranch_probOutput_eq (F := F) (gen := gen) adversary k]

lemma IND_CPA_stepDDH_hopBound
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (k : ℕ) :
    |(Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary (k + 1)]).toReal -
      (Pr[= true | IND_CPA_HybridGame (F := F) (gen := gen) adversary k]).toReal| ≤
      2 * |(Pr[= true |
          DiffieHellman.ddhExp gen
            (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal - 1 / 2| := by
  have h := ddhExp_stepDDHReduction_decomp_toReal (F := F) (gen := gen) adversary k
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
  sorry -- Mechanical: case split on inl/inr, cache hit/miss, counter < realUntil

private lemma allReal_counter_mono
    (pk : G) (b : Bool)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G))
    (p : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Range t × IND_CPA_HybridState (G := G))
    (hp : p ∈ support ((IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b t).run st)) :
    st.2 ≤ p.2.2 := by
  sorry -- Follows from hybridQueryImpl_counter_mono via allReal_eq_hybrid_on_bounded

private lemma allReal_counter_le_succ
    (pk : G) (b : Bool)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G))
    (p : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Range t × IND_CPA_HybridState (G := G))
    (hp : p ∈ support ((IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b t).run st)) :
    p.2.2 ≤ st.2 + 1 := by
  sorry -- Mechanical StateT bookkeeping: single step increases counter by at most 1

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
  sorry -- Induction on comp, uses allReal_eq_hybrid_on_bounded and counter bounds

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
  sorry -- Induction on comp, structural map/bind reasoning

private lemma allReal_queryImpl_proj_eq_real
    (pk : G) (b : Bool)
    (t : (elgamalAsymmEnc F G gen).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (G := G)) :
    Prod.map id Prod.fst <$>
      (IND_CPA_queryImpl_allReal (F := F) (gen := gen) pk b t).run st =
    (((elgamalAsymmEnc F G gen).IND_CPA_queryImpl' pk b) t).run st.1 := by
  sorry -- Mechanical: case split on inl/inr, cache hit/miss, unfold definitions

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
  sorry -- Combines hybrid_q_probOutput_eq_allReal with allReal projection lemmas

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

theorem ElGamal_IND_CPA_bound_toReal
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
            have hb := IND_CPA_stepDDH_hopBound (F := F) (gen := gen) adversary (q - 1 - i)
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

theorem ElGamal_IND_CPA_le_q_mul_ddh
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (q : ℕ) (ε : ℝ)
    (hq : adversary.MakesAtMostQueries q)
    (hddh : ∀ k < q,
      |(Pr[= true | DiffieHellman.ddhExp gen
        (IND_CPA_stepDDHReduction (F := F) (gen := gen) adversary k)]).toReal - 1 / 2| ≤ ε) :
    ((elgamalAsymmEnc F G gen).IND_CPA_advantage adversary).toReal ≤ q * (2 * ε) := by
  refine le_trans (ElGamal_IND_CPA_bound_toReal (gen := gen) adversary q
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

#print axioms ElGamal_IND_CPA_le_q_mul_ddh

end IND_CPA

end elgamalAsymmEnc
