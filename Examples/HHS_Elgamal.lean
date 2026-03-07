/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.EvalDist.Bool
import VCVio.ProgramLogic.Tactics

set_option linter.style.longFile 2100

/-!
# ElGamal over Hard Homogeneous Spaces: Multi-query IND-CPA via DDH

This file defines ElGamal encryption on an additive torsor (`AddTorsor G P`) and proves
multi-query oracle IND-CPA security via a q-step hybrid argument reducing to DDH.

## Proof structure

1. ElGamal definition and correctness.
2. Hybrid game family: the i-th game uses real ElGamal for the first i fresh LR oracle
   queries and random masking thereafter.
3. Key lemma (`IND_CPA_allRandomHalf`): the all-random hybrid (i = 0) has success probability
   exactly 1/2, because `randomMaskedCipher` produces a uniform distribution independent of the
   message (the second component `msg * y` with `y ~ U(P)` is uniform in `P`). The proof uses
   a relational coupling argument (`RelTriple`) via `OracleComp.inductionOn`.
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

variable {G P : Type} [SampleableType G] [SampleableType P]
    [AddCommGroup G] [Group P] [AddTorsor G P]

/-! ## 1. ElGamal definition and correctness -/

/-- ElGamal-style encryption adapted to a hard homogeneous space (`AddTorsor G P`). -/
@[simps!] def elgamalAsymmEnc (G P : Type) [SampleableType G] [SampleableType P]
    [AddCommGroup G] [Group P] [AddTorsor G P] : AsymmEncAlg ProbComp
    (M := P) (PK := P × P) (SK := G) (C := P × P) where
  keygen := do
    let x₀ ← $ᵗ P
    let sk ← $ᵗ G
    return ((x₀, sk +ᵥ x₀), sk)
  encrypt := fun (x₀, pk) msg => do
    let g ← $ᵗ G
    return (g +ᵥ x₀, msg * (g +ᵥ pk))
  decrypt := fun sk (c₁, c₂) =>
    some (c₂ / (sk +ᵥ c₁))
  __ := ExecutionMethod.default

namespace elgamalAsymmEnc

variable {G P : Type} [SampleableType G] [SampleableType P]
    [AddCommGroup G] [Group P] [AddTorsor G P]

@[simp] lemma toExecutionMethod_eq :
    (elgamalAsymmEnc G P).toExecutionMethod = ExecutionMethod.default := rfl

/-- ElGamal decrypts correctly for every message. -/
theorem Correct [DecidableEq P] : (elgamalAsymmEnc G P).PerfectlyCorrect := by
  have hcancel : ∀ (msg x : P) (g₁ g₂ : G),
      msg * (g₂ +ᵥ (g₁ +ᵥ x)) / (g₁ +ᵥ (g₂ +ᵥ x)) = msg :=
    fun m x g₁ g₂ => by
      rw [vadd_comm g₁ g₂ x, mul_div_cancel_right]
  simp [AsymmEncAlg.PerfectlyCorrect, AsymmEncAlg.CorrectExp, elgamalAsymmEnc, hcancel]

/-! ## 2. Hybrid game infrastructure -/

section IND_CPA

variable [DecidableEq P]

/-- Cache type for LR oracle responses (indexed by message pair). -/
abbrev IND_CPA_LRCache := (P × P →ₒ P × P).QueryCache

/-- Hybrid state: query cache plus fresh-query counter. -/
abbrev IND_CPA_HybridState := IND_CPA_LRCache (P := P) × ℕ

/-- Random masking: ephemeral key from G, mask from P, so the second component is
    uniformly distributed in P regardless of `msg`. -/
def randomMaskedCipher (pk : P × P) (msg : P) : ProbComp (P × P) := do
  let g ← $ᵗ G
  let y ← $ᵗ P
  return (g +ᵥ pk.1, msg * y)

/-- Hybrid LR challenge oracle:
    - cache hit: return cached response
    - fresh query with counter < realUntil: real ElGamal encryption
    - fresh query with counter ≥ realUntil: random masking -/
def IND_CPA_hybridChallengeOracle (pk : P × P) (b : Bool) (realUntil : ℕ) :
    QueryImpl (P × P →ₒ P × P)
      (StateT (IND_CPA_HybridState (P := P)) ProbComp) := fun mm => do
  let st ← get
  match st.1 mm with
  | some c => return c
  | none =>
      let msg : P := if b then mm.1 else mm.2
      let c ← if st.2 < realUntil then
          (elgamalAsymmEnc G P).encrypt pk msg
        else
          randomMaskedCipher (G := G) (P := P) pk msg
      let cache' := st.1.cacheQuery mm c
      set (cache', st.2 + 1)
      return c

/-- Full hybrid oracle: unifSpec queries pass through, LR queries go to the hybrid
    challenge oracle. -/
def IND_CPA_queryImpl_hybrid (pk : P × P) (b : Bool) (realUntil : ℕ) :
    QueryImpl (elgamalAsymmEnc G P).IND_CPA_oracleSpec
      (StateT (IND_CPA_HybridState (P := P)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (IND_CPA_HybridState (P := P)) ProbComp) +
    IND_CPA_hybridChallengeOracle (G := G) (P := P) pk b realUntil

/-- Hybrid game: the adversary's first `realUntil` fresh LR queries are answered with
    real ElGamal encryptions; all subsequent fresh queries are randomly masked. -/
def IND_CPA_HybridGame
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (realUntil : ℕ) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (pk, _sk) ← (elgamalAsymmEnc G P).keygen
  let b' ← (simulateQ
      (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b realUntil)
      (adversary pk)).run' (∅, 0)
  return (b == b')

/-- Decreasing hybrid family: `games 0` = `hybrid q` (real game with q real queries),
    `games q` = `hybrid 0` (all-random game). -/
def IND_CPA_HybridFamily
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (q : ℕ) : ℕ → ProbComp Bool :=
  fun i => IND_CPA_HybridGame (G := G) (P := P) adversary (q - i)

@[simp] lemma IND_CPA_HybridFamily_zero
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (q : ℕ) :
    IND_CPA_HybridFamily (G := G) (P := P) adversary q 0 =
      IND_CPA_HybridGame (G := G) (P := P) adversary q := by
  simp [IND_CPA_HybridFamily]

@[simp] lemma IND_CPA_HybridFamily_q
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (q : ℕ) :
    IND_CPA_HybridFamily (G := G) (P := P) adversary q q =
      IND_CPA_HybridGame (G := G) (P := P) adversary 0 := by
  simp [IND_CPA_HybridFamily]

/-- IND-CPA experiment as an alias (equals `IND_CPA_experiment` by definition). -/
abbrev IND_CPA_game
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) : ProbComp Bool :=
  (elgamalAsymmEnc G P).IND_CPA_experiment adversary

/-! ## 3. All-random hybrid has probability 1/2 -/

open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational

/-- `randomMaskedCipher` has the same distribution regardless of `msg`:
left-multiplication by a fixed element is a bijection on `P`, so `msg * y`
with `y ~ U(P)` is uniform in `P`. -/
lemma randomMaskedCipher_dist_indep (pk : P × P) (m₁ m₂ : P) :
    evalDist (randomMaskedCipher (G := G) (P := P) pk m₁) =
    evalDist (randomMaskedCipher (G := G) (P := P) pk m₂) := by
  apply evalDist_ext; intro ⟨c₁, c₂⟩
  simp only [randomMaskedCipher, probOutput_bind_eq_tsum, probOutput_pure, Prod.mk.injEq]
  congr 1; funext g; congr 1
  by_cases h : c₁ = g +ᵥ pk.1
  · simp only [h, true_and]
    have hsum : ∀ msg : P,
        (∑' y, Pr[= y | $ᵗ P] * if c₂ = msg * y then 1 else 0) =
          Pr[= msg⁻¹ * c₂ | $ᵗ P] := by
      intro msg
      rw [tsum_eq_single (msg⁻¹ * c₂)]
      · have : msg * (msg⁻¹ * c₂) = c₂ := by group
        simp [this]
      · intro y hy
        have : c₂ ≠ msg * y := fun heq => hy (show y = msg⁻¹ * c₂ by rw [heq]; group)
        simp [this]
    rw [hsum, hsum]
    exact SampleableType.probOutput_selectElem_eq _ _
  · simp [h]

/-- The oracle simulation's output is independent of `b` in the all-random hybrid.
This is expressed as a relational triple: running with `b = true` vs `b = false`
produces equal distributions. -/


private lemma hybridChallengeOracle_allRandom_evalDist_eq
    (pk : P × P) (mm : P × P) (s : IND_CPA_HybridState (P := P)) :
    evalDist ((IND_CPA_hybridChallengeOracle (G := G) (P := P) pk true 0 mm).run s) =
    evalDist ((IND_CPA_hybridChallengeOracle (G := G) (P := P) pk false 0 mm).run s) := by
  simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind, StateT.run_get, pure_bind,
    Nat.not_lt_zero, ite_false]
  cases hs : s.1 mm with
  | some _ => rfl
  | none =>
    simp only [show ∀ (a b : P), (if (false : Bool) = true then a else b) = b
        from fun _ _ => if_neg Bool.noConfusion, ite_true]
    have hlift : ∀ (x : ProbComp (P × P)) (s' : IND_CPA_HybridState (P := P)),
        (liftM x : StateT (IND_CPA_HybridState (P := P)) ProbComp _) s' =
        (x >>= fun a => pure (a, s')) := by
      intro x s'
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
      have hx : liftComp x unifSpec = x := simulateQ_id' x
      rw [hx]
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    simp only [show ∀ (x : ProbComp (P × P)) (s' : IND_CPA_HybridState (P := P)),
        (liftM x : StateT (IND_CPA_HybridState (P := P)) ProbComp _).run s' =
        (x >>= fun a => pure (a, s')) from hlift,
      bind_assoc, pure_bind]
    rw [evalDist_bind, evalDist_bind]
    congr 1
    · exact randomMaskedCipher_dist_indep pk mm.1 mm.2

lemma IND_CPA_hybridOracle_allRandom_eqDist
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (pk : P × P) :
    RelTriple
      ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0)
        (adversary pk)).run' (∅, 0))
      ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0)
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
      | inr mm => exact hybridChallengeOracle_allRandom_evalDist_eq pk mm s)
    (adversary pk) (∅, 0)

/-- The all-random hybrid game has success probability exactly 1/2.

    **Proof strategy** (see backup branch `quang/elgamal-backup` for full proof):
    The key insight is that `randomMaskedCipher pk msg` has the same distribution for any `msg`,
    because `msg * y` with `y ~ U(P)` is uniform in `P` (left-multiplication is a bijection).
    Therefore in hybrid 0 (all-random), the oracle simulation's output distribution is
    independent of the hidden bit `b`. Guessing `b` correctly then happens with probability 1/2.
    The formal proof proceeds by `OracleComp.inductionOn` with a `RelTriple` coupling argument
    showing the `b = true` and `b = false` branches have identical distributions. -/
theorem IND_CPA_allRandomHalf
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) :
    Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary 0] = 1 / 2 := by
  simp only [IND_CPA_HybridGame,
    show ∀ (a b : Bool), (a == b) = decide (a = b) from by decide]
  have hassoc : ∀ b : Bool,
      ((elgamalAsymmEnc G P).keygen >>= fun x =>
        (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) x.1 b 0)
          (adversary x.1)).run' (∅, 0) >>= fun b' =>
          pure (decide (b = b'))) =
      ((elgamalAsymmEnc G P).keygen >>= fun x =>
        (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) x.1 b 0)
          (adversary x.1)).run' (∅, 0)) >>= fun b' =>
        pure (decide (b = b')) :=
    fun _ => (bind_assoc _ _ _).symm
  simp_rw [hassoc]
  exact probOutput_decide_eq_uniformBool_half _ (by
    simp only [evalDist_bind]
    congr 1; funext ⟨pk, _⟩
    by_equiv
    exact IND_CPA_hybridOracle_allRandom_eqDist adversary pk)

/-! ## 3a. DDH helper lemmas -/



omit [DecidableEq P] in
/-- Left-multiplying a uniform sample by a fixed group element preserves the distribution. -/
lemma probOutput_mul_left_uniform (m x : P) :
    Pr[= x | (fun y : P => m * y) <$> ($ᵗ P)] = Pr[= x | $ᵗ P] := by
  have h : Pr[= m * (m⁻¹ * x) | (fun y : P => m * y) <$> ($ᵗ P)] =
      Pr[= m⁻¹ * x | $ᵗ P] :=
    probOutput_map_injective
      (mx := ($ᵗ P))
      (f := fun y : P => m * y)
      (hf := by
        intro a b hab
        exact mul_left_cancel hab)
      (x := m⁻¹ * x)
  calc
    Pr[= x | (fun y : P => m * y) <$> ($ᵗ P)]
        = Pr[= m * (m⁻¹ * x) | (fun y : P => m * y) <$> ($ᵗ P)] := by simp
    _ = Pr[= m⁻¹ * x | $ᵗ P] := h
    _ = Pr[= x | $ᵗ P] := by
          symm
          simpa [uniformSample] using
            (SampleableType.probOutput_selectElem_eq (β := P) x (m⁻¹ * x))

omit [DecidableEq P] in
/-- Uniform masking is invariant under fixed left-multiplication inside a bind. -/
lemma probOutput_bind_mul_left_uniform {β : Type} (m : P) (f : P → ProbComp β) (z : β) :
    Pr[= z | (do let y ← $ᵗ P; f (m * y))] =
      Pr[= z | (do let y ← $ᵗ P; f y)] := by
  have hleft :
      (do let y ← $ᵗ P; f (m * y)) = (((fun y : P => m * y) <$> ($ᵗ P)) >>= fun y => f y) := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [hleft, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun y => ?_
  rw [probOutput_mul_left_uniform (P := P) m y]

/-- DDH branch decomposition: the DDH experiment's success probability decomposes into
the average of the real and random branch success probabilities. -/
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

/-- The DDH reduction oracle for the hop from `hybrid k` to `hybrid k+1`.
    For the k-th fresh query, it embeds the DDH challenge `(x₂, x₃)` directly:
    - DDH-real (`x₃ = g₂ +ᵥ x₁`): equivalent to real ElGamal encryption.
    - DDH-random (`x₃ ~ U(P)`): equivalent to random masking. -/
private def IND_CPA_stepDDHOracle
    (pk : P × P) (b : Bool) (k : ℕ) (x₂ x₃ : P) :
    QueryImpl (P × P →ₒ P × P)
      (StateT (IND_CPA_HybridState (P := P)) ProbComp) := fun (m₁, m₂) => do
  let st ← get
  match st.1 (m₁, m₂) with
  | some c => return c
  | none =>
      let msg : P := if b then m₁ else m₂
      let c ←
        if st.2 < k then
          (elgamalAsymmEnc G P).encrypt pk msg
        else if st.2 = k then
          pure (x₂, msg * x₃)
        else
          randomMaskedCipher (G := G) (P := P) pk msg
      let cache' := st.1.cacheQuery (m₁, m₂) c
      set (cache', st.2 + 1)
      return c

private def IND_CPA_stepDDHQueryImpl
    (pk : P × P) (b : Bool) (k : ℕ) (x₂ x₃ : P) :
    QueryImpl (elgamalAsymmEnc G P).IND_CPA_oracleSpec
      (StateT (IND_CPA_HybridState (P := P)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (IND_CPA_HybridState (P := P)) ProbComp) +
    IND_CPA_stepDDHOracle (G := G) (P := P) pk b k x₂ x₃

/-- The DDH adversary for the k-th hybrid hop. Given DDH challenge `(x, x₁, x₂, x₃)`,
    uses `(x, x₁)` as public key and embeds `(x₂, msg * x₃)` at the k-th fresh query. -/
def IND_CPA_stepDDHReduction
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) : DiffieHellman.DDHAdversary G P :=
  fun x x₁ x₂ x₃ => do
    let b ← $ᵗ Bool
    let pk : P × P := (x, x₁)
    let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
      (adversary pk)).run' (∅, 0)
    return (b == b')

/-! ## 5. Per-hop bound -/

def stepDDH_realBranchCore
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) (x : P) (g₁ g₂ : G) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let pk : P × P := (x, g₁ +ᵥ x)
  let x₂ : P := g₂ +ᵥ x
  let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
  let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
    (adversary pk)).run' (∅, 0)
  return (b == b')

def stepDDH_randBranchCore
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) (x : P) (g₁ g₂ : G) : ProbComp Bool := do
  let y ← $ᵗ P
  let b ← $ᵗ Bool
  let pk : P × P := (x, g₁ +ᵥ x)
  let x₂ : P := g₂ +ᵥ x
  let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
    (adversary pk)).run' (∅, 0)
  return (b == b')

def stepDDH_realBranchGame
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) : ProbComp Bool := do
  let x ← $ᵗ P
  let g₁ ← $ᵗ G
  let g₂ ← $ᵗ G
  stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂

def stepDDH_randBranchGame
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) : ProbComp Bool := do
  let x ← $ᵗ P
  let g₁ ← $ᵗ G
  let g₂ ← $ᵗ G
  stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂

private lemma stepDDHOracle_eq_hybridChallenge_post_k
    (pk : P × P) (b : Bool) (k : ℕ) (x₂ x₃ : P)
    (m₁ m₂ : P) (st : IND_CPA_HybridState (P := P)) (hgt : k < st.2) :
    (IND_CPA_stepDDHOracle (G := G) (P := P) pk b k x₂ x₃ (m₁, m₂)).run st =
    (IND_CPA_hybridChallengeOracle (G := G) (P := P) pk b (k + 1) (m₁, m₂)).run st := by
  simp only [IND_CPA_stepDDHOracle, IND_CPA_hybridChallengeOracle]
  rcases h : st.1 (m₁, m₂) with _ | c
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, h,
      if_neg (by omega : ¬ st.2 < k), if_neg (by omega : ¬ (st.2 = k)),
      if_neg (by omega : ¬ st.2 < k + 1)]
  · simp [StateT.run_bind, StateT.run_get, pure_bind, h]

private lemma stepDDHOracle_eq_hybridChallenge_post_k_rand
    (pk : P × P) (b : Bool) (k : ℕ) (x₂ x₃ : P)
    (m₁ m₂ : P) (st : IND_CPA_HybridState (P := P)) (hgt : k < st.2) :
    (IND_CPA_stepDDHOracle (G := G) (P := P) pk b k x₂ x₃ (m₁, m₂)).run st =
    (IND_CPA_hybridChallengeOracle (G := G) (P := P) pk b k (m₁, m₂)).run st := by
  simp only [IND_CPA_stepDDHOracle, IND_CPA_hybridChallengeOracle]
  rcases h : st.1 (m₁, m₂) with _ | c
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, h,
      if_neg (by omega : ¬ st.2 < k), if_neg (by omega : ¬ (st.2 = k))]
  · simp [StateT.run_bind, StateT.run_get, pure_bind, h]

private lemma stepDDHQueryImpl_eq_hybridQueryImpl_post_k
    (pk : P × P) (b : Bool) (k : ℕ) (x₂ x₃ : P) (realUntil : ℕ)
    (hrealUntil : realUntil = k ∨ realUntil = k + 1)
    (t : (elgamalAsymmEnc G P).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (P := P)) (hgt : k < st.2) :
    (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃ t).run st =
    (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b realUntil t).run st := by
  cases t with
  | inl tu =>
      simp [IND_CPA_stepDDHQueryImpl, IND_CPA_queryImpl_hybrid]
  | inr mm =>
      obtain ⟨m₁, m₂⟩ := mm
      simp only [IND_CPA_stepDDHQueryImpl, IND_CPA_queryImpl_hybrid]
      rcases hrealUntil with h | h <;> simp only [h]
      · exact stepDDHOracle_eq_hybridChallenge_post_k_rand
          (G := G) (P := P) pk b k x₂ x₃ m₁ m₂ st hgt
      · exact stepDDHOracle_eq_hybridChallenge_post_k
          (G := G) (P := P) pk b k x₂ x₃ m₁ m₂ st hgt

private lemma hybridQueryImpl_counter_mono
    (pk : P × P) (b : Bool) (realUntil : ℕ)
    (t : (elgamalAsymmEnc G P).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (P := P))
    (p : (elgamalAsymmEnc G P).IND_CPA_oracleSpec.Range t × IND_CPA_HybridState (P := P))
    (hp : p ∈ support ((IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b realUntil t).run st)) :
    st.2 ≤ p.2.2 := by
  cases t with
  | inl tu =>
      simp only [IND_CPA_queryImpl_hybrid, QueryImpl.add_apply,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        liftM, monadLift, StateT.instMonadLift] at hp
      rw [StateT.run_lift] at hp
      rw [mem_support_bind_iff] at hp
      obtain ⟨a, _, ha⟩ := hp
      rw [mem_support_pure_iff] at ha
      have h2 : p.2 = st := congrArg Prod.snd ha
      simp [h2]
  | inr mm =>
      obtain ⟨m₁, m₂⟩ := mm
      change p ∈ support ((IND_CPA_hybridChallengeOracle (G := G) (P := P)
        pk b realUntil (m₁, m₂)).run st) at hp
      revert hp
      rcases hcache : st.1 (m₁, m₂) with _ | c <;> intro hp
      · simp only [IND_CPA_hybridChallengeOracle, hcache, StateT.run_bind, StateT.run_get,
          pure_bind] at hp
        rw [mem_support_iff] at hp
        rw [← mem_support_iff] at hp
        have hlift : ∀ (x : ProbComp (P × P)),
            (liftM x : StateT (IND_CPA_HybridState (P := P)) ProbComp (P × P)).run st =
            x >>= fun a => pure (a, st) := by
          intro x
          simp only [liftM, MonadLiftT.monadLift,
            show ∀ (x : ProbComp (P × P)),
                OracleComp.liftComp x unifSpec = x from
              fun x => monadLift_eq_self x,
            MonadLift.monadLift, StateT.run_lift]
        split_ifs at hp with h
        all_goals
          simp only [StateT.run_bind, StateT.run_pure, pure_bind, hlift, bind_assoc,
            support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hp
          obtain ⟨c, _, ⟨i, hi, hp⟩⟩ := hp
          have hset : ∀ (s' : IND_CPA_HybridState (P := P)),
              (set s' : StateT (IND_CPA_HybridState (P := P)) ProbComp PUnit).run st =
              (pure (PUnit.unit, s') : ProbComp _) := fun _ => rfl
          simp only [hset, support_pure, Set.mem_singleton_iff] at hi
          subst hi
          simp only [hp]
          omega
      · simp only [IND_CPA_hybridChallengeOracle, hcache,
          StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hp
        have := congrArg (fun x => x.2.2) hp
        simp at this
        omega

private lemma simulateQ_stepDDH_probOutput_eq_hybrid_post_k
    (pk : P × P) (b : Bool) (k : ℕ) (x₂ x₃ : P) (realUntil : ℕ)
    (hrealUntil : realUntil = k ∨ realUntil = k + 1)
    {α : Type} (a : OracleComp (elgamalAsymmEnc G P).IND_CPA_oracleSpec α) :
    ∀ (st : IND_CPA_HybridState (P := P)), k < st.2 →
    ∀ z : α × IND_CPA_HybridState (P := P),
    Pr[= z | (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃) a).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b realUntil) a).run st] := by
  induction a using OracleComp.inductionOn with
  | pure x =>
      intro st _ z
      simp
  | query_bind t oa ih =>
      intro st hgt z
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      have hq := stepDDHQueryImpl_eq_hybridQueryImpl_post_k (G := G) (P := P) pk b k x₂ x₃
        realUntil hrealUntil t st hgt
      rw [hq]
      refine probOutput_bind_congr fun p hp => ?_
      refine ih p.1 p.2 ?_ z
      exact Nat.lt_of_lt_of_le hgt
        (hybridQueryImpl_counter_mono (G := G) (P := P) pk b realUntil t st p hp)

private lemma stepDDH_real_simulation_deferred
    (pk : P × P) (b : Bool) (k : ℕ)
    {α : Type} (a : OracleComp (elgamalAsymmEnc G P).IND_CPA_oracleSpec α) :
    ∀ (st : IND_CPA_HybridState (P := P)), st.2 ≤ k →
    ∀ z : α × IND_CPA_HybridState (P := P),
    Pr[= z | do
        let g₂ ← ($ᵗ G : ProbComp G)
        (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
          (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2)) a).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P)
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
          simp_rw [show ∀ g₂ : G,
              IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2) (Sum.inl tu) =
              IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b (k + 1)
                (Sum.inl tu) from fun _ => rfl]
          prob_swap_rw
          refine probOutput_bind_congr fun p hp => ?_
          have hst : p.2 = st := by
            simp only [IND_CPA_queryImpl_hybrid, QueryImpl.add_apply_inl,
              QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
              liftM, monadLift, StateT.instMonadLift] at hp
            rw [StateT.run_lift, mem_support_bind_iff] at hp
            obtain ⟨a, _, ha⟩ := hp
            rw [mem_support_pure_iff] at ha
            exact congrArg Prod.snd ha
          subst hst
          exact ih p.1 _ hle z
      | inr mm =>
          obtain ⟨m₁, m₂⟩ := mm
          rcases Nat.lt_or_eq_of_le hle with hlt | heq
          · have hq : ∀ g₂ : G,
                (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                  (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2) (Sum.inr (m₁, m₂))).run st =
                (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b (k + 1)
                  (Sum.inr (m₁, m₂))).run st := by
              intro g₂
              show (IND_CPA_stepDDHOracle (G := G) (P := P) pk b k
                (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2) (m₁, m₂)).run st =
                (IND_CPA_hybridChallengeOracle (G := G) (P := P) pk b
                  (k + 1) (m₁, m₂)).run st
              simp only [IND_CPA_stepDDHOracle, IND_CPA_hybridChallengeOracle,
                StateT.run_bind, StateT.run_get, pure_bind]
              rcases hcache : st.1 (m₁, m₂) with _ | c
              · simp only [if_pos hlt, if_pos (show st.2 < k + 1 by omega)]
              · simp only [StateT.run_pure]
            simp_rw [hq]
            prob_swap_rw
            refine probOutput_bind_congr fun p hp => ?_
            have hle' : p.2.2 ≤ k := by
              change p ∈ support ((IND_CPA_hybridChallengeOracle (G := G)
                (P := P) pk b (k + 1) (m₁, m₂)).run st) at hp
              revert hp
              rcases hcache : st.1 (m₁, m₂) with _ | c <;> intro hp
              · simp only [IND_CPA_hybridChallengeOracle, hcache,
                  StateT.run_bind, StateT.run_get, pure_bind] at hp
                rw [mem_support_iff] at hp
                rw [← mem_support_iff] at hp
                have hlift : ∀ (x : ProbComp (P × P)),
                    (liftM x : StateT (IND_CPA_HybridState (P := P))
                      ProbComp (P × P)).run st =
                    x >>= fun a => pure (a, st) := by
                  intro x
                  simp only [liftM, MonadLiftT.monadLift,
                    show ∀ (x : ProbComp (P × P)),
                        OracleComp.liftComp x unifSpec = x from
                      fun x => monadLift_eq_self x,
                    MonadLift.monadLift, StateT.run_lift]
                split_ifs at hp
                all_goals
                  simp only [StateT.run_bind, StateT.run_pure, pure_bind,
                    hlift, bind_assoc, support_bind, Set.mem_iUnion,
                    support_pure, Set.mem_singleton_iff] at hp
                  obtain ⟨ci, _, ⟨i, hi, hp⟩⟩ := hp
                  have hset : ∀ (s' : IND_CPA_HybridState (P := P)),
                      (set s' : StateT (IND_CPA_HybridState (P := P))
                        ProbComp PUnit).run st =
                      (pure (PUnit.unit, s') : ProbComp _) := fun _ => rfl
                  simp only [hset, support_pure,
                    Set.mem_singleton_iff] at hi
                  subst hi
                  simp only [hp]
                  omega
              · simp only [IND_CPA_hybridChallengeOracle, hcache,
                  StateT.run_bind, StateT.run_get, pure_bind,
                  StateT.run_pure, mem_support_pure_iff] at hp
                have := congrArg (fun x => x.2.2) hp
                simp at this
                omega
            exact ih p.1 p.2 hle' z
          · rcases hcache : st.1 (m₁, m₂) with _ | c
            · have hset : ∀ (s' : IND_CPA_HybridState (P := P)),
                  (set s' : StateT (IND_CPA_HybridState (P := P))
                    ProbComp PUnit).run st =
                  (pure (PUnit.unit, s') : ProbComp _) := fun _ => rfl
              have hstep : ∀ g₂ : G,
                  (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                    (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2) (Sum.inr (m₁, m₂))).run st =
                  (pure ((g₂ +ᵥ pk.1,
                      (if b = true then m₁ else m₂) * (g₂ +ᵥ pk.2)),
                    (st.1.cacheQuery (m₁, m₂) (g₂ +ᵥ pk.1,
                      (if b = true then m₁ else m₂) * (g₂ +ᵥ pk.2)),
                     st.2 + 1)) : ProbComp _) := by
                intro g₂
                show (IND_CPA_stepDDHOracle (G := G) (P := P) pk b k
                  (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2) (m₁, m₂)).run st = _
                simp only [IND_CPA_stepDDHOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache,
                  if_neg (show ¬ st.2 < k by omega),
                  if_pos heq, StateT.run_pure, hset]
              have hhybrid :
                  (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b (k + 1)
                    (Sum.inr (m₁, m₂))).run st =
                  (do let g ← ($ᵗ G : ProbComp G)
                      pure ((g +ᵥ pk.1,
                          (if b = true then m₁ else m₂) * (g +ᵥ pk.2)),
                        (st.1.cacheQuery (m₁, m₂) (g +ᵥ pk.1,
                          (if b = true then m₁ else m₂) * (g +ᵥ pk.2)),
                         st.2 + 1)) : ProbComp _) := by
                show (IND_CPA_hybridChallengeOracle (G := G) (P := P)
                  pk b (k + 1) (m₁, m₂)).run st = _
                simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache,
                  show st.2 < k + 1 by omega, ite_true]
                simp only [elgamalAsymmEnc]
                have hlift : ∀ (x : ProbComp (P × P)),
                    (liftM x : StateT (IND_CPA_HybridState (P := P))
                      ProbComp (P × P)).run st =
                    x >>= fun a => pure (a, st) := by
                  intro x
                  simp only [liftM, MonadLiftT.monadLift,
                    show ∀ (x : ProbComp (P × P)),
                        OracleComp.liftComp x unifSpec = x from
                      fun x => monadLift_eq_self x,
                    MonadLift.monadLift, StateT.run_lift]
                simp only [hlift, bind_assoc,
                  StateT.run_pure, pure_bind, hset]
              simp_rw [hstep, pure_bind]
              rw [hhybrid, bind_assoc]
              simp_rw [pure_bind]
              refine probOutput_bind_congr' ($ᵗ G : ProbComp G) z fun r => ?_
              exact simulateQ_stepDDH_probOutput_eq_hybrid_post_k (G := G)
                (P := P) pk b k (r +ᵥ pk.1) (r +ᵥ pk.2) (k + 1)
                (Or.inr rfl) (oa _) _ (by rw [heq]; omega) z
            · have hstep : ∀ g₂ : G,
                  (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                    (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2)
                    (Sum.inr (m₁, m₂))).run st =
                  (pure (c, st) : ProbComp _) := by
                intro g₂
                show (IND_CPA_stepDDHOracle (G := G) (P := P) pk b k
                  (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2) (m₁, m₂)).run st = _
                simp only [IND_CPA_stepDDHOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, StateT.run_pure]
              have hhybrid :
                  (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b (k + 1)
                    (Sum.inr (m₁, m₂))).run st =
                  (pure (c, st) : ProbComp _) := by
                show (IND_CPA_hybridChallengeOracle (G := G) (P := P)
                  pk b (k + 1) (m₁, m₂)).run st = _
                simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, StateT.run_pure]
              simp_rw [hstep, hhybrid, pure_bind]
              exact ih c st (by omega) z

private lemma stepDDH_rand_simulation_deferred
    (pk : P × P) (b : Bool) (k : ℕ)
    {α : Type} (a : OracleComp (elgamalAsymmEnc G P).IND_CPA_oracleSpec α) :
    ∀ (st : IND_CPA_HybridState (P := P)), st.2 ≤ k →
    ∀ z : α × IND_CPA_HybridState (P := P),
    Pr[= z | do
        let g₂ ← ($ᵗ G : ProbComp G)
        let y ← ($ᵗ P : ProbComp P)
        (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
          (g₂ +ᵥ pk.1) y) a).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P)
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
          simp_rw [show ∀ (g₂ : G) (y : P),
              IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                (g₂ +ᵥ pk.1) y (Sum.inl tu) =
              IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                (Sum.inl tu) from fun _ _ => rfl]
          have hswapY : ∀ g₂ : G,
              Pr[= z | do
                let y ← ($ᵗ P : ProbComp P)
                let p ← (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                  (Sum.inl tu)).run st
                (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                  (g₂ +ᵥ pk.1) y) (oa p.1)).run p.2] =
              Pr[= z | do
                let p ← (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                  (Sum.inl tu)).run st
                let y ← ($ᵗ P : ProbComp P)
                (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                  (g₂ +ᵥ pk.1) y) (oa p.1)).run p.2] := by
            intro g₂
            prob_swap
          have hswapGY :
              Pr[= z | do
                let g₂ ← ($ᵗ G : ProbComp G)
                let y ← ($ᵗ P : ProbComp P)
                let p ← (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                  (Sum.inl tu)).run st
                (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                  (g₂ +ᵥ pk.1) y) (oa p.1)).run p.2] =
              Pr[= z | do
                let g₂ ← ($ᵗ G : ProbComp G)
                let p ← (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                  (Sum.inl tu)).run st
                let y ← ($ᵗ P : ProbComp P)
                (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                  (g₂ +ᵥ pk.1) y) (oa p.1)).run p.2] := by
            refine probOutput_bind_congr' ($ᵗ G : ProbComp G) z ?_
            intro g₂
            exact hswapY g₂
          rw [hswapGY]
          prob_swap_rw
          refine probOutput_bind_congr fun p hp => ?_
          have hst : p.2 = st := by
            simp only [IND_CPA_queryImpl_hybrid, QueryImpl.add_apply_inl,
              QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
              liftM, monadLift, StateT.instMonadLift] at hp
            rw [StateT.run_lift, mem_support_bind_iff] at hp
            obtain ⟨a, _, ha⟩ := hp
            rw [mem_support_pure_iff] at ha
            exact congrArg Prod.snd ha
          subst hst
          exact ih p.1 _ hle z
      | inr mm =>
          obtain ⟨m₁, m₂⟩ := mm
          rcases Nat.lt_or_eq_of_le hle with hlt | heq
          · have hq : ∀ (g₂ : G) (y : P),
                (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                  (g₂ +ᵥ pk.1) y (Sum.inr (m₁, m₂))).run st =
                (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                  (Sum.inr (m₁, m₂))).run st := by
              intro g₂ y
              show (IND_CPA_stepDDHOracle (G := G) (P := P) pk b k
                (g₂ +ᵥ pk.1) y (m₁, m₂)).run st =
                (IND_CPA_hybridChallengeOracle (G := G) (P := P) pk b
                  k (m₁, m₂)).run st
              simp only [IND_CPA_stepDDHOracle, IND_CPA_hybridChallengeOracle,
                StateT.run_bind, StateT.run_get, pure_bind]
              rcases hcache : st.1 (m₁, m₂) with _ | c
              · simp only [if_pos hlt]
              · simp only [StateT.run_pure]
            simp_rw [hq]
            have hswapY : ∀ g₂ : G,
                Pr[= z | do
                  let y ← ($ᵗ P : ProbComp P)
                  let p ← (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                    (Sum.inr (m₁, m₂))).run st
                  (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                    (g₂ +ᵥ pk.1) y) (oa p.1)).run p.2] =
                Pr[= z | do
                  let p ← (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                    (Sum.inr (m₁, m₂))).run st
                  let y ← ($ᵗ P : ProbComp P)
                  (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                    (g₂ +ᵥ pk.1) y) (oa p.1)).run p.2] := by
              intro g₂
              prob_swap
            have hswapGY :
                Pr[= z | do
                  let g₂ ← ($ᵗ G : ProbComp G)
                  let y ← ($ᵗ P : ProbComp P)
                  let p ← (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                    (Sum.inr (m₁, m₂))).run st
                  (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                    (g₂ +ᵥ pk.1) y) (oa p.1)).run p.2] =
                Pr[= z | do
                  let g₂ ← ($ᵗ G : ProbComp G)
                  let p ← (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                    (Sum.inr (m₁, m₂))).run st
                  let y ← ($ᵗ P : ProbComp P)
                  (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                    (g₂ +ᵥ pk.1) y) (oa p.1)).run p.2] := by
              refine probOutput_bind_congr' ($ᵗ G : ProbComp G) z ?_
              intro g₂
              exact hswapY g₂
            rw [hswapGY]
            prob_swap_rw
            refine probOutput_bind_congr fun p hp => ?_
            have hle' : p.2.2 ≤ k := by
              change p ∈ support ((IND_CPA_hybridChallengeOracle (G := G)
                (P := P) pk b k (m₁, m₂)).run st) at hp
              revert hp
              rcases hcache : st.1 (m₁, m₂) with _ | c <;> intro hp
              · simp only [IND_CPA_hybridChallengeOracle, hcache,
                  StateT.run_bind, StateT.run_get, pure_bind] at hp
                rw [mem_support_iff] at hp
                rw [← mem_support_iff] at hp
                have hlift : ∀ (x : ProbComp (P × P)),
                    (liftM x : StateT (IND_CPA_HybridState (P := P))
                      ProbComp (P × P)).run st =
                    x >>= fun a => pure (a, st) := by
                  intro x
                  simp only [liftM, MonadLiftT.monadLift,
                    show ∀ (x : ProbComp (P × P)),
                        OracleComp.liftComp x unifSpec = x from
                      fun x => monadLift_eq_self x,
                    MonadLift.monadLift, StateT.run_lift]
                split_ifs at hp
                all_goals
                  simp only [StateT.run_bind, StateT.run_pure, pure_bind,
                    hlift, bind_assoc, support_bind, Set.mem_iUnion,
                    support_pure, Set.mem_singleton_iff] at hp
                  obtain ⟨ci, _, ⟨i, hi, hp⟩⟩ := hp
                  have hset : ∀ (s' : IND_CPA_HybridState (P := P)),
                      (set s' : StateT (IND_CPA_HybridState (P := P))
                        ProbComp PUnit).run st =
                      (pure (PUnit.unit, s') : ProbComp _) := fun _ => rfl
                  simp only [hset, support_pure,
                    Set.mem_singleton_iff] at hi
                  subst hi
                  simp only [hp]
                  omega
              · simp only [IND_CPA_hybridChallengeOracle, hcache,
                  StateT.run_bind, StateT.run_get, pure_bind,
                  StateT.run_pure, mem_support_pure_iff] at hp
                have := congrArg (fun x => x.2.2) hp
                simp at this
                omega
            exact ih p.1 p.2 hle' z
          · rcases hcache : st.1 (m₁, m₂) with _ | c
            · have hset : ∀ (s' : IND_CPA_HybridState (P := P)),
                  (set s' : StateT (IND_CPA_HybridState (P := P))
                    ProbComp PUnit).run st =
                  (pure (PUnit.unit, s') : ProbComp _) := fun _ => rfl
              have hstep : ∀ (g₂ : G) (y : P),
                  (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                    (g₂ +ᵥ pk.1) y (Sum.inr (m₁, m₂))).run st =
                  (pure ((g₂ +ᵥ pk.1,
                      (if b = true then m₁ else m₂) * y),
                    (st.1.cacheQuery (m₁, m₂) (g₂ +ᵥ pk.1,
                      (if b = true then m₁ else m₂) * y),
                     st.2 + 1)) : ProbComp _) := by
                intro g₂ y
                show (IND_CPA_stepDDHOracle (G := G) (P := P) pk b k
                  (g₂ +ᵥ pk.1) y (m₁, m₂)).run st = _
                simp only [IND_CPA_stepDDHOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache,
                  if_neg (show ¬ st.2 < k by omega),
                  if_pos heq, StateT.run_pure, hset]
              have hhybrid :
                  (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                    (Sum.inr (m₁, m₂))).run st =
                  (do let g ← ($ᵗ G : ProbComp G)
                      let y ← ($ᵗ P : ProbComp P)
                      pure ((g +ᵥ pk.1,
                          (if b = true then m₁ else m₂) * y),
                        (st.1.cacheQuery (m₁, m₂) (g +ᵥ pk.1,
                          (if b = true then m₁ else m₂) * y),
                         st.2 + 1)) : ProbComp _) := by
                show (IND_CPA_hybridChallengeOracle (G := G) (P := P)
                  pk b k (m₁, m₂)).run st = _
                simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache,
                  if_neg (show ¬ st.2 < k by omega)]
                simp only [randomMaskedCipher]
                have hlift : ∀ (x : ProbComp (P × P)),
                    (liftM x : StateT (IND_CPA_HybridState (P := P))
                      ProbComp (P × P)).run st =
                    x >>= fun a => pure (a, st) := by
                  intro x
                  simp only [liftM, MonadLiftT.monadLift,
                    show ∀ (x : ProbComp (P × P)),
                        OracleComp.liftComp x unifSpec = x from
                      fun x => monadLift_eq_self x,
                    MonadLift.monadLift, StateT.run_lift]
                simp only [hlift, bind_assoc,
                  StateT.run_pure, pure_bind, hset]
              simp_rw [hstep, pure_bind]
              rw [hhybrid]
              simp_rw [bind_assoc, pure_bind]
              refine probOutput_bind_congr' ($ᵗ G : ProbComp G) z fun r => ?_
              refine probOutput_bind_congr' ($ᵗ P : ProbComp P) z fun y => ?_
              exact simulateQ_stepDDH_probOutput_eq_hybrid_post_k (G := G)
                (P := P) pk b k (r +ᵥ pk.1) y k
                (Or.inl rfl) (oa ((r +ᵥ pk.1, (if b = true then m₁ else m₂) * y))) _
                (by rw [heq]; omega) z
            · have hstep : ∀ (g₂ : G) (y : P),
                  (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
                    (g₂ +ᵥ pk.1) y (Sum.inr (m₁, m₂))).run st =
                  (pure (c, st) : ProbComp _) := by
                intro g₂ y
                show (IND_CPA_stepDDHOracle (G := G) (P := P) pk b k
                  (g₂ +ᵥ pk.1) y (m₁, m₂)).run st = _
                simp only [IND_CPA_stepDDHOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, StateT.run_pure]
              have hhybrid :
                  (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k
                    (Sum.inr (m₁, m₂))).run st =
                  (pure (c, st) : ProbComp _) := by
                show (IND_CPA_hybridChallengeOracle (G := G) (P := P)
                  pk b k (m₁, m₂)).run st = _
                simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind,
                  StateT.run_get, pure_bind, hcache, StateT.run_pure]
              simp_rw [hstep, hhybrid, pure_bind]
              exact ih c st hle z

set_option maxHeartbeats 400000 in
private lemma stepDDH_realBranch_probOutput_eq
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (k : ℕ) :
    Pr[= true | stepDDH_realBranchGame (G := G) (P := P) adversary k] =
    Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary (k + 1)] := by
  have hswap₁ :
      Pr[= true | stepDDH_realBranchGame (G := G) (P := P) adversary k] =
      Pr[= true | do
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let b ← $ᵗ Bool
        let g₂ ← $ᵗ G
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] := by
    unfold stepDDH_realBranchGame stepDDH_realBranchCore
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun x => ?_
    congr 1
    prob_swap
  have hswap₂ :
      Pr[= true | do
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let b ← $ᵗ Bool
        let g₂ ← $ᵗ G
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] =
      Pr[= true | do
        let x ← $ᵗ P
        let b ← $ᵗ Bool
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] := by
    prob_swap
  have hswap₃ :
      Pr[= true | do
        let x ← $ᵗ P
        let b ← $ᵗ Bool
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] =
      Pr[= true | do
        let b ← $ᵗ Bool
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] := by
    prob_swap
  have hmain :
      Pr[= true | do
        let b ← $ᵗ Bool
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] =
      Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary (k + 1)] := by
    simp [IND_CPA_HybridGame, elgamalAsymmEnc, bind_assoc]
    refine probOutput_bind_congr' ($ᵗ Bool : ProbComp Bool) true ?_
    intro b
    refine probOutput_bind_congr' ($ᵗ P : ProbComp P) true ?_
    intro x
    refine probOutput_bind_congr' ($ᵗ G : ProbComp G) true ?_
    intro g₁
    let pk : P × P := (x, g₁ +ᵥ x)
    have hsim_run :
        evalDist (do
          let g₂ ← ($ᵗ G : ProbComp G)
          (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
            (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2)) (adversary pk)).run (∅, 0) :
            ProbComp (Bool × IND_CPA_HybridState (P := P))) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b (k + 1))
          (adversary pk)).run (∅, 0)) := by
      apply evalDist_ext
      intro z
      simpa [pk] using
        stepDDH_real_simulation_deferred (G := G) (P := P) (pk := pk) (b := b) (k := k)
          (a := adversary pk) (st := (∅, 0)) (by omega) (z := z)
    have hsim :
        evalDist (do
          let g₂ ← ($ᵗ G : ProbComp G)
          (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
            (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2)) (adversary pk)).run' (∅, 0) : ProbComp Bool) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b (k + 1))
          (adversary pk)).run' (∅, 0)) := by
      simp only [StateT.run']
      simpa [evalDist_map] using congrArg (fun p => Prod.fst <$> p) hsim_run
    have hfinal :
        evalDist ((do
          let g₂ ← ($ᵗ G : ProbComp G)
          let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
            (g₂ +ᵥ pk.1) (g₂ +ᵥ pk.2)) (adversary pk)).run' (∅, 0)
          pure (b == b')) : ProbComp Bool) =
        evalDist ((do
          let b' ← (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b (k + 1))
            (adversary pk)).run' (∅, 0)
          pure (b == b')) : ProbComp Bool) := by
      simpa [evalDist_bind] using
        congrArg (fun p => p >>= fun t => evalDist (pure (b == t) : ProbComp Bool)) hsim
    simpa [IND_CPA_HybridGame, elgamalAsymmEnc, bind_assoc, pk] using
      (evalDist_ext_iff.mp hfinal) true
  calc
    Pr[= true | stepDDH_realBranchGame (G := G) (P := P) adversary k]
      = Pr[= true | do
          let x ← $ᵗ P
          let g₁ ← $ᵗ G
          let b ← $ᵗ Bool
          let g₂ ← $ᵗ G
          let pk : P × P := (x, g₁ +ᵥ x)
          let x₂ : P := g₂ +ᵥ x
          let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
          let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
            (adversary pk)).run' (∅, 0)
          pure (b == b')] := hswap₁
    _ = Pr[= true | do
          let x ← $ᵗ P
          let b ← $ᵗ Bool
          let g₁ ← $ᵗ G
          let g₂ ← $ᵗ G
          let pk : P × P := (x, g₁ +ᵥ x)
          let x₂ : P := g₂ +ᵥ x
          let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
          let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
            (adversary pk)).run' (∅, 0)
          pure (b == b')] := hswap₂
    _ = Pr[= true | do
          let b ← $ᵗ Bool
          let x ← $ᵗ P
          let g₁ ← $ᵗ G
          let g₂ ← $ᵗ G
          let pk : P × P := (x, g₁ +ᵥ x)
          let x₂ : P := g₂ +ᵥ x
          let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
          let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
            (adversary pk)).run' (∅, 0)
          pure (b == b')] := hswap₃
    _ = Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary (k + 1)] := hmain

set_option maxHeartbeats 800000 in
private lemma stepDDH_randBranch_probOutput_eq
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (k : ℕ) :
    Pr[= true | stepDDH_randBranchGame (G := G) (P := P) adversary k] =
    Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary k] := by
  have hswap₀ :
      Pr[= true | stepDDH_randBranchGame (G := G) (P := P) adversary k] =
      Pr[= true | do
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let b ← $ᵗ Bool
        let y ← $ᵗ P
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] := by
    unfold stepDDH_randBranchGame stepDDH_randBranchCore
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun x => ?_
    congr 1
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun g₁ => ?_
    congr 1
    prob_swap
  have hswap₁ :
      Pr[= true | do
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let b ← $ᵗ Bool
        let y ← $ᵗ P
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] =
      Pr[= true | do
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let b ← $ᵗ Bool
        let g₂ ← $ᵗ G
        let y ← $ᵗ P
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] := by
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun x => ?_
    congr 1
    prob_swap
  have hswap₂ :
      Pr[= true | do
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let b ← $ᵗ Bool
        let g₂ ← $ᵗ G
        let y ← $ᵗ P
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] =
      Pr[= true | do
        let x ← $ᵗ P
        let b ← $ᵗ Bool
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let y ← $ᵗ P
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] := by
    prob_swap
  have hswap₃ :
      Pr[= true | do
        let x ← $ᵗ P
        let b ← $ᵗ Bool
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let y ← $ᵗ P
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] =
      Pr[= true | do
        let b ← $ᵗ Bool
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let y ← $ᵗ P
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] := by
    prob_swap
  have hmain :
      Pr[= true | do
        let b ← $ᵗ Bool
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let y ← $ᵗ P
        let pk : P × P := (x, g₁ +ᵥ x)
        let x₂ : P := g₂ +ᵥ x
        let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
          (adversary pk)).run' (∅, 0)
        pure (b == b')] =
      Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary k] := by
    simp [IND_CPA_HybridGame, elgamalAsymmEnc, bind_assoc]
    refine probOutput_bind_congr' ($ᵗ Bool : ProbComp Bool) true ?_
    intro b
    refine probOutput_bind_congr' ($ᵗ P : ProbComp P) true ?_
    intro x
    refine probOutput_bind_congr' ($ᵗ G : ProbComp G) true ?_
    intro g₁
    let pk : P × P := (x, g₁ +ᵥ x)
    have hsim_run :
        evalDist (do
          let g₂ ← ($ᵗ G : ProbComp G)
          let y ← ($ᵗ P : ProbComp P)
          (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
            (g₂ +ᵥ pk.1) y) (adversary pk)).run (∅, 0) :
            ProbComp (Bool × IND_CPA_HybridState (P := P))) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k)
          (adversary pk)).run (∅, 0)) := by
      apply evalDist_ext
      intro z
      simpa [pk] using
        stepDDH_rand_simulation_deferred (G := G) (P := P) (pk := pk) (b := b) (k := k)
          (a := adversary pk) (st := (∅, 0)) (by omega) (z := z)
    have hsim :
        evalDist (do
          let g₂ ← ($ᵗ G : ProbComp G)
          let y ← ($ᵗ P : ProbComp P)
          (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
            (g₂ +ᵥ pk.1) y) (adversary pk)).run' (∅, 0) : ProbComp Bool) =
        evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k)
          (adversary pk)).run' (∅, 0)) := by
      simp only [StateT.run']
      simpa [evalDist_map] using congrArg (fun p => Prod.fst <$> p) hsim_run
    have hfinal :
        evalDist ((do
          let g₂ ← ($ᵗ G : ProbComp G)
          let y ← ($ᵗ P : ProbComp P)
          let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k
            (g₂ +ᵥ pk.1) y) (adversary pk)).run' (∅, 0)
          pure (b == b')) : ProbComp Bool) =
        evalDist ((do
          let b' ← (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b k)
            (adversary pk)).run' (∅, 0)
          pure (b == b')) : ProbComp Bool) := by
      simpa [evalDist_bind] using
        congrArg (fun p => p >>= fun t => evalDist (pure (b == t) : ProbComp Bool)) hsim
    simpa [IND_CPA_HybridGame, elgamalAsymmEnc, bind_assoc, pk] using
      (evalDist_ext_iff.mp hfinal) true
  calc
    Pr[= true | stepDDH_randBranchGame (G := G) (P := P) adversary k]
      = Pr[= true | do
          let x ← $ᵗ P
          let g₁ ← $ᵗ G
          let g₂ ← $ᵗ G
          let b ← $ᵗ Bool
          let y ← $ᵗ P
          let pk : P × P := (x, g₁ +ᵥ x)
          let x₂ : P := g₂ +ᵥ x
          let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
            (adversary pk)).run' (∅, 0)
          pure (b == b')] := hswap₀
    _ = Pr[= true | do
          let x ← $ᵗ P
          let g₁ ← $ᵗ G
          let b ← $ᵗ Bool
          let g₂ ← $ᵗ G
          let y ← $ᵗ P
          let pk : P × P := (x, g₁ +ᵥ x)
          let x₂ : P := g₂ +ᵥ x
          let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
            (adversary pk)).run' (∅, 0)
          pure (b == b')] := hswap₁
    _ = Pr[= true | do
          let x ← $ᵗ P
          let b ← $ᵗ Bool
          let g₁ ← $ᵗ G
          let g₂ ← $ᵗ G
          let y ← $ᵗ P
          let pk : P × P := (x, g₁ +ᵥ x)
          let x₂ : P := g₂ +ᵥ x
          let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
            (adversary pk)).run' (∅, 0)
          pure (b == b')] := hswap₂
    _ = Pr[= true | do
          let b ← $ᵗ Bool
          let x ← $ᵗ P
          let g₁ ← $ᵗ G
          let g₂ ← $ᵗ G
          let y ← $ᵗ P
          let pk : P × P := (x, g₁ +ᵥ x)
          let x₂ : P := g₂ +ᵥ x
          let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
            (adversary pk)).run' (∅, 0)
          pure (b == b')] := hswap₃
    _ = Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary k] := hmain

set_option maxHeartbeats 400000 in
private lemma ddhExp_stepDDH_eq_mixture
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (k : ℕ) :
    Pr[= true | DiffieHellman.ddhExp (IND_CPA_stepDDHReduction (G := G) (P := P) adversary k)] =
    Pr[= true | do
      let d ← ($ᵗ Bool : ProbComp Bool)
      let z ← if d then
        stepDDH_realBranchGame (G := G) (P := P) adversary k
      else
        stepDDH_randBranchGame (G := G) (P := P) adversary k
      pure (d == z)] := by
  have hrepr :
      Pr[= true | DiffieHellman.ddhExp (IND_CPA_stepDDHReduction (G := G) (P := P) adversary k)] =
      Pr[= true | do
        let x ← $ᵗ P; let g₁ ← $ᵗ G; let g₂ ← $ᵗ G; let d ← $ᵗ Bool
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] := by
    simp [DiffieHellman.ddhExp, parallelTesting_experiment, IND_CPA_stepDDHReduction,
      stepDDH_realBranchCore, stepDDH_randBranchCore]
  have hswap₁ :
      Pr[= true | do
        let x ← $ᵗ P; let g₁ ← $ᵗ G; let g₂ ← $ᵗ G; let d ← $ᵗ Bool
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] =
      Pr[= true | do
        let x ← $ᵗ P; let g₁ ← $ᵗ G; let d ← ($ᵗ Bool : ProbComp Bool)
        let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] := by
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun x => ?_
    congr 1
    prob_swap
  have hswap₂ :
      Pr[= true | do
        let x ← $ᵗ P; let g₁ ← $ᵗ G; let d ← ($ᵗ Bool : ProbComp Bool)
        let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] =
      Pr[= true | do
        let x ← $ᵗ P; let d ← ($ᵗ Bool : ProbComp Bool)
        let g₁ ← $ᵗ G; let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] := by
    prob_swap
  have hswap₃ :
      Pr[= true | do
        let x ← $ᵗ P; let d ← ($ᵗ Bool : ProbComp Bool)
        let g₁ ← $ᵗ G; let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] =
      Pr[= true | do
        let d ← ($ᵗ Bool : ProbComp Bool)
        let x ← $ᵗ P; let g₁ ← $ᵗ G; let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] := by
    prob_swap
  have hfold :
      Pr[= true | do
        let d ← ($ᵗ Bool : ProbComp Bool)
        let x ← $ᵗ P; let g₁ ← $ᵗ G; let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] =
      Pr[= true | do
        let d ← ($ᵗ Bool : ProbComp Bool)
        let z ← if d then
          stepDDH_realBranchGame (G := G) (P := P) adversary k
        else
          stepDDH_randBranchGame (G := G) (P := P) adversary k
        pure (d == z)] := by
    refine probOutput_bind_congr' ($ᵗ Bool) true ?_
    intro d
    cases d <;>
      simp [stepDDH_realBranchGame, stepDDH_randBranchGame,
        map_eq_bind_pure_comp, bind_assoc]
  rw [hrepr, hswap₁, hswap₂, hswap₃, hfold]

private lemma ddhExp_stepDDHReduction_decomp_toReal
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (k : ℕ) :
    (Pr[= true |
      DiffieHellman.ddhExp (IND_CPA_stepDDHReduction (G := G) (P := P) adversary k)]).toReal
        - 1 / 2 =
    ((Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary (k + 1)]).toReal -
      (Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary k]).toReal) / 2 := by
  rw [ddhExp_stepDDH_eq_mixture (G := G) (P := P) adversary k]
  rw [ddh_decomp_two_games_toReal]
  rw [stepDDH_realBranch_probOutput_eq (G := G) (P := P) adversary k,
      stepDDH_randBranch_probOutput_eq (G := G) (P := P) adversary k]

lemma IND_CPA_stepDDH_hopBound
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) :
    |(Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary (k + 1)]).toReal -
      (Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary k]).toReal| ≤
      2 * |(Pr[= true |
          DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary k)]).toReal - 1 / 2| := by
  have h := ddhExp_stepDDHReduction_decomp_toReal (G := G) (P := P) adversary k
  have heq : (Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary (k + 1)]).toReal -
      (Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary k]).toReal =
      2 * ((Pr[= true |
          DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary k)]).toReal - 1 / 2) := by
    linarith
  rw [heq, abs_mul, abs_of_nonneg (by positivity)]

/-! ## 6. Bridging hybrid game to real game via query bound -/

/-- Always-real challenge oracle in the hybrid state monad. Identical to
`IND_CPA_hybridChallengeOracle` but without the counter-based branch — it always
performs real ElGamal encryption on cache misses. The counter is still incremented
(for structural compatibility) but never read. -/
private def IND_CPA_allRealChallengeOracle (pk : P × P) (b : Bool) :
    QueryImpl (P × P →ₒ P × P)
      (StateT (IND_CPA_HybridState (P := P)) ProbComp) := fun mm => do
  let st ← get
  match st.1 mm with
  | some c => return c
  | none =>
      let msg : P := if b then mm.1 else mm.2
      let c ← (elgamalAsymmEnc G P).encrypt pk msg
      let cache' := st.1.cacheQuery mm c
      set (cache', st.2 + 1)
      return c

/-- Full always-real oracle in the hybrid state monad. -/
private def IND_CPA_queryImpl_allReal (pk : P × P) (b : Bool) :
    QueryImpl (elgamalAsymmEnc G P).IND_CPA_oracleSpec
      (StateT (IND_CPA_HybridState (P := P)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (IND_CPA_HybridState (P := P)) ProbComp) +
    IND_CPA_allRealChallengeOracle (G := G) (P := P) pk b

/-- The always-real oracle agrees with the hybrid oracle when the counter is below
`realUntil`. Both are identical computations on such states. -/
private lemma allReal_eq_hybrid_on_bounded
    (pk : P × P) (b : Bool) (realUntil : ℕ)
    (t : (elgamalAsymmEnc G P).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (P := P)) (hlt : st.2 < realUntil) :
    (IND_CPA_queryImpl_allReal (G := G) (P := P) pk b t).run st =
    (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b realUntil t).run st := by
  cases t with
  | inl _ => rfl
  | inr mm =>
      simp only [IND_CPA_queryImpl_allReal, IND_CPA_queryImpl_hybrid]
      show (IND_CPA_allRealChallengeOracle (G := G) (P := P) pk b mm).run st =
        (IND_CPA_hybridChallengeOracle (G := G) (P := P) pk b realUntil mm).run st
      simp only [IND_CPA_allRealChallengeOracle, IND_CPA_hybridChallengeOracle,
        StateT.run_bind, StateT.run_get, pure_bind]
      rcases hcache : st.1 mm with _ | c
      · simp only [if_pos hlt]
      · simp only [StateT.run_pure]

/-- The counter in the always-real oracle is monotonically non-decreasing. -/
private lemma allReal_counter_mono
    (pk : P × P) (b : Bool)
    (t : (elgamalAsymmEnc G P).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (P := P))
    (p : (elgamalAsymmEnc G P).IND_CPA_oracleSpec.Range t × IND_CPA_HybridState (P := P))
    (hp : p ∈ support ((IND_CPA_queryImpl_allReal (G := G) (P := P) pk b t).run st)) :
    st.2 ≤ p.2.2 := by
  have := hybridQueryImpl_counter_mono (G := G) (P := P) pk b (st.2 + 1)
    t st (p := p)
  rw [← allReal_eq_hybrid_on_bounded pk b (st.2 + 1) t st (by omega)] at this
  exact this hp

/-- A single `allReal` oracle step can increase the counter by at most one. -/
private lemma allReal_counter_le_succ
    (pk : P × P) (b : Bool)
    (t : (elgamalAsymmEnc G P).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (P := P))
    (p : (elgamalAsymmEnc G P).IND_CPA_oracleSpec.Range t × IND_CPA_HybridState (P := P))
    (hp : p ∈ support ((IND_CPA_queryImpl_allReal (G := G) (P := P) pk b t).run st)) :
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
      change p ∈ support ((IND_CPA_allRealChallengeOracle (G := G) (P := P) pk b mm).run st) at hp
      revert hp
      rcases hcache : st.1 mm with _ | c <;> intro hp
      · simp only [IND_CPA_allRealChallengeOracle, hcache,
          StateT.run_bind, StateT.run_get, pure_bind] at hp
        rw [mem_support_iff] at hp
        rw [← mem_support_iff] at hp
        have hlift : ∀ (x : ProbComp (P × P)),
            (liftM x : StateT (IND_CPA_HybridState (P := P)) ProbComp (P × P)).run st =
            x >>= fun a => pure (a, st) := by
          intro x
          simp only [liftM, MonadLiftT.monadLift,
            show ∀ (x : ProbComp (P × P)),
                OracleComp.liftComp x unifSpec = x from
              fun x => monadLift_eq_self x,
            MonadLift.monadLift, StateT.run_lift]
        simp only [StateT.run_pure, pure_bind, hlift, bind_assoc,
          support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hp
        obtain ⟨c, _, ⟨i, hi, hp⟩⟩ := hp
        have hset : ∀ (s' : IND_CPA_HybridState (P := P)),
            (set s' : StateT (IND_CPA_HybridState (P := P)) ProbComp PUnit).run st =
            (pure (PUnit.unit, s') : ProbComp _) := fun _ => rfl
        simp only [hset, support_pure, Set.mem_singleton_iff] at hi
        subst hi
        simp only [hp]
        omega
      · simp only [IND_CPA_allRealChallengeOracle, hcache,
          StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hp
        have := congrArg (fun x => x.2.2) hp
        simp at this
        omega

/-- Invariant simulation: `hybrid q` and `allReal` produce the same `run` distribution
on states where the counter plus remaining budget is at most `q`. -/
private lemma hybrid_q_probOutput_eq_allReal
    (pk : P × P) (b : Bool) (q : ℕ)
    {α : Type} (comp : OracleComp (elgamalAsymmEnc G P).IND_CPA_oracleSpec α)
    (budget : ℕ)
    (hbound : comp.IsQueryBound budget
      (fun t n => match t with | .inl _ => True | .inr _ => 0 < n)
      (fun t n => match t with | .inl _ => n | .inr _ => n - 1)) :
    ∀ (st : IND_CPA_HybridState (P := P)), st.2 + budget ≤ q →
    ∀ z : α × IND_CPA_HybridState (P := P),
    Pr[= z | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b q) comp).run st] =
    Pr[= z | (simulateQ (IND_CPA_queryImpl_allReal (G := G) (P := P) pk b) comp).run st] := by
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
          refine probOutput_bind_congr fun p hp => ?_
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
          have hquery := allReal_eq_hybrid_on_bounded (G := G) (P := P) pk b q (Sum.inr mm) st hlt
          rw [← hquery]
          refine probOutput_bind_congr fun p hp => ?_
          have hle' : p.2.2 + (budget - 1) ≤ q := by
            have hsucc := allReal_counter_le_succ (G := G) (P := P)
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
    (pk : P × P) (b : Bool)
    (t : (elgamalAsymmEnc G P).IND_CPA_oracleSpec.Domain)
    (st : IND_CPA_HybridState (P := P)) :
    Prod.map id Prod.fst <$>
      (IND_CPA_queryImpl_allReal (G := G) (P := P) pk b t).run st =
    (((elgamalAsymmEnc G P).IND_CPA_queryImpl' pk b) t).run st.1 := by
  rcases st with ⟨cache, n⟩
  cases t with
  | inl tu =>
      simp [IND_CPA_queryImpl_allReal, AsymmEncAlg.IND_CPA_queryImpl']
  | inr mm =>
      rcases hcache : cache mm with _ | c
      · have hlift : ∀ (x : ProbComp (P × P)),
            (liftM x : StateT (IND_CPA_HybridState (P := P)) ProbComp (P × P)).run (cache, n) =
            x >>= fun a => pure (a, (cache, n)) := by
          intro x
          simp only [liftM, MonadLiftT.monadLift,
            show ∀ (x : ProbComp (P × P)),
                OracleComp.liftComp x unifSpec = x from
              fun x => monadLift_eq_self x,
            MonadLift.monadLift, StateT.run_lift]
        have hallReal :
            Prod.map id Prod.fst <$>
              (IND_CPA_allRealChallengeOracle (G := G) (P := P) pk b mm).run (cache, n) =
            (do
              let c ← (elgamalAsymmEnc G P).encrypt pk (if b then mm.1 else mm.2)
              pure (c, cache.cacheQuery mm c) : ProbComp _) := by
          simp only [IND_CPA_allRealChallengeOracle, hcache,
            StateT.run_bind, StateT.run_get, pure_bind, hlift, bind_assoc,
            StateT.run_pure]
          rw [map_bind]
          refine bind_congr fun c => ?_
          simp
        have hreal :
            (((elgamalAsymmEnc G P).IND_CPA_queryImpl' pk b) (Sum.inr mm)).run cache =
            (do
              let c ← (elgamalAsymmEnc G P).encrypt pk (if b then mm.1 else mm.2)
              pure (c, cache.cacheQuery mm c) : ProbComp _) := by
          simp [AsymmEncAlg.IND_CPA_queryImpl', QueryImpl.withCaching_apply, hcache,
            StateT.run_bind, StateT.run_get, pure_bind]
        simpa [IND_CPA_queryImpl_allReal] using hallReal.trans hreal.symm
      · simp [IND_CPA_queryImpl_allReal, IND_CPA_allRealChallengeOracle,
          AsymmEncAlg.IND_CPA_queryImpl', QueryImpl.withCaching_apply, hcache,
          StateT.run_bind, StateT.run_get, pure_bind]

/-- State-projection simulation: `allReal` projected to `(result, cache)` has the same
`evalDist` as the real IND-CPA oracle.

This uses the fact that the counter in `allReal` is never read, so it doesn't affect the
output distribution when projected away. -/
private lemma allReal_evalDist_proj_eq_real
    (pk : P × P) (b : Bool)
    {α : Type} (comp : OracleComp (elgamalAsymmEnc G P).IND_CPA_oracleSpec α)
    (cache : IND_CPA_LRCache (P := P)) (n : ℕ) :
    evalDist (Prod.map id Prod.fst <$>
      (simulateQ (IND_CPA_queryImpl_allReal (G := G) (P := P) pk b) comp).run (cache, n)) =
    evalDist ((simulateQ ((elgamalAsymmEnc G P).IND_CPA_queryImpl' pk b) comp).run cache) := by
  simpa using congrArg evalDist
    (proj_map_run_simulateQ_eq
      (impl₁ := IND_CPA_queryImpl_allReal (G := G) (P := P) pk b)
      (impl₂ := (elgamalAsymmEnc G P).IND_CPA_queryImpl' pk b)
      (proj := Prod.fst)
      (hproj := allReal_queryImpl_proj_eq_real (G := G) (P := P) pk b)
      comp (cache, n))

/-- Combining projection and invariant: `run'` of hybrid-q equals `run'` of real. -/
private lemma hybrid_q_run'_evalDist_eq_real
    (pk : P × P) (b : Bool) (q : ℕ)
    {α : Type} (comp : OracleComp (elgamalAsymmEnc G P).IND_CPA_oracleSpec α)
    (budget : ℕ)
    (hbound : comp.IsQueryBound budget
      (fun t n => match t with | .inl _ => True | .inr _ => 0 < n)
      (fun t n => match t with | .inl _ => n | .inr _ => n - 1))
    (cache : IND_CPA_LRCache (P := P)) (n : ℕ) (hn : n + budget ≤ q) :
    evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b q)
      comp).run' (cache, n)) =
    evalDist ((simulateQ ((elgamalAsymmEnc G P).IND_CPA_queryImpl' pk b)
      comp).run' cache) := by
  have hrun :
      evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b q) comp).run
        (cache, n)) =
      evalDist ((simulateQ (IND_CPA_queryImpl_allReal (G := G) (P := P) pk b) comp).run
        (cache, n)) := by
    apply evalDist_ext
    intro z
    exact hybrid_q_probOutput_eq_allReal (G := G) (P := P) pk b q comp budget hbound
      (cache, n) hn z
  have hhybrid_run' :
      evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b q) comp).run'
        (cache, n)) =
      evalDist ((simulateQ (IND_CPA_queryImpl_allReal (G := G) (P := P) pk b) comp).run'
        (cache, n)) := by
    simp only [StateT.run']
    simpa [evalDist_map] using congrArg (fun p => Prod.fst <$> p) hrun
  have hrun_eq :
      Prod.map id Prod.fst <$>
        (simulateQ (IND_CPA_queryImpl_allReal (G := G) (P := P) pk b) comp).run (cache, n) =
      (simulateQ ((elgamalAsymmEnc G P).IND_CPA_queryImpl' pk b) comp).run cache :=
    proj_map_run_simulateQ_eq
      (impl₁ := IND_CPA_queryImpl_allReal (G := G) (P := P) pk b)
      (impl₂ := (elgamalAsymmEnc G P).IND_CPA_queryImpl' pk b)
      (proj := Prod.fst)
      (hproj := allReal_queryImpl_proj_eq_real (G := G) (P := P) pk b)
      comp (cache, n)
  have hallReal_run' :
      evalDist ((simulateQ (IND_CPA_queryImpl_allReal (G := G) (P := P) pk b) comp).run'
        (cache, n)) =
      evalDist ((simulateQ ((elgamalAsymmEnc G P).IND_CPA_queryImpl' pk b) comp).run'
        cache) := by
    have hrun'_eq :
        (simulateQ (IND_CPA_queryImpl_allReal (G := G) (P := P) pk b) comp).run' (cache, n) =
        (simulateQ ((elgamalAsymmEnc G P).IND_CPA_queryImpl' pk b) comp).run' cache := by
      have hmap := congrArg (fun p => Prod.fst <$> p) hrun_eq
      simpa [StateT.run', fst_map_prod_map] using hmap
    simpa using congrArg evalDist hrun'_eq
  exact hhybrid_run'.trans hallReal_run'

/-- The `q`-th hybrid game has the same winning probability as the actual IND-CPA experiment
when the adversary makes at most `q` total challenge queries. -/
theorem IND_CPA_HybridGame_q_eq_game
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (q : ℕ)
    (hq : adversary.MakesAtMostQueries q) :
    (Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary q]).toReal =
    (Pr[= true | IND_CPA_game adversary]).toReal := by
  congr 1
  have hinner : ∀ (pk : P × P) (b : Bool),
      evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b q)
        (adversary pk)).run' (∅, 0)) =
      evalDist ((simulateQ ((elgamalAsymmEnc G P).IND_CPA_queryImpl' pk b)
        (adversary pk)).run' ∅) :=
    fun pk b => hybrid_q_run'_evalDist_eq_real (G := G) (P := P)
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

/-- Detailed bound: IND-CPA advantage of ElGamal is at most the sum of per-hop DDH advantages.

The hypothesis `hstart` asserts that the `q`-th hybrid has the same winning probability as
the actual IND-CPA experiment. This holds for any adversary making at most `q` distinct fresh
LR oracle queries (see `IND_CPA_HybridGame_q_eq_game`). -/
theorem ElGamal_IND_CPA_bound_toReal
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (q : ℕ)
    (hstart : (Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary q]).toReal =
      (Pr[= true | IND_CPA_game adversary]).toReal) :
    ((elgamalAsymmEnc G P).IND_CPA_advantage adversary).toReal ≤
      Finset.sum (Finset.range q) (fun k =>
        2 * |(Pr[= true |
              DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary k)]).toReal - 1 / 2|) := by
  refine le_trans (AsymmEncAlg.IND_CPA_advantage_toReal_le_abs_signedAdvantageReal adversary) ?_
  refine le_trans
    (AsymmEncAlg.IND_CPA_advantage'_abs_le_sum_hybridDiff_abs
      adversary q (IND_CPA_HybridFamily (G := G) (P := P) adversary q)
      (by simp only [IND_CPA_HybridFamily_zero]; exact hstart)
      (by simp only [IND_CPA_HybridFamily_q];
          rw [IND_CPA_allRandomHalf]; simp)) ?_
  calc
    Finset.sum (Finset.range q) (fun i =>
          |(Pr[= true | IND_CPA_HybridFamily (G := G) (P := P) adversary q i]).toReal -
            (Pr[= true | IND_CPA_HybridFamily (G := G) (P := P) adversary q (i + 1)]).toReal|)
        ≤ Finset.sum (Finset.range q) (fun i =>
            2 * |(Pr[= true |
                  DiffieHellman.ddhExp
                    (IND_CPA_stepDDHReduction adversary (q - 1 - i))]).toReal - 1 / 2|) :=
          Finset.sum_le_sum fun i hi => by
            simp only [IND_CPA_HybridFamily]
            have hlt : i < q := Finset.mem_range.mp hi
            have h1 : q - 1 - i + 1 = q - i := by omega
            have h2 : q - (i + 1) = q - 1 - i := by omega
            rw [h2]
            have hb := IND_CPA_stepDDH_hopBound (G := G) (P := P) adversary (q - 1 - i)
            rwa [h1] at hb
    _ = Finset.sum (Finset.range q) (fun i =>
            2 * |(Pr[= true |
                  DiffieHellman.ddhExp
                    (IND_CPA_stepDDHReduction adversary i)]).toReal - 1 / 2|) :=
          Finset.sum_range_reflect
            (fun i => 2 * |(Pr[= true |
              DiffieHellman.ddhExp
                (IND_CPA_stepDDHReduction adversary i)]).toReal - 1 / 2|)
            q

/-- **Main theorem**: For any `q`-query IND-CPA adversary against ElGamal over a hard
homogeneous space, the IND-CPA advantage is at most `q * (2ε)` where `ε` bounds the DDH
advantage of each per-hop reduction.

The query bound is expressed via `MakesAtMostQueries`: the adversary issues at most `q` total
queries to the encryption oracle (fresh + cached), while uniform sampling is unrestricted. -/
theorem ElGamal_IND_CPA_le_q_mul_ddh
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (q : ℕ) (ε : ℝ)
    (hq : adversary.MakesAtMostQueries q)
    (hddh : ∀ k < q,
      |(Pr[= true | DiffieHellman.ddhExp
        (IND_CPA_stepDDHReduction adversary k)]).toReal - 1 / 2| ≤ ε) :
    ((elgamalAsymmEnc G P).IND_CPA_advantage adversary).toReal ≤ q * (2 * ε) := by
  refine le_trans (ElGamal_IND_CPA_bound_toReal adversary q
    (IND_CPA_HybridGame_q_eq_game adversary q hq)) ?_
  calc
    Finset.sum (Finset.range q) (fun k =>
          2 * |(Pr[= true |
                DiffieHellman.ddhExp
                  (IND_CPA_stepDDHReduction adversary k)]).toReal - 1 / 2|)
        ≤ Finset.sum (Finset.range q) (fun _ => 2 * ε) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact mul_le_mul_of_nonneg_left (hddh k (Finset.mem_range.mp hk)) (by positivity)
    _ = q * (2 * ε) := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

#print axioms ElGamal_IND_CPA_le_q_mul_ddh

end IND_CPA

end elgamalAsymmEnc
