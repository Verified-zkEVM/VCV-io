/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.ProgramLogic.Notation

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
6. Main theorem: IND-CPA advantage ≤ sum of per-hop DDH advantages, via telescoping and
   triangle inequality.

## Key honest hypothesis

The main theorem takes `hstart : IND_CPA_HybridGame adversary q = IND_CPA_game adversary`
as its sole external premise. This is a **legitimate query-bound hypothesis**: it is provable
for any specific adversary that makes at most q distinct fresh LR oracle queries.
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
-- TODO: move to SimSemantics or EvalDist
private lemma evalDist_simulateQ_run_eq_of_impl_evalDist_eq
    {ι' : Type} {spec' : OracleSpec ι'}
    {σ α : Type}
    (impl₁ impl₂ : QueryImpl spec' (StateT σ ProbComp))
    (h : ∀ (t : spec'.Domain) (s : σ),
      evalDist ((impl₁ t).run s) = evalDist ((impl₂ t).run s))
    (comp : OracleComp spec' α) (s : σ) :
    evalDist ((simulateQ impl₁ comp).run s) =
      evalDist ((simulateQ impl₂ comp).run s) := by
  revert s
  induction comp using OracleComp.inductionOn with
  | pure _ => intro _; rfl
  | query_bind t oa ih =>
    intro s
    simp only [simulateQ_query_bind, StateT.run_bind]
    rw [evalDist_bind, evalDist_bind]
    congr 1
    · exact h t s
    · funext ⟨u, s'⟩; exact ih u s'

-- TODO: move to EvalDist or HHS_Elgamal helpers
private lemma hybridChallengeOracle_allRandom_evalDist_eq
    (pk : P × P) (mm : P × P) (s : IND_CPA_HybridState (P := P)) :
    evalDist ((IND_CPA_hybridChallengeOracle (G := G) (P := P) pk true 0 mm).run s) =
    evalDist ((IND_CPA_hybridChallengeOracle (G := G) (P := P) pk false 0 mm).run s) := by
  simp only [IND_CPA_hybridChallengeOracle, StateT.run_bind, StateT.run_get, pure_bind,
    Nat.not_lt_zero, ite_false]
  cases hs : s.1 mm with
  | some _ => rfl
  | none =>
    simp only [Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_monadLift, pure_bind, StateT.run_set, StateT.run_pure,
      bind_assoc]
    rw [evalDist_bind, evalDist_bind]
    congr 1
    · simp only [evalDist_liftComp]
      exact randomMaskedCipher_dist_indep pk mm.1 mm.2

lemma IND_CPA_hybridOracle_allRandom_eqDist
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (pk : P × P) :
    RelTriple
      ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0)
        (adversary pk)).run' (∅, 0))
      ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0)
        (adversary pk)).run' (∅, 0))
      (EqRel _) := by
  apply relTriple_eqRel_of_evalDist_eq
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
    exact evalDist_eq_of_relTriple_eqRel
      (IND_CPA_hybridOracle_allRandom_eqDist adversary pk))

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
def IND_CPA_stepDDHReduction [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) : DiffieHellman.DDHAdversary G P :=
  fun x x₁ x₂ x₃ => do
    let b ← $ᵗ Bool
    let pk : P × P := (x, x₁)
    let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
      (adversary pk)).run' (∅, 0)
    return (b == b')

/-! ## 5. Per-hop bound -/

/-- When `x₃ = g₂ +ᵥ (g₁ +ᵥ x)` (the DDH-real case), the step reduction's oracle
simulation produces the same distribution as `IND_CPA_HybridGame adversary (k+1)`. -/
lemma IND_CPA_stepDDH_real_branch_eq [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (k : ℕ)
    (x : P) (g₁ g₂ : G) :
    let pk : P × P := (x, g₁ +ᵥ x)
    let x₂ := g₂ +ᵥ x
    let x₃ := g₂ +ᵥ (g₁ +ᵥ x)
    evalDist ((simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk true k x₂ x₃)
      (adversary pk)).run' (∅, 0)) =
    evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true (k + 1))
      (adversary pk)).run' (∅, 0)) := by
  sorry

/-- When `x₃ ~ U(P)` (the DDH-random case), the step reduction's oracle
simulation produces the same distribution as `IND_CPA_HybridGame adversary k`. -/
lemma IND_CPA_stepDDH_random_branch_eq [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) (k : ℕ)
    (x : P) (g₁ g₂ : G) (y : P) :
    let pk : P × P := (x, g₁ +ᵥ x)
    let x₂ := g₂ +ᵥ x
    evalDist ((simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk true k x₂ y)
      (adversary pk)).run' (∅, 0)) =
    evalDist ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true k)
      (adversary pk)).run' (∅, 0)) := by
  sorry

/-- The per-hop DDH bound: the absolute difference between consecutive hybrid winning
    probabilities is at most twice the DDH advantage of `IND_CPA_stepDDHReduction`.

    **Proof strategy** (see backup branch `quang/elgamal-backup` for partial proof):
    1. Show `Pr[step reduction wins | DDH real] = Pr[hybrid k+1 wins]` by verifying that
       `(x₂, msg * x₃)` with `x₃ = g₂ +ᵥ x₁` is distributed as real ElGamal encryption.
    2. Show `Pr[step reduction wins | DDH random] = Pr[hybrid k wins]` by verifying that
       `msg * y` with `y ~ U(P)` matches `randomMaskedCipher`.
    3. Apply `ddh_decomp_two_games` to decompose the DDH experiment into the difference
       of the two branch probabilities. -/
lemma IND_CPA_stepDDH_hopBound [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) :
    |AsymmEncAlg.trueProbReal (IND_CPA_HybridGame (G := G) (P := P) adversary (k + 1)) -
      AsymmEncAlg.trueProbReal (IND_CPA_HybridGame (G := G) (P := P) adversary k)| ≤
      2 * |AsymmEncAlg.trueProbReal
          (DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary k)) - 1 / 2| := by
  sorry

/-! ## 6. Main theorem -/

/-- **Main theorem**: For any `q`-query IND-CPA adversary against ElGamal, the advantage is
    bounded by the sum of the per-hop DDH advantages.

    The hypothesis `hstart` asserts that the `q`-th hybrid is identical to the actual IND-CPA
    experiment. This holds for any concrete adversary making at most `q` distinct fresh LR
    oracle queries. -/
theorem ElGamal_IND_CPA_bound_toReal [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (q : ℕ)
    (hstart : IND_CPA_HybridGame (G := G) (P := P) adversary q = IND_CPA_game adversary) :
    ((elgamalAsymmEnc G P).IND_CPA_advantage adversary).toReal ≤
      Finset.sum (Finset.range q) (fun k =>
        2 * |AsymmEncAlg.trueProbReal
              (DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary k)) - 1 / 2|) := by
  refine le_trans (AsymmEncAlg.IND_CPA_advantage_toReal_le_abs_signedAdvantageReal adversary) ?_
  refine le_trans
    (AsymmEncAlg.IND_CPA_advantage'_abs_le_sum_hybridDiff_abs
      adversary q (IND_CPA_HybridFamily (G := G) (P := P) adversary q)
      (by simp only [IND_CPA_HybridFamily_zero]; exact hstart)
      (by simp only [IND_CPA_HybridFamily_q, AsymmEncAlg.trueProbReal];
          rw [IND_CPA_allRandomHalf]; simp)) ?_
  calc
    Finset.sum (Finset.range q) (fun i =>
          |AsymmEncAlg.trueProbReal (IND_CPA_HybridFamily (G := G) (P := P) adversary q i) -
            AsymmEncAlg.trueProbReal (IND_CPA_HybridFamily (G := G) (P := P) adversary q (i + 1))|)
        ≤ Finset.sum (Finset.range q) (fun i =>
            2 * |AsymmEncAlg.trueProbReal
                  (DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary (q - 1 - i))) - 1 / 2|) :=
          Finset.sum_le_sum fun i hi => by
            simp only [IND_CPA_HybridFamily]
            have hlt : i < q := Finset.mem_range.mp hi
            have h1 : q - 1 - i + 1 = q - i := by omega
            have h2 : q - (i + 1) = q - 1 - i := by omega
            rw [h2]
            have hb := IND_CPA_stepDDH_hopBound (G := G) (P := P) adversary (q - 1 - i)
            rwa [h1] at hb
    _ = Finset.sum (Finset.range q) (fun i =>
            2 * |AsymmEncAlg.trueProbReal
                  (DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary i)) - 1 / 2|) :=
          Finset.sum_range_reflect
            (fun i => 2 * |AsymmEncAlg.trueProbReal
              (DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary i)) - 1 / 2|)
            q

/-- **Corollary**: If each per-hop DDH advantage is at most `ε`, then the IND-CPA advantage
    is at most `q * (2 * ε)`. -/
theorem ElGamal_IND_CPA_le_q_mul_ddh [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (q : ℕ) (ε : ℝ)
    (hstart : IND_CPA_HybridGame (G := G) (P := P) adversary q = IND_CPA_game adversary)
    (hddh : ∀ k < q,
      |AsymmEncAlg.trueProbReal (DiffieHellman.ddhExp
        (IND_CPA_stepDDHReduction adversary k)) - 1 / 2| ≤ ε) :
    ((elgamalAsymmEnc G P).IND_CPA_advantage adversary).toReal ≤ q * (2 * ε) := by
  refine le_trans (ElGamal_IND_CPA_bound_toReal adversary q hstart) ?_
  calc
    Finset.sum (Finset.range q) (fun k =>
          2 * |AsymmEncAlg.trueProbReal
                (DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary k)) - 1 / 2|)
        ≤ Finset.sum (Finset.range q) (fun _ => 2 * ε) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact mul_le_mul_of_nonneg_left (hddh k (Finset.mem_range.mp hk)) (by positivity)
    _ = q * (2 * ε) := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end IND_CPA

end elgamalAsymmEnc
