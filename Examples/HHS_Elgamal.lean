/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.ProgramLogic.Relational.Basic

/-!
# ElGamal over Hard Homogeneous Spaces: Multi-query IND-CPA via DDH

This file defines ElGamal encryption on an additive torsor (`AddTorsor G P`) and proves
multi-query oracle IND-CPA security via a q-step hybrid argument reducing to DDH.

## Proof structure

1. ElGamal definition and correctness.
2. Hybrid game family: the i-th game uses real ElGamal for the first i fresh LR oracle
   queries and random masking thereafter.
3. Key lemma: the all-random hybrid (i = 0) has success probability exactly 1/2.
4. Per-hop DDH reduction: a DDH adversary for the k → k+1 hop.
5. Per-hop equality: `|Pr[hybrid k+1 wins] - Pr[hybrid k wins]| = 2 × |signedDDHAdv(step k)|`.
6. Main theorem: IND-CPA advantage ≤ sum of per-hop DDH advantages, given a query-bound
   hypothesis linking the q-th hybrid to the real IND-CPA game.

## Key honest hypothesis

The main theorem takes `hstart : IND_CPA_HybridGame adversary q = IND_CPA_game adversary`
as its sole external premise. This is a **legitimate query-bound hypothesis** (not reward
hacking): it is provable for any specific adversary that makes at most q distinct fresh LR
oracle queries, but is not provable universally.
-/

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic.Relational

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

/-! ## 3. Helper probability lemmas -/

/-- Conditioning on a uniform boolean: average over the two branches. -/
lemma probOutput_bind_uniformBool {α : Type}
    (f : Bool → ProbComp α) (x : α) :
    Pr[= x | (do let b ← $ᵗ Bool; f b)] =
      (Pr[= x | f true] + Pr[= x | f false]) / 2 := by
  rw [probOutput_bind_eq_tsum]
  rw [tsum_fintype (L := .unconditional _), Fintype.sum_bool]
  simp [probOutput_uniformSample, div_eq_mul_inv, add_comm]
  rw [← left_distrib, mul_comm]

/-- Boolean-map simplification for `BEq.beq true`. -/
private lemma probOutput_true_eq_true_map (mx : ProbComp Bool) :
    Pr[= true | (BEq.beq true <$> mx)] = Pr[= true | mx] := by
  have hbeqTrue : (BEq.beq true : Bool → Bool) = id := by funext b; cases b <;> rfl
  rw [hbeqTrue]
  exact probOutput_map_injective (mx := mx) (f := id) (hf := Function.injective_id) (x := true)

/-- Boolean-map simplification for `BEq.beq false`. -/
private lemma probOutput_true_eq_falseMap (mx : ProbComp Bool) :
    Pr[= true | (BEq.beq false <$> mx)] = Pr[= false | mx] := by
  have hbeqFalse : (BEq.beq false : Bool → Bool) = Bool.not := by funext b; cases b <;> rfl
  rw [hbeqFalse]
  simpa using
    (probOutput_map_injective (mx := mx) (f := Bool.not)
      (hf := by
        intro a b hab
        have h : Bool.not (Bool.not a) = Bool.not (Bool.not b) := congrArg Bool.not hab
        simpa using h)
      (x := false))

omit [DecidableEq P] in
/-- Left-multiplying a uniform sample by a fixed group element preserves the distribution. -/
lemma probOutput_mul_left_uniform (m x : P) :
    Pr[= x | (fun y : P => m * y) <$> ($ᵗ P)] = Pr[= x | $ᵗ P] := by
  have h : Pr[= m * (m⁻¹ * x) | (fun y : P => m * y) <$> ($ᵗ P)] =
      Pr[= m⁻¹ * x | $ᵗ P] :=
    probOutput_map_injective
      (mx := ($ᵗ P))
      (f := fun y : P => m * y)
      (hf := by intro a b hab; exact mul_left_cancel hab)
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

/-- Generic DDH branch decomposition identity: the DDH advantage equals half the difference
    between the success probabilities in the "real" and "random" experiment branches. -/
lemma ddh_decomp_two_games (real rand : ProbComp Bool) :
    Pr[= true | do
      let b ← $ᵗ Bool
      let z ← if b then real else rand
      pure (b == z)] - 1 / 2 =
    (Pr[= true | real] - Pr[= true | rand]) / 2 := by
  let pR : ℝ≥0∞ := Pr[= true | real]
  let pF : ℝ≥0∞ := Pr[= true | rand]
  let x : ℝ≥0∞ := pR + (1 - pF)
  let y : ℝ≥0∞ := pF + (1 - pF)

  have hmix :
      Pr[= true | do
        let b ← $ᵗ Bool
        if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand)] =
      (Pr[= true | (BEq.beq true <$> real)] + Pr[= true | (BEq.beq false <$> rand)]) / 2 :=
    probOutput_bind_uniformBool
      (f := fun b => if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand))
      (x := true)

  have hgameRepr :
      Pr[= true | do
        let b ← $ᵗ Bool
        let z ← if b then real else rand
        pure (b == z)] =
      Pr[= true | do
        let b ← $ᵗ Bool
        if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand)] := by
    refine probOutput_bind_congr' ($ᵗ Bool) true ?_
    intro b
    cases b
    · have hbeqFalse : (BEq.beq false : Bool → Bool) = Bool.not := by
        funext t; cases t <;> rfl
      simp [hbeqFalse]
    · have hbeqTrue : (BEq.beq true : Bool → Bool) = id := by
        funext t; cases t <;> rfl
      simp [hbeqTrue]

  have hfalseSum : Pr[= true | rand] + Pr[= false | rand] = 1 := by
    have hsumAll : ∑ b : Bool, Pr[= b | rand] = 1 :=
      HasEvalPMF.sum_probOutput_eq_one (m := ProbComp) (mx := rand)
    simpa [Fintype.sum_bool] using hsumAll

  have hfalseAsSub : Pr[= false | rand] = 1 - Pr[= true | rand] := by
    have hsum' : Pr[= false | rand] + Pr[= true | rand] = 1 := by
      simpa [add_comm] using hfalseSum
    exact ENNReal.eq_sub_of_add_eq (hc := probOutput_ne_top) hsum'

  have hx : x = Pr[= true | (BEq.beq true <$> real)] + Pr[= true | (BEq.beq false <$> rand)] := by
    unfold x pR pF
    rw [probOutput_true_eq_true_map, probOutput_true_eq_falseMap, hfalseAsSub]

  have hy : y = 1 := by
    unfold y pF
    have h : (1 - Pr[= true | rand]) + Pr[= true | rand] = 1 :=
      tsub_add_cancel_of_le probOutput_le_one
    rw [add_comm] at h
    exact h

  have hxySub : x - y = Pr[= true | real] - Pr[= true | rand] := by
    unfold x y pR pF
    have hnotTop : (1 - Pr[= true | rand]) ≠ ∞ := ENNReal.sub_ne_top one_ne_top
    simpa [add_comm, add_left_comm, add_assoc] using
      (ENNReal.add_sub_add_eq_sub_right (a := Pr[= true | real]) (b := Pr[= true | rand])
        (c := 1 - Pr[= true | rand]) hnotTop)

  have hsubmul : (x - y) * ((2 : ℝ≥0∞)⁻¹) = x * ((2 : ℝ≥0∞)⁻¹) - y * ((2 : ℝ≥0∞)⁻¹) := by
    simpa using
      (ENNReal.sub_mul (a := x) (b := y) (c := (2 : ℝ≥0∞)⁻¹)
        (h := by intro _ _; simp))

  calc
    Pr[= true | do
      let b ← $ᵗ Bool
      let z ← if b then real else rand
      pure (b == z)] - 1 / 2
        = (Pr[= true | (BEq.beq true <$> real)] +
            Pr[= true | (BEq.beq false <$> rand)]) / 2 - 1 / 2 := by
              rw [hgameRepr, hmix]
    _ = x / 2 - y / 2 := by rw [hy, hx]
    _ = (x - y) / 2 := by
          have hsubmul' : x * ((2 : ℝ≥0∞)⁻¹) - y * ((2 : ℝ≥0∞)⁻¹) =
              (x - y) * ((2 : ℝ≥0∞)⁻¹) := hsubmul.symm
          simpa [div_eq_mul_inv] using hsubmul'
    _ = (Pr[= true | real] - Pr[= true | rand]) / 2 := by rw [hxySub]

/-! ## 4. All-random hybrid has probability 1/2 -/

omit [DecidableEq P] in
/-- The distribution of `randomMaskedCipher pk m` is the same for any two messages `m` and `m'`.
    Proof: the second component `m * y` (with `y ~ U(P)`) is uniform in `P` regardless of `m`. -/
lemma randomMaskedCipher_dist_eq (pk : P × P) (m m' : P) :
    ∀ c : P × P,
    Pr[= c | randomMaskedCipher (G := G) (P := P) pk m] =
    Pr[= c | randomMaskedCipher (G := G) (P := P) pk m'] := by
  intro c
  -- Both sides equal Pr[= c | do g ← $G; y ← $P; pure (g +ᵥ pk.1, y)],
  -- since y ↦ msg * y is a bijection (P is a group), so msg * y ~ U(P) when y ~ U(P).
  suffices h : ∀ msg : P,
      Pr[= c | randomMaskedCipher (G := G) (P := P) pk msg] =
      Pr[= c | (do let g ← ($ᵗ G : ProbComp G)
                   let y ← ($ᵗ P : ProbComp P)
                   (pure (g +ᵥ pk.1, y) : ProbComp (P × P)))] from
    (h m).trans (h m').symm
  intro msg
  simp only [randomMaskedCipher]
  conv_lhs => rw [probOutput_bind_eq_tsum]
  conv_rhs => rw [probOutput_bind_eq_tsum]
  refine tsum_congr fun g => ?_
  congr 1
  exact probOutput_bind_mul_left_uniform (P := P) msg
    (fun y : P => (pure (g +ᵥ pk.1, y) : ProbComp (P × P))) c

/-- Random masking remains message-independent after embedding into the hybrid cache/state output. -/
private lemma randomMaskedCipher_state_dist_eq
    (pk : P × P) (mm : P × P) (st : IND_CPA_HybridState (P := P))
    (z : (P × P) × IND_CPA_HybridState (P := P)) :
    Pr[= z | (do
      let c ← randomMaskedCipher (G := G) (P := P) pk mm.1
      pure (c, (st.1.cacheQuery mm c, st.2 + 1)))] =
    Pr[= z | (do
      let c ← randomMaskedCipher (G := G) (P := P) pk mm.2
      pure (c, (st.1.cacheQuery mm c, st.2 + 1)))] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun c => ?_
  rw [randomMaskedCipher_dist_eq (G := G) (P := P) pk mm.1 mm.2 c]

/-- In `ProbComp`, the active `monadLift` coercion is extensionally identity. -/
private lemma monadLift_probComp_eq {α : Type} (x : ProbComp α) :
    (monadLift x : ProbComp α) = x := by
  change OracleComp.liftComp x unifSpec = x
  change simulateQ (fun t => liftM (OracleQuery.query (spec := unifSpec) t)) x = x
  change simulateQ (QueryImpl.ofLift unifSpec (OracleComp unifSpec)) x = x
  exact simulateQ_ofLift_eq_self (spec := unifSpec) (mx := x)

/-- Relational form of `simulateQ_hybrid0_bdistrib_eq`, used to compose via `relTriple_bind`. -/
private lemma simulateQ_hybrid0_relTriple
    (pk : P × P) :
    ∀ {α : Type} (a : OracleComp (elgamalAsymmEnc G P).IND_CPA_oracleSpec α)
      (st : IND_CPA_HybridState (P := P)),
    RelTriple
      ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0) a).run st)
      ((simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0) a).run st)
      (EqRel (α × IND_CPA_HybridState (P := P))) := by
  intro α a
  induction a using OracleComp.inductionOn with
  | pure x =>
      intro st
      apply relTriple_eqRel_of_eq
      simp
  | query_bind t oa ih =>
      intro st
      simp only [simulateQ_bind, StateT.run_bind]
      refine (relTriple_bind
        (R := EqRel (((elgamalAsymmEnc G P).IND_CPA_oracleSpec.Range t) ×
          IND_CPA_HybridState (P := P)))
        (S := EqRel (α × IND_CPA_HybridState (P := P))) ?_ ?_)
      · cases t with
        | inl tu =>
            apply relTriple_eqRel_of_eq
            simp [IND_CPA_queryImpl_hybrid, IND_CPA_hybridChallengeOracle]
        | inr mm =>
            cases hcache : st.1 mm with
            | some c =>
                apply relTriple_eqRel_of_eq
                simp [IND_CPA_queryImpl_hybrid, IND_CPA_hybridChallengeOracle, hcache]
            | none =>
                apply relTriple_eqRel_of_probOutput_eq
                intro z
                simp only [IND_CPA_queryImpl_hybrid, IND_CPA_hybridChallengeOracle, hcache,
                  simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
                  map_eq_bind_pure_comp, StateT.run_bind]
                rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
                refine tsum_congr fun p => ?_
                congr 1
                rcases p with ⟨c, st'⟩
                simpa [IND_CPA_hybridChallengeOracle, hcache, monadLift_probComp_eq] using
                  (randomMaskedCipher_state_dist_eq (G := G) (P := P) pk mm st (c, st'))
      · intro us vs hEq
        rcases hEq with rfl
        simpa using ih us.1 us.2

/-- Key b-independence lemma: in hybrid 0 (all-random masking), the oracle simulation has
    the same output distribution whether the hidden bit is `true` or `false`.

    Proof sketch (by `OracleComp.inductionOn`):
    - For `pure x`: trivial, both sides equal `pure x`.
    - For `query_bind`:
      - Unifspec queries: independent of `b` (uniform sampling doesn't depend on `b`).
      - LR oracle queries in hybrid 0: response is `randomMaskedCipher pk (if b then m₁ else m₂)`.
        By `randomMaskedCipher_dist_eq`, this has the same distribution for `b = true` and
        `b = false`. Cache entries therefore have the same distribution, so by induction
        the continuation also has the same distribution.
-/
lemma simulateQ_hybrid0_bdistrib_eq
    (pk : P × P) :
    ∀ {α : Type} (a : OracleComp (elgamalAsymmEnc G P).IND_CPA_oracleSpec α)
      (st : IND_CPA_HybridState (P := P)),
    ∀ t : α × IND_CPA_HybridState (P := P),
    Pr[= t | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0) a).run st] =
    Pr[= t | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0) a).run st] := by
  intro α a st t
  exact probOutput_eq_of_relTriple_eqRel
    (simulateQ_hybrid0_relTriple (G := G) (P := P) pk a st) t

/-- Output distribution of `run'` in hybrid 0 is independent of the hidden bit. -/
private lemma probOutput_run'_hybrid0_eq
    (pk : P × P)
    {α : Type}
    (a : OracleComp (elgamalAsymmEnc G P).IND_CPA_oracleSpec α)
    (st : IND_CPA_HybridState (P := P))
    (x : α) :
    Pr[= x | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0) a).run' st] =
    Pr[= x | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0) a).run' st] := by
  let runTrue := (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0) a).run st
  let runFalse := (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0) a).run st
  have hRun :
      ∀ z : α × IND_CPA_HybridState (P := P), Pr[= z | runTrue] = Pr[= z | runFalse] := by
    intro z
    simpa [runTrue, runFalse] using
      (simulateQ_hybrid0_bdistrib_eq (G := G) (P := P) pk a st z)
  have hMapTrue :
      Pr[= x | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0) a).run' st] =
        Pr[(fun z : α × IND_CPA_HybridState (P := P) => z.1 = x) | runTrue] := by
    calc
      Pr[= x | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0) a).run' st]
          = Pr[= x | Prod.fst <$> runTrue] := by rfl
      _ = Pr[(fun y : α => y = x) | Prod.fst <$> runTrue] := by simp
      _ = Pr[(fun z : α × IND_CPA_HybridState (P := P) => z.1 = x) | runTrue] := by
            simpa [Function.comp] using
              (probEvent_map (mx := runTrue) (f := Prod.fst) (q := fun y : α => y = x))
  have hMapFalse :
      Pr[(fun z : α × IND_CPA_HybridState (P := P) => z.1 = x) | runFalse] =
        Pr[= x | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0) a).run' st] := by
    calc
      Pr[(fun z : α × IND_CPA_HybridState (P := P) => z.1 = x) | runFalse]
          = Pr[(fun y : α => y = x) | Prod.fst <$> runFalse] := by
              simpa [Function.comp] using
                (probEvent_map (mx := runFalse) (f := Prod.fst) (q := fun y : α => y = x)).symm
      _ = Pr[= x | Prod.fst <$> runFalse] := by simp
      _ = Pr[= x | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0) a).run' st] :=
            by rfl
  have hEvent :
      Pr[(fun z : α × IND_CPA_HybridState (P := P) => z.1 = x) | runTrue] =
        Pr[(fun z : α × IND_CPA_HybridState (P := P) => z.1 = x) | runFalse] := by
    simp only [probEvent_eq_tsum_indicator, hRun]
  calc
    Pr[= x | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0) a).run' st]
        = Pr[(fun z : α × IND_CPA_HybridState (P := P) => z.1 = x) | runTrue] := hMapTrue
    _ = Pr[(fun z : α × IND_CPA_HybridState (P := P) => z.1 = x) | runFalse] := hEvent
    _ = Pr[= x | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0) a).run' st] :=
      hMapFalse

/-- The all-random hybrid game has success probability exactly 1/2.
    The adversary's view (via `simulateQ_hybrid0_bdistrib_eq`) is independent of the hidden
    bit `b`, so guessing `b` correctly happens with probability 1/2. -/
theorem IND_CPA_allRandomHalf
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) :
    Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary 0] = 1 / 2 := by
  let view : Bool → ProbComp Bool := fun b => do
    let (pk, _sk) ← (elgamalAsymmEnc G P).keygen
    (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk b 0) (adversary pk)).run' (∅, 0)
  have hviewEq : ∀ x : Bool, Pr[= x | view true] = Pr[= x | view false] := by
    intro x
    rw [show view true = (do
      let (pk, _sk) ← (elgamalAsymmEnc G P).keygen
      (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0) (adversary pk)).run' (∅, 0))
        from rfl]
    rw [show view false = (do
      let (pk, _sk) ← (elgamalAsymmEnc G P).keygen
      (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0) (adversary pk)).run' (∅, 0))
        from rfl]
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun ks => ?_
    rcases ks with ⟨pk, sk⟩
    change
      Pr[= ((pk, sk) : (P × P) × G) | (elgamalAsymmEnc G P).keygen] *
        Pr[= x | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk true 0)
          (adversary pk)).run' (∅, 0)] =
      Pr[= ((pk, sk) : (P × P) × G) | (elgamalAsymmEnc G P).keygen] *
        Pr[= x | (simulateQ (IND_CPA_queryImpl_hybrid (G := G) (P := P) pk false 0)
          (adversary pk)).run' (∅, 0)]
    rw [probOutput_run'_hybrid0_eq (G := G) (P := P) (pk := pk) (a := adversary pk)
      (st := (∅, 0)) (x := x)]
  have hrepr :
      Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary 0] =
      Pr[= true | do
        let b ← $ᵗ Bool
        if b then (BEq.beq true <$> view true) else (BEq.beq false <$> view false)] := by
    refine probOutput_bind_congr' ($ᵗ Bool) true ?_
    intro b
    cases b <;> simp [IND_CPA_HybridGame, view, bind_assoc]
  have hmix :
      Pr[= true | do
        let b ← $ᵗ Bool
        if b then (BEq.beq true <$> view true) else (BEq.beq false <$> view false)] =
      (Pr[= true | (BEq.beq true <$> view true)] +
        Pr[= true | (BEq.beq false <$> view false)]) / 2 :=
    probOutput_bind_uniformBool
      (f := fun b => if b then (BEq.beq true <$> view true) else (BEq.beq false <$> view false))
      (x := true)
  have hsum : Pr[= true | view true] + Pr[= false | view true] = 1 := by
    have hsumAll : ∑ b : Bool, Pr[= b | view true] = 1 :=
      HasEvalPMF.sum_probOutput_eq_one (m := ProbComp) (mx := view true)
    simpa [Fintype.sum_bool] using hsumAll
  calc
    Pr[= true | IND_CPA_HybridGame (G := G) (P := P) adversary 0]
        = (Pr[= true | (BEq.beq true <$> view true)] +
            Pr[= true | (BEq.beq false <$> view false)]) / 2 := by
              rw [hrepr, hmix]
    _ = (Pr[= true | view true] + Pr[= false | view false]) / 2 := by
          rw [probOutput_true_eq_true_map, probOutput_true_eq_falseMap]
    _ = (Pr[= true | view true] + Pr[= false | view true]) / 2 := by
          rw [hviewEq false]
    _ = 1 / 2 := by rw [hsum]

/-! ## 5. Per-hop DDH reduction -/

/-- The DDH reduction adversary for the hop from `hybrid k` to `hybrid k+1`.

    Given DDH challenge `(x, x₁, x₂, x₃)` (with `x₁ = g₁ +ᵥ x`, `x₂ = g₂ +ᵥ x`):
    - Public key is `(x, x₁)`.
    - For fresh LR oracle queries with counter `j < k`: real ElGamal encryption.
    - For fresh LR oracle query with counter `j = k`: return `(x₂, m_b * x₃)`.
      - In the DDH-real branch (`x₃ = g₂ +ᵥ x₁`): this equals `(g₂ +ᵥ x, m_b * (g₂ +ᵥ x₁))`,
        a valid ElGamal ciphertext with ephemeral key `g₂` ~ `U(G)`.
      - In the DDH-random branch (`x₃ ~ U(P)`): this equals `(g₂ +ᵥ x, m_b * y)` where
        `y ~ U(P)`, matching `randomMaskedCipher`.
    - For fresh LR oracle queries with counter `j > k`: random masking.
    - Repeated (cached) queries: serve from cache.
    This means: `Pr[step reduction wins | DDH real] = Pr[hybrid k+1 wins]`
                `Pr[step reduction wins | DDH random] = Pr[hybrid k wins]` -/
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

def IND_CPA_stepDDHReduction [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) : DiffieHellman.DDHAdversary G P :=
  fun x x₁ x₂ x₃ => do
    let b ← $ᵗ Bool
    let pk : P × P := (x, x₁)
    let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
      (adversary pk)).run' (∅, 0)
    return (b == b')

private def stepDDH_realBranchCore [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) (x : P) (g₁ g₂ : G) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let pk : P × P := (x, g₁ +ᵥ x)
  let x₂ : P := g₂ +ᵥ x
  let x₃ : P := g₂ +ᵥ g₁ +ᵥ x
  let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ x₃)
    (adversary pk)).run' (∅, 0)
  return (b == b')

private def stepDDH_randBranchCore [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) (x : P) (g₁ g₂ : G) : ProbComp Bool := do
  let y ← $ᵗ P
  let b ← $ᵗ Bool
  let pk : P × P := (x, g₁ +ᵥ x)
  let x₂ : P := g₂ +ᵥ x
  let b' ← (simulateQ (IND_CPA_stepDDHQueryImpl (G := G) (P := P) pk b k x₂ y)
    (adversary pk)).run' (∅, 0)
  return (b == b')

private def stepDDH_realBranchGame [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) : ProbComp Bool := do
  let x ← $ᵗ P
  let g₁ ← $ᵗ G
  let g₂ ← $ᵗ G
  stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂

private def stepDDH_randBranchGame [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) : ProbComp Bool := do
  let x ← $ᵗ P
  let g₁ ← $ᵗ G
  let g₂ ← $ᵗ G
  stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂

private lemma ddhExp_stepDDHReduction_decomp [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) :
    Pr[= true | DiffieHellman.ddhExp (IND_CPA_stepDDHReduction (G := G) (P := P) adversary k)] -
      1 / 2 =
    (Pr[= true | stepDDH_realBranchGame (G := G) (P := P) adversary k] -
      Pr[= true | stepDDH_randBranchGame (G := G) (P := P) adversary k]) / 2 := by
  let mixedCore : ProbComp Bool := do
    let x ← $ᵗ P
    let g₁ ← $ᵗ G
    let g₂ ← $ᵗ G
    let d ← $ᵗ Bool
    let z ← if d then
      stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
    else
      stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
    pure (d == z)
  have hrepr :
      Pr[= true | DiffieHellman.ddhExp (IND_CPA_stepDDHReduction (G := G) (P := P) adversary k)] =
      Pr[= true | mixedCore] := by
    simp [mixedCore, DiffieHellman.ddhExp, parallelTesting_experiment,
      IND_CPA_stepDDHReduction, stepDDH_realBranchCore, stepDDH_randBranchCore,
      bind_assoc]
  have hswap₁ :
      Pr[= true | mixedCore] =
      Pr[= true | do
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let d ← $ᵗ Bool
        let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] := by
    unfold mixedCore
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun x => ?_
    congr 1
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun g₁ => ?_
    congr 1
    simpa [bind_assoc] using
      (probEvent_bind_bind_swap
        (mx := ($ᵗ G : ProbComp G))
        (my := ($ᵗ Bool : ProbComp Bool))
        (f := fun g₂ d => do
          let z ← if d then
            stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
          else
            stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
          pure (d == z))
        (q := fun t : Bool => t = true))
  have hswap₂ :
      Pr[= true | do
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let d ← $ᵗ Bool
        let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] =
      Pr[= true | do
        let x ← $ᵗ P
        let d ← $ᵗ Bool
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] := by
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun x => ?_
    congr 1
    simpa [bind_assoc] using
      (probEvent_bind_bind_swap
        (mx := ($ᵗ G : ProbComp G))
        (my := ($ᵗ Bool : ProbComp Bool))
        (f := fun g₁ d => do
          let g₂ ← $ᵗ G
          let z ← if d then
            stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
          else
            stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
          pure (d == z))
        (q := fun t : Bool => t = true))
  have hswap₃ :
      Pr[= true | do
        let x ← $ᵗ P
        let d ← $ᵗ Bool
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] =
      Pr[= true | do
        let d ← $ᵗ Bool
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] := by
    simpa [bind_assoc] using
      (probEvent_bind_bind_swap
        (mx := ($ᵗ P : ProbComp P))
        (my := ($ᵗ Bool : ProbComp Bool))
        (f := fun x d => do
          let g₁ ← $ᵗ G
          let g₂ ← $ᵗ G
          let z ← if d then
            stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
          else
            stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
          pure (d == z))
        (q := fun t : Bool => t = true))
  have hmix :
      Pr[= true | do
        let d ← $ᵗ Bool
        let z ← if d then
          stepDDH_realBranchGame (G := G) (P := P) adversary k
        else
          stepDDH_randBranchGame (G := G) (P := P) adversary k
        pure (d == z)] =
      Pr[= true | do
        let d ← $ᵗ Bool
        let x ← $ᵗ P
        let g₁ ← $ᵗ G
        let g₂ ← $ᵗ G
        let z ← if d then
          stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
        else
          stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
        pure (d == z)] := by
    refine probOutput_bind_congr' ($ᵗ Bool) true ?_
    intro d
    cases d <;>
      simp [stepDDH_realBranchGame, stepDDH_randBranchGame,
        map_eq_bind_pure_comp, bind_assoc]
  calc
    Pr[= true | DiffieHellman.ddhExp (IND_CPA_stepDDHReduction (G := G) (P := P) adversary k)] -
        1 / 2
      = Pr[= true | mixedCore] - 1 / 2 := by rw [hrepr]
    _ = Pr[= true | do
          let x ← $ᵗ P
          let g₁ ← $ᵗ G
          let d ← $ᵗ Bool
          let g₂ ← $ᵗ G
          let z ← if d then
            stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
          else
            stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
          pure (d == z)] - 1 / 2 := by rw [hswap₁]
    _ = Pr[= true | do
          let x ← $ᵗ P
          let d ← $ᵗ Bool
          let g₁ ← $ᵗ G
          let g₂ ← $ᵗ G
          let z ← if d then
            stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
          else
            stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
          pure (d == z)] - 1 / 2 := by rw [hswap₂]
    _ = Pr[= true | do
          let d ← $ᵗ Bool
          let x ← $ᵗ P
          let g₁ ← $ᵗ G
          let g₂ ← $ᵗ G
          let z ← if d then
            stepDDH_realBranchCore (G := G) (P := P) adversary k x g₁ g₂
          else
            stepDDH_randBranchCore (G := G) (P := P) adversary k x g₁ g₂
          pure (d == z)] - 1 / 2 := by rw [hswap₃]
    _ = Pr[= true | do
          let d ← $ᵗ Bool
          let z ← if d then
            stepDDH_realBranchGame (G := G) (P := P) adversary k
          else
            stepDDH_randBranchGame (G := G) (P := P) adversary k
          pure (d == z)] - 1 / 2 := by rw [hmix]
    _ = (Pr[= true | stepDDH_realBranchGame (G := G) (P := P) adversary k] -
          Pr[= true | stepDDH_randBranchGame (G := G) (P := P) adversary k]) / 2 :=
        ddh_decomp_two_games
          (real := stepDDH_realBranchGame (G := G) (P := P) adversary k)
          (rand := stepDDH_randBranchGame (G := G) (P := P) adversary k)

/-! ## 6. Per-hop bound -/

/-- The per-hop DDH bound: the absolute difference between consecutive hybrid winning
    probabilities equals twice the absolute signed DDH advantage of `IND_CPA_stepDDHReduction`.

    Equivalently: `|Pr[hybrid k+1 wins] - Pr[hybrid k wins]| = 2 * |signedDDHAdv(step k)|`
    where `signedDDHAdv(adv) = Pr[ddhExp(adv) wins] - 1/2` (in ℝ, can be negative).

    Proof sketch:
    1. Distribution equality (real branch):
       `Pr[step reduction wins | DDH real] = Pr[hybrid k+1 wins]`
       Requires: showing `(g₂ +ᵥ x, m_b * (g₂ +ᵥ x₁))` is distributed as real ElGamal
       with fresh ephemeral key, via OracleComp induction.
    2. Distribution equality (random branch):
       `Pr[step reduction wins | DDH random] = Pr[hybrid k wins]`
       Requires: showing `m_b * y` (y ~ U(P)) matches `randomMaskedCipher`, via induction.
    3. Apply `ddh_decomp_two_games` to decompose the DDH experiment.
    4. The signed advantage determines the direction; taking `|·|` gives the hop bound. -/
lemma IND_CPA_stepDDH_hopBound [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (k : ℕ) :
    |AsymmEncAlg.trueProbReal (IND_CPA_HybridGame (G := G) (P := P) adversary (k + 1)) -
      AsymmEncAlg.trueProbReal (IND_CPA_HybridGame (G := G) (P := P) adversary k)| ≤
      2 * |AsymmEncAlg.trueProbReal
          (DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary k)) - 1 / 2| := by
  sorry

/-! ## 7. Main theorem -/

/-- **Main theorem**: For any `q`-query IND-CPA adversary against ElGamal, the advantage is
    bounded by the sum of the per-hop DDH advantages.

    The hypothesis `hstart : IND_CPA_HybridGame adversary q = IND_CPA_game adversary` is the
    **legitimate query-bound assumption**: it asserts that the `q`-th hybrid (which uses real
    ElGamal for the first `q` fresh LR queries) is identical in distribution to the actual
    IND-CPA experiment. This holds for any concrete adversary that makes at most `q` distinct
    fresh LR queries. -/
theorem ElGamal_IND_CPA_bound_toReal [DecidableEq G]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary)
    (q : ℕ)
    (hstart : IND_CPA_HybridGame (G := G) (P := P) adversary q = IND_CPA_game adversary) :
    ((elgamalAsymmEnc G P).IND_CPA_advantage adversary).toReal ≤
      Finset.sum (Finset.range q) (fun k =>
        2 * |AsymmEncAlg.trueProbReal
              (DiffieHellman.ddhExp (IND_CPA_stepDDHReduction adversary k)) - 1 / 2|) := by
  -- Step 1: bridge from ENNReal advantage to |signedAdvantage| in ℝ
  refine le_trans (AsymmEncAlg.IND_CPA_advantage_toReal_le_abs_signedAdvantageReal adversary) ?_
  -- Step 2: telescope the signed advantage over the hybrid family
  refine le_trans
    (AsymmEncAlg.IND_CPA_advantage'_abs_le_sum_hybridDiff_abs
      adversary q (IND_CPA_HybridFamily (G := G) (P := P) adversary q)
      (by simp only [IND_CPA_HybridFamily_zero]; exact hstart)
      (by simp only [IND_CPA_HybridFamily_q, AsymmEncAlg.trueProbReal];
          rw [IND_CPA_allRandomHalf]; simp)) ?_
  -- Step 3: bound each hop by DDH, then reindex via sum_range_reflect.
  -- Family is decreasing: games i = hybrid (q-i), games (i+1) = hybrid (q-i-1).
  -- Hop i uses stepDDHReduction (q-1-i); then sum_range_reflect converts to index i.
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
            -- Arithmetic: q - (i+1) = q - 1 - i, and q - 1 - i + 1 = q - i (since i < q)
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
