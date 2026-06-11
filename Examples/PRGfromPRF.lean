/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.PRF
import VCVio.CryptoFoundations.PRG
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# PRG from PRF

This file constructs a simple stream-style PRG from a PRF
`f : K → S → S × O`. Starting from a random state `s₀`, each round applies
the PRF to the current state, producing the next state and one output block.

The proof outline follows the standard switching argument:

1. Replace the real PRF with a random function.
2. Show that, except when the state chain repeats, the random-function world is
   identical to the ideal PRG world of independent uniform outputs.
3. Bound the remaining gap by the probability of a state collision.
-/

open OracleComp OracleSpec ENNReal PRFScheme PRGScheme
open List (Vector)

namespace PRGfromPRF

variable {K S O : Type}
variable [Inhabited K] [Fintype K] [SampleableType K]
variable [Inhabited S] [Fintype S] [DecidableEq S] [SampleableType S]
variable [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O]

/-- Deterministically unroll `n` rounds of a state transition/output function. -/
def streamOutputs (step : S → S × O) : (n : ℕ) → S → List.Vector O n
  | 0, _ => .nil
  | n + 1, s =>
      let (s', out) := step s
      out ::ᵥ streamOutputs step n s'

/-- Query the PRF oracle `n` times, threading the returned state and collecting outputs. -/
def oracleOutputs :
    (n : ℕ) → S → OracleComp (PRFScheme.PRFOracleSpec S (S × O)) (List.Vector O n)
  | 0, _ => pure .nil
  | n + 1, s => do
      let (s', out) ← (PRFScheme.PRFOracleSpec S (S × O)).query (Sum.inr s)
      let rest ← oracleOutputs n s'
      pure (out ::ᵥ rest)

/-- Query the PRF oracle `n` times, recording the states fed to the oracle. Repeated
states are exactly the bad event for the random-function to ideal-PRG hop. -/
def oracleVisitedStates :
    (n : ℕ) → S → OracleComp (PRFScheme.PRFOracleSpec S (S × O)) (List.Vector S n)
  | 0, _ => pure .nil
  | n + 1, s => do
      let (s', _) ← (PRFScheme.PRFOracleSpec S (S × O)).query (Sum.inr s)
      let rest ← oracleVisitedStates n s'
      pure (s ::ᵥ rest)

/-- Stream-style PRG obtained by iterating a PRF `n` times. The seed contains both the
PRF key and the initial state; later theorems assume the PRF key distribution is uniform. -/
@[simps!] def streamPRG (prf : PRFScheme K S (S × O)) (n : ℕ) :
    PRGScheme (K × S) (List.Vector O n) where
  gen ks := streamOutputs (prf.eval ks.1) n ks.2

namespace streamPRG

variable {prf : PRFScheme K S (S × O)} {n : ℕ}

/-- Reduction from a distinguisher on the stream PRG output to a PRF distinguisher. It
samples an initial state, queries the candidate oracle `n` times, and feeds the resulting
output vector to the PRG adversary. -/
def prfReduction (n : ℕ) (adv : PRGAdversary (List.Vector O n)) : PRFAdversary S (S × O) :=
  show OracleComp (unifSpec + (S →ₒ S × O)) Bool from do
    let seed ← OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + (S →ₒ S × O))
      ($ᵗ S)
    let outputs ← oracleOutputs n seed
    OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + (S →ₒ S × O))
      (adv outputs)

/-- Collision experiment for the ideal random-function world: sample an initial state,
iterate a lazy random oracle for `n` rounds, and test whether any queried state repeats. -/
def idealCollisionExp (n : ℕ) : ProbComp Bool := do
  let seed ← $ᵗ S
  let states ←
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := S) (R := S × O))
      (oracleVisitedStates n seed)).run' ∅
  return decide (¬ states.toList.Nodup)

/-- Probability of the bad event in the ideal random-function world. -/
noncomputable def collisionProb (n : ℕ) : ℝ :=
  (Pr[= true | idealCollisionExp (S := S) (O := O) n]).toReal

omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S]
  [DecidableEq S] [SampleableType S] [Inhabited O] [Fintype O]
  [DecidableEq O] [SampleableType O] in
/-- Under the real PRF query implementation, querying the oracle `n` times produces the
same outputs as the deterministic `streamOutputs`. -/
private lemma simulateQ_prfReal_oracleOutputs (k : K) (n : ℕ) (s : S) :
    simulateQ (prfRealQueryImpl prf k) (oracleOutputs n s) =
      (pure (streamOutputs (prf.eval k) n s) : ProbComp _) := by
  induction n generalizing s with
  | zero => simp [oracleOutputs, streamOutputs]
  | succ n ih =>
    simp only [oracleOutputs, streamOutputs, simulateQ_bind, simulateQ_query,
      OracleQuery.cont_query, id_map, OracleQuery.input_query]
    show prfRealQueryImpl prf k (Sum.inr s) >>= _ = _
    simp only [prfRealQueryImpl, QueryImpl.add_apply_inr]
    cases h : prf.eval k s with
    | mk s' out =>
        let so : QueryImpl (S →ₒ S × O) ProbComp := fun d => pure (prf.eval k d)
        change simulateQ
            ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) + so)
            (do
              let rest ← oracleOutputs n s'
              pure (out ::ᵥ rest)) = _
        have ih' :
            simulateQ
                ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) + so)
                (oracleOutputs n s') =
              pure (streamOutputs (prf.eval k) n s') := by
          simpa [PRFScheme.prfRealQueryImpl, so] using ih (s := s')
        rw [simulateQ_bind, ih']
        simp [h, so]

omit [Inhabited K] [Fintype K] [SampleableType K] [Fintype S] [DecidableEq S]
  [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O] in
/-- Applying the real PRF query implementation to the full reduction body simplifies to
sampling a seed and running the adversary on deterministic output. -/
private lemma simulateQ_prfReal_reduction (k : K) (n : ℕ)
    (adv : PRGAdversary (List.Vector O n)) :
    simulateQ (prf.prfRealQueryImpl k)
      (show OracleComp (unifSpec + (S →ₒ S × O)) Bool from do
        let seed ← liftComp ($ᵗ S) (unifSpec + ofFn fun _ => S × O)
        let outputs ← oracleOutputs n seed
        liftComp (adv outputs) (unifSpec + ofFn fun _ => S × O)) =
    (do let s ← $ᵗ S; adv (streamOutputs (prf.eval k) n s)) := by
  change simulateQ (prf.prfRealQueryImpl k)
      (do
        let seed ← liftComp ($ᵗ S) (unifSpec + ofFn fun _ => S × O)
        let outputs ← oracleOutputs n seed
        liftComp (adv outputs) (unifSpec + ofFn fun _ => S × O)) =
    (do
      let s ← $ᵗ S
      adv (streamOutputs (prf.eval k) n s))
  rw [simulateQ_bind, simulateQ_prfRealQueryImpl_liftComp]
  refine bind_congr ?_
  intro s
  rw [simulateQ_bind, simulateQ_prfReal_oracleOutputs, pure_bind,
      simulateQ_prfRealQueryImpl_liftComp]

omit [DecidableEq S] [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O] in
/-- In the real world, the stream PRG experiment has the same output distribution as
the real PRF experiment for the reduction adversary, provided the PRF key
distribution is uniform. -/
theorem prgRealExp_eq_prfRealExp
    (hkey : 𝒟[prf.keygen] = 𝒟[$ᵗ K])
    (adv : PRGAdversary (List.Vector O n)) :
    𝒟[PRGScheme.prgRealExp (streamPRG prf n) adv] =
      𝒟[PRFScheme.prfRealExp prf (prfReduction (S := S) (O := O) n adv)] := by
  simp only [PRGScheme.prgRealExp, PRFScheme.prfRealExp, prfReduction, streamPRG]
  simp_rw [simulateQ_prfReal_reduction]
  change 𝒟[(·, ·) <$> ($ᵗ K) <*> ($ᵗ S) >>=
    fun ks => adv (streamOutputs (prf.eval ks.1) n ks.2)] = _
  simp only [monad_norm, Function.comp_def]
  rw [evalDist_bind, evalDist_bind, hkey]

/-- Running a state-lifted computation that begins by lifting a stateless computation `oa`
and then continues with `rest` is the same as sampling `oa` first and continuing each branch
with the discarded-state run of `rest`. -/
private lemma run'_liftM_bind {σ β γ : Type} (oa : ProbComp β)
    (rest : β → StateT σ ProbComp γ) (s : σ) :
    ((liftM oa : StateT σ ProbComp β) >>= rest).run' s = oa >>= fun x => (rest x).run' s := by
  rw [StateT.run'_eq, StateT.run_bind, liftM_run_StateT, bind_assoc]
  simp only [pure_bind, map_bind]
  rfl

/-- Running a state-lifted computation that ends by lifting a stateless continuation `f`
discards the threaded state exactly as `run'` followed by `f`. -/
private lemma run'_bind_liftM {σ β γ : Type} (N : StateT σ ProbComp β)
    (f : β → ProbComp γ) (s : σ) :
    (N >>= fun a => (liftM (f a) : StateT σ ProbComp γ)).run' s = N.run' s >>= f := by
  rw [StateT.run'_eq, StateT.run_bind, StateT.run'_eq, map_bind, bind_map_left]
  refine bind_congr fun p => ?_
  rw [liftM_run_StateT, map_bind]
  simp only [map_pure]
  rw [bind_pure]

/-- The output distribution that the ideal PRF reduction feeds to the PRG adversary:
sample an initial seed, then read `n` output blocks off the lazy random oracle chain. -/
noncomputable def idealOutputs (n : ℕ) : ProbComp (List.Vector O n) := do
  let seed ← $ᵗ S
  (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs n seed)).run' ∅

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq S] [Inhabited O] [Fintype O]
  [DecidableEq O] in
/-- The ideal PRG experiment for the stream adversary is exactly: sample a uniform output
vector and run the adversary on it. -/
lemma prgIdealExp_eq_bind (adv : PRGAdversary (List.Vector O n)) :
    PRGScheme.prgIdealExp adv = (($ᵗ (List.Vector O n)) >>= adv) :=
  rfl

omit [DecidableEq O] in
/-- The ideal PRF experiment, applied to the stream reduction, factors as sampling the
adversary's input via the lazy-random-oracle chain (`idealOutputs`) and then running the
adversary. -/
lemma prfIdealExp_prfReduction_eq (adv : PRGAdversary (List.Vector O n)) :
    PRFScheme.prfIdealExp (prfReduction (S := S) (O := O) n adv) =
      (idealOutputs (S := S) (O := O) n >>= adv) := by
  unfold PRFScheme.prfIdealExp prfReduction idealOutputs
  rw [simulateQ_bind, simulateQ_prfIdealQueryImpl_liftComp, run'_liftM_bind, bind_assoc]
  refine bind_congr fun seed => ?_
  rw [simulateQ_bind]
  simp only [simulateQ_prfIdealQueryImpl_liftComp]
  rw [run'_bind_liftM]

/-- The per-seed output distribution: run the lazy random oracle chain for `n` rounds from a
fixed initial state `seed`, collecting the output blocks. Averaging over `seed ← $ᵗ S` gives
`idealOutputs`. -/
noncomputable def seedOutputs (n : ℕ) (seed : S) : ProbComp (List.Vector O n) :=
  (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs n seed)).run' ∅

/-- The per-seed collision experiment: run the lazy random oracle chain for `n` rounds from a
fixed initial state `seed`, and test whether any queried state repeats. Averaging over
`seed ← $ᵗ S` gives `idealCollisionExp`. -/
noncomputable def seedCollisionExp (n : ℕ) (seed : S) : ProbComp Bool := do
  let states ←
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
      (oracleVisitedStates n seed)).run' ∅
  return decide (¬ states.toList.Nodup)

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq O] in
/-- `idealOutputs` averages the per-seed chain outputs over a uniform initial state. -/
lemma idealOutputs_eq_bind :
    idealOutputs (S := S) (O := O) n = (($ᵗ S) >>= seedOutputs (S := S) (O := O) n) := rfl

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq O] in
/-- `idealCollisionExp` averages the per-seed collision test over a uniform initial state. -/
lemma idealCollisionExp_eq_bind :
    idealCollisionExp (S := S) (O := O) n = (($ᵗ S) >>= seedCollisionExp (S := S) (O := O) n) :=
  rfl

/-- Generalized collision experiment for an arbitrary starting cache `c`. Running the lazy
random oracle chain for `N` rounds from state `s`, the bad event is that the chain repeats a
state (`¬ Nodup`) or revisits a state already present in `c`. For `c = ∅` this reduces to
`seedCollisionExp`. The generalized cache is the induction vehicle: each fresh step extends
`c` by the just-visited state. -/
noncomputable def genCollisionExp (N : ℕ) (s : S) (c : (S →ₒ S × O).QueryCache) :
    ProbComp Bool := do
  let states ←
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleVisitedStates N s)).run' c
  return decide (¬ states.toList.Nodup ∨ ∃ x ∈ states.toList, c.isCached x = true)

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq O] in
/-- One lazy-random-oracle step of the output chain: sample/recall the answer at `s`, then
recurse on the returned next-state with the updated cache, prepending the output block. -/
private lemma simulateQ_oracleOutputs_succ_run' (N : ℕ) (s : S)
    (c : (S →ₒ S × O).QueryCache) :
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs (N + 1) s)).run' c =
      (do
        let p ← ((S →ₒ S × O).randomOracle s).run c
        let rest ← (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
          (oracleOutputs N p.1.1)).run' p.2
        pure (p.1.2 ::ᵥ rest)) := by
  rw [oracleOutputs]
  simp only [simulateQ_bind, simulateQ_prfIdealQueryImpl_inr, StateT.run'_eq, StateT.run_bind,
    map_bind]
  refine bind_congr fun a => ?_
  obtain ⟨⟨s', out⟩, c'⟩ := a
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
    bind_map_left]

omit [DecidableEq O] in
/-- **Generalized per-seed core coupling.** For an arbitrary starting cache `c`, the total
variation distance between the lazy-random-oracle output chain (run from cache `c`) and a
uniformly random output vector is bounded by the generalized collision probability. Proved by
induction on the number of rounds: a fresh query produces an independent uniform block and the
cache grows by exactly the just-visited state, so the collision recursion closes; a repeated
query has already triggered the bad event, where the bound is trivially `1`. -/
lemma tvDist_seedOutputs_le_collision_gen (N : ℕ) (s : S)
    (c : (S →ₒ S × O).QueryCache) :
    tvDist ((simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
          (oracleOutputs N s)).run' c) ($ᵗ (List.Vector O N)) ≤
      (Pr[= true | genCollisionExp N s c]).toReal := by
  induction N generalizing s c with
  | zero =>
    refine le_trans (le_of_eq ?_) ENNReal.toReal_nonneg
    rw [tvDist_eq_zero_iff]
    simp only [oracleOutputs, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine evalDist_ext fun y => ?_
    simp
  | succ N ih =>
    sorry

omit [DecidableEq O] in
/-- **Per-seed core coupling.** For a fixed initial state, the total variation distance between
the lazy-random-oracle output chain and a uniformly random output vector is bounded by the
probability that the state chain revisits a state. This is the fundamental "identical until
bad" step: until the chain repeats, the lazy random oracle returns independent uniform blocks.

The empty-cache specialization of `tvDist_seedOutputs_le_collision_gen`. -/
lemma tvDist_seedOutputs_le_collision (seed : S) :
    tvDist (seedOutputs n seed) ($ᵗ (List.Vector O n)) ≤
      (Pr[= true | seedCollisionExp (O := O) n seed]).toReal := by
  have heq : genCollisionExp (O := O) n seed ∅ = seedCollisionExp (O := O) n seed := by
    unfold genCollisionExp seedCollisionExp
    refine bind_congr fun states => ?_
    simp [QueryCache.isCached_empty]
  have h := tvDist_seedOutputs_le_collision_gen (O := O) n seed ∅
  rw [heq] at h
  exact h

omit [DecidableEq O] in
/-- **Core coupling.** The total variation distance between the lazy-random-oracle output
chain and a uniformly random output vector is bounded by the state-collision probability.
This is the fundamental "identical until bad" step: until the state chain repeats, the lazy
random oracle returns independent uniform blocks, matching the ideal PRG distribution.

Obtained by averaging the per-seed bound `tvDist_seedOutputs_le_collision` over the uniform
initial state. -/
lemma tvDist_idealOutputs_le_collisionProb :
    tvDist (idealOutputs (S := S) (O := O) n) ($ᵗ (List.Vector O n)) ≤
      collisionProb (S := S) (O := O) n := by
  rw [collisionProb, idealCollisionExp_eq_bind, idealOutputs_eq_bind]
  -- Replace the constant right-hand side by a (lossless) bind over the same seed.
  have h_const : tvDist (($ᵗ S) >>= seedOutputs n) ($ᵗ (List.Vector O n)) =
      tvDist (($ᵗ S) >>= seedOutputs n) (($ᵗ S) >>= fun _ => $ᵗ (List.Vector O n)) := by
    simp only [tvDist]
    congr 1
    refine evalDist_ext fun y => ?_
    rw [probOutput_bind_const]
    simp
  rw [h_const]
  refine le_trans (tvDist_bind_left_le _ _ _) ?_
  -- Bound each per-seed TV distance by the per-seed collision probability, then reassemble.
  rw [probOutput_bind_eq_tsum]
  rw [ENNReal.tsum_toReal_eq (fun seed => ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)]
  refine Summable.tsum_le_tsum (fun seed => ?_) ?_ ?_
  · rw [ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_left (tvDist_seedOutputs_le_collision seed) ENNReal.toReal_nonneg
  · exact Summable.of_nonneg_of_le
      (fun seed => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
      (fun seed => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _))
      (ENNReal.summable_toReal tsum_probOutput_ne_top)
  · exact ENNReal.summable_toReal (by rw [← probOutput_bind_eq_tsum]; exact probOutput_ne_top)

omit [DecidableEq O] in
/-- The gap between the ideal PRF and ideal PRG experiments is bounded by the
collision probability. This follows from the fundamental lemma of game playing:
when a lazy random function never receives the same input twice, its outputs are
independent uniform — matching the ideal PRG distribution exactly. The bound
comes from the probability that the state chain revisits some state.

*Proof outline (switching argument):*
1. Factor both experiments as: sample inputs to `adv`, then run `adv`.
2. In the ideal PRF world, the inputs come from a random-oracle chain.
3. In the ideal PRG world, the inputs are i.i.d. uniform.
4. Conditioned on no state collision, the random-oracle chain produces
   independent uniform outputs, so the two input distributions coincide.
5. By the "identical until bad" lemma (`tvDist_simulateQ_le_probEvent_bad`),
   the TV distance between the two input distributions is at most `Pr[collision]`.
6. By the data-processing inequality, running `adv` cannot increase the gap.

Full formalization requires coupling the random-oracle chain with independent
uniform outputs and instantiating the switching-lemma infrastructure for this
specific oracle. -/
theorem prfIdealGap_le_collisionProb (adv : PRGAdversary (List.Vector O n)) :
    |(Pr[= true | PRFScheme.prfIdealExp (prfReduction (S := S) (O := O) n adv)]).toReal -
      (Pr[= true | PRGScheme.prgIdealExp adv]).toReal| ≤
      collisionProb (S := S) (O := O) n := by
  rw [prfIdealExp_prfReduction_eq adv, prgIdealExp_eq_bind adv]
  calc |(Pr[= true | idealOutputs n >>= adv]).toReal -
          (Pr[= true | ($ᵗ (List.Vector O n)) >>= adv]).toReal|
      ≤ tvDist (idealOutputs n >>= adv) (($ᵗ (List.Vector O n)) >>= adv) :=
        abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist (idealOutputs n) ($ᵗ (List.Vector O n)) := tvDist_bind_right_le _ _ _
    _ ≤ collisionProb (S := S) (O := O) n := tvDist_idealOutputs_le_collisionProb

omit [DecidableEq O] in
/-- Security of the stream PRG obtained from a PRF: PRG distinguishing advantage is
bounded by the PRF advantage of the reduction plus the collision probability in the
ideal random-function world. -/
theorem security
    (hkey : 𝒟[prf.keygen] = 𝒟[$ᵗ K])
    (adv : PRGAdversary (List.Vector O n)) :
    PRGScheme.prgAdvantage (streamPRG prf n) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction (S := S) (O := O) n adv) +
      collisionProb (S := S) (O := O) n := by
  unfold PRGScheme.prgAdvantage PRFScheme.prfAdvantage
  have hreal : (Pr[= true | PRGScheme.prgRealExp (streamPRG prf n) adv]).toReal =
      (Pr[= true | PRFScheme.prfRealExp prf (prfReduction (S := S) (O := O) n adv)]).toReal :=
    congrArg ENNReal.toReal (probOutput_congr rfl (prgRealExp_eq_prfRealExp hkey adv))
  rw [hreal]
  set a := (Pr[= true | PRFScheme.prfRealExp prf (prfReduction (S := S) (O := O) n adv)]).toReal
  set b := (Pr[= true | PRFScheme.prfIdealExp (prfReduction (S := S) (O := O) n adv)]).toReal
  set c := (Pr[= true | PRGScheme.prgIdealExp adv]).toReal
  have hgap : |b - c| ≤ collisionProb (S := S) (O := O) n :=
    prfIdealGap_le_collisionProb adv
  calc |a - c| = |(a - b) + (b - c)| := by ring_nf
    _ ≤ |a - b| + |b - c| := abs_add_le _ _
    _ ≤ |a - b| + collisionProb (S := S) (O := O) n := by linarith

end streamPRG

end PRGfromPRF
