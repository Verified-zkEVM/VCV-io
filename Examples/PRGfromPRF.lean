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

omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [DecidableEq S]
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

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq O] in
/-- One lazy-random-oracle step of the visited-state chain: sample/recall the answer at `s`, then
recurse on the returned next-state with the updated cache, prepending the just-visited state `s`. -/
private lemma simulateQ_oracleVisitedStates_succ_run' (N : ℕ) (s : S)
    (c : (S →ₒ S × O).QueryCache) :
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
        (oracleVisitedStates (N + 1) s)).run' c =
      (do
        let p ← ((S →ₒ S × O).randomOracle s).run c
        let rest ← (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
          (oracleVisitedStates N p.1.1)).run' p.2
        pure (s ::ᵥ rest)) := by
  rw [oracleVisitedStates]
  simp only [simulateQ_bind, simulateQ_prfIdealQueryImpl_inr, StateT.run'_eq, StateT.run_bind,
    map_bind]
  refine bind_congr fun a => ?_
  obtain ⟨⟨s', out⟩, c'⟩ := a
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
    bind_map_left]

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq O] in
/-- Cache-miss form of the lazy random oracle on input `s`: a fresh uniform draw `u : S × O`,
returned together with the cache extended by `s ↦ u`. -/
private lemma randomOracle_run_of_none (s : S) (c : (S →ₒ S × O).QueryCache) (hc : c s = none) :
    ((S →ₒ S × O).randomOracle s).run c
      = (fun u => (u, c.cacheQuery s u)) <$> ($ᵗ (S × O)) := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc]; rfl

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq S] [DecidableEq O] in
/-- Sampling a pair uniformly is the same as sampling each coordinate independently. -/
private lemma uniformSample_prod_eq_bind :
    ($ᵗ (S × O)) = (do let a ← $ᵗ S; let b ← $ᵗ O; pure (a, b)) := by
  rw [uniformSample]
  change ((·, ·) <$> ($ᵗ S) <*> ($ᵗ O)) = _
  simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]

omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [DecidableEq S]
  [SampleableType S] [Fintype O] [DecidableEq O] in
/-- A uniform output vector of length `N + 1` decomposes as a uniform head block prepended to a
uniform vector of length `N`. -/
private lemma evalDist_uniformSample_vector_succ (N : ℕ) :
    𝒟[($ᵗ (List.Vector O (N + 1)))] =
      𝒟[(do let out ← $ᵗ O; let rest ← $ᵗ (List.Vector O N); pure (out ::ᵥ rest))] := by
  classical
  haveI : Fintype O := Fintype.ofFinite O
  refine evalDist_ext fun v => ?_
  obtain ⟨out, rest, rfl⟩ : ∃ out rest, v = out ::ᵥ rest :=
    ⟨v.head, v.tail, (List.Vector.cons_head_tail v).symm⟩
  have hR :
      Pr[= (out ::ᵥ rest) | (do let o ← $ᵗ O; let r ← $ᵗ (List.Vector O N); pure (o ::ᵥ r))]
        = Pr[= out | ($ᵗ O)] * Pr[= rest | ($ᵗ (List.Vector O N))] := by
    rw [probOutput_bind_eq_tsum, tsum_eq_single out]
    · rw [probOutput_bind_eq_tsum, tsum_eq_single rest]
      · simp
      · intro b hb
        rw [probOutput_pure, if_neg (by simp [List.Vector.eq_cons_iff, Ne.symm hb]), mul_zero]
    · intro b hb
      rw [probOutput_bind_eq_tsum, ENNReal.tsum_eq_zero.2 (fun r => by
        rw [probOutput_pure, if_neg (by simp [List.Vector.eq_cons_iff, Ne.symm hb]),
          mul_zero]), mul_zero]
  have hL :
      Pr[= (out ::ᵥ rest) | ($ᵗ (List.Vector O (N + 1)))]
        = Pr[= out | ($ᵗ O)] * Pr[= rest | ($ᵗ (List.Vector O N))] := by
    rw [probOutput_uniformSample, probOutput_uniformSample, probOutput_uniformSample,
      ← ENNReal.mul_inv (by simp) (by simp)]
    congr 1
    rw [← Nat.cast_mul]
    congr 1
    simp [card_vector, pow_succ, Nat.mul_comm]
  rw [hL, hR]

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq S] [DecidableEq O] in
/-- The reference uniform output vector of length `N + 1`, written as a bind over a uniformly
sampled pair `p : S × O` whose first coordinate is discarded and whose second coordinate is the
prepended head block. This is the shared-base form used for the identical-until-bad coupling. -/
private lemma evalDist_uniformSample_vector_succ_pair (N : ℕ) :
    𝒟[($ᵗ (List.Vector O (N + 1)))] =
      𝒟[(do let p ← $ᵗ (S × O); let rest ← $ᵗ (List.Vector O N); pure (p.2 ::ᵥ rest))] := by
  rw [evalDist_uniformSample_vector_succ, uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  refine (evalDist_ext fun v => ?_).symm
  rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq O] in
/-- Cache-miss recursion for the generalized collision experiment. When `s` is uncached, the bad
event on the length-`N + 1` visited chain splits into the fresh draw at `s` (extending the cache by
`s`) followed by the bad event on the length-`N` sub-chain run against the extended cache. The
just-visited state `s` is folded into the cache, so the two bad events match pointwise. -/
private lemma genCollisionExp_succ_of_none (N : ℕ) (s : S) (c : (S →ₒ S × O).QueryCache)
    (hc : c s = none) :
    genCollisionExp (N + 1) s c =
      (do let p ← $ᵗ (S × O); genCollisionExp N p.1 (c.cacheQuery s p)) := by
  rw [genCollisionExp, simulateQ_oracleVisitedStates_succ_run', randomOracle_run_of_none s c hc]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  rw [uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun a => bind_congr fun b => ?_
  rw [genCollisionExp]
  refine bind_congr fun rest => ?_
  congr 1
  rw [decide_eq_decide, List.Vector.toList_cons]
  -- pointwise equivalence of the two bad events, using `c s = none`.
  have hkey : ∀ x : S,
      (c.cacheQuery s (a, b)).isCached x = true ↔ (x = s ∨ c.isCached x = true) := by
    intro x
    by_cases hx : x = s
    · subst hx; simp
    · rw [QueryCache.isCached_cacheQuery_of_ne c (a, b) hx]; simp [hx]
  have hcs : c.isCached s = false := by simp [QueryCache.isCached, hc]
  have hrest : (∃ x ∈ rest.toList, (c.cacheQuery s (a, b)).isCached x = true)
      ↔ (s ∈ rest.toList ∨ ∃ x ∈ rest.toList, c.isCached x = true) := by
    constructor
    · rintro ⟨x, hx, hxc⟩
      rcases (hkey x).1 hxc with rfl | hc'
      · exact Or.inl hx
      · exact Or.inr ⟨x, hx, hc'⟩
    · rintro (hs | ⟨x, hx, hxc⟩)
      · exact ⟨s, hs, (hkey s).2 (Or.inl rfl)⟩
      · exact ⟨x, hx, (hkey x).2 (Or.inr hxc)⟩
  have hhead : (∃ x ∈ (s :: rest.toList), c.isCached x = true)
      ↔ (∃ x ∈ rest.toList, c.isCached x = true) := by
    constructor
    · rintro ⟨x, hx, hxc⟩
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [hcs] at hxc; exact absurd hxc (by simp)
      · exact ⟨x, hx, hxc⟩
    · rintro ⟨x, hx, hxc⟩; exact ⟨x, List.mem_cons_of_mem _ hx, hxc⟩
  rw [hrest, List.nodup_cons, hhead]
  tauto

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq O] in
/-- Cache-hit determinism for the generalized collision experiment. When `s` is already cached, the
visited chain of length `N + 1` starts at `s`, which lies in the chain and is cached, so the bad
event always fires and the experiment returns `true` with probability one. -/
private lemma probOutput_genCollisionExp_succ_of_isCached (N : ℕ) (s : S)
    (c : (S →ₒ S × O).QueryCache) (hc : c.isCached s = true) :
    Pr[= true | genCollisionExp (N + 1) s c] = 1 := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · simp [genCollisionExp]
  · intro x hx
    rw [genCollisionExp, simulateQ_oracleVisitedStates_succ_run'] at hx
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hx
    obtain ⟨p, ⟨_, -, rest, -, hpeq⟩, rfl⟩ := hx
    subst hpeq
    rw [List.Vector.toList_cons, decide_eq_true (Or.inr ⟨s, List.mem_cons_self, hc⟩)]

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
    cases hc : c.isCached s with
    | false =>
      -- Cache miss: identical-until-bad coupling.
      have hcnone : c s = none := by
        simpa [QueryCache.isCached] using hc
      -- Both computations are binds over a freshly sampled pair `p : S × O`, sharing the head
      -- block `p.2` and differing only in the recursive tail.
      have hLHS :
          (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
              (oracleOutputs (N + 1) s)).run' c =
            (do let p ← $ᵗ (S × O);
                (fun v => p.2 ::ᵥ v) <$> (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
                  (oracleOutputs N p.1)).run' (c.cacheQuery s p)) := by
        rw [simulateQ_oracleOutputs_succ_run', randomOracle_run_of_none s c hcnone, bind_map_left]
        simp only [map_eq_bind_pure_comp, bind_pure_comp]
      have hRHS :
          𝒟[($ᵗ (List.Vector O (N + 1)))] =
            𝒟[(do let p ← $ᵗ (S × O); (fun v => p.2 ::ᵥ v) <$> ($ᵗ (List.Vector O N)))] := by
        rw [evalDist_uniformSample_vector_succ_pair (S := S) N]
        rfl
      -- Rewrite the goal as a TV distance between two binds over the shared pair `p : S × O`.
      rw [hLHS]
      rw [show tvDist
          (($ᵗ (S × O)) >>= fun p =>
              (fun v => p.2 ::ᵥ v) <$> (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
                (oracleOutputs N p.1)).run' (c.cacheQuery s p))
          ($ᵗ (List.Vector O (N + 1))) =
          tvDist
            (($ᵗ (S × O)) >>= fun p =>
                (fun v => p.2 ::ᵥ v) <$> (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
                  (oracleOutputs N p.1)).run' (c.cacheQuery s p))
            (($ᵗ (S × O)) >>= fun p => (fun v => p.2 ::ᵥ v) <$> ($ᵗ (List.Vector O N))) from by
        unfold tvDist; rw [hRHS]]
      refine le_trans (tvDist_bind_left_le _ _ _) ?_
      -- Bound each per-pair TV distance by the per-pair generalized collision probability.
      rw [genCollisionExp_succ_of_none N s c hcnone, probOutput_bind_eq_tsum,
        ENNReal.tsum_toReal_eq (fun p => ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)]
      refine Summable.tsum_le_tsum (fun p => ?_) ?_ ?_
      · rw [ENNReal.toReal_mul]
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        exact le_trans (tvDist_map_le (fun v => p.2 ::ᵥ v) _ _) (ih p.1 (c.cacheQuery s p))
      · refine Summable.of_nonneg_of_le
          (fun p => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
          (fun p => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _))
          (ENNReal.summable_toReal tsum_probOutput_ne_top)
      · exact ENNReal.summable_toReal
          (by rw [← probOutput_bind_eq_tsum]; exact probOutput_ne_top)
    | true =>
      -- Cache hit: the bad event already fired, so the bound is trivially `1`.
      rw [probOutput_genCollisionExp_succ_of_isCached N s c hc, ENNReal.toReal_one]
      exact tvDist_le_one _ _

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

omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [SampleableType S]
  [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O] in
/-- Caching a fresh (previously absent) key increases the live-entry count by exactly one. -/
private lemma enncard_cacheQuery_of_none (c : (S →ₒ S × O).QueryCache) (s : S) (u : S × O)
    (hc : c s = none) :
    QueryCache.enncard (c.cacheQuery s u) = QueryCache.enncard c + 1 := by
  unfold QueryCache.enncard
  have hset : (c.cacheQuery s u).toSet = insert ⟨s, u⟩ c.toSet := by
    ext ⟨t', u'⟩
    by_cases ht : t' = s
    · subst ht
      simp only [QueryCache.mem_toSet, QueryCache.cacheQuery_self, Set.mem_insert_iff,
        Sigma.mk.injEq, heq_eq_eq, true_and]
      constructor
      · intro h
        exact Or.inl (Option.some.inj h).symm
      · rintro (rfl | h)
        · rfl
        · rw [hc] at h; exact absurd h (by simp)
    · rw [QueryCache.mem_toSet, QueryCache.cacheQuery_of_ne c u ht]
      simp [Set.mem_insert_iff, ht, QueryCache.mem_toSet]
  rw [hset]
  have hnotmem : (⟨s, u⟩ : (t : S) × S × O) ∉ c.toSet := by
    rw [QueryCache.mem_toSet, hc]; simp
  rw [Set.encard_insert_of_notMem hnotmem]
  push_cast
  ring

omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [DecidableEq S] [SampleableType S]
  [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O] in
/-- For a finite state space, the live-entry count of a cache is the number of cached states. -/
private lemma enncard_eq_sum_isCached (c : (S →ₒ S × O).QueryCache) :
    QueryCache.enncard c = ∑ s : S, (if c.isCached s then (1 : ℝ≥0∞) else 0) := by
  classical
  unfold QueryCache.enncard
  have himg : Sigma.fst '' c.toSet = {s : S | c.isCached s = true} := by
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨t, u⟩, ht, rfl⟩
      rw [QueryCache.mem_toSet] at ht
      simp [QueryCache.isCached, ht]
    · intro hs
      rw [QueryCache.isCached, Option.isSome_iff_exists] at hs
      obtain ⟨u, hu⟩ := hs
      exact ⟨⟨s, u⟩, hu, rfl⟩
  have hinj : Set.InjOn Sigma.fst c.toSet := by
    rintro ⟨t₁, u₁⟩ h₁ ⟨t₂, u₂⟩ h₂ (rfl : t₁ = t₂)
    rw [QueryCache.mem_toSet] at h₁ h₂
    rw [h₁] at h₂
    obtain rfl := Option.some.inj h₂
    rfl
  have hencard : c.toSet.encard = {s : S | c.isCached s = true}.encard := by
    rw [← himg, hinj.encard_image]
  rw [hencard, Set.encard_eq_coe_toFinset_card, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [mul_one, mul_zero, add_zero, nsmul_eq_mul]
  rw [Set.toFinset_setOf]
  norm_cast

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq O] in
/-- **Domain-invariance of the collision probability.** The generalized collision experiment reads
the starting cache only through its domain (`isCached`): on the good path cached values are never
inspected, and on a hit the bad event has already fired. Hence two caches with the same domain give
the same collision probability. -/
private lemma probOutput_genCollisionExp_eq_of_isCached_agree (N : ℕ) (s : S)
    (c c' : (S →ₒ S × O).QueryCache) (h : ∀ x, c.isCached x = c'.isCached x) :
    Pr[= true | genCollisionExp N s c] = Pr[= true | genCollisionExp N s c'] := by
  induction N generalizing s c c' with
  | zero => simp [genCollisionExp]
  | succ N ih =>
    cases hc : c.isCached s with
    | true =>
      rw [probOutput_genCollisionExp_succ_of_isCached N s c hc,
        probOutput_genCollisionExp_succ_of_isCached N s c' (by rw [← h s]; exact hc)]
    | false =>
      have hc' : c'.isCached s = false := by rw [← h s]; exact hc
      have hcnone : c s = none := by simpa [QueryCache.isCached] using hc
      have hc'none : c' s = none := by simpa [QueryCache.isCached] using hc'
      rw [genCollisionExp_succ_of_none N s c hcnone,
        genCollisionExp_succ_of_none N s c' hc'none,
        probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine tsum_congr fun p => ?_
      congr 1
      refine ih p.1 (c.cacheQuery s p) (c'.cacheQuery s p) fun x => ?_
      by_cases hx : x = s
      · subst hx; simp
      · rw [QueryCache.isCached_cacheQuery_of_ne c p hx,
          QueryCache.isCached_cacheQuery_of_ne c' p hx]
        exact h x

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq S] [DecidableEq O] in
/-- Sampling a pair uniformly and discarding the second coordinate is the same as sampling the
first coordinate uniformly. -/
private lemma probOutput_bind_uniformSample_prod_fst (f : S → ProbComp Bool) (b : Bool) :
    Pr[= b | (do let p ← $ᵗ (S × O); f p.1)] = Pr[= b | (do let s' ← $ᵗ S; f s')] := by
  have heq : (do let p ← $ᵗ (S × O); f p.1) = (do let a ← $ᵗ S; let _ ← $ᵗ O; f a) := by
    rw [uniformSample_prod_eq_bind]
    simp only [bind_assoc, pure_bind]
  rw [heq, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun a => ?_
  congr 1
  rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]

omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq O] in
/-- **Generalized averaged birthday bound.** Averaging over the uniform initial state, the
generalized collision probability of the length-`N` chain starting from cache `c` is bounded by
`∑_{j < N} (|c| + j) / |S|`. Proved by induction on `N` (generalizing `c`): a cache miss draws a
fresh uniform state, growing the cache by one and shifting the bound; the union over already-cached
states contributes the leading `|c| / |S|` term. -/
private lemma probOutput_genCollisionExp_bind_le (N : ℕ) (c : (S →ₒ S × O).QueryCache) :
    Pr[= true | (do let s ← $ᵗ S; genCollisionExp N s c)] ≤
      ∑ j ∈ Finset.range N, (QueryCache.enncard c + (j : ℝ≥0∞)) * (Fintype.card S : ℝ≥0∞)⁻¹ := by
  induction N generalizing c with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, nonpos_iff_eq_zero]
    rw [probOutput_bind_eq_tsum]
    simp [genCollisionExp]
  | succ N ih =>
    set C : ℝ≥0∞ := (Fintype.card S : ℝ≥0∞) with hC
    have hCne : C ≠ 0 := by
      rw [hC]; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hCtop : C ≠ ⊤ := by rw [hC]; exact ENNReal.natCast_ne_top _
    have hCcancel : C * C⁻¹ = 1 := ENNReal.mul_inv_cancel hCne hCtop
    set B : ℝ≥0∞ := ∑ j ∈ Finset.range N, (QueryCache.enncard c + 1 + (j : ℝ≥0∞)) * C⁻¹ with hB
    -- Termwise bound on the per-state collision probability.
    have hterm : ∀ s : S, Pr[= true | genCollisionExp (N + 1) s c] ≤
        (if c.isCached s then (1 : ℝ≥0∞) else 0) + B := by
      intro s
      cases hcs : c.isCached s with
      | true =>
        rw [probOutput_genCollisionExp_succ_of_isCached N s c hcs, if_pos rfl]
        exact le_self_add
      | false =>
        rw [if_neg (by simp), zero_add]
        have hcnone : c s = none := by simpa [QueryCache.isCached] using hcs
        rw [genCollisionExp_succ_of_none N s c hcnone]
        -- Replace each fresh cache value by a fixed one (domain invariance), then drop the
        -- unused output coordinate.
        have hdom :
            Pr[= true | (($ᵗ (S × O)) >>= fun p => genCollisionExp N p.1 (c.cacheQuery s p))]
              = Pr[= true | (($ᵗ (S × O)) >>= fun p =>
                  genCollisionExp N p.1 (c.cacheQuery s (default, default)))] := by
          rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
          refine tsum_congr fun p => ?_
          congr 1
          refine probOutput_genCollisionExp_eq_of_isCached_agree N p.1 _ _ fun x => ?_
          by_cases hx : x = s
          · subst hx; simp
          · rw [QueryCache.isCached_cacheQuery_of_ne c p hx,
              QueryCache.isCached_cacheQuery_of_ne c (default, default) hx]
        rw [hdom, probOutput_bind_uniformSample_prod_fst
          (fun s' => genCollisionExp N s' (c.cacheQuery s (default, default))) true]
        refine le_trans (ih (c.cacheQuery s (default, default))) (le_of_eq ?_)
        rw [hB]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [enncard_cacheQuery_of_none c s (default, default) hcnone]
    calc Pr[= true | (do let s ← $ᵗ S; genCollisionExp (N + 1) s c)]
        = ∑ s : S, Pr[= s | ($ᵗ S)] * Pr[= true | genCollisionExp (N + 1) s c] :=
          probOutput_bind_eq_sum_fintype _ _ true
      _ ≤ ∑ s : S, Pr[= s | ($ᵗ S)] * ((if c.isCached s then (1 : ℝ≥0∞) else 0) + B) := by
          refine Finset.sum_le_sum fun s _ => ?_
          exact mul_le_mul_of_nonneg_left (hterm s) (by simp)
      _ = QueryCache.enncard c * C⁻¹ + B := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          congr 1
          · rw [enncard_eq_sum_isCached, Finset.sum_mul]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [probOutput_uniformSample, ← hC, mul_comm]
          · simp_rw [probOutput_uniformSample, ← hC, ← Finset.sum_mul]
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hC, hCcancel, one_mul]
      _ = ∑ j ∈ Finset.range (N + 1), (QueryCache.enncard c + (j : ℝ≥0∞)) * C⁻¹ := by
          rw [Finset.sum_range_succ', hB]
          rw [Nat.cast_zero, add_zero]
          rw [add_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast
          ring_nf

omit [DecidableEq O] in
/-- **Birthday bound for the state-collision probability.** Over `n` rounds of the lazy random
oracle chain, each freshly sampled state is uniform over `S`, so the probability that the chain
revisits a state is at most `n·(n-1) / (2·|S|)` by a union bound over the at most `C(n,2)` pairs. -/
theorem collisionProb_le_birthday (n : ℕ) :
    collisionProb (S := S) (O := O) n ≤ ((n * (n - 1) : ℕ) : ℝ) / (2 * Fintype.card S) := by
  -- The collision probability equals the empty-cache averaged collision probability.
  have hseed : ∀ seed : S,
      genCollisionExp (O := O) n seed ∅ = seedCollisionExp (O := O) n seed := by
    intro seed
    unfold genCollisionExp seedCollisionExp
    refine bind_congr fun states => ?_
    simp [QueryCache.isCached_empty]
  have hcomp : ((do let s ← $ᵗ S; genCollisionExp (O := O) n s ∅) : ProbComp Bool) =
      idealCollisionExp (S := S) (O := O) n := by
    rw [idealCollisionExp_eq_bind]
    exact bind_congr hseed
  -- Bound the ENNReal collision probability by the Gauss sum, then collapse it.
  have hbound : Pr[= true | idealCollisionExp (S := S) (O := O) n] ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * (Fintype.card S : ℝ≥0∞)) := by
    rw [← hcomp]
    refine le_trans (probOutput_genCollisionExp_bind_le n ∅) (le_of_eq ?_)
    simp only [QueryCache.enncard_empty, zero_add]
    exact ENNReal.gauss_sum_inv_eq n (Fintype.card S : ℝ≥0∞)
  -- Convert the ENNReal bound to a real bound.
  have hden : (2 * (Fintype.card S : ℝ≥0∞)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [collisionProb]
  refine le_trans (ENNReal.toReal_mono
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden) hbound) (le_of_eq ?_)
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  norm_num

omit [DecidableEq O] in
/-- **Concrete security of the stream PRG.** The PRG distinguishing advantage is bounded by the
PRF advantage of the reduction plus the birthday term `n·(n-1) / (2·|S|)`, obtained by combining
`security` with `collisionProb_le_birthday`. -/
theorem security_birthday
    (hkey : 𝒟[prf.keygen] = 𝒟[$ᵗ K])
    (adv : PRGAdversary (List.Vector O n)) :
    PRGScheme.prgAdvantage (streamPRG prf n) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction (S := S) (O := O) n adv) +
      ((n * (n - 1) : ℕ) : ℝ) / (2 * Fintype.card S) := by
  refine (security hkey adv).trans ?_
  have := collisionProb_le_birthday (S := S) (O := O) n
  linarith

end streamPRG

end PRGfromPRF
