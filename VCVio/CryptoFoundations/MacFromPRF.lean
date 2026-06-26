/-
Copyright (c) 2026 Lacramioara Astefanoaei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacramioara Astefanoaei
-/

import VCVio.CryptoFoundations.PRF
import VCVio.CryptoFoundations.MacAlg
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.SimSemantics.Append
import ToMathlib.Control.StateT

/-!
# Deterministic MAC from a PRF

The standard construction of a message authentication code from a pseudorandom function
(Boneh-Shoup v0.6, §6.3; Katz-Lindell, Construction 4.3):

- `tag k m := pure (prf.eval k m)`
- `verify k m t := pure (t == prf.eval k m)`

## Main Definitions

- `PRFScheme.toMacAlg` — the derived MAC from a PRF.
- `PRFScheme.toMacAlg_perfectlyComplete` — honest tags always verify.

## Security (Boneh-Shoup Theorem 6.2)

- `PRFScheme.macToPRFReduction` — the PRF distinguisher constructed from a UF-CMA forger.
- `PRFScheme.prf_implies_uf_cma` — PRF security implies UF-CMA security:
  `UF_CMA_Advantage(A) ≤ prfAdvantage(prf, B) + 1/|R|`.

## References

- [Boneh, Shoup, *A Graduate Course in Applied Cryptography*, v0.6, §6.3]
  (https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf)
-/

open OracleComp OracleSpec ENNReal

namespace PRFScheme

variable {K D R : Type}

/-! ## Construction -/

/-- The deterministic MAC derived from a PRF: tagging is PRF evaluation,
verification recomputes and compares. -/
def toMacAlg [DecidableEq R] (prf : PRFScheme K D R) : MacAlg ProbComp D K R where
  keygen := prf.keygen
  tag k m := pure (prf.eval k m)
  verify k m t := pure (decide (t = prf.eval k m))

/-- The derived MAC is perfectly complete: an honestly generated tag always verifies. -/
theorem toMacAlg_perfectlyComplete [DecidableEq R] (prf : PRFScheme K D R) :
    prf.toMacAlg.PerfectlyComplete ProbCompRuntime.probComp := by
  intro msg
  simp only [toMacAlg, pure_bind, decide_true]
  change Pr[= true | do let _ ← prf.keygen; pure true] = 1
  simp

/-! ## Security Reduction (Boneh-Shoup Theorem 6.2)

Given a UF-CMA forger `A` against `prf.toMacAlg`, we construct a PRF distinguisher `B`
(`macToPRFReduction A`) and prove:

    UF_CMA_Advantage(A) ≤ prfAdvantage(prf, B) + 1/|R|

The reduction forwards `A`'s tagging queries to its own PRF/random-function oracle while
logging them, then checks the forgery condition.

**Strong vs weak UF-CMA.** Boneh-Shoup's Attack Game 6.1 checks that the forgery *pair*
`(m, t)` is fresh (strong UF-CMA). VCVio's `MacAlg.UF_CMA_Exp` checks only message
freshness (`!log.wasQueried msg`). For the deterministic MAC `prf.toMacAlg`, each message
has exactly one valid tag, so the two notions coincide.
-/

variable [DecidableEq D] [DecidableEq R]

/-- Query the `(D →ₒ R)` component of the PRF oracle spec. -/
private def prfFuncQuery (msg : D) :
    OracleComp (unifSpec + (D →ₒ R)) R :=
  (unifSpec + (D →ₒ R)).query (Sum.inr msg)

/-- Oracle implementation for the reduction: forwards `unifSpec` queries transparently
and forwards `(D →ₒ R)` queries to the ambient oracle while logging them. -/
noncomputable def macToPRFQueryImpl :
    QueryImpl (unifSpec + (D →ₒ R))
      (WriterT (QueryLog (D →ₒ R)) (OracleComp (unifSpec + (D →ₒ R)))) :=
  let fwdTag : QueryImpl (D →ₒ R) (OracleComp (unifSpec + (D →ₒ R))) :=
    fun msg => prfFuncQuery msg
  (HasQuery.toQueryImpl (spec := unifSpec)
    (m := OracleComp (unifSpec + (D →ₒ R)))).liftTarget
      (WriterT (QueryLog (D →ₒ R)) (OracleComp (unifSpec + (D →ₒ R)))) +
  fwdTag.withLogging

/-- The PRF distinguisher constructed from a UF-CMA forger. Runs the forger with
logged-and-forwarded oracles, then verifies the forgery via one additional oracle query.
If the forger makes Q tagging queries, the reduction makes Q + 1 oracle queries total;
this can be tracked separately via `IsTotalQueryBound`. -/
noncomputable def macToPRFReduction (prf : PRFScheme K D R)
    (adversary : (prf.toMacAlg).UF_CMA_Adversary) :
    PRFAdversary D R :=
  ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) adversary.main).run >>=
    fun ((msg, τ), log) => prfFuncQuery msg >>= fun t =>
      pure (!QueryLog.wasQueried log msg && decide (τ = t)) :
    OracleComp (unifSpec + (D →ₒ R)) Bool)

/-- The UF-CMA oracle for `prf.toMacAlg` at key `k`, definitionally equal to the inline
query implementation in `MacAlg.UF_CMA_Exp`. Factored out so that the composition
`simulateQ (prfRealQueryImpl prf k) ∘ simulateQ macToPRFQueryImpl` can be identified
with it by `rfl`. -/
private def ufCmaImpl (prf : PRFScheme K D R) (k : K) :
    QueryImpl (unifSpec + (D →ₒ R))
      (WriterT (QueryLog (D →ₒ R)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (WriterT (QueryLog (D →ₒ R)) ProbComp) +
    (prf.toMacAlg).taggingOracle k

omit [DecidableEq D] in
/-- Composing the outer `prfRealQueryImpl` with the inner `macToPRFQueryImpl` gives exactly
the UF-CMA oracle (which uses `withLogging` over `pure ∘ prf.eval k`). -/
private theorem simulateQ_prfReal_macToPRFQueryImpl_run
    {α : Type} (prf : PRFScheme K D R) (k : K)
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) :
    simulateQ (prfRealQueryImpl prf k)
        ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) oa).run) =
      (simulateQ (ufCmaImpl prf k) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    simp only [simulateQ_pure, WriterT.run_pure]
  | query_bind t f ih =>
    simp only [simulateQ_bind, WriterT.run_bind']
    erw [simulateQ_bind]
    cases t <;>
      · simp only [macToPRFQueryImpl, ufCmaImpl, QueryImpl.add_apply_inl,
          QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply, QueryImpl.withLogging_apply,
          prfFuncQuery, toMacAlg, MacAlg.taggingOracle, simulateQ_spec_query,
          HasQuery.toQueryImpl_apply]
        erw [simulateQ_bind]
        refine bind_congr fun ⟨v, w⟩ => ?_
        rw [simulateQ_map]
        exact congrArg _ (ih v)

/-- The prfRealExp with the reduction equals the UF-CMA body as a `ProbComp` computation. -/
private theorem prfRealExp_macToPRFReduction_eq_body (prf : PRFScheme K D R)
    (adversary : (prf.toMacAlg).UF_CMA_Adversary) :
    prf.prfRealExp (macToPRFReduction prf adversary) = (do
      let k ← prf.keygen
      let ((msg, τ), log) ← (simulateQ (ufCmaImpl prf k) adversary.main).run
      pure (!QueryLog.wasQueried log msg && decide (τ = prf.eval k msg)) :
    ProbComp Bool) := by
  unfold prfRealExp macToPRFReduction
  refine bind_congr fun k => ?_
  rw [simulateQ_bind, simulateQ_prfReal_macToPRFQueryImpl_run prf k]
  refine bind_congr fun x => ?_
  erw [simulateQ_bind, simulateQ_prfRealQueryImpl_inr, pure_bind, simulateQ_pure]

/-- In the real PRF experiment, the reduction reproduces exactly the UF-CMA game. -/
theorem prfRealExp_macToPRFReduction_eq_UF_CMA_Exp (prf : PRFScheme K D R)
    (adversary : (prf.toMacAlg).UF_CMA_Adversary) :
    Pr[= true | prf.prfRealExp (macToPRFReduction prf adversary)] =
      MacAlg.UF_CMA_Advantage ProbCompRuntime.probComp adversary := by
  rw [prfRealExp_macToPRFReduction_eq_body]
  rfl

/-- The ideal experiment decomposes as: run the forger (under the random-oracle simulation
producing a log and cache), then perform one final random-oracle query and check the forgery.

This is the ideal-world analogue of `prfRealExp_macToPRFReduction_eq_body`. -/
private theorem prfIdealExp_macToPRFReduction_eq_ideal_body [SampleableType R]
    (prf : PRFScheme K D R)
    (adversary : (prf.toMacAlg).UF_CMA_Adversary) :
    prfIdealExp (macToPRFReduction prf adversary) =
      ((simulateQ prfIdealQueryImpl
        ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) adversary.main).run)).run ∅ >>=
      fun (((msg, τ), log), cache) =>
        ((D →ₒ R).randomOracle msg).run cache >>= fun (t, _) =>
          (pure (!QueryLog.wasQueried log msg && decide (τ = t)) : ProbComp Bool)) := by
  unfold prfIdealExp macToPRFReduction
  rw [simulateQ_bind]
  simp only [StateT.run'_bind']
  refine bind_congr fun ⟨⟨⟨msg, τ⟩, log⟩, cache⟩ => ?_
  rw [simulateQ_bind]
  simp only [prfFuncQuery]
  erw [simulateQ_prfIdealQueryImpl_inr]
  simp

/-- Inductive step of `log_cache_invariant_aux` for a `unifSpec` query: the uniform
query never touches the `(D →ₒ R)` cache, so the invariant is inherited from the
continuation via the inductive hypothesis `ih`. -/
private theorem log_cache_invariant_step_unif [SampleableType R]
    {α : Type} (msg : D) (cache₀ : (D →ₒ R).QueryCache)
    (z : (α × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache) (hcache : z.2 msg ≠ none)
    (n : ℕ) (f : (unifSpec + (D →ₒ R)).Range (Sum.inl n) → OracleComp (unifSpec + (D →ₒ R)) α)
    (ih : ∀ (u : (unifSpec + (D →ₒ R)).Range (Sum.inl n)) (cache₀ : (D →ₒ R).QueryCache),
      ∀ z ∈ support
        ((simulateQ prfIdealQueryImpl (simulateQ macToPRFQueryImpl (f u)).run).run cache₀),
        z.2 msg ≠ none → cache₀ msg ≠ none ∨ QueryLog.wasQueried z.1.2 msg = true)
    (hmem : z ∈ support ((simulateQ prfIdealQueryImpl
      (simulateQ macToPRFQueryImpl (liftM (OracleSpec.query (Sum.inl n)) >>= f)).run).run cache₀)) :
    cache₀ msg ≠ none ∨ QueryLog.wasQueried z.1.2 msg = true := by
  simp only [simulateQ_bind, macToPRFQueryImpl, WriterT.run_bind', simulateQ_spec_query,
    QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
    StateT.run_bind] at hmem
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨⟨⟨val, log_q⟩, cache_mid⟩, hu, hmem⟩ := hmem
  erw [simulateQ_bind, simulateQ_spec_query] at hu
  simp only [monadLift_self, StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hu
  obtain ⟨⟨u, s⟩, hq, hc⟩ := hu
  simp only [Function.comp] at hc
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
  erw [StateT.run_monadLift] at hq
  simp only [support_bind, Set.mem_iUnion,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hq
  obtain ⟨_, _, rfl, hcache_eq⟩ := hq
  dsimp only [Prod.fst, Prod.snd] at hmem
  simp only [show ∀ x : QueryLog (D →ₒ R), ∅ ++ x = x from List.nil_append,
    show (Prod.map (@id α) fun x : QueryLog (D →ₒ R) => x) = id from
      funext fun ⟨_, _⟩ => rfl, id_map] at hmem
  exact hcache_eq ▸ ih val cache_mid z hmem hcache

/-- Inductive step of `log_cache_invariant_aux` for a `(D →ₒ R)` query: forwarding the
query through `macToPRFQueryImpl` logs `msg'`. If the tracked point `msg` equals `msg'`
it is now in the log; otherwise the query leaves `cache_mid msg` unchanged and the
invariant is inherited from the continuation via the inductive hypothesis `ih`. -/
private theorem log_cache_invariant_step_query [SampleableType R]
    {α : Type} (msg : D) (cache₀ : (D →ₒ R).QueryCache)
    (z : (α × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache) (hcache : z.2 msg ≠ none)
    (msg' : D) (f : (unifSpec + (D →ₒ R)).Range (Sum.inr msg') → OracleComp (unifSpec + (D →ₒ R)) α)
    (ih : ∀ (u : (unifSpec + (D →ₒ R)).Range (Sum.inr msg')) (cache₀ : (D →ₒ R).QueryCache),
      ∀ z ∈ support
        ((simulateQ prfIdealQueryImpl (simulateQ macToPRFQueryImpl (f u)).run).run cache₀),
        z.2 msg ≠ none → cache₀ msg ≠ none ∨ QueryLog.wasQueried z.1.2 msg = true)
    (hmem : z ∈ support ((simulateQ prfIdealQueryImpl (simulateQ macToPRFQueryImpl
      (liftM (OracleSpec.query (Sum.inr msg')) >>= f)).run).run cache₀)) :
    cache₀ msg ≠ none ∨ QueryLog.wasQueried z.1.2 msg = true := by
  simp only [simulateQ_bind, macToPRFQueryImpl, prfFuncQuery, WriterT.run_bind',
    simulateQ_spec_query, QueryImpl.add_apply_inr, StateT.run_bind] at hmem
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨⟨⟨val, log_q⟩, cache_mid⟩, hro, hmem⟩ := hmem
  dsimp only [Prod.fst, Prod.snd] at hmem
  rw [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hmem
  obtain ⟨⟨⟨res, inner_log⟩, inner_cache⟩, hinner, rfl⟩ := hmem
  simp only [Prod.map, id]
  erw [QueryImpl.run_withLogging_apply] at hro
  erw [simulateQ_bind] at hro
  by_cases heq : msg = msg'
  · subst heq; right
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hro
    obtain ⟨⟨_, _⟩, _, ⟨⟨rfl, rfl⟩, _⟩⟩ := hro
    exact QueryLog.wasQueried_cons_self
  · simp only [StateT.run_bind] at hro
    erw [simulateQ_prfIdealQueryImpl_inr] at hro
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hro
    obtain ⟨⟨q_val, q_cache⟩, hro_q, hmem2⟩ := hro
    dsimp only at hmem2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hmem2
    rw [randomOracle.apply_eq] at hro_q
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hro_q
    have hcache_mid_eq : cache_mid msg = cache₀ msg := by
      rcases hc : cache₀ msg' with _ | u₀
      · simp only [hc, StateT.run_bind, StateT.run_monadLift, StateT.run_modifyGet,
          support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hro_q
        obtain ⟨i, ⟨_, _, hi⟩, _, hcm⟩ := hro_q
        subst hi; dsimp only [Prod.fst, Prod.snd] at hcm
        rw [hcm]
        simp [heq]
      · simp only [hc, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hro_q
        rw [hro_q.2]
    rcases ih val cache_mid ((res, inner_log), inner_cache) hinner hcache with hinv | hinv
    · left; rwa [hcache_mid_eq] at hinv
    · right
      simp only [List.singleton_append] at *
      rw [QueryLog.wasQueried_cons_of_ne (Ne.symm heq)]
      exact hinv

/-- Generalized log-cache invariant for arbitrary initial cache. Every domain point
cached in the final state was either already cached initially, or was logged. -/
private theorem log_cache_invariant_aux [SampleableType R]
    {α : Type}
    (oa : OracleComp (unifSpec + (D →ₒ R)) α)
    (cache₀ : (D →ₒ R).QueryCache)
    (z : (α × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache)
    (hmem : z ∈ support
      ((simulateQ prfIdealQueryImpl
        ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) oa).run)).run cache₀))
    (msg : D) (hcache : z.2 msg ≠ none) :
    cache₀ msg ≠ none ∨ QueryLog.wasQueried z.1.2 msg = true := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure x =>
    simp only [simulateQ_pure, WriterT.run_pure'] at hmem
    subst hmem; exact Or.inl hcache
  | query_bind t f ih =>
    cases t with
    | inl n => exact log_cache_invariant_step_unif msg cache₀ z hcache n f ih hmem
    | inr msg' => exact log_cache_invariant_step_query msg cache₀ z hcache msg' f ih hmem

/-- **Log-cache invariant**: every domain point cached by the random oracle was
also logged by `macToPRFQueryImpl`. This holds because `macToPRFQueryImpl` logs
every `(D →ₒ R)` query as part of forwarding it, and forwarding is the only path
that populates the cache. -/
private theorem log_cache_invariant [SampleableType R]
    (adversary_main : OracleComp (unifSpec + (D →ₒ R)) (D × R))
    (state : (((D × R) × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache))
    (hmem : state ∈ support
      ((simulateQ prfIdealQueryImpl
        ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) adversary_main).run)).run ∅))
    (msg : D) (hcache : state.2 msg ≠ none) :
    QueryLog.wasQueried state.1.2 msg = true := by
  simpa [QueryCache.empty_apply] using
    log_cache_invariant_aux adversary_main ∅ state hmem msg hcache

/-- The `ℝ≥0∞`-valued core of `prfIdealExp_macToPRFReduction_le`: in the ideal PRF
experiment, the reduction outputs `true` with probability at most `1/|R|`. A fresh
random-oracle query on `msg` returns a uniform `t ← $ᵗ R` independent of the forger's
claimed tag `τ`, so `Pr[τ = t] = 1/|R|`; if `msg` was already queried the output is
`false`. -/
private theorem prfIdealExp_macToPRFReduction_probOutput_le [SampleableType R] [Fintype R]
    (prf : PRFScheme K D R) (adversary : (prf.toMacAlg).UF_CMA_Adversary) :
    Pr[= true | prfIdealExp (macToPRFReduction prf adversary)] ≤
      (Fintype.card R : ℝ≥0∞)⁻¹ := by
  rw [prfIdealExp_macToPRFReduction_eq_ideal_body, probOutput_bind_eq_tsum]
  calc ∑' x : (((D × R) × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache),
        Pr[= x | (simulateQ prfIdealQueryImpl
          ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) adversary.main).run)).run ∅] *
        Pr[= true | ((D →ₒ R).randomOracle x.1.1.1).run x.2 >>= fun (t, _) =>
          (pure (!QueryLog.wasQueried x.1.2 x.1.1.1 && decide (x.1.1.2 = t)) : ProbComp Bool)]
      ≤ ∑' x, Pr[= x | (simulateQ prfIdealQueryImpl
          ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) adversary.main).run)).run ∅] *
        (Fintype.card R : ℝ≥0∞)⁻¹ := by
        refine ENNReal.tsum_le_tsum fun ⟨((msg, τ), log), cache⟩ => ?_
        by_cases hmem : (((msg, τ), log), cache) ∈ support
            ((simulateQ prfIdealQueryImpl
              ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) adversary.main).run)).run ∅)
        · refine mul_le_mul' le_rfl ?_
          cases hcache : cache msg with
          | some v =>
            simp only [randomOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind, hcache,
              StateT.run_pure, log_cache_invariant adversary.main (((msg, τ), log), cache) hmem msg
                (by change cache msg ≠ none; rw [hcache]; exact Option.some_ne_none _),
              probOutput_pure]
            exact zero_le
          | none =>
            rw [show ((D →ₒ R).randomOracle msg).run cache =
                (fun u => (u, cache.cacheQuery msg u)) <$> ($ᵗ R) from
              QueryImpl.withCaching_run_none _ hcache]
            simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
            rw [probOutput_bind_eq_tsum]
            simp only [probOutput_uniformSample, probOutput_pure, mul_ite, mul_one, mul_zero]
            set c := (Fintype.card R : ℝ≥0∞)⁻¹
            calc ∑' t, (if (true : Bool) = (!log.wasQueried msg && decide (τ = t))
                    then c else 0)
                ≤ ∑' t, (if t = τ then c else 0) :=
                  ENNReal.tsum_le_tsum fun t => by
                    split_ifs with h1 h2
                    · exact le_rfl
                    · simp only [Bool.true_eq, Bool.and_eq_true, decide_eq_true_eq] at h1
                      exact absurd h1.2.symm h2
                    all_goals exact zero_le
              _ = c := tsum_ite_eq τ (fun _ => c)
        · simp [probOutput_eq_zero_of_not_mem_support hmem]
    _ ≤ (Fintype.card R : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left zero_le' tsum_probOutput_le_one

/-- In the ideal PRF experiment (random oracle), the reduction succeeds with probability
at most `1/|R|` — a fresh random oracle query is independent of the forger's output. -/
theorem prfIdealExp_macToPRFReduction_le [Nonempty R] [SampleableType R] [Fintype R]
    (prf : PRFScheme K D R)
    (adversary : (prf.toMacAlg).UF_CMA_Adversary) :
    (Pr[= true | prfIdealExp (macToPRFReduction prf adversary)]).toReal ≤
      (Fintype.card R : ℝ)⁻¹ := by
  rw [show (Fintype.card R : ℝ)⁻¹ = ((Fintype.card R : ℝ≥0∞)⁻¹).toReal by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]]
  exact (ENNReal.toReal_le_toReal probOutput_ne_top (by simp)).mpr
    (prfIdealExp_macToPRFReduction_probOutput_le prf adversary)

/-- **Boneh-Shoup Theorem 6.2.** PRF security implies UF-CMA security for the derived MAC:
for any forger `A`, the constructed distinguisher `macToPRFReduction prf A` satisfies
`UF_CMA_Advantage(A) ≤ prfAdvantage(prf, B) + 1/|R|`. -/
theorem prf_implies_uf_cma [Nonempty R] [SampleableType R] [Fintype R]
    (prf : PRFScheme K D R) (adversary : (prf.toMacAlg).UF_CMA_Adversary) :
    (MacAlg.UF_CMA_Advantage ProbCompRuntime.probComp adversary).toReal ≤
      prf.prfAdvantage (macToPRFReduction prf adversary) +
        (Fintype.card R : ℝ)⁻¹ := by
  rw [← prfRealExp_macToPRFReduction_eq_UF_CMA_Exp prf adversary]
  unfold prfAdvantage
  set a := (Pr[= true | prf.prfRealExp (macToPRFReduction prf adversary)]).toReal
  set b := (Pr[= true | prfIdealExp (macToPRFReduction prf adversary)]).toReal
  linarith [le_abs_self (a - b), prfIdealExp_macToPRFReduction_le prf adversary]

end PRFScheme
