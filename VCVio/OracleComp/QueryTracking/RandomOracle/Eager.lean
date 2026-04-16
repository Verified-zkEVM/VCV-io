/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.Constructions.GenerateSeed

/-!
# Eager Random Oracle

The eager random oracle serves answers from a pre-generated `QuerySeed`, consuming values
sequentially and falling back to fresh uniform sampling when exhausted. Different calls to
the same oracle consume different seed values. State: `QuerySeed`.

This gives INDEPENDENT samples (each call consumes a different seed value), unlike
`randomOracle` which gives CONSISTENT samples (same input → same output via caching).
When averaged over a uniformly sampled seed, the eager version matches the fresh
independent-query semantics of `evalDist`.
-/

open OracleComp OracleSpec

universe u v w

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}

/-- The eager random oracle: serves answers from a pre-generated `QuerySeed`, consuming
seed values sequentially and falling back to fresh uniform sampling when exhausted.

Concretely, on query `t`:
- If `seed t` is non-empty, return the head and advance to the tail.
- If `seed t` is empty, sample `$ᵗ spec.Range t` uniformly and leave the seed unchanged.

**Important**: This gives INDEPENDENT samples (each call consumes a different seed value),
unlike `randomOracle` which gives CONSISTENT samples (same input → same output via caching).
The two models agree when no oracle index is queried more than once.

This is definitionally equal to `uniformSampleImpl.withPregen` (from `SeededOracle.lean`). -/
@[inline, reducible] def eagerRandomOracle {ι} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t : spec.Domain, SampleableType (spec.Range t)] :
    QueryImpl spec (StateT (QuerySeed spec) ProbComp) :=
  fun t => StateT.mk fun seed =>
    match seed t with
    | u :: us => pure (u, Function.update seed t us)
    | [] => (·, seed) <$> ($ᵗ spec.Range t)

namespace eagerRandomOracle

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

lemma apply_eq (t : spec₀.Domain) :
    (eagerRandomOracle (spec := spec₀)) t = StateT.mk fun seed =>
      match seed t with
      | u :: us => pure (u, Function.update seed t us)
      | [] => (·, seed) <$> ($ᵗ spec₀.Range t) := rfl

/-- With an empty seed, the eager random oracle reduces to `uniformSampleImpl`:
every query falls through to fresh uniform sampling with no state change.
This is a faithful simulation (preserves `evalDist`). -/
theorem evalDist_simulateQ_run'_empty [spec₀.Fintype] [spec₀.Inhabited]
    {α : Type} (oa : OracleComp spec₀ α) :
    evalDist ((simulateQ (eagerRandomOracle (spec := spec₀)) oa).run' ∅) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure, evalDist_pure]
  | query_bind t f ih =>
    rw [simulateQ_bind,
      show simulateQ eagerRandomOracle (liftM (query t)) = eagerRandomOracle t by
        rw [simulateQ_query]; simp [OracleQuery.cont_query, OracleQuery.input_query, id_map],
      evalDist_query_bind]
    have hsimp : (eagerRandomOracle t >>= fun u =>
        simulateQ eagerRandomOracle (f u)).run' (∅ : QuerySeed spec₀) =
        $ᵗ spec₀.Range t >>= fun u => (simulateQ eagerRandomOracle (f u)).run' ∅ := by
      change Prod.fst <$> ((eagerRandomOracle t).run ∅ >>= fun p =>
          (simulateQ eagerRandomOracle (f p.1)).run p.2) =
        $ᵗ spec₀.Range t >>= fun u => Prod.fst <$> (simulateQ eagerRandomOracle (f u)).run ∅
      have h : (eagerRandomOracle t).run (∅ : QuerySeed spec₀) =
          (fun u => (u, (∅ : QuerySeed spec₀))) <$> ($ᵗ spec₀.Range t) := by
        simp [eagerRandomOracle, StateT.mk, StateT.run]
      rw [h]; simp [map_bind, bind_map_left]
    rw [hsimp, evalDist_bind]
    congr 1
    · exact evalDist_uniformSample (spec₀.Range t)
    · funext u; exact ih u

end eagerRandomOracle

/-- Helper: the `run'` of the eager oracle bind reduces to uniform sampling
when `seed t = []`. -/
private lemma eagerRandomOracle_run'_nil {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]
    {α : Type} (t : spec₀.Domain) (f : spec₀.Range t → OracleComp spec₀ α)
    (seed : QuerySeed spec₀) (ht : seed t = []) :
    (eagerRandomOracle t >>= fun u => simulateQ eagerRandomOracle (f u)).run' seed =
    ($ᵗ spec₀.Range t) >>= fun u => (simulateQ eagerRandomOracle (f u)).run' seed := by
  change Prod.fst <$> ((eagerRandomOracle t).run seed >>= fun p =>
      (simulateQ eagerRandomOracle (f p.1)).run p.2) = _
  have h : (eagerRandomOracle (spec := spec₀) t).run seed =
      (fun u => (u, seed)) <$> ($ᵗ spec₀.Range t) := by
    change (match seed t with
        | v :: vs => pure (v, Function.update seed t vs)
        | [] => (·, seed) <$> ($ᵗ spec₀.Range t)) = _
    rw [ht]
  rw [h]; simp [map_bind, bind_map_left]

/-- Helper: the `run'` of the eager oracle bind consumes the head
when `seed t = u :: us`. -/
private lemma eagerRandomOracle_run'_cons {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]
    {α : Type} (t : spec₀.Domain) (f : spec₀.Range t → OracleComp spec₀ α)
    (seed : QuerySeed spec₀) (u : spec₀.Range t) (us : List (spec₀.Range t))
    (ht : seed t = u :: us) :
    (eagerRandomOracle t >>= fun v => simulateQ eagerRandomOracle (f v)).run' seed =
    (simulateQ eagerRandomOracle (f u)).run' (Function.update seed t us) := by
  change Prod.fst <$> ((eagerRandomOracle t).run seed >>= fun p =>
      (simulateQ eagerRandomOracle (f p.1)).run p.2) = _
  have h : (eagerRandomOracle (spec := spec₀) t).run seed =
      pure (u, Function.update seed t us) := by
    change (match seed t with
        | v :: vs => pure (v, Function.update seed t vs)
        | [] => (·, seed) <$> ($ᵗ spec₀.Range t)) = _
    rw [ht]
  rw [h]; rfl

/-- The eager random oracle, averaged over a uniformly sampled seed, matches the
fresh independent-query semantics of `evalDist`. This is because the pre-sampled
seed values are i.i.d. uniform, exactly matching fresh oracle queries.

This is the analog of `seededOracle.evalDist_liftComp_generateSeed_bind_simulateQ_run'`
but for `eagerRandomOracle` (which falls back to `ProbComp` rather than `OracleComp spec`). -/
theorem eagerRandomOracle_evalDist_generateSeed_bind {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀}
    [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]
    [spec₀.Fintype] [spec₀.Inhabited]
    {α : Type} (oa : OracleComp spec₀ α)
    (qc : ι₀ → ℕ) (js : List ι₀) :
    evalDist (do
      let seed ← generateSeed spec₀ qc js
      (simulateQ (eagerRandomOracle (spec := spec₀)) oa).run' seed) = evalDist oa := by
  classical
  revert qc js
  induction oa using OracleComp.inductionOn with
  | pure a => intro qc js; apply evalDist_ext; intro; simp
  | query_bind t f ih =>
    intro qc js; apply evalDist_ext; intro x
    have hsimQ : ∀ seed : QuerySeed spec₀,
        (simulateQ eagerRandomOracle (liftM (query t) >>= f)).run' seed =
        (eagerRandomOracle t >>= fun u => simulateQ eagerRandomOracle (f u)).run' seed :=
      fun _ => by congr 1
    simp_rw [hsimQ]
    rw [probOutput_bind_eq_tsum (liftM (query t)) f x]
    simp_rw [probOutput_query t]
    rw [probOutput_bind_eq_tsum]
    have hih : ∀ u, ∑' seed, Pr[= seed | generateSeed spec₀ qc js] *
        Pr[= x | (simulateQ eagerRandomOracle (f u)).run' seed] = Pr[= x | f u] := fun u => by
      rw [← probOutput_bind_eq_tsum]; exact congrFun (congrArg DFunLike.coe (ih u qc js)) x
    by_cases hcount : qc t * js.count t = 0
    · have hnil : ∀ seed ∈ support (generateSeed spec₀ qc js), seed t = [] :=
        fun s hs => eq_nil_of_mem_support_generateSeed spec₀ qc js s t hs hcount
      have hstep : ∀ seed,
          Pr[= seed | generateSeed spec₀ qc js] *
            Pr[= x | (eagerRandomOracle t >>= fun u =>
              simulateQ eagerRandomOracle (f u)).run' seed] =
          Pr[= seed | generateSeed spec₀ qc js] *
            (∑' u, (↑(Fintype.card (spec₀.Range t)))⁻¹ *
              Pr[= x | (simulateQ eagerRandomOracle (f u)).run' seed]) := by
        intro seed
        by_cases hs : seed ∈ support (generateSeed spec₀ qc js)
        · rw [eagerRandomOracle_run'_nil t f seed (hnil seed hs), probOutput_bind_eq_tsum]
          simp only [probOutput_uniformSample]
        · simp [(probOutput_eq_zero_iff _ _).mpr hs]
      simp_rw [hstep, ENNReal.tsum_mul_left, ← mul_assoc,
        mul_comm (Pr[= _ | generateSeed _ _ _]) _, mul_assoc, ENNReal.tsum_mul_left]
      congr 1
      simp_rw [← ENNReal.tsum_mul_left (a := Pr[= _ | generateSeed _ _ _])]
      rw [ENNReal.tsum_comm]; congr 1; ext u; exact hih u
    · have hpos : 0 < qc t * js.count t := Nat.pos_of_ne_zero (by omega)
      have hstep : ∀ seed,
          Pr[= seed | generateSeed spec₀ qc js] *
            Pr[= x | (eagerRandomOracle t >>= fun u =>
              simulateQ eagerRandomOracle (f u)).run' seed] =
          Pr[= seed | generateSeed spec₀ qc js] *
            (match seed t with
              | u :: us => Pr[= x | (simulateQ eagerRandomOracle (f u)).run'
                  (Function.update seed t us)]
              | [] => 0) := by
        intro seed
        by_cases hs : seed ∈ support (generateSeed spec₀ qc js)
        · obtain ⟨u, us, hc⟩ :=
            exists_cons_of_mem_support_generateSeed spec₀ qc js seed t hs hpos
          rw [eagerRandomOracle_run'_cons t f seed u us hc, hc]
        · simp [(probOutput_eq_zero_iff _ _).mpr hs]
      simp_rw [hstep]
      rw [← (QuerySeed.prependValues_singleton_injective t).tsum_eq (by
        intro seed hseed; simp only [Function.mem_support] at hseed
        have hmem : seed ∈ support (generateSeed spec₀ qc js) := by
          by_contra h; exact hseed (by simp [(probOutput_eq_zero_iff _ _).mpr h])
        obtain ⟨u, us, hc⟩ :=
          exists_cons_of_mem_support_generateSeed spec₀ qc js seed t hmem hpos
        exact ⟨(u, Function.update seed t us),
          QuerySeed.eq_prependValues_of_pop_eq_some
            (QuerySeed.pop_eq_some_of_cons seed t u us hc)⟩)]
      simp only [QuerySeed.prependValues, List.singleton_append,
        Function.update_self, Function.update_idem, Function.update_eq_self]
      rw [ENNReal.tsum_prod']; congr 1; ext u
      simp only [show ∀ b : QuerySeed spec₀,
          Function.update (u, b).2 t ((u, b).1 :: (u, b).2 t) = b.prependValues [u] from
        fun b => by simp [QuerySeed.prependValues]]
      simp_rw [probOutput_generateSeed_prependValues spec₀ qc js u _ hpos,
        mul_assoc, ENNReal.tsum_mul_left]
      congr 1; rw [← probOutput_bind_eq_tsum]
      exact congrFun (congrArg DFunLike.coe (ih u _ js.dedup)) x
