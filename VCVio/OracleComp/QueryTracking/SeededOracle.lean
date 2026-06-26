/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.Constructions.GenerateSeed
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.Structures

/-!
# Pre-computing Results of Oracle Queries

This file defines a function `QueryImpl.withPregen` that modifies a query implementation
to take in a list of pre-chosen outputs to use when answering queries.
Uses `StateT` so that consumed seed values are threaded to subsequent queries.

Note that ordering is subtle, for example `so.withCaching.withPregen` will first check for seeds
and not cache the result if one is found, while `so.withPregen.withCaching` checks the cache first,
and include seed values into the cache after returning them.
-/

open OracleComp OracleSpec

universe u v w

open scoped OracleSpec.PrimitiveQuery

variable {ι : Type u} {spec : OracleSpec ι} [DecidableEq ι]

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Modify a `QueryImpl` to check for pregenerated responses for oracle queries first.
If a seed value is available for the query, it is used and the seed is consumed (the tail
replaces the head). When no seed remains, falls back to the underlying implementation. -/
def withPregen (so : QueryImpl spec m) :
    QueryImpl spec (StateT (QuerySeed spec) m) :=
  fun t => StateT.mk fun seed =>
    match seed t with
    | u :: us => pure (u, Function.update seed t us)
    | [] => (·, seed) <$> so t

@[simp, grind =]
lemma withPregen_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withPregen t = StateT.mk fun seed =>
      match seed t with
      | u :: us => pure (u, Function.update seed t us)
      | [] => (·, seed) <$> so t := rfl

/-- Seed-hit: `withPregen` returns the head of the seed list without invoking `so`. -/
lemma withPregen_run_cons (so : QueryImpl spec m) {t : spec.Domain}
    {seed : QuerySeed spec} {u : spec.Range t} {us : List (spec.Range t)}
    (h : seed t = u :: us) :
    (so.withPregen t).run seed = pure (u, Function.update seed t us) := by
  rw [withPregen_apply, StateT.run_mk, h]
  rfl

/-- Seed-miss: `withPregen` falls back to a single call of `so`, threading the seed unchanged. -/
lemma withPregen_run_nil (so : QueryImpl spec m) {t : spec.Domain}
    {seed : QuerySeed spec} (h : seed t = []) :
    (so.withPregen t).run seed = (·, seed) <$> so t := by
  rw [withPregen_apply, StateT.run_mk, h]

/-! ## Forward query bounds for `withPregen`

A wrapped step makes ≤ 1 underlying query (zero on a seed-hit, one on a seed-miss), so any
bound on `so t` transfers to `(so.withPregen t).run seed`. -/

section QueryBound

variable {ι' : Type u} {spec' : OracleSpec ι'}

lemma isQueryBoundP_run_withPregen
    (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain)
    {p : ι' → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP (so t) p n) (seed : QuerySeed spec) :
    OracleComp.IsQueryBoundP ((so.withPregen t).run seed) p n := by
  cases hseed : seed t with
  | nil =>
      rw [withPregen_run_nil _ hseed]
      exact (OracleComp.isQueryBoundP_map_iff (p := p) _ _ _).mpr h
  | cons u us =>
      rw [withPregen_run_cons _ hseed]
      trivial

lemma isTotalQueryBound_run_withPregen
    (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain) {n : ℕ}
    (h : OracleComp.IsTotalQueryBound (so t) n) (seed : QuerySeed spec) :
    OracleComp.IsTotalQueryBound ((so.withPregen t).run seed) n := by
  cases hseed : seed t with
  | nil =>
      rw [withPregen_run_nil _ hseed]
      exact (OracleComp.isQueryBound_map_iff _ _ _ _ _).mpr h
  | cons u us =>
      rw [withPregen_run_cons _ hseed]
      trivial

lemma isPerIndexQueryBound_run_withPregen
    (so : QueryImpl spec (OracleComp spec)) (t : spec.Domain) {qb : ι → ℕ}
    (h : OracleComp.IsPerIndexQueryBound (so t) qb) (seed : QuerySeed spec) :
    OracleComp.IsPerIndexQueryBound ((so.withPregen t).run seed) qb := by
  cases hseed : seed t with
  | nil =>
      rw [withPregen_run_nil _ hseed]
      exact (OracleComp.isPerIndexQueryBound_map_iff _ _ _).mpr h
  | cons u us =>
      rw [withPregen_run_cons _ hseed]
      trivial

end QueryBound

end QueryImpl

/-! ### Parametric `simulateQ` lifts for `withPregen` -/

namespace OracleComp

variable {ι' : Type u} {spec' : OracleSpec ι'} {α : Type u}

theorem IsQueryBoundP.simulateQ_run_withPregen [IsUniformSpec spec']
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    (so : QueryImpl spec (OracleComp spec'))
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → IsQueryBoundP (so t) q 1)
    (hstep_np : ∀ t, ¬ p t → IsQueryBoundP (so t) q 0)
    (seed : QuerySeed spec) :
    IsQueryBoundP ((simulateQ so.withPregen oa).run seed) q n :=
  IsQueryBoundP.simulateQ_run_of_step h
    (fun t hp s' => QueryImpl.isQueryBoundP_run_withPregen so t (hstep_p t hp) s')
    (fun t hnp s' => QueryImpl.isQueryBoundP_run_withPregen so t (hstep_np t hnp) s')
    seed

theorem IsTotalQueryBound.simulateQ_run_withPregen [IsUniformSpec spec]
    (so : QueryImpl spec (OracleComp spec))
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep : ∀ t, IsTotalQueryBound (so t) 1)
    (seed : QuerySeed spec) :
    IsTotalQueryBound ((simulateQ so.withPregen oa).run seed) n :=
  IsTotalQueryBound.simulateQ_run_of_step h
    (fun t s' => QueryImpl.isTotalQueryBound_run_withPregen so t (hstep t) s')
    seed

theorem IsPerIndexQueryBound.simulateQ_run_withPregen
    (so : QueryImpl spec (OracleComp spec))
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep : ∀ t, IsPerIndexQueryBound (so t) (Function.update 0 t 1))
    (seed : QuerySeed spec) :
    IsPerIndexQueryBound ((simulateQ so.withPregen oa).run seed) qb :=
  IsPerIndexQueryBound.simulateQ_run_of_uniform_step h
    (fun t s' => QueryImpl.isPerIndexQueryBound_run_withPregen so t (hstep t) s')
    seed

end OracleComp

/-- Use pregenerated oracle responses for queries, falling back to the real oracle
when the seed is exhausted. Seed consumption is tracked via `StateT`. -/
def OracleSpec.seededOracle :
    QueryImpl spec (StateT (QuerySeed spec) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withPregen

namespace seededOracle

/-- Definitional unfold of `seededOracle` as the pregen handler over the lifting handler. -/
lemma eq_withPregen :
    (spec.seededOracle : QueryImpl spec (StateT (QuerySeed spec) (OracleComp spec))) =
      (QueryImpl.ofLift spec (OracleComp spec)).withPregen := rfl

/-- Seed-hit: `seededOracle t` returns the head of the seed list with no underlying query. -/
lemma run_cons {t : spec.Domain} {seed : QuerySeed spec} {u : spec.Range t}
    {us : List (spec.Range t)} (h : seed t = u :: us) :
    (seededOracle t).run seed = pure (u, Function.update seed t us) :=
  QueryImpl.withPregen_run_cons _ h

/-- Seed-miss: `seededOracle t` falls back to a single underlying `query t`. -/
lemma run_nil {t : spec.Domain} {seed : QuerySeed spec} (h : seed t = []) :
    (seededOracle t).run seed = (·, seed) <$> (liftM (query t) : OracleComp spec _) := by
  rw [eq_withPregen, QueryImpl.withPregen_run_nil _ h, QueryImpl.ofLift_apply]

/-- The probability that a lifted uniform sample equals a fixed value is `(card α)⁻¹`. -/
lemma probEvent_liftComp_uniformSample_eq_of_eq
    {ι : Type} {spec : OracleSpec ι}
    [(i : ι) → SampleableType (spec.Range i)]
    [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec]
    [IsUniformSpec spec]
    {i : ι} (u₀ : spec.Range i) :
    probEvent (liftComp (uniformSample (spec.Range i)) spec)
      (fun u => u₀ = u) =
      (↑(Fintype.card (spec.Range i)) : ENNReal)⁻¹ := by
  rw [probEvent_eq_eq_probOutput', probOutput_liftComp, probOutput_uniformSample]

@[simp]
lemma apply_eq (t : spec.Domain) :
    seededOracle t = StateT.mk fun seed =>
      match seed t with
      | u :: us => pure (u, Function.update seed t us)
      | [] => (·, seed) <$> OracleSpec.query t := rfl

lemma run_bind_query_eq_pop {α : Type u}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) (seed : QuerySeed spec) :
    (((seededOracle t) >>= fun u => simulateQ seededOracle (mx u)).run seed) =
      match seed.pop t with
      | none => do
          let u ← spec.query t
          (simulateQ seededOracle (mx u)).run seed
      | some (u, seed') =>
          (simulateQ seededOracle (mx u)).run seed' := by
  cases hst : seed t <;>
    simp [seededOracle.apply_eq, StateT.run_bind, QuerySeed.pop, hst]

/-- `run'` form of `run_bind_query_eq_pop`: querying `t` then continuing splits on `seed.pop t`,
either falling back to a fresh `query t` or consuming the popped head. -/
lemma run'_bind_query_eq_pop {α : Type u}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) (seed : QuerySeed spec) :
    (((seededOracle t) >>= fun u => simulateQ seededOracle (mx u)).run' seed) =
      match seed.pop t with
      | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' seed
      | some (u, s') => (simulateQ seededOracle (mx u)).run' s' := by
  change Prod.fst <$>
    (seededOracle t >>= fun u => simulateQ seededOracle (mx u)).run seed = _
  rw [run_bind_query_eq_pop]
  cases seed.pop t with
  | none => simp [map_bind]
  | some p => rfl

/-- For any weight `g`, the support of `s ↦ Pr[= s | generateSeed …] * g s` lands in the range
of `prependValues` with a single head value at `t`, provided `t` is queried at least once.
Used to reparametrize seed sums over `generateSeed` by a popped head value. -/
private lemma support_generateSeed_mul_subset_range_prependValues_aux {ι₀ : Type}
    {spec₀ : OracleSpec ι₀} [DecidableEq ι₀] [∀ i, SampleableType (spec₀.Range i)]
    [unifSpec ⊂ₒ spec₀] [unifSpec ˡ⊂ₒ spec₀] [IsUniformSpec spec₀]
    (qc : ι₀ → ℕ) (js : List ι₀) (t : ι₀) (hcount : 0 < qc t * js.count t)
    (g : QuerySeed spec₀ → ENNReal) :
    Function.support (fun s => Pr[= s | generateSeed spec₀ qc js] * g s) ⊆
      Set.range (fun (p : spec₀.Range t × QuerySeed spec₀) => p.2.prependValues [p.1]) := by
  intro s hs
  simp only [Function.mem_support] at hs
  have hmem : s ∈ support (generateSeed spec₀ qc js) := by
    by_contra hc; exact hs (by simp [(probOutput_eq_zero_iff _ _).2 hc])
  obtain ⟨u, us, hcons⟩ := List.exists_cons_of_ne_nil
    (ne_nil_of_mem_support_generateSeed (spec := spec₀) (qc := qc) (js := js) s t hmem hcount)
  exact ⟨(u, Function.update s t us),
    QuerySeed.eq_prependValues_of_pop_eq_some (QuerySeed.pop_eq_some_of_cons s t u us hcons)⟩

private lemma evalDist_liftComp_generateSeed_bind_simulateQ_run'
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [unifSpec ˡ⊂ₒ spec₀]
    [IsUniformSpec spec₀]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α : Type} (oa : OracleComp spec₀ α) :
    𝒟[(do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      (simulateQ seededOracle oa).run' seed : OracleComp spec₀ α)] =
    𝒟[oa] := by
  classical
  revert qc js
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro qc js
    apply evalDist_ext; intro a
    simp
  | query_bind t mx ih =>
    intro qc js
    have hrun' : ∀ s : QuerySeed spec₀,
        (do let u ← seededOracle t; simulateQ seededOracle (mx u) :
          StateT _ (OracleComp spec₀) α).run' s =
        match s.pop t with
        | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s
        | some (u, s') => (simulateQ seededOracle (mx u)).run' s' :=
      run'_bind_query_eq_pop t mx
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map]
    apply evalDist_ext; intro x
    simp_rw [hrun']
    rw [probOutput_bind_eq_tsum]
    simp_rw [probOutput_liftComp]
    by_cases hcount : qc t * js.count t = 0
    · have hpop : ∀ s ∈ support (generateSeed spec₀ qc js), s.pop t = none := by
        intro s hs; rw [QuerySeed.pop_eq_none_iff]
        rw [support_generateSeed (spec := spec₀)] at hs
        have hlen : (s t).length = qc t * js.count t := hs t
        exact List.eq_nil_of_length_eq_zero (hlen.trans hcount)
      have step1 : ∀ s,
          Pr[= s | generateSeed spec₀ qc js] *
            Pr[= x | match s.pop t with
              | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s'] =
          Pr[= s | generateSeed spec₀ qc js] *
            Pr[= x | liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s] := by
        intro s
        by_cases hs : s ∈ support (generateSeed spec₀ qc js)
        · simp [hpop s hs]
        · simp [(probOutput_eq_zero_iff _ _).2 hs]
      simp_rw [step1, probOutput_bind_eq_tsum (liftM (query t))]
      simp_rw [← ENNReal.tsum_mul_left, mul_left_comm]
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left]
      congr 1; ext u; congr 1
      have hih : Pr[= x | (liftComp (generateSeed spec₀ qc js) spec₀ >>= fun seed =>
          (simulateQ seededOracle (mx u)).run' seed)] = Pr[= x | mx u] :=
        congrFun (congrArg DFunLike.coe (ih u qc js)) x
      rw [probOutput_bind_eq_tsum] at hih
      simp_rw [probOutput_liftComp] at hih
      exact hih
    · push Not at hcount
      have hpop_some : ∀ s ∈ support (generateSeed spec₀ qc js),
          ∃ u s', s.pop t = some (u, s') := by
        intro s hs
        have hne : s t ≠ [] :=
          ne_nil_of_mem_support_generateSeed (spec := spec₀) (qc := qc) (js := js) s t hs
            (Nat.pos_of_ne_zero (by lia))
        obtain ⟨u, us, hcons⟩ := List.exists_cons_of_ne_nil hne
        exact ⟨u, Function.update s t us, QuerySeed.pop_eq_some_of_cons s t u us hcons⟩
      have step1 : ∀ s,
          Pr[= s | generateSeed spec₀ qc js] *
            Pr[= x | match s.pop t with
              | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s'] =
          Pr[= s | generateSeed spec₀ qc js] *
            (match s.pop t with
              | none => 0
              | some (u, s') =>
                  Pr[= x | (simulateQ seededOracle (mx u)).run' s']) := by
        intro s
        by_cases hs : s ∈ support (generateSeed spec₀ qc js)
        · obtain ⟨u, s', hpop⟩ := hpop_some s hs; simp [hpop]
        · simp [(probOutput_eq_zero_iff _ _).2 hs]
      simp_rw [step1]
      have hpos : 0 < qc t * js.count t := Nat.pos_of_ne_zero (by lia)
      rw [← (QuerySeed.prependValues_singleton_injective t).tsum_eq
        (support_generateSeed_mul_subset_range_prependValues_aux qc js t hpos _)]
      simp only [QuerySeed.pop_prependValues_singleton]
      rw [ENNReal.tsum_prod', probOutput_bind_eq_tsum]
      congr 1; ext u
      have hfact := fun s' => probOutput_generateSeed_prependValues spec₀ qc js u s' hpos
      simp_rw [hfact, mul_assoc]
      rw [ENNReal.tsum_mul_left]
      congr 1
      · exact (probOutput_query t u).symm
      · suffices h : Pr[= x | (do
            let seed ← liftComp (generateSeed spec₀
                (Function.update (fun i => qc i * js.count i) t (qc t * js.count t - 1))
                js.dedup) spec₀
            (simulateQ seededOracle (mx u)).run' seed)] = Pr[= x | mx u] by
          rw [probOutput_bind_eq_tsum] at h
          simp_rw [probOutput_liftComp] at h
          exact h
        exact congrFun (congrArg DFunLike.coe (ih u _ js.dedup)) x

@[simp]
lemma probOutput_generateSeed_bind_simulateQ_bind
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [unifSpec ˡ⊂ₒ spec₀]
    [IsUniformSpec spec₀]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α β : Type} (oa : OracleComp spec₀ α) (ob : α → OracleComp spec₀ β) (y : β) :
    Pr[= y | do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      let x ← Prod.fst <$> (simulateQ seededOracle oa).run seed
      ob x] = Pr[= y | oa >>= ob] := by
  rw [show (do
    let seed ← liftComp (generateSeed spec₀ qc js) spec₀
    let x ← Prod.fst <$> (simulateQ seededOracle oa).run seed
    ob x) = ((do
    let seed ← liftComp (generateSeed spec₀ qc js) spec₀
    (simulateQ seededOracle oa).run' seed) >>= ob) from by simp [monad_norm],
    probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  congr 1; ext x; congr 1
  exact congrFun (congrArg DFunLike.coe
    (evalDist_liftComp_generateSeed_bind_simulateQ_run' qc js oa)) x

@[simp]
lemma probOutput_generateSeed_bind_map_simulateQ
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [unifSpec ˡ⊂ₒ spec₀]
    [IsUniformSpec spec₀]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α β : Type} (oa : OracleComp spec₀ α) (f : α → β) (y : β) :
    Pr[= y | (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      f <$> Prod.fst <$> (simulateQ seededOracle oa).run seed : OracleComp spec₀ β)] =
      Pr[= y | f <$> oa] := by
  simpa [monad_norm, Function.comp] using
    probOutput_generateSeed_bind_simulateQ_bind (qc := qc) (js := js)
      (oa := oa) (ob := fun x => pure (f x)) (y := y)

private lemma pop_addValue_self_nil_aux {seed : QuerySeed spec} {i : ι} (h : seed i = [])
    (v : spec.Range i) : (seed.addValue i v).pop i = some (v, seed) := by
  have hlist : (seed.addValue i v) i = [v] := by
    simp [QuerySeed.addValue, QuerySeed.addValues, h]
  rw [QuerySeed.pop_eq_some_of_cons _ _ v [] hlist]
  suffices Function.update (seed.addValue i v) i ([] : List (spec.Range i)) = seed by
    rw [this]; rfl
  funext j; by_cases hj : j = i
  · subst hj; simp [h]
  · rw [Function.update_of_ne hj]
    exact QuerySeed.addValues_of_ne seed [v] hj

private lemma pop_addValue_self_cons_aux {seed : QuerySeed spec} {i : ι} {u₀ : spec.Range i}
    {rest : List (spec.Range i)} (h : seed i = u₀ :: rest) (v : spec.Range i) :
    (seed.addValue i v).pop i =
      some (u₀, QuerySeed.addValue (Function.update seed i rest) i v) := by
  have hlist : (seed.addValue i v) i = u₀ :: (rest ++ [v]) := by
    simp [QuerySeed.addValue, QuerySeed.addValues, h]
  rw [QuerySeed.pop_eq_some_of_cons _ _ u₀ (rest ++ [v]) hlist]
  suffices Function.update (seed.addValue i v) i (rest ++ [v]) =
      QuerySeed.addValue (Function.update seed i rest) i v by rw [this]; rfl
  funext j; by_cases hj : j = i
  · subst hj; simp [QuerySeed.addValue, QuerySeed.addValues]
  · simp [Function.update_of_ne hj, QuerySeed.addValue, QuerySeed.addValues]

private lemma pop_addValue_of_ne_nil_aux {seed : QuerySeed spec} {i t : ι} (hti : t ≠ i)
    (h : seed t = []) (v : spec.Range i) : (seed.addValue i v).pop t = none := by
  rw [QuerySeed.pop_eq_none_iff]
  exact (QuerySeed.addValues_of_ne seed [_] hti).trans h

private lemma pop_addValue_of_ne_cons_aux {seed : QuerySeed spec} {i t : ι} {u₀ : spec.Range t}
    {rest : List (spec.Range t)} (hti : t ≠ i) (h : seed t = u₀ :: rest) (v : spec.Range i) :
    (seed.addValue i v).pop t =
      some (u₀, QuerySeed.addValue (Function.update seed t rest) i v) := by
  have hlist : (seed.addValue i v) t = u₀ :: rest :=
    (QuerySeed.addValues_of_ne seed [_] hti).trans h
  rw [QuerySeed.pop_eq_some_of_cons _ _ u₀ rest hlist]
  suffices Function.update (seed.addValue i v) t rest =
      QuerySeed.addValue (Function.update seed t rest) i v by rw [this]; rfl
  change Function.update (Function.update seed i (seed i ++ [v])) t rest =
    Function.update (Function.update seed t rest) i
      ((Function.update seed t rest) i ++ [v])
  conv_rhs =>
    rw [show (Function.update seed t rest) i = seed i from
      Function.update_of_ne (Ne.symm hti) rest seed]
  exact Function.update_comm (Ne.symm hti) (seed i ++ [v]) rest seed

/-- Adding a uniform value at index `i` to a seed does not change the distribution of
running a computation with the seeded oracle. This is because the extra value replaces
what would otherwise be a fresh uniform oracle response. -/
lemma evalDist_liftComp_uniformSample_bind_simulateQ_run'_addValue
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ j, SampleableType (spec₀.Range j)] [unifSpec ⊂ₒ spec₀]
    [unifSpec ˡ⊂ₒ spec₀]
    [IsUniformSpec spec₀]
    (σ : QuerySeed spec₀) (i : ι₀) {α : Type} (oa : OracleComp spec₀ α) :
    𝒟[(do
      let u ← liftComp ($ᵗ spec₀.Range i) spec₀
      (simulateQ seededOracle oa).run' (σ.addValue i u) : OracleComp spec₀ α)] =
    𝒟[((simulateQ seededOracle oa).run' σ : OracleComp spec₀ α)] := by
  revert σ
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro σ
    have hrun' : ∀ s, (simulateQ seededOracle (pure x : OracleComp spec₀ α)).run' s =
        (pure x : OracleComp spec₀ α) := fun s => by simp
    apply evalDist_ext; intro a
    simp_rw [hrun']
    rw [probOutput_bind_const]
    simp [probFailure_of_liftM_PMF]
  | query_bind t mx ih =>
    intro σ
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map]
    apply evalDist_ext; intro a
    simp_rw [run'_bind_query_eq_pop t mx]
    by_cases hti : t = i
    · cases hti
      cases hσi : σ i with
      | nil =>
        simp_rw [pop_addValue_self_nil_aux hσi, (QuerySeed.pop_eq_none_iff σ i).mpr hσi]
        rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
        congr 1; ext v; congr 1
        simp only [probOutput_liftComp, probOutput_uniformSample, probOutput_query]
      | cons u₀ rest =>
        simp_rw [pop_addValue_self_cons_aux hσi,
          QuerySeed.pop_eq_some_of_cons σ i u₀ rest hσi]
        exact congrFun (congrArg DFunLike.coe (ih u₀ (Function.update σ i rest))) a
    · cases hσt : σ t with
      | nil =>
        simp_rw [pop_addValue_of_ne_nil_aux hti hσt, (QuerySeed.pop_eq_none_iff σ t).mpr hσt]
        rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
        simp_rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left, mul_left_comm]
        rw [ENNReal.tsum_comm]
        simp_rw [ENNReal.tsum_mul_left]
        congr 1; ext r; congr 1
        rw [← probOutput_bind_eq_tsum]
        exact congrFun (congrArg DFunLike.coe (ih r σ)) a
      | cons u₀ rest =>
        simp_rw [pop_addValue_of_ne_cons_aux hti hσt,
          QuerySeed.pop_eq_some_of_cons σ t u₀ rest hσt]
        exact congrFun (congrArg DFunLike.coe
          (ih u₀ (Function.update σ t rest))) a

lemma evalDist_liftComp_replicate_uniformSample_bind_simulateQ_run'_addValues
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ j, SampleableType (spec₀.Range j)] [unifSpec ⊂ₒ spec₀]
    [unifSpec ˡ⊂ₒ spec₀]
    [IsUniformSpec spec₀]
    (i : ι₀) {α : Type} (oa : OracleComp spec₀ α) (n : ℕ) :
    ∀ (σ : QuerySeed spec₀),
    𝒟[(do
      let us ← liftComp (replicate n ($ᵗ spec₀.Range i)) spec₀
      (simulateQ seededOracle oa).run' (σ.addValues us) : OracleComp spec₀ α)] =
    𝒟[((simulateQ seededOracle oa).run' σ : OracleComp spec₀ α)] := by
  induction n with
  | zero => intro σ; simp [replicate_zero, QuerySeed.addValues_nil]
  | succ n ih =>
    intro σ
    simp only [replicate_succ, monad_norm, liftComp_bind, liftComp_pure, Function.comp]
    have hrew : (do
        let u ← liftComp ($ᵗ spec₀.Range i) spec₀
        let us ← liftComp (replicate n ($ᵗ spec₀.Range i)) spec₀
        (simulateQ seededOracle oa).run' (σ.addValues (u :: us)) : OracleComp spec₀ α) =
      (do
        let u ← liftComp ($ᵗ spec₀.Range i) spec₀
        let us ← liftComp (replicate n ($ᵗ spec₀.Range i)) spec₀
        (simulateQ seededOracle oa).run' ((σ.addValues [u]).addValues us) :
          OracleComp spec₀ α) := by
      congr 1; ext u; congr 1; ext us
      rw [QuerySeed.addValues_cons]
    rw [congrArg evalDist hrew, evalDist_bind]
    simp_rw [ih]
    rw [← evalDist_bind]
    exact evalDist_liftComp_uniformSample_bind_simulateQ_run'_addValue σ i oa

private lemma probOutput_liftComp_generateSeed_bind_simulateQ_run'_takeAtIndex_eq_tsum
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [unifSpec ˡ⊂ₒ spec₀]
    [IsUniformSpec spec₀]
    (qc : ι₀ → ℕ) (js : List ι₀) (i₀ : ι₀) (k : ℕ)
    {α : Type} (oa : OracleComp spec₀ α) (x : α) :
    Pr[= x | (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      (simulateQ seededOracle oa).run' (seed.takeAtIndex i₀ k) : OracleComp spec₀ α)] =
    ∑' s, Pr[= s | generateSeed spec₀ qc js] *
      Pr[= x | (simulateQ seededOracle oa).run' (s.takeAtIndex i₀ k)] := by
  rw [probOutput_bind_eq_tsum]
  simp_rw [probOutput_liftComp]

private lemma probOutput_prependValues_takeAtIndex_tsum_eq_query_mul
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [unifSpec ˡ⊂ₒ spec₀]
    [IsUniformSpec spec₀]
    (qc : ι₀ → ℕ) (js : List ι₀) (t : ι₀) (i₀ : ι₀) (k : ℕ)
    {α : Type} (ob : OracleComp spec₀ α) (u : spec₀.Range t) (x : α)
    (hcount : 0 < qc t * js.count t)
    (h : 𝒟[(do
      let seed ← liftComp (generateSeed spec₀
        (Function.update (fun i => qc i * js.count i) t (qc t * js.count t - 1)) js.dedup) spec₀
      (simulateQ seededOracle ob).run' (seed.takeAtIndex i₀ k) : OracleComp spec₀ α)] = 𝒟[ob]) :
    ∑' s : QuerySeed spec₀, Pr[= s.prependValues [u] | generateSeed spec₀ qc js] *
        Pr[= x | (simulateQ seededOracle ob).run' (s.takeAtIndex i₀ k)] =
      Pr[= u | (liftM (query t) : OracleComp spec₀ _)] * Pr[= x | ob] := by
  simp_rw [probOutput_generateSeed_prependValues spec₀ qc js u _ hcount, mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  · exact (probOutput_query _ u).symm
  · rw [← probOutput_liftComp_generateSeed_bind_simulateQ_run'_takeAtIndex_eq_tsum]
    exact congrFun (congrArg DFunLike.coe h) x

/-- Truncating the seed at oracle `i₀` to only the first `k` entries does not change
the distribution when averaging over seeds from `generateSeed`. -/
lemma evalDist_liftComp_generateSeed_bind_simulateQ_run'_takeAtIndex
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [unifSpec ˡ⊂ₒ spec₀]
    [IsUniformSpec spec₀]
    (qc : ι₀ → ℕ) (js : List ι₀) (i₀ : ι₀) (k : ℕ)
    {α : Type} (oa : OracleComp spec₀ α) :
    𝒟[(do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      (simulateQ seededOracle oa).run' (seed.takeAtIndex i₀ k) : OracleComp spec₀ α)] =
    𝒟[oa] := by
  classical
  revert qc js k
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro qc js k; apply evalDist_ext; intro a; simp
  | query_bind t mx ih =>
    intro qc js k
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map]
    apply evalDist_ext; intro x
    have hrun' : ∀ s : QuerySeed spec₀,
        (do let u ← seededOracle t; simulateQ seededOracle (mx u) :
          StateT _ (OracleComp spec₀) α).run' s =
        match s.pop t with
        | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s
        | some (u, s') => (simulateQ seededOracle (mx u)).run' s' :=
      run'_bind_query_eq_pop t mx
    simp_rw [hrun']
    rw [probOutput_bind_eq_tsum]
    simp_rw [probOutput_liftComp]
    by_cases hpop_none : qc t * js.count t = 0 ∨ (t = i₀ ∧ k = 0)
    · have hpop : ∀ s ∈ support (generateSeed spec₀ qc js),
          (s.takeAtIndex i₀ k).pop t = none := by
        intro s hs; rw [QuerySeed.pop_eq_none_iff]
        rw [support_generateSeed (spec := spec₀)] at hs
        rcases hpop_none with hcount | ⟨rfl, rfl⟩
        · have hlen : (s t).length = qc t * js.count t := hs t
          have hnil := List.eq_nil_of_length_eq_zero (hlen.trans hcount)
          by_cases hti : t = i₀
          · subst hti; simp [QuerySeed.takeAtIndex, hnil]
          · rw [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hti]; exact hnil
        · simp [QuerySeed.takeAtIndex]
      have step1 : ∀ s,
          Pr[= s | generateSeed spec₀ qc js] *
            Pr[= x | match (s.takeAtIndex i₀ k).pop t with
              | none => liftM (query t) >>= fun u =>
                  (simulateQ seededOracle (mx u)).run' (s.takeAtIndex i₀ k)
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s'] =
          Pr[= s | generateSeed spec₀ qc js] *
            Pr[= x | liftM (query t) >>= fun u =>
                (simulateQ seededOracle (mx u)).run' (s.takeAtIndex i₀ k)] := by
        intro s
        by_cases hs : s ∈ support (generateSeed spec₀ qc js)
        · simp [hpop s hs]
        · simp [(probOutput_eq_zero_iff _ _).2 hs]
      simp_rw [step1, probOutput_bind_eq_tsum (liftM (query t))]
      simp_rw [← ENNReal.tsum_mul_left, mul_left_comm]
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left]
      congr 1; ext u; congr 1
      rw [← probOutput_liftComp_generateSeed_bind_simulateQ_run'_takeAtIndex_eq_tsum]
      exact congrFun (congrArg DFunLike.coe (ih u qc js k)) x
    · push Not at hpop_none
      obtain ⟨hcount_ne, htk⟩ := hpop_none
      have hcount : 0 < qc t * js.count t := Nat.pos_of_ne_zero (by lia)
      have hpop_take : ∀ s ∈ support (generateSeed spec₀ qc js),
          ∃ u s', (s.takeAtIndex i₀ k).pop t = some (u, s') := by
        intro s hs
        have hne : s t ≠ [] :=
          ne_nil_of_mem_support_generateSeed (spec := spec₀) (qc := qc) (js := js) s t hs hcount
        by_cases hti : t = i₀
        · have hk : 0 < k := Nat.pos_of_ne_zero (htk hti)
          have htake_ne : (s.takeAtIndex i₀ k) t ≠ [] := by
            rw [hti, QuerySeed.takeAtIndex_apply_self]
            obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (hti ▸ hne)
            rw [hl, show k = (k - 1) + 1 from (Nat.succ_pred_eq_of_pos hk).symm,
              List.take_succ_cons]
            exact List.cons_ne_nil _ _
          obtain ⟨u, us, hcons⟩ := List.exists_cons_of_ne_nil htake_ne
          exact ⟨u, Function.update (s.takeAtIndex i₀ k) t us,
            QuerySeed.pop_eq_some_of_cons _ _ u us hcons⟩
        · obtain ⟨u, us, hcons⟩ := List.exists_cons_of_ne_nil hne
          exact ⟨u, Function.update (s.takeAtIndex i₀ k) t us,
            QuerySeed.pop_eq_some_of_cons _ _ u us
              ((QuerySeed.takeAtIndex_apply_of_ne s i₀ k t hti).trans hcons)⟩
      have step1 : ∀ s,
          Pr[= s | generateSeed spec₀ qc js] *
            Pr[= x | match (s.takeAtIndex i₀ k).pop t with
              | none => liftM (query t) >>= fun u =>
                  (simulateQ seededOracle (mx u)).run' (s.takeAtIndex i₀ k)
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s'] =
          Pr[= s | generateSeed spec₀ qc js] *
            (match (s.takeAtIndex i₀ k).pop t with
              | none => 0
              | some (u, s') =>
                  Pr[= x | (simulateQ seededOracle (mx u)).run' s']) := by
        intro s
        by_cases hs : s ∈ support (generateSeed spec₀ qc js)
        · obtain ⟨u, s', hpop⟩ := hpop_take s hs; simp [hpop]
        · simp [(probOutput_eq_zero_iff _ _).2 hs]
      simp_rw [step1]
      rw [← (QuerySeed.prependValues_singleton_injective t).tsum_eq
        (support_generateSeed_mul_subset_range_prependValues_aux qc js t hcount _)]
      by_cases hti : t = i₀
      · subst hti
        have hk : 0 < k := Nat.pos_of_ne_zero (htk rfl)
        simp only [QuerySeed.pop_takeAtIndex_prependValues_self _ _ _ hk]
        rw [ENNReal.tsum_prod', probOutput_bind_eq_tsum]
        congr 1; ext u
        exact probOutput_prependValues_takeAtIndex_tsum_eq_query_mul qc js t t (k - 1)
          (mx u) u x hcount (ih u _ js.dedup (k - 1))
      · simp only [QuerySeed.pop_takeAtIndex_prependValues_of_ne _ _ _ _ hti]
        rw [ENNReal.tsum_prod', probOutput_bind_eq_tsum]
        congr 1; ext u
        exact probOutput_prependValues_takeAtIndex_tsum_eq_query_mul qc js t i₀ k
          (mx u) u x hcount (ih u _ js.dedup k)

@[simp]
lemma probOutput_generateSeed_bind_map_simulateQ_takeAtIndex
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [unifSpec ˡ⊂ₒ spec₀]
    [IsUniformSpec spec₀]
    (qc : ι₀ → ℕ) (js : List ι₀) (i₀ : ι₀) (k : ℕ)
    {α β : Type} (oa : OracleComp spec₀ α) (f : α → β) (y : β) :
    Pr[= y | (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      f <$> (simulateQ seededOracle oa).run' (seed.takeAtIndex i₀ k) : OracleComp spec₀ β)] =
      Pr[= y | f <$> oa] := by
  rw [← map_bind]
  exact congrFun (congrArg DFunLike.coe (by simp only [evalDist_map,
    evalDist_liftComp_generateSeed_bind_simulateQ_run'_takeAtIndex])) y

private lemma takeAtIndex_prependValues_singleton_self_aux {ι₀ : Type} {spec₀ : OracleSpec ι₀}
    [DecidableEq ι₀] (t : ι₀) (k : ℕ) (hk : 0 < k) (u₀ : spec₀.Range t) (s' : QuerySeed spec₀) :
    (s'.prependValues [u₀]).takeAtIndex t k =
      (s'.takeAtIndex t (k - 1)).prependValues [u₀] := by
  funext j; by_cases hj : j = t
  · subst hj
    simp only [QuerySeed.takeAtIndex_apply_self, QuerySeed.prependValues_singleton]
    conv_lhs => rw [show k = (k - 1) + 1 from (Nat.succ_pred_eq_of_pos hk).symm]
    rw [List.take_succ_cons]
  · simp [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hj, QuerySeed.prependValues_of_ne _ _ hj]

private lemma takeAtIndex_prependValues_singleton_of_ne_aux {ι₀ : Type} {spec₀ : OracleSpec ι₀}
    [DecidableEq ι₀] (t i₀ : ι₀) (hti : t ≠ i₀) (k : ℕ) (u₀ : spec₀.Range t)
    (s' : QuerySeed spec₀) :
    (s'.prependValues [u₀]).takeAtIndex i₀ k = (s'.takeAtIndex i₀ k).prependValues [u₀] := by
  funext j; by_cases hji : j = i₀
  · subst hji
    simp [QuerySeed.takeAtIndex_apply_self, QuerySeed.prependValues_of_ne _ _ (Ne.symm hti)]
  · rw [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hji]
    by_cases hjt : j = t
    · subst hjt; simp [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hti]
    · simp [QuerySeed.prependValues_of_ne _ _ hjt, QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hji]

private lemma takeAtIndex_zero_prependValues_singleton_aux {ι₀ : Type} {spec₀ : OracleSpec ι₀}
    [DecidableEq ι₀] (t : ι₀) (u₀ : spec₀.Range t) (s' : QuerySeed spec₀) :
    (s'.prependValues [u₀]).takeAtIndex t 0 = s'.takeAtIndex t 0 := by
  funext j; by_cases hj : j = t
  · subst hj; simp [QuerySeed.takeAtIndex_apply_self]
  · simp [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hj, QuerySeed.prependValues_of_ne _ _ hj]

private lemma tsum_probOutput_generateSeed_prependValues_weight_aux {ι₀ : Type}
    {spec₀ : OracleSpec ι₀} [DecidableEq ι₀] [∀ i, SampleableType (spec₀.Range i)]
    [unifSpec ⊂ₒ spec₀] [unifSpec ˡ⊂ₒ spec₀] [IsUniformSpec spec₀]
    (qc : ι₀ → ℕ) (js : List ι₀) (t : ι₀) (i₀ jdx : ι₀) (k jk : ℕ)
    {α : Type} (ob : OracleComp spec₀ α) (u₀ : spec₀.Range t) (x : α)
    (hcount : 0 < qc t * js.count t)
    (htake : ∀ b : QuerySeed spec₀, (b.prependValues [u₀]).takeAtIndex i₀ k =
      (b.takeAtIndex jdx jk).prependValues [u₀])
    (hih : ∀ g : QuerySeed spec₀ → ENNReal,
      ∑' σ, Pr[= σ | generateSeed spec₀ (Function.update (fun i => qc i * js.count i) t
            (qc t * js.count t - 1)) js.dedup] *
          (g (σ.takeAtIndex jdx jk) * Pr[= x | (simulateQ seededOracle ob).run' σ]) =
        ∑' σ, Pr[= σ | generateSeed spec₀ (Function.update (fun i => qc i * js.count i) t
            (qc t * js.count t - 1)) js.dedup] *
          (g (σ.takeAtIndex jdx jk) *
            Pr[= x | (simulateQ seededOracle ob).run' (σ.takeAtIndex jdx jk)]))
    (h : QuerySeed spec₀ → ENNReal) :
    ∑' b : QuerySeed spec₀, Pr[= b.prependValues [u₀] | generateSeed spec₀ qc js] *
        (h ((b.prependValues [u₀]).takeAtIndex i₀ k) *
          Pr[= x | (simulateQ seededOracle ob).run' b]) =
      ∑' b : QuerySeed spec₀, Pr[= b.prependValues [u₀] | generateSeed spec₀ qc js] *
        (h ((b.prependValues [u₀]).takeAtIndex i₀ k) *
          Pr[= x | (simulateQ seededOracle ob).run' (b.takeAtIndex jdx jk)]) := by
  simp_rw [htake, probOutput_generateSeed_prependValues spec₀ qc js u₀ _ hcount, mul_assoc]
  rw [ENNReal.tsum_mul_left]
  conv_rhs => rw [ENNReal.tsum_mul_left]
  congr 1
  exact hih (fun σ => h (σ.prependValues [u₀]))

/-- Weighted takeAtIndex faithfulness: a prefix-dependent weight `h` preserves the
faithfulness equality between full-seed and truncated-seed simulation.
This generalizes the basic takeAtIndex faithfulness by allowing multiplication
by an arbitrary function of the seed prefix `σ.takeAtIndex i₀ k`. -/
lemma tsum_probOutput_generateSeed_weight_takeAtIndex
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [unifSpec ˡ⊂ₒ spec₀]
    [IsUniformSpec spec₀]
    (qc : ι₀ → ℕ) (js : List ι₀) (i₀ : ι₀) (k : ℕ)
    {α : Type} (oa : OracleComp spec₀ α) (x : α)
    (h : QuerySeed spec₀ → ENNReal) :
    ∑' σ, Pr[= σ | generateSeed spec₀ qc js] *
      (h (σ.takeAtIndex i₀ k) *
        Pr[= x | (simulateQ seededOracle oa).run' σ]) =
    ∑' σ, Pr[= σ | generateSeed spec₀ qc js] *
      (h (σ.takeAtIndex i₀ k) *
        Pr[= x | (simulateQ seededOracle oa).run' (σ.takeAtIndex i₀ k)]) := by
  classical
  revert qc js k h
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qc js k h; simp
  | query_bind t mx ih =>
    intro qc js k h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map]
    have hrun' : ∀ s : QuerySeed spec₀,
        (do let u ← seededOracle t; simulateQ seededOracle (mx u) :
          StateT _ (OracleComp spec₀) α).run' s =
        match s.pop t with
        | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s
        | some (u, s') => (simulateQ seededOracle (mx u)).run' s' :=
      run'_bind_query_eq_pop t mx
    simp_rw [hrun']
    have hcomm : ∀ (g : spec₀.Range t → QuerySeed spec₀ → OracleComp spec₀ α),
        ∑' s, Pr[= s | generateSeed spec₀ qc js] *
          (h (s.takeAtIndex i₀ k) *
            ∑' u, Pr[= u | (spec₀.query t : OracleComp spec₀ _)] *
              Pr[= x | g u s]) =
        ∑' u, Pr[= u | (spec₀.query t : OracleComp spec₀ _)] *
          ∑' s, Pr[= s | generateSeed spec₀ qc js] *
            (h (s.takeAtIndex i₀ k) * Pr[= x | g u s]) := by
      intro g
      simp_rw [ENNReal.tsum_mul_left.symm]
      rw [ENNReal.tsum_comm]
      congr 1; ext u; congr 1; ext s; ring
    by_cases hcount_zero : qc t * js.count t = 0
    · -- Case 1: no seed entries at oracle t — both pop to none
      have hpop_full : ∀ s ∈ support (generateSeed spec₀ qc js), s.pop t = none := by
        intro s hs; rw [QuerySeed.pop_eq_none_iff]
        rw [support_generateSeed (spec := spec₀)] at hs
        exact List.eq_nil_of_length_eq_zero ((hs t).trans hcount_zero)
      have hpop_take : ∀ s ∈ support (generateSeed spec₀ qc js),
          (s.takeAtIndex i₀ k).pop t = none := by
        intro s hs; rw [QuerySeed.pop_eq_none_iff]
        have hnil := List.eq_nil_of_length_eq_zero (((support_generateSeed
          (spec := spec₀) (qc := qc) (js := js) ▸ hs : _) t).trans hcount_zero)
        by_cases hti : t = i₀
        · subst hti; simp [QuerySeed.takeAtIndex, hnil]
        · rw [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hti]; exact hnil
      have step : ∀ (σ : QuerySeed spec₀ → QuerySeed spec₀)
          (hpop : ∀ s ∈ support (generateSeed spec₀ qc js), (σ s).pop t = none) s,
          Pr[= s | generateSeed spec₀ qc js] *
            (h (s.takeAtIndex i₀ k) * Pr[= x | match (σ s).pop t with
              | none => liftM (query t) >>= fun u =>
                  (simulateQ seededOracle (mx u)).run' (σ s)
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s']) =
          Pr[= s | generateSeed spec₀ qc js] *
            (h (s.takeAtIndex i₀ k) * Pr[= x | liftM (query t) >>= fun u =>
                (simulateQ seededOracle (mx u)).run' (σ s)]) := by
        intro σ hpop s
        by_cases hs : s ∈ support (generateSeed spec₀ qc js)
        · simp [hpop s hs]
        · simp [(probOutput_eq_zero_iff _ _).2 hs]
      simp_rw [step (fun s => s) hpop_full, step _ hpop_take,
        probOutput_bind_eq_tsum (liftM (query t))]
      rw [hcomm, hcomm]
      congr 1; ext u; congr 1
      exact ih u qc js k h
    · -- Case 2+3: seed has entries at oracle t
      push Not at hcount_zero
      have hcount : 0 < qc t * js.count t := Nat.pos_of_ne_zero (by lia)
      rw [← (QuerySeed.prependValues_singleton_injective t).tsum_eq
          (support_generateSeed_mul_subset_range_prependValues_aux qc js t hcount _),
        ← (QuerySeed.prependValues_singleton_injective t).tsum_eq
          (support_generateSeed_mul_subset_range_prependValues_aux qc js t hcount _)]
      simp only [QuerySeed.pop_prependValues_singleton]
      by_cases hti : t = i₀
      · subst hti
        by_cases hk : k = 0
        · -- Case 3: t = i₀, k = 0 — LHS pop some, RHS pop none
          subst hk
          have hpop_rhs : ∀ (s' : QuerySeed spec₀),
              (QuerySeed.takeAtIndex s' t 0).pop t = none := fun s' => by
            rw [QuerySeed.pop_eq_none_iff]; simp [QuerySeed.takeAtIndex]
          simp_rw [takeAtIndex_zero_prependValues_singleton_aux t, hpop_rhs]
          rw [ENNReal.tsum_prod']; conv_rhs => rw [ENNReal.tsum_prod']
          simp_rw [probOutput_generateSeed_prependValues spec₀ qc js _ _ hcount,
            mul_assoc, ENNReal.tsum_mul_left]
          congr 1
          conv_lhs =>
            arg 1
            intro u₀
            rw [ih u₀ _ js.dedup 0 h]
          rw [ENNReal.tsum_comm]; conv_rhs => rw [ENNReal.tsum_comm]
          congr 1; ext s'
          simp_rw [ENNReal.tsum_mul_left]
          congr 2
          conv_rhs => rw [probOutput_bind_eq_tsum (spec₀.query t : OracleComp spec₀ _)]
          conv_rhs => simp [probOutput_query]
          conv_rhs => rw [← Finset.mul_sum]
          have hcard_ne_zero : (↑(Fintype.card (spec₀.Range t)) : ENNReal) ≠ 0 := by
            exact_mod_cast Fintype.card_pos.ne'
          have hcard_ne_top : (↑(Fintype.card (spec₀.Range t)) : ENNReal) ≠ ⊤ :=
            ENNReal.natCast_ne_top (n := Fintype.card (spec₀.Range t))
          rw [← mul_assoc, ENNReal.mul_inv_cancel hcard_ne_zero hcard_ne_top, one_mul]
          simp
        · -- Case 2a: t = i₀, k > 0 — both pop some, k decreases
          have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
          simp only [QuerySeed.pop_takeAtIndex_prependValues_self _ _ _ hk_pos]
          rw [ENNReal.tsum_prod']
          conv_rhs => rw [ENNReal.tsum_prod']
          congr 1; ext u₀
          exact tsum_probOutput_generateSeed_prependValues_weight_aux qc js t t t k (k - 1)
            (mx u₀) u₀ x hcount (takeAtIndex_prependValues_singleton_self_aux t k hk_pos u₀)
            (ih u₀ _ js.dedup (k - 1)) h
      · -- Case 2b: t ≠ i₀ — both pop some, k unchanged
        simp only [QuerySeed.pop_takeAtIndex_prependValues_of_ne _ _ _ _ hti]
        rw [ENNReal.tsum_prod']
        conv_rhs => rw [ENNReal.tsum_prod']
        congr 1; ext u₀
        exact tsum_probOutput_generateSeed_prependValues_weight_aux qc js t i₀ i₀ k k
          (mx u₀) u₀ x hcount (takeAtIndex_prependValues_singleton_of_ne_aux t i₀ hti k u₀)
          (ih u₀ _ js.dedup k) h

section queryBounds

variable {α : Type u}

/-- If a pre-generated seed already supplies all but `residual t` of the answers allowed by the
structural per-index query bound `qb`, then running `oa` against `seededOracle` can make at most
those residual live queries.

This theorem is the core replay-cost statement for seeded simulations: a large enough seed turns
most oracle interactions into deterministic table lookups, leaving only the uncovered suffix of
the computation as genuine oracle queries. -/
theorem isPerIndexQueryBound_run'_of_seedCoverage
    {oa : OracleComp spec α} {qb residual : ι → ℕ} {seed : QuerySeed spec}
    (hqb : IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t - residual t ≤ (seed t).length) :
    IsPerIndexQueryBound ((simulateQ seededOracle oa).run' seed) residual := by
  revert qb residual seed
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro qb residual seed _ _
      simp
  | query_bind t mx ih =>
      intro qb residual seed hqb hcover
      rw [isPerIndexQueryBound_query_bind_iff] at hqb
      rw [show (simulateQ seededOracle (liftM (query t) >>= mx)).run' seed =
            ((seededOracle t >>= fun r => simulateQ seededOracle (mx r)).run' seed) by simp,
        run'_bind_query_eq_pop t mx seed]
      cases hpop : seed.pop t with
      | none =>
          rw [isPerIndexQueryBound_query_bind_iff]
          have hres_pos : 0 < residual t := by
            have hcov_t := hcover t
            rw [QuerySeed.pop_eq_none_iff] at hpop
            simp [hpop] at hcov_t
            lia
          refine ⟨hres_pos, ?_⟩
          intro u
          simpa using
            (ih u
              (qb := Function.update qb t (qb t - 1))
              (residual := Function.update residual t (residual t - 1))
              (seed := seed)
              (hqb := hqb.2 u)
              (by
                intro j
                have hcov_j := hcover j
                by_cases hj : j = t
                · subst hj
                  simp only [Function.update_self]
                  lia
                · simpa [Function.update_of_ne hj, hj] using hcov_j))
      | some p =>
          rcases p with ⟨u, seed'⟩
          simpa using
            (ih u
              (qb := Function.update qb t (qb t - 1))
              (residual := residual)
              (seed := seed')
              (hqb := hqb.2 u)
              (by
                intro j
                have hcov_j := hcover j
                by_cases hj : j = t
                · subst hj
                  have hlen : (seed j).length = (seed' j).length + 1 := by
                    rw [← QuerySeed.cons_of_pop_eq_some seed j u seed' hpop, List.length_cons]
                  simp only [Function.update_self]
                  lia
                · rw [QuerySeed.rest_eq_update_tail_of_pop_eq_some seed t u seed' hpop]
                  simpa [Function.update_of_ne hj, hj] using hcov_j))

/-- A seed that covers the full structural query bound eliminates all live oracle queries. -/
theorem isPerIndexQueryBound_run'_zero
    {oa : OracleComp spec α} {qb : ι → ℕ} {seed : QuerySeed spec}
    (hqb : IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t ≤ (seed t).length) :
    IsPerIndexQueryBound ((simulateQ seededOracle oa).run' seed) 0 :=
  isPerIndexQueryBound_run'_of_seedCoverage (oa := oa) (qb := qb) (residual := 0)
    (seed := seed) hqb fun t => by simpa using hcover t

/-- If the seed stores only the first `k` answers for oracle `i`, then the replay can make live
queries only to `i`, and at most `qb i - k` of them remain.

This is the structural query-bound form of the usual forking-lemma intuition: after rewinding to
the `k`-th query to oracle `i`, every earlier answer is fixed by the prefix seed, so only the
suffix after the fork point can still hit the live oracle. -/
theorem isPerIndexQueryBound_run'_takeAtIndex
    {oa : OracleComp spec α} {qb : ι → ℕ} {seed : QuerySeed spec} {i : ι} {k : ℕ}
    (hqb : IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t ≤ (seed t).length)
    (hk : k ≤ qb i) :
    IsPerIndexQueryBound
      ((simulateQ seededOracle oa).run' (seed.takeAtIndex i k))
      (Function.update 0 i (qb i - k)) := by
  refine isPerIndexQueryBound_run'_of_seedCoverage
    (oa := oa) (qb := qb) (residual := Function.update 0 i (qb i - k))
    (seed := seed.takeAtIndex i k) hqb ?_
  intro t
  grind [QuerySeed.takeAtIndex_apply_self, QuerySeed.takeAtIndex_apply_of_ne,
    Function.update_of_ne]

/-- After rewinding to query index `s` and appending one fresh answer at oracle `i`, the replayed
run can still make live queries only to `i`, with at most `qb i - (s + 1)` such queries left. -/
theorem isPerIndexQueryBound_run'_takeAtIndex_addValue
    {oa : OracleComp spec α} {qb : ι → ℕ} {seed : QuerySeed spec} {i : ι}
    (hqb : IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t ≤ (seed t).length)
    (s : Fin (qb i + 1)) (u : spec.Range i) :
    IsPerIndexQueryBound
      ((simulateQ seededOracle oa).run' ((seed.takeAtIndex i ↑s).addValue i u))
      (Function.update 0 i (qb i - (↑s + 1))) := by
  refine isPerIndexQueryBound_run'_of_seedCoverage
    (oa := oa) (qb := qb) (residual := Function.update 0 i (qb i - (↑s + 1)))
    (seed := (seed.takeAtIndex i ↑s).addValue i u) hqb ?_
  intro t
  by_cases ht : t = i
  · subst ht
    have hs' : ↑s ≤ (seed t).length := le_trans (Nat.lt_succ_iff.mp s.2) (hcover t)
    simp [QuerySeed.addValue, QuerySeed.addValues]
    omega
  · simp [QuerySeed.addValue, QuerySeed.addValues, ht, hcover t]

end queryBounds

/-! ### Forward query bounds for `seededOracle`

Forward only — the reverse fails because pregenerated values strictly reduce the count. -/

theorem isTotalQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀}
    [IsUniformSpec spec₀]
    {α : Type} {oa : OracleComp spec₀ α} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n) (seed : QuerySeed spec₀) :
    OracleComp.IsTotalQueryBound ((simulateQ spec₀.seededOracle oa).run seed) n := by
  rw [eq_withPregen]
  exact OracleComp.IsTotalQueryBound.simulateQ_run_withPregen _ h
    (fun t => (OracleComp.isQueryBound_query_iff t 1 _ _).mpr Nat.one_pos) seed

theorem isQueryBoundP_run_simulateQ {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀}
    [IsUniformSpec spec₀]
    {α : Type} {oa : OracleComp spec₀ α}
    {p : ι₀ → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n) (seed : QuerySeed spec₀) :
    OracleComp.IsQueryBoundP ((simulateQ spec₀.seededOracle oa).run seed) p n := by
  rw [eq_withPregen]
  exact OracleComp.IsQueryBoundP.simulateQ_run_withPregen _ h
    (fun t _ => (OracleComp.isQueryBoundP_query_iff p t 1).mpr (fun _ => Nat.one_pos))
    (fun t hnp => (OracleComp.isQueryBoundP_query_iff p t 0).mpr (fun hpt => absurd hpt hnp))
    seed

theorem isPerIndexQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀}
    [IsUniformSpec spec₀]
    {α : Type} {oa : OracleComp spec₀ α} {qb : ι₀ → ℕ}
    (h : OracleComp.IsPerIndexQueryBound oa qb) (seed : QuerySeed spec₀) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.seededOracle oa).run seed) qb := by
  rw [eq_withPregen]
  refine OracleComp.IsPerIndexQueryBound.simulateQ_run_withPregen _ h ?_ seed
  intro t
  rw [QueryImpl.ofLift_apply]
  exact (OracleComp.isPerIndexQueryBound_query_iff t (Function.update 0 t 1)).mpr (by
    simp [Function.update_self])

/-- State-preserving variant of `isPerIndexQueryBound_run'_zero`: when the seed covers `qb`
at every index, the simulation makes zero further queries even with the seed in scope. -/
theorem isPerIndexQueryBound_run_simulateQ_zero
    {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀} [IsUniformSpec spec₀]
    {α : Type}
    {oa : OracleComp spec₀ α} {qb : ι₀ → ℕ} {seed : QuerySeed spec₀}
    (hqb : OracleComp.IsPerIndexQueryBound oa qb)
    (hseed : ∀ t, qb t ≤ (seed t).length) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.seededOracle oa).run seed) 0 := by
  have h := isPerIndexQueryBound_run'_zero (oa := oa) (qb := qb) (seed := seed) hqb hseed
  rw [StateT.run'] at h
  exact (OracleComp.isPerIndexQueryBound_map_iff _ Prod.fst 0).mp h

/-- State-preserving variant of `isPerIndexQueryBound_run'_of_seedCoverage`: any uncovered
suffix of the seed becomes the residual budget in the result spec. -/
theorem isPerIndexQueryBound_run_simulateQ_of_seedCoverage
    {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀} [IsUniformSpec spec₀]
    {α : Type}
    {oa : OracleComp spec₀ α} {qb residual : ι₀ → ℕ} {seed : QuerySeed spec₀}
    (hqb : OracleComp.IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t - residual t ≤ (seed t).length) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.seededOracle oa).run seed) residual := by
  have h := isPerIndexQueryBound_run'_of_seedCoverage (oa := oa) (qb := qb)
    (residual := residual) (seed := seed) hqb hcover
  rw [StateT.run'] at h
  exact (OracleComp.isPerIndexQueryBound_map_iff _ Prod.fst residual).mp h

end seededOracle
