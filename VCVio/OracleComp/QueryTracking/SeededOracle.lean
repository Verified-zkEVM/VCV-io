/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.Constructions.GenerateSeed
import VCVio.OracleComp.Coercions.SubSpec


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

end QueryImpl

/-- Use pregenerated oracle responses for queries, falling back to the real oracle
when the seed is exhausted. Seed consumption is tracked via `StateT`. -/
def seededOracle :
    QueryImpl spec (StateT (QuerySeed spec) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withPregen

namespace seededOracle

/-- The probability that a lifted uniform sample equals a fixed value is `(card α)⁻¹`. -/
lemma probEvent_liftComp_uniformSample_eq_of_eq
    {ι : Type} {spec : OracleSpec ι}
    [(i : ι) → SampleableType (spec.Range i)]
    [unifSpec ⊂ₒ spec] [OracleSpec.LawfulSubSpec unifSpec spec]
    [spec.Fintype] [spec.Inhabited]
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
      | [] => (·, seed) <$> OracleComp.query t := rfl

lemma run_bind_query_eq_pop {α : Type u}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) (seed : QuerySeed spec) :
    (((seededOracle t) >>= fun u => simulateQ seededOracle (mx u)).run seed) =
      match seed.pop t with
      | none => do
          let u ← liftM (query t)
          (simulateQ seededOracle (mx u)).run seed
      | some (u, seed') =>
          (simulateQ seededOracle (mx u)).run seed' := by
  cases hst : seed t with
  | nil =>
    simp [seededOracle.apply_eq, StateT.run_bind, QuerySeed.pop, hst]
  | cons u us =>
    simp [seededOracle.apply_eq, StateT.run_bind, QuerySeed.pop, hst]

private lemma evalDist_liftComp_generateSeed_bind_simulateQ_run'
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α : Type} (oa : OracleComp spec₀ α) :
    evalDist (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      (simulateQ seededOracle oa).run' seed : OracleComp spec₀ α) =
    evalDist oa := by
  classical
  revert qc js
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro qc js
    apply evalDist_ext; intro a
    simp
  | query_bind t mx ih =>
    intro qc js
    -- Prove at the evalDist level, not pointwise
    -- First establish the run' decomposition
    have hrun' : ∀ s : QuerySeed spec₀,
        (do let u ← seededOracle t; simulateQ seededOracle (mx u) :
          StateT _ (OracleComp spec₀) α).run' s =
        match s.pop t with
        | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' s
        | some (u, s') => (simulateQ seededOracle (mx u)).run' s' := by
      intro s
      change Prod.fst <$>
        (seededOracle t >>= fun u => simulateQ seededOracle (mx u)).run s = _
      rw [run_bind_query_eq_pop]
      cases s.pop t with
      | none => simp [map_bind]
      | some p => rfl
    -- Use the decomposition to prove evalDist equality
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map]
    apply evalDist_ext; intro x
    simp_rw [hrun']
    rw [probOutput_bind_eq_tsum]
    simp_rw [probOutput_liftComp]
    by_cases hcount : qc t * js.count t = 0
    · -- All seeds have s t = [], pop = none.
      have hpop : ∀ s ∈ support (generateSeed spec₀ qc js), s.pop t = none := by
        intro s hs; rw [QuerySeed.pop_eq_none_iff]
        rw [support_generateSeed (spec := spec₀)] at hs
        have hlen : (s t).length = qc t * js.count t := hs t
        exact List.eq_nil_of_length_eq_zero (hlen.trans hcount)
      -- Replace match with none branch (zero terms vanish)
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
        · have h0 : Pr[= s | generateSeed spec₀ qc js] = 0 :=
            (probOutput_eq_zero_iff _ _).2 hs
          simp [h0]
      simp_rw [step1, probOutput_bind_eq_tsum (liftM (query t))]
      -- ∑' s, Pr[= s|gen] * ∑' u, Pr[= u|query t] * Pr[= x|run'(mx u) s]
      -- Distribute and swap
      simp_rw [← ENNReal.tsum_mul_left, mul_left_comm]
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left]
      congr 1; ext u; congr 1
      have hih : Pr[= x | (liftComp (generateSeed spec₀ qc js) spec₀ >>= fun seed =>
          (simulateQ seededOracle (mx u)).run' seed)] = Pr[= x | mx u] :=
        congrFun (congrArg DFunLike.coe (ih u qc js)) x
      rw [show Pr[= x | liftComp (generateSeed spec₀ qc js) spec₀ >>= fun seed =>
          (simulateQ seededOracle (mx u)).run' seed] =
        ∑' s, Pr[= s | generateSeed spec₀ qc js] *
          Pr[= x | (simulateQ seededOracle (mx u)).run' s] from by
        rw [probOutput_bind_eq_tsum]; simp_rw [probOutput_liftComp]] at hih
      exact hih
    · push Not at hcount
      -- All seeds in support have s t ≠ [], so pop = some.
      have hpop_some : ∀ s ∈ support (generateSeed spec₀ qc js),
          ∃ u s', s.pop t = some (u, s') := by
        intro s hs
        have hne : s t ≠ [] :=
          ne_nil_of_mem_support_generateSeed (spec := spec₀) (qc := qc) (js := js) s t hs
            (Nat.pos_of_ne_zero (by omega))
        obtain ⟨u, us, hcons⟩ := List.exists_cons_of_ne_nil hne
        exact ⟨u, Function.update s t us, QuerySeed.pop_eq_some_of_cons s t u us hcons⟩
      -- Replace match with some branch for seeds in support (others are 0)
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
      -- Reparametrize: ∑' s, f(s) = ∑' (u,s'), f(s'.prependValues [u])
      -- using injectivity of prependValues and support ⊆ range
      have h_supp : Function.support (fun s =>
          Pr[= s | generateSeed spec₀ qc js] *
            match s.pop t with
            | none => 0
            | some (u, s') => Pr[= x | (simulateQ seededOracle (mx u)).run' s']) ⊆
          Set.range (fun (p : spec₀.Range t × QuerySeed spec₀) =>
            p.2.prependValues [p.1]) := by
        intro s hs
        simp only [Function.mem_support] at hs
        have hmem : s ∈ support (generateSeed spec₀ qc js) := by
          by_contra h; exact hs (by simp [(probOutput_eq_zero_iff _ _).2 h])
        obtain ⟨u, s', hpop⟩ := hpop_some s hmem
        exact ⟨(u, s'), QuerySeed.eq_prependValues_of_pop_eq_some hpop⟩
      rw [← (QuerySeed.prependValues_singleton_injective t).tsum_eq h_supp]
      simp only [QuerySeed.pop_prependValues_singleton]
      rw [ENNReal.tsum_prod', probOutput_bind_eq_tsum]
      congr 1; ext u
      -- Goal: ∑' s', Pr[= s'.prependValues [u]|gen] * Pr[= x|run'(mx u) s']
      --     = Pr[= u|liftM (query t)] * Pr[= x|mx u]
      have hpos : 0 < qc t * js.count t := Nat.pos_of_ne_zero (by omega)
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
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α β : Type} (oa : OracleComp spec₀ α) (ob : α → OracleComp spec₀ β) (y : β) :
    Pr[= y | do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      let x ← Prod.fst <$> (simulateQ seededOracle oa).run seed
      ob x] = Pr[= y | oa >>= ob] := by
  have h := evalDist_liftComp_generateSeed_bind_simulateQ_run' qc js oa
  rw [show (do
    let seed ← liftComp (generateSeed spec₀ qc js) spec₀
    let x ← Prod.fst <$> (simulateQ seededOracle oa).run seed
    ob x) = ((do
    let seed ← liftComp (generateSeed spec₀ qc js) spec₀
    (simulateQ seededOracle oa).run' seed) >>= ob) from by simp [bind_assoc]]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  congr 1; ext x
  congr 1
  exact congrFun (congrArg DFunLike.coe h) x

@[simp]
lemma probOutput_generateSeed_bind_map_simulateQ
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α β : Type} (oa : OracleComp spec₀ α) (f : α → β) (y : β) :
    Pr[= y | (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      f <$> Prod.fst <$> (simulateQ seededOracle oa).run seed : OracleComp spec₀ β)] =
      Pr[= y | f <$> oa] := by
  -- Reduce `map` to `bind` + `pure`, then apply the `bind` lemma.
  simpa [map_eq_bind_pure_comp, Function.comp] using
    (probOutput_generateSeed_bind_simulateQ_bind (qc := qc) (js := js)
      (oa := oa) (ob := fun x => pure (f x)) (y := y))

/-- Adding a uniform value at index `i` to a seed does not change the distribution of
running a computation with the seeded oracle. This is because the extra value replaces
what would otherwise be a fresh uniform oracle response. -/
lemma evalDist_liftComp_uniformSample_bind_simulateQ_run'_addValue
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ j, SampleableType (spec₀.Range j)] [unifSpec ⊂ₒ spec₀]
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (σ : QuerySeed spec₀) (i : ι₀) {α : Type} (oa : OracleComp spec₀ α) :
    evalDist (do
      let u ← liftComp ($ᵗ spec₀.Range i) spec₀
      (simulateQ seededOracle oa).run' (σ.addValue i u) : OracleComp spec₀ α) =
    evalDist ((simulateQ seededOracle oa).run' σ : OracleComp spec₀ α) := by
  revert σ
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro σ
    have hrun' : ∀ s, (simulateQ seededOracle (pure x : OracleComp spec₀ α)).run' s =
        (pure x : OracleComp spec₀ α) := fun s => by simp
    apply evalDist_ext; intro a
    simp_rw [hrun']
    rw [probOutput_bind_const]
    simp [HasEvalPMF.probFailure_eq_zero]
  | query_bind t mx ih =>
    intro σ
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map]
    apply evalDist_ext; intro a
    have hrun' : ∀ s : QuerySeed spec₀,
        (do let r ← seededOracle t; simulateQ seededOracle (mx r) :
          StateT _ (OracleComp spec₀) α).run' s =
        match s.pop t with
        | none => liftM (query t) >>= fun r => (simulateQ seededOracle (mx r)).run' s
        | some (r, s') => (simulateQ seededOracle (mx r)).run' s' := by
      intro s
      change Prod.fst <$>
        (seededOracle t >>= fun r => simulateQ seededOracle (mx r)).run s = _
      rw [run_bind_query_eq_pop]
      cases s.pop t with
      | none => simp [map_bind]
      | some p => rfl
    simp_rw [hrun']
    by_cases hti : t = i
    · cases hti
      cases hσi : σ i with
      | nil =>
        have hadd_pop : ∀ v, (σ.addValue i v).pop i = some (v, σ) := by
          intro v
          have hlist : (σ.addValue i v) i = [v] := by
            simp [QuerySeed.addValue, QuerySeed.addValues, hσi]
          rw [QuerySeed.pop_eq_some_of_cons _ _ v [] hlist]
          suffices Function.update (σ.addValue i v) i
              ([] : List (spec₀.Range i)) = σ by rw [this]; rfl
          funext j; by_cases hj : j = i
          · subst hj; simp [hσi]
          · rw [Function.update_of_ne hj]
            exact QuerySeed.addValues_of_ne σ [v] hj
        have horig_pop : σ.pop i = none := by
          rw [QuerySeed.pop_eq_none_iff]; exact hσi
        simp_rw [hadd_pop, horig_pop]
        rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
        congr 1; ext v; congr 1
        simp only [probOutput_liftComp, probOutput_uniformSample, probOutput_query]
      | cons u₀ rest =>
        have hadd_pop : ∀ v, (σ.addValue i v).pop i =
            some (u₀, QuerySeed.addValue (Function.update σ i rest) i v) := by
          intro v
          have hlist : (σ.addValue i v) i = u₀ :: (rest ++ [v]) := by
            simp [QuerySeed.addValue, QuerySeed.addValues, hσi]
          rw [QuerySeed.pop_eq_some_of_cons _ _ u₀ (rest ++ [v]) hlist]
          suffices Function.update (σ.addValue i v) i (rest ++ [v]) =
              QuerySeed.addValue (Function.update σ i rest) i v by rw [this]; rfl
          funext j; by_cases hj : j = i
          · subst hj; simp [QuerySeed.addValue, QuerySeed.addValues]
          · simp [Function.update_of_ne hj, QuerySeed.addValue,
              QuerySeed.addValues]
        have horig_pop : σ.pop i = some (u₀, Function.update σ i rest) :=
          QuerySeed.pop_eq_some_of_cons σ i u₀ rest hσi
        simp_rw [hadd_pop, horig_pop]
        exact congrFun (congrArg DFunLike.coe (ih u₀ (Function.update σ i rest))) a
    · cases hσt : σ t with
      | nil =>
        have hadd_pop : ∀ v, (σ.addValue i v).pop t = none := by
          intro v; rw [QuerySeed.pop_eq_none_iff]
          exact (QuerySeed.addValues_of_ne σ [_] hti).trans hσt
        have horig_pop : σ.pop t = none := by
          rw [QuerySeed.pop_eq_none_iff]; exact hσt
        simp_rw [hadd_pop, horig_pop]
        rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
        simp_rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left, mul_left_comm]
        rw [ENNReal.tsum_comm]
        simp_rw [ENNReal.tsum_mul_left]
        congr 1; ext r; congr 1
        rw [← probOutput_bind_eq_tsum]
        exact congrFun (congrArg DFunLike.coe (ih r σ)) a
      | cons u₀ rest =>
        have hadd_pop : ∀ v, (σ.addValue i v).pop t =
            some (u₀, QuerySeed.addValue (Function.update σ t rest) i v) := by
          intro v
          have hlist : (σ.addValue i v) t = u₀ :: rest :=
            (QuerySeed.addValues_of_ne σ [_] hti).trans hσt
          rw [QuerySeed.pop_eq_some_of_cons _ _ u₀ rest hlist]
          suffices Function.update (σ.addValue i v) t rest =
              QuerySeed.addValue (Function.update σ t rest) i v by rw [this]; rfl
          change Function.update (Function.update σ i (σ i ++ [v])) t rest =
            Function.update (Function.update σ t rest) i
              ((Function.update σ t rest) i ++ [v])
          conv_rhs =>
            rw [show (Function.update σ t rest) i = σ i from
              Function.update_of_ne (Ne.symm hti) rest σ]
          exact Function.update_comm (Ne.symm hti) (σ i ++ [v]) rest σ
        have horig_pop : σ.pop t = some (u₀, Function.update σ t rest) :=
          QuerySeed.pop_eq_some_of_cons σ t u₀ rest hσt
        simp_rw [hadd_pop, horig_pop]
        exact congrFun (congrArg DFunLike.coe
          (ih u₀ (Function.update σ t rest))) a

lemma evalDist_liftComp_replicate_uniformSample_bind_simulateQ_run'_addValues
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ j, SampleableType (spec₀.Range j)] [unifSpec ⊂ₒ spec₀]
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (i : ι₀) {α : Type} (oa : OracleComp spec₀ α) (n : ℕ) :
    ∀ (σ : QuerySeed spec₀),
    evalDist (do
      let us ← liftComp (replicate n ($ᵗ spec₀.Range i)) spec₀
      (simulateQ seededOracle oa).run' (σ.addValues us) : OracleComp spec₀ α) =
    evalDist ((simulateQ seededOracle oa).run' σ : OracleComp spec₀ α) := by
  induction n with
  | zero => intro σ; simp [replicate_zero, QuerySeed.addValues_nil]
  | succ n ih =>
    intro σ
    simp only [replicate_succ, seq_eq_bind_map, map_eq_bind_pure_comp,
      liftComp_bind, liftComp_pure, bind_assoc, Function.comp, pure_bind]
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

/-- Truncating the seed at oracle `i₀` to only the first `k` entries does not change
the distribution when averaging over seeds from `generateSeed`. -/
lemma evalDist_liftComp_generateSeed_bind_simulateQ_run'_takeAtIndex
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀) (i₀ : ι₀) (k : ℕ)
    {α : Type} (oa : OracleComp spec₀ α) :
    evalDist (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      (simulateQ seededOracle oa).run' (seed.takeAtIndex i₀ k) : OracleComp spec₀ α) =
    evalDist oa := by
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
        | some (u, s') => (simulateQ seededOracle (mx u)).run' s' := by
      intro s
      change Prod.fst <$>
        (seededOracle t >>= fun u => simulateQ seededOracle (mx u)).run s = _
      rw [run_bind_query_eq_pop]
      cases s.pop t with
      | none => simp [map_bind]
      | some p => rfl
    simp_rw [hrun']
    rw [probOutput_bind_eq_tsum]
    simp_rw [probOutput_liftComp]
    by_cases hpop_none : qc t * js.count t = 0 ∨ (t = i₀ ∧ k = 0)
    · -- Pop from the take'd seed gives none
      have hpop : ∀ s ∈ support (generateSeed spec₀ qc js),
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
      have hih : Pr[= x | (liftComp (generateSeed spec₀ qc js) spec₀ >>= fun seed =>
          (simulateQ seededOracle (mx u)).run' (seed.takeAtIndex i₀ k))] = Pr[= x | mx u] :=
        congrFun (congrArg DFunLike.coe (ih u qc js k)) x
      rw [show Pr[= x | liftComp (generateSeed spec₀ qc js) spec₀ >>= fun seed =>
          (simulateQ seededOracle (mx u)).run' (seed.takeAtIndex i₀ k)] =
        ∑' s, Pr[= s | generateSeed spec₀ qc js] *
          Pr[= x | (simulateQ seededOracle (mx u)).run' (s.takeAtIndex i₀ k)] from by
        rw [probOutput_bind_eq_tsum]; simp_rw [probOutput_liftComp]] at hih
      exact hih
    · -- Pop from the take'd seed gives some
      push Not at hpop_none
      obtain ⟨hcount_ne, htk⟩ := hpop_none
      have hcount : 0 < qc t * js.count t := Nat.pos_of_ne_zero (by omega)
      -- Original seed always has non-empty list at t
      have hpop_orig : ∀ s ∈ support (generateSeed spec₀ qc js),
          ∃ u s', s.pop t = some (u, s') := by
        intro s hs
        have hne : s t ≠ [] :=
          ne_nil_of_mem_support_generateSeed (spec := spec₀) (qc := qc) (js := js) s t hs
            (Nat.pos_of_ne_zero (by omega))
        obtain ⟨u, us, hcons⟩ := List.exists_cons_of_ne_nil hne
        exact ⟨u, Function.update s t us, QuerySeed.pop_eq_some_of_cons s t u us hcons⟩
      -- Take'd seed also has non-empty list at t
      have hpop_take : ∀ s ∈ support (generateSeed spec₀ qc js),
          ∃ u s', (s.takeAtIndex i₀ k).pop t = some (u, s') := by
        intro s hs
        have hne : s t ≠ [] :=
          ne_nil_of_mem_support_generateSeed (spec := spec₀) (qc := qc) (js := js) s t hs
            (Nat.pos_of_ne_zero (by omega))
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
      -- h_supp uses the ORIGINAL seed's pop for reparametrization
      have h_supp : Function.support (fun s =>
          Pr[= s | generateSeed spec₀ qc js] *
            match (s.takeAtIndex i₀ k).pop t with
            | none => 0
            | some (u, s') => Pr[= x | (simulateQ seededOracle (mx u)).run' s']) ⊆
          Set.range (fun (p : spec₀.Range t × QuerySeed spec₀) =>
            p.2.prependValues [p.1]) := by
        intro s hs
        simp only [Function.mem_support] at hs
        have hmem : s ∈ support (generateSeed spec₀ qc js) := by
          by_contra h; exact hs (by simp [(probOutput_eq_zero_iff _ _).2 h])
        obtain ⟨u, s', hpop⟩ := hpop_orig s hmem
        exact ⟨(u, s'), QuerySeed.eq_prependValues_of_pop_eq_some hpop⟩
      rw [← (QuerySeed.prependValues_singleton_injective t).tsum_eq h_supp]
      -- After reparametrization: seed = s'.prependValues [u₀]
      -- Use helper lemmas for pop of take'd seed after prependValues
      by_cases hti : t = i₀
      · -- t = i₀, k > 0: pop consumes from the take'd prefix, k decreases by 1
        subst hti
        have hk : 0 < k := Nat.pos_of_ne_zero (htk rfl)
        simp only [QuerySeed.pop_takeAtIndex_prependValues_self _ _ _ hk]
        rw [ENNReal.tsum_prod', probOutput_bind_eq_tsum]
        congr 1; ext u
        have hfact := fun s' =>
          probOutput_generateSeed_prependValues spec₀ qc js u s' hcount
        simp_rw [hfact, mul_assoc]
        rw [ENNReal.tsum_mul_left]
        congr 1
        · exact (probOutput_query _ u).symm
        · suffices h : Pr[= x | (do
              let seed ← liftComp (generateSeed spec₀
                  (Function.update (fun j => qc j * js.count j) t
                    (qc t * js.count t - 1))
                  js.dedup) spec₀
              (simulateQ seededOracle (mx u)).run'
                (seed.takeAtIndex t (k - 1)))] = Pr[= x | mx u] by
            rw [probOutput_bind_eq_tsum] at h
            simp_rw [probOutput_liftComp] at h
            exact h
          exact congrFun (congrArg DFunLike.coe (ih u _ js.dedup (k - 1))) x
      · -- t ≠ i₀: pop consumes from oracle t, k stays the same
        simp only [QuerySeed.pop_takeAtIndex_prependValues_of_ne _ _ _ _ hti]
        rw [ENNReal.tsum_prod', probOutput_bind_eq_tsum]
        congr 1; ext u
        have hfact := fun s' =>
          probOutput_generateSeed_prependValues spec₀ qc js u s' hcount
        simp_rw [hfact, mul_assoc]
        rw [ENNReal.tsum_mul_left]
        congr 1
        · exact (probOutput_query t u).symm
        · suffices h : Pr[= x | (do
              let seed ← liftComp (generateSeed spec₀
                  (Function.update (fun j => qc j * js.count j) t
                    (qc t * js.count t - 1))
                  js.dedup) spec₀
              (simulateQ seededOracle (mx u)).run'
                (seed.takeAtIndex i₀ k))] = Pr[= x | mx u] by
            rw [probOutput_bind_eq_tsum] at h
            simp_rw [probOutput_liftComp] at h
            exact h
          exact congrFun (congrArg DFunLike.coe (ih u _ js.dedup k)) x

@[simp]
lemma probOutput_generateSeed_bind_map_simulateQ_takeAtIndex
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀) (i₀ : ι₀) (k : ℕ)
    {α β : Type} (oa : OracleComp spec₀ α) (f : α → β) (y : β) :
    Pr[= y | (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      f <$> (simulateQ seededOracle oa).run' (seed.takeAtIndex i₀ k) : OracleComp spec₀ β)] =
      Pr[= y | f <$> oa] := by
  have h := evalDist_liftComp_generateSeed_bind_simulateQ_run'_takeAtIndex
    qc js i₀ k oa
  have hcomp : (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      f <$> (simulateQ seededOracle oa).run' (seed.takeAtIndex i₀ k) : OracleComp spec₀ β) =
    f <$> (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      (simulateQ seededOracle oa).run' (seed.takeAtIndex i₀ k)) := by
    simp only [map_bind]
  rw [hcomp]
  exact congrFun (congrArg DFunLike.coe (by simp only [evalDist_map, h])) y

/-- Weighted takeAtIndex faithfulness: a prefix-dependent weight `h` preserves the
faithfulness equality between full-seed and truncated-seed simulation.
This generalizes the basic takeAtIndex faithfulness by allowing multiplication
by an arbitrary function of the seed prefix `σ.takeAtIndex i₀ k`. -/
lemma tsum_probOutput_generateSeed_weight_takeAtIndex
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [OracleSpec.LawfulSubSpec unifSpec spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
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
        | some (u, s') => (simulateQ seededOracle (mx u)).run' s' := by
      intro s
      change Prod.fst <$>
        (seededOracle t >>= fun u => simulateQ seededOracle (mx u)).run s = _
      rw [run_bind_query_eq_pop]
      cases s.pop t with
      | none => simp [map_bind]
      | some p => rfl
    simp_rw [hrun']
    have hcomm : ∀ (g : spec₀.Range t → QuerySeed spec₀ → OracleComp spec₀ α),
        ∑' s, Pr[= s | generateSeed spec₀ qc js] *
          (h (s.takeAtIndex i₀ k) *
            ∑' u, Pr[= u | (liftM (query t) : OracleComp spec₀ _)] *
              Pr[= x | g u s]) =
        ∑' u, Pr[= u | (liftM (query t) : OracleComp spec₀ _)] *
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
      have step_full : ∀ s,
          Pr[= s | generateSeed spec₀ qc js] *
            (h (s.takeAtIndex i₀ k) * Pr[= x | match s.pop t with
              | none => liftM (query t) >>= fun u =>
                  (simulateQ seededOracle (mx u)).run' s
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s']) =
          Pr[= s | generateSeed spec₀ qc js] *
            (h (s.takeAtIndex i₀ k) * Pr[= x | liftM (query t) >>= fun u =>
                (simulateQ seededOracle (mx u)).run' s]) := by
        intro s
        by_cases hs : s ∈ support (generateSeed spec₀ qc js)
        · simp [hpop_full s hs]
        · simp [(probOutput_eq_zero_iff _ _).2 hs]
      have step_take : ∀ s,
          Pr[= s | generateSeed spec₀ qc js] *
            (h (s.takeAtIndex i₀ k) * Pr[= x | match (s.takeAtIndex i₀ k).pop t with
              | none => liftM (query t) >>= fun u =>
                  (simulateQ seededOracle (mx u)).run' (s.takeAtIndex i₀ k)
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s']) =
          Pr[= s | generateSeed spec₀ qc js] *
            (h (s.takeAtIndex i₀ k) * Pr[= x | liftM (query t) >>= fun u =>
                (simulateQ seededOracle (mx u)).run' (s.takeAtIndex i₀ k)]) := by
        intro s
        by_cases hs : s ∈ support (generateSeed spec₀ qc js)
        · simp [hpop_take s hs]
        · simp [(probOutput_eq_zero_iff _ _).2 hs]
      simp_rw [step_full, step_take, probOutput_bind_eq_tsum (liftM (query t))]
      rw [hcomm, hcomm]
      congr 1; ext u; congr 1
      exact ih u qc js k h
    · -- Case 2+3: seed has entries at oracle t
      push Not at hcount_zero
      have hcount : 0 < qc t * js.count t := Nat.pos_of_ne_zero (by omega)
      have hpop_orig : ∀ s ∈ support (generateSeed spec₀ qc js),
          ∃ u s', s.pop t = some (u, s') := by
        intro s hs
        have hne : s t ≠ [] :=
          ne_nil_of_mem_support_generateSeed (spec := spec₀) (qc := qc) (js := js) s t hs
            (Nat.pos_of_ne_zero (by omega))
        obtain ⟨u, us, hcons⟩ := List.exists_cons_of_ne_nil hne
        exact ⟨u, Function.update s t us, QuerySeed.pop_eq_some_of_cons s t u us hcons⟩
      have h_supp_full : Function.support (fun s =>
          Pr[= s | generateSeed spec₀ qc js] *
            (h (s.takeAtIndex i₀ k) * Pr[= x | match s.pop t with
              | none => liftM (query t) >>= fun u =>
                  (simulateQ seededOracle (mx u)).run' s
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s'])) ⊆
          Set.range (fun (p : spec₀.Range t × QuerySeed spec₀) =>
            p.2.prependValues [p.1]) := by
        intro s hs
        simp only [Function.mem_support] at hs
        have hmem : s ∈ support (generateSeed spec₀ qc js) := by
          by_contra hc; exact hs (by simp [(probOutput_eq_zero_iff _ _).2 hc])
        obtain ⟨u, s', hpop⟩ := hpop_orig s hmem
        exact ⟨(u, s'), QuerySeed.eq_prependValues_of_pop_eq_some hpop⟩
      have h_supp_take : Function.support (fun s =>
          Pr[= s | generateSeed spec₀ qc js] *
            (h (s.takeAtIndex i₀ k) * Pr[= x | match (s.takeAtIndex i₀ k).pop t with
              | none => liftM (query t) >>= fun u =>
                  (simulateQ seededOracle (mx u)).run' (s.takeAtIndex i₀ k)
              | some (u, s') => (simulateQ seededOracle (mx u)).run' s'])) ⊆
          Set.range (fun (p : spec₀.Range t × QuerySeed spec₀) =>
            p.2.prependValues [p.1]) := by
        intro s hs
        simp only [Function.mem_support] at hs
        have hmem : s ∈ support (generateSeed spec₀ qc js) := by
          by_contra hc; exact hs (by simp [(probOutput_eq_zero_iff _ _).2 hc])
        obtain ⟨u, s', hpop⟩ := hpop_orig s hmem
        exact ⟨(u, s'), QuerySeed.eq_prependValues_of_pop_eq_some hpop⟩
      rw [← (QuerySeed.prependValues_singleton_injective t).tsum_eq h_supp_full,
        ← (QuerySeed.prependValues_singleton_injective t).tsum_eq h_supp_take]
      simp only [QuerySeed.pop_prependValues_singleton]
      by_cases hti : t = i₀
      · subst hti
        by_cases hk : k = 0
        · -- Case 3: t = i₀, k = 0 — LHS pop some, RHS pop none
          subst hk
          have htake_zero : ∀ (u₀ : spec₀.Range t) (s' : QuerySeed spec₀),
              (QuerySeed.prependValues s' [u₀]).takeAtIndex t 0 =
              QuerySeed.takeAtIndex s' t 0 := by
            intro u₀ s'; funext j; by_cases hj : j = t
            · subst hj; simp [QuerySeed.takeAtIndex_apply_self]
            · simp [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hj,
                QuerySeed.prependValues_of_ne _ _ hj]
          have hpop_rhs : ∀ (s' : QuerySeed spec₀),
              (QuerySeed.takeAtIndex s' t 0).pop t = none := by
            intro s'; rw [QuerySeed.pop_eq_none_iff]
            simp [QuerySeed.takeAtIndex]
          simp_rw [htake_zero, hpop_rhs]
          rw [ENNReal.tsum_prod']; conv_rhs => rw [ENNReal.tsum_prod']
          simp_rw [probOutput_generateSeed_prependValues spec₀ qc js _ _ hcount,
            mul_assoc]
          conv_lhs =>
            arg 1
            intro u₀
            rw [ENNReal.tsum_mul_left]
          conv_rhs =>
            arg 1
            intro u₀
            rw [ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_mul_left]; conv_rhs => rw [ENNReal.tsum_mul_left]
          congr 1
          conv_lhs =>
            arg 1
            intro u₀
            rw [ih u₀ _ js.dedup 0 h]
          rw [ENNReal.tsum_comm]; conv_rhs => rw [ENNReal.tsum_comm]
          congr 1; ext s'
          rw [ENNReal.tsum_mul_left]; conv_rhs => rw [ENNReal.tsum_mul_left]
          congr 1
          rw [ENNReal.tsum_mul_left]; conv_rhs => rw [ENNReal.tsum_mul_left]
          congr 1
          conv_rhs => rw [probOutput_bind_eq_tsum (liftM (query t) : OracleComp spec₀ _)]
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
          have htake_prepend : ∀ (s' : QuerySeed spec₀),
              (QuerySeed.prependValues s' [u₀]).takeAtIndex t k =
              QuerySeed.prependValues (QuerySeed.takeAtIndex s' t (k - 1)) [u₀] := by
            intro s'; funext j; by_cases hj : j = t
            · subst hj
              simp only [QuerySeed.takeAtIndex_apply_self,
                QuerySeed.prependValues_singleton]
              conv_lhs =>
                rw [show k = (k - 1) + 1 from (Nat.succ_pred_eq_of_pos hk_pos).symm]
              rw [List.take_succ_cons]
            · simp [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hj,
                QuerySeed.prependValues_of_ne _ _ hj]
          simp_rw [htake_prepend]
          have hfact := fun (s' : QuerySeed spec₀) =>
            probOutput_generateSeed_prependValues spec₀ qc js u₀ s' hcount
          simp_rw [hfact, mul_assoc]
          rw [ENNReal.tsum_mul_left]
          conv_rhs => rw [ENNReal.tsum_mul_left]
          congr 1
          exact ih u₀ _ js.dedup (k - 1)
            (fun σ => h (QuerySeed.prependValues σ [u₀]))
      · -- Case 2b: t ≠ i₀ — both pop some, k unchanged
        simp only [QuerySeed.pop_takeAtIndex_prependValues_of_ne _ _ _ _ hti]
        rw [ENNReal.tsum_prod']
        conv_rhs => rw [ENNReal.tsum_prod']
        congr 1; ext u₀
        have htake_prepend : ∀ (s' : QuerySeed spec₀),
            (QuerySeed.prependValues s' [u₀]).takeAtIndex i₀ k =
            QuerySeed.prependValues (QuerySeed.takeAtIndex s' i₀ k) [u₀] := by
          intro s'; funext j; by_cases hji : j = i₀
          · subst hji
            simp [QuerySeed.takeAtIndex_apply_self,
              QuerySeed.prependValues_of_ne _ _ (Ne.symm hti)]
          · rw [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hji]
            by_cases hjt : j = t
            · subst hjt
              simp [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hti]
            · simp [QuerySeed.prependValues_of_ne _ _ hjt,
                QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hji]
        simp_rw [htake_prepend]
        have hfact := fun (s' : QuerySeed spec₀) =>
          probOutput_generateSeed_prependValues spec₀ qc js u₀ s' hcount
        simp_rw [hfact, mul_assoc]
        rw [ENNReal.tsum_mul_left]
        conv_rhs => rw [ENNReal.tsum_mul_left]
        congr 1
        exact ih u₀ _ js.dedup k
          (fun σ => h (QuerySeed.prependValues σ [u₀]))

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
      have hrun' :
          (do let r ← seededOracle t; simulateQ seededOracle (mx r) :
            StateT (QuerySeed spec) (OracleComp spec) α).run' seed =
          match seed.pop t with
          | none => liftM (query t) >>= fun r => (simulateQ seededOracle (mx r)).run' seed
          | some (r, seed') => (simulateQ seededOracle (mx r)).run' seed' := by
        change Prod.fst <$> ((seededOracle t >>= fun r => simulateQ seededOracle (mx r)).run seed) =
          _
        rw [run_bind_query_eq_pop]
        cases hpop : seed.pop t with
        | none => simp [map_bind]
        | some p => rfl
      rw [show (simulateQ seededOracle (liftM (query t) >>= mx)).run' seed =
          ((do let r ← seededOracle t; simulateQ seededOracle (mx r) :
            StateT (QuerySeed spec) (OracleComp spec) α).run' seed) by
            simp]
      rw [hrun']
      cases hpop : seed.pop t with
      | none =>
          rw [isPerIndexQueryBound_query_bind_iff]
          have hres_pos : 0 < residual t := by
            have hlen0 : (seed t).length = 0 := by
              simpa [QuerySeed.pop_eq_none_iff] using hpop
            have hcov_t : qb t - residual t ≤ 0 := by
              simpa [hlen0] using hcover t
            omega
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
                  have hsub :
                      (qb j - 1) - (residual j - 1) = qb j - residual j := by
                    omega
                  simpa [Function.update_self, hsub] using hcov_j
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
                  have hseedt : seed j = u :: seed' j := by
                    simpa using (QuerySeed.cons_of_pop_eq_some seed j u seed' hpop).symm
                  have hcov_j' : qb j - residual j ≤ (seed' j).length + 1 := by
                    simpa [hseedt] using hcov_j
                  simp [Function.update_self]
                  by_cases hle : qb j ≤ residual j
                  · omega
                  · have hlt : residual j < qb j := Nat.lt_of_not_ge hle
                    omega
                · rcases QuerySeed.rest_eq_update_tail_of_pop_eq_some seed t u seed' hpop with hrest
                  have hseed'_j : seed' j = seed j := by
                    have := congrArg (fun s => s j) hrest
                    simpa [Function.update_of_ne hj] using this
                  simpa [Function.update_of_ne hj, hseed'_j, hj] using hcov_j))

/-- A seed that covers the full structural query bound eliminates all live oracle queries. -/
theorem isPerIndexQueryBound_run'_zero
    {oa : OracleComp spec α} {qb : ι → ℕ} {seed : QuerySeed spec}
    (hqb : IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t ≤ (seed t).length) :
    IsPerIndexQueryBound ((simulateQ seededOracle oa).run' seed) 0 := by
  refine isPerIndexQueryBound_run'_of_seedCoverage (oa := oa) (qb := qb) (residual := 0)
    (seed := seed) hqb ?_
  intro t
  simpa using hcover t

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
  by_cases ht : t = i
  · subst ht
    have hlen : qb t ≤ (seed t).length := hcover t
    have hk' : k ≤ (seed t).length := le_trans hk hlen
    rw [QuerySeed.takeAtIndex_apply_self, Function.update_self]
    simp
    omega
  · simpa [Function.update_of_ne ht, QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ ht] using hcover t

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
    have hs0 : ↑s ≤ qb t := Nat.lt_succ_iff.mp s.2
    have hlen : qb t ≤ (seed t).length := hcover t
    have hs' : ↑s ≤ (seed t).length := le_trans hs0 hlen
    simp [QuerySeed.addValue, QuerySeed.addValues]
    omega
  · simp [QuerySeed.addValue, QuerySeed.addValues, ht, hcover t]

end queryBounds

end seededOracle
