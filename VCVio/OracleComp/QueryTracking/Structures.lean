/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import PolyFun.PFunctor.Trace
public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Structures For Tracking a Computation's Oracle Queries

This file defines types like `QueryLog` and `QueryCache` for use with
simulation oracles and implementation transformers defined in the same directory.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp

/- Query logs are definitionally PolyFun traces for an oracle specification. These reducers
must remain available at implicit transparency when specializing that generic API. -/
attribute [local implicit_reducible] PFunctor.Idx FreeMonoid

universe u v w

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec ι}

/-- Type to represent a cache of queries to oracles in `spec`.
Defined to be a function from (indexed) inputs to an optional output. -/
@[reducible] def QueryCache (spec : OracleSpec.{u, v} ι) : Type (max u v) :=
  (t : spec.Domain) → Option (spec.Range t)

namespace QueryCache

instance : EmptyCollection (QueryCache spec) := ⟨fun _ => none⟩

@[simp]
lemma empty_apply (t : spec.Domain) : (∅ : QueryCache spec) t = none := rfl

@[ext]
protected lemma ext {c₁ c₂ : QueryCache spec} (h : ∀ t, c₁ t = c₂ t) : c₁ = c₂ :=
  funext h

/-! ### Agreement with answer functions -/

/-- A total answer function agrees with a cache if it returns every cached response. -/
@[grind]
def AgreesWithFn (f : QueryImpl spec Id) (cache : QueryCache spec) : Prop :=
  ∀ ⦃t : spec.Domain⦄ ⦃r : spec.Range t⦄, cache t = some r → f t = r

/-- Every cache is extended by some total answer function. -/
lemma exists_agreesWithFn [spec.Inhabited] (cache : QueryCache spec) :
    ∃ f : QueryImpl spec Id, cache.AgreesWithFn f := by
  refine ⟨fun t => (cache t).getD default, ?_⟩
  intro t r h
  simp [h]

/-! ### Partial Order

A `QueryCache` carries a natural partial order where `c₁ ≤ c₂` means every cached entry
in `c₁` also appears (with the same value) in `c₂`. The empty cache is the bottom element. -/

instance : PartialOrder (QueryCache spec) where
  le c₁ c₂ := ∀ ⦃t⦄ ⦃u : spec.Range t⦄, c₁ t = some u → c₂ t = some u
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁₂ h₂₃ _ _ h := h₂₃ (h₁₂ h)
  le_antisymm a b hab hba := by funext t; aesop

instance : OrderBot (QueryCache spec) where
  bot := ∅
  bot_le _ := by intro _ _ h; simp at h

@[simp]
lemma bot_eq_empty : (⊥ : QueryCache spec) = ∅ := rfl

@[grind =]
lemma le_def {c₁ c₂ : QueryCache spec} :
    c₁ ≤ c₂ ↔ ∀ ⦃t⦄ ⦃u : spec.Range t⦄, c₁ t = some u → c₂ t = some u :=
  ⟨fun h => h, fun h => h⟩

/-! ### Query membership -/

/-- Check whether a query `t` has a cached response. -/
def isCached (cache : QueryCache spec) (t : spec.Domain) : Bool :=
  (cache t).isSome

@[simp]
lemma isCached_empty (t : spec.Domain) : isCached (∅ : QueryCache spec) t = false := rfl

/-! ### Conversion to a set of query-response pairs -/

/-- The set of all `(query, response)` pairs stored in the cache. -/
def toSet (cache : QueryCache spec) : Set ((t : spec.Domain) × spec.Range t) :=
  fun ⟨t, r⟩ => cache t = some r

@[simp]
lemma mem_toSet {cache : QueryCache spec} {t : spec.Domain} {r : spec.Range t} :
    ⟨t, r⟩ ∈ cache.toSet ↔ cache t = some r :=
  Iff.rfl

@[simp]
lemma toSet_empty : (∅ : QueryCache spec).toSet = ∅ := by
  ext ⟨t, r⟩; simp

lemma toSet_mono {c₁ c₂ : QueryCache spec} (h : c₁ ≤ c₂) : c₁.toSet ⊆ c₂.toSet :=
  fun ⟨_, _⟩ hx => h hx

/-- Number of live entries in a query cache, as an `ℝ≥0∞` resource. -/
noncomputable def enncard (cache : QueryCache spec) : ℝ≥0∞ :=
  (cache.toSet.encard : ℝ≥0∞)

@[simp]
lemma enncard_empty : enncard (∅ : QueryCache spec) = 0 := by
  simp [enncard]

/-! ### Cache update -/

variable [DecidableEq ι] (cache : QueryCache spec)

/- `simp` does not currently specialize Mathlib's dependent `Function.update` equations through
the `QueryCache` abbreviation. Keep that representation detail behind cache-specific equations. -/
@[simp]
lemma functionUpdate_self (t : spec.Domain) (u : spec.Range t) :
    Function.update cache t (some u) t = some u :=
  Function.update_self t (some u) cache

@[simp]
lemma functionUpdate_of_ne {t' t : spec.Domain} (u : spec.Range t) (h : t' ≠ t) :
    Function.update cache t (some u) t' = cache t' :=
  Function.update_of_ne h (some u) cache

/-- Add an index + input pair to the cache by updating the function
(wrapper around `Function.update`). -/
def cacheQuery (t : spec.Domain) (u : spec.Range t) : QueryCache spec :=
  Function.update cache t u

@[simp, grind =]
lemma cacheQuery_self (t : spec.Domain) (u : spec.Range t) :
    (cache.cacheQuery t u) t = some u := by
  simp [cacheQuery]

@[simp, grind =]
lemma cacheQuery_of_ne {t' t : spec.Domain} (u : spec.Range t) (h : t' ≠ t) :
    (cache.cacheQuery t u) t' = cache t' := by
  simp [cacheQuery, h]

/-- An answer function agrees with `cache.cacheQuery t u` iff it agrees with `cache` and returns
`u` on `t`, provided `t` was not already cached. -/
lemma agreesWithFn_cacheQuery_iff (t : spec.Domain) (u : spec.Range t) (f : QueryImpl spec Id)
    (hcache : cache t = none) :
    (cache.cacheQuery t u).AgreesWithFn f ↔ cache.AgreesWithFn f ∧ f t = u := by
  grind [cacheQuery]

lemma toSet_cacheQuery_subset_insert (t : spec.Domain) (u : spec.Range t) :
    (cache.cacheQuery t u).toSet ⊆ insert ⟨t, u⟩ cache.toSet := by
  rintro ⟨t', u'⟩ hmem
  rcases eq_or_ne t' t with ht | ht
  · subst t'
    change cache.cacheQuery t u t = some u' at hmem
    have hu : u = u' := Option.some.inj ((cacheQuery_self cache t u).symm.trans hmem)
    subst u'
    exact Set.mem_insert _ _
  · right
    change cache.cacheQuery t u t' = some u' at hmem
    change cache t' = some u'
    rw [← cacheQuery_of_ne cache u ht]
    exact hmem

lemma toSet_encard_cacheQuery_le (t : spec.Domain) (u : spec.Range t) :
    (cache.cacheQuery t u).toSet.encard ≤ cache.toSet.encard + 1 :=
  le_trans (Set.encard_le_encard (toSet_cacheQuery_subset_insert cache t u))
    (Set.encard_insert_le cache.toSet ⟨t, u⟩)

lemma enncard_cacheQuery_le (t : spec.Domain) (u : spec.Range t) :
    enncard (cache.cacheQuery t u) ≤ enncard cache + 1 := by
  simp only [enncard]
  exact_mod_cast toSet_encard_cacheQuery_le cache t u

lemma le_cacheQuery {t : spec.Domain} {u : spec.Range t} (h : cache t = none) :
    cache ≤ cache.cacheQuery t u := by grind

lemma cacheQuery_mono {c₁ c₂ : QueryCache spec} (h : c₁ ≤ c₂) (t : spec.Domain)
    (u : spec.Range t) : c₁.cacheQuery t u ≤ c₂.cacheQuery t u := by
  intro t' u' ht'
  rcases eq_or_ne t' t with rfl | heq
  · simpa only [cacheQuery_self] using ht'
  · exact cacheQuery_of_ne c₂ u heq ▸ h (cacheQuery_of_ne c₁ u heq ▸ ht')

@[simp]
lemma isCached_cacheQuery_self (t : spec.Domain) (u : spec.Range t) :
    (cache.cacheQuery t u).isCached t = true := by
  simp [isCached]

@[simp]
lemma isCached_cacheQuery_of_ne {t' t : spec.Domain} (u : spec.Range t) (h : t' ≠ t) :
    (cache.cacheQuery t u).isCached t' = cache.isCached t' := by
  simp [isCached, cacheQuery_of_ne cache u h]

/-! ### Sum spec projections -/

section sum

variable {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

/-- Project a cache for `spec₁ + spec₂` onto `spec₁`. -/
protected def fst (cache : QueryCache (spec₁ + spec₂)) : QueryCache spec₁ :=
  fun t => cache (.inl t)

/-- Project a cache for `spec₁ + spec₂` onto `spec₂`. -/
protected def snd (cache : QueryCache (spec₁ + spec₂)) : QueryCache spec₂ :=
  fun t => cache (.inr t)

/-- Embed a cache for `spec₁` into one for `spec₁ + spec₂`. -/
protected def inl (cache : QueryCache spec₁) : QueryCache (spec₁ + spec₂) :=
  Sum.rec cache (fun _ => none)

/-- Embed a cache for `spec₂` into one for `spec₁ + spec₂`. -/
protected def inr (cache : QueryCache spec₂) : QueryCache (spec₁ + spec₂) :=
  Sum.rec (fun _ => none) cache

@[simp] lemma fst_apply (cache : QueryCache (spec₁ + spec₂)) (t : ι₁) :
    cache.fst t = cache (.inl t) := rfl

@[simp] lemma snd_apply (cache : QueryCache (spec₁ + spec₂)) (t : ι₂) :
    cache.snd t = cache (.inr t) := rfl

@[simp] lemma inl_apply_inl (cache : QueryCache spec₁) (t : ι₁) :
    (cache.inl : QueryCache (spec₁ + spec₂)) (.inl t) = cache t := rfl

@[simp] lemma inl_apply_inr (cache : QueryCache spec₁) (t : ι₂) :
    (cache.inl : QueryCache (spec₁ + spec₂)) (.inr t) = none := rfl

@[simp] lemma inr_apply_inl (cache : QueryCache spec₂) (t : ι₁) :
    (cache.inr : QueryCache (spec₁ + spec₂)) (.inl t) = none := rfl

@[simp] lemma inr_apply_inr (cache : QueryCache spec₂) (t : ι₂) :
    (cache.inr : QueryCache (spec₁ + spec₂)) (.inr t) = cache t := rfl

@[simp] lemma fst_inl (cache : QueryCache spec₁) :
    (cache.inl : QueryCache (spec₁ + spec₂)).fst = cache := rfl

@[simp] lemma snd_inr (cache : QueryCache spec₂) :
    (cache.inr : QueryCache (spec₁ + spec₂)).snd = cache := rfl

@[simp] lemma fst_inr (cache : QueryCache spec₂) :
    (cache.inr : QueryCache (spec₁ + spec₂)).fst = ∅ := rfl

@[simp] lemma snd_inl (cache : QueryCache spec₁) :
    (cache.inl : QueryCache (spec₁ + spec₂)).snd = ∅ := rfl

/-- Embedding a left-component cache commutes with caching a left-component query. -/
@[simp]
lemma inl_cacheQuery [DecidableEq ι₁] [DecidableEq ι₂]
    (cache : QueryCache spec₁) (t : spec₁.Domain) (u : spec₁.Range t) :
    (cache.cacheQuery t u).inl =
      (cache.inl : QueryCache (spec₁ + spec₂)).cacheQuery (.inl t) u := by
  unfold QueryCache.cacheQuery QueryCache.inl
  exact Sum.rec_update_left (γ := fun t => Option ((spec₁ + spec₂).Range t))
    cache (fun _ => none) t (some u)

/-- Embedding a right-component cache commutes with caching a right-component query. -/
@[simp]
lemma inr_cacheQuery [DecidableEq ι₁] [DecidableEq ι₂]
    (cache : QueryCache spec₂) (t : spec₂.Domain) (u : spec₂.Range t) :
    (cache.cacheQuery t u).inr =
      (cache.inr : QueryCache (spec₁ + spec₂)).cacheQuery (.inr t) u := by
  unfold QueryCache.cacheQuery QueryCache.inr
  exact Sum.rec_update_right (γ := fun t => Option ((spec₁ + spec₂).Range t))
    (fun _ => none) cache t (some u)

@[simp] lemma fst_empty :
    (∅ : QueryCache (spec₁ + spec₂)).fst = (∅ : QueryCache spec₁) := rfl

@[simp] lemma snd_empty :
    (∅ : QueryCache (spec₁ + spec₂)).snd = (∅ : QueryCache spec₂) := rfl

instance : Coe (QueryCache spec₁) (QueryCache (spec₁ + spec₂)) := ⟨QueryCache.inl⟩
instance : Coe (QueryCache spec₂) (QueryCache (spec₁ + spec₂)) := ⟨QueryCache.inr⟩

end sum

end QueryCache

/-- Simple wrapper in order to introduce the `Monoid` structure for `countingOracle`.
Marked as reducible and can generally be treated as just a function.
`idx` gives the "index" for a given input.

A `QueryCount ι` is a commutative monoid under pointwise addition; it is
exactly the trace-monoid value type used by `QueryImpl.withCost`, which
attaches a `WriterT (QueryCount ι) m` writer effect via the generic
`QueryImpl.withTraceBefore` primitive in
`VCVio/OracleComp/QueryTracking/Tracing.lean`. -/
@[reducible] def QueryCount (ι : Type*) := ι → ℕ

namespace QueryCount

/-- Pointwise addition as the `Monoid` operation used for `WriterT`. -/
instance : Monoid (QueryCount ι) where
  mul qc qc' := qc + qc'
  mul_assoc := add_assoc
  one := 0
  one_mul := zero_add
  mul_one := add_zero
  npow n qc := n • qc
  npow_zero qc := AddMonoid.nsmul_zero qc
  npow_succ n qc := AddMonoid.nsmul_succ n qc

@[simp] lemma monoid_mul_def (qc qc' : QueryCount ι) :
  (@HMul.hMul _ _ _ (@instHMul _ (Monoid.toMulOneClass.toMul)) qc qc')
     = (qc : ι → ℕ) + (qc' : ι → ℕ) := rfl

@[simp] lemma monoid_one_def :
    (@OfNat.ofNat (QueryCount ι) 1 (@One.toOfNat1 _ (Monoid.toOne))) = (0 : ι → ℕ) := rfl

/-- The query count recording one query at index `i` and none elsewhere. -/
def single [DecidableEq ι] (i : ι) : QueryCount ι := Pi.single i 1

@[simp]
lemma single_le_iff_pos [DecidableEq ι] (i : ι) (qc : QueryCount ι) :
    single i ≤ qc ↔ 0 < qc i := by
  simp [single, Pi.single, update_le_iff, Nat.lt_iff_add_one_le]

end QueryCount

/-- Log of queries represented by a list of dependent product's tagging the oracle's index.
`(t : spec.Domain) × (spec.Range t)` is slightly more restricted as it doesn't
keep track of query ordering between different oracles.

A `QueryLog spec` is morally a free monoid on `Idx spec.toPFunctor`, with
identity `[]` and product `(++)`. By Mathlib reducibility this is exactly
`FreeMonoid (Idx spec.toPFunctor) = TraceList spec.toPFunctor`, so a
trace-valued boundary description such as `BoundaryAction.emit` (in
`PolyFun/Interaction/UC/OpenProcess.lean`) and a per-call `QueryLog`-valued
writer share the same underlying free-monoid carrier.

We do *not* declare a global `Monoid (QueryLog spec)` instance: doing so
would conflict with the `[EmptyCollection ω] [Append ω] → Monad (WriterT ω M)`
instance Mathlib already provides for `WriterT (QueryLog spec) M`, which the
existing `WriterTBridge`/`mvcgen` proof infrastructure relies on. The
`QueryImpl.withTrace`/`withLogging` API instead uses the Append-based
`Monad (WriterT _ _)` directly via `QueryImpl.withTraceAppend`. -/
@[reducible] def QueryLog (spec : OracleSpec.{u, v} ι) : Type (max u v) :=
  List ((t : spec.Domain) × spec.Range t)

namespace QueryLog

/-- Query log with a single entry. -/
def singleton (t : spec.Domain) (u : spec.Range t) : QueryLog spec := [⟨t, u⟩]

/-- Update a query log by adding a new element to the appropriate list.
Note that this requires decidable equality on the indexing set. -/
def logQuery (log : QueryLog spec) (t : spec.Domain) (u : spec.Range t) : QueryLog spec :=
  log ++ singleton t u

instance [spec.DecidableEq] : DecidableEq (QueryLog spec) :=
  inferInstanceAs (DecidableEq (List _))

section getQ

/-- Get all the queries with inputs satisfying `p` -/
def getQ (log : QueryLog spec) (p : spec.Domain → Prop) [DecidablePred p] :
    List ((t : spec.Domain) × spec.Range t) :=
  List.foldr (fun ⟨t, u⟩ xs => if p t then ⟨t, u⟩ :: xs else xs) [] log

@[simp]
lemma getQ_nil (p : spec.Domain → Prop) [DecidablePred p] :
    getQ ([] : QueryLog spec) p = [] := rfl

@[simp]
lemma getQ_cons (entry : (t : spec.Domain) × spec.Range t) (log : QueryLog spec)
    (p : spec.Domain → Prop) [DecidablePred p] :
    getQ (entry :: log) p = if p entry.1 then entry :: getQ log p else getQ log p := rfl

@[simp]
lemma getQ_singleton (t : spec.Domain) (u : spec.Range t)
    (p : spec.Domain → Prop) [DecidablePred p] :
    getQ (singleton t u) p = if p t then [⟨t, u⟩] else [] := by
  simp [singleton, getQ]

@[simp]
lemma getQ_append (log log' : QueryLog spec) (p : spec.Domain → Prop) [DecidablePred p] :
    (log ++ log').getQ p = log.getQ p ++ log'.getQ p := by
  induction log with
  | nil => rfl
  | cons hd tl ih => grind [getQ_cons]

end getQ

section countQ

/-- Count the number of queries with inputs satisfying `p`. -/
def countQ (log : QueryLog spec) (p : spec.Domain → Prop) [DecidablePred p] : ℕ :=
  (log.getQ p).length

@[simp]
lemma countQ_cons (entry : (t : spec.Domain) × spec.Range t) (log : QueryLog spec)
    (p : spec.Domain → Prop) [DecidablePred p] :
    countQ (entry :: log) p = if p entry.1 then countQ log p + 1 else countQ log p := by
  by_cases hp : p entry.1 <;> simp [countQ, getQ_cons, hp, Nat.add_comm]

@[simp]
lemma countQ_singleton (t : spec.Domain) (u : spec.Range t)
    (p : spec.Domain → Prop) [DecidablePred p] :
    countQ (singleton t u) p = if p t then 1 else 0 := by
  simp [countQ, apply_ite List.length]

@[simp]
lemma countQ_append (log log' : QueryLog spec) (p : spec.Domain → Prop) [DecidablePred p] :
    (log ++ log').countQ p = log.countQ p + log'.countQ p := by
  simp [countQ, List.length_append]

end countQ

/-! ### Lookup by oracle occurrence -/

/-- The `n`-th answer in the log for queries to oracle `t`, if it exists. -/
def getQueryValue? [spec.DecidableEq] (log : QueryLog spec) (t : ι) (n : Nat) :
    Option (spec.Range t) :=
  match (log.getQ (· = t))[n]? with
  | none => none
  | some ⟨t', u⟩ => if h : t' = t then some (h ▸ u) else none

/-- Decompose `getQ` across a `logQuery` step. -/
lemma getQ_logQuery (log : QueryLog spec) (t : ι) (u : spec.Range t)
    (p : ι → Prop) [DecidablePred p] :
    (log.logQuery t u).getQ p = log.getQ p ++ (if p t then [⟨t, u⟩] else []) := by
  simp [QueryLog.logQuery, QueryLog.singleton]

/-- If `getQueryValue? log t n = some u`, then the `n`-th `t`-filtered entry of
`log` is `⟨t, u⟩`. -/
lemma getQ_getElem?_eq_of_getQueryValue?_eq_some [spec.DecidableEq]
    (log : QueryLog spec) (t : ι) (n : Nat) (u : spec.Range t)
    (h : getQueryValue? log t n = some u) :
    (log.getQ (· = t))[n]? = some ⟨t, u⟩ := by
  rcases hopt : (log.getQ (· = t))[n]? with _ | ⟨t', u'⟩
  · simp [getQueryValue?, hopt] at h
  · obtain rfl : t' = t := by by_contra ht; simp [getQueryValue?, hopt, ht] at h
    simpa [getQueryValue?, hopt] using h

/-- Converse: if the `n`-th `t`-filtered entry is `⟨t, u⟩`, then
`getQueryValue? log t n = some u`. -/
lemma getQueryValue?_eq_some_of_getQ_getElem? [spec.DecidableEq]
    (log : QueryLog spec) (t : ι) (n : Nat) (u : spec.Range t)
    (h : (log.getQ (· = t))[n]? = some ⟨t, u⟩) :
    getQueryValue? log t n = some u := by simp [getQueryValue?, h]

/-- Every entry of `log.getQ (· = t)` has its first component equal to `t`. -/
lemma getQ_eq_mem [spec.DecidableEq] (log : QueryLog spec) (t : ι)
    {entry : (t' : ι) × spec.Range t'} (h : entry ∈ log.getQ (· = t)) :
    entry.1 = t := by
  induction log <;> grind [QueryLog.getQ_cons, QueryLog.getQ_nil]

/-- If the `t`-filtered log has at least `n + 1` entries, then the indexed
lookup succeeds. -/
lemma getQueryValue?_isSome_of_lt [spec.DecidableEq]
    (log : QueryLog spec) (t : ι) (n : Nat)
    (h : n < (log.getQ (· = t)).length) :
    (getQueryValue? log t n).isSome := by
  simp [getQueryValue?, List.getElem?_eq_getElem h,
    getQ_eq_mem log t (List.getElem_mem h)]

/-- Prepending an entry whose oracle index does not match `t` leaves the
`t`-indexed view of the log unchanged. -/
lemma getQueryValue?_cons_of_ne [spec.DecidableEq]
    (entry : (t' : ι) × spec.Range t') (log : QueryLog spec) (t : ι) (n : Nat)
    (h : entry.1 ≠ t) :
    getQueryValue? (entry :: log) t n = getQueryValue? log t n := by
  simp [getQueryValue?, QueryLog.getQ_cons, h]

/-- The first matching entry is the zeroth indexed query value. -/
@[simp] lemma getQueryValue?_cons_self_zero [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (log : QueryLog spec) :
    getQueryValue? (⟨t, u⟩ :: log) t 0 = some u :=
  getQueryValue?_eq_some_of_getQ_getElem? _ _ _ _ (by simp [QueryLog.getQ_cons])

/-- Prepending a matching entry shifts later indexed lookups by one. -/
@[simp] lemma getQueryValue?_cons_self_succ [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (log : QueryLog spec) (n : Nat) :
    getQueryValue? (⟨t, u⟩ :: log) t (n + 1) = getQueryValue? log t n := by
  simp [getQueryValue?, QueryLog.getQ_cons]

/-- The entry immediately following a prefix is found at the prefix's count
of matching oracle queries. -/
lemma getQueryValue?_append_self_at_countQ [spec.DecidableEq]
    (before after : QueryLog spec) (t : ι) (u : spec.Range t) :
    getQueryValue? (before ++ ⟨t, u⟩ :: after) t (before.countQ (· = t)) = some u :=
  getQueryValue?_eq_some_of_getQ_getElem? _ _ _ _ (by simp [QueryLog.countQ])

/-- Query-log counting is the `OracleSpec` specialization of PolyFun's
generic occurrence count on erased polynomial traces. -/
lemma countQ_eq_occurrences [spec.DecidableEq] (log : QueryLog spec) (t : ι) :
    log.countQ (· = t) = PFunctor.TraceList.occurrences (P := spec.toPFunctor) t
      (show PFunctor.TraceList spec.toPFunctor from log) := by
  induction log with
  | nil => rfl
  | cons entry log ih =>
      rcases entry with ⟨t', u⟩
      by_cases h : t' = t
      · subst t'
        simp only [QueryLog.countQ, QueryLog.getQ_cons, if_pos trivial,
          List.length_cons]
        rw [PFunctor.TraceList.occurrences,
          List.countP_cons_of_pos (by simp)]
        rw [PFunctor.TraceList.occurrences] at ih
        simpa [QueryLog.countQ] using ih
      · simp only [QueryLog.countQ, QueryLog.getQ_cons, if_neg h]
        rw [PFunctor.TraceList.occurrences,
          List.countP_cons_of_neg (by simp [h])]
        rw [PFunctor.TraceList.occurrences] at ih
        simpa [QueryLog.countQ] using ih

/-- Query-log lookup is the `OracleSpec` specialization of dependent lookup
on PolyFun traces. -/
lemma getQueryValue?_eq_getAt? [spec.DecidableEq]
    (log : QueryLog spec) (t : ι) (n : Nat) :
    getQueryValue? log t n =
      PFunctor.TraceList.getAt?
        (show PFunctor.TraceList spec.toPFunctor from log) t n := by
  induction log generalizing n with
  | nil => rfl
  | cons entry log ih =>
      rcases entry with ⟨t', u⟩
      by_cases h : t' = t
      · subst t'
        cases n with
        | zero =>
            rw [getQueryValue?_cons_self_zero,
              PFunctor.TraceList.getAt?_cons_self_zero]
        | succ n =>
            rw [getQueryValue?_cons_self_succ,
              PFunctor.TraceList.getAt?_cons_self_succ]
            exact ih n
      · rw [getQueryValue?_cons_of_ne ⟨t', u⟩ log t n (by simpa using h),
          PFunctor.TraceList.getAt?_cons_of_ne h]
        exact ih n

/-- Check if an element was ever queried in a log of queries.
Relies on decidable equality of the domain types of oracles. -/
def wasQueried [spec.DecidableEq] (log : QueryLog spec) (t : spec.Domain) : Bool :=
  log.getQ (· = t) ≠ []

lemma getQ_ne_nil_iff_mem_map_fst [spec.DecidableEq]
    (log : QueryLog spec) (t : spec.Domain) :
    log.getQ (· = t) ≠ [] ↔ t ∈ log.map (fun e => e.1) := by
  induction log with
  | nil => simp
  | cons hd tl ih => rcases eq_or_ne hd.1 t with h | h <;> simp [List.mem_map, ih, h, Ne.symm]

lemma wasQueried_eq_decide_mem_map_fst [spec.DecidableEq]
    (log : QueryLog spec) (t : spec.Domain) :
    log.wasQueried t = decide (t ∈ log.map (fun e => e.1)) :=
  decide_eq_decide.mpr (getQ_ne_nil_iff_mem_map_fst log t)

@[simp]
lemma wasQueried_cons_self [spec.DecidableEq] {t : spec.Domain} {u : spec.Range t}
    {log : QueryLog spec} :
    wasQueried (⟨t, u⟩ :: log) t = true := by
  simp [wasQueried_eq_decide_mem_map_fst]

@[simp]
lemma wasQueried_cons_of_ne [spec.DecidableEq] {t t' : spec.Domain}
    {u : spec.Range t'} {log : QueryLog spec} (hne : t' ≠ t) :
    wasQueried (⟨t', u⟩ :: log) t = wasQueried log t := by
  simp [wasQueried_eq_decide_mem_map_fst, List.mem_cons, hne.symm, eq_comm]

section prod

variable {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

/-- Get only the portion of the log for queries in `spec₁`. -/
protected def fst (log : QueryLog (spec₁ + spec₂)) : QueryLog spec₁ :=
  log.filterMap (fun | ⟨.inl t, u⟩ => some ⟨t, u⟩ | _ => none)

/-- Get only the portion of the log for queries in `spec₂`. -/
protected def snd (log : QueryLog (spec₁ + spec₂)) : QueryLog spec₂ :=
  log.filterMap (fun | ⟨.inr t, u⟩ => some ⟨t, u⟩ | _ => none)

/-- View a log for `spec₁` as one for `spec₁ + spec₂` by inclusion. -/
protected def inl (log : QueryLog spec₁) : QueryLog (spec₁ + spec₂) :=
  log.map fun ⟨t, u⟩ => ⟨.inl t, u⟩

/-- View a log for `spec₂` as one for `spec₁ + spec₂` by inclusion. -/
protected def inr (log : QueryLog spec₂) : QueryLog (spec₁ + spec₂) :=
  log.map fun ⟨t, u⟩ => ⟨.inr t, u⟩

instance : Coe (QueryLog spec₁) (QueryLog (spec₁ + spec₂)) := ⟨QueryLog.inl⟩
instance : Coe (QueryLog spec₂) (QueryLog (spec₁ + spec₂)) := ⟨QueryLog.inr⟩

end prod

end QueryLog

/-- A store of pre-generated seed values for oracle queries, indexed by oracle.
Maps each oracle index `i` to a list of outputs `List (spec.Range i)`. -/
@[reducible] def QuerySeed (spec : OracleSpec.{u, v} ι) : Type (max u v) :=
  (i : ι) → List (spec.Range i)

namespace QuerySeed

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

instance : EmptyCollection (QuerySeed spec) := ⟨fun _ => []⟩

@[ext]
protected lemma ext {seed₁ seed₂ : QuerySeed spec} (h : ∀ i, seed₁ i = seed₂ i) :
    seed₁ = seed₂ :=
  funext h

@[simp]
lemma empty_apply (i : ι) : (∅ : QuerySeed spec) i = [] := rfl

variable [DecidableEq ι]

/- These equations are the public reduction surface for dependent updates of a `QuerySeed`.
Using specialized lemmas avoids coupling all seed proofs to simplifier support for the generic
dependent `Function.update`. -/
@[simp]
lemma functionUpdate_self (seed : QuerySeed spec) (i : ι) (xs : List (spec.Range i)) :
    Function.update seed i xs i = xs :=
  Function.update_self i xs seed

@[simp]
lemma functionUpdate_of_ne (seed : QuerySeed spec) (i : ι) (xs : List (spec.Range i))
    (j : ι) (hj : j ≠ i) : Function.update seed i xs j = seed j :=
  Function.update_of_ne hj xs seed

@[simp]
lemma functionUpdate_eq_self (seed : QuerySeed spec) (i : ι) :
    Function.update seed i (seed i) = seed :=
  Function.update_eq_self i seed

@[simp]
lemma functionUpdate_idem (seed : QuerySeed spec) (i : ι)
    (xs ys : List (spec.Range i)) :
    Function.update (Function.update seed i xs) i ys = Function.update seed i ys :=
  Function.update_idem (a := i) xs ys seed

/-- Replace the seed values at index `i`. -/
def update (seed : QuerySeed spec) (i : ι) (xs : List (spec.Range i)) : QuerySeed spec :=
  Function.update seed i xs

@[simp]
lemma update_self (seed : QuerySeed spec) (i : ι) (xs : List (spec.Range i)) :
    seed.update i xs i = xs := by
  exact functionUpdate_self seed i xs

@[simp]
lemma update_of_ne (seed : QuerySeed spec) (i : ι) (xs : List (spec.Range i))
    (j : ι) (hj : j ≠ i) :
    seed.update i xs j = seed j := by
  exact functionUpdate_of_ne seed i xs j hj

@[simp]
lemma update_eq_self (seed : QuerySeed spec) (i : ι) : seed.update i (seed i) = seed :=
  functionUpdate_eq_self seed i

@[simp]
lemma update_idem (seed : QuerySeed spec) (i : ι) (xs ys : List (spec.Range i)) :
    (seed.update i xs).update i ys = seed.update i ys :=
  functionUpdate_idem seed i xs ys

/-- Updates at distinct seed indices commute. -/
lemma update_comm (seed : QuerySeed spec) {i j : ι} (h : i ≠ j)
    (xs : List (spec.Range i)) (ys : List (spec.Range j)) :
    (seed.update i xs).update j ys = (seed.update j ys).update i xs := by
  unfold update
  exact Function.update_comm h xs ys seed

/-- Append a list of values to the seed at index `i`. -/
def addValues (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i)) : QuerySeed spec :=
  seed.update i (seed i ++ us)

/-- Replacing an index after appending there discards the appended values. -/
@[simp]
lemma update_addValues_same (seed : QuerySeed spec) (i : ι)
    (us xs : List (spec.Range i)) :
    (seed.addValues (i := i) us).update i xs = seed.update i xs := by
  unfold addValues
  exact update_idem seed i _ xs

/-- Appending at one seed index commutes with replacing a distinct index. -/
lemma update_addValues_comm (seed : QuerySeed spec) {i j : ι} (h : i ≠ j)
    (us : List (spec.Range i)) (ys : List (spec.Range j)) :
    (seed.addValues (i := i) us).update j ys =
      (seed.update j ys).addValues (i := i) us := by
  unfold addValues
  rw [update_of_ne seed j ys i h]
  exact update_comm seed h (seed i ++ us) ys

@[simp]
lemma addValues_self (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i)) :
    seed.addValues us i = seed i ++ us := by
  simp [addValues]

@[simp]
lemma addValues_of_ne (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i))
    {j : ι} (hj : j ≠ i) : seed.addValues us j = seed j := by
  simp [addValues, hj]

@[simp]
lemma addValues_nil (seed : QuerySeed spec) (i : ι) :
    seed.addValues (i := i) ([] : List (spec.Range i)) = seed := by
  simp [addValues]

lemma addValues_cons (seed : QuerySeed spec) {i : ι} (u : spec.Range i)
    (us : List (spec.Range i)) :
    seed.addValues (u :: us) = (seed.addValues [u]).addValues us := by
  simp [addValues]

/-- Prepend a list of values to the seed at index `i`. -/
def prependValues (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i)) : QuerySeed spec :=
  seed.update i (us ++ seed i)

@[simp]
lemma prependValues_self (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i)) :
    seed.prependValues us i = us ++ seed i := by
  simp [prependValues]

@[simp]
lemma prependValues_singleton (seed : QuerySeed spec) {i : ι} (u : spec.Range i) :
    seed.prependValues [u] i = u :: seed i := by
  simp [prependValues]

@[simp]
lemma prependValues_of_ne (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i))
    {j : ι} (hj : j ≠ i) : seed.prependValues us j = seed j := by
  simp [prependValues, hj]

@[simp]
lemma prependValues_nil (seed : QuerySeed spec) (i : ι) :
    seed.prependValues (i := i) ([] : List (spec.Range i)) = seed := by
  simp [prependValues]

lemma prependValues_take_drop (seed : QuerySeed spec) (i : ι) (n : ℕ) :
    QuerySeed.prependValues (seed.update i ((seed i).drop n))
      ((seed i).take n : List (spec.Range i)) = seed := by
  simp [prependValues]

lemma eq_of_prependValues_eq (seed rest : QuerySeed spec)
    {i : ι} (xs : List (spec.Range i)) {n : ℕ} (hlen : xs.length = n)
    (h : rest.prependValues xs = seed) :
    xs = (seed i).take n ∧ rest = seed.update i ((seed i).drop n) := by
  subst hlen; subst h; simp [prependValues]

lemma eq_of_prependValues_singleton_eq (seed rest : QuerySeed spec)
    {i : ι} (u : spec.Range i) (h : rest.prependValues [u] = seed) :
    u :: rest i = seed i ∧ rest = seed.update i ((seed i).tail) := by
  subst h; simp [prependValues]

abbrev addValue (seed : QuerySeed spec) (i : ι) (u : spec.Range i) :
    QuerySeed spec :=
  seed.addValues [u]

/-- Take only the first `n` values of the seed at index `i`. -/
def takeAtIndex (seed : QuerySeed spec) (i : ι) (n : ℕ) : QuerySeed spec :=
  seed.update i ((seed i).take n)

@[simp] lemma takeAtIndex_apply_self (seed : QuerySeed spec) (i : ι) (n : ℕ) :
    seed.takeAtIndex i n i = (seed i).take n := by
  simp [takeAtIndex]

@[simp] lemma takeAtIndex_apply_of_ne (seed : QuerySeed spec) (i : ι) (n : ℕ) (j : ι)
    (hj : j ≠ i) : seed.takeAtIndex i n j = seed j := by
  simp [takeAtIndex, hj]

@[simp] lemma takeAtIndex_length (seed : QuerySeed spec) (i : ι) :
    seed.takeAtIndex i (seed i).length = seed :=
  funext fun j => by
    by_cases hj : j = i
    · subst hj; simp [takeAtIndex]
    · simp [takeAtIndex, hj]

lemma takeAtIndex_addValues_drop (seed : QuerySeed spec) (i : ι) (n : ℕ) :
    (seed.takeAtIndex i n).addValues ((seed i).drop n) = seed := by
  ext j; by_cases hj : j = i
  · subst hj; simp [takeAtIndex, addValues, List.take_append_drop]
  · simp [takeAtIndex, addValues, hj]

/-- Pop one value from index `i`, returning the consumed value and updated seed when nonempty. -/
def pop (seed : QuerySeed spec) (i : ι) : Option (spec.Range i × QuerySeed spec) :=
  match seed i with
  | [] => none
  | u :: us => some (u, seed.update i us)

@[simp]
lemma pop_eq_none_iff (seed : QuerySeed spec) (i : ι) :
    seed.pop i = none ↔ seed i = [] := by
  unfold pop
  cases hsi : seed i <;> simp

@[simp]
lemma pop_eq_some_of_cons (seed : QuerySeed spec) (i : ι)
    (u : spec.Range i) (us : List (spec.Range i))
    (h : seed i = u :: us) :
    seed.pop i = some (u, seed.update i us) := by
  unfold pop
  simp [h]

lemma cons_of_pop_eq_some (seed : QuerySeed spec) (i : ι)
    (u : spec.Range i) (rest : QuerySeed spec)
    (h : seed.pop i = some (u, rest)) :
    u :: rest i = seed i := by
  unfold pop at h
  cases hsi : seed i with
  | nil => simp [hsi] at h
  | cons u0 us =>
    simp only [hsi, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp

lemma rest_eq_update_tail_of_pop_eq_some (seed : QuerySeed spec) (i : ι)
    (u : spec.Range i) (rest : QuerySeed spec)
    (h : seed.pop i = some (u, rest)) :
    rest = seed.update i ((seed i).tail) := by
  unfold pop at h
  cases hsi : seed i with
  | nil => simp [hsi] at h
  | cons u0 us =>
    simp only [hsi, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp

/-- Construct a query seed from a list at a single index. -/
def ofList {i : ι} (xs : List (spec.Range i)) : QuerySeed spec :=
  fun j => if h : i = j then h ▸ xs else []

@[simp] lemma ofList_apply_self {i : ι} (xs : List (spec.Range i)) :
    (ofList xs : QuerySeed spec) i = xs := by simp [ofList]

@[simp] lemma ofList_apply_of_ne {i j : ι} (xs : List (spec.Range i)) (hj : j ≠ i) :
    (ofList xs : QuerySeed spec) j = [] := by simp [ofList, Ne.symm hj]

lemma eq_addValues_iff (seed seed' : QuerySeed spec)
    {i : ι} (xs : List (spec.Range i)) :
    seed = seed'.addValues xs ↔ seed' i ++ xs = seed i ∧
      ∀ j, j ≠ i → seed' j = seed j := by
  constructor
  · rintro rfl
    exact ⟨by simp, fun j hj => by simp [addValues, hj]⟩
  · rintro ⟨happ, hother⟩
    funext j
    by_cases hj : j = i
    · subst hj; rw [addValues_self]; exact happ.symm
    · rw [addValues_of_ne _ _ hj, hother j hj]

lemma addValues_eq_iff (seed seed' : QuerySeed spec)
    {i : ι} (xs : List (spec.Range i)) :
    seed.addValues xs = seed' ↔ seed i ++ xs = seed' i ∧
      ∀ j, j ≠ i → seed j = seed' j :=
  eq_comm.trans (eq_addValues_iff seed' seed xs)

@[simp]
lemma pop_prependValues_singleton (s' : QuerySeed spec) (i : ι) (u : spec.Range i) :
    (s'.prependValues [u]).pop i = some (u, s') := by
  simp only [pop, prependValues, update_self, List.singleton_append, update_idem, update_eq_self]

lemma prependValues_singleton_injective (i : ι) :
    Function.Injective (fun (p : spec.Range i × QuerySeed spec) => p.2.prependValues [p.1]) := by
  intro ⟨u₁, s₁⟩ ⟨u₂, s₂⟩ h
  obtain ⟨hu, hst⟩ := List.cons_eq_cons.mp <|
    by simpa only [prependValues_singleton] using congr_fun h i
  refine Prod.ext hu (funext fun j => ?_)
  by_cases hj : j = i
  · exact hj ▸ hst
  · simpa only [prependValues_of_ne _ _ hj] using congr_fun h j

lemma eq_prependValues_of_pop_eq_some {seed : QuerySeed spec} {i : ι}
    {u : spec.Range i} {rest : QuerySeed spec} (h : seed.pop i = some (u, rest)) :
    rest.prependValues [u] = seed := by
  have hcons := cons_of_pop_eq_some seed i u rest h
  have hrest := rest_eq_update_tail_of_pop_eq_some seed i u rest h
  funext j
  by_cases hj : j = i
  · subst hj; simpa [prependValues_singleton] using hcons
  · rw [prependValues_of_ne _ _ hj, hrest]
    exact update_of_ne seed i _ j hj

lemma pop_takeAtIndex_prependValues_of_ne (s' : QuerySeed spec) (i₀ : ι) (k : ℕ)
    {t : ι} (u₀ : spec.Range t) (hti : t ≠ i₀) :
    ((s'.prependValues [u₀]).takeAtIndex i₀ k).pop t =
      some (u₀, s'.takeAtIndex i₀ k) := by
  have h1 : ((s'.prependValues [u₀]).takeAtIndex i₀ k) t = u₀ :: s' t := by
    rw [takeAtIndex_apply_of_ne _ _ _ _ hti, prependValues_singleton]
  rw [pop_eq_some_of_cons _ _ u₀ (s' t) h1]
  refine congrArg some (Prod.ext rfl (funext fun j => ?_))
  by_cases hj : j = t <;> by_cases hji : j = i₀ <;> subst_vars <;>
    simp_all [update_self, update_of_ne, takeAtIndex_apply_self,
      takeAtIndex_apply_of_ne, prependValues_of_ne]

lemma pop_takeAtIndex_prependValues_self (s' : QuerySeed spec) (i₀ : ι)
    (u₀ : spec.Range i₀) {k : ℕ} (hk : 0 < k) :
    ((s'.prependValues [u₀]).takeAtIndex i₀ k).pop i₀ =
      some (u₀, s'.takeAtIndex i₀ (k - 1)) := by
  have h1 : ((s'.prependValues [u₀]).takeAtIndex i₀ k) i₀ =
      u₀ :: (s' i₀).take (k - 1) := by
    simp only [takeAtIndex_apply_self, prependValues_singleton, List.take_cons hk]
  rw [pop_eq_some_of_cons _ _ u₀ ((s' i₀).take (k - 1)) h1]
  refine congrArg some (Prod.ext rfl (funext fun j => ?_))
  by_cases hj : j = i₀ <;> subst_vars <;>
    simp_all [update_self, update_of_ne, takeAtIndex_apply_self,
      takeAtIndex_apply_of_ne, prependValues_of_ne]

end QuerySeed

end OracleSpec
