/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.SimulateQ
import ToMathlib.Control.WriterT

/-!
# Structures For Tracking a Computation's Oracle Queries

This file defines types like `QueryLog` and `QueryCache` for use with
simulation oracles and implementation transformers defined in the same directory.
-/

open OracleSpec OracleComp

universe u v w

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec ι}

/-- Type to represent a cache of queries to oracles in `spec`.
Defined to be a function from (indexed) inputs to an optional output. -/
def QueryCache (spec : OracleSpec.{u,v} ι) : Type (max u v) :=
  (t : spec.Domain) → Option (spec.Range t)

namespace QueryCache

instance : EmptyCollection (QueryCache spec) := ⟨fun _ => none⟩

@[simp]
lemma empty_apply (t : spec.Domain) : (∅ : QueryCache spec) t = none := rfl

@[ext]
protected lemma ext {c₁ c₂ : QueryCache spec} (h : ∀ t, c₁ t = c₂ t) : c₁ = c₂ :=
  funext h

/-! ### Partial Order

A `QueryCache` carries a natural partial order where `c₁ ≤ c₂` means every cached entry
in `c₁` also appears (with the same value) in `c₂`. The empty cache is the bottom element. -/

instance : PartialOrder (QueryCache spec) where
  le c₁ c₂ := ∀ ⦃t⦄ ⦃u : spec.Range t⦄, c₁ t = some u → c₂ t = some u
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁₂ h₂₃ _ _ h := h₂₃ (h₁₂ h)
  le_antisymm a b hab hba := by
    funext t
    cases ha : a t with
    | none =>
      cases hb : b t with
      | none => rfl
      | some u => exact absurd (hba hb) (by simp [ha])
    | some u => exact (hab ha).symm

instance : OrderBot (QueryCache spec) where
  bot := ∅
  bot_le _ := by intro _ _ h; simp at h

@[simp]
lemma bot_eq_empty : (⊥ : QueryCache spec) = ∅ := rfl

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

/-! ### Cache update -/

variable [spec.DecidableEq] [DecidableEq ι] (cache : QueryCache spec)

/-- Add an index + input pair to the cache by updating the function
(wrapper around `Function.update`). -/
def cacheQuery (t : spec.Domain) (u : spec.Range t) : QueryCache spec :=
  Function.update cache t u

omit [spec.DecidableEq] in
@[simp]
lemma cacheQuery_self (t : spec.Domain) (u : spec.Range t) :
    (cache.cacheQuery t u) t = some u := by
  simp [cacheQuery]

omit [spec.DecidableEq] in
@[simp]
lemma cacheQuery_of_ne {t' t : spec.Domain} (u : spec.Range t) (h : t' ≠ t) :
    (cache.cacheQuery t u) t' = cache t' := by
  simp [cacheQuery, h]

omit [spec.DecidableEq] in
lemma le_cacheQuery {t : spec.Domain} {u : spec.Range t} (h : cache t = none) :
    cache ≤ cache.cacheQuery t u := by
  intro t' u' ht'
  by_cases heq : t' = t
  · subst heq; simp [h] at ht'
  · rwa [cacheQuery_of_ne cache u heq]

omit [spec.DecidableEq] in
lemma cacheQuery_mono {c₁ c₂ : QueryCache spec} (h : c₁ ≤ c₂) (t : spec.Domain)
    (u : spec.Range t) : c₁.cacheQuery t u ≤ c₂.cacheQuery t u := by
  intro t' u' ht'
  by_cases heq : t' = t
  · subst heq; simp only [cacheQuery_self] at ht' ⊢; exact ht'
  · have h₁ := cacheQuery_of_ne c₁ u heq
    have h₂ := cacheQuery_of_ne c₂ u heq
    rw [h₁] at ht'; rw [h₂]; exact h ht'

omit [spec.DecidableEq] in
@[simp]
lemma isCached_cacheQuery_self (t : spec.Domain) (u : spec.Range t) :
    (cache.cacheQuery t u).isCached t = true := by
  simp [isCached]

omit [spec.DecidableEq] in
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
  fun | .inl t => cache t | .inr _ => none

/-- Embed a cache for `spec₂` into one for `spec₁ + spec₂`. -/
protected def inr (cache : QueryCache spec₂) : QueryCache (spec₁ + spec₂) :=
  fun | .inl _ => none | .inr t => cache t

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
`idx` gives the "index" for a given input -/
@[reducible] def QueryCount (ι : Type*) := ι → ℕ

namespace QueryCount

/-- Pointwise addition as the `Monoid` operation used for `WriterT`. -/
instance : Monoid (QueryCount ι) where
  mul qc qc' := qc + qc'
  mul_assoc := add_assoc
  one := 0
  one_mul := zero_add
  mul_one := add_zero

@[simp] lemma monoid_mul_def (qc qc' : QueryCount ι) :
  (@HMul.hMul _ _ _ (@instHMul _ (Monoid.toMulOneClass.toMul)) qc qc')
     = (qc : ι → ℕ) + (qc' : ι → ℕ) := rfl

@[simp] lemma monoid_one_def :
    (@OfNat.ofNat (QueryCount ι) 1 (@One.toOfNat1 _ (Monoid.toOne))) = (0 : ι → ℕ) := rfl

def single [DecidableEq ι] (i : ι) : QueryCount ι := Function.update 0 i 1

@[simp]
lemma single_le_iff_pos [DecidableEq ι] (i : ι) (qc : QueryCount ι) :
    single i ≤ qc ↔ 0 < qc i := by
  simp [single, Function.update, Pi.hasLe]
  constructor <;> intro h
  · have : 1 ≤ qc i := by simpa using h i
    exact this
  · intro j
    by_cases hj : j = i
    · simp [hj]; omega
    · simp [hj]

end QueryCount

/-- Log of queries represented by a list of dependent product's tagging the oracle's index.
`(t : spec.Domain) × (spec.Range t)` is slightly more restricted as it doesn't
keep track of query ordering between different oracles. -/
@[reducible] def QueryLog (spec : OracleSpec.{u,v} ι) : Type (max u v) :=
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

-- variable [DecidableEq ι]

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
  | cons hd tl ih => simp [ih]; split_ifs <;> simp

end getQ

section countQ

-- variable [DecidableEq ι]

/-- Count the number of queries with inputs satisfying `p`. -/
def countQ (log : QueryLog spec) (p : spec.Domain → Prop) [DecidablePred p] : ℕ :=
  (log.getQ p).length

@[simp]
lemma countQ_singleton (t : spec.Domain) (u : spec.Range t)
    (p : spec.Domain → Prop) [DecidablePred p] :
    countQ (singleton t u) p = if p t then 1 else 0 := by
  simp [countQ]; split_ifs <;> rfl

@[simp]
lemma countQ_append (log log' : QueryLog spec) (p : spec.Domain → Prop) [DecidablePred p] :
    (log ++ log').countQ p = log.countQ p + log'.countQ p := by
  simp [countQ, List.length_append]

end countQ

/-- Check if an element was ever queried in a log of queries.
Relies on decidable equality of the domain types of oracles. -/
def wasQueried [spec.DecidableEq] (log : QueryLog spec) (t : spec.Domain) : Bool :=
  log.getQ (· = t) ≠ []

section prod

variable {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

/-- Get only the portion of the log for queries in `spec₁`. -/
protected def fst (log : QueryLog (spec₁ + spec₂)) : QueryLog spec₁ :=
  log.filterMap (fun | ⟨.inl t, u⟩ => some ⟨t, u⟩ | _ => none)

/-- Get only the portion of the log for queries in `spec₂`. -/
protected def snd (log : QueryLog (spec₁ + spec₂)) : QueryLog spec₂ :=
  log.filterMap (fun | ⟨.inr t, u⟩ => some ⟨t, u⟩ | _ => none)

/-- View a log for `spec₁` as one for `spec₁ ++ₒ spec₂` by inclusion. -/
protected def inl (log : QueryLog spec₁) : QueryLog (spec₁ + spec₂) :=
  log.map fun ⟨t, u⟩ => ⟨.inl t, u⟩

/-- View a log for `spec₂` as one for `spec₁ ++ₒ spec₂` by inclusion. -/
protected def inr (log : QueryLog spec₂) : QueryLog (spec₁ + spec₂) :=
  log.map fun ⟨t, u⟩ => ⟨.inr t, u⟩

instance : Coe (QueryLog spec₁) (QueryLog (spec₁ + spec₂)) := ⟨QueryLog.inl⟩
instance : Coe (QueryLog spec₂) (QueryLog (spec₁ + spec₂)) := ⟨QueryLog.inr⟩

end prod

end QueryLog

/-- A store of pre-generated seed values for oracle queries, indexed by oracle.
Maps each oracle index `i` to a list of outputs `List (spec.Range i)`. -/
def QuerySeed (spec : OracleSpec.{u,v} ι) : Type (max u v) :=
  (i : ι) → List (spec.Range i)

namespace QuerySeed

variable {ι : Type u} {spec : OracleSpec.{u,v} ι}

instance : EmptyCollection (QuerySeed spec) := ⟨fun _ => []⟩

@[ext]
protected lemma ext {seed₁ seed₂ : QuerySeed spec} (h : ∀ i, seed₁ i = seed₂ i) :
    seed₁ = seed₂ :=
  funext h

@[simp]
lemma empty_apply (i : ι) : (∅ : QuerySeed spec) i = [] := rfl

variable [DecidableEq ι]

/-- Replace the seed values at index `i`. -/
def update (seed : QuerySeed spec) (i : ι) (xs : List (spec.Range i)) : QuerySeed spec :=
  Function.update seed i xs

@[simp]
lemma update_self (seed : QuerySeed spec) (i : ι) (xs : List (spec.Range i)) :
    seed.update i xs i = xs := by
  simp [update]

@[simp]
lemma update_of_ne (seed : QuerySeed spec) (i : ι) (xs : List (spec.Range i))
    (j : ι) (hj : j ≠ i) :
    seed.update i xs j = seed j := by
  simp [update, Function.update_of_ne hj]

/-- Append a list of values to the seed at index `i`. -/
def addValues (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i)) : QuerySeed spec :=
  Function.update seed i (seed i ++ us)

@[simp]
lemma addValues_self (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i)) :
    seed.addValues us i = seed i ++ us := by
  simp [addValues]

@[simp]
lemma addValues_of_ne (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i))
    {j : ι} (hj : j ≠ i) : seed.addValues us j = seed j := by
  simp [addValues, Function.update_of_ne hj]

@[simp]
lemma addValues_nil (seed : QuerySeed spec) (i : ι) :
    seed.addValues (i := i) ([] : List (spec.Range i)) = seed := by
  simp [addValues]

lemma addValues_cons (seed : QuerySeed spec) {i : ι} (u : spec.Range i)
    (us : List (spec.Range i)) :
    seed.addValues (u :: us) = (seed.addValues [u]).addValues us := by
  ext j; by_cases hj : j = i
  · subst hj; simp [addValues]
  · simp [addValues, Function.update_of_ne hj]

/-- Prepend a list of values to the seed at index `i`. -/
def prependValues (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i)) : QuerySeed spec :=
  Function.update seed i (us ++ seed i)

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
  simp [prependValues, Function.update_of_ne hj]

@[simp]
lemma prependValues_nil (seed : QuerySeed spec) (i : ι) :
    seed.prependValues (i := i) ([] : List (spec.Range i)) = seed := by
  simp [prependValues]

lemma prependValues_take_drop (seed : QuerySeed spec) (i : ι) (n : ℕ) :
    QuerySeed.prependValues (Function.update seed i ((seed i).drop n))
      ((seed i).take n : List (spec.Range i)) = seed := by
  ext j
  by_cases hj : j = i
  · subst hj; simp [prependValues, List.take_append_drop]
  · simp [prependValues, Function.update_of_ne hj]

lemma eq_of_prependValues_eq (seed rest : QuerySeed spec)
    {i : ι} (xs : List (spec.Range i)) {n : ℕ} (hlen : xs.length = n)
    (h : rest.prependValues xs = seed) :
    xs = (seed i).take n ∧ rest = Function.update seed i ((seed i).drop n) := by
  have hi : xs ++ rest i = seed i := by
    have := congrArg (· i) h; simp [prependValues] at this; exact this
  constructor
  · calc xs = (xs ++ rest i).take xs.length := by simp
      _ = (seed i).take n := by rw [hi, hlen]
  · funext j
    by_cases hj : j = i
    · cases hj
      simp only [Function.update_self]
      have : rest i = (xs ++ rest i).drop xs.length := by simp
      rw [this, hi, hlen]
    · have hj' : rest j = seed j := by
        have := congrArg (· j) h; simp [prependValues, Function.update_of_ne hj] at this
        exact this
      simp [Function.update_of_ne hj, hj']

lemma eq_of_prependValues_singleton_eq (seed rest : QuerySeed spec)
    {i : ι} (u : spec.Range i) (h : rest.prependValues [u] = seed) :
    u :: rest i = seed i ∧ rest = Function.update seed i ((seed i).tail) := by
  have hEq :
      [u] = (seed i).take 1 ∧ rest = Function.update seed i ((seed i).drop 1) :=
    eq_of_prependValues_eq (seed := seed) (rest := rest) (i := i)
      (xs := [u]) (n := 1) (by simp) h
  refine ⟨?_, ?_⟩
  · have hi : [u] ++ rest i = seed i := by
      have := congrArg (fun s => s i) h
      simpa [prependValues] using this
    simpa using hi
  · simpa using hEq.2

abbrev addValue (seed : QuerySeed spec) (i : ι) (u : spec.Range i) :
    QuerySeed spec :=
  seed.addValues [u]

/-- Take only the first `n` values of the seed at index `i`. -/
def takeAtIndex (seed : QuerySeed spec) (i : ι) (n : ℕ) : QuerySeed spec :=
  Function.update seed i ((seed i).take n)

@[simp] lemma takeAtIndex_apply_self (seed : QuerySeed spec) (i : ι) (n : ℕ) :
    seed.takeAtIndex i n i = (seed i).take n := by
  simp [takeAtIndex]

@[simp] lemma takeAtIndex_apply_of_ne (seed : QuerySeed spec) (i : ι) (n : ℕ) (j : ι)
    (hj : j ≠ i) : seed.takeAtIndex i n j = seed j := by
  simp [takeAtIndex, Function.update_of_ne hj]

@[simp] lemma takeAtIndex_length (seed : QuerySeed spec) (i : ι) :
    seed.takeAtIndex i (seed i).length = seed :=
  funext fun j => by
    by_cases hj : j = i
    · subst hj; simp [takeAtIndex]
    · simp [takeAtIndex, Function.update_of_ne hj]

lemma takeAtIndex_addValues_drop (seed : QuerySeed spec) (i : ι) (n : ℕ) :
    (seed.takeAtIndex i n).addValues ((seed i).drop n) = seed := by
  ext j; by_cases hj : j = i
  · subst hj; simp [takeAtIndex, addValues, List.take_append_drop]
  · simp [takeAtIndex, addValues, Function.update_of_ne hj]

/-- Pop one value from index `i`, returning the consumed value and updated seed when nonempty. -/
def pop (seed : QuerySeed spec) (i : ι) : Option (spec.Range i × QuerySeed spec) :=
  match seed i with
  | [] => none
  | u :: us => some (u, Function.update seed i us)

@[simp]
lemma pop_eq_none_iff (seed : QuerySeed spec) (i : ι) :
    seed.pop i = none ↔ seed i = [] := by
  unfold pop
  cases hsi : seed i <;> simp

@[simp]
lemma pop_eq_some_of_cons (seed : QuerySeed spec) (i : ι)
    (u : spec.Range i) (us : List (spec.Range i))
    (h : seed i = u :: us) :
    seed.pop i = some (u, Function.update seed i us) := by
  unfold pop
  simp [h]

lemma cons_of_pop_eq_some (seed : QuerySeed spec) (i : ι)
    (u : spec.Range i) (rest : QuerySeed spec)
    (h : seed.pop i = some (u, rest)) :
    u :: rest i = seed i := by
  unfold pop at h
  cases hsi : seed i with
  | nil =>
    simp [hsi] at h
  | cons u0 us =>
    simp [hsi] at h
    rcases h with ⟨hu, hrest⟩
    subst hu hrest
    simp

lemma rest_eq_update_tail_of_pop_eq_some (seed : QuerySeed spec) (i : ι)
    (u : spec.Range i) (rest : QuerySeed spec)
    (h : seed.pop i = some (u, rest)) :
    rest = Function.update seed i ((seed i).tail) := by
  unfold pop at h
  cases hsi : seed i with
  | nil =>
    simp [hsi] at h
  | cons u0 us =>
    simp [hsi] at h
    rcases h with ⟨hu, hrest⟩
    subst hu hrest
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
    exact ⟨by simp, fun j hj => by simp [addValues, Function.update_of_ne hj]⟩
  · rintro ⟨happ, hother⟩
    apply funext; intro j
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
  simp only [pop, prependValues, Function.update_self, List.singleton_append,
    Function.update_idem, Function.update_eq_self]

lemma prependValues_singleton_injective (i : ι) :
    Function.Injective (fun (p : spec.Range i × QuerySeed spec) => p.2.prependValues [p.1]) := by
  intro ⟨u₁, s₁⟩ ⟨u₂, s₂⟩ h
  have ht := congr_fun h i
  simp only [prependValues_singleton] at ht
  obtain ⟨hu, hst⟩ := List.cons_eq_cons.mp ht
  refine Prod.ext hu (funext fun j => ?_)
  by_cases hj : j = i
  · exact hj ▸ hst
  · have := congr_fun h j; simp only [prependValues_of_ne _ _ hj] at this; exact this

lemma eq_prependValues_of_pop_eq_some {seed : QuerySeed spec} {i : ι}
    {u : spec.Range i} {rest : QuerySeed spec} (h : seed.pop i = some (u, rest)) :
    rest.prependValues [u] = seed := by
  have hcons := cons_of_pop_eq_some seed i u rest h
  have hrest := rest_eq_update_tail_of_pop_eq_some seed i u rest h
  subst hrest; funext j
  by_cases hj : j = i
  · subst hj; simp only [prependValues_singleton, Function.update_self]
    simpa [Function.update_self] using hcons
  · simp only [prependValues_of_ne _ _ hj, Function.update_of_ne hj]

lemma pop_takeAtIndex_prependValues_of_ne (s' : QuerySeed spec) (i₀ : ι) (k : ℕ)
    {t : ι} (u₀ : spec.Range t) (hti : t ≠ i₀) :
    ((s'.prependValues [u₀]).takeAtIndex i₀ k).pop t =
      some (u₀, s'.takeAtIndex i₀ k) := by
  have h1 : ((s'.prependValues [u₀]).takeAtIndex i₀ k) t = u₀ :: s' t := by
    rw [takeAtIndex_apply_of_ne _ _ _ _ hti, prependValues_singleton]
  rw [pop_eq_some_of_cons _ _ u₀ (s' t) h1]
  congr 1
  suffices Function.update ((s'.prependValues [u₀]).takeAtIndex i₀ k) t (s' t) =
      s'.takeAtIndex i₀ k from Prod.ext rfl this
  funext j
  by_cases hj : j = t
  · subst hj; simp [Function.update_self, takeAtIndex_apply_of_ne _ _ _ _ hti]
  · rw [Function.update_of_ne hj]
    by_cases hji : j = i₀
    · subst hji
      simp [takeAtIndex_apply_self, prependValues_of_ne _ _ (Ne.symm hti)]
    · simp [takeAtIndex_apply_of_ne _ _ _ _ hji, prependValues_of_ne _ _ hj]

lemma pop_takeAtIndex_prependValues_self (s' : QuerySeed spec) (i₀ : ι)
    (u₀ : spec.Range i₀) {k : ℕ} (hk : 0 < k) :
    ((s'.prependValues [u₀]).takeAtIndex i₀ k).pop i₀ =
      some (u₀, s'.takeAtIndex i₀ (k - 1)) := by
  have h1 : ((s'.prependValues [u₀]).takeAtIndex i₀ k) i₀ =
      u₀ :: (s' i₀).take (k - 1) := by
    simp only [takeAtIndex_apply_self, prependValues_singleton]
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
    simp [List.take_succ_cons]
  rw [pop_eq_some_of_cons _ _ u₀ ((s' i₀).take (k - 1)) h1]
  congr 1
  suffices Function.update ((s'.prependValues [u₀]).takeAtIndex i₀ k) i₀
      ((s' i₀).take (k - 1)) = s'.takeAtIndex i₀ (k - 1) by
    exact Prod.ext rfl this
  funext j
  by_cases hj : j = i₀
  · subst hj; simp [Function.update_self, takeAtIndex_apply_self]
  · rw [Function.update_of_ne hj, takeAtIndex_apply_of_ne _ _ _ _ hj,
      takeAtIndex_apply_of_ne _ _ _ _ hj, prependValues_of_ne _ _ hj]

end QuerySeed

end OracleSpec
