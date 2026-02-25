/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
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

variable [spec.DecidableEq] [DecidableEq ι] (cache : QueryCache spec)

/-- Add a index + input pair to the cache by updating the function (wrapper around `Function.update`) -/
def cacheQuery (t : spec.Domain) (u : spec.Range t) : QueryCache spec :=
  Function.update cache t u

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

-- -- NOTE: should this simp? feels bad to simp with ▸ and pattern matching in target
-- lemma getQ_singleton {α} (q : OracleQuery spec α) (u : α)
--     (p : spec.Domain → Prop) [DecidablePred p] :
--     getQ (singleton q u) p = match q with
--       | query j t => if h : j = i then [h ▸ (t, u)] else [] := by
--   cases q with | query i t => ?_
--   simp [getQ, singleton]

-- @[simp]
-- lemma getQ_singleton_self (i : ι) (t : spec.Domain i) (u : spec.Range i) :
--     getQ (singleton (query i t) u) i = [(t, u)] := by simp [getQ_singleton]

-- lemma getQ_singleton_of_ne {α} {q : OracleQuery spec α} {u : α} {i : ι}
--     (h : q.index ≠ i) : getQ (singleton q u) i = [] := by
--   cases q with | query i t => simpa [getQ_singleton] using h

-- @[simp]
-- lemma getQ_cons (log : QueryLog spec) (q : (i : ι) × spec.Domain i × spec.Range i) (i : ι) :
--     getQ (q :: log) i =
--       if h : q.1 = i then h ▸ (q.2.1, q.2.2) :: getQ log i else getQ log i := by
--   simp [getQ]

-- @[simp]
-- lemma getQ_append (log log' : QueryLog spec) (i : ι) :
--     (log ++ log').getQ i = log.getQ i ++ log'.getQ i := by
--   induction log with
--   | nil => rfl
--   | cons hd tl ih =>
--     induction log' with
--     | nil => simp [getQ]
--     | cons hd' tl' ih' =>
--       simp
--       split_ifs with hi₁ <;> simp [ih, ih', hi₁]
--       · split_ifs; simp
--       · simpa
--       · split_ifs; simp
--       · simpa

-- @[simp]
-- lemma getQ_logQuery {α} (log : QueryLog spec) (q : OracleQuery spec α) (u : α)
--     (i : ι) : (log.logQuery q u).getQ i = log.getQ i ++ (singleton q u).getQ i := by
--   rw [logQuery, getQ_append]

end getQ

section countQ

-- variable [DecidableEq ι]

/-- Count the number of queries with inputs satisfying `p`. -/
def countQ (log : QueryLog spec) (p : spec.Domain → Prop) [DecidablePred p] : ℕ :=
  (log.getQ p).length

-- @[simp]
-- lemma countQ_singleton {α} (q : OracleQuery spec α) (u : α) (i : ι) :
--     countQ (singleton q u) i = if q.index = i then 1 else 0 := by
--   cases q with | query i t => ?_
--   simp only [countQ, getQ_singleton, OracleQuery.index_query]
--   split_ifs with hi <;> rfl

-- lemma countQ_singleton_self (i : ι) (t : spec.Domain i) (u : spec.Range i) :
--     countQ (singleton (query i t) u) i = 1 := by simp

-- @[simp]
-- lemma countQ_append (log log' : QueryLog spec) (i : ι) :
--     (log ++ log').countQ i = log.countQ i + log'.countQ i := by simp [countQ]

-- @[simp]
-- lemma countQ_logQuery {α} (log : QueryLog spec) (q : OracleQuery spec α) (u : α)
--     (i : ι) : (log.logQuery q u).countQ i = log.countQ i + if q.index = i then 1 else 0 := by
--   rw [logQuery, countQ_append, countQ_singleton]

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

/-- Prepend a list of values to the seed at index `i`. -/
def prependValues (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i)) : QuerySeed spec :=
  Function.update seed i (us ++ seed i)

@[simp]
lemma prependValues_self (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i)) :
    seed.prependValues us i = us ++ seed i := by
  simp [prependValues]

@[simp]
lemma prependValues_of_ne (seed : QuerySeed spec) {i : ι} (us : List (spec.Range i))
    {j : ι} (hj : j ≠ i) : seed.prependValues us j = seed j := by
  simp [prependValues, Function.update_of_ne hj]

@[simp]
lemma prependValues_nil (seed : QuerySeed spec) (i : ι) :
    seed.prependValues (i := i) ([] : List (spec.Range i)) = seed := by
  simp [prependValues]

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

end QuerySeed

end OracleSpec
