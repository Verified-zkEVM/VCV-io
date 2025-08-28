/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Structures For Tracking a Computation's Oracle Queries

This file defines types like `QueryLog` and `QueryCache` for use with
simulation oracles and implementation transformers defined in the same directory.
-/

open OracleSpec OracleComp

universe u v w

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec}

/-- Type to represent a cache of queries to oracles in `spec`.
Defined to be a function from (indexed) inputs to an optional output. -/
def QueryCache (spec : OracleSpec) : Type _ :=
  (t : spec.domain) → Option (spec.range t)

namespace QueryCache

instance : EmptyCollection (QueryCache spec) := ⟨fun _ => none⟩

variable [spec.DecidableEq] [DecidableEq ι] (cache : QueryCache spec)

/-- Add a index + input pair to the cache by updating the function -/
def cacheQuery (t : spec.domain) (u : spec.range t) : QueryCache spec :=
  Function.update cache t u

-- lemma cacheQuery_eq_ite_ite (i : ι) (t : spec.domain i) (u : spec.range i) :
--     cache.cacheQuery i t u = λ j t' ↦
--       if h : j = i then (if h ▸ t' = t then some (h ▸ u) else cache j t') else cache j t' := by
--   refine funext (λ j ↦ funext (λ t' ↦ ?_))
--   by_cases h : j = i
--   · induction h
--     by_cases ht : t' = t
--     · simp [ht, cacheQuery]
--     · simp [ht, cacheQuery]
--   · simp [h, cacheQuery]

end QueryCache

/-- Simple wrapper in order to introduce the `Monoid` structure for `countingOracle`.
Marked as reducible and can generally be treated as just a function.
`idx` gives the "index" for a given input -/
@[reducible] def QueryCount (ι : Type*) (_spec : OracleSpec) := ι → ℕ

namespace QueryCount

/-- Pointwise addition as the `Monoid` operation used for `WriterT`. -/
instance : Monoid (QueryCount ι spec) where
  mul qc qc' := qc + qc'
  mul_assoc := add_assoc
  one := 0
  one_mul := zero_add
  mul_one := add_zero

@[simp] lemma monoid_mul_def (qc qc' : QueryCount ι spec) :
  (@HMul.hMul _ _ _ (@instHMul _ (Monoid.toMulOneClass.toMul)) qc qc')
     = (qc : ι → ℕ) + (qc' : ι → ℕ) := rfl

@[simp] lemma monoid_one_def :
    (@OfNat.ofNat (QueryCount ι spec) 1 (@One.toOfNat1 _ (Monoid.toOne))) = (0 : ι → ℕ) := rfl

def single [DecidableEq ι] (i : ι) : QueryCount ι spec := Function.update 0 i 1

-- @[simp]
-- lemma single_le_iff_pos [DecidableEq ι] (i : ι) (qc : QueryCount spec) :
--     single i ≤ qc ↔ 0 < qc i := by
--   simp [single, Function.update, Pi.hasLe]
--   constructor <;> intro h
--   · have : 1 ≤ qc i := by simpa using h i
--     exact this
--   · intro j
--     by_cases hj : j = i
--     · simp [hj]; omega
--     · simp [hj]

end QueryCount

/-- Log of queries represented by a list of dependent product's tagging the oracle's index.
`(i : ι) → spec.domain i × spec.range i` is slightly more restricted as it doesn't
keep track of query ordering between different oracles. -/
@[reducible] def QueryLog (spec : OracleSpec) : Type _ :=
  List ((t : spec.domain) × spec.range t)

namespace QueryLog

/-- Dummy `Monoid` instance to be used with `WriterT`, actual calls should use `append`. -/
instance : Monoid (QueryLog spec) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := List.nil
  one_mul := List.nil_append
  mul_one := List.append_nil

@[simp] -- Automatically reduce "multiplication" of query logs to `List.append`
lemma monoid_mul_def (qc qc' : QueryLog spec) :
  (@HMul.hMul _ _ _ (@instHMul _ (Monoid.toMulOneClass.toMul)) qc qc')
     = (qc : List _) ++ (qc' : List _) := rfl

@[simp] lemma monoid_one_def : (1 : QueryLog spec) = List.nil := rfl

/-- Query log with a single entry. -/
def singleton (t : spec.domain) (u : spec.range t) : QueryLog spec := [⟨t, u⟩]

/-- Update a query log by adding a new element to the appropriate list.
Note that this requires decidable equality on the indexing set. -/
def logQuery (log : QueryLog spec) (t : spec.domain) (u : spec.range t) : QueryLog spec :=
  log ++ singleton t u

instance [spec.DecidableEq] : DecidableEq (QueryLog spec) :=
  inferInstanceAs (DecidableEq (List _))

section getQ

-- variable [DecidableEq ι]

/-- Get all the queries with inputs satisfying `p` -/
def getQ (log : QueryLog spec) (p : spec.domain → Prop) [DecidablePred p] :
    List ((t : spec.domain) × spec.range t) :=
  List.foldr (fun ⟨t, u⟩ xs => if p t then ⟨t, u⟩ :: xs else xs) [] log

-- -- NOTE: should this simp? feels bad to simp with ▸ and pattern matching in target
-- lemma getQ_singleton {α} (q : OracleQuery spec α) (u : α) (i : ι) :
--     getQ (singleton q u) i = match q with
--       | query j t => if h : j = i then [h ▸ (t, u)] else [] := by
--   cases q with | query i t => ?_
--   simp [getQ, singleton]

-- @[simp]
-- lemma getQ_singleton_self (i : ι) (t : spec.domain i) (u : spec.range i) :
--     getQ (singleton (query i t) u) i = [(t, u)] := by simp [getQ_singleton]

-- lemma getQ_singleton_of_ne {α} {q : OracleQuery spec α} {u : α} {i : ι}
--     (h : q.index ≠ i) : getQ (singleton q u) i = [] := by
--   cases q with | query i t => simpa [getQ_singleton] using h

-- @[simp]
-- lemma getQ_cons (log : QueryLog spec) (q : (i : ι) × spec.domain i × spec.range i) (i : ι) :
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
def countQ (log : QueryLog spec) (p : spec.domain → Prop) [DecidablePred p] : ℕ :=
  (log.getQ p).length

-- @[simp]
-- lemma countQ_singleton {α} (q : OracleQuery spec α) (u : α) (i : ι) :
--     countQ (singleton q u) i = if q.index = i then 1 else 0 := by
--   cases q with | query i t => ?_
--   simp only [countQ, getQ_singleton, OracleQuery.index_query]
--   split_ifs with hi <;> rfl

-- lemma countQ_singleton_self (i : ι) (t : spec.domain i) (u : spec.range i) :
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
def wasQueried [spec.DecidableEq] (log : QueryLog spec) (t : spec.domain) : Bool :=
  log.getQ (· = t) ≠ []

section prod

-- variable {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

-- /-- Get only the portion of the log for queries in `spec₁`. -/
-- protected def fst (log : QueryLog (spec₁ ++ₒ spec₂)) : QueryLog spec₁ :=
--   log.filterMap (fun | ⟨.inl i, t, u⟩ => some ⟨i, t, u⟩ | _ => none)

-- /-- Get only the portion of the log for queries in `spec₂`. -/
-- protected def snd (log : QueryLog (spec₁ ++ₒ spec₂)) : QueryLog spec₂ :=
--   log.filterMap (fun | ⟨.inr i, t, u⟩ => some ⟨i, t, u⟩ | _ => none)

-- /-- View a log for `spec₁` as one for `spec₁ ++ₒ spec₂` by inclusion. -/
-- protected def inl (log : QueryLog spec₁) : QueryLog (spec₁ ++ₒ spec₂) :=
--   log.map fun ⟨i, t, u⟩ => ⟨.inl i, t, u⟩

-- /-- View a log for `spec₂` as one for `spec₁ ++ₒ spec₂` by inclusion. -/
-- protected def inr (log : QueryLog spec₂) : QueryLog (spec₁ ++ₒ spec₂) :=
--   log.map fun ⟨i, t, u⟩ => ⟨.inr i, t, u⟩

-- instance : Coe (QueryLog spec₁) (QueryLog (spec₁ ++ₒ spec₂)) := ⟨QueryLog.inl⟩
-- instance : Coe (QueryLog spec₂) (QueryLog (spec₁ ++ₒ spec₂)) := ⟨QueryLog.inr⟩

end prod

end QueryLog

/-- Type to represent a store of seed values to use in a computation, represented as a function.
Updates to individual seed lists are performed via continuation passing. -/
def QuerySeed (spec : OracleSpec) (ι : Type u) [HasIndexing spec ι] : Type _ :=
  (i : ι) → List (HasIndexing.xdi spec i)

-- namespace QuerySeed

-- instance : DFunLike (QuerySeed spec) ι (λ i ↦ List (spec.range i)) where
--   coe := λ seed ↦ seed
--   coe_injective' := Function.injective_id

-- @[ext]
-- protected lemma ext (seed₁ seed₂ : QuerySeed spec) (h : ∀ i, seed₁ i = seed₂ i) : seed₁ = seed₂ :=
--     DFunLike.ext seed₁ seed₂ h

-- @[simp] instance : EmptyCollection (QuerySeed spec) := ⟨λ _ ↦ []⟩

-- def update [DecidableEq ι] (seed : QuerySeed spec) (i : ι)
--     (xs : List (spec.range i)) : QuerySeed spec :=
--   Function.update seed i xs

-- section addValues

-- /-- Add a list of values to the query seed.-/
-- def addValues [DecidableEq ι] {i : ι}
--     (us : List (spec.range i)) (seed : QuerySeed spec) : QuerySeed spec :=
--   Function.update seed i (seed i ++ us)

-- variable [DecidableEq ι] {i : ι} (seed : QuerySeed spec) (us : List (spec.range i))

-- @[simp]
-- lemma addValues_apply (j : ι) : seed.addValues us j =
--     Function.update seed i (seed i ++ us) j := rfl

-- @[simp]
-- lemma addValues_nil {i : ι} (seed : QuerySeed spec) : seed.addValues (i := i) [] = seed := by
--   simp only [addValues, List.append_nil, Function.update_eq_self]

-- /-- Add a single value into the seed, by adding a singleton list -/
-- abbrev addValue (seed : QuerySeed spec) (i : ι) (u : spec.range i) : QuerySeed spec :=
--   seed.addValues [u]

-- end addValues

-- section takeAtIndex

-- /-- Take only the first `n` values of the seed at index `i`. -/
-- def takeAtIndex [DecidableEq ι] (seed : QuerySeed spec) (i : ι) (n : ℕ) : QuerySeed spec :=
--   Function.update seed i ((seed i).take n)

-- variable [DecidableEq ι] (seed : QuerySeed spec) (i : ι) (n : ℕ)

-- @[simp]
-- lemma takeAtIndex_apply (j : ι) : seed.takeAtIndex i n j =
--     (Function.update seed i ((seed i).take n) j) := rfl

-- @[simp]
-- lemma takeAtIndex_addValues (seed : QuerySeed spec) {i : ι} (n : ℕ) (xs : List (spec.range i)) :
--     (seed.addValues xs).takeAtIndex i n = if n ≤ (seed i).length
--       then seed.takeAtIndex i n else seed.addValues (xs.take (n - (seed i).length)) := by
--   refine funext (λ j ↦ ?_)
--   by_cases hj : j = i
--   · induction hj
--     split_ifs with hn
--     · simp [hn]
--     · suffices List.take n (seed j ++ xs) = seed j ++ List.take (n - (seed j).length) xs
--       by simpa using this
--       rw [List.take_append_eq_append_take]
--       simpa using le_of_not_le hn
--   · split_ifs with _ <;> simp [hj]

-- -- @[simp]
-- -- lemma addValues_takeAtIndex (seed : QuerySeed spec) {i : ι} (xs : List (spec.range i)) (n : ℕ) :
-- --     (seed.takeAtIndex i n).addValues xs =

-- @[simp]
-- lemma takeAtIndex_length (seed : QuerySeed spec) (i : ι) :
--     seed.takeAtIndex i (seed i).length = seed := funext (λ j ↦ by simp)

-- lemma eq_takeAtIndex_length_iff (seed seed' : QuerySeed spec) (i : ι) :
--     seed = seed'.takeAtIndex i (seed i).length ↔
--       seed' = seed.addValues ((seed' i).drop (seed i).length) := by
--   refine ⟨λ h ↦ QuerySeed.ext _ _ (λ j ↦ ?_), λ h ↦ ?_⟩
--   · by_cases hj : j = i
--     · induction hj
--       rw [h]
--       suffices (seed j).length ≤ (seed' j).length
--       by simp [this]
--       simpa using congr_arg List.length (congr_fun h j)
--     · rw [h]
--       simp [hj]
--   · rw [h]
--     simp

-- end takeAtIndex

-- section ofList

-- def ofList [DecidableEq ι] {i : ι} (xs : List (spec.range i)) : QuerySeed spec :=
--   fun j => if h : i = j then h ▸ xs else []

-- end ofList

-- -- def nextSeed [DecidableEq ι] {α : Type} :
-- --     (q : OracleQuery spec α) → StateT (QuerySeed spec) (OracleComp spec) α
-- --   | query i t => do
-- --     let seed ← get
-- --     return List.get?
-- --     match (← get) i with
-- --       | u :: us => return (u, Function.update seed i us)
-- --       | [] => failure

-- lemma eq_addValues_iff [DecidableEq ι] (seed seed' : QuerySeed spec)
--     {i : ι} (xs : List (spec.range i)) :
--     seed = seed'.addValues xs ↔ seed' = seed.takeAtIndex i (seed' i).length ∧
--       xs = (seed i).drop (seed' i).length := by
--   refine ⟨λ h ↦ ?_, λ ⟨h1, h2⟩ ↦ ?_⟩
--   · simp [h]
--   · rw [h1, h2]
--     refine funext (λ j ↦ ?_)
--     by_cases hj : j = i
--     · induction hj; simp
--     · simp [hj]

-- lemma addValues_eq_iff [DecidableEq ι] (seed seed' : QuerySeed spec)
--     {i : ι} (xs : List (spec.range i)) :
--     seed.addValues xs = seed' ↔ seed = seed'.takeAtIndex i (seed i).length ∧
--       xs = (seed' i).drop (seed i).length :=
--   eq_comm.trans (eq_addValues_iff seed' seed xs)

-- end QuerySeed

end OracleSpec
