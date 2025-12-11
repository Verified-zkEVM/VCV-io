/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Support of a Computation

This file defines a function `OracleComp.support : OracleComp spec α → Set α` that
gives the set of possible outputs of a computation, assuming all oracle outputs are possible.

If the final output type has decidable equality we can also define a function
`OracleComp.finSupport : OracleComp spec α → Finset α` with the same property.
This relies on decidable equality instances in `OracleSpec` as well, and the definition
would need to be adjusted if those were moved into a seperate typeclass.

We avoid using `(evalDist oa).support` as the definition of the support, as this forces
noncomputability due to the use of real numbers, and also makes defining `finSupport` harder.
-/

open OracleSpec

namespace OracleComp

universe u v w

-- TODO: We need global `Set.AlternativeMonad` instances to transition this.
-- section support_test

-- variable {ι : Type u} {spec : OracleSpec ι} {α : Type v}

-- section altMonadTest

-- open Classical

-- protected def Set.alternativeMonad : AlternativeMonad.{u} Set where
--   failure := ∅
--   orElse s t := if s = ∅ then t () else s
--   __ := Set.monad

-- end altMonadTest

-- attribute [local instance] Set.alternativeMonad

-- def supportWhen' (ox : OracleComp spec α)
--     (possible_outputs : {α : Type v} → OracleQuery spec α → Set α) : Set α :=
--   ox.simulateQ ⟨possible_outputs⟩

-- def support' (oa : OracleComp spec α) : Set α :=
--   oa.simulateQ ⟨fun | query i _ => Set.univ⟩

-- end support_test

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type v}

/-- Possible outputs of the computation `oa` given a set of possible outputs for each query. -/
def supportWhen (oa : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Set α) : Set α := by
  induction oa using OracleComp.construct with
  | pure x => exact {x}
  | failure => exact ∅
  | query_bind q _ f => exact ⋃ u ∈ possible_outputs q, f u

/-- The `support` of a computation `oa` is the set of all possible output values,
assuming that all output values of the oracles are possible.
This is naturally compatible with `evalDist` where the oracles respond uniformly. -/
def support (oa : OracleComp spec α) : Set α :=
  oa.supportWhen fun _ => Set.univ

lemma support_def (oa : OracleComp spec α) :
    oa.support = oa.supportWhen fun _ => Set.univ := rfl

-- @[simp] lemma supportWhen_univ (oa : OracleComp spec α) :
--     (oa.supportWhen fun _ => Set.univ) = oa.support := rfl

/-- Given a `DecidableEq` instance on the return typ of a computation `oa`,
and a finite set `possible_outputs q` for any possible oracle query `q`,
construct a finite set of all possible outputs of the computation `oa` assuming that at each
query only the possible outputs are returned. -/
def finSupportWhen [DecidableEq α] (oa : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Finset α) : Finset α := by
  induction oa using OracleComp.construct with
  | pure x => exact {x}
  | failure => exact ∅
  | query_bind q _ f => exact (possible_outputs q).biUnion f

/-- Case of `finSupportWhen` where each oracle has a finite type as output and we assume any
possible output of oracle queries. -/
def finSupport [∀ i, Fintype (spec.range i)] [DecidableEq α] (oa : OracleComp spec α) : Finset α :=
  oa.finSupportWhen fun | query _ _ => Finset.univ

lemma finSupport_def [∀ i, Fintype (spec.range i)] [DecidableEq α] (oa : OracleComp spec α) :
    oa.finSupport = oa.finSupportWhen fun | query _ _ => Finset.univ := rfl

section basic

variable (poss : {α : Type v} → OracleQuery spec α → Set α)
  (fin_poss : {α : Type v} → OracleQuery spec α → Finset α)

@[simp] lemma supportWhen_pure (x : α) :
    (pure x : OracleComp spec α).supportWhen poss = {x} := rfl

@[simp] lemma support_pure (x : α) :
    (pure x : OracleComp spec α).support = {x} := rfl

@[simp] lemma finSupportWhen_pure [DecidableEq α] (x : α) :
    (pure x : OracleComp spec α).finSupportWhen fin_poss = {x} := rfl

@[simp] lemma finSupport_pure [spec.FiniteRange] [DecidableEq α] (x : α) :
    (pure x : OracleComp spec α).finSupport = {x} := rfl

@[simp] lemma supportWhen_failure : (failure : OracleComp spec α).supportWhen poss = ∅ := rfl

@[simp] lemma support_failure : (failure : OracleComp spec α).support = ∅ := rfl

@[simp] lemma finSupportWhen_failure [DecidableEq α] :
    (failure : OracleComp spec α).finSupportWhen fin_poss = ∅ := rfl

@[simp] lemma finSupport_failure [spec.FiniteRange] [DecidableEq α] :
    (failure : OracleComp spec α).finSupport = ∅ := rfl

@[simp] lemma supportWhen_query (q : OracleQuery spec α) :
    (q : OracleComp spec α).supportWhen poss = poss q := by
  simp only [supportWhen, construct_query, Set.biUnion_of_singleton]

@[simp] lemma support_query (q : OracleQuery spec α) :
    (q : OracleComp spec α).support = Set.univ := by
  rw [support_def, supportWhen_query]

@[simp] lemma finSupportWhen_query [DecidableEq α] (q : OracleQuery spec α) :
    (q : OracleComp spec α).finSupportWhen fin_poss = fin_poss q := by
  simp only [finSupportWhen, construct_query, Finset.biUnion_singleton_eq_self]

lemma finSupport_query [spec.FiniteRange] [DecidableEq α] (q : OracleQuery spec α) :
    (q : OracleComp spec _).finSupport = match q with | query _ _ => Finset.univ := by
  simp [finSupport_def, finSupportWhen_query]

@[simp] lemma supportWhen_query_bind (q : OracleQuery spec α) (ob : α → OracleComp spec β) :
    (liftM q >>= ob).supportWhen poss = ⋃ x ∈ poss q, (ob x).supportWhen poss := by
  simp [supportWhen]

@[simp] lemma support_query_bind (q : OracleQuery spec α) (ob : α → OracleComp spec β) :
    (liftM q >>= ob).support = ⋃ x, (ob x).support := by
  simp [support]

@[simp] lemma finSupportWhen_query_bind [DecidableEq β]
    (q : OracleQuery spec α) (ob : α → OracleComp spec β) :
    (liftM q >>= ob).finSupportWhen fin_poss =
      (fin_poss q).biUnion fun x => (ob x).finSupportWhen fin_poss := by
  simp [finSupportWhen]

@[simp] lemma finSupport_query_bind [spec.FiniteRange] [Fintype α] [DecidableEq β]
    (q : OracleQuery spec α) (ob : α → OracleComp spec β) :
    (liftM q >>= ob).finSupport = Finset.univ.biUnion fun x => (ob x).finSupport := by
  cases q; simp [finSupport, Finset.ext_iff]

@[simp] lemma supportWhen_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).supportWhen poss = ⋃ x ∈ oa.supportWhen poss, (ob x).supportWhen poss := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simp
  | query_bind i t oa hoa => simp [hoa]
  | failure => simp

@[simp] lemma support_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).support = ⋃ x ∈ oa.support, (ob x).support := by
  simp [support]

@[simp] lemma finSupportWhen_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    [DecidableEq α] [DecidableEq β] :
    (oa >>= ob).finSupportWhen fin_poss =
      (oa.finSupportWhen fin_poss).biUnion fun x => (ob x).finSupportWhen fin_poss := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simp
  | query_bind i t oa hoa => simp [hoa, Finset.biUnion_biUnion]
  | failure => simp

@[simp] lemma finSupport_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    [hα : DecidableEq α] [hβ : DecidableEq β] [spec.FiniteRange] :
    (oa >>= ob).finSupport = oa.finSupport.biUnion (λ x ↦ (ob x).finSupport) := by
  simp [finSupport]

lemma mem_support_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    y ∈ (oa >>= ob).support ↔ ∃ x ∈ oa.support, y ∈ (ob x).support := by simp

lemma mem_finSupport_bind_iff [spec.FiniteRange]
    (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    [hoa : DecidableEq α] [hob : DecidableEq β] (y : β) : y ∈ (oa >>= ob).finSupport ↔
      ∃ x ∈ oa.finSupport, y ∈ (ob x).finSupport := by simp

/-- The support of a computation is finite if oracles have finite ranges. -/
instance supportWhen_finite [spec.FiniteRange] (oa : OracleComp spec α) :
    Finite ↥(oa.supportWhen poss) := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact Set.finite_singleton x
  | query_bind i t oa hoa =>
      simpa using Finite.Set.finite_biUnion'' _ fun x => (oa x).supportWhen poss
  | failure => exact Set.toFinite ∅

/-- The support of a computation is finite when viewed as a type. -/
instance support_finite [spec.FiniteRange] (oa : OracleComp spec α) :
    Finite ↥(oa.support) := supportWhen_finite _ oa

/-- With a `DecidableEq` instance we can show that the support is actually a `Fintype`,
rather than just `Finite` as in `support_finite`. -/
instance support_fintype [spec.FiniteRange] [DecidableEq α] (oa : OracleComp spec α) :
    Fintype ↥oa.support := by
  induction oa using OracleComp.construct with
  | pure x => exact Fintype.subtypeEq x
  | query_bind q oa hoa => have := q.rangeFintype; simpa using Set.fintypeiUnion _
  | failure => exact Set.fintypeEmpty

end basic

section coe

/-- `finSupport` when viewed as a `Set` gives the regular `support` of the computation.  -/
@[simp]
lemma coe_finSupport [spec.FiniteRange] [DecidableEq α]
    (oa : OracleComp spec α) : ↑oa.finSupport = oa.support := by
  induction oa using OracleComp.induction with
  | pure x => apply Finset.coe_singleton
  | query_bind i t oa hoa => simp [hoa]
  | failure => apply Finset.coe_empty

variable [spec.FiniteRange] [DecidableEq α] (oa : OracleComp spec α) (s : Finset α)

lemma finSupport_eq_iff_support_eq_coe : oa.finSupport = s ↔ oa.support = ↑s :=
  Finset.coe_inj.symm.trans (by rw [coe_finSupport])
lemma eq_finSupport_iff_coe_eq_support : s = oa.finSupport ↔ ↑s = oa.support :=
  Finset.coe_inj.symm.trans (by rw [coe_finSupport])

lemma finSupport_subset_iff_support_subset_coe : oa.finSupport ⊆ s ↔ oa.support ⊆ ↑s :=
  Finset.coe_subset.symm.trans (by rw [coe_finSupport])
lemma subset_finSupport_iff_coe_subset_support : s ⊆ oa.finSupport ↔ ↑s ⊆ oa.support :=
  Finset.coe_subset.symm.trans (by rw [coe_finSupport])

lemma mem_finSupport_iff_mem_support (x : α) : x ∈ oa.finSupport ↔ x ∈ oa.support := by
  rw [← Finset.mem_coe, coe_finSupport]

lemma mem_finSupport_of_mem_support {x : α} (hx : x ∈ oa.support) : x ∈ oa.finSupport :=
  (mem_finSupport_iff_mem_support oa x).2 hx
lemma mem_support_of_mem_finSupport {x : α} (hx : x ∈ oa.finSupport) : x ∈ oa.support :=
  (mem_finSupport_iff_mem_support oa x).1 hx

end coe

section decidable

/-- If the output type of a computation has `DecidableEq` then membership in the `support`
of a computation is also decidable as a predicate.
NOTE: will need to be restricted if we allow infinite oracle codomains. -/
instance decidablePred_mem_support [spec.FiniteRange] [hα : DecidableEq α]
    (oa : OracleComp spec α) : DecidablePred (· ∈ oa.support) := by
  induction oa using OracleComp.construct with
  | pure x => exact λ y ↦ hα y x
  | failure => exact λ _ ↦ Decidable.isFalse (not_false)
  | query_bind q oa hoa =>
      simp only [support_bind, support_query, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      have := q.rangeFintype
      exact λ _ ↦ Fintype.decidableExistsFintype

/-- Membership in `finSupport` is a decidable predicate if it's defined. -/
instance decidablePred_mem_finSupport [spec.DecidableEq] [spec.FiniteRange] [DecidableEq α]
    (oa : OracleComp spec α) : DecidablePred (· ∈ oa.finSupport) := by
  simp [mem_finSupport_iff_mem_support]
  apply decidablePred_mem_support

end decidable

section nonempty

variable (oa : OracleComp spec α)

-- lemma defaultResult_mem_support : oa.defaultResult ∈ oa.support := by
--   induction oa using OracleComp.inductionOn with
--   | h_pure x => simp only [defaultResult, support_pure, Set.mem_singleton_iff]
--   | h_queryBind i t oa hoa =>
--       have : ∃ u, defaultResult (oa default) ∈ (oa u).support := ⟨default, hoa default⟩
--       simpa only [defaultResult, OracleComp.bind'_eq_bind, pure_bind,support_bind,support_query,
--         Set.mem_univ, Set.iUnion_true, Set.mem_iUnion] using this

-- lemma exists_mem_support : ∃ x : α, x ∈ oa.support :=
--   ⟨defaultResult oa, defaultResult_mem_support oa⟩

-- lemma defaultResult_mem_finSupport [DecidableEq α] : oa.defaultResult ∈ oa.finSupport := by
--   simpa only [mem_finSupport_iff_mem_support] using defaultResult_mem_support oa

-- @[simp] lemma support_nonempty : oa.support.Nonempty :=
--   ⟨defaultResult oa, defaultResult_mem_support oa⟩

-- @[simp] lemma finSupport_nonempty [DecidableEq α] : oa.finSupport.Nonempty :=
--   ⟨defaultResult oa, defaultResult_mem_finSupport oa⟩

-- @[simp] lemma support_ne_empty : oa.support ≠ ∅ := (support_nonempty oa).ne_empty
-- @[simp] lemma finSupport_ne_empty [DecidableEq α] : oa.finSupport ≠ ∅ :=
--   Finset.ne_empty_of_mem (defaultResult_mem_finSupport oa)

-- @[simp] lemma support_eq_singleton_iff (x : α) :
--     oa.support = {x} ↔ oa.support ⊆ {x} := by
--   rw [oa.support_nonempty.subset_singleton_iff]
-- @[simp] lemma finSupport_eq_singleton_iff [DecidableEq α] (x : α) :
--     oa.finSupport = {x} ↔ oa.finSupport ⊆ {x} := by
--   simp [finSupport_eq_iff_support_eq_coe]

end nonempty

@[simp] lemma support_eqRec (oa : OracleComp spec α) (h : α = β) :
    (h ▸ oa).support = h.symm ▸ oa.support := by
  induction h; rfl
@[simp] lemma finSupport_eqRec [spec.DecidableEq] [spec.FiniteRange]
    [hα : DecidableEq α] [hβ : DecidableEq β] (oa : OracleComp spec α) (h : α = β) :
    @finSupport _ _ _ _ hβ (h ▸ oa : OracleComp spec β) =
      h.symm ▸ @finSupport _ _ _ _ hα oa := by
  refine Finset.ext (λ x ↦ ?_)
  simp [mem_finSupport_iff_mem_support]
  induction h -- We can't do this earlier without running into trouble with `DecidableEq`
  exact Iff.symm (mem_finSupport_iff_mem_support oa x)

lemma mem_support_eqRec_iff (oa : OracleComp spec α) (h : α = β) (y : β) :
    y ∈ (h ▸ oa).support ↔ h.symm ▸ y ∈ oa.support := by
  induction h; rfl
-- lemma mem_finSupport_eqRec_iff [spec.DecidableEq] [spec.FiniteRange]
--     [hα : DecidableEq α] [hβ : DecidableEq β] (oa : OracleComp spec α) (h : α = β) (y : β) :
--     y ∈ (h ▸ oa).finSupport ↔ h.symm ▸ y ∈ oa.finSupport := by
--   induction h; rfl

@[simp] lemma support_map (oa : OracleComp spec α) (f : α → β) :
    (f <$> oa).support = f '' oa.support := by
  simp only [map_eq_pure_bind, ← Set.image_eq_iUnion, support_bind, support_pure]
@[simp] lemma fin_support_map [spec.DecidableEq] [spec.FiniteRange]
    [DecidableEq α] [DecidableEq β] (oa : OracleComp spec α) (f : α → β) :
    (f <$> oa).finSupport = oa.finSupport.image f := by
  simp [finSupport_eq_iff_support_eq_coe]

lemma mem_support_map {oa : OracleComp spec α} {x : α}
    (hx : x ∈ oa.support) (f : α → β) : f x ∈ (f <$> oa).support := by
  simp only [support_map, Set.mem_image]
  refine ⟨x, hx, rfl⟩

@[simp] lemma support_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    (if p then oa else oa').support = if p then oa.support else oa'.support :=
  apply_ite support p oa oa'
@[simp] lemma finSupport_ite [spec.DecidableEq] [spec.FiniteRange] [DecidableEq α]
    (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    (if p then oa else oa').finSupport = if p then oa.finSupport else oa'.finSupport :=
  apply_ite finSupport p oa oa'

@[simp] lemma support_coin : coin.support = {true, false} := by
  simpa using Set.pair_comm false true
@[simp] lemma finSupport_coin : coin.finSupport = {true, false} := by
  simp [finSupport_eq_iff_support_eq_coe]
  exact Set.pair_comm false true

@[simp] lemma support_uniformFin (n : ℕ) : ($[0..n]).support = Set.univ := support_query _
@[simp] lemma finSupport_uniformFin (n : ℕ) : ($[0..n]).finSupport = Finset.univ :=
  finSupport_query _

example : support (do
    let b ← coin; let b' ← coin
    let x ← (if b && b' then return 0 else return 1);
    let z ← (if b && b' then return x else return 0);
    return (x * z)) = {0} :=
  by simp [Set.eq_singleton_iff_unique_mem]

example : finSupport (do
    let b ← coin; let b' ← coin
    let x ← (if b || b' then return 0 else return 1);
    let z ← (if b || b' then return x else return 0);
    return (x * z)) = {0} :=
  by simp

-- section simulate

-- variable {ι ιₜ : Type*} {spec : OracleSpec ι} {specₜ : OracleSpec ιₜ}
--     {m : Type u → Type v} {α β γ σ : Type u} (so : QueryImpl spec (StateT σ (OracleComp specₜ)))

-- open Prod

-- lemma support_simulate' (oa : OracleComp spec α) (s : σ) :
--     (simulate' so s oa).support = fst <$> (simulate so s oa).support :=
--   support_map _ fst

-- /-- Since `support` assumes any possible query result, `simulate` will never reduce the support.
-- In particular the support of a simulation lies in the preimage of the original support. -/
-- lemma support_simulate_subset_preimage_support (oa : OracleComp spec α) (s : σ) :
--     (simulate so s oa).support ⊆ fst ⁻¹' oa.support := by
--   revert s
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa hoa =>
--       simp [hoa]
--       refine λ _ t s' _ ↦ Set.subset_iUnion_of_subset t (hoa t s')
--   | failure => simp

-- /-- Simulation only reduces the possible oracle outputs, so can't reduce the support.
-- In particular
-- the first output of a simulation has support at most that of the original computation -/
-- lemma support_simulate'_subset_support (oa : OracleComp spec α) (s : σ) :
--     (simulate' so s oa).support ⊆ oa.support := by
--   rw [simulate', StateT.run', support_map, Set.image_subset_iff]
--   apply support_simulate_subset_preimage_support

-- lemma mem_support_simulate'_of_mem_support_simulate {oa : OracleComp spec α} {s : σ} {x : α}
--     (s' : σ) (h : (x, s') ∈ (simulate so s oa).support) : x ∈ (simulate' so s oa).support := by
--   simp only [support_simulate', Set.fmap_eq_image, Set.mem_image, Prod.exists, exists_and_right,
--     exists_eq_right]
--   exact ⟨s', h⟩

-- end simulate

end OracleComp
