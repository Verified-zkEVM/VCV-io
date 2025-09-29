/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.NeverFails
import VCVio.EvalDist.OptionT
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Output Distribution of Computations

This file defines a `HasEvalPMF` for `OracleComp`, assuming uniform outputs of computations.
-/

open OracleSpec Option ENNReal BigOperators

universe u v w

namespace OracleComp

variable {spec : OracleSpec} {spec' : OracleSpec} {α β γ : Type w}

noncomputable instance [spec.Fintype] [spec.Inhabited] :
    HasEvalPMF (OracleComp spec) where
  toPMF := PFunctor.FreeM.mapMHom fun t : spec.domain => PMF.uniformOfFintype (spec.range t)

-- /-- The support of a computation assuming any possible return value of queries. -/
-- protected instance HasEvalSet : HasEvalSet (OracleComp spec) where
--   __ := PFunctor.FreeM.mapMHom (m := SetM) fun _ : spec.domain => Set.univ

-- lemma support_def (oa : OracleComp spec α) :
--     support oa = SetM.run (PFunctor.FreeM.mapM (fun _ => Set.univ) oa) := rfl

-- @[simp] lemma support_query (t : spec.domain) : support (query t) = Set.univ := by
--   simp [support_def, SetM.run]

-- variable [spec.Fintype] [spec.Inhabited]

-- /-- The standard (no failure) evaluation distribution `HasEvalPMF` on `OracleComp` given by mapping
--   queries to a uniform output distribution. In the case of `ProbComp` this is exactly the
--   distribution coming from each uniform selection responding uniformly. -/
-- noncomputable instance : HasEvalPMF (OracleComp spec) where
--   toPMF := simulateQ fun t => PMF.uniformOfFintype (spec.range t)

-- lemma evalDist_def (oa : OracleComp spec α) : evalDist oa =
--     simulateQ (fun t => OptionT.mk (some <$> PMF.uniformOfFintype (spec.range t))) oa := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind t oa h => simp; sorry
--   -- simp [instHasEvalPMF, HasEvalPMF.instHasEvalSPMF, PMF.toSPMF, instMonad, evalDist, OptionT.mk]
--   -- rw [← PMF.monad_map_eq_map]
--   -- simp [simulateQ]
--   -- ext a
--   -- simp [OptionT.run, evalDist, OptionT.mk, simulateQ]
--   -- have aux {x y : α} : (some x = some y) = (y = x) := by aesop
--   -- conv =>
--   --   enter [1, 1, a, 1]
--   --   rw [aux]
--   -- sorry
--   -- classical
--   -- rw [tsum_ite_eq a (PFunctor.FreeM.mapM (fun t ↦ PMF.uniformOfFintype (spec.range t)) oa)]

-- @[simp] lemma evalDist_query (t : spec.domain) :
--     evalDist (query t) = OptionT.mk (some <$> PMF.uniformOfFintype (spec.range t)) := by
--   simp [evalDist_def]

-- lemma toPMF_def (oa : OracleComp spec α) : toPMF oa =
--     simulateQ (fun t => PMF.uniformOfFintype (spec.range t)) oa := rfl

-- @[simp] lemma toPMF_query (t : spec.domain) :
--     toPMF (query t) = PMF.uniformOfFintype (spec.range t) := by simp [toPMF_def]

-- section finSupport

-- open Classical -- We need decidable equality for the `finset` binds
-- -- dtumad: could avoid classical by instead having [DecidableEq] instance?

-- protected noncomputable instance finSupport [spec.Fintype] [spec.Inhabited] :
--     HasEvalFinsupport (OracleComp spec) where
--   finSupport oa := OracleComp.construct (fun x => {x}) (fun t oa r => Finset.univ.biUnion r) oa
--   mem_finSupport_iff oa x := by
--     induction oa using OracleComp.inductionOn with
--     | pure x => simp
--     | query_bind t my h => simp [h]

-- lemma finSupport_def (oa : OracleComp spec α) : finSupport oa =
--     OracleComp.construct (fun x => {x}) (fun _ _ r => Finset.univ.biUnion r) oa := rfl

-- @[simp] lemma finSupport_query (t : spec.domain) :
--     finSupport (query t) = Finset.univ := by simp [finSupport_def]

-- end finSupport

-- end instances

-- section lift

-- @[simp] lemma support_lift (q : spec α) :
--     support (m := OracleComp spec) (PFunctor.FreeM.lift q) = Set.range q.2 := by
--   simp [support_def, SetM.run]

-- @[simp] lemma support_liftA (t : spec.domain) :
--     support (m := OracleComp spec) (PFunctor.FreeM.liftA t) = Set.univ := by
--   simp [PFunctor.FreeM.liftA, support_def, SetM.run]
--   exact Set.iUnion_of_singleton (spec.B t)

-- lemma support_liftM (q : spec α) :
--     support (liftM q : OracleComp spec α) = Set.range q.2 := by simp

-- variable [spec.Fintype] [spec.Inhabited]

-- @[simp] lemma evalDist_lift (q : spec α) :
--     evalDist (m := OracleComp spec) (PFunctor.FreeM.lift q) =
--       q.2 <$> OptionT.mk (some <$> PMF.uniformOfFintype (spec.range q.1)) := by
--   simp [evalDist_def]

-- @[simp] lemma evalDist_liftA (t : spec.domain) :
--     evalDist (m := OracleComp spec) (PFunctor.FreeM.liftA t) =
--       OptionT.mk (some <$> PMF.uniformOfFintype (spec.range t)) := by
--   simp [evalDist_def]

-- lemma evalDist_liftM (q : spec α) :
--     evalDist (liftM q : OracleComp spec α) =
--       q.2 <$> OptionT.mk (some <$> PMF.uniformOfFintype (spec.range q.1)) := by simp

-- end lift

-- section uniform

-- @[simp] lemma support_coin : support coin = {true, false} := by
--   rw [coin_def, support_query]
--   simp [Set.ext_iff]

-- @[simp] lemma support_uniformFin (n : ℕ) : support $[0..n] = Set.univ := by
--   simp [uniformFin_def]
--   rw [support_query]

-- end uniform

-- lemma evalDist_query_bind [spec.Fintype] [spec.Inhabited]
--     (t : spec.domain) (ou : spec.range t → OracleComp spec α) :
--     evalDist ((query t : OracleComp spec _) >>= ou) =
--       (OptionT.lift (PMF.uniformOfFintype (spec.range t))) >>= (evalDist ∘ ou) := by
--   rw [evalDist_bind, evalDist_query]
--   rfl

-- @[simp]
-- lemma evalDist_coin : evalDist coin = OptionT.lift (PMF.uniformOfFintype Bool) := by
--   rw [coin, evalDist_query]
--   rfl

-- @[simp]
-- lemma evalDist_uniformFin (n : ℕ) :
--     evalDist $[0..n] = OptionT.lift (PMF.uniformOfFintype (Fin (n + 1))) := by
--   rw [uniformFin, evalDist_query]
--   rfl

section support

-- -- TODO: maybe these should be implicit for some lemmas
-- variable [spec.Fintype] [spec.Inhabited] (oa : OracleComp spec α) (x : α) (p q : α → Prop)

-- /-- An output has non-zero probability iff it is in the `support` of the computation. -/
-- @[simp]
-- lemma mem_support_evalDist_iff :
--     some x ∈ support (evalDist oa).run ↔ x ∈ support oa := by
--   induction oa using OracleComp.inductionOn with
--   -- Should think about better simp pathways here
--   | pure a => simp [PMF.instHasEvalSet, PMF.pure, support, SetM.run, DFunLike.coe]
--   | query_bind t oa hoa => simp [hoa, OptionT.lift, elimM]; sorry

-- alias ⟨mem_support_of_mem_support_evalDist, mem_support_evalDist⟩ := mem_support_evalDist_iff

-- /-- An output has non-zero probability iff it is in the `finSupport` of the computation. -/
-- @[simp]
-- lemma mem_support_evalDist_iff' [DecidableEq α]
--     (oa : OracleComp spec α) (x : α) :
--     some x ∈ (evalDist oa).run.support ↔ x ∈ finSupport oa := by sorry
-- --   rw [mem_support_evalDist_iff, mem_finSupport_iff_mem_support]
-- -- alias ⟨mem_finSupport_of_mem_support_evalDist, mem_support_evalDist'⟩ := mem_support_evalDist_iff'

-- @[simp]
-- lemma evalDist_apply_eq_zero_iff (x : Option α) :
--     (evalDist oa).run x = 0 ↔ x.rec (Pr[⊥ | oa] = 0) (· ∉ support oa) :=
--   match x with
--   | none => by simp [probFailure_def]
--   | some x => by simp [OptionT.run, ← mem_support_evalDist_iff]; sorry

-- @[simp]
-- lemma evalDist_apply_eq_zero_iff' [spec.DecidableEq] [DecidableEq α] (x : Option α) :
--     (evalDist oa).run x = 0 ↔ x.rec ([⊥ | oa] = 0) (· ∉ oa.finSupport) := by
--   cases x <;> simp [mem_finSupport_iff_mem_support]

-- /-- The support of `evalDist oa` is exactly `support oa`. -/
-- lemma support_evalDist : (evalDist oa).run.support = if [⊥ | oa] = 0 then
--     some '' oa.support else insert none (some '' oa.support) := by
--   rw [probFailure_def]
--   refine Set.ext (λ x ↦ x.rec ?_ ?_)
--   · split_ifs with h <;> simp [h]
--   · split_ifs <;> simp

-- lemma support_evalDist' [spec.DecidableEq] [DecidableEq α] :
--     (evalDist oa).run.support = if [⊥ | oa] = 0 then
--       oa.finSupport.image some else insert none (oa.finSupport.image some) := by
--   rw [support_evalDist]
--   split_ifs with h <;> simp only [Finset.coe_insert, Finset.coe_image, coe_finSupport]

-- @[simp low]
-- lemma probEvent_eq_zero_iff : [p | oa] = 0 ↔ ∀ x ∈ oa.support, ¬ p x := by
--   rw [probEvent_def, PMF.toOuterMeasure_apply_eq_zero_iff]
--   simp [Set.disjoint_iff_forall_ne, Option.forall]
--   refine forall_congr' λ x ↦ forall_congr' λ hx ↦ ?_
--   refine ⟨λ h hx ↦ h x hx rfl, λ h y hy hxy ↦ h (hxy ▸ hy)⟩
-- alias ⟨not_of_mem_support_of_probEvent_eq_zero, probEvent_eq_zero⟩ := probEvent_eq_zero_iff
-- @[simp low]
-- lemma zero_eq_probEvent_iff : 0 = [p | oa] ↔ ∀ x ∈ oa.support, ¬ p x := by
--   rw [eq_comm, probEvent_eq_zero_iff]
-- alias ⟨_, zero_eq_probEvent⟩ := zero_eq_probEvent_iff

-- @[simp]
-- lemma probEvent_eq_zero_iff' [spec.DecidableEq] [DecidableEq α] :
--     [p | oa] = 0 ↔ ∀ x ∈ oa.finSupport, ¬ p x := by
--   simp only [probEvent_eq_zero_iff, mem_finSupport_iff_mem_support]
-- alias ⟨not_of_mem_finSupport_of_probEvent_eq_zero, probEvent_eq_zero'⟩ := probEvent_eq_zero_iff'
-- @[simp]
-- lemma zero_eq_probEvent_iff' [spec.DecidableEq] [DecidableEq α] :
--     0 = [p | oa] ↔ ∀ x ∈ oa.finSupport, ¬ p x := by
--   rw [eq_comm, probEvent_eq_zero_iff']
-- alias ⟨_, zero_eq_probEvent'⟩ := zero_eq_probEvent_iff'

-- @[simp low]
-- lemma probOutput_pos_iff : 0 < [= x | oa] ↔ x ∈ oa.support := by
--   rw [pos_iff_ne_zero, ne_eq, probOutput_eq_zero_iff, not_not]
-- alias ⟨mem_support_of_probOutput_pos, probOutput_pos⟩ := probOutput_pos_iff

-- @[simp]
-- lemma probOutput_pos_iff' [spec.DecidableEq] [DecidableEq α] :
--     0 < [= x | oa] ↔ x ∈ oa.finSupport := by
--   rw [probOutput_pos_iff, mem_finSupport_iff_mem_support]
-- alias ⟨mem_finSupport_of_probOutput_pos, probOutput_pos'⟩ := probOutput_pos_iff'

-- @[simp low]
-- lemma probEvent_pos_iff : 0 < [p | oa] ↔ ∃ x ∈ oa.support, p x := by
--   simp_rw [pos_iff_ne_zero, ne_eq, probEvent_eq_zero_iff, not_forall, not_not, exists_prop]
-- alias ⟨exists_mem_support_of_probEvent_pos, probEvent_pos⟩ := probEvent_pos_iff

-- @[simp]
-- lemma probEvent_pos_iff' [spec.DecidableEq] [DecidableEq α] :
--     0 < [p | oa] ↔ ∃ x ∈ oa.finSupport, p x := by
--   simp_rw [pos_iff_ne_zero, ne_eq, probEvent_eq_zero_iff', not_forall, not_not, exists_prop]
-- alias ⟨exists_mem_finSupport_of_probEvent_pos, probEvent_pos'⟩ := probEvent_pos_iff'

-- @[simp low]
-- lemma probOutput_eq_one_iff :
--     [= x | oa] = 1 ↔ [⊥ | oa] = 0 ∧ oa.support = {x} := by
--   simp [probOutput_def, PMF.apply_eq_one_iff, Set.ext_iff, Option.forall]
-- alias ⟨_, probOutput_eq_one⟩ := probOutput_eq_one_iff
-- @[simp low]
-- lemma one_eq_probOutput_iff :
--     1 = [= x | oa] ↔ [⊥ | oa] = 0 ∧ oa.support = {x} := by
--   rw [eq_comm, probOutput_eq_one_iff]
-- alias ⟨_, one_eq_probOutput⟩ := one_eq_probOutput_iff

-- @[simp]
-- lemma probOutput_eq_one_iff' [spec.DecidableEq] [DecidableEq α] :
--     [= x | oa] = 1 ↔ [⊥ | oa] = 0 ∧ oa.finSupport = {x} := by
--   rw [probOutput_eq_one_iff, finSupport_eq_iff_support_eq_coe, Finset.coe_singleton]
-- alias ⟨_, probOutput_eq_one'⟩ := probOutput_eq_one_iff'
-- @[simp]
-- lemma one_eq_probOutput_iff' [spec.DecidableEq] [DecidableEq α] :
--     1 = [= x | oa] ↔ [⊥ | oa] = 0 ∧ oa.finSupport = {x} := by
--   rw [eq_comm, probOutput_eq_one_iff']
-- alias ⟨_, one_eq_probOutput'⟩ := one_eq_probOutput_iff'

-- @[simp low]
-- lemma probEvent_eq_one_iff : [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x := by
--   rw [probEvent, PMF.toOuterMeasure_apply_eq_one_iff]
--   simp [support_evalDist]
--   split_ifs with hoa
--   · simp [hoa, Set.preimage_image_eq _ (some_injective α), Set.subset_def]
--   · simp [hoa]
--     intro h
--     specialize h (Set.mem_insert none _)
--     simp at h
-- alias ⟨_, probEvent_eq_one⟩ := probEvent_eq_one_iff
-- @[simp low]
-- lemma one_eq_probEvent_iff : 1 = [p | oa] ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x := by
--   rw [eq_comm, probEvent_eq_one_iff]
-- alias ⟨_, one_eq_probEvent⟩ := probEvent_eq_one_iff

-- @[simp]
-- lemma probEvent_eq_one_iff' [spec.DecidableEq] [DecidableEq α] :
--     [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.finSupport, p x := by
--   simp_rw [probEvent_eq_one_iff, mem_finSupport_iff_mem_support]
-- alias ⟨_, probEvent_eq_one'⟩ := probEvent_eq_one_iff'
-- @[simp]
-- lemma one_eq_probEvent_iff' [spec.DecidableEq] [DecidableEq α] :
--     1 = [p | oa] ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.finSupport, p x := by
--   rw [eq_comm, probEvent_eq_one_iff']
-- alias ⟨_, one_eq_probEvent'⟩ := one_eq_probEvent_iff'

-- lemma mem_support_iff_probOutput_ne_zero : x ∈ oa.support ↔ [= x | oa] ≠ 0 := by
--   simp only [ne_eq, probOutput_eq_zero_iff, not_not]
-- lemma mem_finSupport_iff_probOutput_ne_zero [spec.DecidableEq] [DecidableEq α] :
--     x ∈ oa.finSupport ↔ [= x | oa] ≠ 0 := by
--   rw [mem_finSupport_iff_mem_support, mem_support_iff_probOutput_ne_zero]

-- lemma mem_support_iff_probOutput_pos : x ∈ oa.support ↔ 0 < [= x | oa] := by
--   simp only [probOutput_pos_iff]

-- lemma not_mem_support_iff_probOutput_eq_zero : x ∉ oa.support ↔ [= x | oa] = 0 := by
--   simp only [probOutput_eq_zero_iff]

-- variable {oa x p q}

-- /-- If `p` implies `q` on the `support` of a computation then it is more likely to happen. -/
-- lemma probEvent_mono (h : ∀ x ∈ oa.support, p x → q x) : [p | oa] ≤ [q | oa] := by
--   refine PMF.toOuterMeasure_mono _ λ x hx ↦ match x with
--   | none => by simp at hx
--   | some x => by
--       simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, some.injEq, exists_eq_right,
--         PMF.mem_support_iff, ne_eq, evalDist_apply_eq_zero_iff, not_not] at hx
--       exact ⟨x, h x hx.2 hx.1, rfl⟩

-- /-- If `p` implies `q` on the `finSupport` of a computation then it is more likely to happen. -/
-- lemma probEvent_mono' [spec.DecidableEq] [DecidableEq α]
--     (h : ∀ x ∈ oa.finSupport, p x → q x) : [p | oa] ≤ [q | oa] :=
--   probEvent_mono (λ x hx hpx ↦ h x (mem_finSupport_of_mem_support oa hx) hpx)

-- -- NOTE: should allow `p` and `q` to differ outside the shared support.
-- lemma probEvent_congr {oa : OracleComp spec α} {oa' : OracleComp spec' α}
--     (h1 : ∀ x, p x ↔ q x) (h2 : evalDist oa = evalDist oa') : [p | oa] = [q | oa'] := by
--   simp only [probEvent, probOutput, h1, h2]

-- lemma probEvent_ext (h : ∀ x ∈ oa.support, p x ↔ q x) : [p | oa] = [q | oa] :=
--   le_antisymm (probEvent_mono <| λ x hx hp ↦ (h x hx).1 hp)
--     (probEvent_mono <| λ x hx hp ↦ (h x hx).2 hp)

-- lemma probEvent_ext' [spec.DecidableEq] [DecidableEq α]
--     (h : ∀ x ∈ oa.finSupport, p x ↔ q x) : [p | oa] = [q | oa] :=
--   le_antisymm (probEvent_mono' <| λ x hx hp ↦ (h x hx).1 hp)
--     (probEvent_mono' <| λ x hx hp ↦ (h x hx).2 hp)

-- @[simp]
-- lemma function_support_probOutput : Function.support ([= · | oa]) = oa.support := by
--   simp only [Function.support, ne_eq, probOutput_eq_zero_iff, not_not, Set.setOf_mem_eq]

-- lemma mem_support_iff_of_evalDist_eq {oa : OracleComp spec α} {oa' : OracleComp spec' α}
--     (h : evalDist oa = evalDist oa') (x : α) : x ∈ oa.support ↔ x ∈ oa'.support := by
--   simp only [mem_support_iff_probOutput_ne_zero, probOutput_def, h]

-- lemma mem_finSupport_iff_of_evalDist_eq [spec.DecidableEq] [spec'.DecidableEq]
--     [DecidableEq α] {oa : OracleComp spec α} {oa' : OracleComp spec' α}
--     (h : evalDist oa = evalDist oa') (x : α) : x ∈ oa.finSupport ↔ x ∈ oa'.finSupport := by
--   simp only [mem_finSupport_iff_mem_support, mem_support_iff_of_evalDist_eq h]

end support

-- @[simp] lemma probEvent_eq_eq_probOutput (oa : OracleComp spec α) (x : α) :
--     [(· = x) | oa] = [= x | oa] := by
--   simp [probEvent_def, PMF.toOuterMeasure_apply_singleton, evalDist_apply_some]

-- @[simp] lemma probEvent_eq_eq_probOutput' (oa : OracleComp spec α) (x : α) :
--     [(x = ·) | oa] = [= x | oa] :=
--   (probEvent_congr (λ _ ↦ eq_comm) rfl).trans (probEvent_eq_eq_probOutput oa x)

-- section sums

-- variable (oa : OracleComp spec α) (p : α → Prop)

-- /-- The probability of an event written as a sum over the set `{x | p x}` viewed as a subtype.
-- This notably doesn't require decidability of the predicate `p` unlike many other lemmas. -/
-- lemma probEvent_eq_tsum_subtype : [p | oa] = ∑' x : {x | p x}, [= x | oa] := by
--   rw [probEvent_eq_tsum_indicator, tsum_subtype]

-- /-- Version `probEvent_eq_tsum_subtype` that preemptively filters out elements that
-- aren't in the support, since they will have no mass contribution anyways.
-- This can make some proofs simpler by handling things on the level of subtypes. -/
-- lemma probEvent_eq_tsum_subtype_mem_support :
--     [p | oa] = ∑' x : {x ∈ oa.support | p x}, [= x | oa] := by
--   simp_rw [probEvent_eq_tsum_subtype, tsum_subtype]
--   refine tsum_congr (λ x ↦ ?_)
--   by_cases hpx : p x
--   · refine (if_pos hpx).trans ?_
--     by_cases hx : x ∈ oa.support
--     · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_self, ↓reduceIte]
--     · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_true, ↓reduceIte,
--       probOutput_eq_zero_iff, not_false_eq_true]
--   · exact (if_neg hpx).trans (by simp [Set.indicator, hpx])

-- lemma probEvent_eq_tsum_subtype_support_ite [DecidablePred p] :
--     [p | oa] = ∑' x : oa.support, if p x then [= x | oa] else 0 :=
-- calc
--   [p | oa] = (∑' x, if p x then [= x | oa] else 0) := by rw [probEvent_eq_tsum_ite oa p]
--   _ = ∑' x, oa.support.indicator (λ x ↦ if p x then [= x | oa] else 0) x := by
--     refine tsum_congr (λ x ↦ ?_)
--     unfold Set.indicator
--     split_ifs with h1 h2 h2 <;> simp [h1, h2]
--   _ = ∑' x : oa.support, if p x then [= x | oa] else 0 := by
--     rw [tsum_subtype (support oa) (λ x ↦ if p x then [= x | oa] else 0)]

-- lemma probEvent_eq_sum_fintype_indicator [Fintype α] (oa : OracleComp spec α) (p : α → Prop) :
--     [p | oa] = ∑ x : α, {x | p x}.indicator ([= · | oa]) x :=
--   (probEvent_eq_tsum_indicator oa p).trans (tsum_fintype _)

-- lemma probEvent_eq_sum_fintype_ite [DecidablePred p] [Fintype α] :
--     [p | oa] = ∑ x : α, if p x then [= x | oa] else 0 :=
--   (probEvent_eq_tsum_ite oa p).trans (tsum_fintype _)

-- lemma probEvent_eq_sum_filter_univ [DecidablePred p] [Fintype α] :
--     [p | oa] = ∑ x ∈ Finset.univ.filter p, [= x | oa] := by
--   rw [probEvent_eq_sum_fintype_ite, Finset.sum_filter]

-- lemma probEvent_eq_sum_filter_finSupport [spec.DecidableEq] [DecidablePred p] [DecidableEq α] :
--     [p | oa] = ∑ x ∈ oa.finSupport.filter p, [= x | oa] :=
--   (probEvent_eq_tsum_ite oa p).trans <|
--     (tsum_eq_sum' <| by simp; tauto).trans
--       (Finset.sum_congr rfl <| λ x hx ↦ if_pos (Finset.mem_filter.1 hx).2)

-- lemma probEvent_eq_sum_finSupport_ite [spec.DecidableEq] [DecidablePred p] [DecidableEq α] :
--     [p | oa] = ∑ x ∈ oa.finSupport, if p x then [= x | oa] else 0 := by
--   rw [probEvent_eq_sum_filter_finSupport, Finset.sum_filter]

-- end sums

-- lemma probOutput_congr {x y : α} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
--     (h1 : x = y) (h2 : evalDist oa = evalDist oa') : [= x | oa] = [= y | oa'] := by
--   simp_rw [probOutput, h1, h2]

-- lemma probEvent_congr' {p q : α → Prop} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
--     (h1 : ∀ x, x ∈ oa.support → x ∈ oa'.support → (p x ↔ q x))
--     (h2 : evalDist oa = evalDist oa') : [p | oa] = [q | oa'] := by
--   have h : ∀ x, x ∈ oa.support ↔ x ∈ oa'.support := mem_support_iff_of_evalDist_eq h2
--   have h' : ∀ x, [= x | oa] = [= x | oa'] := λ x ↦ probOutput_congr rfl h2
--   rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator]
--   refine tsum_congr λ x ↦ ?_
--   simp [Set.indicator, h']
--   by_cases hp : p x
--   · by_cases hq : q x
--     · simp [hp, hq]
--     · simp [hp, hq, h]
--       refine λ hoa ↦ hq ?_
--       refine (h1 _ ?_ hoa).1 hp
--       refine (h _).2 hoa
--   · by_cases hq : q x
--     · simp [hp, hq]
--       simp [h] at h1
--       intro hoa
--       specialize h1 _ hoa
--       tauto
--     · rw [if_neg hp, if_neg hq]


-- @[simp] lemma probEvent_const (oa : OracleComp spec α) (p : Prop) [Decidable p] :
--     [λ _ ↦ p | oa] = if p then 1 - [⊥ | oa] else 0 := by
--   rw [probEvent_eq_tsum_ite]
--   split_ifs with hp <;> simp [hp, tsum_probOutput_eq_sub]

-- lemma probEvent_true (oa : OracleComp spec α) : [λ _ ↦ true | oa] = 1 - [⊥ | oa] := by simp
-- lemma probEvent_false (oa : OracleComp spec α) : [λ _ ↦ false | oa] = 0 := by simp

-- lemma probFailure_eq_sub_probEvent (oa : OracleComp spec α) :
--     [⊥ | oa] = 1 - [λ _ ↦ true | oa] := by
--   rw [probEvent_true, ENNReal.sub_sub_cancel one_ne_top probFailure_le_one]

-- lemma evalDist_ext_probEvent {oa : OracleComp spec α} {oa' : OracleComp spec' α}
--     (h : ∀ x, [= x | oa] = [= x | oa']) : (evalDist oa).run = (evalDist oa').run :=
--   PMF.ext λ x ↦ match x with
--   | none => by simp [← probFailure_def, probFailure_eq_sub_tsum, h]
--   | some x => h x

-- section pure

-- variable (x : α)

-- @[simp]
-- lemma probOutput_pure [DecidableEq α] (y : α) :
--     [= y | (pure x : OracleComp spec α)] = if y = x then 1 else 0 := by
--   simp [probOutput]

-- @[simp]
-- lemma probFailure_pure : [⊥ | (pure x : OracleComp spec α)] = 0 := by
--   simp [probFailure]

-- lemma probOutput_pure_eq_zero {x y : α} (h : y ≠ x) :
--     [= y | (pure x : OracleComp spec α)] = 0 := by simpa using h

-- lemma probOutput_pure_eq_one {x y : α} (h : y = x) :
--     [= y | (pure x : OracleComp spec α)] = 1 := by simpa using h.symm

-- @[simp]
-- lemma probOutput_pure_self (x : α) : [= x | (pure x : OracleComp spec α)] = 1 := by simp

-- @[simp]
-- lemma probOutput_pure_subsingleton [Subsingleton α] (x y : α) :
--     [= x | (pure y : OracleComp spec α)] = 1 := by
--   simp [Subsingleton.elim x y]

-- @[simp]
-- lemma probEvent_pure (p : α → Prop) [DecidablePred p] :
--     [p | (pure x : OracleComp spec α)] = if p x then 1 else 0 := by
--   simp [probEvent_eq_tsum_ite]
--   refine (tsum_eq_single x (by simp; tauto)).trans (by simp)

-- lemma probEvent_pure_eq_zero {p : α → Prop} {x : α} (h : ¬ p x) :
--     [p | (pure x : OracleComp spec α)] = 0 := by simpa

-- lemma probEvent_pure_eq_one {p : α → Prop} {x : α} (h : p x) :
--     [p | (pure x : OracleComp spec α)] = 1 := by simpa

-- end pure

-- section bind

-- variable (oa : OracleComp spec α) (ob : α → OracleComp spec β)

-- end bind

-- section mul_le_probEvent_bind

-- lemma mul_le_probEvent_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--     {p : α → Prop} {q : β → Prop} {r r' : ℝ≥0∞}
--     (h : r ≤ [p | oa]) (h' : ∀ x ∈ oa.support, p x → r' ≤ [q | ob x]) :
--     r * r' ≤ [q | oa >>= ob] := by
--   rw [probEvent_bind_eq_tsum]
--   refine (mul_le_mul_right' h r').trans ?_
--   rw [probEvent_eq_tsum_indicator, ← ENNReal.tsum_mul_right]
--   refine ENNReal.tsum_le_tsum fun x => ?_
--   rw [← Set.indicator_mul_const]
--   by_cases hx : x ∈ oa.support
--   · refine Set.indicator_apply_le' (fun h => ?_) (fun _ => zero_le')
--     exact (ENNReal.mul_le_mul_left (probOutput_ne_zero _ _ hx) probOutput_ne_top).mpr (h' x hx h)
--   · simp [probOutput_eq_zero _ _ hx]

-- end mul_le_probEvent_bind

-- section bind_const

-- variable (oa : OracleComp spec α) (ob : OracleComp spec β)

-- -- lemma probFailure_bind_const :
-- --   [⊥ | do oa; ob] = [⊥ | oa] + [⊥ | ob] - [⊥ | oa] * [⊥ | ob]


-- end bind_const

-- section query

-- variable (i : ι) (t : spec.domain i)

-- @[simp]
-- lemma probOutput_liftM [Fintype α] (q : OracleQuery spec α) (u : α) :
--     [= u | (q : OracleComp spec α)] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
--   have : Inhabited α := q.rangeInhabited
--   simp [probOutput, PMF.monad_map_eq_map, OptionT.lift]
--   refine (tsum_eq_single u ?_).trans ?_
--   · simp [not_imp_not]
--   · simp only [↓reduceIte, inv_inj, Nat.cast_inj]

-- lemma probOutput_query (u : spec.range i) :
--     [= u | (query i t : OracleComp spec _)] = (Fintype.card (spec.range i) : ℝ≥0∞)⁻¹ := by
--   rw [probOutput_liftM]

-- @[simp]
-- lemma probFailure_liftM (q : OracleQuery spec α) :
--     [⊥ | (q : OracleComp spec _)] = 0 := by
--   have : Fintype α := q.rangeFintype
--   have : Inhabited α := q.rangeInhabited
--   simp only [probFailure, evalDist_liftM]
--   erw [PMF.bind_apply]
--   simp only [PMF.uniformOfFintype_apply, ENNReal.tsum_eq_zero, mul_eq_zero, ENNReal.inv_eq_zero,
--     natCast_ne_top, false_or]
--   intro i
--   erw [PMF.pure_apply]
--   simp

-- lemma probFailure_query : [⊥ | (query i t : OracleComp spec _)] = 0 := by
--   rw [probFailure_liftM]

-- @[simp]
-- lemma probEvent_liftM_eq_mul_inv [Fintype α] (q : OracleQuery spec α)
--     (p : α → Prop) [DecidablePred p] : [p | (q : OracleComp spec _)] =
--       (Finset.univ.filter p).card * (↑(Fintype.card α))⁻¹ := by
--   simp [probEvent_eq_sum_fintype_ite]

-- lemma probEvent_query_eq_mul_inv (p : spec.range i → Prop) [DecidablePred p] :
--     [p | (query i t : OracleComp spec _)] =
--       (Finset.univ.filter p).card * (↑(Fintype.card (spec.range i)))⁻¹ := by
--   rw [probEvent_liftM_eq_mul_inv]

-- lemma probEvent_liftM_eq_inv_mul [Fintype α] (q : OracleQuery spec α)
--     (p : α → Prop) [DecidablePred p] : [p | (q : OracleComp spec _)] =
--       (↑(Fintype.card α))⁻¹ * (Finset.univ.filter p).card := by
--   rw [probEvent_liftM_eq_mul_inv, mul_comm]

-- lemma probEvent_query_eq_inv_mul [spec.DecidableEq] (p : spec.range i → Prop) [DecidablePred p] :
--     [p | (query i t : OracleComp spec _)] =
--       (↑(Fintype.card (spec.range i)))⁻¹ * (Finset.univ.filter p).card := by
--   rw [probEvent_query_eq_mul_inv, mul_comm]

-- lemma probEvent_liftM_eq_div [Fintype α] (q : OracleQuery spec α)
--     (p : α → Prop) [DecidablePred p] : [p | (q : OracleComp spec _)] =
--       (Finset.univ.filter p).card / (Fintype.card α) := by
--   rw [div_eq_mul_inv, probEvent_liftM_eq_mul_inv]

-- lemma probEvent_query_eq_div [spec.DecidableEq] (p : spec.range i → Prop) [DecidablePred p] :
--     [p | (query i t : OracleComp spec _)] =
--       (Finset.univ.filter p).card / (Fintype.card (spec.range i)) := by
--   rw [probEvent_liftM_eq_div]

-- end query

-- section failure

-- @[simp]
-- lemma probOutput_failure (x : α) : [= x | (failure : OracleComp spec α)] = 0 := by simp

-- @[simp]
-- lemma probFailure_failure : [⊥ | (failure : OracleComp spec α)] = 1 := by simp [probFailure]

-- @[simp]
-- lemma probEvent_failure (p : α → Prop) :
--     [p | (failure : OracleComp spec α)] = 0 := by simp

-- end failure

-- section map

-- variable (oa : OracleComp spec α) (f : α → β)

-- /-- Write the probability of an output after mapping the result of a computation as a sum
-- over all outputs such that they map to the correct final output, using subtypes.
-- This lemma notably doesn't require decidable equality on the final type, unlike most
-- lemmas about probability when mapping a computation. -/
-- lemma probOutput_map_eq_tsum_subtype (y : β) :
--     [= y | f <$> oa] = ∑' x : {x ∈ oa.support | y = f x}, [= x | oa] := by
--   simp only [map_eq_bind_pure_comp, tsum_subtype _ (λ x ↦ [= x | oa]), probOutput_bind_eq_tsum,
--     Function.comp_apply, probOutput_pure, mul_ite, mul_one, mul_zero,
--     Set.indicator, Set.mem_setOf_eq]
--   refine (tsum_congr (λ x ↦ ?_))
--   by_cases hy : y = f x <;> by_cases hx : x ∈ oa.support <;> simp [hy, hx]

-- lemma probOutput_map_eq_tsum (y : β) :
--     [= y | f <$> oa] = ∑' x, [= x | oa] * [= y | (pure (f x) : OracleComp spec β)] := by
--   simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply]

-- lemma probOutput_map_eq_tsum_subtype_ite [DecidableEq β] (y : β) :
--     [= y | f <$> oa] = ∑' x : oa.support, if y = f x then [= x | oa] else 0 := by
--   simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum_subtype, Function.comp_apply,
--     probOutput_pure, mul_ite, mul_one, mul_zero]

-- lemma probOutput_map_eq_tsum_ite [DecidableEq β] (y : β) :
--     [= y | f <$> oa] = ∑' x : α, if y = f x then [= x | oa] else 0 := by
--   simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply, probOutput_pure,
--     mul_ite, mul_one, mul_zero]

-- lemma probOutput_map_eq_sum_fintype_ite [Fintype α] [DecidableEq β] (y : β) :
--     [= y | f <$> oa] = ∑ x : α, if y = f x then [= x | oa] else 0 :=
--   (probOutput_map_eq_tsum_ite oa f y).trans (tsum_eq_sum' <|
--     by simp only [Finset.coe_univ, Set.subset_univ])

-- lemma probOutput_map_eq_sum_finSupport_ite [spec.DecidableEq] [DecidableEq α] [DecidableEq β]
--     (y : β) : [= y | f <$> oa] = ∑ x ∈ oa.finSupport, if y = f x then [= x | oa] else 0 :=
--   (probOutput_map_eq_tsum_ite oa f y).trans (tsum_eq_sum' <|
--     by simp only [coe_finSupport, Function.support_subset_iff, ne_eq, ite_eq_right_iff,
--       probOutput_eq_zero_iff', mem_finSupport_iff_mem_support, Classical.not_imp, not_not, and_imp,
--       imp_self, implies_true])

-- lemma probOutput_map_eq_sum_filter_finSupport [spec.DecidableEq] [DecidableEq α] [DecidableEq β]
--     (y : β) : [= y | f <$> oa] = ∑ x ∈ oa.finSupport.filter (y = f ·), [= x | oa] := by
--   rw [Finset.sum_filter, probOutput_map_eq_sum_finSupport_ite]

-- @[simp]
-- lemma probFailure_map : [⊥ | f <$> oa] = [⊥ | oa] := by
--   simp [probFailure, evalDist_map, PMF.map_apply, PMF.monad_map_eq_map]
--   refine (tsum_eq_single none λ x ↦ ?_).trans (if_pos rfl)
--   cases x <;> simp

-- @[simp]
-- lemma probEvent_map (q : β → Prop) : [q | f <$> oa] = [q ∘ f | oa] := by
--   simp only [probEvent, evalDist_map, PMF.toOuterMeasure_map_apply, Function.comp_apply]
--   simp [PMF.monad_map_eq_map]
--   refine congr_arg (oa.evalDist.toOuterMeasure) ?_
--   simp only [Set.preimage, Set.mem_image, Set.mem_setOf_eq, Set.ext_iff]
--   intro x
--   cases x <;> simp
-- lemma probEvent_comp (q : β → Prop) : [q ∘ f | oa] = [q | f <$> oa] :=
--   symm <| probEvent_map oa f q

-- lemma probOutput_map_eq_probOutput_inverse (f : α → β) (g : β → α)
--     (hl : Function.LeftInverse f g) (hr : Function.RightInverse f g)
--     (y : β) : [= y | f <$> oa] = [= g y | oa] := by
--   rw [probOutput_map_eq_tsum]
--   refine (tsum_eq_single (g y) (λ x hx ↦ ?_)).trans ?_
--   · suffices y ≠ f x by simp [this]
--     exact (λ h ↦ hx ((congr_arg g h).trans (hr x)).symm)
--   · simp [hl y]

-- lemma probFailure_eq_sub_sum_probOutput_map [Fintype β] (oa : OracleComp spec α) (f : α → β) :
--     [⊥ | oa] = 1 - ∑ y : β, [= y | f <$> oa] := by
--   rw [← probFailure_map (f := f), probFailure_eq_sub_tsum, tsum_fintype]

-- end map

-- section NeverFail

-- -- TODO: expand api and include `mayFail` versions for `probFailure_pos`.

-- @[simp]
-- lemma probFailure_eq_zero_iff (oa : OracleComp spec α) : [⊥ | oa] = 0 ↔ oa.NeverFail := by
--   sorry
--   -- induction oa using OracleComp.inductionOn with
--   -- | pure x => simp
--   -- | failure => simp
--   -- | query_bind i t oa h => simp [probFailure_bind_eq_tsum, h]

-- @[simp]
-- lemma probFailure_pos_iff (oa : OracleComp spec α) : 0 < [⊥ | oa] ↔ ¬ oa.NeverFail := by
--   sorry --rw [pos_iff_ne_zero, ne_eq, probFailure_eq_zero_iff]

-- lemma noFailure_of_probFailure_eq_zero {oa : OracleComp spec α} (h : [⊥ | oa] = 0) :
--     NeverFail oa := by rwa [← probFailure_eq_zero_iff]

-- lemma not_noFailure_of_probFailure_pos {oa : OracleComp spec α} (h : 0 < [⊥ | oa]) :
--     ¬ NeverFail oa := by rwa [← probFailure_pos_iff]

-- end NeverFail

-- section unit

-- @[simp]
-- lemma probOutput_guard {p : Prop} [Decidable p] :
--     [= () | (guard p : OracleComp spec _)] = if p then 1 else 0 := by
--   by_cases h : p <;> simp [h]

-- @[simp]
-- lemma probFailure_guard {p : Prop} [Decidable p] :
--     [⊥ | (guard p : OracleComp spec _)] = if p then 0 else 1 := by
--   by_cases h : p <;> simp [h]

-- lemma probOutput_eq_sub_probFailure_of_unit {oa : OracleComp spec PUnit} :
--     [= () | oa] = 1 - [⊥ | oa] := by
--   rw [probFailure_eq_sub_sum, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
--   rw [ENNReal.sub_sub_cancel (by simp) (by simp)]

-- lemma probOutput_guard_eq_sub_probOutput_guard_not {α : Type} {oa : OracleComp spec α}
--     (h : oa.NeverFail) {p : α → Prop} [DecidablePred p] :
--     [= () | do let a ← oa; guard (p a)] = 1 - [= () | do let a ← oa; guard (¬ p a)] := by
--   rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
--   simp
--   sorry

-- end unit


-- section coin

-- @[simp]
-- lemma probOutput_coin (b : Bool) : [= b | coin] = 2⁻¹ := by
--   simp only [coin, probOutput_liftM, Fintype.card_bool, Nat.cast_ofNat]

-- lemma probEvent_coin_eq_sum_subtype (p : Bool → Prop) :
--     [p | coin] = ∑' _ : {x | p x}, 2⁻¹ := by
--   simp only [probEvent_eq_tsum_subtype, Set.coe_setOf, Set.mem_setOf_eq, probOutput_coin]

-- @[simp]
-- lemma probEvent_coin (p : Bool → Prop) [DecidablePred p] : [p | coin] =
--     if p true then (if p false then 1 else 2⁻¹) else (if p false then 2⁻¹ else 0) := by
--   by_cases hpt : p true <;> by_cases hpf : p false <;>
--     simp [probEvent, tsum_bool, hpt, hpf, inv_two_add_inv_two, PMF.monad_map_eq_map, OptionT.lift]

-- lemma probEvent_coin_eq_add (p : Bool → Prop) [DecidablePred p] :
--     [p | coin] = (if p true then 2⁻¹ else 0) + (if p false then 2⁻¹ else 0) := by
--   rw [probEvent_coin]; split_ifs <;> simp [inv_two_add_inv_two, PMF.monad_map_eq_map]

-- -- /-- The xor of two coin flips looks like flipping a single coin -/
-- -- example (x : Bool) : [= x | do let b ← coin; let b' ← coin; return xor b b'] = [= x | coin] := by
-- --   have : (↑2 : ℝ≥0∞) ≠ ∞ := by simp
-- --   cases x <;> simp [← mul_two, mul_comm (2 : ℝ≥0∞), mul_assoc,
-- --     ENNReal.inv_mul_cancel two_ne_zero this, probOutput_bind_eq_sum_fintype]
-- --   ·

-- end coin

-- section uniformFin

-- variable (n : ℕ)

-- @[simp]
-- lemma probOutput_uniformFin (x : Fin (n + 1)) : [= x | $[0..n]] = ((n : ℝ≥0∞) + 1)⁻¹ := by
--   simp [uniformFin, probOutput_query (spec := unifSpec), OracleSpec.range]

-- @[simp]
-- lemma probFailure_uniformFin : [⊥ | $[0..n]] = 0 := probFailure_query _ _

-- @[simp]
-- lemma probEvent_uniformFin (p : Fin (n + 1) → Prop) [DecidablePred p] :
--     [p | $[0..n]] = (Finset.univ.filter p).card * (n + 1 : ℝ≥0∞)⁻¹ := by
--   simp only [probEvent_eq_sum_filter_finSupport, finSupport_uniformFin, probOutput_uniformFin,
--     Finset.sum_const, nsmul_eq_mul]

-- end uniformFin

-- /-- Example of brute forcing a probability computation by expanding terms and using `ring_nf`. -/
-- example : [⊥ | do
--     let x ←$[0..5]; let y ←$[0..3]
--     guard (x = 0); guard (y.val ≠ x.val); return ()] = 21 / 24 := by
--   -- would be nice not to need arithmetic facts
--   have : (6 : ℝ≥0∞)⁻¹ * (4 : ℝ≥0∞)⁻¹ = (24 : ℝ≥0∞)⁻¹ :=
--     by rw [← ENNReal.mul_inv (by tauto) (by tauto)]; ring_nf
--   simp [probFailure_bind_eq_sum_fintype, Fin.sum_univ_succ, Fin.succ_ne_zero,
--     div_eq_mul_inv, this]
--   ring_nf
--   rw [this]
--   ring_nf

-- section hoare

-- variable {ι : Type u} {spec : OracleSpec ι} [spec.FiniteRange] {α β γ δ : Type v}
-- /-- If pre-condition `P` holds fox `x` then `comp x` satisfies
-- post-contdition `Q` with probability at least `r`-/
-- def HoareTriple (P : α → Prop) (comp : α → OracleComp spec β)
--     (Q : β → Prop) (r : ℝ≥0∞) : Prop :=
--   ∀ x : α, P x → r ≤ [Q | comp x]

-- notation "⦃" P "⦄ " comp " ⦃" Q "⦄ " r => HoareTriple P comp Q r

-- def HoareTriple.bind {P : α → Prop} {comp₁ : α → OracleComp spec β}
--     {Q : β → Prop} {comp₂ : α → β → OracleComp spec γ} {R : γ → Prop} {r r' : ℝ≥0∞}
--     (h1 : ⦃P⦄ comp₁ ⦃Q⦄ r) (h2 : ∀ x, ⦃Q⦄ comp₂ x ⦃R⦄ r') :
--         ⦃P⦄ fun x => comp₁ x >>= comp₂ x ⦃R⦄ (r * r') := by
--   refine fun x hx => (mul_le_mul_right' (h1 x hx) r').trans ?_
--   rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_indicator, ← ENNReal.tsum_mul_right]
--   refine ENNReal.tsum_le_tsum fun y => ?_
--   rw [← Set.indicator_mul_const]
--   refine Set.indicator_apply_le' ?_ ?_
--   · exact fun hy => mul_le_mul_left' (h2 x y hy) [=y|comp₁ x]
--   · simp only [zero_le, implies_true]

-- end hoare

-- end OracleComp

-- open OracleSpec Option ENNReal BigOperators

-- universe u v w

-- namespace OracleComp

-- variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u} [hs : spec.FiniteRange]

-- /-- If `fst <$> so i (t, s)` has the same distribution as `query i t` for any state `s`,
-- Then `simulate' so` doesn't change the output distribution.
-- Stateless oracles are the most common example of this
-- TODO: move-/
-- lemma evalDist_simulate'_eq_evalDist {σ α : Type u}
--     (so : QueryImpl spec (StateT σ (OracleComp spec)))
--     (h : ∀ i t s, (evalDist ((so.impl (query i t)).run' s)) =
--       OptionT.lift (PMF.uniformOfFintype (spec.range i)))
--     (s : σ) (oa : OracleComp spec α) : evalDist ((simulateQ so oa).run' s) = evalDist oa := by
--   revert s
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa hoa => exact (λ s ↦ by
--       simp only [StateT.run'_eq] at h
--       simp [← h i t s, Function.comp_def]

--       sorry
--       )
--   | failure => intro s; simp

-- lemma probFailure_simulateQ_WriterT_eq_probFailure {ω : Type u} [Monoid ω]
--     (so : QueryImpl spec (WriterT ω (OracleComp spec)))
--     (h : ∀ {α}, ∀ q : OracleQuery spec α, [⊥ | (so.impl q).run] = 0) (oa : OracleComp spec α) :
--     [⊥ | (simulateQ so oa).run] = [⊥ | oa] := by
--   -- revert s
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | failure => simp
--   | query_bind i t oa hq => {
--     simp [probFailure_bind_eq_tsum, h, hq]
--     intro s
--     rw [ENNReal.tsum_prod']
--     refine tsum_congr fun x => ?_
--     simp [ENNReal.tsum_mul_right]
--     congr 1

--     sorry
--   }

end OracleComp
