/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.Fischlin.Completeness
public import VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Extraction
import all VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Extraction
public import VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Potential
import all VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Potential

/-!
# Fischlin supermartingale induction and knowledge soundness
-/

public section

universe u v

open OracleComp OracleSpec

namespace Fischlin

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

open ENNReal OracleComp.EvalDist

section security

variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (ρ b S : ℕ) (M : Type) [DecidableEq M]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **The generalized supermartingale induction (multi-record cells).** The induction tracks
only *relevant* records, and within a cell relevant records are separated by an abstract
challenge tag `chalOf` (`hcell`). Caching a second relevant record at an already-revealed cell
kills
the slot (`hdead_kill`); all other relevant/live cache misses are martingale reveal steps;
irrelevant and dead-slot misses leave the potential unchanged. The bound is unchanged:
`q·μ + Φ + μ`. -/
private theorem main_induction_gen {T K C : Type} [DecidableEq T]
    (relevant : T → Prop)
    (key : T → K) (coord : T → Fin ρ) (chalOf : T → C)
    (hcell : ∀ t₁ t₂, relevant t₁ → relevant t₂ → key t₁ = key t₂ → coord t₁ = coord t₂ →
      chalOf t₁ = chalOf t₂ → t₁ = t₂)
    (dead : (T →ₒ Fin (2 ^ b)).QueryCache → K → Prop)
    [∀ c, DecidablePred (dead c)]
    (hdead_mono : ∀ c (t : T) (u : Fin (2 ^ b)) k, dead c k → dead (c.cacheQuery t u) k)
    (hdead_kill : ∀ (cache : (T →ₒ Fin (2 ^ b)).QueryCache) (t t' : T) (u u' : Fin (2 ^ b)),
      relevant t → relevant t' → key t = key t' → coord t = coord t' →
      chalOf t ≠ chalOf t' → cache t' = some u' → dead (cache.cacheQuery t u) (key t))
    {α : Type} (leaf : α → (T →ₒ Fin (2 ^ b)).QueryCache → ℝ≥0∞)
    (hleaf : ∀ (a : α) cache keys st,
      INV' ρ b relevant key coord (dead cache) cache keys st →
      leaf a cache ≤ Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none))
    (oa : OracleComp (unifSpec + (T →ₒ Fin (2 ^ b))) α) :
    ∀ (q : ℕ), IsQueryBoundP oa (· matches .inr _) q →
    ∀ cache keys st, INV' ρ b relevant key coord (dead cache) cache keys st →
    expectedValue ((simulateQ (roImpl b T) oa).run cache) (fun z => leaf z.1 z.2)
      ≤ (q : ℝ≥0∞) * slotPsi ρ b S (fun _ => none)
        + Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro q _ cache keys st hINV
      rw [simulateQ_pure, StateT.run_pure, expectedValue_pure]
      exact (hleaf x cache keys st hINV).trans (add_le_add le_add_self le_rfl)
  | query_bind t mx ih =>
      intro q hq cache keys st hINV
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hrest⟩ := hq
      rw [simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      rcases t with n | s
      · -- unifSpec query: forwarded, cache unchanged, budget unchanged
        have hbud : (if (Sum.inl n : ℕ ⊕ T) matches Sum.inr _ then q - 1 else q) = q :=
          if_neg (by simp)
        rw [hbud] at hrest
        change expectedValue ((unifFwdImpl (T →ₒ Fin (2 ^ b)) n).run cache >>=
            fun p : unifSpec.Range n × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2) (fun z => leaf z.1 z.2) ≤ _
        have hrun : ((unifFwdImpl (T →ₒ Fin (2 ^ b)) n).run cache >>=
            fun p : unifSpec.Range n × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2)
            = (HasQuery.query (spec := unifSpec) (m := ProbComp) n) >>=
              fun a => (simulateQ (roImpl b T) (mx a)).run cache := by
          simp only [unifFwdImpl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
          rw [OracleComp.liftM_run_StateT, bind_assoc]
          simp only [pure_bind]
        rw [hrun]
        exact expectedValue_bind_le_of_le fun a => ih a q (hrest a) cache keys st hINV
      · -- hash query
        have hp : ((Sum.inr s : ℕ ⊕ T) matches Sum.inr _) := rfl
        have hq0 : 0 < q := hcan.resolve_left (by simp)
        have hbud : (if (Sum.inr s : ℕ ⊕ T) matches Sum.inr _ then q - 1 else q) = q - 1 :=
          if_pos hp
        rw [hbud] at hrest
        have hμ : ((q - 1 : ℕ) : ℝ≥0∞) * slotPsi ρ b S (fun _ => none)
            + slotPsi ρ b S (fun _ => none)
            = (q : ℝ≥0∞) * slotPsi ρ b S (fun _ => none) := by
          have hcast : ((q - 1 : ℕ) : ℝ≥0∞) + 1 = (q : ℝ≥0∞) := by
            exact_mod_cast Nat.succ_pred_eq_of_pos hq0
          rw [← hcast, add_mul, one_mul]
        change expectedValue ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
            fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2) (fun z => leaf z.1 z.2) ≤ _
        rcases hc : cache s with _ | u
        · -- cache miss: fresh uniform sample
          have hrun : ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
              fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
                (simulateQ (roImpl b T) (mx p.1)).run p.2)
              = ($ᵗ Fin (2 ^ b)) >>= fun u =>
                  (simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u) := by
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hc, bind_map_left]
            rfl
          rw [hrun]
          by_cases hlive : relevant s ∧ ¬ dead cache (key s) ∧ st (key s) (coord s) = none
          · -- REVEAL: relevant record at a fresh cell of a live slot — martingale step
            obtain ⟨hrel, hdd, hstn⟩ := hlive
            set μ := slotPsi ρ b S (fun _ => none) with hμdef
            set k₀ := key s with hk₀
            set i₀ := coord s with hi₀
            have hIH : ∀ u : Fin (2 ^ b),
                expectedValue ((simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u))
                    (fun z => leaf z.1 z.2)
                  ≤ ((q - 1 : ℕ) : ℝ≥0∞) * μ
                    + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache) + μ := by
              intro u
              refine (ih u (q - 1) (hrest u) (cache.cacheQuery s u) (insert k₀ keys)
                (updateSlot st k₀ i₀ u)
                (hINV.cacheQuery_reveal (hdead_mono cache s u) s hc hrel hstn u)).trans ?_
              gcongr
              exact Phi_mono_dead ρ b S _ _ _ _ (hdead_mono cache s u)
            rw [expectedValue_bind]
            calc expectedValue ($ᵗ Fin (2 ^ b)) (fun u =>
                    expectedValue ((simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u))
                      (fun z => leaf z.1 z.2))
                ≤ expectedValue ($ᵗ Fin (2 ^ b)) (fun u =>
                    ((q - 1 : ℕ) : ℝ≥0∞) * μ
                      + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache) + μ) :=
                  expectedValue_mono _ hIH
              _ = ∑ u : Fin (2 ^ b), ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
                    * (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ
                      + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache)) := by
                  rw [expectedValue_def, tsum_fintype]
                  refine Finset.sum_congr rfl fun u _ => ?_
                  rw [probOutput_uniformSample, Fintype.card_fin, add_right_comm]
              _ = ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
                    * ((2 ^ b) • (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ)
                      + ∑ u : Fin (2 ^ b),
                          Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache)) := by
                  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
                    Finset.card_univ, Fintype.card_fin]
              _ = (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ)
                    + (∑ u : Fin (2 ^ b),
                        Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache))
                      / ((2 ^ b : ℕ) : ℝ≥0∞) := by
                  rw [mul_add, nsmul_eq_mul, ← mul_assoc,
                    ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul, mul_comm
                      (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹, ← div_eq_mul_inv]
              _ ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := ?_
            rw [hμ]
            by_cases hkmem : k₀ ∈ keys
            · -- extend an already-open slot: martingale step
              rw [show insert k₀ keys = keys from Finset.insert_eq_self.mpr hkmem]
              have hstep := Phi_extend_le ρ b S keys st (dead cache) k₀ i₀ hkmem hstn
              calc (q : ℝ≥0∞) * μ + (∑ u : Fin (2 ^ b),
                      Phi ρ b S keys (updateSlot st k₀ i₀ u) (dead cache))
                      / ((2 ^ b : ℕ) : ℝ≥0∞)
                  ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) :=
                    add_le_add le_rfl hstep
                _ ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := le_self_add
            · -- open a fresh slot: pay one μ
              have hstep := Phi_open_le ρ b S keys st (dead cache) k₀ i₀ hkmem
                (hINV.untouched k₀ hkmem)
              calc (q : ℝ≥0∞) * μ + (∑ u : Fin (2 ^ b),
                      Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache))
                      / ((2 ^ b : ℕ) : ℝ≥0∞)
                  ≤ (q : ℝ≥0∞) * μ + (Phi ρ b S keys st (dead cache) + μ) :=
                    add_le_add le_rfl hstep
                _ = (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := by
                    rw [add_assoc]
          · -- INERT: irrelevant record, dead slot, or kill — ghost state unchanged,
            -- potential non-increasing, average over the sampled value is trivial.
            have hinert : ∀ u : Fin (2 ^ b),
                relevant s → dead (cache.cacheQuery s u) (key s) := by
              intro u hrel
              by_cases hdd : dead cache (key s)
              · exact hdead_mono cache s u _ hdd
              · rcases hcv : st (key s) (coord s) with _ | u'
                · exact absurd ⟨hrel, hdd, hcv⟩ hlive
                · -- KILL: the cell was revealed by an earlier relevant record `t'`;
                  -- by `hcell` its challenge tag differs, so `hdead_kill` applies.
                  obtain ⟨t', ht'rel, ht'k, ht'i, ht'c⟩ :=
                    hINV.revealed_has_record (key s) (coord s) u' hdd hcv
                  have hts : t' ≠ s := fun h => by
                    rw [h, hc] at ht'c; simp at ht'c
                  have hchal : chalOf s ≠ chalOf t' := fun h =>
                    hts.symm (hcell s t' hrel ht'rel ht'k.symm ht'i.symm h)
                  exact hdead_kill cache s t' u u' hrel ht'rel ht'k.symm ht'i.symm
                    hchal ht'c
            refine expectedValue_bind_le_of_le fun u => ?_
            refine (ih u (q - 1) (hrest u) (cache.cacheQuery s u) keys st
              (hINV.cacheQuery_inert (hdead_mono cache s u) s hc u (hinert u))).trans ?_
            gcongr
            · exact Nat.sub_le q 1
            · exact Phi_mono_dead ρ b S _ _ _ _ (hdead_mono cache s u)
        · -- cache hit: no sampling, state unchanged, budget decremented
          have hrun : ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
              fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
                (simulateQ (roImpl b T) (mx p.1)).run p.2)
              = (simulateQ (roImpl b T) (mx u)).run cache := by
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hc, pure_bind]
          rw [hrun]
          refine (ih u (q - 1) (hrest u) cache keys st hINV).trans ?_
          gcongr
          exact Nat.sub_le q 1

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Initial-state specialization of `main_induction_gen`: from the empty cache the
expected leaf payoff is at most `(q + 1)·μ`. -/
private theorem main_induction_gen_init {T K C : Type} [DecidableEq T]
    (relevant : T → Prop)
    (key : T → K) (coord : T → Fin ρ) (chalOf : T → C)
    (hcell : ∀ t₁ t₂, relevant t₁ → relevant t₂ → key t₁ = key t₂ → coord t₁ = coord t₂ →
      chalOf t₁ = chalOf t₂ → t₁ = t₂)
    (dead : (T →ₒ Fin (2 ^ b)).QueryCache → K → Prop)
    [∀ c, DecidablePred (dead c)]
    (hdead_mono : ∀ c (t : T) (u : Fin (2 ^ b)) k, dead c k → dead (c.cacheQuery t u) k)
    (hdead_kill : ∀ (cache : (T →ₒ Fin (2 ^ b)).QueryCache) (t t' : T) (u u' : Fin (2 ^ b)),
      relevant t → relevant t' → key t = key t' → coord t = coord t' →
      chalOf t ≠ chalOf t' → cache t' = some u' → dead (cache.cacheQuery t u) (key t))
    {α : Type} (leaf : α → (T →ₒ Fin (2 ^ b)).QueryCache → ℝ≥0∞)
    (hleaf : ∀ (a : α) cache keys st,
      INV' ρ b relevant key coord (dead cache) cache keys st →
      leaf a cache ≤ Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none))
    (oa : OracleComp (unifSpec + (T →ₒ Fin (2 ^ b))) α)
    (q : ℕ) (hq : IsQueryBoundP oa (· matches .inr _) q) :
    expectedValue ((simulateQ (roImpl b T) oa).run ∅) (fun z => leaf z.1 z.2)
      ≤ ((q + 1 : ℕ) : ℝ≥0∞) * slotPsi ρ b S (fun _ => none) := by
  classical
  have hINV : INV' ρ b relevant key coord (dead ∅) ∅ (∅ : Finset K)
      (fun _ _ => none) := by
    refine ⟨fun t u _ _ hcc => ?_, fun k i u _ hst => ?_, fun _ _ => rfl⟩
    · rw [QueryCache.empty_apply] at hcc
      simp at hcc
    · simp at hst
  refine (main_induction_gen ρ b S relevant key coord chalOf hcell dead hdead_mono
    hdead_kill leaf hleaf oa q hq ∅ ∅ (fun _ _ => none) hINV).trans (le_of_eq ?_)
  rw [Phi, Finset.sum_empty, add_zero, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Left query on the logged stack: forwarded, no log, cache unchanged. Stated with the
mapped function's domain at the sum-spec `Range` type so keyed rewriting fires after
`simulateQ_bind`. -/
private lemma loggedImpl_run_run_inl {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
     [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    (i : unifSpec.Domain) (c : hashSpec.QueryCache) :
    (((idImplW hashSpec + loggedROW hashSpec) (Sum.inl i)).run).run c =
      (fun (u : (unifSpec + hashSpec).Range (Sum.inl i)) =>
          ((u, (∅ : QueryLog hashSpec)), c)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) i) := by
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Right query on the logged stack, cache hit: cached value, logged, cache unchanged. -/
private lemma loggedImpl_run_run_inr_some {ι : Type} {hashSpec : OracleSpec ι}
    [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {j : hashSpec.Domain} {c : hashSpec.QueryCache}
    {u : hashSpec.Range j} (h : c j = some u) :
    (((idImplW hashSpec + loggedROW hashSpec) (Sum.inr j)).run).run c =
      pure (((u, ([⟨j, u⟩] : QueryLog hashSpec)), c) :
        ((unifSpec + hashSpec).Range (Sum.inr j) × QueryLog hashSpec) ×
          hashSpec.QueryCache) := by
  change ((loggedROW hashSpec j).run).run c = _
  rw [loggedROW, QueryImpl.run_withLogging_apply, StateT.run_bind,
    show hashSpec.randomOracle = QueryImpl.withCaching uniformSampleImpl from rfl,
    QueryImpl.withCaching_run_some _ h, pure_bind]
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Right query on the logged stack, cache miss: sample, log, cache the value. -/
private lemma loggedImpl_run_run_inr_none {ι : Type} {hashSpec : OracleSpec ι}
    [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {j : hashSpec.Domain} {c : hashSpec.QueryCache} (h : c j = none) :
    (((idImplW hashSpec + loggedROW hashSpec) (Sum.inr j)).run).run c =
      (fun (u : (unifSpec + hashSpec).Range (Sum.inr j)) =>
          ((u, ([⟨j, u⟩] : QueryLog hashSpec)), c.cacheQuery j u)) <$>
        ($ᵗ hashSpec.Range j) := by
  change ((loggedROW hashSpec j).run).run c = _
  rw [loggedROW, QueryImpl.run_withLogging_apply, StateT.run_bind,
    show hashSpec.randomOracle = QueryImpl.withCaching uniformSampleImpl from rfl,
    QueryImpl.withCaching_run_none _ h]
  rw [show uniformSampleImpl (spec := hashSpec) j = ($ᵗ hashSpec.Range j) from rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind, StateT.run_pure]
  exact (map_eq_bind_pure_comp ProbComp
    (fun u : hashSpec.Range j => ((u, ([⟨j, u⟩] : QueryLog hashSpec)), c.cacheQuery j u))
    ($ᵗ hashSpec.Range j)).symm

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Left query on the unlogged stack: forwarded, cache unchanged. -/
private lemma unloggedImpl_run_inl {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    (i : unifSpec.Domain) (c : hashSpec.QueryCache) :
    ((unifFwdImpl hashSpec + hashSpec.randomOracle) (Sum.inl i)).run c =
      (fun (u : (unifSpec + hashSpec).Range (Sum.inl i)) => (u, c)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) i) := by
  change (unifFwdImpl hashSpec i).run c = _
  simp [unifFwdImpl, StateT.run_monadLift, bind_pure_comp]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Right query on the unlogged stack, cache hit. -/
private lemma unloggedImpl_run_inr_some {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {j : hashSpec.Domain} {c : hashSpec.QueryCache}
    {u : hashSpec.Range j} (h : c j = some u) :
    ((unifFwdImpl hashSpec + hashSpec.randomOracle) (Sum.inr j)).run c =
      pure ((u, c) : (unifSpec + hashSpec).Range (Sum.inr j) × hashSpec.QueryCache) :=
  QueryImpl.withCaching_run_some (so := uniformSampleImpl) h

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Right query on the unlogged stack, cache miss. -/
private lemma unloggedImpl_run_inr_none {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {j : hashSpec.Domain} {c : hashSpec.QueryCache} (h : c j = none) :
    ((unifFwdImpl hashSpec + hashSpec.randomOracle) (Sum.inr j)).run c =
      (fun (u : (unifSpec + hashSpec).Range (Sum.inr j)) =>
        (u, c.cacheQuery j u)) <$> ($ᵗ hashSpec.Range j) :=
  QueryImpl.withCaching_run_none (so := uniformSampleImpl) h

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Dropping the log.** Projecting away the query log from the logged run yields, as a
plain `ProbComp` term equality, the unlogged run. -/
private theorem dropLog_run_eq {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
     [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α) (cache : hashSpec.QueryCache) :
    (fun z => (z.1.1, z.2)) <$>
        ((simulateQ (idImplW hashSpec + loggedROW hashSpec) oa).run).run cache
      = (simulateQ (unifFwdImpl hashSpec + hashSpec.randomOracle) oa).run cache := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a =>
      simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure, map_pure]
  | query_bind t k ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', StateT.run_bind,
        StateT.run_map, map_bind]
      cases t with
      | inl i =>
          rw [loggedImpl_run_run_inl, unloggedImpl_run_inl]
          simp only [Functor.map_map, Prod.map_fst, id_eq]
          erw [bind_map_left]
          exact bind_congr fun u => ih u cache
      | inr j =>
          cases hc : cache j with
          | some u =>
              rw [loggedImpl_run_run_inr_some hc, unloggedImpl_run_inr_some hc]
              simp only [pure_bind, Functor.map_map, Prod.map_fst, id_eq]
              exact ih u cache
          | none =>
              rw [loggedImpl_run_run_inr_none hc, unloggedImpl_run_inr_none hc]
              simp only [Functor.map_map, Prod.map_fst, id_eq]
              erw [bind_map_left]
              erw [bind_map_left]
              exact bind_congr fun u => ih u (cache.cacheQuery j u)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Expected payoffs that ignore the log coincide between the logged and unlogged runs. -/
private theorem dropLog_expectedValue {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α) (cache : hashSpec.QueryCache)
    (f : α → hashSpec.QueryCache → ℝ≥0∞) :
    expectedValue (((simulateQ (idImplW hashSpec + loggedROW hashSpec) oa).run).run cache)
        (fun z => f z.1.1 z.2)
      = expectedValue ((simulateQ (unifFwdImpl hashSpec + hashSpec.randomOracle) oa).run cache)
        (fun w => f w.1 w.2) := by
  rw [← dropLog_run_eq oa cache, expectedValue_map]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Probabilities of events depending only on the value and the final cache agree between
the logged and the unlogged run. -/
private theorem dropLog_probEvent {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α) (cache : hashSpec.QueryCache)
    (p : α → hashSpec.QueryCache → Prop) :
    Pr[fun z => p z.1.1 z.2 |
        ((simulateQ (idImplW hashSpec + loggedROW hashSpec) oa).run).run cache]
      = Pr[fun w => p w.1 w.2 |
        (simulateQ (unifFwdImpl hashSpec + hashSpec.randomOracle) oa).run cache] := by
  rw [← dropLog_run_eq oa cache, probEvent_map]
  rfl

/-! ### Knowledge-Soundness Assembly: Classifier Instantiation

The supermartingale induction `main_induction_gen_init` is instantiated on the Fischlin
random-oracle records: a record is *relevant* (`ksRelevant`) when it carries the proof's
statement/message tags and σ-verifies against the commitment stored at its repetition
index in its own commitment list; cells are indexed by `(comList, rep)`; and a
commitment-list key dies (`ksDead`) once the cache holds two relevant records in the same
cell with distinct challenges — exactly the event in which the online extractor succeeds. -/

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Relevance classifier for the supermartingale induction: the record carries the proof's
statement and message tags, and its challenge–response pair σ-verifies against the
commitment stored at its repetition index of its own commitment list. -/
private def ksRelevant (x : Stmt) (msg : M)
    (t : FischlinROInput Stmt Commit Chal Resp ρ M) : Prop :=
  t.stmt = x ∧ t.msg = msg ∧
    ∃ c, t.comList[(t.rep : ℕ)]? = some c ∧ σ.verify x c t.chal t.resp = true

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Deadness classifier: a commitment-list key is dead once the cache holds two relevant
records at the same repetition with distinct challenges (the extractor's success event). -/
private def ksDead (x : Stmt) (msg : M)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (k : List Commit) : Prop :=
  ∃ t t' : FischlinROInput Stmt Commit Chal Resp ρ M, ∃ u u' : Fin (2 ^ b),
    ksRelevant σ ρ M x msg t ∧ ksRelevant σ ρ M x msg t' ∧
      t.comList = k ∧ t'.comList = k ∧ t.rep = t'.rep ∧ t.chal ≠ t'.chal ∧
      cache t = some u ∧ cache t' = some u'

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Cell injectivity.** Under unique responses, two relevant records in the same cell
(same commitment list and repetition) with the same challenge are equal: the commitment is
determined by the cell, and the response by unique responses. -/
private lemma ksRelevant_cell_inj (hur : σ.UniqueResponses) (x : Stmt) (msg : M)
    (t₁ t₂ : FischlinROInput Stmt Commit Chal Resp ρ M)
    (h₁ : ksRelevant σ ρ M x msg t₁) (h₂ : ksRelevant σ ρ M x msg t₂)
    (hk : t₁.comList = t₂.comList) (hi : t₁.rep = t₂.rep) (hc : t₁.chal = t₂.chal) :
    t₁ = t₂ := by
  obtain ⟨s₁, m₁, cl₁, r₁, ch₁, rp₁⟩ := t₁
  obtain ⟨s₂, m₂, cl₂, r₂, ch₂, rp₂⟩ := t₂
  obtain ⟨hs₁, hm₁, c₁, hc₁, hv₁⟩ := h₁
  obtain ⟨hs₂, hm₂, c₂, hc₂, hv₂⟩ := h₂
  dsimp only at hs₁ hm₁ hc₁ hv₁ hs₂ hm₂ hc₂ hv₂ hk hi hc
  subst hs₁ hm₁ hs₂ hm₂ hk hi hc
  cases Option.some.inj (hc₁.symm.trans hc₂)
  exact congrArg (FischlinROInput.mk _ _ _ _ _) (hur _ c₁ _ rp₁ rp₂ hv₁ hv₂)

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- **Deadness is monotone** under caching: a cache update never erases an entry. -/
private lemma ksDead_mono (x : Stmt) (msg : M)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (s : FischlinROInput Stmt Commit Chal Resp ρ M) (v : Fin (2 ^ b)) (k : List Commit)
    (h : ksDead σ ρ b M x msg cache k) :
    ksDead σ ρ b M x msg (cache.cacheQuery s v) k := by
  obtain ⟨t, t', u, u', h₁, h₂, h₃, h₄, h₅, h₆, hct, hct'⟩ := h
  have hsome : ∀ (r : FischlinROInput Stmt Commit Chal Resp ρ M) (w : Fin (2 ^ b)),
      cache r = some w → ∃ w', (cache.cacheQuery s v) r = some w' := by
    intro r w hw
    by_cases hrs : r = s
    · subst hrs
      exact ⟨v, QueryCache.cacheQuery_self cache r v⟩
    · exact ⟨w, by rw [QueryCache.cacheQuery_of_ne _ _ hrs]; exact hw⟩
  obtain ⟨w, hw⟩ := hsome t u hct
  obtain ⟨w', hw'⟩ := hsome t' u' hct'
  exact ⟨t, t', w, w', h₁, h₂, h₃, h₄, h₅, h₆, hw, hw'⟩

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- **Kill step.** Caching a relevant record on top of a cached relevant record in the same
cell with a different challenge makes the key dead. -/
private lemma ksDead_kill (x : Stmt) (msg : M)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (t t' : FischlinROInput Stmt Commit Chal Resp ρ M) (u u' : Fin (2 ^ b))
    (hrel : ksRelevant σ ρ M x msg t) (hrel' : ksRelevant σ ρ M x msg t')
    (hk : t.comList = t'.comList) (hi : t.rep = t'.rep) (hch : t.chal ≠ t'.chal)
    (hc' : cache t' = some u') :
    ksDead σ ρ b M x msg (cache.cacheQuery t u) t.comList := by
  have hne : t' ≠ t := fun h => hch (by rw [h])
  exact ⟨t, t', u, u', hrel, hrel', rfl, hk.symm, hi, hch,
    QueryCache.cacheQuery_self cache t u,
    by rw [QueryCache.cacheQuery_of_ne _ _ hne]; exact hc'⟩

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Each per-repetition verification record of a σ-verifying proof is relevant. -/
private lemma ksRelevant_record (x : Stmt) (msg : M) (π : FischlinProof Commit Chal Resp ρ)
    (i : Fin ρ) (hver : σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true) :
    ksRelevant σ ρ M x msg
      ⟨x, msg, List.ofFn fun j => (π j).1, i, (π i).2.1, (π i).2.2⟩ := by
  refine ⟨rfl, rfl, (π i).1, ?_, hver⟩
  rw [List.getElem?_ofFn, dif_pos i.isLt]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- A relevant record at the proof's commitment list σ-verifies against the proof's
commitment at the record's repetition. -/
private lemma ksRelevant_verify_at (x : Stmt) (msg : M)
    (π : FischlinProof Commit Chal Resp ρ) (t : FischlinROInput Stmt Commit Chal Resp ρ M)
    (h : ksRelevant σ ρ M x msg t)
    (hcom : t.comList = List.ofFn fun j => (π j).1) :
    σ.verify x (π t.rep).1 t.chal t.resp = true := by
  obtain ⟨_, _, c, hc, hv⟩ := h
  rw [hcom, List.getElem?_ofFn, dif_pos t.rep.isLt] at hc
  cases Option.some.inj hc
  exact hv

omit [SampleableType Chal] in
/-- Leaf payoff of the knowledge-soundness induction: the acceptance probability of the
Fischlin verifier on the final cache, gated by the cache-side pinning predicate
`CachePinned` (the event that the extractor's log scan misses). -/
private noncomputable def ksLeaf (x : Stmt) (msg : M)
    (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) : ℝ≥0∞ :=
  letI : Decidable (CachePinned σ ρ b M x π cache) := Classical.propDecidable _
  (if CachePinned σ ρ b M x π cache then 1 else 0) *
    Pr[= true | (simulateQ (fischlinImpl ρ b M)
      ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
        σ hr ρ b S M).verify x msg π)).run' cache]

omit [SampleableType Chal] in
/-- **Per-leaf bound.** Under the generalized multi-record coupling invariant `INV'` for the
Fischlin classifiers, the leaf payoff is at most the live multi-slot potential plus one fresh slot
potential: when the scan misses (`CachePinned`), the verifier's acceptance probability is
*exactly* the slot potential of the proof's commitment-list key, which is either a live
summand of `Phi` or (if untouched) exactly `μ`. -/
private lemma fischlin_leaf_le (hur : σ.UniqueResponses) (x : Stmt) (msg : M)
    (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (keys : Finset (List Commit))
    (st : List Commit → Fin ρ → Option (Fin (2 ^ b)))
    [DecidablePred (ksDead σ ρ b M x msg cache)]
    (hINV : INV' ρ b (ksRelevant σ ρ M x msg) (fun t => t.comList) (fun t => t.rep)
      (ksDead σ ρ b M x msg cache) cache keys st) :
    ksLeaf σ hr ρ b S M x msg π cache
      ≤ Phi ρ b S keys st (ksDead σ ρ b M x msg cache)
        + slotPsi ρ b S (fun _ => none) := by
  unfold ksLeaf
  by_cases hpin : CachePinned σ ρ b M x π cache
  case neg =>
    rw [if_neg hpin, zero_mul]
    exact zero_le
  rw [if_pos hpin, one_mul]
  by_cases hver : ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true
  case neg =>
    -- Some repetition fails σ-verification: acceptance probability is zero.
    have hall :
        ((List.finRange ρ).all fun i => σ.verify x (π i).1 (π i).2.1 (π i).2.2) ≠ true :=
      fun hAll => hver fun i => List.all_eq_true.mp hAll i (List.mem_finRange i)
    rw [verify_probOutput_true_mixed σ hr ρ b S M x msg π cache
      (fun j => cache ⟨x, msg, List.ofFn fun k => (π k).1, j, (π j).2.1, (π j).2.2⟩)
      (fun j => rfl), if_neg hall, zero_mul, ENNReal.zero_div]
    exact zero_le
  set k₀ : List Commit := List.ofFn fun j => (π j).1 with hk₀
  -- The proof's key is live: deadness would give two distinct pinned challenges in a cell.
  have hlive : ¬ ksDead σ ρ b M x msg cache k₀ := by
    rintro ⟨t, t', u, u', hrel, hrel', hck, hck', hrep, hchal, hct, hct'⟩
    have hpt : t.chal = (π t.rep).2.1 :=
      hpin t u hct hrel.1 hck (ksRelevant_verify_at σ ρ M x msg π t hrel hck)
    have hpt' : t'.chal = (π t'.rep).2.1 :=
      hpin t' u' hct' hrel'.1 hck' (ksRelevant_verify_at σ ρ M x msg π t' hrel' hck')
    exact hchal (by rw [hpt, hpt', hrep])
  -- Hits correspondence: the cache at the proof's records is exactly the ghost slot state.
  have hcache : ∀ i : Fin ρ,
      cache ⟨x, msg, k₀, i, (π i).2.1, (π i).2.2⟩ = st k₀ i := by
    intro i
    cases hc : cache ⟨x, msg, k₀, i, (π i).2.1, (π i).2.2⟩ with
    | some u =>
        exact (hINV.cached_imp _ u (ksRelevant_record σ ρ M x msg π i (hver i)) hlive hc).symm
    | none =>
        cases hst : st k₀ i with
        | none => rfl
        | some u =>
            exfalso
            obtain ⟨t, htrel, htk, hti, htc⟩ := hINV.revealed_has_record k₀ i u hlive hst
            have hchal : t.chal = (π t.rep).2.1 :=
              hpin t u htc htrel.1 htk (ksRelevant_verify_at σ ρ M x msg π t htrel htk)
            have hresp : t.resp = (π t.rep).2.2 :=
              hur x (π t.rep).1 (π t.rep).2.1 t.resp (π t.rep).2.2
                (hchal ▸ ksRelevant_verify_at σ ρ M x msg π t htrel htk) (hver t.rep)
            obtain ⟨hts, htm, -⟩ := htrel
            have ht : t = ⟨x, msg, k₀, i, (π i).2.1, (π i).2.2⟩ := by
              obtain ⟨ts, tm, tcl, tr, tch, trp⟩ := t
              dsimp only at hts htm htk hti hchal hresp
              subst hts htm htk hti
              rw [hchal, hresp]
            rw [ht, hc] at htc
            exact Option.some_ne_none u htc.symm
  -- Exact leaf value: the slot potential of the proof's key.
  have hall :
      ((List.finRange ρ).all fun i => σ.verify x (π i).1 (π i).2.1 (π i).2.2) = true :=
    List.all_eq_true.mpr fun i _ => hver i
  rw [verify_probOutput_true_mixed σ hr ρ b S M x msg π cache (st k₀) hcache, if_pos hall,
    one_mul]
  change slotPsi ρ b S (st k₀) ≤ _
  by_cases hk : k₀ ∈ keys
  · -- Touched live key: its slot potential is a summand of `Phi`.
    refine le_trans ?_ le_self_add
    rw [Phi]
    calc slotPsi ρ b S (st k₀)
        = if ksDead σ ρ b M x msg cache k₀ then 0 else slotPsi ρ b S (st k₀) :=
          (if_neg hlive).symm
      _ ≤ ∑ k ∈ keys, if ksDead σ ρ b M x msg cache k then 0 else slotPsi ρ b S (st k) :=
          Finset.single_le_sum
            (f := fun k => if ksDead σ ρ b M x msg cache k then 0 else slotPsi ρ b S (st k))
            (fun k _ => zero_le) hk
  · -- Untouched key: its slot state is all-`none`, contributing exactly `μ`.
    rw [hINV.untouched k₀ hk]
    exact le_add_self

omit [SampleableType Chal] in
/-- **Factoring the miss event through the logged run.** The probability that the verifier
accepts while the extractor's scan misses equals the expected value, over the logged prover
run, of the scan-miss indicator times the verifier's acceptance probability on the final
cache. -/
private lemma ksSample_probEvent_eq_expectedValue
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) :
    Pr[fun out => out.2 = true ∧ fischlinFindWitness σ ρ b M x out.1.1 out.1.2 = none
        | ksSample σ hr ρ b S M prover x msg]
      = expectedValue (((simulateQ (idImplW (fischlinROSpec Stmt Commit Chal Resp ρ b M)
            + loggedROW (fischlinROSpec Stmt Commit Chal Resp ρ b M))
          (prover x msg)).run).run ∅)
        (fun z =>
          (if fischlinFindWitness σ ρ b M x z.1.1 z.1.2 = none then 1 else 0) *
            Pr[= true | (simulateQ (fischlinImpl ρ b M)
              ((Fischlin (m := OracleComp (unifSpec
                  + fischlinROSpec Stmt Commit Chal Resp ρ b M))
                σ hr ρ b S M).verify x msg z.1.1)).run' z.2]) := by
  classical
  have hks : ksSample σ hr ρ b S M prover x msg
      = ((simulateQ (idImplW (fischlinROSpec Stmt Commit Chal Resp ρ b M)
            + loggedROW (fischlinROSpec Stmt Commit Chal Resp ρ b M))
          (prover x msg)).run).run ∅ >>= fun z =>
            (simulateQ (fischlinImpl ρ b M)
              ((Fischlin (m := OracleComp (unifSpec
                  + fischlinROSpec Stmt Commit Chal Resp ρ b M))
                σ hr ρ b S M).verify x msg z.1.1)).run z.2 >>= fun vc =>
              pure ((z.1.1, z.1.2), vc.1) := rfl
  rw [hks, probEvent_bind_eq_tsum, expectedValue]
  refine tsum_congr fun z => ?_
  congr 1
  rw [probEvent_bind_eq_tsum]
  by_cases hfw : fischlinFindWitness σ ρ b M x z.1.1 z.1.2 = none
  · rw [if_pos hfw, one_mul, StateT.run', ← probEvent_eq_eq_probOutput, probEvent_map,
      probEvent_eq_tsum_ite]
    refine tsum_congr fun vc => ?_
    rw [probEvent_pure]
    by_cases hv : vc.1 = true
    · rw [if_pos ⟨hv, hfw⟩, mul_one]
      exact (if_pos hv).symm
    · rw [if_neg (fun h => hv h.1), mul_zero]
      exact (if_neg hv).symm
  · rw [if_neg hfw, zero_mul]
    refine ENNReal.tsum_eq_zero.mpr fun vc => ?_
    rw [probEvent_pure, if_neg (fun h => hfw h.2), mul_zero]

omit [SampleableType Chal] in
/-- **Support transfer.** On the support of the logged run, the extractor's scan-miss
indicator coincides with the cache-side pinning predicate (`CachePinned`), turning the
factored payoff into the log-free leaf `ksLeaf`. -/
private lemma EP_scanMiss_eq_EP_ksLeaf
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) :
    expectedValue (((simulateQ (idImplW (fischlinROSpec Stmt Commit Chal Resp ρ b M)
            + loggedROW (fischlinROSpec Stmt Commit Chal Resp ρ b M))
          (prover x msg)).run).run ∅)
        (fun z =>
          (if fischlinFindWitness σ ρ b M x z.1.1 z.1.2 = none then 1 else 0) *
            Pr[= true | (simulateQ (fischlinImpl ρ b M)
              ((Fischlin (m := OracleComp (unifSpec
                  + fischlinROSpec Stmt Commit Chal Resp ρ b M))
                σ hr ρ b S M).verify x msg z.1.1)).run' z.2])
      = expectedValue (((simulateQ (idImplW (fischlinROSpec Stmt Commit Chal Resp ρ b M)
            + loggedROW (fischlinROSpec Stmt Commit Chal Resp ρ b M))
          (prover x msg)).run).run ∅)
        (fun z => ksLeaf σ hr ρ b S M x msg z.1.1 z.2) := by
  classical
  refine expectedValue_congr_of_support fun z hz => ?_
  unfold ksLeaf
  have hiff := fischlinFindWitness_eq_none_iff_cachePinned σ ρ b M x z.1.1
    (log_subset_cache (prover x msg) hz) (cache_subset_log (prover x msg) hz)
  by_cases hfw : fischlinFindWitness σ ρ b M x z.1.1 z.1.2 = none
  · rw [if_pos hfw, if_pos (hiff.mp hfw)]
  · rw [if_neg hfw, if_neg fun hp => hfw (hiff.mpr hp)]

omit [SampleableType Chal] in
/-- **Online-extraction reduction (Fischlin 2005, Theorem 2 core).** The Fischlin
knowledge-soundness bad event — the verifier accepts the cheating prover's proof yet the online
extractor recovers no
valid witness — occurs with probability at most `(Q+1)` (one slot per logged hash query, plus the
trivial slot) times the chance that a fresh tuple of `ρ` independent random-oracle answers lands in
the small-sum target set, namely `smallSumCount ρ b S / (2^b)^ρ`.

Argument sketch: special soundness with unique responses (`hss`, `hur`) implies that whenever the
extractor fails, every repetition's accepting transcript is pinned to a single logged query, so the
prover must have hit a small-sum assignment of `ρ` *fresh* uniform hash values without a second
accepting query at a different challenge. Union-bounding over the `≤ Q` logged queries and the
small-sum target set, and using independence of the `ρ` fresh answers, gives the denominator
`(2^b)^ρ`. -/
private lemma knowledgeSoundness_badEvent_le
    (hss : σ.SpeciallySound) (hur : σ.UniqueResponses)
    (adv : KnowledgeSoundnessAdv ρ b M) (Q : ℕ) (_hρ : 0 < ρ)
    (hQ : ∀ x msg, ROQueryBound ρ b M (adv.run x msg) Q) (x : Stmt) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M adv.run x msg]
      ≤ (↑(Q + 1) : ℝ≥0∞) * ↑(smallSumCount ρ b S) / ((↑(2 ^ b) : ℝ≥0∞) ^ ρ) := by
  classical
  let : ∀ c, DecidablePred (ksDead σ ρ b M x msg c) := fun _ => Classical.decPred _
  -- Step 1: bound the bad event by the verifier-accepts-while-scan-misses event.
  refine le_trans (knowledgeSoundnessExp_bad_le_misses' σ hr ρ b S M hss adv.run x msg) ?_
  -- Step 2: factor the miss event through the logged prover run as an expected payoff.
  rw [ksSample_probEvent_eq_expectedValue σ hr ρ b S M adv.run x msg,
    -- Step 3: on the support, swap the scan-miss indicator for the pinning predicate.
    EP_scanMiss_eq_EP_ksLeaf σ hr ρ b S M adv.run x msg,
    -- Step 4: drop the log, moving to the unlogged lazy-random-oracle run.
    dropLog_expectedValue (adv.run x msg) ∅ (fun π cache => ksLeaf σ hr ρ b S M x msg π cache)]
  -- Step 5: run the supermartingale induction from the empty cache.
  refine le_trans (main_induction_gen_init ρ b S
    (ksRelevant σ ρ M x msg) (fun t => t.comList) (fun t => t.rep) (fun t => t.chal)
    (fun t₁ t₂ h₁ h₂ hk hi hc => ksRelevant_cell_inj σ ρ M hur x msg t₁ t₂ h₁ h₂ hk hi hc)
    (ksDead σ ρ b M x msg)
    (fun c t u k h => ksDead_mono σ ρ b M x msg c t u k h)
    (fun cache t t' u u' hrel hrel' hk hi hch hc' =>
      ksDead_kill σ ρ b M x msg cache t t' u u' hrel hrel' hk hi hch hc')
    (fun π cache => ksLeaf σ hr ρ b S M x msg π cache)
    (fun a cache keys st hINV => fischlin_leaf_le σ hr ρ b S M hur x msg a cache keys st hINV)
    (adv.run x msg) Q ((OracleComp.isQueryBoundP_congr_pred
      fun t => by cases t <;> exact Iff.rfl).mp (hQ x msg))) (le_of_eq ?_)
  -- Step 6: evaluate the fresh slot potential `μ = smallSumCount / (2^b)^ρ`.
  rw [slotPsi_none, ← mul_div_assoc, Nat.cast_pow, Nat.cast_ofNat]

omit [SampleableType Chal] in
/-- Knowledge soundness of the Fischlin transform via online (straight-line) extraction
(Fischlin 2005, Theorem 2).

If the Σ-protocol is specially sound with unique responses, then for any cheating prover
making at most `Q` hash queries, the probability that the verifier accepts but the
online extractor fails to recover a valid witness is at most
`(Q + 1) · (S + 1) · C(S + ρ - 1, ρ - 1) / 2^(bρ)`.

Unlike the Fiat-Shamir transform, this extraction is **straight-line** (no rewinding),
which enables a tight security reduction. -/
theorem knowledgeSoundness
    (hss : σ.SpeciallySound) (hur : σ.UniqueResponses)
    (adv : KnowledgeSoundnessAdv ρ b M)
    (Q : ℕ) (hρ : 0 < ρ)
    (hQ : ∀ x msg, ROQueryBound ρ b M (adv.run x msg) Q)
    (x : Stmt) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M adv.run x msg]
      ≤ knowledgeSoundnessError Q ρ b S := by
  refine le_trans (knowledgeSoundness_badEvent_le σ hr ρ b S M hss hur adv Q hρ hQ x msg) ?_
  rw [knowledgeSoundnessError]
  -- Monotonicity: replace the small-sum count by its stars-and-bars upper bound.
  gcongr
  exact_mod_cast smallSumCount_le ρ b S

/-! ### EUF-CMA Security

A tight EUF-CMA corollary for the Fischlin signature scheme requires an explicit
simulation of signing queries inside a hard-relation experiment. The previous
placeholder theorem overclaimed by bounding forgery probability solely by the
knowledge-soundness error, so we intentionally leave that corollary unstated
until the signing-simulation reduction is formalized. -/

end security

end Fischlin
