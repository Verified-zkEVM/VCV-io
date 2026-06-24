/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.Auth

/-!
# PRF Tag/Reader Protocol — Collision Bound, Per-Step Forge Infrastructure

Per-step random-oracle infrastructure for the random-function authentication world: cache
monotonicity of `authRFLookup` (the `StateT.PreservesInv` lemmas), single-point miss bounds for
fresh lookups, the per-query step core, and the per-reader-step forge bound
`authRFReaderStep_forge_le` together with the reader lookup pass `authRFReaderLookups` and its
log characterization `authRFLookup_mapM_logs_eq`.

The collision-bound theorems built on this infrastructure live in the parent module
`Examples.PRFTagReader.Collision`.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section Theorems

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- One `authRFLookup` step preserves the invariant `responses t₀ = some d`: a cache hit leaves the
table unchanged, and a cache miss only writes a fresh entry at the looked-up point, which is
necessarily distinct from `t₀` since `t₀` is already cached. -/
private lemma authRFLookup_responses_some_preservesInv
    (t₀ : TagId × Nonce) (d : Digest) (tag : TagId) (nonce : Nonce) :
    StateT.PreservesInv
      (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce)
      (fun st => st.responses t₀ = some d) := by
  intro st hst z hz
  unfold authRFLookup at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hresp : st.responses (tag, nonce) with
  | some out =>
    simp only [hresp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact hst
  | none =>
    simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
      StateT.run_map, StateT.run_set, support_bind, support_uniformSample, Set.mem_univ,
      Set.mem_iUnion, support_map, Set.mem_image, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨i, -, x, rfl, rfl⟩ := hz
    have hkey : t₀ ≠ (tag, nonce) := by
      rintro rfl
      rw [hresp] at hst
      simp at hst
    change (st.responses.cacheQuery (tag, nonce) i.1) t₀ = some d
    rw [QueryCache.cacheQuery_of_ne _ _ hkey]
    exact hst

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- The reader's `mapM` of `authRFLookup` over a list of tags preserves the invariant
`responses t₀ = some d`, by iterating `authRFLookup_responses_some_preservesInv`. -/
private lemma authRFLookup_mapM_responses_some_preservesInv
    (t₀ : TagId × Nonce) (d : Digest) (nonce : Nonce) (tags : List TagId) :
    StateT.PreservesInv
      (tags.mapM (fun tag => do
        let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
        pure (tag, dg)))
      (fun st => st.responses t₀ = some d) := by
  induction tags with
  | nil =>
    simp only [List.mapM_nil]
    exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)
  | cons hd tl ih =>
    rw [List.mapM_cons]
    refine StateT.preservesInv_bind _ _ _ ?_ ?_
    · refine StateT.preservesInv_bind _ _ _ ?_ ?_
      · exact authRFLookup_responses_some_preservesInv t₀ d hd nonce
      · intro dg
        exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)
    · intro p
      refine StateT.preservesInv_bind _ _ _ ih ?_
      intro ps
      exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The lazy random-oracle cache threaded by `authRFQueryImpl` only grows: once a point `t₀`
holds a digest `d`, every reachable later state still has `t₀ ↦ d`. -/
private lemma authRFQueryImpl_responses_some_preservesInv
    (t₀ : TagId × Nonce) (d : Digest) :
    QueryImpl.PreservesInv
      (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
      (fun st => st.responses t₀ = some d) := by
  intro t st hst z hz
  cases t with
  | inl tag =>
    have htag : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (Sum.inl tag)).run st =
        (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run st :=
      rfl
    rw [htag] at hz
    unfold authIdealTagQueryImpl at hz
    simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_eq_self, bind_map_left] at hz
    obtain ⟨nonce, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    cases hresp : st.responses (tag, nonce) with
    | none =>
      simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
        StateT.run_map, StateT.run_set, map_pure, Functor.map_map] at hz
      rw [map_eq_bind_pure_comp] at hz
      obtain ⟨auth, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      simp only [Function.comp_apply] at hz
      subst hz
      have hkey : t₀ ≠ (tag, nonce) := by
        rintro rfl
        rw [hresp] at hst
        simp at hst
      change (st.responses.cacheQuery (tag, nonce) auth) t₀ = some d
      rw [QueryCache.cacheQuery_of_ne _ _ hkey]
      exact hst
    | some out =>
      simp only [hresp, StateT.run_map, StateT.run_set, map_pure] at hz
      rcases hz with rfl
      exact hst
  | inr transcript =>
    have hrd : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (Sum.inr transcript)).run st =
        (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript).run st :=
      rfl
    rw [hrd] at hz
    unfold authRFReaderQueryImpl at hz
    simp only [bind_pure_comp, StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    simp only [StateT.run_get, pure_bind, StateT.run_map, StateT.run_set, map_pure] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact authRFLookup_mapM_responses_some_preservesInv t₀ d transcript.nonce
      (Finset.univ : Finset TagId).toList st hst p hp

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- One `authRFLookup tag nonce` step at a point distinct from `t₀` preserves `responses t₀ = none`.
The looked-up point `(tag, nonce)` differs from `t₀`, so a cache miss writes elsewhere. -/
private lemma authRFLookup_responses_none_preservesInv
    (t₀ : TagId × Nonce) (tag : TagId) (nonce : Nonce) (hne : (tag, nonce) ≠ t₀) :
    StateT.PreservesInv
      (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce)
      (fun st => st.responses t₀ = none) := by
  intro st hst z hz
  unfold authRFLookup at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hresp : st.responses (tag, nonce) with
  | some out =>
    simp only [hresp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact hst
  | none =>
    simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
      StateT.run_map, StateT.run_set, support_bind, support_uniformSample, Set.mem_univ,
      Set.mem_iUnion, support_map, Set.mem_image, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨i, -, x, rfl, rfl⟩ := hz
    change (st.responses.cacheQuery (tag, nonce) i.1) t₀ = none
    rw [QueryCache.cacheQuery_of_ne _ _ (fun h => hne h.symm)]
    exact hst

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- The reader's `mapM` of `authRFLookup` at a nonce different from `t₀.2` preserves
`responses t₀ = none`: every looked-up point `(tag, nonce)` differs from `t₀`. -/
private lemma authRFLookup_mapM_responses_none_preservesInv
    (t₀ : TagId × Nonce) (nonce : Nonce) (hne : nonce ≠ t₀.2) (tags : List TagId) :
    StateT.PreservesInv
      (tags.mapM (fun tag => do
        let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
        pure (tag, dg)))
      (fun st => st.responses t₀ = none) := by
  induction tags with
  | nil =>
    simp only [List.mapM_nil]
    exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)
  | cons hd tl ih =>
    rw [List.mapM_cons]
    refine StateT.preservesInv_bind _ _ _ ?_ ?_
    · refine StateT.preservesInv_bind _ _ _ ?_ ?_
      · refine authRFLookup_responses_none_preservesInv t₀ hd nonce ?_
        intro hcontra
        exact hne (congrArg Prod.snd hcontra)
      · intro dg
        exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)
    · intro p
      refine StateT.preservesInv_bind _ _ _ ih ?_
      intro ps
      exact StateT.preservesInv_of_statePreserving _ _ (StateT.statePreserving_pure _)

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- One `authRFLookup tag nonce` step at the point `t₀` itself, starting from `responses t₀ = none`
(so it is a genuine cache miss), draws a single fresh uniform digest into `t₀`: the probability that
`t₀` ends holding any fixed `v₀` is at most `maxDigestProb`, and it never stays `none`. -/
private lemma authRFLookup_miss_bound
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (t₀ : TagId × Nonce) (v₀ : Digest)
    (st : AuthIdealState TagId Nonce Digest)
    (hnone : st.responses t₀ = none) :
    Pr[fun p => p.2.responses t₀ = some v₀ |
        (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t₀.1 t₀.2).run st] ≤
      maxDigestProb ∧
    Pr[fun p => p.2.responses t₀ = none |
        (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          t₀.1 t₀.2).run st] = 0 := by
  classical
  have hrun : (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      t₀.1 t₀.2).run st =
      ((fun d => (d, ({ st with responses := st.responses.cacheQuery t₀ d } :
          AuthIdealState TagId Nonce Digest))) <$> ($ᵗ Digest : ProbComp Digest)) := by
    unfold authRFLookup
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rw [show st.responses (t₀.1, t₀.2) = none from (Prod.mk.eta ▸ hnone)]
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
      StateT.run_map, StateT.run_set, map_pure, Functor.map_map]
  rw [hrun]
  rw [probEvent_map, probEvent_map]
  refine ⟨?_, ?_⟩
  · have hext : Pr[((fun p => p.2.responses t₀ = some v₀) ∘ fun d =>
          (d, ({ st with responses := st.responses.cacheQuery t₀ d } :
            AuthIdealState TagId Nonce Digest))) | ($ᵗ Digest : ProbComp Digest)] =
        Pr[fun d => d = v₀ | ($ᵗ Digest : ProbComp Digest)] := by
      refine probEvent_ext fun d _ => ?_
      change (st.responses.cacheQuery t₀ d) t₀ = some v₀ ↔ d = v₀
      rw [QueryCache.cacheQuery_self]
      exact Option.some_inj
    rw [hext, probEvent_eq_eq_probOutput]
    exact hmax v₀
  · rw [probEvent_eq_zero_iff]
    intro d _
    change ¬ (st.responses.cacheQuery t₀ d) t₀ = none
    rw [QueryCache.cacheQuery_self]
    exact Option.some_ne_none d

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- A `responses`-only event of the reader's lookup `mapM` over `hd :: tl` factors as the head
lookup followed by the tail `mapM`: the accumulated tag list never affects the `responses` table,
so the event depends only on the threaded state. -/
private lemma authRFLookup_mapM_cons_responses
    (hd : TagId) (tl : List TagId) (nonce : Nonce)
    (st : AuthIdealState TagId Nonce Digest)
    (P : ((TagId × Nonce) →ₒ Digest).QueryCache → Prop) :
    Pr[fun p => P p.2.responses |
        ((hd :: tl).mapM (fun tag => do
          let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
          pure (tag, dg))).run st] =
      Pr[fun p => P p.2.responses |
        (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) hd nonce).run st >>=
          fun q => (tl.mapM (fun tag => do
            let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
            pure (tag, dg))).run q.2] := by
  classical
  rw [List.mapM_cons]
  simp only [bind_pure_comp, StateT.run_bind, StateT.run_map, bind_map_left]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun q => ?_
  congr 1
  rw [probEvent_map]
  rfl

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- The reader's `mapM` of `authRFLookup` over a nodup list of tags that contains `t₀.1`, run at
nonce `t₀.2`, fills the cache point `t₀` with exactly one fresh uniform draw: starting from
`responses t₀ = none`, the probability the final state has `t₀ ↦ v₀` plus `maxDigestProb` times the
probability `t₀` is still `none` is at most `maxDigestProb`. -/
private lemma authRFLookup_mapM_miss_bound
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (t₀ : TagId × Nonce) (v₀ : Digest) :
    ∀ (tags : List TagId), tags.Nodup → t₀.1 ∈ tags →
      ∀ (st : AuthIdealState TagId Nonce Digest), st.responses t₀ = none →
        Pr[fun p => p.2.responses t₀ = some v₀ |
            (tags.mapM (fun tag => do
              let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                tag t₀.2
              pure (tag, dg))).run st] +
          maxDigestProb *
            Pr[fun p => p.2.responses t₀ = none |
              (tags.mapM (fun tag => do
                let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  tag t₀.2
                pure (tag, dg))).run st] ≤
        maxDigestProb := by
  classical
  intro tags
  induction tags with
  | nil => intro _ hmem; exact absurd hmem (List.not_mem_nil)
  | cons hd tl ih =>
    intro hnodup hmem st hnone
    rw [authRFLookup_mapM_cons_responses (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        hd tl t₀.2 st (fun c => c t₀ = some v₀),
      authRFLookup_mapM_cons_responses (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        hd tl t₀.2 st (fun c => c t₀ = none)]
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    set f := fun tag => do
      let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag t₀.2
      pure (tag, dg) with hf
    by_cases hhd : hd = t₀.1
    · -- Head lookup is at `t₀` itself: a cache miss that draws the single fresh digest.
      subst hhd
      have hlook := authRFLookup_miss_bound (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        maxDigestProb hmax t₀ v₀ st hnone
      -- After the head lookup `t₀` is pinned, so the tail `mapM` keeps `t₀` filled.
      have hpin : ∀ q ∈ support
          ((authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t₀.1 t₀.2).run st),
          ∃ d, q.2.responses t₀ = some d := by
        intro q hq
        unfold authRFLookup at hq
        simp only [StateT.run_bind, StateT.run_get, pure_bind] at hq
        rw [show st.responses (t₀.1, t₀.2) = none from hnone] at hq
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
          StateT.run_map, StateT.run_set, support_bind, support_uniformSample, Set.mem_univ,
          Set.mem_iUnion, support_map, Set.mem_image, support_pure, Set.mem_singleton_iff] at hq
        obtain ⟨i, -, x, rfl, rfl⟩ := hq
        exact ⟨i.1, QueryCache.cacheQuery_self _ _ _⟩
      have hnone0 :
          ∑' q : Digest × AuthIdealState TagId Nonce Digest,
            Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              t₀.1 t₀.2).run st] *
              Pr[fun p => p.2.responses t₀ = none | (tl.mapM f).run q.2] = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun q => ?_
        by_cases hsupp : q ∈ support
            ((authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              t₀.1 t₀.2).run st)
        · obtain ⟨d, hqd⟩ := hpin q hsupp
          have hz : Pr[fun p => p.2.responses t₀ = none | (tl.mapM f).run q.2] = 0 := by
            rw [probEvent_eq_zero_iff]
            intro p hp
            have hpp := authRFLookup_mapM_responses_some_preservesInv (TagId := TagId)
              (Nonce := Nonce) (Digest := Digest) t₀ d t₀.2 tl q.2 hqd p hp
            simp [hpp]
          rw [hz, mul_zero]
        · rw [probOutput_eq_zero _ q hsupp, zero_mul]
      have hsome_le :
          ∑' q : Digest × AuthIdealState TagId Nonce Digest,
            Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              t₀.1 t₀.2).run st] *
              Pr[fun p => p.2.responses t₀ = some v₀ | (tl.mapM f).run q.2] ≤
            Pr[fun p => p.2.responses t₀ = some v₀ |
              (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                t₀.1 t₀.2).run st] := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_le_tsum fun q => ?_
        by_cases hsupp : q ∈ support
            ((authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              t₀.1 t₀.2).run st)
        · obtain ⟨d, hqd⟩ := hpin q hsupp
          by_cases hdv : d = v₀
          · subst hdv
            rw [if_pos hqd]
            exact le_trans (mul_le_mul' le_rfl probEvent_le_one) (le_of_eq (mul_one _))
          · have hz : Pr[fun p => p.2.responses t₀ = some v₀ | (tl.mapM f).run q.2] = 0 := by
              rw [probEvent_eq_zero_iff]
              intro p hp
              have hpp := authRFLookup_mapM_responses_some_preservesInv (TagId := TagId)
                (Nonce := Nonce) (Digest := Digest) t₀ d t₀.2 tl q.2 hqd p hp
              rw [hpp]
              simp [hdv]
            rw [hz, mul_zero]
            exact zero_le
        · rw [probOutput_eq_zero _ q hsupp, zero_mul]
          exact zero_le
      rw [hnone0, mul_zero, add_zero]
      exact le_trans hsome_le hlook.1
    · -- Head lookup is at a tag `≠ t₀.1`: the point `(hd, t₀.2) ≠ t₀`, so `t₀` stays `none`.
      have hmemtl : t₀.1 ∈ tl := by
        rcases List.mem_cons.1 hmem with h | h
        · exact absurd h.symm hhd
        · exact h
      have hnoduptl : tl.Nodup := (List.nodup_cons.1 hnodup).2
      have hne : (hd, t₀.2) ≠ t₀ := by
        intro hc
        exact hhd (congrArg Prod.fst hc)
      have hpres := authRFLookup_responses_none_preservesInv (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) t₀ hd t₀.2 hne
      calc (∑' q : Digest × AuthIdealState TagId Nonce Digest,
              Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                hd t₀.2).run st] *
                Pr[fun p => p.2.responses t₀ = some v₀ | (tl.mapM f).run q.2]) +
            maxDigestProb *
              ∑' q : Digest × AuthIdealState TagId Nonce Digest,
                Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  hd t₀.2).run st] *
                  Pr[fun p => p.2.responses t₀ = none | (tl.mapM f).run q.2]
          = ∑' q : Digest × AuthIdealState TagId Nonce Digest,
              Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                hd t₀.2).run st] *
                (Pr[fun p => p.2.responses t₀ = some v₀ | (tl.mapM f).run q.2] +
                  maxDigestProb *
                    Pr[fun p => p.2.responses t₀ = none | (tl.mapM f).run q.2]) := by
            rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
            refine tsum_congr fun q => ?_
            rw [mul_add]
            congr 1
            rw [mul_left_comm]
        _ ≤ ∑' q : Digest × AuthIdealState TagId Nonce Digest,
              Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                hd t₀.2).run st] * maxDigestProb := by
            refine ENNReal.tsum_le_tsum fun q => ?_
            by_cases hsupp : q ∈ support
                ((authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  hd t₀.2).run st)
            · have hqn : q.2.responses t₀ = none := hpres st hnone q hsupp
              exact mul_le_mul' le_rfl (ih hnoduptl hmemtl q.2 hqn)
            · rw [probOutput_eq_zero _ q hsupp, zero_mul, zero_mul]
        _ = maxDigestProb * ∑' q : Digest × AuthIdealState TagId Nonce Digest,
              Pr[= q | (authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                hd t₀.2).run st] := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun q => ?_
            rw [mul_comm]
        _ ≤ maxDigestProb :=
            le_trans (mul_le_mul' le_rfl tsum_probOutput_le_one) (le_of_eq (mul_one _))

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Single-step random-oracle bound for a cache point `t₀` that is not yet filled: after one
`authRFQueryImpl` query step, the probability that `t₀` ends holding `v₀` plus `maxDigestProb`
times the probability that `t₀` is still unfilled is at most `maxDigestProb`.

A query step fills `t₀` (if at all) with a single fresh uniform `Digest` draw, so the event
`t₀ ↦ v₀` is dominated by `maxDigestProb` times the probability that the step touched `t₀`. -/
private lemma probEvent_authRFQueryImpl_step_core
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (t₀ : TagId × Nonce) (v₀ : Digest)
    (t : AuthOracleSpec TagId Nonce Digest |>.Domain)
    (st : AuthIdealState TagId Nonce Digest)
    (hnone : st.responses t₀ = none) :
    Pr[fun p => p.2.responses t₀ = some v₀ |
        (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run st] +
      maxDigestProb *
        Pr[fun p => p.2.responses t₀ = none |
          (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run st] ≤
      maxDigestProb := by
  classical
  cases t with
  | inl tag =>
    have htag : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (Sum.inl tag)).run st =
        (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag).run st :=
      rfl
    rw [htag]
    -- Reduce the tag handler to a `nonce`-bind whose body either fills `t₀` or leaves it `none`.
    have hrun : (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        tag).run st =
        (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
          (match st.responses (tag, nonce) with
            | some out => pure
                (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                  ({ responses := st.responses,
                     honestOutputs :=
                       insert (tag,
                         ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                         st.honestOutputs,
                     readerForged := st.readerForged } :
                    AuthIdealState TagId Nonce Digest))
            | none => (($ᵗ Digest : ProbComp Digest) >>= fun out => pure
                (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                  ({ responses := st.responses.cacheQuery (tag, nonce) out,
                     honestOutputs :=
                       insert (tag,
                         ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                         st.honestOutputs,
                     readerForged := st.readerForged } :
                    AuthIdealState TagId Nonce Digest)))) :
            ProbComp (TagTranscript Nonce Digest × AuthIdealState TagId Nonce Digest)) := by
      unfold authIdealTagQueryImpl
      simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
        monadLift_eq_self, bind_map_left]
      refine bind_congr fun nonce => ?_
      cases hresp : st.responses (tag, nonce) with
      | some out =>
        simp only [StateT.run_map, StateT.run_set, map_pure]
      | none =>
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
          StateT.run_map, StateT.run_set, map_pure, Functor.map_map]
    rw [hrun]
    -- Per-`nonce` bounds on the two events.
    have hkey : ∀ nonce : Nonce, (tag, nonce) = t₀ ↔ (tag = t₀.1 ∧ nonce = t₀.2) := by
      intro nonce
      constructor
      · intro h; exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · intro ⟨h1, h2⟩; exact Prod.ext h1 h2
    -- Probability of `t₀ ↦ v₀` after the bind, bounded per `nonce`.
    have hsome :
        Pr[fun p => p.2.responses t₀ = some v₀ |
            (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
              (match st.responses (tag, nonce) with
                | some out => pure
                    (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                      ({ responses := st.responses,
                         honestOutputs :=
                           insert (tag,
                             ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                             st.honestOutputs,
                         readerForged := st.readerForged } :
                        AuthIdealState TagId Nonce Digest))
                | none => (($ᵗ Digest : ProbComp Digest) >>= fun out => pure
                    (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                      ({ responses := st.responses.cacheQuery (tag, nonce) out,
                         honestOutputs :=
                           insert (tag,
                             ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                             st.honestOutputs,
                         readerForged := st.readerForged } :
                        AuthIdealState TagId Nonce Digest)))) :
                ProbComp (TagTranscript Nonce Digest × AuthIdealState TagId Nonce Digest))] ≤
          ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (tag, nonce) = t₀ then maxDigestProb else 0) := by
      rw [probEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun nonce => mul_le_mul' le_rfl ?_
      by_cases hk : (tag, nonce) = t₀
      · rw [if_pos hk]
        rw [show st.responses (tag, nonce) = none from hk ▸ hnone]
        rw [probEvent_bind_eq_tsum]
        calc ∑' out : Digest, Pr[= out | ($ᵗ Digest : ProbComp Digest)] *
                Pr[fun p => p.2.responses t₀ = some v₀ |
                  (pure (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                    ({ responses := st.responses.cacheQuery (tag, nonce) out,
                       honestOutputs :=
                         insert (tag,
                           ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                           st.honestOutputs,
                       readerForged := st.readerForged } :
                      AuthIdealState TagId Nonce Digest)) :
                    ProbComp (TagTranscript Nonce Digest × AuthIdealState TagId Nonce Digest))]
            = ∑' out : Digest,
                (if out = v₀ then Pr[= out | ($ᵗ Digest : ProbComp Digest)] else 0) := by
              refine tsum_congr fun out => ?_
              rw [probEvent_pure]
              have hco : (st.responses.cacheQuery (tag, nonce) out) t₀ = some out := by
                rw [← hk, QueryCache.cacheQuery_self]
              by_cases hov : out = v₀
              · subst hov
                simp [hco]
              · simp only [hco]
                rw [if_neg (by simp [hov]), if_neg hov, mul_zero]
          _ = Pr[= v₀ | ($ᵗ Digest : ProbComp Digest)] := by
              rw [tsum_ite_eq]
          _ ≤ maxDigestProb := hmax v₀
      · rw [if_neg hk]
        have hne : t₀ ≠ (tag, nonce) := fun h => hk h.symm
        cases hresp : st.responses (tag, nonce) with
        | some out =>
          rw [probEvent_pure]
          simp [hnone]
        | none =>
          rw [probEvent_bind_eq_tsum]
          refine le_of_le_of_eq (le_refl _) ?_
          refine ENNReal.tsum_eq_zero.mpr fun out => ?_
          rw [probEvent_pure]
          simp [QueryCache.cacheQuery_of_ne _ _ hne, hnone]
    -- Probability of `t₀` staying `none` after the bind, bounded per `nonce`.
    have hnoneEv :
        Pr[fun p => p.2.responses t₀ = none |
            (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
              (match st.responses (tag, nonce) with
                | some out => pure
                    (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                      ({ responses := st.responses,
                         honestOutputs :=
                           insert (tag,
                             ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                             st.honestOutputs,
                         readerForged := st.readerForged } :
                        AuthIdealState TagId Nonce Digest))
                | none => (($ᵗ Digest : ProbComp Digest) >>= fun out => pure
                    (({ nonce := nonce, auth := out } : TagTranscript Nonce Digest),
                      ({ responses := st.responses.cacheQuery (tag, nonce) out,
                         honestOutputs :=
                           insert (tag,
                             ({ nonce := nonce, auth := out } : TagTranscript Nonce Digest))
                             st.honestOutputs,
                         readerForged := st.readerForged } :
                        AuthIdealState TagId Nonce Digest)))) :
                ProbComp (TagTranscript Nonce Digest × AuthIdealState TagId Nonce Digest))] ≤
          ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1) := by
      rw [probEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun nonce => mul_le_mul' le_rfl ?_
      by_cases hk : (tag, nonce) = t₀
      · rw [if_pos hk]
        rw [show st.responses (tag, nonce) = none from hk ▸ hnone]
        rw [probEvent_bind_eq_tsum]
        refine le_of_le_of_eq (le_refl _) ?_
        refine ENNReal.tsum_eq_zero.mpr fun out => ?_
        rw [probEvent_pure]
        have hcache : (st.responses.cacheQuery (tag, nonce) out) t₀ = some out := by
          rw [← hk, QueryCache.cacheQuery_self]
        simp [hcache]
      · rw [if_neg hk]
        exact probEvent_le_one
    -- Combine: total `≤ maxDigestProb * ∑' nonce, Pr[= nonce] ≤ maxDigestProb`.
    refine le_trans (add_le_add hsome (mul_le_mul' le_rfl hnoneEv)) ?_
    have hcollapse :
        (∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (tag, nonce) = t₀ then maxDigestProb else 0)) +
          maxDigestProb * ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1) =
          maxDigestProb * ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] := by
      have hterm : ∀ nonce : Nonce,
          (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
              (if (tag, nonce) = t₀ then maxDigestProb else 0)) +
            maxDigestProb * (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
              (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1)) =
            maxDigestProb * Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] := by
        intro nonce
        by_cases hk : (tag, nonce) = t₀ <;> simp [hk, mul_comm]
      calc (∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
              (if (tag, nonce) = t₀ then maxDigestProb else 0)) +
            maxDigestProb * ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
              (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1)
          = (∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
                (if (tag, nonce) = t₀ then maxDigestProb else 0)) +
              ∑' nonce : Nonce, maxDigestProb *
                (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
                  (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1)) := by
            rw [ENNReal.tsum_mul_left]
        _ = ∑' nonce : Nonce,
              ((Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
                  (if (tag, nonce) = t₀ then maxDigestProb else 0)) +
                maxDigestProb * (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
                  (if (tag, nonce) = t₀ then (0 : ℝ≥0∞) else 1))) := by
            rw [ENNReal.tsum_add]
        _ = ∑' nonce : Nonce, maxDigestProb * Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] :=
            tsum_congr hterm
        _ = maxDigestProb * ∑' nonce : Nonce, Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] := by
            rw [ENNReal.tsum_mul_left]
    rw [hcollapse]
    exact le_trans (mul_le_mul' le_rfl tsum_probOutput_le_one) (le_of_eq (mul_one _))
  | inr transcript =>
    have hrd : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (Sum.inr transcript)).run st =
        (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript).run st :=
      rfl
    rw [hrd]
    -- The reader handler runs the lookup `mapM`, then a `get`/`set` that only touches
    -- `readerForged`; hence the `responses`-field events factor through the `mapM`.
    have hmapM_run : ∀ (P : ((TagId × Nonce) →ₒ Digest).QueryCache → Prop),
        Pr[fun p => P p.2.responses |
            (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              transcript).run st] =
          Pr[fun p => P p.2.responses |
            ((Finset.univ : Finset TagId).toList.mapM (fun tag => do
              let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                tag transcript.nonce
              pure (tag, dg))).run st] := by
      intro P
      unfold authRFReaderQueryImpl
      simp only [bind_pure_comp, StateT.run_bind]
      rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
      refine tsum_congr fun p => ?_
      rw [mul_comm]
      simp only [StateT.run_get, pure_bind, StateT.run_map, StateT.run_set, map_pure,
        probEvent_pure]
      by_cases hP : P p.2.responses <;> simp [hP]
    have heq1 := hmapM_run (fun c => c t₀ = some v₀)
    have heq2 := hmapM_run (fun c => c t₀ = none)
    refine heq1 ▸ heq2 ▸ ?_
    by_cases hnonce : transcript.nonce = t₀.2
    · -- Here `transcript.nonce = t₀.2`, so the lookup `mapM` over `Finset.univ.toList` includes a
      -- cache-miss lookup at `t₀ = (t₀.1, t₀.2)`, drawing one fresh uniform digest that pins `t₀`.
      rw [hnonce]
      exact authRFLookup_mapM_miss_bound (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        maxDigestProb hmax t₀ v₀ (Finset.univ : Finset TagId).toList
        (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _)) st hnone
    · -- The lookup `mapM` is at a nonce `≠ t₀.2`, so `t₀` is never touched: stays `none`.
      have hpres :=
        authRFLookup_mapM_responses_none_preservesInv (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) t₀ transcript.nonce hnonce (Finset.univ : Finset TagId).toList
      have hsome0 :
          Pr[fun p => p.2.responses t₀ = some v₀ |
            ((Finset.univ : Finset TagId).toList.mapM (fun tag => do
              let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                tag transcript.nonce
              pure (tag, dg))).run st] = 0 := by
        rw [probEvent_eq_zero_iff]
        intro p hp
        have hpn := hpres st hnone p hp
        rw [hpn]
        simp
      have hnone1 :
          Pr[fun p => p.2.responses t₀ = none |
            ((Finset.univ : Finset TagId).toList.mapM (fun tag => do
              let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                tag transcript.nonce
              pure (tag, dg))).run st] ≤ 1 := probEvent_le_one
      rw [hsome0, zero_add]
      exact le_trans (mul_le_mul' le_rfl hnone1) (le_of_eq (mul_one _))


omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Single-point random-oracle bound: a fixed cache point `t₀` is filled by at most one uniform
draw over the whole `authRFQueryImpl` simulation, so it ends holding any fixed digest `v₀` with
probability at most `maxDigestProb`. -/
private lemma probEvent_authRFQueryImpl_responses_eq_le
    {α : Type}
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (adversary : OracleComp (AuthOracleSpec TagId Nonce Digest) α)
    (t₀ : TagId × Nonce) (v₀ : Digest)
    (st : AuthIdealState TagId Nonce Digest)
    (hnone : st.responses t₀ = none) :
    Pr[fun z => z.2.responses t₀ = some v₀ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run st] ≤ maxDigestProb := by
  classical
  -- State-indexed bound: `1` once `t₀ ↦ v₀`, `maxDigestProb` while `t₀` is unfilled, `0` otherwise.
  set stbound : AuthIdealState TagId Nonce Digest → ℝ≥0∞ := fun st =>
    if st.responses t₀ = some v₀ then (1 : ℝ≥0∞)
    else if st.responses t₀ = none then maxDigestProb else 0 with hstbound
  -- General claim: the win probability from any reachable state is bounded by `stbound`.
  have hgen : ∀ (adv : OracleComp (AuthOracleSpec TagId Nonce Digest) α)
      (s : AuthIdealState TagId Nonce Digest),
      Pr[fun z => z.2.responses t₀ = some v₀ |
          (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
            adv).run s] ≤ stbound s := by
    intro adv
    induction adv using OracleComp.inductionOn with
    | pure x =>
      intro s
      simp only [simulateQ_pure, StateT.run_pure, probEvent_pure]
      by_cases hv : s.responses t₀ = some v₀
      · simp only [hv, if_true, hstbound]
        simp
      · simp only [hv, if_false]
        simp only [hstbound]
        positivity
    | query_bind t oa ih =>
      intro s
      simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind, monadLift_self]
      rw [probEvent_bind_eq_tsum]
      -- Bound each continuation by the inductive hypothesis, then bound the step sum.
      have hstep_le :
          ∑' p, Pr[= p |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s] *
            Pr[fun z => z.2.responses t₀ = some v₀ |
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (oa p.1)).run p.2] ≤
            ∑' p, Pr[= p |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s] *
              stbound p.2 := by
        refine ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl (ih p.1 p.2)
      refine le_trans hstep_le ?_
      -- Three cases on the value held at `t₀` in the pre-state `s`.
      by_cases hsv : s.responses t₀ = some v₀
      · -- `t₀` already holds `v₀`: `stbound s = 1`; LEMMA 1 keeps it so, sum `≤ 1`.
        have hpres :=
          authRFQueryImpl_responses_some_preservesInv (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) t₀ v₀ t s hsv
        have hbound : ∀ p ∈ support
            ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s),
            stbound p.2 = 1 := by
          intro p hp
          simp only [hstbound, hpres p hp, if_true]
        calc ∑' p, Pr[= p |
                (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s] *
              stbound p.2
            = ∑' p, Pr[= p |
                (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s] *
                1 := by
              refine tsum_congr fun p => ?_
              by_cases hp : p ∈ support
                  ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    t).run s)
              · rw [hbound p hp]
              · rw [probOutput_eq_zero_of_not_mem_support hp]; simp
          _ ≤ 1 := by simp only [mul_one]; exact tsum_probOutput_le_one
          _ = stbound s := by simp only [hstbound, hsv, if_true]
      · by_cases hsn : s.responses t₀ = none
        · -- `t₀` is unfilled: `stbound s = maxDigestProb`; this is the core per-step bound.
          have hsplit : ∀ p : (AuthOracleSpec TagId Nonce Digest).Range t ×
              AuthIdealState TagId Nonce Digest, stbound p.2 ≤
              (if p.2.responses t₀ = some v₀ then (1 : ℝ≥0∞) else 0) +
                maxDigestProb * (if p.2.responses t₀ = none then (1 : ℝ≥0∞) else 0) := by
            intro p
            simp only [hstbound]
            by_cases h1 : p.2.responses t₀ = some v₀
            · simp [h1]
            · by_cases h2 : p.2.responses t₀ = none
              · simp [h2]
              · simp [h1, h2]
          have hsum_le :
              ∑' p, Pr[= p |
                  (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    t).run s] * stbound p.2 ≤
                ∑' p, Pr[= p |
                  (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    t).run s] *
                  ((if p.2.responses t₀ = some v₀ then (1 : ℝ≥0∞) else 0) +
                    maxDigestProb * (if p.2.responses t₀ = none then (1 : ℝ≥0∞) else 0)) :=
            ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl (hsplit p)
          refine le_trans hsum_le ?_
          -- Distribute the sum into the two probability events.
          have hdist :
              ∑' p, Pr[= p |
                  (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    t).run s] *
                  ((if p.2.responses t₀ = some v₀ then (1 : ℝ≥0∞) else 0) +
                    maxDigestProb * (if p.2.responses t₀ = none then (1 : ℝ≥0∞) else 0)) =
                Pr[fun p => p.2.responses t₀ = some v₀ |
                    (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                      t).run s] +
                  maxDigestProb *
                    Pr[fun p => p.2.responses t₀ = none |
                      (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                        t).run s] := by
            rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite,
              ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
            refine tsum_congr fun p => ?_
            by_cases h1 : p.2.responses t₀ = some v₀ <;>
              by_cases h2 : p.2.responses t₀ = none <;>
              simp [h1, h2, mul_comm]
          rw [hdist]
          have hcore :=
            probEvent_authRFQueryImpl_step_core (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) maxDigestProb hmax t₀ v₀ t s hsn
          have hgoal : stbound s = maxDigestProb := by
            simp only [hstbound, hsn]
            simp
          rw [hgoal]
          exact hcore
        · -- `t₀` holds some `d ≠ v₀`: `stbound s = 0`; LEMMA 1 keeps `t₀ ↦ d`, sum `= 0`.
          obtain ⟨d, hd⟩ : ∃ d, s.responses t₀ = some d := by
            cases hc : s.responses t₀ with
            | none => exact absurd hc hsn
            | some d => exact ⟨d, rfl⟩
          have hpres :=
            authRFQueryImpl_responses_some_preservesInv (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) t₀ d t s hd
          have hzero : ∀ p ∈ support
              ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                t).run s), stbound p.2 = 0 := by
            intro p hp
            have hpd := hpres p hp
            have hdv : d ≠ v₀ := by
              rintro rfl
              exact hsv hd
            have hne : p.2.responses t₀ ≠ some v₀ := by
              rw [hpd]
              simp [hdv]
            simp only [hstbound, hpd]
            simp [hdv]
          have hsum0 :
              ∑' p, Pr[= p |
                  (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    t).run s] * stbound p.2 = 0 := by
            refine ENNReal.tsum_eq_zero.mpr fun p => ?_
            by_cases hp : p ∈ support
                ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) t).run s)
            · rw [hzero p hp, mul_zero]
            · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul]
          rw [hsum0]
          exact zero_le
  have hfinal : stbound st = maxDigestProb := by
    simp only [hstbound, hnone]
    simp
  exact (hgen adversary st).trans (le_of_eq hfinal)

/-- The reader's per-tag lookup pass: run `authRFLookup` at `nonce` for every tag in `tags`,
collecting each looked-up `(tag, digest)` pair. This is the `responses`-touching core of
`authRFReaderQueryImpl`, isolated so that the collision argument can reason about it directly. -/
noncomputable def authRFReaderLookups
    (nonce : Nonce) (tags : List TagId) :
    StateT (AuthIdealState TagId Nonce Digest) ProbComp (List (TagId × Digest)) :=
  tags.mapM (fun tag => do
    let dg ← authRFLookup (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
    pure (tag, dg))

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- Every looked-up pair produced by `authRFReaderLookups` lands in the final cache: if `(tag, d)`
occurs in the result list, the final `responses` table holds `(tag, nonce) ↦ d`. Each lookup pins
its own point, and the tail `mapM` preserves it. -/
private lemma authRFLookup_mapM_pairs_responses
    (nonce : Nonce) (tags : List TagId) (st : AuthIdealState TagId Nonce Digest) :
    ∀ z ∈ support ((authRFReaderLookups (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        nonce tags).run st),
      ∀ p ∈ z.1, z.2.responses (p.1, nonce) = some p.2 := by
  unfold authRFReaderLookups
  induction tags generalizing st with
  | nil =>
    intro z hz
    simp only [List.mapM_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    intro p hp
    simp at hp
  | cons hd tl ih =>
    intro z hz
    rw [List.mapM_cons] at hz
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_map, support_bind, support_map,
      Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨r, ⟨lk, hlk, rfl⟩, w, hw, rfl⟩ := hz
    -- The head lookup at `hd` pins `(hd, nonce) ↦ lk.1` in `lk.2`.
    have hlook : lk.2.responses (hd, nonce) = some lk.1 := by
      unfold authRFLookup at hlk
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hlk
      cases hresp : st.responses (hd, nonce) with
      | some out =>
        simp only [hresp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hlk
        rcases hlk with rfl
        exact hresp
      | none =>
        simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
          bind_pure_comp, StateT.run_map, StateT.run_set, support_bind, support_uniformSample,
          Set.mem_univ, Set.mem_iUnion, support_map, Set.mem_image, support_pure,
          Set.mem_singleton_iff] at hlk
        obtain ⟨i, -, x, rfl, rfl⟩ := hlk
        exact QueryCache.cacheQuery_self _ _ _
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · -- `p` is the head pair `(hd, lk.1)`: the tail `mapM` keeps `(hd, nonce)` pinned.
      exact authRFLookup_mapM_responses_some_preservesInv (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (hd, nonce) lk.1 nonce tl lk.2 hlook w hw
    · -- `p` is in the tail pairs: apply the induction hypothesis.
      exact ih lk.2 w hw p hp'

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- `authRFReaderLookups` only writes the `responses` table: the observable logs `honestOutputs`
and `readerForged` are untouched by every reachable outcome. -/
lemma authRFLookup_mapM_logs_eq
    (nonce : Nonce) (tags : List TagId) (st : AuthIdealState TagId Nonce Digest) :
    ∀ z ∈ support ((authRFReaderLookups (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        nonce tags).run st),
      z.2.honestOutputs = st.honestOutputs ∧ z.2.readerForged = st.readerForged := by
  unfold authRFReaderLookups
  induction tags generalizing st with
  | nil =>
    intro z hz
    simp only [List.mapM_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact ⟨rfl, rfl⟩
  | cons hd tl ih =>
    intro z hz
    rw [List.mapM_cons] at hz
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_map, support_bind, support_map,
      Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨r, ⟨lk, hlk, rfl⟩, w, hw, rfl⟩ := hz
    have hhead : lk.2.honestOutputs = st.honestOutputs ∧ lk.2.readerForged = st.readerForged := by
      unfold authRFLookup at hlk
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hlk
      cases hresp : st.responses (hd, nonce) with
      | some out =>
        simp only [hresp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hlk
        rcases hlk with rfl
        exact ⟨rfl, rfl⟩
      | none =>
        simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
          bind_pure_comp, StateT.run_map, StateT.run_set, support_bind, support_uniformSample,
          Set.mem_univ, Set.mem_iUnion, support_map, Set.mem_image, support_pure,
          Set.mem_singleton_iff] at hlk
        obtain ⟨i, -, x, rfl, rfl⟩ := hlk
        exact ⟨rfl, rfl⟩
    obtain ⟨htail₁, htail₂⟩ := ih lk.2 w hw
    exact ⟨htail₁.trans hhead.1, htail₂.trans hhead.2⟩

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Per-reader-step collision bound. When the pre-state has no recorded forgeries and every cached
cell in the queried nonce's column belongs to `honestOutputs`, one `authRFReaderQueryImpl` step
records a forgery with probability at most `|TagId| * maxDigestProb`.

A reader step makes one fresh random-oracle draw per tag at the transcript's nonce. A cached cell
in that column cannot become a forgery: a match against `transcript.auth` would place
`(tag, transcript)` inside `honestOutputs`, which forgeries exclude. An uncached cell can match the
adversary-chosen authenticator with probability at most `maxDigestProb`. -/
lemma authRFReaderStep_forge_le
    (transcript : TagTranscript Nonce Digest)
    (st : AuthIdealState TagId Nonce Digest)
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (hforged : st.readerForged = ∅)
    (hcol : ∀ tag : TagId, ∀ d : Digest,
      st.responses (tag, transcript.nonce) = some d →
        (tag, ⟨transcript.nonce, d⟩) ∈ st.honestOutputs) :
    Pr[fun z => z.2.readerForged ≠ ∅ |
        (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript).run st] ≤
      (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
  classical
  -- Abbreviate the per-tag lookup pass and the forged-tag set extracted from its result.
  set lookups := (authRFReaderLookups (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    transcript.nonce (Finset.univ : Finset TagId).toList).run st with hlookups
  set newForged : List (TagId × Digest) → Finset TagId := fun pairs =>
    ((pairs.filter fun p => decide (p.2 = transcript.auth ∧
      (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset with hnewForged
  -- The reader run is the lookup pass followed by a pure log update; push the event through.
  have hmap :
      Pr[fun z => z.2.readerForged ≠ ∅ |
          (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            transcript).run st] =
        Pr[fun mp : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
            (mp.2.readerForged ∪
              (((mp.1.filter fun p => decide (p.2 = transcript.auth ∧
                (p.1, transcript) ∉ mp.2.honestOutputs)).map Prod.fst).toFinset.image
                  (·, transcript))) ≠ ∅ | lookups] := by
    rw [hlookups]
    unfold authRFReaderQueryImpl authRFReaderLookups
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map,
      StateT.run_set, map_pure]
    rw [probEvent_map]
    rfl
  rw [hmap]
  -- Forge ⇒ some tag lies in `newForged`, which forces a cached-or-fresh match at its column.
  have hstep :
      Pr[fun mp : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
          (mp.2.readerForged ∪
            (((mp.1.filter fun p => decide (p.2 = transcript.auth ∧
              (p.1, transcript) ∉ mp.2.honestOutputs)).map Prod.fst).toFinset.image
                (·, transcript))) ≠ ∅ | lookups] ≤
        Pr[fun mp => ∃ tag ∈ (Finset.univ : Finset TagId), tag ∈ newForged mp.1 | lookups] := by
    refine probEvent_mono fun mp hmp hne => ?_
    obtain ⟨hho, hrf⟩ := authRFLookup_mapM_logs_eq (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList st mp hmp
    rw [hho, hrf, hforged, Finset.empty_union] at hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨tag, htag, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨tag, Finset.mem_univ tag, htag⟩
  refine le_trans hstep ?_
  refine le_trans (probEvent_exists_finset_le_sum (Finset.univ : Finset TagId) lookups
    (fun tag mp => tag ∈ newForged mp.1)) ?_
  -- Per-tag: cached cells cannot forge; uncached cells match with probability ≤ maxDigestProb.
  have hper : ∀ tag : TagId,
      Pr[fun mp => tag ∈ newForged mp.1 | lookups] ≤ maxDigestProb := by
    intro tag
    by_cases hcached : ∃ d, st.responses (tag, transcript.nonce) = some d
    · -- Cached column cell: a match would land in `honestOutputs`, so it is never forged.
      obtain ⟨d, hd⟩ := hcached
      refine le_trans (le_of_eq ?_) zero_le
      rw [probEvent_eq_zero_iff]
      intro mp hmp hmem
      simp only [hnewForged, List.mem_toFinset, List.mem_map, List.mem_filter,
        decide_eq_true_eq] at hmem
      obtain ⟨p, ⟨hpmem, hpauth, hpnh⟩, rfl⟩ := hmem
      have hpresp := authRFLookup_mapM_pairs_responses (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList st mp hmp p hpmem
      -- The cached cell keeps its digest `d`; a forgery would need `p.2 = d = transcript.auth`.
      have hcell : st.responses (p.1, transcript.nonce) = some d := hd
      have hpd : mp.2.responses (p.1, transcript.nonce) = some d :=
        authRFLookup_mapM_responses_some_preservesInv (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (p.1, transcript.nonce) d transcript.nonce
          (Finset.univ : Finset TagId).toList st hcell mp hmp
      have hpd' : p.2 = d := (Option.some.injEq _ _).mp (hpresp.symm.trans hpd)
      have hhonest : (p.1, transcript) ∈ st.honestOutputs := by
        have h := hcol p.1 d hcell
        rw [← hpd', hpauth, show (⟨transcript.nonce, transcript.auth⟩ :
          TagTranscript Nonce Digest) = transcript from rfl] at h
        exact h
      exact hpnh hhonest
    · -- Uncached column cell: bounded by the single-step random-oracle bound.
      simp only [not_exists] at hcached
      have hnone : st.responses (tag, transcript.nonce) = none := by
        cases hc : st.responses (tag, transcript.nonce) with
        | none => rfl
        | some d => exact absurd hc (hcached d)
      have hstepcore := probEvent_authRFQueryImpl_step_core (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) maxDigestProb hmax (tag, transcript.nonce) transcript.auth
        (Sum.inr transcript) st hnone
      have hreaderResp :
          Pr[fun mp : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
              mp.2.responses (tag, transcript.nonce) = some transcript.auth | lookups] ≤
            maxDigestProb := by
        have hrun : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (Sum.inr transcript)).run st =
            (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              transcript).run st := rfl
        have hpush :
            Pr[fun p => p.2.responses (tag, transcript.nonce) = some transcript.auth |
                (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  transcript).run st] =
              Pr[fun mp : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
                mp.2.responses (tag, transcript.nonce) = some transcript.auth | lookups] := by
          rw [hlookups]
          unfold authRFReaderQueryImpl authRFReaderLookups
          simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map,
            StateT.run_set, map_pure]
          rw [probEvent_map]
          rfl
        rw [← hpush, ← hrun]
        exact le_trans (le_add_right le_rfl) hstepcore
      refine le_trans (probEvent_mono fun mp hmp hmem => ?_) hreaderResp
      simp only [hnewForged, List.mem_toFinset, List.mem_map, List.mem_filter,
        decide_eq_true_eq] at hmem
      obtain ⟨p, ⟨hpmem, hpauth, _⟩, rfl⟩ := hmem
      have hpresp := authRFLookup_mapM_pairs_responses (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList st mp hmp p hpmem
      rw [hpresp, hpauth]
  exact le_trans (Finset.sum_le_sum fun tag _ => hper tag)
    (le_of_eq (by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]))

end Theorems

end PRFTagReader
