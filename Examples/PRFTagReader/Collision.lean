/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.Collision.ForgeStep

/-!
# PRF Tag/Reader Protocol — Collision Bound

The collision-bound theorems for the random-function authentication world: the
nonce-distinctness machinery (`pNonce`, `HasDistinctReaderNonces`), the forge-event induction
over the adversary, and the collision-bound theorems culminating in
`authExp_le_prfAdvantage_add_collisionBound` and its uniform-digest variant.

The per-step random-oracle cache and forge-bound infrastructure these proofs consume lives in
`Examples.PRFTagReader.Collision.ForgeStep`.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section Theorems

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- Per-nonce reader-query predicate on the authentication oracle interface. `pNonce n` holds of a
reader query exactly when its transcript carries the nonce `n`, and never holds of a tag query.
Bounding the number of `pNonce n`-queries by `1` for every `n` expresses that the adversary's
reader queries use pairwise-distinct nonces. -/
def pNonce (n : Nonce) : (AuthOracleSpec TagId Nonce Digest).Domain → Prop :=
  fun i => match i with
    | Sum.inr tr => tr.nonce = n
    | Sum.inl _ => False

instance pNonceDecidable (n : Nonce) :
    DecidablePred (pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n) := by
  intro i
  cases i with
  | inr tr => exact (inferInstance : Decidable (tr.nonce = n))
  | inl _ => exact (inferInstance : Decidable False)

/-- The adversary's reader queries use pairwise-distinct nonces: every nonce `n` is carried by at
most one reader query. This is the public hypothesis under which the random-function collision
bound is fully proven (`authRFExp_le_collisionBound_of_distinctReaderNonces` and its uniform
specialization). -/
def HasDistinctReaderNonces (adversary : AuthAdversary TagId Nonce Digest) : Prop :=
  ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pNonce n) 1

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] in
/-- `HasDistinctReaderNonces` unfolds definitionally to a per-nonce reader-query bound: it holds
exactly when, for every nonce `n`, at most one reader query carries `n`. Use this lemma to
discharge the hypothesis from a per-nonce `IsQueryBoundP` family, or to peel it back when a proof
needs the underlying bound directly. -/
lemma hasDistinctReaderNonces_iff (adversary : AuthAdversary TagId Nonce Digest) :
    HasDistinctReaderNonces adversary ↔
      ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pNonce n) 1 :=
  Iff.rfl

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Every `pNonce n`-query is a reader query: `pNonce n` is false on tag (`Sum.inl`) queries and,
on reader (`Sum.inr`) queries, refines `Sum.isRight`. -/
lemma pNonce_imp_isRight (n : Nonce) (t : (AuthOracleSpec TagId Nonce Digest).Domain) :
    pNonce (TagId := TagId) (Digest := Digest) n t → t.isRight := by
  cases t with
  | inl x => exact fun h => (h : (False : Prop)).elim
  | inr tr => exact fun _ => rfl

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Intro lemma: an adversary making at most one reader query has pairwise-distinct reader nonces.
A single reader query cannot collide with itself, so the per-nonce bound holds for free; this is
the common case where no bespoke distinctness argument is needed. Adversaries with no reader
queries also qualify — feed `hq.mono (Nat.zero_le 1)`. -/
theorem hasDistinctReaderNonces_of_readerBound
    (adversary : AuthAdversary TagId Nonce Digest)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) 1) :
    HasDistinctReaderNonces adversary := fun n =>
  OracleComp.IsQueryBoundP.of_imp (pNonce_imp_isRight n) hq

/-- Coupled invariant carried by the random-function collision induction. A state `st` satisfies
`forgeInv adversary st` when no forgery has been recorded yet and every cached cell at column
`nonce` is either an honest tag output or sits in a column the residual adversary will never query
again (`IsQueryBoundP adversary (pNonce nonce) 0`). Under pairwise-distinct reader nonces, the
second disjunct fails exactly at the column of the next reader query, so all of that column's
cached cells are honest — the hypothesis needed for the per-step bound. -/
private def forgeInv (adversary : AuthAdversary TagId Nonce Digest)
    (st : AuthIdealState TagId Nonce Digest) : Prop :=
  st.readerForged = ∅ ∧
    ∀ (tag : TagId) (nonce : Nonce) (d : Digest), st.responses (tag, nonce) = some d →
      ((tag, (⟨nonce, d⟩ : TagTranscript Nonce Digest)) ∈ st.honestOutputs ∨
        OracleComp.IsQueryBoundP adversary (pNonce nonce) 0)

omit [Fintype TagId] [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Column-indexed cell invariant of the random-function tag oracle. With a fixed per-column
predicate `Q`, a tag step preserves both an empty forgery log and the property that every cached
cell is honest or sits in a `Q`-column: a freshly cached cell is the honest transcript just
emitted, and every pre-existing cell keeps its disjunct under cache growth. -/
private lemma authIdealTagStep_cell_inv
    (tag : TagId) (st : AuthIdealState TagId Nonce Digest)
    (Q : Nonce → Prop)
    (hread : st.readerForged = ∅)
    (hcell : ∀ (t' : TagId) (n : Nonce) (d : Digest),
      st.responses (t', n) = some d →
        ((t', (⟨n, d⟩ : TagTranscript Nonce Digest)) ∈ st.honestOutputs ∨ Q n)) :
    ∀ z ∈ support ((authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) tag).run st),
      z.2.readerForged = ∅ ∧
        ∀ (t' : TagId) (n : Nonce) (d : Digest), z.2.responses (t', n) = some d →
          ((t', (⟨n, d⟩ : TagTranscript Nonce Digest)) ∈ z.2.honestOutputs ∨ Q n) := by
  intro z hz
  unfold authIdealTagQueryImpl at hz
  simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    monadLift_eq_self, bind_map_left, support_bind, support_uniformSample, Set.mem_univ,
    Set.iUnion_true, Set.mem_iUnion] at hz
  rcases hz with ⟨nonce, hz⟩
  cases hresp : st.responses (tag, nonce) with
  | none =>
    simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
      StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
      support_uniformSample, Set.image_univ, Set.mem_range] at hz
    obtain ⟨auth, rfl⟩ := hz
    refine ⟨hread, ?_⟩
    intro t' n d hlookup
    by_cases hkey : (t', n) = (tag, nonce)
    · -- The freshly cached cell is the honest transcript just emitted.
      cases hkey
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hlookup
      subst hlookup
      exact Or.inl (Finset.mem_insert_self _ _)
    · -- A pre-existing cell keeps its disjunct; honest membership survives the `insert`.
      have hlookup' : st.responses (t', n) = some d := by
        simpa [QueryCache.cacheQuery_of_ne (cache := st.responses) auth hkey] using hlookup
      rcases hcell t' n d hlookup' with hh | hq
      · exact Or.inl (Finset.mem_insert_of_mem hh)
      · exact Or.inr hq
  | some out =>
    simp only [hresp, StateT.run_map, StateT.run_set, map_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl
    refine ⟨hread, ?_⟩
    intro t' n d hlookup
    rcases hcell t' n d hlookup with hh | hq
    · exact Or.inl (Finset.mem_insert_of_mem hh)
    · exact Or.inr hq

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- `authRFReaderLookups` at column `nm` never disturbs cells outside that column: any cached cell
at a nonce `n ≠ nm` keeps its pre-step value in every reachable outcome. -/
private lemma authRFLookup_mapM_responses_eq_of_ne_column
    (nm : Nonce) (tags : List TagId) (t' : TagId) (n : Nonce) (hne : n ≠ nm)
    (st : AuthIdealState TagId Nonce Digest) :
    ∀ z ∈ support ((authRFReaderLookups (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        nm tags).run st),
      z.2.responses (t', n) = st.responses (t', n) := by
  unfold authRFReaderLookups
  induction tags generalizing st with
  | nil =>
    intro z hz
    simp only [List.mapM_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    rfl
  | cons hd tl ih =>
    intro z hz
    rw [List.mapM_cons] at hz
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_map, support_bind, support_map,
      Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨r, ⟨lk, hlk, rfl⟩, w, hw, rfl⟩ := hz
    have hhead : lk.2.responses (t', n) = st.responses (t', n) := by
      unfold authRFLookup at hlk
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hlk
      cases hresp : st.responses (hd, nm) with
      | some out =>
        simp only [hresp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hlk
        rcases hlk with rfl
        rfl
      | none =>
        simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
          bind_pure_comp, StateT.run_map, StateT.run_set, support_bind, support_uniformSample,
          Set.mem_univ, Set.mem_iUnion, support_map, Set.mem_image, support_pure,
          Set.mem_singleton_iff] at hlk
        obtain ⟨i, -, x, rfl, rfl⟩ := hlk
        change (st.responses.cacheQuery (hd, nm) i.1) (t', n) = st.responses (t', n)
        rw [QueryCache.cacheQuery_of_ne _ _ (fun h => hne (congrArg Prod.snd h))]
    rw [ih lk.2 w hw, hhead]

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- A reader step at nonce `nm` only adds cells in column `nm`: every reachable outcome leaves the
honest-tag log unchanged, and every cached cell outside column `nm` keeps its pre-step value. -/
private lemma authRFReaderStep_state
    (transcript : TagTranscript Nonce Digest)
    (st : AuthIdealState TagId Nonce Digest) :
    ∀ z ∈ support ((authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        transcript).run st),
      z.2.honestOutputs = st.honestOutputs ∧
        ∀ (t' : TagId) (n : Nonce) (d : Digest), n ≠ transcript.nonce →
          z.2.responses (t', n) = some d → st.responses (t', n) = some d := by
  intro z hz
  -- The reader run is the lookup pass followed by a pure log update.
  have hz' := hz
  unfold authRFReaderQueryImpl at hz'
  simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map,
    StateT.run_set, map_pure, support_map, Set.mem_image] at hz'
  obtain ⟨mp, hmp, rfl⟩ := hz'
  have hmp' : mp ∈ support ((authRFReaderLookups (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList).run st) := by
    unfold authRFReaderLookups
    exact hmp
  obtain ⟨hho, _⟩ := authRFLookup_mapM_logs_eq (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList st mp hmp'
  refine ⟨hho, ?_⟩
  intro t' n d hncol hcell
  have hcol := authRFLookup_mapM_responses_eq_of_ne_column (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) transcript.nonce (Finset.univ : Finset TagId).toList t' n hncol st mp hmp'
  rw [← hcol]
  exact hcell

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Inductive collision bound for the random-function world under pairwise-distinct reader nonces.
For an adversary making at most `q` reader queries, all on distinct nonces, the probability that a
forgery is recorded while running it against `authRFQueryImpl` from a `forgeInv`-state is at most
`q * |TagId| * maxDigestProb`.

The induction follows the adversary's query structure. A tag query touches no forgery state and
preserves the invariant. A reader query consumes one unit of the `q` budget: the step itself
records a forgery with probability at most `|TagId| * maxDigestProb` (`authRFReaderStep_forge_le`,
whose column-honesty hypothesis is supplied by `forgeInv` together with distinctness), and the
residual adversary contributes at most `(q - 1) * |TagId| * maxDigestProb`. -/
private lemma simulateQ_authRF_forge_le
    (adversary : AuthAdversary TagId Nonce Digest)
    (maxDigestProb : ℝ≥0∞)
    (hmax : ∀ v : Digest, Pr[= v | ($ᵗ Digest : ProbComp Digest)] ≤ maxDigestProb)
    (q : ℕ)
    (st : AuthIdealState TagId Nonce Digest)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pNonce n) 1)
    (hinv : forgeInv adversary st) :
    Pr[fun z => z.2.readerForged ≠ ∅ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run st] ≤
      (q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
  classical
  induction adversary using OracleComp.inductionOn generalizing st q with
  | pure x =>
    -- No queries: the forgery log is still empty.
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, hinv.1, ne_eq, not_true_eq_false,
      ite_false]
    exact zero_le
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind, monadLift_self]
    cases t with
    | inl tag =>
      -- A tag query: the budgets pass unchanged, and `forgeInv` is preserved.
      have hstepRun : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inl tag)) = authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) tag := rfl
      rw [probEvent_bind_eq_tsum]
      have hcont : ∀ p ∈ support
          ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (Sum.inl tag)).run st),
          Pr[fun z => z.2.readerForged ≠ ∅ |
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (oa p.1)).run p.2] ≤
            (q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
        intro p hp
        -- Budgets for the continuation: a tag query satisfies neither predicate.
        have hqcont : OracleComp.IsQueryBoundP (oa p.1) (fun i => i.isRight) q := by
          have := (isQueryBoundP_query_bind_iff (p := fun i => i.isRight) (Sum.inl tag) oa q).mp hq
          simpa using this.2 p.1
        have hdcont : ∀ n : Nonce, OracleComp.IsQueryBoundP (oa p.1) (pNonce n) 1 := by
          intro n
          have := (isQueryBoundP_query_bind_iff (p := pNonce n) (Sum.inl tag) oa 1).mp (hdistinct n)
          have hfalse : ¬ pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n
              (Sum.inl tag) := id
          simpa [hfalse] using this.2 p.1
        -- `forgeInv` for the continuation: the cell budget disjunct passes to `oa p.1`.
        have hinvcont : forgeInv (oa p.1) p.2 := by
          have hcellQ : ∀ (t' : TagId) (n : Nonce) (d : Digest),
              st.responses (t', n) = some d →
                ((t', (⟨n, d⟩ : TagTranscript Nonce Digest)) ∈ st.honestOutputs ∨
                  OracleComp.IsQueryBoundP (oa p.1) (pNonce n) 0) := by
            intro t' n d hcell
            rcases hinv.2 t' n d hcell with hh | hb
            · exact Or.inl hh
            · refine Or.inr ?_
              have := (isQueryBoundP_query_bind_iff (p := pNonce n) (Sum.inl tag) oa 0).mp hb
              have hfalse : ¬ pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n
                  (Sum.inl tag) := id
              simpa [hfalse] using this.2 p.1
          have hpres := authIdealTagStep_cell_inv (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) tag st (fun n => OracleComp.IsQueryBoundP (oa p.1) (pNonce n) 0)
            hinv.1 hcellQ p (by rwa [hstepRun] at hp)
          exact ⟨hpres.1, hpres.2⟩
        exact ih p.1 q p.2 hqcont hdcont hinvcont
      calc ∑' p, Pr[= p |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (Sum.inl tag)).run st] *
            Pr[fun z => z.2.readerForged ≠ ∅ |
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (oa p.1)).run p.2]
          ≤ ∑' p, Pr[= p |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (Sum.inl tag)).run st] *
              ((q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb) := by
            refine ENNReal.tsum_le_tsum fun p => ?_
            by_cases hp : p ∈ support
                ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (Sum.inl tag)).run st)
            · exact mul_le_mul' le_rfl (hcont p hp)
            · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]
        _ = (∑' p, Pr[= p |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (Sum.inl tag)).run st]) *
              ((q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb) := by
            rw [ENNReal.tsum_mul_right]
        _ ≤ (q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
            exact le_trans (mul_le_mul' tsum_probOutput_le_one le_rfl) (le_of_eq (one_mul _))
    | inr transcript =>
      -- A reader query: consumes one budget unit. `0 < q` from the reader-query bound.
      have hqsplit := (isQueryBoundP_query_bind_iff (p := fun i => i.isRight)
        (Sum.inr transcript) oa q).mp hq
      have hqpos : 0 < q := by
        have : ¬ ¬ (Sum.inr transcript :
            (AuthOracleSpec TagId Nonce Digest).Domain).isRight = true := by simp
        rcases hqsplit.1 with h | h
        · exact absurd h this
        · exact h
      set nm := transcript.nonce with hnm
      have hdsplit := (isQueryBoundP_query_bind_iff (p := pNonce nm)
        (Sum.inr transcript) oa 1).mp (hdistinct nm)
      have hpNm : pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) nm
          (Sum.inr transcript) := by simp [pNonce, hnm]
      -- Every column-`nm` cell is honest: the budget disjunct fails for a `pNonce nm`-query.
      have hcol : ∀ tag : TagId, ∀ d : Digest,
          st.responses (tag, transcript.nonce) = some d →
            (tag, (⟨transcript.nonce, d⟩ : TagTranscript Nonce Digest)) ∈ st.honestOutputs := by
        intro tag d hcell
        rcases hinv.2 tag transcript.nonce d hcell with hh | hb
        · exact hh
        · exfalso
          have := (isQueryBoundP_query_bind_iff (p := pNonce transcript.nonce)
            (Sum.inr transcript) oa 0).mp hb
          rcases this.1 with h | h
          · exact h hpNm
          · exact absurd h (lt_irrefl 0)
      -- The per-step forge bound from `authRFReaderStep_forge_le`.
      have hstepRun : (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inr transcript)).run st =
          (authRFReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            transcript).run st := rfl
      have hstepForge :
          Pr[fun z => ¬ z.2.readerForged = ∅ |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (Sum.inr transcript)).run st] ≤
            (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
        rw [hstepRun]
        exact authRFReaderStep_forge_le (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript st maxDigestProb hmax hinv.1 hcol
      -- The continuation bound from the induction hypothesis.
      have hcont : ∀ p ∈ support
          ((authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (Sum.inr transcript)).run st),
          p.2.readerForged = ∅ →
          Pr[fun z => ¬ z.2.readerForged = ∅ |
              (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                (oa p.1)).run p.2] ≤
            ((q - 1 : ℕ) : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
        intro p hp hpforged
        -- Budgets for the continuation.
        have hqcont : OracleComp.IsQueryBoundP (oa p.1) (fun i => i.isRight) (q - 1) := by
          have := hqsplit.2 p.1
          simpa using this
        have hdcont : ∀ n : Nonce, OracleComp.IsQueryBoundP (oa p.1) (pNonce n) 1 := by
          intro n
          by_cases hnn : n = nm
          · subst hnn
            have := hdsplit.2 p.1
            rw [if_pos hpNm] at this
            exact this.mono (Nat.zero_le 1)
          · have hsplitn := (isQueryBoundP_query_bind_iff (p := pNonce n)
              (Sum.inr transcript) oa 1).mp (hdistinct n)
            have hfalse : ¬ pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n
                (Sum.inr transcript) := by
              change ¬ transcript.nonce = n
              rw [← hnm]
              exact fun h => hnn h.symm
            have := hsplitn.2 p.1
            rwa [if_neg hfalse] at this
        -- `forgeInv` for the continuation.
        have hinvcont : forgeInv (oa p.1) p.2 := by
          refine ⟨hpforged, ?_⟩
          intro t' n d hcell
          have hreaderState := authRFReaderStep_state (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) transcript st p (by rwa [hstepRun] at hp)
          by_cases hnn : n = nm
          · -- Column-`nm` cell: the budget disjunct holds for the continuation.
            refine Or.inr ?_
            subst hnn
            have := hdsplit.2 p.1
            rwa [if_pos hpNm] at this
          · -- Cell outside column `nm`: carried over from `st`.
            have hcellst : st.responses (t', n) = some d :=
              hreaderState.2 t' n d hnn hcell
            rcases hinv.2 t' n d hcellst with hh | hb
            · refine Or.inl ?_
              rw [hreaderState.1]
              exact hh
            · refine Or.inr ?_
              have hfalse : ¬ pNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n
                  (Sum.inr transcript) := by
                change ¬ transcript.nonce = n
                rw [← hnm]
                exact fun h => hnn h.symm
              have := (isQueryBoundP_query_bind_iff (p := pNonce n)
                (Sum.inr transcript) oa 0).mp hb
              have := this.2 p.1
              rwa [if_neg hfalse] at this
        exact ih p.1 (q - 1) p.2 hqcont hdcont hinvcont
      -- Combine the step bound and the continuation bound.
      have hcombine := probEvent_bind_le_add
        (mx := (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (Sum.inr transcript)).run st)
        (my := fun p => (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest)) (oa p.1)).run p.2)
        (p := fun z => z.2.readerForged = ∅)
        (q := fun y => y.2.readerForged = ∅)
        (ε₁ := (Fintype.card TagId : ℝ≥0∞) * maxDigestProb)
        (ε₂ := ((q - 1 : ℕ) : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb)
        hstepForge hcont
      calc Pr[fun z => z.2.readerForged ≠ ∅ |
              (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (Sum.inr transcript)).run st >>= fun p =>
                (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest)) (oa p.1)).run p.2]
          ≤ (Fintype.card TagId : ℝ≥0∞) * maxDigestProb +
              ((q - 1 : ℕ) : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := hcombine
        _ = (q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb := by
            have hqcast : (1 : ℝ≥0∞) + ((q - 1 : ℕ) : ℝ≥0∞) = (q : ℝ≥0∞) := by
              have : 1 + (q - 1) = q := Nat.add_sub_cancel' (Nat.succ_le_iff.mpr hqpos)
              exact_mod_cast this
            have hc : (Fintype.card TagId : ℝ≥0∞) * maxDigestProb +
                ((q - 1 : ℕ) : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * maxDigestProb =
                (1 + ((q - 1 : ℕ) : ℝ≥0∞)) * ((Fintype.card TagId : ℝ≥0∞) * maxDigestProb) := by
              rw [add_mul, one_mul, mul_assoc]
            rw [hc, hqcast, mul_assoc]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Collision bound for the random-function authentication world, restricted to adversaries whose
reader queries use pairwise-distinct nonces. For such an adversary making at most `q` reader
queries, the probability that the random-function reader records a forged acceptance is at most
`q * |TagId| * maxDigestProb`.

The distinctness hypothesis `HasDistinctReaderNonces adversary` states that every nonce is carried
by at most one reader query: no two reader queries write the same cache column, so every cached
cell in a reader query's column was produced by an honest tag output, and the per-reader-step
forge probability is bounded by `|TagId| * maxDigestProb`. -/
theorem authRFExp_le_collisionBound_of_distinctReaderNonces
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : HasDistinctReaderNonces adversary)
    (maxDigestProb : ℝ)
    (hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ maxDigestProb) :
    (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary]).toReal ≤
      ((q * Fintype.card TagId : ℕ) : ℝ) * maxDigestProb := by
  -- Pass to the directly-defined random-function experiment.
  have hmax_ENNReal : ∀ d : Digest,
      Pr[= d | ($ᵗ Digest : ProbComp Digest)] ≤ ENNReal.ofReal maxDigestProb := by
    intro d
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top one_ne_top probOutput_le_one)]
    exact ENNReal.ofReal_le_ofReal (hmax d)
  have hlhs : Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) adversary] =
      Pr[fun z : Unit × AuthIdealState TagId Nonce Digest => z.2.readerForged ≠ ∅ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run AuthIdealState.init] := by
    rw [authRFExp_eq_authRFDirectExp, ← probEvent_eq_eq_probOutput, authRFDirectExp,
      probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    simp
  rw [hlhs]
  -- Apply the inductive collision bound from the initial state.
  have hinit : forgeInv (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary
      AuthIdealState.init := by
    refine ⟨rfl, ?_⟩
    intro tag nonce d hcell
    simp [AuthIdealState.init] at hcell
  have hcore := simulateQ_authRF_forge_le (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    adversary (ENNReal.ofReal maxDigestProb) hmax_ENNReal q AuthIdealState.init hq hdistinct hinit
  -- Convert the `ℝ≥0∞` bound to `ℝ`.
  have hconv : (Pr[fun z : Unit × AuthIdealState TagId Nonce Digest => z.2.readerForged ≠ ∅ |
        (simulateQ (authRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
          adversary).run AuthIdealState.init]).toReal ≤
      ((q : ℝ≥0∞) * (Fintype.card TagId : ℝ≥0∞) * ENNReal.ofReal maxDigestProb).toReal :=
    ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) hcore
  have hsupp : (support ($ᵗ Digest : ProbComp Digest)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ne_eq, ← probFailure_eq_one_iff]
    simp
  obtain ⟨d0, _⟩ := hsupp
  have hmax_nonneg : 0 ≤ maxDigestProb := ENNReal.toReal_nonneg.trans (hmax d0)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hmax_nonneg] at hconv
  rw [Nat.cast_mul]
  exact hconv

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Uniform-`Digest` specialization of `authRFExp_le_collisionBound_of_distinctReaderNonces`: when
`Digest` is finite and sampled uniformly, the per-digest probability is `1 / |Digest|`, so the
distinct-reader-nonce collision bound reads `q * |TagId| / |Digest|`. -/
theorem authRFExp_le_uniformCollisionBound_of_distinctReaderNonces [Fintype Digest]
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : HasDistinctReaderNonces adversary) :
    (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary]).toReal ≤
      ((q * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
  have hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ (Fintype.card Digest : ℝ)⁻¹ := fun d => by
    simp [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have h := authRFExp_le_collisionBound_of_distinctReaderNonces
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    adversary q hq hdistinct ((Fintype.card Digest : ℝ)⁻¹) hmax
  rwa [div_eq_mul_inv]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Worked specialization showing the proved bound in use: an adversary making at most one reader
query satisfies the random-function collision bound with no separate distinctness hypothesis. A
single reader query is vacuously distinct (`hasDistinctReaderNonces_of_readerBound`), so the
forged-acceptance probability is at most `|TagId| / |Digest|`. -/
theorem authRFExp_le_uniformCollisionBound_of_singleReaderQuery [Fintype Digest]
    (adversary : AuthAdversary TagId Nonce Digest)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) 1) :
    (Pr[= true | authRFExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary]).toReal ≤
      (Fintype.card TagId : ℝ) / (Fintype.card Digest : ℝ) := by
  have h := authRFExp_le_uniformCollisionBound_of_distinctReaderNonces
    (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    adversary 1 hq (hasDistinctReaderNonces_of_readerBound adversary hq)
  simpa using h

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- End-to-end authentication bound, distinct-reader-nonce regime. Composing the PRF reduction
`authExp_le_prfAdvantage_add_authRF` with the proved collision bound
`authRFExp_le_collisionBound_of_distinctReaderNonces`, the active-authentication adversary's
forgery probability is bounded by a single quantity: the PRF distinguishing advantage of the
canonical reduction plus the collision term `q * |TagId| * maxDigestProb`.

This is the result downstream users should cite — it folds the two-step reduction (PRF hop, then
collision analysis) into one inequality, so there is no need to stitch the intermediate
`authRFExp` world in by hand. -/
theorem authExp_le_prfAdvantage_add_collisionBound
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : HasDistinctReaderNonces adversary)
    (maxDigestProb : ℝ)
    (hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ maxDigestProb) :
    (Pr[= true | authExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary]).toReal ≤
      PRFScheme.prfAdvantage prfs.multiplePRFScheme
        (authToPRFReduction (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary) +
      ((q * Fintype.card TagId : ℕ) : ℝ) * maxDigestProb := by
  refine le_trans (authExp_le_prfAdvantage_add_authRF prfs adversary) ?_
  gcongr
  exact authRFExp_le_collisionBound_of_distinctReaderNonces adversary q hq hdistinct
    maxDigestProb hmax

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Existential form of `authExp_le_prfAdvantage_add_collisionBound`: there is a PRF adversary
whose distinguishing advantage, added to the distinct-reader-nonce collision term, bounds the
authentication adversary's forgery probability. The witness is `authToPRFReduction adversary`. -/
theorem exists_prfAdv_authExp_le_prfAdvantage_add_collisionBound
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : HasDistinctReaderNonces adversary)
    (maxDigestProb : ℝ)
    (hmax : ∀ d : Digest,
      (Pr[= d | ($ᵗ Digest : ProbComp Digest)]).toReal ≤ maxDigestProb) :
    ∃ prfAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      (Pr[= true | authExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary]).toReal ≤
        PRFScheme.prfAdvantage prfs.multiplePRFScheme prfAdv +
        ((q * Fintype.card TagId : ℕ) : ℝ) * maxDigestProb :=
  ⟨authToPRFReduction adversary,
    authExp_le_prfAdvantage_add_collisionBound prfs adversary q hq hdistinct maxDigestProb hmax⟩

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Uniform-`Digest` specialization of `authExp_le_prfAdvantage_add_collisionBound`: when `Digest`
is finite and sampled uniformly, the collision term reads `q * |TagId| / |Digest|`, so the
authentication adversary's forgery probability is bounded by the PRF advantage plus
`q * |TagId| / |Digest|`. -/
theorem authExp_le_prfAdvantage_add_uniformCollisionBound [Fintype Digest]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest)
    (q : ℕ)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) q)
    (hdistinct : HasDistinctReaderNonces adversary) :
    (Pr[= true | authExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary]).toReal ≤
      PRFScheme.prfAdvantage prfs.multiplePRFScheme
        (authToPRFReduction (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary) +
      ((q * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
  refine le_trans (authExp_le_prfAdvantage_add_authRF prfs adversary) ?_
  gcongr
  exact authRFExp_le_uniformCollisionBound_of_distinctReaderNonces adversary q hq hdistinct


end Theorems

end PRFTagReader
