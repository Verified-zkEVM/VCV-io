/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.ReadRecording

/-!
# EUF-CMA for Fiat-Shamir with aborts: TapeFactorization

The first-moment reduction scaffolding for the coincidence-count bound and
the fold-level tape factorization: every interleaved signing query's attempt-draw
block commutes to the front of the opaque adversary fold, so the run distributes as
a pre-drawn tape followed by a tape-consuming run.

Part of the CMA-to-NMA security development for the Fiat-Shamir-with-aborts
transform; `VCVio.CryptoFoundations.FiatShamir.WithAbort.Security` assembles
the headline `euf_cma_to_nma` and holds the overview docstring.
-/

public section

universe u v

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section EUF_CMA

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

section scaffold

variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
variable (adv : SignatureAlg.unforgeableAdv
  (FiatShamirWithAbort
    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))

/-! ### First-moment reduction scaffolding for the coincidence-count bound

The numeric residual `readRecord_expected_coincidences_le` reduces, by elementary arithmetic, to a
single value-free cross-term atom. The reduction chain:

* the coincidence count is dominated by the pair count
  `Σ_{rc ∈ readlist} drawnlist.count rc` (`List.countP_le_sum_count_mem`);
* the *number of recorded reads* is bounded **deterministically** by the read-query budget `qH`
  (`deferredDrawReadImpl_run_readlist_length_le`), so the read-recording run's readlist length is at
  most `s.readlist.length + qH`;
* the expected drawn-list length of the read-recording run is at most
  `s.drawnlist.length + qSrem · (1/(1-p))` (`deferredDrawRead_run_expected_drawnlist_length_le`, the
  read-recording counterpart of `deferredDraw_run_expected_length_le`);
* the genuine content is then the **value-free per-pair atom**
  `readRecord_expected_pairs_nontape_le`: the expected pair count is at most `ε` times the expected
  `readlist.length · drawnlist.length`, because each recorded drawn commit is a fresh raw
  `Prod.fst <$> ids.commit` draw (mass `≤ ε`) and is independent of the value-free recorded
  read-commit list.

`readRecord_expected_coincidences_le` chains these with the deterministic read bound
(`readlist.length ≤ qH+1` from the empty start) and the final-arithmetic conversion.

The tape factorization (`tapeDrawReadImpl`, `evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`,
`readRecord_expected_pairs_tape_le`, `readRecord_expected_pairs_le`) is a separate, reusable
front-loading representation of the same run; it is not on the live path of the chain above. -/

/-- Domination of the membership count by the per-element coincidence count: the number of recorded
read-commits lying in the drawn list is at most `Σ_{rc ∈ readlist} drawnlist.count rc`, the total
number of coinciding `(read, draw)` pairs. -/
private lemma countP_mem_le_sum_count {α : Type} [DecidableEq α] (l d : List α) :
    l.countP (fun rc => decide (rc ∈ d)) ≤ (l.map (fun rc => d.count rc)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons]
      by_cases h : a ∈ d
      · simp only [decide_eq_true_eq, h, if_true]
        have : 1 ≤ d.count a := List.one_le_count_iff.mpr h
        omega
      · simp only [decide_eq_true_eq, h, if_false]
        omega

/-- Expressing a `List.count` as a sum of equality indicators over the list. -/
private lemma count_eq_sum_map_ite {α : Type} [DecidableEq α] (d : List α) (a : α) :
    (d.map (fun w => (if w = a then 1 else 0))).sum = d.count a := by
  induction d with
  | nil => simp
  | cons x d ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.count_cons]
      by_cases h : x = a
      · simp [h]; ring
      · simp [h]

/-- **Symmetric double-count of two lists.** Summing `d.count rc` over `rc ∈ l` equals summing
`l.count w` over `w ∈ d`; both count the coinciding `(read, draw)` pairs
(`Σ_x l.count x · d.count x`). This re-index lets the per-pair charge be organised by the
*draw* list (whose entries are fresh i.i.d. commitments) rather than the read list. -/
private lemma sum_map_count_comm {α : Type} [DecidableEq α] (l d : List α) :
    (l.map (fun rc => d.count rc)).sum = (d.map (fun w => l.count w)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      have key : (d.map (fun w => (a :: l).count w)).sum
          = (d.map (fun w => (if w = a then 1 else 0))).sum + (d.map (fun w => l.count w)).sum := by
        rw [← List.sum_map_add]
        refine congrArg _ (List.map_congr_left fun w _ => ?_)
        rw [List.count_cons]
        by_cases h : w = a
        · subst h; simp [add_comm]
        · simp [h, Ne.symm h]
      rw [key, count_eq_sum_map_ite, add_comm]

omit [SampleableType Stmt] in
/-- **Deterministic readlist-length bound.** Every reachable final state of the read-recording run
records at most `qH` new read-commits, where `qH` bounds the random-oracle (read) queries `oa` makes
(the `(· matches .inl (.inr _))` component of `signHashQueryBound`): each read step prepends exactly
one commitment to the recorded read-commit list and uniform/signing steps leave it untouched. Hence
`readlist.length ≤ s.readlist.length + qH` on the whole support — a *deterministic* (support-wide)
bound, used to dominate the random `readlist.length` factor of the pair count by the constant
`qH`. -/
theorem deferredDrawReadImpl_run_readlist_length_le {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qH : ℕ), oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH →
      ∀ (s : DeferredReadState M Commit Chal)
        (z : γ × DeferredReadState M Commit Chal),
        z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s) →
        z.2.2.length ≤ s.2.length + qH := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qH _ s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
  | query_bind t ob ih =>
      intro qH hQ s z hz
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      rcases t with (n | mc) | msg
      · -- UNIFORM: readlist untouched; budget unchanged.
        have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs
        have hih := ih u qH (by simpa using hQ2 u) s z hzx
        simpa using hih
      · -- READ: readlist grows by one; budget decrements by one (`0 < qH`).
        have hpos : 0 < qH := by
          rcases hQ1 with hno | hpos
          · exact absurd rfl hno
          · exact hpos
        have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$>
              roStep M s.1.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs
        have hih := ih cu.1 (qH - 1) (by simpa using hQ2 cu.1)
          ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)), mc.2 :: s.2) z hzx
        simp only [List.length_cons] at hih
        omega
      · -- SIGN: readlist untouched; budget unchanged.
        have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs
        have hih := ih alc.1.1 qH (by simpa using hQ2 alc.1.1)
          ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2) z hzx
        simpa using hih

omit [SampleableType Stmt] in
/-- **Per-step expected drawn-list length growth of the read-recording handler.** One step of
`deferredDrawReadImpl` grows the expected drawn-list length by at most `1/(1-p)` on a signing query
and by `0` on uniform / random-oracle-read queries (which leave the drawn list `s.1.1.2`
untouched). Identical to `deferredDrawImpl_step_expected_length_le` on the underlying deferred
state; the extra read-commit list is irrelevant to the drawn-list length. -/
lemma deferredDrawReadImpl_step_expected_drawnlist_length_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredReadState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredReadState M Commit Chal,
      Pr[= z | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
        (z.2.1.1.2.length : ℝ≥0∞))
      ≤ (s.1.1.2.length : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · -- UNIFORM: state untouched, drawn list `s.1.1.2` preserved.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawReadImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · -- READ: writes only the base cache / bad flag / readlist; drawn list `s.1.1.2` preserved.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
              mc.2 :: s.2))) <$>
            roStep M s.1.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawReadImpl, StateT.run_mk]
      rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · -- SIGN: drawn list becomes `s.1.1.2 ++ alc.1.2`; expected new length ≤ 1/(1-p).
    rw [if_pos (by simp)]
    have hrun : (deferredDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)))
      (fun z => (z.2.1.1.2.length : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              ((s.1.1.2.length : ℝ≥0∞) + (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append]
          push_cast
          ring
      _ = (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (s.1.1.2.length : ℝ≥0∞)) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (alc.1.2.length : ℝ≥0∞) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ (s.1.1.2.length : ℝ≥0∞) + ENNReal.ofReal (1 / (1 - p_abort)) := by
          refine add_le_add ?_ ?_
          · rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          · exact le_trans (tsum_probOutput_run_ghostSignDrawBody_mul_length_le ids M pk sk msg
              hAbort maxAttempts s.1.1.1.1) (geomAttemptSum_le maxAttempts hp₀ hp)

omit [SampleableType Stmt] in
/-- **Run-level expected drawn-list length of the read-recording run.** By induction on `oa`, the
expected final drawn-list length of the read-recording run from a start state `s` is at most
`s.drawnlist.length + qSrem · (1/(1-p))`, where `qSrem` bounds the number of signing queries. The
read-recording counterpart of `deferredDraw_run_expected_length_le`: the drawn list evolves
identically (the recorded read-commit list never affects it), so the per-step charge
`deferredDrawReadImpl_step_expected_drawnlist_length_le` telescopes against the signing-query budget
exactly as before. -/
theorem deferredDrawRead_run_expected_drawnlist_length_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredReadState M Commit Chal),
        (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            (z.2.1.1.2.length : ℝ≥0∞))
          ≤ (s.1.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
          Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawReadImpl]
          · simp only [deferredDrawReadImpl, StateT.run_mk]
            rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawReadImpl])
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
            (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob x.1)).run x.2] * (z.2.1.1.2.length : ℝ≥0∞))
              ≤ (x.2.1.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
            (x.2.1.1.2.length : ℝ≥0∞)) ≤ (s.1.1.2.length : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob x.1)).run x.2] * (z.2.1.1.2.length : ℝ≥0∞))
            ≤ (s.1.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * (z.2.1.1.2.length : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                ((x.2.1.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                  (x.2.1.1.2.length : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                    ((x.2.1.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      (x.2.1.1.2.length : ℝ≥0∞) +
                    Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ ((s.1.1.2.length : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by gcongr
          _ ≤ (s.1.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by rw [add_assoc]; gcongr
      rcases t with (n | mc) | msg
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_drawnlist_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_drawnlist_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawReadImpl_step_expected_drawnlist_length_le ids M maxAttempts
            pk sk hp₀ hp hAbort (.inr msg) s
          rwa [if_pos (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **Per-step expected attempt-count growth of the read-recording handler.** One step of
`deferredDrawReadImpl` grows the expected combined size `drawnlist.length + signedlist.length` by at
most `1/(1-p)` on a signing query and by `0` on a uniform or random-oracle-read query (which leave
both lists untouched). The read-recording counterpart of
`deferredDrawImpl_step_expected_attemptCount_le`; the recorded read-commit list never affects the
drawn or signed lists, so the charge is identical. -/
lemma deferredDrawReadImpl_step_expected_attemptCount_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredReadState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredReadState M Commit Chal,
      Pr[= z | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
        ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
      ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawReadImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
              mc.2 :: s.2))) <$>
            roStep M s.1.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawReadImpl, StateT.run_mk]
      rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · rw [if_pos (by simp)]
    have hrun : (deferredDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)))
      (fun z => ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞) +
                (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append, List.length_cons]
          push_cast
          ring
      _ = ((∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞))) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (alc.1.2.length : ℝ≥0∞)) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) +
            ENNReal.ofReal (1 / (1 - p_abort)) := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          rw [add_assoc]
          gcongr
          refine le_trans (add_le_add_right
            (tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight ids M pk sk msg
              hAbort maxAttempts s.1.1.1.1) _) ?_
          rw [add_comm]
          refine le_trans (le_of_eq ?_) (geomSum_le hp₀ hp (maxAttempts + 1))
          rw [Finset.sum_range_succ']
          simp only [pow_zero]

omit [SampleableType Stmt] in
/-- **Run-level expected attempt count of the read-recording run.** By induction on `oa`, the
expected combined size `drawnlist.length + signedlist.length` of the read-recording run from a start
state `s` is at most `(s.drawnlist.length + s.signedlist.length) + qSrem · (1/(1-p))`, where `qSrem`
bounds the number of signing queries. The read-recording counterpart of
`deferredDraw_run_expected_attemptCount_le`. Subtracting the start signed-list length `l.length`
gives the attempt-count mean `≤ qSrem/(1-p)` used by the sound `#attempts`-form coincidence
bound. -/
theorem deferredDrawRead_run_expected_attemptCount_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredReadState M Commit Chal),
        (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
          ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) +
              (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
          Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawReadImpl]
          · simp only [deferredDrawReadImpl, StateT.run_mk]
            rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawReadImpl])
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
            (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob x.1)).run x.2] * ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
            ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob x.1)).run x.2] * ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                (((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                  ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                    (((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) +
                    Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ (((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by
              gcongr
          _ ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
              rw [add_assoc]; gcongr
      rcases t with (n | mc) | msg
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawReadImpl_step_expected_attemptCount_le ids M maxAttempts
            pk sk hp₀ hp hAbort (.inr msg) s
          rwa [if_pos (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **The read-recording run never fails.** Every step of `deferredDrawReadImpl` pushes forward a
non-failing `ProbComp`, so the whole fold has zero failure mass. -/
theorem deferredDrawRead_run_neverFail {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredReadState M Commit Chal),
      Pr[⊥ | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; simp [simulateQ_pure, StateT.run_pure]
  | query_bind t ob ih =>
      intro s
      rw [simulateQ_query_bind, StateT.run_bind, probFailure_bind_eq_zero_iff]
      refine ⟨?_, fun x _ => ih x.1 x.2⟩
      rcases t with (n | mc) | msg
      · simp [deferredDrawReadImpl]
      · simp only [deferredDrawReadImpl]
        rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
      · simp [deferredDrawReadImpl]

omit [SampleableType Stmt] in
/-- **The signed-message list of the read-recording run grows.** From any start state the recorded
signed-message list only ever gets longer, so its start length `l.length` is a lower bound on every
reachable final length. -/
theorem deferredDrawRead_run_signed_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredReadState M Commit Chal)
      (z : γ × DeferredReadState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.1.1.2.length ≤ z.2.1.1.1.2.length := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact le_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine le_trans ?_ (ih x.1 x.2 z hzx)
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; simp

omit [SampleableType Stmt] in
/-- **The drawn-list of the read-recording run grows.** From any start state the recorded drawn
(rejected-commit) list only ever gets longer: uniform and read steps leave it untouched, signing
steps append the body's rejected draws. So the start length is a lower bound on every reachable
final length. -/
theorem deferredDrawRead_run_drawn_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredReadState M Commit Chal)
      (z : γ × DeferredReadState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.1.2.length ≤ z.2.1.1.2.length := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact le_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine le_trans ?_ (ih x.1 x.2 z hzx)
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; simp

omit [SampleableType Stmt] in
/-- **Read-recording attempt-count mean.** The constructed attempt count
`(drawnlist.length) + (signedlist.length - l.length)` (= #rejects + #signing-queries, the count that
soundly dominates the consumed-attempt positions) of the read-recording run from the empty-draw
start `((((re, l), []), false), [])` has mean at most `qSrem/(1-p)`. Mirrors
`deferredDraw_attemptKn_mean_le`: recover the total combined size by adding back `l.length`, valid
because `l` is a signed-list prefix (`deferredDrawRead_run_signed_prefix`); bound by the run-level
attempt-count fold `deferredDrawRead_run_expected_attemptCount_le`, then cancel `l.length` (run mass
`1`, `deferredDrawRead_run_neverFail`). -/
theorem deferredDrawRead_attemptKn_mean_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ) (hQ : oa.IsQueryBoundP (· matches Sum.inr _) qSrem)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞))
      ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  set run : ProbComp (γ × DeferredReadState M Commit Chal) :=
    (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run ((((re, l), []), false), [])
    with hrun
  have hmass : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run]) = 1 := by
    rw [hrun]
    exact tsum_probOutput_eq_one'
      (deferredDrawRead_run_neverFail ids M maxAttempts pk sk oa ((((re, l), []), false), []))
  -- Recover the total combined size by adding back `l.length`; the start drawn list is empty.
  have hsplit : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
        ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
        ((l.length : ℕ) : ℝ≥0∞)
      = ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞) := by
    rw [show ((l.length : ℕ) : ℝ≥0∞)
          = ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] * ((l.length : ℕ) : ℝ≥0∞) by
        rw [ENNReal.tsum_mul_right, hmass, one_mul]]
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    rw [← mul_add]
    by_cases hz : z ∈ support run
    · have hpre : l.length ≤ z.2.1.1.1.2.length := by
        have := deferredDrawRead_run_signed_prefix ids M maxAttempts pk sk oa
          ((((re, l), []), false), []) z (by rwa [hrun] at hz)
        simpa using this
      congr 1
      rw [← Nat.cast_add]
      congr 1
      omega
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
  -- The total combined size is bounded by `l.length + qSrem/(1-p)`; cancel `l.length`.
  have htot : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
        ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
      ≤ ((l.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [hrun]
    have := deferredDrawRead_run_expected_attemptCount_le ids M maxAttempts pk sk hp₀ hp hAbort
      oa qSrem hQ ((((re, l), []), false), [])
    simpa using this
  -- Subtract `l.length` from both sides of `hsplit ≤ htot` (it is a finite quantity ≤ both).
  have hle : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
        ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
        ((l.length : ℕ) : ℝ≥0∞)
      ≤ ((qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort))) + ((l.length : ℕ) : ℝ≥0∞) := by
    rw [hsplit, add_comm ((qSrem : ℝ≥0∞) * _)]; exact htot
  exact ENNReal.le_of_add_le_add_right (by simp) hle

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq Commit] in
/-- **Splitting an i.i.d. front draw block.** Drawing `n + m` independent commitment draws into a
list is the same computation as drawing the first `n` and then the last `m` and concatenating: the
front block factors into independent sub-blocks. This is the structural identity that, with the
i.i.d. resampling commute, lets the per-query draw blocks accumulate into one front tape. -/
lemma drawList_commit_add (pk : Stmt) (sk : Wit) (n m : ℕ) :
    OracleComp.drawList (ids.commit pk sk) (n + m) =
      OracleComp.drawList (ids.commit pk sk) n >>= fun a =>
        OracleComp.drawList (ids.commit pk sk) m >>= fun b => pure (a ++ b) := by
  classical
  induction n with
  | zero => simp [OracleComp.drawList]
  | succ n ih =>
      rw [Nat.succ_add, OracleComp.drawList, OracleComp.drawList, ih]
      simp only [bind_assoc, pure_bind, List.cons_append]

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq Commit] in
/-- **Front draw blocks have a deterministic length.** Every list in the support of
`drawList (ids.commit pk sk) n` has length exactly `n`: the block always draws `n` keys. This lets
the `take`/`drop` split of an over-provisioned tape resolve to the per-query block and its
remainder. -/
lemma length_mem_support_drawList_commit (pk : Stmt) (sk : Wit) (n : ℕ)
    (ws : List (Commit × PrvState))
    (hws : ws ∈ support (OracleComp.drawList (ids.commit pk sk) n)) :
    ws.length = n := by
  classical
  induction n generalizing ws with
  | zero =>
      simp only [OracleComp.drawList, support_pure, Set.mem_singleton_iff] at hws
      subst hws; rfl
  | succ n ih =>
      rw [OracleComp.drawList] at hws
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hws
      obtain ⟨w, hw, ws', hws', rfl⟩ := hws
      simp [ih ws' hws']

/-! ### Fold-level tape factorization (reusable front-loading infrastructure)

The body-level half of the tape factorization
(`evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody`)
recasts *one* signing body's inline attempt draws as consumption from a pre-drawn tape. The
*fold-level* half — built here — lifts that across the opaque adversary `simulateQ (oa)` fold: every
interleaved signing query's draw block commutes to the very front, so the whole run distributes as

  `drawList (ids.commit pk sk) L >>= fun tape => (simulateQ tapeDrawReadImpl oa).run (s, tape)`,

a single independent front draw block of `L := maxAttempts · #signing-queries` commitments followed
by a tape-*consuming* run. Once the draws are front-loaded, the recorded drawn list is a function of
the tape and the value-free read list is a function of the non-tape randomness, so the read list is
independent of the tape.

The tape-consuming handler `tapeDrawReadImpl` carries a draw tape in its state; a signing query
consumes the first `maxAttempts` tape entries (running `tapeSignBody` on them and dropping them)
instead of drawing inline, while reads/uniform behave exactly as `deferredDrawReadImpl`. The
fold equality is proved by `inductionOn oa`: at a read/uniform step the answer is independent of the
tape so the front draw block commutes trivially; at a signing step the per-body factorization
splices in the body's `drawList maxAttempts` block, which then commutes to the front of the
remaining tape via the i.i.d. resampling commute `evalSPMF_bind_comm_probComp`.

This representation is an alternative to the inline (non-tape) charge that the headline uses; see
`readRecord_expected_pairs_tape_le` and `readRecord_expected_pairs_le`. -/

/-- The tape-consuming read-recording handler. Its state extends `DeferredReadState` with a *draw
tape* `List (Commit × PrvState)`: a signing query consumes the first `maxAttempts` entries of the
tape (running the tape-consuming body `tapeSignBody` on them and dropping them from the tape)
instead of drawing each attempt's commitment inline; uniform and random-oracle-read queries behave
exactly as `deferredDrawReadImpl` and leave the tape untouched. Over-provisioning the tape (length
`maxAttempts · #signing-queries`) makes the front-loaded draw block independent of the value-free
read list. -/
@[expose] noncomputable def tapeDrawReadImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (DeferredReadState M Commit Chal × List (Commit × PrvState)) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun cu => (cu.1, (((((cu.2, s.1.1.1.1.2), s.1.1.1.2), s.1.1.2 || decide (mc.2 ∈ s.1.1.1.2)),
          mc.2 :: s.1.2), s.2))) <$>
        roStep M s.1.1.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1.1, (((((alc.2, msg :: s.1.1.1.1.2), s.1.1.1.2 ++ alc.1.2), s.1.1.2),
          s.1.2), s.2.drop maxAttempts))) <$>
        (tapeSignBody ids M pk sk msg (s.2.take maxAttempts)).run s.1.1.1.1.1

omit [SampleableType Stmt] in
/-- **One-step unfolding of `tapeDrawReadImpl` on a uniform query.** -/
lemma tapeDrawReadImpl_run_unif (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : DeferredReadState M Commit Chal × List (Commit × PrvState)) :
    (tapeDrawReadImpl ids M maxAttempts pk sk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl

omit [SampleableType Stmt] in
/-- **One-step unfolding of `tapeDrawReadImpl` on a random-oracle read query.** -/
lemma tapeDrawReadImpl_run_read (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : DeferredReadState M Commit Chal × List (Commit × PrvState)) :
    (tapeDrawReadImpl ids M maxAttempts pk sk (.inl (.inr mc))).run s =
      (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((((cu.2, s.1.1.1.1.2), s.1.1.1.2), s.1.1.2 || decide (mc.2 ∈ s.1.1.1.2)),
            mc.2 :: s.1.2), s.2))) <$>
        roStep M s.1.1.1.1.1 mc := rfl

omit [SampleableType Stmt] in
/-- **One-step unfolding of `tapeDrawReadImpl` on a signing query.** The body consumes the first
`maxAttempts` tape entries (via `tapeSignBody`), the drawn list is extended by the recorded rejected
commitments, and the tape advances by `maxAttempts`. -/
lemma tapeDrawReadImpl_run_sign (pk : Stmt) (sk : Wit) (msg : M)
    (s : DeferredReadState M Commit Chal × List (Commit × PrvState)) :
    (tapeDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run s =
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, (((((alc.2, msg :: s.1.1.1.1.2), s.1.1.1.2 ++ alc.1.2), s.1.1.2),
            s.1.2), s.2.drop maxAttempts))) <$>
        (tapeSignBody ids M pk sk msg (s.2.take maxAttempts)).run s.1.1.1.1.1 := rfl

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- **Answer-irrelevant cross-step commute (the read/uniform inductive step).** A query step whose
answer and new non-tape state are produced by a tape-*preserving* `ProbComp` `step` (the uniform and
random-oracle-read steps both leave the tape untouched) commutes with the front draw block: pushing
the per-continuation front block to the very front past the answer is the i.i.d. resampling commute
`evalSPMF_bind_comm_probComp`. Given the inductive hypothesis `hcont` (the continuation run factors
as a front block followed by the tape-consuming continuation), the whole step factors likewise. -/
theorem evalSPMF_tapePreserving_step_commute {γ Ans : Type}
    (step : ProbComp (Ans × DeferredReadState M Commit Chal))
    (L : ℕ)
    (defCont : Ans → DeferredReadState M Commit Chal →
      ProbComp (γ × DeferredReadState M Commit Chal))
    (tapeCont : Ans → DeferredReadState M Commit Chal × List (Commit × PrvState) →
      ProbComp (γ × (DeferredReadState M Commit Chal × List (Commit × PrvState))))
    (pk : Stmt) (sk : Wit)
    (hcont : ∀ (a : Ans) (s' : DeferredReadState M Commit Chal),
      𝒮[defCont a s'] =
        𝒮[OracleComp.drawList (ids.commit pk sk) L >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$> tapeCont a (s', tape)]) :
    𝒮[step >>= fun p => defCont p.1 p.2] =
      𝒮[OracleComp.drawList (ids.commit pk sk) L >>= fun tape =>
          (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
              (p.1, p.2.1)) <$>
            (((fun p : Ans × DeferredReadState M Commit Chal => (p.1, (p.2, tape))) <$> step)
              >>= fun p => tapeCont p.1 p.2)] :=
  -- A direct instance of the generic answer-irrelevant tape commute: the front draw block is the
  -- `drawList (ids.commit pk sk) L` tape and `proj` discards the spent suffix.
  OracleComp.DeferredSampling.evalSPMF_step_commute_tape step
    (OracleComp.drawList (ids.commit pk sk) L)
    (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) => (p.1, p.2.1))
    defCont tapeCont hcont

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] in
/-- **Tape-combine reconciliation.** A front block drawn in two pieces — `maxAttempts` then
`maxAttempts · q'` — feeding a continuation `g blk rest` is the same computation as drawing the
whole `maxAttempts · (q'+1)` block at once and splitting it with `take`/`drop`: the first
`maxAttempts` entries are the body block, the remainder is the leftover tape. Uses
`drawList_commit_add` to split and the deterministic block length
`length_mem_support_drawList_commit` to resolve `take`/`drop`. -/
theorem drawList_combine_take_drop {δ : Type} (pk : Stmt) (sk : Wit) (q' : ℕ)
    (g : List (Commit × PrvState) → List (Commit × PrvState) → ProbComp δ) :
    𝒮[OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
        OracleComp.drawList (ids.commit pk sk) (maxAttempts * q') >>= fun rest => g blk rest]
      = 𝒮[OracleComp.drawList (ids.commit pk sk) (maxAttempts * (q' + 1)) >>= fun tape =>
          g (tape.take maxAttempts) (tape.drop maxAttempts)] := by
  classical
  rw [show maxAttempts * (q' + 1) = maxAttempts + maxAttempts * q' by ring,
    drawList_commit_add ids pk sk maxAttempts (maxAttempts * q'), bind_assoc]
  -- On the support of the first block, its length is `maxAttempts`, so `take`/`drop` resolve.
  refine evalSPMF_bind_congr (fun blk hblk => ?_)
  have hlen : blk.length = maxAttempts := length_mem_support_drawList_commit ids pk sk _ blk hblk
  rw [bind_assoc]
  refine evalSPMF_bind_congr_left _ _ _ (fun rest => ?_)
  rw [pure_bind, List.take_left' hlen, List.drop_left' hlen]

omit [SampleableType Stmt] in
theorem evalSPMF_defSignStep_splice {δ : Type} (pk : Stmt) (sk : Wit) (msg : M)
    (s : DeferredReadState M Commit Chal)
    (k : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache →
      ProbComp δ) :
    𝒮[(ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 >>= k] =
      𝒮[OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
          (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1 >>= k] := by
  rw [show (OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
        (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1 >>= k)
      = (OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
          (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1) >>= k from by rw [bind_assoc]]
  rw [evalSPMF_bind,
    evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody ids M pk sk msg maxAttempts s.1.1.1.1,
    ← evalSPMF_bind]

omit [SampleableType Stmt] in
/-- **Sign-step cross-step commute (the crux inductive step).** The deferred-draw sign step,
composed with the deferred continuation, factors as a single front draw block of
`maxAttempts·(q'+1)` commitments followed by the tape-consuming sign step + tape continuation. The
genuine framework content: the body's `maxAttempts` draw block splices to the front via the per-body
factorization (`evalSPMF_defSignStep_splice`); the continuation's `maxAttempts·q'` block (supplied
by the inductive hypothesis `hcont`) commutes past the body via the i.i.d. resampling commute
(`evalSPMF_bind_comm_probComp`); the two blocks combine into one `maxAttempts·(q'+1)` block split by
`take`/`drop` (`drawList_combine_take_drop`), exactly the tape the tape-consuming sign step
consumes. -/
theorem evalSPMF_signStep_commute {γ : Type} (pk : Stmt) (sk : Wit) (msg : M)
    (s : DeferredReadState M Commit Chal) (q' : ℕ)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
        (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hcont : ∀ (a : ((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
        (s' : DeferredReadState M Commit Chal),
      𝒮[(simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob a)).run s'] =
        𝒮[OracleComp.drawList (ids.commit pk sk) (maxAttempts * q') >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob a)).run (s', tape)]) :
    𝒮[(deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s >>= fun p =>
        (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2] =
      𝒮[OracleComp.drawList (ids.commit pk sk) (maxAttempts * (q' + 1)) >>= fun tape =>
          (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
              (p.1, p.2.1)) <$>
            ((tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run (s, tape) >>= fun p =>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2)] := by
  classical
  -- LHS: fold the deferred sign step's map into the body bind, then splice the front block.
  rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s >>= (fun p =>
        (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2)
      = (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 >>= fun alc =>
          (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
            (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)
      from by
        rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s
              = (fun alc : (Option (Commit × Resp) × List Commit) ×
                  (M × Commit →ₒ Chal).QueryCache =>
                  (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
                (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 from rfl]
        simp [bind_map_left]]
  rw [evalSPMF_defSignStep_splice ids M maxAttempts pk sk msg s
    (fun alc => (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
      (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))]
  -- Rewrite the continuation by `hcont`, under the leading `drawList maxAttempts` and body binds.
  rw [evalSPMF_bind_congr (mx := OracleComp.drawList (ids.commit pk sk) maxAttempts)
    (fun blk _ => evalSPMF_bind_congr (mx := (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1)
      (fun alc _ => hcont alc.1.1 ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)))]
  -- Commute the continuation's `maxAttempts·q'` block to the front past the body.
  rw [evalSPMF_bind_congr (mx := OracleComp.drawList (ids.commit pk sk) maxAttempts)
    (fun blk _ => evalSPMF_bind_comm_probComp ((tapeSignBody ids M pk sk msg blk).run s.1.1.1.1)
      (OracleComp.drawList (ids.commit pk sk) (maxAttempts * q'))
      (fun alc tape => (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
          (p.1, p.2.1)) <$>
        (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk)
          (ob alc.1.1)).run
            (((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2), tape)))]
  -- Combine the two front blocks into one `maxAttempts·(q'+1)` block split by `take`/`drop`.
  rw [drawList_combine_take_drop ids maxAttempts pk sk q'
    (fun blk rest => (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1 >>= fun alc =>
      (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
          (p.1, p.2.1)) <$>
        (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk)
          (ob alc.1.1)).run
            (((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2), rest))]
  -- Match the RHS: the tape sign step consumes `take maxAttempts` and threads `drop maxAttempts`.
  refine evalSPMF_bind_congr_left _ _ _ (fun tape => ?_)
  rw [show (tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run (s, tape)
        = (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, (((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2),
              tape.drop maxAttempts))) <$>
          (tapeSignBody ids M pk sk msg (tape.take maxAttempts)).run s.1.1.1.1 from rfl]
  simp [bind_map_left, map_bind]

omit [SampleableType Stmt] in
/-- **The fold-level tape factorization (the framework lemma).** By induction on the adversary
computation `oa`, the read-recording deferred-draw run distributes as a single front draw block of
`maxAttempts · qSrem` commitments followed by a tape-consuming run:

`𝒮[(simulateQ deferredDrawReadImpl oa).run s]`
`  = 𝒮[drawList (ids.commit pk sk) (maxAttempts · qSrem) >>= fun tape =>`
`        (simulateQ tapeDrawReadImpl oa).run (s, tape)]`,

where `qSrem` bounds the number of signing queries of `oa` (the `(· matches .inr _)` component of
`signHashQueryBound`). The tape is over-provisioned (length `maxAttempts · qSrem`); each signing
query consumes its `maxAttempts`-prefix and the unused suffix is discarded on early accept.

The proof inducts on `oa`. At a **read/uniform** step the query answer is independent of the tape,
so the front draw block commutes past it (the i.i.d. resampling commute
`evalSPMF_bind_comm_probComp`),
matching the inductive hypothesis for the continuation. At a **signing** step the per-body
factorization `evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody` recasts the body's inline draws
as a `drawList maxAttempts` block; that block is split off the front via `drawList_commit_add` (the
remaining `maxAttempts · (qSrem-1)` block feeding the continuation by the inductive hypothesis) and
commuted to the front past the answer-irrelevant continuation. The general principle it instantiates
is that answer-irrelevant per-step draws factor to a front tape in `simulateQ`. -/
theorem evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredReadState M Commit Chal),
        𝒮[(simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] =
          𝒮[OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
              (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                  (p.1, p.2.1)) <$>
                (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run (s, tape)] := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rw [evalSPMF_bind_const_neverFails _ (OracleComp.probFailure_drawList _ _)]
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rcases t with (n | mc) | msg
      · -- UNIFORM: the answer is independent of the tape; commute the front block past the draw.
        have hqs : (if (match (Sum.inl (Sum.inl n) :
              ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind]
        rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run s
              = (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
            from rfl]
        -- The tape uniform step is the deferred step with the tape inserted (`Functor.map_map`).
        rw [show (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              ((tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run (s, tape)
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (((fun p : (((unifSpec + (M × Commit →ₒ Chal)) +
                  (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inl n))) ×
                    DeferredReadState M Commit Chal => (p.1, (p.2, tape))) <$>
                  ((fun u => (u, s)) <$>
                    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n))
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            from by funext tape; rw [tapeDrawReadImpl_run_unif, Functor.map_map]; rfl]
        exact evalSPMF_tapePreserving_step_commute ids M
          ((fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n)
          (maxAttempts * qSrem)
          (fun a s' => (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob a)).run s')
          (fun a st => (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob a)).run st)
          pk sk (fun a s' => ih a qSrem (hQ2 a) s')
      · -- READ: the answer is `roStep` (real layer), independent of the tape; same commute.
        have hqs : (if (match (Sum.inl (Sum.inr mc) :
              ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind]
        rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run s
              = (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
                  (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                    mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc
            from rfl]
        rw [show (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              ((tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run (s, tape)
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (((fun p : Chal × DeferredReadState M Commit Chal => (p.1, (p.2, tape))) <$>
                  ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
                    (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                      mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc))
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            from by funext tape; rw [tapeDrawReadImpl_run_read, Functor.map_map]; rfl]
        exact evalSPMF_tapePreserving_step_commute ids M
          ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc)
          (maxAttempts * qSrem)
          (fun a s' => (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob a)).run s')
          (fun a st => (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob a)).run st)
          pk sk (fun a s' => ih a qSrem (hQ2 a) s')
      · -- SIGN: the crux. Splice the per-body draw block to the front past the continuation.
        have hpos : 0 < qSrem := by
          rcases hQ1 with h | h
          · exact absurd rfl h
          · exact h
        clear hQ1
        have hqs : (if (match (Sum.inr msg :
              ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem - 1 := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind]
        rw [show qSrem = (qSrem - 1) + 1 from by omega]
        exact evalSPMF_signStep_commute ids M maxAttempts pk sk msg s (qSrem - 1) ob
          (fun a s' => ih a (qSrem - 1) (hQ2 a) s')

omit [SampleableType Stmt] in
/-- **The atomic value-free charge (the irreducible probabilistic kernel).** One fresh raw
commitment draw `w ← ids.commit pk sk`, *independent of* a value-free list `rl`, contributes
expected multiplicity `E[rl.count w.1] ≤ ε · rl.length`: each of the `rl.length` slots of `rl` is
hit by the fresh draw with probability `Pr[= slot | Prod.fst <$> ids.commit pk sk] ≤ ε` (`hGuess`).

This is the single source of the `ε` in the ghost-read bound. It is purely the per-draw mass bound
combined with the independence of the draw from the (value-free) read list; the structural content
of the full charge is to exhibit each recorded rejected draw of the tape run in exactly this
independent-of-the-readlist position (the value-substitution at rejected tape positions). -/
private lemma tsum_probOutput_commit_mul_count_le {C P : Type} [DecidableEq C]
    (commit : ProbComp (C × P)) (rl : List C) (ε : ℝ)
    (hGuess : ∀ cm : C, Pr[= cm | Prod.fst <$> commit] ≤ ENNReal.ofReal ε) :
    (∑' w : C × P, Pr[= w | commit] * (rl.count w.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * (rl.length : ℝ≥0∞) :=
  OracleComp.DeferredSampling.tsum_probOutput_fresh_mul_count_le commit rl ε hGuess

omit [SampleableType Stmt] in
/-- **Value-substitution: the recorded read list is independent of the drawn-list content.** The
expected multiplicity `E[readlist.count w]` of any fixed commitment `w` in the recorded read list of
the read-recording run depends only on the start *real cache*, *signed list*, and *read list* — not
on the start *drawn list* `D` nor the start *bad flag* `b`. This is the structural value-freeness at
the heart of the ghost-read bound: the recorded reads answer via `roStep` on the real layer and
never the drawn (rejected) values, so changing the drawn list (or the bad flag, which is write-only
and never gates control flow) leaves the read-list marginal unchanged.

Formally the expectation is invariant under both drawn-list and bad-flag start values. Proved by
induction on `oa`:
* **pure** — the read list is the start one (independent of `D`, `b`).
* **uniform** — the draw is forwarded and the drawn list / bad flag / read list are untouched; the
  inductive hypothesis applies to the unchanged-`D` continuation.
* **read** — the read list grows by exactly `mc.2` (the same regardless of `D`); the bad flag
  updates to `b || (mc.2 ∈ D)` (which *does* depend on `D`), but since the inductive hypothesis is
  quantified over *all* bad-flag values, the two `D`-runs still agree.
* **sign** — the body draws are the same regardless of `D`, `b`; the drawn list grows by the body's
  rejected commitments and the bad flag is preserved, and the inductive hypothesis (quantified over
  all `D`) closes the differing-drawn-list continuations. -/
theorem deferredDrawRead_run_count_dl_invariant {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (w : Commit) (re : (M × Commit →ₒ Chal).QueryCache) (sgn : List M)
    (rl : List Commit) :
    ∀ (D₁ : List Commit) (b₁ : Bool) (D₂ : List Commit) (b₂ : Bool),
      (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, sgn), D₁), b₁), rl)] * (z.2.2.count w : ℝ≥0∞))
        = ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                ((((re, sgn), D₂), b₂), rl)] * (z.2.2.count w : ℝ≥0∞) := by
  induction oa using OracleComp.inductionOn generalizing re sgn rl with
  | pure a =>
      intro D₁ b₁ D₂ b₂
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
  | query_bind t ob ih =>
      intro D₁ b₁ D₂ b₂
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, tsum_probOutput_bind_mul]
      rcases t with (n | mc) | msg
      · -- UNIFORM: drawn list / bad flag / read list untouched; forward draw.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inl (Sum.inl n))) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (z.2.2.count w : ℝ≥0∞) with hG
        have hx₁ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run
              ((((re, sgn), D₁), b₁), rl)) =
            (fun u => (u, ((((re, sgn), D₁), b₁), rl))) <$>
              (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
        have hx₂ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run
              ((((re, sgn), D₂), b₂), rl)) =
            (fun u => (u, ((((re, sgn), D₂), b₂), rl))) <$>
              (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
        rw [hx₁, hx₂]
        refine (tsum_probOutput_map_mul _ _ G).trans
          ((tsum_congr fun u => ?_).trans (tsum_probOutput_map_mul _ _ G).symm)
        exact congrArg _ (ih u re sgn rl D₁ b₁ D₂ b₂)
      · -- READ: read list grows by `mc.2` (independent of `D`); the bad flag updates to
        -- `b || (mc.2 ∈ D)` (D-dependent), but `ih` is quantified over *all* bad flags.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inl (Sum.inr mc))) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (z.2.2.count w : ℝ≥0∞) with hG
        have hx₁ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run
              ((((re, sgn), D₁), b₁), rl)) =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, sgn), D₁), b₁ || decide (mc.2 ∈ D₁)), mc.2 :: rl))) <$>
              roStep M re mc := rfl
        have hx₂ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run
              ((((re, sgn), D₂), b₂), rl)) =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, sgn), D₂), b₂ || decide (mc.2 ∈ D₂)), mc.2 :: rl))) <$>
              roStep M re mc := rfl
        rw [hx₁, hx₂]
        refine (tsum_probOutput_map_mul _ _ G).trans
          ((tsum_congr fun cu => ?_).trans (tsum_probOutput_map_mul _ _ G).symm)
        exact congrArg _
          (ih cu.1 cu.2 sgn (mc.2 :: rl) D₁ (b₁ || decide (mc.2 ∈ D₁)) D₂
            (b₂ || decide (mc.2 ∈ D₂)))
      · -- SIGN: the body draws are `D`-independent; drawn list grows by the body's rejected
        -- commitments and the bad flag is preserved; `ih` (over all `D`) closes the continuations.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inr msg)) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (z.2.2.count w : ℝ≥0∞) with hG
        have hx₁ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run
              ((((re, sgn), D₁), b₁), rl)) =
            (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
              (alc.1.1, ((((alc.2, msg :: sgn), D₁ ++ alc.1.2), b₁), rl))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run re := rfl
        have hx₂ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run
              ((((re, sgn), D₂), b₂), rl)) =
            (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
              (alc.1.1, ((((alc.2, msg :: sgn), D₂ ++ alc.1.2), b₂), rl))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run re := rfl
        rw [hx₁, hx₂]
        refine (tsum_probOutput_map_mul _ _ G).trans
          ((tsum_congr fun alc => ?_).trans (tsum_probOutput_map_mul _ _ G).symm)
        exact congrArg _
          (ih alc.1.1 alc.2 (msg :: sgn) rl (D₁ ++ alc.1.2) b₁ (D₂ ++ alc.1.2) b₂)

omit [SampleableType Stmt] in
/-- **The value-substituted continuation read-multiplicity functional is drawn-invariant.** A
restatement of `deferredDrawRead_run_count_dl_invariant` reorganised for the body charge: the
expected read-multiplicity `E[Σ_{rc ∈ readlist} R.count rc]` of a *fixed* commit list `R` against
the continuation's recorded read list is invariant under the continuation's start drawn list (and
bad flag). The reads answer via `roStep` on the real layer, never the drawn (rejected) values, so
adding `R` (or any list) to the start drawn list does not change the read-list marginal. -/
theorem deferredDrawRead_run_sum_count_dl_invariant {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (R : List Commit) (re : (M × Commit →ₒ Chal).QueryCache) (sgn : List M)
    (rl : List Commit) (D₁ : List Commit) (b₁ : Bool) (D₂ : List Commit) (b₂ : Bool) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, sgn), D₁), b₁), rl)] * ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
      = ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, sgn), D₂), b₂), rl)] * ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) := by
  classical
  induction R with
  | nil => simp
  | cons w R ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      rw [show ∀ (D : List Commit) (b : Bool),
            (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                  ((((re, sgn), D), b), rl)] *
                (((z.2.2.count w : ℕ) : ℝ≥0∞) + ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞)))
              = (∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                      ((((re, sgn), D), b), rl)] * ((z.2.2.count w : ℕ) : ℝ≥0∞))
                + ∑' z : γ × DeferredReadState M Commit Chal,
                    Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                        ((((re, sgn), D), b), rl)] *
                      ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) from
          fun D b => by rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
      rw [deferredDrawRead_run_count_dl_invariant ids M maxAttempts pk sk oa w re sgn rl
            D₁ b₁ D₂ b₂, ih, ← ENNReal.tsum_add]
      exact tsum_congr fun z => by rw [mul_add]

omit [SampleableType Stmt] in
/-- **One step of the constant-length body charge (the genuine per-attempt induction step).** The
`succ` case of `ghostSignDrawBody_continuation_charge`: peel the head commit draw `ws` (kept
*averaged* — the head `ε`-kernel needs the full `ids.commit` marginal, a per-`ws` bound is false),
the challenge and the response, and case on the accept/reject branch. On *accept* the body records
nothing (charge `0`). On *reject* the recorded rejects are `ws.1 :: rec-rejects`; the
read-multiplicity splits into the head `z.readlist.count ws.1` (paid by the unconditional `+1` via
the value-substituted, gate-dropped marginal `ε`-kernel) and the recursive body charge (the
inductive hypothesis `ih` at the extended start drawn list `dr ++ [ws.1]`). The body never fails, so
the full-mass identities make the head `≤ L₀` match the RHS `+1`. -/
theorem ghostSignDrawBody_succ_charge {γ : Type}
    (qH : ℕ) (ε : ℝ) (_hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (msg : M)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hob : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (sgn : List M) (rl : List Commit) (bad : Bool) (n : ℕ)
    (re : (M × Commit →ₒ Chal).QueryCache) (dr : List Commit)
    (ih : ∀ (re : (M × Commit →ₒ Chal).QueryCache) (dr : List Commit),
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) *
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞)) :
    (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | (ghostSignDrawBody ids M pk sk msg (n + 1)).run re] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
              ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) *
        ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg (n + 1)).run re] *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
  classical
  set L₀ : ℝ≥0∞ := ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) with hL₀
  -- The continuation run never fails, so its output mass is `1`.
  have hcontMass : ∀ (u : ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
      (cache : (M × Commit →ₒ Chal).QueryCache) (D : List Commit),
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run
            ((((cache, sgn), D), bad), rl)]) = 1 := fun u cache D =>
    tsum_probOutput_eq_one'
      (deferredDrawRead_run_neverFail ids M maxAttempts pk sk (ob u) _)
  -- The signing body never fails, so its output mass is `1`.
  have hbodyMass : ∀ (re' : (M × Commit →ₒ Chal).QueryCache),
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re']) = 1 := by
    intro re'
    exact tsum_probOutput_eq_one' (by simp)
  -- Deterministic continuation-readlist bound: every continuation run started at read list `rl`
  -- with read budget `qH` records `≤ rl.length + qH` reads.
  have hlen : ∀ (u : ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
      (cache : (M × Commit →ₒ Chal).QueryCache) (D : List Commit)
      (z' : γ × DeferredReadState M Commit Chal),
      z' ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run
          ((((cache, sgn), D), bad), rl)) →
      (z'.2.2.length : ℝ≥0∞) ≤ ((rl.length + qH : ℕ) : ℝ≥0∞) := by
    intro u cache D z' hz'
    have := deferredDrawReadImpl_run_readlist_length_le ids M maxAttempts pk sk (ob u) qH
      (hob u) ((((cache, sgn), D), bad), rl) z' hz'
    exact_mod_cast this
  -- Per-`ws` value-substituted ungated head charge.
  set H : Commit × PrvState → ℝ≥0∞ := fun ws =>
    ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob rws.1.1)).run
              ((((rws.2, sgn), dr), bad), rl)] * ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞) with hH
  -- Per-`ws` recorded-length factor of the one-attempt body (RHS length factor minus the `+1`).
  set R : Commit × PrvState → ℝ≥0∞ := fun ws =>
    ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= alc | uniformSample Chal >>= fun ch =>
        ids.respond pk sk ws.2 ch >>= fun oz =>
          match oz with
          | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
          | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
              (ghostSignDrawBody ids M pk sk msg n).run re] *
        ((alc.1.2.length : ℕ) : ℝ≥0∞) with hR
  -- The per-`ws` head bound, summed over `ws` (gate dropped, value-substituted, `ε`-kernel).
  have hHead : (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * H ws) ≤ L₀ := by
    rw [hH]
    -- Per `(rws, z)` the inner `ws`-marginal of `z.count ws.1` is `≤ L₀`; the body and continuation
    -- have full mass, so the whole head expectation is `≤ L₀`.
    have hinner : ∀ (rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache)
        (z : γ × DeferredReadState M Commit Chal),
        z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob rws.1.1)).run
            ((((rws.2, sgn), dr), bad), rl)) →
        (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
          ≤ L₀ := by
      intro rws z hz
      calc (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
          ≤ ENNReal.ofReal ε * ((z.2.2.length : ℕ) : ℝ≥0∞) :=
            tsum_probOutput_commit_mul_count_le (ids.commit pk sk) z.2.2 ε (fun cm => hGuess cm)
        _ ≤ L₀ := by rw [hL₀]; gcongr; exact_mod_cast hlen rws.1.1 rws.2 dr z hz
    -- Rewrite the head as a single average over `(ws, rws, z)`, reorder, bound, and recombine.
    calc (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] *
                    ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
        = ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] *
                  (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                    ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞)) := by
          -- Fully distribute the probability weights, reorder `ws` innermost, recombine.
          simp_rw [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun rws => ?_
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun z => ?_
          refine tsum_congr fun ws => by ring
      _ ≤ ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] * L₀ := by
          refine ENNReal.tsum_le_tsum fun rws => ?_
          refine mul_le_mul' le_rfl ?_
          refine ENNReal.tsum_le_tsum fun z => ?_
          rcases eq_or_ne Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
              (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] 0 with hz | hz
          · rw [hz]; simp
          · gcongr
            exact hinner rws z ((mem_support_iff _ _).mpr hz)
      _ = L₀ * ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun rws => ?_
          rw [ENNReal.tsum_mul_right, ← mul_assoc, mul_comm _ L₀, mul_assoc]
      _ = L₀ := by
          have hone : (∑' rws : (Option (Commit × Resp) × List Commit) ×
              (M × Commit →ₒ Chal).QueryCache,
              Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)]) = 1 := by
            rw [← hbodyMass re]
            exact tsum_congr fun rws => by rw [hcontMass rws.1.1 rws.2 dr, mul_one]
          rw [hone, mul_one]
  -- The per-`ws` LHS inner bound: head + recursive (the inductive hypothesis).
  have h_ws : ∀ ws : Commit × PrvState,
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
              ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ H ws + L₀ * R ws := by
    intro ws
    -- Body-`n` expected `length + 1` (the reject-branch length factor; `+1` is the head commit).
    set Rr : ℝ≥0∞ :=
      ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
        ((rws.1.2.length + 1 : ℕ) : ℝ≥0∞) with hRr
    -- `R ws = Pr[reject ws] · Rr` (accept records length `0`; reject records `ws.1 :: rws`).
    have hR_eq : R ws = Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
        Rr := by
      rw [hR, probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
      simp only []
      rw [tsum_probOutput_bind_mul]
      refine tsum_congr fun ch => ?_
      rw [tsum_probOutput_bind_mul]
      -- Per response `oz`: accept records length `0`; reject records `(ws.1 :: rws).length`.
      have h_oz : ∀ oz : Option Resp,
          (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (match oz with
              | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
              | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re :
              ProbComp ((Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache))] * ((alc.1.2.length : ℕ) : ℝ≥0∞))
            = (if oz = none then Rr else 0) := by
        intro oz
        cases oz with
        | some z => rw [if_neg (by simp), tsum_probOutput_pure_mul]; simp
        | none =>
            rw [if_pos rfl, hRr, map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
            refine tsum_congr fun rws => ?_
            simp only [Function.comp]
            rw [tsum_probOutput_pure_mul]
            simp [List.length_cons]
      rw [tsum_eq_single (none : Option Resp) fun oz hoz => by
        rw [h_oz oz, if_neg hoz, mul_zero]]
      rw [h_oz none, if_pos rfl]; ring
    -- Peel the challenge `ch`. On *accept* the recorded list is empty (charge `0`); only the
    -- *reject* branch contributes, gated by `Pr[none | respond]`.
    rw [tsum_probOutput_bind_mul]
    -- Per-challenge: peel the response, then case on accept/reject.
    have h_ch : ∀ ch : Chal,
        (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
          ≤ Pr[= none | ids.respond pk sk ws.2 ch] * (H ws + L₀ * Rr) := by
      intro ch
      rw [tsum_probOutput_bind_mul]
      -- Per response `oz`: accept records nothing (charge `0`); reject = head + recursion.
      have h_oz : ∀ oz : Option Resp,
          (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (match oz with
              | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
              | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re :
              ProbComp ((Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache))] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                    ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                  ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
            ≤ (if oz = none then H ws + L₀ * Rr else 0) := by
        intro oz
        cases oz with
        | some z =>
            rw [if_neg (by simp), tsum_probOutput_pure_mul]
            simp
        | none =>
            rw [if_pos rfl, map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
            -- The reject branch: split the recorded count list `ws.1 :: rws.1.2` into head + tail.
            have hsplit : ∀ rws : (Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache,
                (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                  Pr[= alc | (pure ((rws.1.1, ws.1 :: rws.1.2), rws.2) :
                    ProbComp ((Option (Commit × Resp) × List Commit) ×
                      (M × Commit →ₒ Chal).QueryCache))] *
                    ∑' z : γ × DeferredReadState M Commit Chal,
                      Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                          (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                        ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
                  = (∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] *
                          ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
                    + ∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run
                            ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                          ((rws.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) := by
              intro rws
              rw [tsum_probOutput_pure_mul]
              simp only [List.map_cons, List.sum_cons, Nat.cast_add]
              rw [show dr ++ ws.1 :: rws.1.2 = (dr ++ [ws.1]) ++ rws.1.2 from by simp]
              rw [show (∑' z : γ × DeferredReadState M Commit Chal,
                    Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                        (ob rws.1.1)).run ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                      ((z.2.2.count ws.1 : ℝ≥0∞) +
                        ((rws.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞)))
                  = (∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run
                            ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                          ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
                    + ∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run
                            ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                          ((rws.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) from by
                rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
              -- Head: value-substitute the drawn list from `(dr ++ [ws.1]) ++ rws.1.2` to `dr`.
              congr 1
              exact deferredDrawRead_run_count_dl_invariant ids M maxAttempts pk sk (ob rws.1.1)
                ws.1 rws.2 sgn rl ((dr ++ [ws.1]) ++ rws.1.2) bad dr bad
            -- Now `h_oz none` reduces to: `∑'rws Pr[rws]·(head + rec) ≤ H ws + L₀·Rr`.
            simp only [Function.comp]
            simp_rw [hsplit, mul_add]
            rw [ENNReal.tsum_add]
            -- The head sum *is* `H ws`; the recursive sum is bounded by the inductive hypothesis.
            refine add_le_add (le_of_eq ?_) ?_
            · rw [hH]
            · -- `dr ++ [ws.1]` form matches the inductive hypothesis at the extended prefix.
              rw [hRr]
              refine le_trans ?_ (ih re (dr ++ [ws.1]))
              exact le_of_eq (tsum_congr fun x => by rw [List.append_assoc])
      -- Sum over `oz`: only the reject (`none`) term survives, gated by `Pr[none | respond]`.
      calc (∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
              ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= alc | (match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re :
                  ProbComp ((Option (Commit × Resp) × List Commit) ×
                    (M × Commit →ₒ Chal).QueryCache))] *
                  ∑' z : γ × DeferredReadState M Commit Chal,
                    Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                        (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                      ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
          ≤ ∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
              (if oz = none then H ws + L₀ * Rr else 0) :=
            ENNReal.tsum_le_tsum fun oz => by gcongr; exact h_oz oz
        _ = Pr[= none | ids.respond pk sk ws.2 ch] * (H ws + L₀ * Rr) := by
            rw [tsum_eq_single (none : Option Resp) fun oz hoz => by rw [if_neg hoz, mul_zero]]
            rw [if_pos rfl]
    -- Sum over `ch`: factor out the reject probability and fold via `hR_eq`.
    calc (∑' ch : Chal, Pr[= ch | uniformSample Chal] *
            ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= alc | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                    ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ∑' ch : Chal, Pr[= ch | uniformSample Chal] *
            (Pr[= none | ids.respond pk sk ws.2 ch] * (H ws + L₀ * Rr)) :=
          ENNReal.tsum_le_tsum fun ch => by gcongr; exact h_ch ch
      _ = (∑' ch : Chal, Pr[= ch | uniformSample Chal] *
            Pr[= none | ids.respond pk sk ws.2 ch]) * (H ws + L₀ * Rr) := by
          rw [← ENNReal.tsum_mul_right]; exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      _ = Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
            (H ws + L₀ * Rr) := by rw [probOutput_bind_eq_tsum]
      _ ≤ H ws + L₀ * R ws := by
          rw [mul_add, hR_eq]
          refine add_le_add (mul_le_of_le_one_left zero_le probOutput_le_one) ?_
          rw [← mul_assoc, mul_comm
            Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] L₀, mul_assoc]
  -- Assemble: unfold the `succ` body, peel the commit draw, apply `h_ws`, and split the sums.
  rw [run_ghostSignDrawBody_succ, tsum_probOutput_bind_mul]
  rw [tsum_probOutput_bind_mul]
  -- RHS inner equals `R ws + 1` (the body never fails, so the `+1` carries full mass).
  have hRinner : ∀ ws : Commit × PrvState,
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re] *
          ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞))
        = R ws + 1 := by
    intro ws
    have hmass : (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re]) = 1 :=
      tsum_probOutput_eq_one' (by simp)
    rw [hR]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | uniformSample Chal >>= fun ch =>
            ids.respond pk sk ws.2 ch >>= fun oz =>
              match oz with
              | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
              | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re] *
            ((alc.1.2.length : ℝ≥0∞) + 1))
        = (∑' alc, Pr[= alc | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (alc.1.2.length : ℝ≥0∞))
          + ∑' alc, Pr[= alc | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] from by
      rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add, mul_one]]
    rw [hmass]
  calc (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                  ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (H ws + L₀ * R ws) :=
          ENNReal.tsum_le_tsum fun ws => by gcongr; exact h_ws ws
      _ = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * H ws)
            + ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (L₀ * R ws) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun ws => by rw [mul_add]
      _ ≤ L₀ + ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (L₀ * R ws) := by
          gcongr
      _ = L₀ * ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= alc | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch >>= fun oz =>
                  match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re] *
                ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
          have hcommitMass : (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk]) = 1 :=
            tsum_probOutput_eq_one' (by simp)
          simp_rw [hRinner, mul_add, mul_one]
          rw [ENNReal.tsum_add, hcommitMass, mul_add, mul_one]
          rw [show (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (L₀ * R ws))
              = L₀ * ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * R ws from by
            rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun ws => by ring]
          rw [add_comm]

omit [SampleableType Stmt] in
/-- **The constant-length body charge (the genuine per-attempt induction).** Over one signing body
`ghostSignDrawBody n`, the expected continuation read-multiplicity of the body's *rejected* draws —
`E[Σ_{w ∈ body-rejects} continuation.readlist.count w]` — is at most `ε · (rl.length + qH) ·
E[#body-rejects + 1]`, where `rl` is the continuation's start read list and `qH` the continuation's
read-query budget (so the continuation's recorded read list has length `≤ rl.length + qH`
deterministically). The `+1` is the body's single unconditional signing query; it is *not* slack —
it pays the reject-gate skew of the head charge (see below).

Proved by induction on `n`:
* **0** — the body rejects nothing, the read-multiplicity is `0 ≤ ε · (rl.length + qH) · 1`.
* **n+1** — peel the head commit draw `ws` (kept *averaged*: the `ε`-kernel needs the full
  `ids.commit` marginal — a per-`ws` bound is false, the adversary could target a fixed `ws.1`),
  the challenge, the response, and case on the accept/reject branch. On *accept* the body records
  nothing (`rej = []`, charge `0`). On *reject* the recorded rejects are `ws.1 :: rec-rejects`; the
  read-multiplicity `Σ_{w ∈ ws.1 :: rec-rejects} z'.readlist.count w` splits as
  `z'.readlist.count ws.1` (head) plus the recursive body charge (recurses to the inductive
  hypothesis at the extended start drawn list `dr ++ [ws.1]`).

  Crucially the two halves treat the reject gate `1[respond = none]` differently:
  * the **head** charge `Σ_{ws} commit(ws) · 1[reject(ws.2)] · z'.readlist.count ws.1` drops the
    gate (`1[reject] ≤ 1`) — necessary because `ws.1` and the reject decision `f(ws.2, c)` are
    *correlated* (the prover state `ws.2` determines both the commit and the accept decision), so a
    gated kernel would skew the `ws.1` marginal. After value-substitution
    (`deferredDrawRead_run_sum_count_dl_invariant` moves `ws.1` out of the continuation's drawn
    list) and the marginal `ε`-kernel `tsum_probOutput_commit_mul_count_le`, the ungated head is
    `≤ ε · z'.readlist.length ≤ ε · (rl.length + qH)`, paid by the unconditional `+1`;
  * the **recursive** charge `Σ_{ws} commit(ws) · 1[reject(ws.2)] · (rec body charge)` *keeps* the
    gate, so it is `Pr[reject] · ε · (rl.length + qH) · E[#rec-rejects + 1]` (inductive hypothesis),
    which the reject paths of `#body-rejects` in the right-hand side exactly cover. Dropping the
    recursive gate would be unsound (it over-charges by the accept mass). -/
theorem ghostSignDrawBody_continuation_charge {γ : Type}
    (qH : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (msg : M)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hob : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (sgn : List M) (rl : List Commit) (bad : Bool) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache) (dr : List Commit),
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) *
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
  classical
  intro n
  induction n with
  | zero =>
      intro re dr
      simp only [ghostSignDrawBody, StateT.run_pure, tsum_probOutput_pure_mul, List.map_nil,
        List.sum_nil, Nat.cast_zero, mul_zero, tsum_zero]
      exact zero_le
  | succ n ih =>
      intro re dr
      -- The genuine per-attempt step; see `ghostSignDrawBody_succ_charge`.
      exact ghostSignDrawBody_succ_charge ids M maxAttempts qH ε hε pk sk hGuess msg ob hob sgn rl
        bad n re dr ih


omit [SampleableType Stmt] in
/-- **The sign-step value-free charge — the probabilistic core of the ghost-read bound.**
This is the single-query step of the inline-run induction
`readRecord_expected_pairs_nontape_general` at a *signing* query `Sum.inr msg`. The signing body
`ghostSignDrawBody` draws `maxAttempts` fresh commitments inline, records the *rejected* ones into
the drawn list, and runs the continuation `ob` from the post-body state; the goal bounds the
resulting expected pair count by the `s`-based pre-existing term plus `ε` times the `s`-based
new-attempt count.

The genuine content is concentrated here. Expanding the inductive hypothesis at the post-body state,
the only term not covered by the `s`-based pre-existing term and the slack of the `#attempt` count
is the **body charge** `E[Σ_{rc ∈ readlist} body-rejects.count rc]`, which must be bounded by
`ε · E[readlist.length · #body-attempts]` (where `#body-attempts = #body-rejects + 1`, the body's
single unconditional signing query providing the `+1`). Crucially the body's draws must remain
**averaged** (the sum over body outputs is retained, not factored): for a *fixed* body output the
recorded rejected commitment is a determined value, and a continuation adversary could read the
random oracle at exactly that value, so the per-output charge is not `≤ ε`. The `ε` arises only by
averaging each rejected commitment over the fresh `ids.commit pk sk` draw
(`tsum_probOutput_commit_mul_count_le`).

The charge is sound because the recorded read list is *value-free*: the continuation's
reads answer via `roStep` on the real layer and never the drawn (rejected) values, and the rejected
commitments are write-only (never cached; only accepted commitments are, via `cacheQuery`). The
value-substitution lemma `deferredDrawRead_run_count_dl_invariant` makes this precise: the
continuation's expected `readlist.count w` is invariant under the start drawn list, so the read list
is independent of every rejected draw's *value*. Combined with the body's draws being independent of
*reach* (a position is reached iff the earlier attempts rejected, which is determined by the earlier
draws — the body tape factorization `evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody` exhibits
this), each rejected draw charges its continuation read-multiplicity at the full marginal
`Pr[· | Prod.fst <$> commit] ≤ ε` (drop the reject indicator `≤ 1` on the value-substituted, hence
fixed, read list — no rejection-conditioning skew). The body's single unconditional signing query
(`+1`) pays the full-marginal head charge, and the read list `⊥` the attempt count factors
`E[readlist.length · #attempts] = E[readlist.length] · E[#attempts]`.

**Proof.** Unfold the sign step (`deferredDrawReadImpl … (Sum.inr msg)`), which maps each
signing-body output `alc` to the post-state with drawn list `s.drawn ++ alc.1.2` and signed list
`msg :: s.signed`. The continuation charge from the post-body state is bounded per `alc` by the
inductive hypothesis `ih`; its pre-existing drawn count splits via `List.count_append` into the
start drawn count (matched against the right-hand side) and the *body coincidence*
`E[Σ_{rc ∈ readlist} alc.1.2.count rc]`, which the bilinear count swap `sum_map_count_comm` recasts
as `E[Σ_{w ∈ alc.1.2} readlist.count w]` and `ghostSignDrawBody_continuation_charge` bounds by
`ε · (rl.length + qH) · E[#attempts + 1]`. The slack length factor recombines via the deterministic
prefix monotonicities `deferredDrawRead_run_drawn_prefix` / `deferredDrawRead_run_signed_prefix`:
the gap between the start slack and the post-body slack is exactly `alc.1.2.length + 1` (the body's
rejected draws plus the single signing query), which the body's `+1` term covers. The continuation
run's full mass (`deferredDrawRead_run_neverFail`) makes the constant-length factor `L₀` exact. -/
theorem nontape_signStep_charge {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (_hp₀ : 0 ≤ p_abort) (_hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (_hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (msg : M)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s : DeferredReadState M Commit Chal)
    (hob : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (ih : ∀ (u : ((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
        (s' : DeferredReadState M Commit Chal),
        (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH →
        (∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run s'] *
              ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
          ≤ (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run s'] *
                ((z.2.2.map (fun rc => s'.1.1.2.count rc)).sum : ℝ≥0∞))
            + ENNReal.ofReal ε * ((s'.2.length + qH : ℕ) : ℝ≥0∞) *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run s'] *
                  (((z.2.1.1.2.length - s'.1.1.2.length)
                    + (z.2.1.1.1.2.length - s'.1.1.1.2.length) : ℕ) : ℝ≥0∞)) :
    (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        ((Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z |
                  (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
          + ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) *
            (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z |
                    (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                  (((z.2.1.1.2.length - s.1.1.2.length)
                    + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞))) := by
  classical
  set L₀ : ℝ≥0∞ := ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) with hL₀
  -- Unfold the sign step: it maps each signing-body output `alc` to the post-state with drawn list
  -- `s.drawn ++ alc.1.2` and signed list `msg :: s.signed`. Convert all three sign-step averages to
  -- averages over the signing-body output `alc`.
  have hLHS : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞) :=
    tsum_probOutput_map_mul _ _ _
  have hRHS1 : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
      = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞) :=
    tsum_probOutput_map_mul _ _ _
  have hRHS2 : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        L₀ * (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (((z.2.1.1.2.length - s.1.1.2.length)
                + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞)))
      = L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                (((z.2.1.1.2.length - s.1.1.2.length)
                  + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.tsum_mul_left]; exact congrArg (L₀ * ·) (tsum_probOutput_map_mul _ _ _)
  -- Rewrite all three sums to body averages; the RHS is `(pre-existing) + L₀ · (slack)`.
  rw [hLHS]
  rw [ENNReal.tsum_add]
  conv_rhs => rw [show (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) *
          (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z |
                  (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                (((z.2.1.1.2.length - s.1.1.2.length)
                  + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞)))
      = ∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        L₀ * (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z |
                (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (((z.2.1.1.2.length - s.1.1.2.length)
                + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞)) from
    tsum_congr fun x => by rw [hL₀]]
  rw [hRHS1, hRHS2]
  -- Both sides are now body averages; bound the LHS per `alc` by the inductive hypothesis at the
  -- post-body state, splitting the pre-existing drawn count and applying induction (1) to the body
  -- coincidence and the slack length identities.
  -- The body-coincidence charge `E_alc[E_z[Σ_{rc∈readlist} alc.1.2.count rc]]` is bounded by
  -- induction (1) (after the bilinear count swap `sum_map_count_comm`).
  have hbody : (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
              ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
            ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
      ≤ L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
    rw [hL₀]
    exact ghostSignDrawBody_continuation_charge ids M maxAttempts qH ε hε pk sk hGuess msg ob
      (fun u => hob u) (msg :: s.1.1.1.2) s.2 s.1.2 maxAttempts s.1.1.1.1 s.1.1.2
  -- The continuation runs never fail, so their mass is `1`.
  have hcontMass : ∀ alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
            ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)]) = 1 := fun alc =>
    tsum_probOutput_eq_one' (deferredDrawRead_run_neverFail ids M maxAttempts pk sk (ob alc.1.1) _)
  -- Per `alc`: split the pre-existing drawn count and rewrite the slack via the prefix lemmas.
  -- The slack inner sum splits as the post-body inductive slack plus the body's `#attempts + 1`.
  have hslack : ∀ (alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache),
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
            ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
          (((z.2.1.1.2.length - s.1.1.2.length)
            + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞))
      = (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
              ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
            (((z.2.1.1.2.length - (s.1.1.2 ++ alc.1.2).length)
              + (z.2.1.1.1.2.length - (msg :: s.1.1.1.2).length) : ℕ) : ℝ≥0∞))
        + ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
    intro alc
    rw [show ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞)
        = (∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)]) *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) from by rw [hcontMass alc, one_mul]]
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
        (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))
    · have hdr := deferredDrawRead_run_drawn_prefix ids M maxAttempts pk sk (ob alc.1.1)
        ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2) z hz
      have hsg := deferredDrawRead_run_signed_prefix ids M maxAttempts pk sk (ob alc.1.1)
        ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2) z hz
      simp only at hdr hsg
      rw [← mul_add]
      congr 1
      rw [← Nat.cast_add]
      congr 1
      simp only [List.length_append, List.length_cons] at hdr hsg ⊢
      omega
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul, zero_mul, add_zero]
  -- Per `alc`: the inductive hypothesis at the post-body state, with the pre-existing drawn count
  -- split into the start drawn count and the body coincidence (the bilinear count swap).
  have h_alc : ∀ (alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache),
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
            ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
              ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
            ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
        + (∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
              ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
          + L₀ * ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
                (((z.2.1.1.2.length - (s.1.1.2 ++ alc.1.2).length)
                  + (z.2.1.1.1.2.length - (msg :: s.1.1.1.2).length) : ℕ) : ℝ≥0∞) := by
    intro alc
    have hih := ih alc.1.1 ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)
      (hob alc.1.1)
    -- The post-state read list is `s.2`, so the read-length factor is `L₀`.
    simp only [hL₀.symm] at hih ⊢
    refine le_trans hih (le_of_eq ?_)
    congr 1
    -- Pre-existing drawn count `(s.drawn ++ alc.1.2).count` splits into `s.drawn.count` plus the
    -- body coincidence (via the bilinear count swap).
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    rw [← mul_add]
    congr 1
    rw [← Nat.cast_add]
    congr 1
    rw [show (z.2.2.map (fun rc => (s.1.1.2 ++ alc.1.2).count rc))
        = z.2.2.map (fun rc => s.1.1.2.count rc + alc.1.2.count rc) from
      List.map_congr_left fun rc _ => by rw [List.count_append]]
    rw [List.sum_map_add, sum_map_count_comm alc.1.2 z.2.2]
  -- Assemble: sum the per-`alc` bound, split into pre-existing + body-coincidence + ih-slack, then
  -- recombine the slack via `hslack` (the `#attempts + 1` gap) and the coincidence via `hbody`.
  refine le_trans (ENNReal.tsum_le_tsum fun alc => mul_le_mul' le_rfl (h_alc alc)) ?_
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, add_assoc]
  refine add_le_add le_rfl ?_
  -- The body coincidence plus the post-body inductive slack equal `L₀ · (the full RHS slack)`.
  have hslackSum :
      L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞)
        + (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (L₀ * ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                      s.2)] *
                  (((z.2.1.1.2.length - (s.1.1.2 ++ alc.1.2).length)
                    + (z.2.1.1.1.2.length - (msg :: s.1.1.1.2).length) : ℕ) : ℝ≥0∞)))
      = L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                (((z.2.1.1.2.length - s.1.1.2.length)
                  + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun alc => ?_
    rw [hslack alc, mul_add, add_comm]
    ring
  rw [← hslackSum]
  exact add_le_add hbody le_rfl

omit [SampleableType Stmt] in
/-- **The general per-pair charge over the inline read-recording run (induction carrier).** For an
arbitrary start state `s`, the expected pair count `E[Σ_{rc ∈ readlist} drawnlist.count rc]` is at
most the *un-charged pre-existing* contribution `E[Σ_{rc ∈ readlist} s.drawnlist.count rc]` (the
start drawn list, which the adversary may target deterministically) plus `ε` times the expected
`readlist.length · #new-attempts`, where `#new-attempts` counts only the draws and signing queries
made *after* `s` (the new drawn-list and signed-list growth). The base instance (empty start drawn
list) has a zero pre-existing term, giving `readRecord_expected_pairs_nontape_le`.

By induction on `oa`:
* **pure** — readlist and drawn list are the start ones; the pre-existing term *is* the pair count
  and there are no new attempts (equality).
* **read** — the drawn and signed lists are unchanged, so the bound passes through the inductive
  hypothesis (the bound never references the start *read* list, only the final one).
* **sign** — the body's fresh rejected draws extend the drawn list; the inductive hypothesis charges
  them as part of the continuation's pre-existing term, which splits as the genuine pre-existing
  term plus the body's contribution `E[Σ_{rc ∈ readlist} body-rejects.count rc]`, bounded by
  `ε · E[readlist.length · #body-rejects]` via the body-charge `nontape_signStep_body_charge` (the
  body's rejected values are independent of the value-free final read list); the residual `#new`
  attempt slack (`+1` per query) is absorbed. -/
theorem readRecord_expected_pairs_nontape_general {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hQ : oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (s : DeferredReadState M Commit Chal) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
        + ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
              (((z.2.1.1.2.length - s.1.1.2.length)
                + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞) := by
  classical
  induction oa using OracleComp.inductionOn generalizing s qH with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      simp only [add_zero, Nat.sub_eq_zero_of_le (le_refl _), Nat.cast_zero, mul_zero, add_zero]
      exact le_refl _
  | query_bind t ob ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul,
        ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      rcases t with (n | mc) | msg
      · -- UNIFORM: the step is deterministic in the state (`x.2 = s`); factor per step output and
        -- apply the inductive hypothesis directly (drawn / signed / read lists unchanged, budget
        -- unchanged: uniform queries are not read queries).
        have hQ2' : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH := by
          intro u; exact hQ2 u
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support ((deferredDrawReadImpl ids M maxAttempts pk sk
            (Sum.inl (Sum.inl n))).run s)
        · have hxs : x ∈ support ((fun u => (u, s)) <$>
              (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
          rw [support_map] at hxs
          obtain ⟨u, _, rfl⟩ := hxs
          beta_reduce
          rw [mul_left_comm (ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞)), ← mul_add]
          gcongr
          exact ih u qH (hQ2' u) s
        · rw [probOutput_eq_zero_of_not_mem_support hx]; simp
      · -- READ: the post-state drawn / signed lists are unchanged; the read list grows by one and
        -- the read budget decrements by one, so the constant `readlist.length + qH` is preserved.
        have hpos : 0 < qH := by
          rcases hQ1 with h | h
          · exact absurd rfl h
          · exact h
        have hQ2' : ∀ cu : Chal × (M × Commit →ₒ Chal).QueryCache,
            (ob cu.1).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) (qH - 1) := by
          intro cu; exact hQ2 cu.1
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support ((deferredDrawReadImpl ids M maxAttempts pk sk
            (Sum.inl (Sum.inr mc))).run s)
        · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                  mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc) := hx
          rw [support_map] at hxs
          obtain ⟨cu, _, rfl⟩ := hxs
          beta_reduce
          have hconst : ((s.2.length + qH : ℕ) : ℝ≥0∞)
              = (((mc.2 :: s.2).length + (qH - 1) : ℕ) : ℝ≥0∞) := by
            simp only [List.length_cons]; congr 1; omega
          rw [hconst, mul_left_comm (ENNReal.ofReal ε * (((mc.2 :: s.2).length + (qH - 1) : ℕ) :
            ℝ≥0∞)), ← mul_add]
          gcongr
          exact ih cu.1 (qH - 1) (hQ2' cu) ((((cu.2, s.1.1.1.2), s.1.1.2),
            s.1.2 || decide (mc.2 ∈ s.1.1.2)), mc.2 :: s.2)
        · rw [probOutput_eq_zero_of_not_mem_support hx]; simp
      · -- SIGN: the body's fresh rejected draws extend the drawn list; the body charge must keep
        -- the body draws *averaged* (a fixed body output lets the adversary target the recorded
        -- value), so the sum over body outputs is retained. The read budget is unchanged (signing
        -- is not a read query), so the continuation's `readlist.length` is bounded by the same
        -- constant `s.2.length + qH`. This is the value-free sign-step charge.
        have hQ2' : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH := by
          intro u; exact hQ2 u
        exact nontape_signStep_charge ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk hGuess
          hAbort msg ob s hQ2' (fun u s' hQ' => ih u qH hQ' s')

omit [SampleableType Stmt] in
/-- **The value-free per-pair charge over the *inline* (non-tape) read-recording run — the direct
characterization consumed by `readRecord_expected_coincidences_le`.** The expected pair count
`E[Σ_{rc ∈ readlist} drawnlist.count rc]` of the `deferredDrawReadImpl` run is at most `ε · qH`
times the expected attempt count.

In this representation each rejected commitment is drawn *inline* at its signing step, so each fresh
draw sits in the independent-of-the-readlist position required by the atomic value-free charge
`tsum_probOutput_commit_mul_count_le`: the recorded reads answer from `roStep` on the real layer and
never the drawn (rejected) values, so the final read list is independent of every rejected draw.
The proof instantiates the inline-run induction `readRecord_expected_pairs_nontape_general` at the
empty-drawn-list start state, where the pre-existing term vanishes and the constant read-length
factor collapses to the read budget `qH`.

The charge is against `#attempts := drawnlist.length + (signedlist.length − l.length)`
(= #rejects + #signing-queries), whose mean is `qSrem/(1-p)`; the `drawnlist.length`-only form is
unsound (it omits the accepting attempts' fresh draws). The start drawn list is empty
(no pre-existing draws the adversary could target deterministically).

The same inequality over the front-loaded tape representation is
`readRecord_expected_pairs_tape_le`; see also `readRecord_expected_pairs_le`, which restates this
bound with the tape's signing-query budget `qSrem` in scope. Both are separate reusable
infrastructure and are not on the live path. -/
theorem readRecord_expected_pairs_nontape_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hQ : oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, l), []), false), [])] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
  -- Instantiate the general carrier at the empty-drawn-list start state: the pre-existing term
  -- vanishes (`[].count _ = 0`), the constant read-length factor `s.2.length + qH` becomes `qH`
  -- (empty start read list), and `#new-attempts` becomes the target `#attempts`.
  have hgen := readRecord_expected_pairs_nontape_general ids M maxAttempts qH ε p_abort hp₀ hp hε
    pk sk hGuess hAbort oa hQ ((((re, l), []), false), [])
  simp only [List.count_nil, List.map_const', List.sum_replicate, smul_zero, Nat.sub_zero,
    List.length_nil, Nat.cast_zero, mul_zero, tsum_zero, zero_add] at hgen
  exact hgen

omit [SampleableType Stmt] in
/-- **The value-free per-pair charge in the tape-factored representation.** Separate reusable
infrastructure: the same bound as `readRecord_expected_pairs_nontape_le`, stated over the
front-loaded run produced by `evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`, in which the
read-recording run reads `drawList (ids.commit pk sk) (maxAttempts·qSrem) >>= fun tape => …` with
the draw tape sampled *upfront* as one independent block. It is not on the live path of
`readRecord_expected_coincidences_le`, which consumes the inline form directly.

In this representation the recorded drawn list is a function of the tape (its rejected entries)
while the recorded read list is **value-free** (the reads answer from `roStep` on the real layer,
never the tape values), so the read list is manifestly independent of the tape values. The
proof transports each tape probability back to the corresponding inline `deferredDrawReadImpl`
probability through the fold equality and applies `readRecord_expected_pairs_nontape_le`.

**The charge is against `#attempts`, not `drawnlist.length`.** The per-position reading of the bound
takes each *consumed* tape position (dropping the reject check): `drawnlist.count rc ≤ #consumed
positions k with `tape[k].1 = rc``, and for a fixed position `tape[k]` is a fresh raw
`Prod.fst <$> ids.commit` draw of mass `≤ ε` (`hGuess`), independent of the value-free `rc` and of
whether `k` is reached (reach depends only on *earlier* tape entries), giving
`≤ ε · readlist.length · #consumed`. The RHS therefore uses
`#attempts := drawnlist.length + (signedlist.length − l.length)`
(= #rejects + #signing-queries `≥` #consumed), whose mean is `qSrem/(1-p)`
(`deferredDrawRead_attemptKn_mean_le`). A `drawnlist.length`-form RHS would be false, since
charging all consumed positions exceeds the rejected-only count by the accepted positions,
`ε · E[#accepts]`.

The structural fact underlying the tape reading is *functional*, not distributional: the
accept/reject decision of `tapeSignBody` on the head `(w, st)` is `ids.respond pk sk st c = none`,
which depends on the `PrvState` part `st` and the challenge `c` but **not on the `Commit` part
`w`**. So for any fixed state and challenge randomness, at a position the body *rejects*, replacing
`tape[k].1 = w` by any other `w'` leaves the output, the real cache, and (therefore, through the
value-free `roStep` read channel) the recorded read list unchanged — only the recorded drawn list
changes. The accept branch returns `(some (w, z), [])`, so `w` enters the output/signature there,
which is why the reject indicator excludes accepted positions; the reject branch records `w`
write-only into the drawn list. On the inline route this same value-substitution fact is
`deferredDrawRead_run_count_dl_invariant`. -/
theorem readRecord_expected_pairs_tape_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ)
    (hQ : FiatShamir.signHashQueryBound M (S' := Option (Commit × Resp)) (oa := oa) qSrem qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
                (((((re, l), []), false), []), tape)] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
              (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                  (p.1, p.2.1)) <$>
                (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
                  (((((re, l), []), false), []), tape)] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
  -- The content is the per-position value-free charge. The independence it rests on is
  -- `readlist ⊥ (rejected tape position's VALUE)`: the tape→readlist channel runs only through
  -- signatures (= ACCEPTED entries), so a rejected position's `Commit` value never enters any read
  -- target or query answer (reads answer via `roStep` on the real layer). Front-loading the draws
  -- (`evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`) exhibits the draws as one independent
  -- block but does not by itself supply that independence.
  -- Transport BACK to the non-tape run via the fold equality: every tape probability equals the
  -- corresponding non-tape `deferredDrawReadImpl` run probability. This makes the recorded draws
  -- *inline-fresh* (drawn at each sign step) rather than front-loaded, which is the position in
  -- which each rejected draw is independent of the (value-free) final read list, and lets
  -- `readRecord_expected_pairs_nontape_le` discharge the goal.
  have hfold := evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead ids M maxAttempts pk sk oa qSrem
    hQ.1 ((((re, l), []), false), [])
  have hpr : ∀ z : γ × DeferredReadState M Commit Chal,
      Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
          (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
              (p.1, p.2.1)) <$>
            (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
              (((((re, l), []), false), []), tape)] =
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] :=
    fun z => by rw [probOutput_def, probOutput_def, ← hfold]
  simp only [hpr]
  exact readRecord_expected_pairs_nontape_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
    hGuess hAbort oa hQ.2 re l

omit [SampleableType Stmt] in
/-- **The value-free per-pair atom, stated with the signing-query budget `qSrem` in scope.**
Separate reusable infrastructure obtained by routing `readRecord_expected_pairs_nontape_le` through
the tape representation and back; it is not on the live path of
`readRecord_expected_coincidences_le`, which consumes the inline form directly.

The expected pair count — the expected number of coinciding
`(recorded read-commit, recorded drawn commit)` pairs, `E[Σ_{rc ∈ readlist} drawnlist.count rc]` —
is at most `ε · qH` times the expected attempt count. The content is the per-pair value-free
independence: for every `(read slot, draw slot)` pair, `E[1[rc = d]] ≤ ε`, because
* each recorded drawn commit `d` is a fresh i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw of mass
  `≤ ε` (`hGuess`), recorded write-only on rejected attempts (the accept branch records `[]`);
* the recorded read-commit list is **value-free** — the reads answer from the real RO layer via
  `roStep`, never the drawn values (`blindStepProj_map_ghostBlindImpl_indep` /
  `ghostHybridImpl_proj_trans`), so the readlist is jointly independent of the drawn *values*.

Summing the per-pair bound over the `readlist.length · drawnlist.length` pairs gives the claim. The
factoring `E[Σ_pairs 1[rc=d]] = Σ_pairs E[1[rc=d]]` cannot be read off a single step of the opaque
adversary `simulateQ (oa)` fold: a draw-before-read pair has its draw resolved before the later
read, so the read-step increment is deterministic in the pre-state and is not `≤ ε` at that step.
What supplies the bound instead is the global independence of the readlist law from the
drawn-value law, established on the inline route by the value-substitution invariant
`deferredDrawRead_run_count_dl_invariant` inside `nontape_signStep_charge`.

**Tape factorization.** The same independence is exhibited representationally by the two halves of
the tape factorization: `evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody` recasts one signing
body's inline attempt draws as consumption from a pre-drawn tape
(`𝒮[(ghostSignDrawBody … n).run re] = 𝒮[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`)
via the local i.i.d. resampling commute `evalSPMF_bind_comm_probComp`, and
`evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead` lifts that across the `simulateQ (oa)` fold, so
the per-query tape blocks of every interleaved signing query commute to the very front as a single
independent draw block of `maxAttempts · qSrem` commitments, past the adaptive read points.

The surrounding reduction is `countP_mem_le_sum_count`, the deterministic readlist-length bound
`deferredDrawReadImpl_run_readlist_length_le`, the expected drawn-list length fold
`deferredDrawRead_run_expected_drawnlist_length_le`, and the final arithmetic. -/
theorem readRecord_expected_pairs_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ)
    (hQ : FiatShamir.signHashQueryBound M (S' := Option (Commit × Resp)) (oa := oa) qSrem qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, l), []), false), [])] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
  classical
  -- STEP C: transport both expectations through the fold-level tape factorization, so the recorded
  -- draws become a function of the front tape and the value-free read list becomes independent of
  -- the tape values.
  have hfold := evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead ids M maxAttempts pk sk oa qSrem
    hQ.1 ((((re, l), []), false), [])
  have hpr : ∀ z : γ × DeferredReadState M Commit Chal,
      Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
          ((((re, l), []), false), [])] =
        Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
                (((((re, l), []), false), []), tape)] :=
    fun z => by rw [probOutput_def, probOutput_def, hfold]
  simp only [hpr]
  -- The per-pair charge in the tape-factored representation: with `drawnlist = f(tape)` (recorded
  -- rejected tape entries) and `readlist` value-free (`roStep`), each `(read slot, draw slot)` pair
  -- charges at most `ε` by `hGuess` (each tape entry is a fresh raw `Prod.fst <$> ids.commit` draw
  -- of mass `≤ ε`, independent of the value-free read points).
  exact readRecord_expected_pairs_tape_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
    hGuess hAbort oa qSrem hQ re l

omit [SampleableType Stmt] in
/-- **The expected-coincidence-count bound (the numeric core of the first-moment route).**
The read-recording run's expected coincidence count
`E[#{ rc ∈ readlist : rc ∈ drawnlist }]` — the first moment fed by the Markov step
`readRecord_pred_le_expected_coincidences` — is at most `qSrem · (qH+1) · ε / (1-p)`.

This is the σ-free numeric form of the ghost-read charge (no front-loaded game, no all-miss
strategy `σ`): both the headline ghost-read bound and the `euf_cma` proof are charged through this
single numeric inequality.

**The accounting (why this is TRUE and additive — no per-output skew).** The coincidence count is a
double sum `Σ_{rc ∈ readlist} Σ_{d ∈ drawnlist} 1[rc = d]`, hence purely additive; the
rejection-conditioning skew that broke every `Pr[bad]` / per-output route lives in
output-conditioning, never in a SUM. Bounding `E[count]` decomposes over (read, draw) pairs:
* each recorded drawn commit `d` is a fresh i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw of mass
  `≤ ε` (`hGuess`), recorded write-only on rejected attempts (the accept branch records `[]`);
* the recorded read-commit list is **value-free** — the reads answer from the real RO layer via
  `roStep`, never the drawn values (`blindStepProj_map_ghostBlindImpl_indep` /
  `ghostHybridImpl_proj_trans`), so the readlist is jointly independent of the drawn *values*;
* by that independence, for each pair `E[1[rc = d]] ≤ ε`, and there are `≤ (qH+1) · E[#attempts]`
  pairs (`(qH+1)` reads by `hQ`, `E[#attempts] ≤ qSrem/(1-p)` by `deferredDraw_attemptKn_mean_le`),
  giving `E[count] ≤ (qH+1) · ε · E[#attempts] ≤ qSrem · (qH+1) · ε / (1-p)`.

**The reduction.** The bound reduces by elementary arithmetic to a
single value-free atom (see the scaffolding lemmas above):
* the coincidence count is dominated pointwise by the pair count
  `Σ_{rc ∈ readlist} drawnlist.count rc` (`countP_mem_le_sum_count`);
* the recorded readlist has length `≤ qH` on the whole support — a *deterministic* bound from the
  read-query budget (`deferredDrawReadImpl_run_readlist_length_le`, empty start readlist);
* the expected drawn-list length is `≤ qSrem · (1/(1-p))` (`deferredDrawRead_run_expected_…`, empty
  start drawnlist);
* the genuine content is the **value-free per-pair atom**
  `readRecord_expected_pairs_nontape_le`:
  `E[Σ_{rc ∈ readlist} drawnlist.count rc] ≤ ε · E[readlist.length · drawnlist.length]`.

**Where the probabilistic content sits.** The arithmetic after factoring the joint expectation is
linear and discharged here; the factoring itself — that each fresh draw is conditionally i.i.d. and
`⊥` the recorded readlist *through the opaque adversary `simulateQ (oa)` fold* — is supplied by
`readRecord_expected_pairs_nontape_le`. A threaded fold charges the *sign* steps directly (each
fresh draw `⊥` the *current* readlist, value-free, additive), but a *draw-before-read* pair has its
draw resolved before the later read, so the read-step increment `1[mc.2 ∈ drawnlist]` is
deterministic in the pre-state and is not `≤ ε` at that single step. What covers it is the global
independence of the readlist law from the drawn-value law, established as the value-substitution
invariant `deferredDrawRead_run_count_dl_invariant` carried through
`readRecord_expected_pairs_nontape_general` / `nontape_signStep_charge`.

The start drawn list is empty (`ws₀ = []`): the bound is sound only with no pre-existing draws,
since the adversary's read points are value-free w.r.t. the run's fresh draws but can
deterministically target a fixed pre-existing commitment. The headline instance uses the empty
start. -/
theorem readRecord_expected_coincidences_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ)
    (hQ : FiatShamir.signHashQueryBound M (S' := Option (Commit × Resp)) (oa := oa) qSrem qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          (z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) : ℝ≥0∞))
      ≤ ENNReal.ofReal ((qSrem : ℝ) * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  classical
  obtain ⟨hQS, hQH⟩ := hQ
  set run : ProbComp (γ × DeferredReadState M Commit Chal) :=
    (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run ((((re, l), []), false), [])
    with hrun
  -- Step 1+2: dominate the coincidence count pointwise by the pair count.
  have hstep12 :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          (z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) : ℝ≥0∞))
        ≤ ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
            ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞) := by
    refine ENNReal.tsum_le_tsum fun z => ?_
    gcongr
    exact_mod_cast countP_mem_le_sum_count z.2.2 z.2.1.1.2
  -- Step 3 (the atom): the expected pair count is `≤ ε · qH · E[#attempts]`, where the read-list
  -- length is dominated *deterministically* by the read-query budget `qH` (the constant factor
  -- threaded through the carrier), and `#attempts := drawnlist.length + (signedlist.length −
  -- l.length)` (= #rejects + #queries). The `#attempts` (not `drawnlist.length = #rejects`) factor
  -- is the sound charge: charging per consumed tape position (drop-reject) covers all reached
  -- attempts, which dominates the rejected ones; its mean is the same `qSrem/(1-p)` as the drawn.
  have hatom :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
        ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
          ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
    rw [hrun]
    exact readRecord_expected_pairs_nontape_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
      hGuess hAbort oa hQH re l
  -- Step 5: `E[#attempts] ≤ qSrem · (1/(1-p))` (empty start drawnlist;
  -- `deferredDrawRead_attemptKn_mean_le`).
  have hdraw :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞))
        ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [hrun]
    exact deferredDrawRead_attemptKn_mean_le ids M maxAttempts pk sk hp₀ hp hAbort
      oa qSrem hQS re l
  -- Assemble the chain and convert to the target `ofReal` form. The exposed `(qH+1)` constant is
  -- the (loose) weakening of the deterministic read-length bound `qH`.
  refine le_trans hstep12 (le_trans hatom ?_)
  have hchain : ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)
      ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) * (qSrem : ℝ≥0∞) *
        ENNReal.ofReal (1 / (1 - p_abort)) := by
    calc ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
            ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
              ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)
        ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) *
            ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
              ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) := by
          gcongr
          · exact le_self_add
      _ ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) *
            ((qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort))) := by
          rw [mul_assoc, mul_assoc]
          gcongr
      _ = ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) * (qSrem : ℝ≥0∞) *
            ENNReal.ofReal (1 / (1 - p_abort)) := by ring
  refine le_trans hchain (le_of_eq ?_)
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  rw [show ((qH : ℝ≥0∞) + 1) = ENNReal.ofReal ((qH : ℝ) + 1) by
        rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp,
      show ((qSrem : ℝ≥0∞)) = ENNReal.ofReal (qSrem : ℝ) by simp]
  rw [← ENNReal.ofReal_mul hε, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

omit [SampleableType Stmt] in
/-- **Ghost-blind ghost-read bound** (the sound headline target). The ghost-blind run's
adversarial-read bad mass is at most `qS·(qH+1)·ε/(1-p)`, via the first-moment route: the eager bad
mass is reduced to the deferred-draw run (`ghostBlind_bad_le_deferredDraw`), then to the
read-recording final-state read-hit predicate (`deferredDraw_bad_le_readRecord`), then to the
expected coincidence count by the Markov step (`readRecord_pred_le_expected_coincidences`),
which is finally charged by the numeric value-free bound `readRecord_expected_coincidences_le`.
Chaining with `probEvent_ghostHybridImpl_bad_le_ghostBlind` discharges the eager form
(`probEvent_ghostRead_bad_le`). -/
theorem probEvent_ghostBlindImpl_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  -- The first-moment route: reduce the eager bad mass to the deferred-draw run, then to the
  -- read-recording final-state predicate, then to the expected coincidence count (the Markov
  -- step), and charge that count by the numeric value-free bound.
  refine le_trans (ghostBlind_bad_le_deferredDraw ids M maxAttempts pk sk (adv.main pk)
    ((((∅, ∅), []), false) : GhostState M Commit Chal)
    ((((∅, []), []), false) : DeferredState M Commit Chal)
    ⟨rfl, rfl, fun mc h => absurd rfl h, by simp⟩) ?_
  refine le_trans (deferredDraw_bad_le_readRecord ids M maxAttempts pk sk (adv.main pk)
    ((((∅, []), []), false) : DeferredState M Commit Chal)
    (((((∅, []), []), false), []) : DeferredReadState M Commit Chal)
    ⟨rfl, fun h => absurd h (by simp)⟩) ?_
  refine le_trans (readRecord_pred_le_expected_coincidences ids M maxAttempts pk sk (adv.main pk)
    (((((∅, []), []), false), []) : DeferredReadState M Commit Chal)) ?_
  exact readRecord_expected_coincidences_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
    hGuess hAbort (adv.main pk) qS (hQ pk) ∅ []

omit [SampleableType Stmt] in
/-- **Ghost-read collision bound** for the Prog → Trans hop: the probability that the
adversary ever queries the random oracle at a ghost point (a rejected signing attempt's
programmed point) is at most `qS·(qH+1)·ε/(1-p)`.

Probabilistic content (deferred sampling): a rejected attempt's commitment `w` enters
the ghost layer with the joint law of `(w, c)` conditioned on rejection, and influences
the run only through the ghost-domain membership tests of later adversarial queries.
Per (rejected attempt `j`, adversarial query `k`) pair, the conditional independence of
the post-rejection run from `w` given the rejection event yields
`Pr[query k hits attempt j] ≤ Pr[attempt j runs] · ε` (the `1/Pr[reject]` skew of the
conditioned commitment law cancels against the rejection probability of the attempt).
Summing the expected number of attempts (`≤ 1/(1-p)` per signing query by `hAbort`)
against the `qH` adversarial queries (`hQ`) gives the bound; the budget `qH + 1` leaves
one unit of slack for a verification read, which the freshness check already rules out
(see `ghostHybridImpl_preserves_signed_inv`).

The abort probability is assumed to lie in `[0, 1)` (`hp₀`, `hp`), which is what makes the
geometric attempt factor `1/(1 - p_abort)` well defined and at least `1`; `hε : 0 ≤ ε` matches
the per-attempt guessing bound `hGuess`, and `hQ` pins the query budgets `(qS, qH)` of
`adv.main pk`. The proof reduces the eager ghost-read bad mass to the ghost-blind run
(`probEvent_ghostHybridImpl_bad_le_ghostBlind`, identical until bad) and closes it with the
first-moment bound `probEvent_ghostBlindImpl_bad_le`. -/
lemma probEvent_ghostRead_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
  -- M1 reduces the eager ghost-read bad mass to the ghost-blind run's bad mass
  -- (`probEvent_ghostHybridImpl_bad_le_ghostBlind`, identical until bad), and the ghost-blind
  -- bound `probEvent_ghostBlindImpl_bad_le` (the first-moment route) closes it at
  -- `qS·(qH+1)·ε/(1-p)`, with the numeric charge supplied by
  -- `readRecord_expected_coincidences_le`.
  refine (probEvent_ghostHybridImpl_bad_le_ghostBlind ids hr M maxAttempts adv pk sk).trans ?_
  refine le_trans (probEvent_ghostBlindImpl_bad_le ids hr M maxAttempts adv qS qH ε p_abort
    hp₀ hp hε hQ pk sk hGuess hAbort) (le_of_eq ?_)
  norm_cast

end scaffold

end EUF_CMA

end FiatShamirWithAbort
