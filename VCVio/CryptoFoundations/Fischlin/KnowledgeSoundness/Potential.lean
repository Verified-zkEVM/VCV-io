/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.Fischlin.Completeness
public import VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Extraction
import all VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Extraction

/-!
# Fischlin small-sum counting and potential invariants
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

/-- The number of hash-value tuples `v : Fin ρ → Fin (2^b)` whose entries sum to at most `S`.

This counts the "small-sum" verifier-accepting hash assignments: a Fischlin proof is accepted only
when `∑ᵢ H(…,ωᵢ,respᵢ) ≤ S`, so this finite set is the target the prover's fresh random-oracle
answers must hit. It is bounded by `(S+1)·C(S+ρ-1, ρ-1)` (stars-and-bars). -/
@[expose]
def smallSumCount (ρ b S : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : Fin ρ → Fin (2 ^ b) => ∑ i, (v i).val ≤ S)).card

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Stars-and-bars bound.** The number of hash-value tuples summing to at most `S` is at most
`(S+1)·C(S+ρ-1, ρ-1)`.

Each `Fin (2^b)`-valued tuple injects into a `Fin ρ → ℕ` tuple with the same (bounded) sum; the
number of such natural tuples with sum exactly `s` is `C(s+ρ-1, ρ-1)`, which is monotone in `s`, so
summing over the `S+1` values `s = 0, …, S` gives the stated bound. -/
private lemma smallSumCount_le :
    smallSumCount ρ b S ≤ (S + 1) * Nat.choose (S + ρ - 1) (ρ - 1) := by
  classical
  -- Per-fiber count: tuples `Fin ρ → ℕ` summing to exactly `s` number `C(ρ+s-1, s)`.
  have hfiber : ∀ s : ℕ, (Finset.univ.piAntidiag s : Finset (Fin ρ → ℕ)).card
      = (ρ + s - 1).choose s := by
    intro s
    rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ, Finset.card_univ,
      Sym.card_sym_eq_choose, Fintype.card_fin]
  -- The `Fin.val` image of a small-sum hash tuple lands in the union of exact-sum natural tuples.
  set T : Finset (Fin ρ → ℕ) :=
    (Finset.range (S + 1)).biUnion (fun s => Finset.univ.piAntidiag s) with hT
  have hmap : (Finset.univ.filter (fun v : Fin ρ → Fin (2 ^ b) => ∑ i, (v i).val ≤ S)).image
      (fun v i => (v i).val) ⊆ T := by
    intro g hg
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨v, hv, rfl⟩ := hg
    simp only [hT, Finset.mem_biUnion, Finset.mem_range, Finset.mem_piAntidiag,
      Finset.mem_univ, implies_true, and_true]
    exact ⟨∑ i, (v i).val, by omega, rfl⟩
  -- The image has the same cardinality (the map `v ↦ Fin.val ∘ v` is injective).
  have hinj : Set.InjOn (fun v : Fin ρ → Fin (2 ^ b) => fun i => (v i).val)
      ↑(Finset.univ.filter (fun v : Fin ρ → Fin (2 ^ b) => ∑ i, (v i).val ≤ S)) := by
    intro v₁ _ v₂ _ h
    funext i
    exact Fin.val_injective (congrFun h i)
  rw [smallSumCount, ← Finset.card_image_of_injOn hinj]
  refine le_trans (Finset.card_le_card hmap) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  rw [Finset.sum_congr rfl (fun s _ => hfiber s)]
  -- Each fiber count is at most `C(S+ρ-1, ρ-1)`; there are `S+1` of them.
  refine le_trans (Finset.sum_le_card_nsmul _ _ ((S + ρ - 1).choose (ρ - 1)) (fun s hs => ?_)) ?_
  · rw [Finset.mem_range] at hs
    rcases Nat.eq_zero_or_pos ρ with hρ0 | hρpos
    · subst hρ0
      rcases Nat.eq_zero_or_pos s with rfl | hspos
      · simp
      · rw [Nat.choose_eq_zero_of_lt (by omega : 0 + s - 1 < s)]; exact Nat.zero_le _
    · have h1 : (ρ + s - 1).choose s = (ρ + s - 1).choose (ρ - 1) := by
        rw [← Nat.choose_symm (by omega)]; congr 1; omega
      rw [h1]; exact Nat.choose_le_choose _ (by omega)
  · rw [Finset.card_range, smul_eq_mul]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Each output tuple of `n` IID uniform draws is equally likely, with probability
`(Fintype.card α)⁻¹ ^ n`. -/
private lemma probOutput_mOfFn_uniformSample {α : Type} [SampleableType α] [Fintype α]
    (n : ℕ) (w : Fin n → α) :
    Pr[= w | Fin.mOfFn n (fun _ => ($ᵗ α : ProbComp α))]
      = (Fintype.card α : ℝ≥0∞)⁻¹ ^ n := by
  let : DecidableEq α := Classical.decEq α
  induction n with
  | zero =>
    have hw : w = Fin.elim0 := funext fun i => i.elim0
    simp [Fin.mOfFn, hw]
  | succ n ih =>
    have hcond : ∀ (a : α) (r : Fin n → α),
        w = Fin.cons a r ↔ r = Fin.tail w ∧ a = w 0 := by
      intro a r
      constructor
      · rintro rfl
        simp
      · rintro ⟨rfl, rfl⟩
        exact (Fin.cons_self_tail w).symm
    rw [Fin.mOfFn]
    simp only [probOutput_bind_eq_tsum, probOutput_pure, ih, probOutput_uniformSample,
      hcond, ite_and, mul_ite, mul_one, mul_zero, tsum_ite_eq]
    rw [pow_succ']

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The probability that `n` IID uniform draws land in a (decidable) target set is exactly the
size of the target set over `(Fintype.card α) ^ n`. -/
private lemma probEvent_mOfFn_uniformSample {α : Type} [SampleableType α] [Fintype α]
    (n : ℕ) (p : (Fin n → α) → Prop) [DecidablePred p] :
    Pr[p | Fin.mOfFn n (fun _ => ($ᵗ α : ProbComp α))]
      = ((Finset.univ.filter p).card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ n := by
  rw [probEvent_eq_sum_filter_univ]
  simp only [probOutput_mOfFn_uniformSample, Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv, ENNReal.inv_pow]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Untouched slot completes with probability exactly `μ`.** The probability that `ρ` fresh
uniform `Fin (2^b)` draws sum to at most `S` is exactly `smallSumCount ρ b S / (2^b)^ρ`. -/
private lemma probEvent_sum_le_mOfFn_uniform :
    Pr[fun v => ∑ i, (v i).val ≤ S | Fin.mOfFn ρ (fun _ => $ᵗ (Fin (2 ^ b)))]
      = (smallSumCount ρ b S : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ ρ := by
  rw [probEvent_mOfFn_uniformSample, Fintype.card_fin, smallSumCount]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Conditional tail.** Given a revealed partial sum `T ≤ S`, the probability that `k` fresh
uniform draws bring the total to at most `S` is exactly `smallSumCount k b (S - T) / (2^b)^k`.
This is the per-slot completion probability with some coordinates already revealed, used by the
potential-function step of the knowledge-soundness bound. -/
private lemma probEvent_add_sum_le_mOfFn_uniform (k T : ℕ) (hT : T ≤ S) :
    Pr[fun v => T + ∑ i, (v i).val ≤ S | Fin.mOfFn k (fun _ => $ᵗ (Fin (2 ^ b)))]
      = (smallSumCount k b (S - T) : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ k := by
  have hfilter :
      (Finset.univ.filter (fun v : Fin k → Fin (2 ^ b) => T + ∑ i, (v i).val ≤ S))
        = (Finset.univ.filter (fun v : Fin k → Fin (2 ^ b) => ∑ i, (v i).val ≤ S - T)) :=
    Finset.filter_congr fun v _ => by omega
  rw [probEvent_mOfFn_uniformSample k
      (fun v : Fin k → Fin (2 ^ b) => T + ∑ i, (v i).val ≤ S),
    Fintype.card_fin, smallSumCount, hfilter]

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- **Mixed-cache query vector.** Simulating a `Fin.mOfFn` of random-oracle re-queries at
pairwise distinct records on a cache that stores exactly the `hits`-marked records: each hit
reads its cached value deterministically; each miss draws a fresh uniform `Fin (2^b)` (and
caches it, which never collides with the remaining records by injectivity). The output
distribution is the independent per-index product `pure (hit value) / $ᵗ Fin (2^b)`. The
all-hit special case is `run_mOfFn_query_hit`. -/
private lemma run'_mOfFn_query_mixed {β : Type} (n : ℕ)
    (records : Fin n → (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain)
    (hinj : Function.Injective records)
    (hits : Fin n → Option (Fin (2 ^ b)))
    (f : Fin n → Fin (2 ^ b) → β)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hcache : ∀ i, cache (records i) = hits i) :
    𝒮[(simulateQ (fischlinImpl ρ b M)
        (Fin.mOfFn n fun i => do
          let h ← HasQuery.query (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M) (records i)
          pure (f i h))).run' cache]
      = 𝒮[(fun u => fun i => f i (u i)) <$>
          Fin.mOfFn n fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)] := by
  induction n generalizing cache with
  | zero =>
      simp only [Fin.mOfFn, simulateQ_pure, StateT.run'_pure', map_pure]
      exact congrArg (fun z => 𝒮[(pure z : ProbComp (Fin 0 → β))]) (funext fun i => i.elim0)
  | succ n ih =>
      -- Tail step, shared by both branches: with head answer `x` and any cache `c` storing
      -- `hits ∘ Fin.succ` at the tail records, the tail simulation matches the model tail.
      have hstep : ∀ (x : Fin (2 ^ b))
          (c : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache),
          (∀ j : Fin n, c (records j.succ) = hits j.succ) →
          𝒮[(simulateQ (fischlinImpl ρ b M)
              (Fin.mOfFn n (fun j => do
                let h ← HasQuery.query (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)
                  (records j.succ)
                pure (f j.succ h)) >>= fun rest => pure (Fin.cons (f 0 x) rest))).run' c]
            = 𝒮[(fun u : Fin n → Fin (2 ^ b) => fun i : Fin (n + 1) =>
                  f i ((Fin.cons x u : Fin (n + 1) → Fin (2 ^ b)) i)) <$>
                Fin.mOfFn n fun j =>
                  match hits j.succ with
                  | some h => (pure h : ProbComp (Fin (2 ^ b)))
                  | none => $ᵗ Fin (2 ^ b)] := by
        intro x c hc
        rw [bind_pure_comp, simulateQ_map, StateT.run'_map']
        refine (evalSPMF_map_eq_of_evalSPMF_eq
          (ih (fun j => records j.succ)
            (fun j₁ j₂ hj => Fin.succ_injective n (hinj hj))
            (fun j => hits j.succ) (fun j => f j.succ) c hc)
          (Fin.cons (α := fun _ => β) (f 0 x))).trans ?_
        rw [Functor.map_map]
        refine congrArg evalSPMF (congrArg (· <$> _) ?_)
        funext u i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [Fin.cons_zero]
        · simp [Fin.cons_succ]
      -- Freshness of tail records is preserved by caching the head record (distinct records).
      have hcache' : ∀ (x : Fin (2 ^ b)) (j : Fin n),
          (cache.cacheQuery (records 0) x) (records j.succ) = hits j.succ := by
        intro x j
        have hne : records j.succ ≠ records 0 := fun hEq => Fin.succ_ne_zero j (hinj hEq)
        exact (QueryCache.cacheQuery_of_ne cache x hne).trans (hcache j.succ)
      cases hh : hits 0 with
      | some h0 =>
          have hc0 : cache (records 0) = some h0 := by rw [hcache 0, hh]
          simp only [Fin.mOfFn]
          rw [simulateQ_bind, StateT.run'_bind', simulateQ_bind,
            roSim.simulateQ_HasQuery_query, StateT.run_bind,
            QueryImpl.withCaching_run_some (so := uniformSampleImpl) hc0]
          simp only [pure_bind, simulateQ_pure, StateT.run_pure]
          rw [hstep h0 cache (fun j => hcache j.succ)]
          simp only [hh, pure_bind, bind_pure_comp, Functor.map_map]
      | none =>
          have hc0 : cache (records 0) = none := by rw [hcache 0, hh]
          simp only [Fin.mOfFn]
          rw [simulateQ_bind, StateT.run'_bind', simulateQ_bind,
            roSim.simulateQ_HasQuery_query, StateT.run_bind,
            QueryImpl.withCaching_run_none (so := uniformSampleImpl) hc0]
          simp only [uniformSampleImpl, bind_map_left, pure_bind, simulateQ_pure,
            StateT.run_pure, bind_assoc]
          simp only [hh, map_bind]
          rw [evalSPMF_bind, evalSPMF_bind]
          refine congrArg (𝒮[$ᵗ Fin (2 ^ b)] >>= ·) (funext fun x => ?_)
          rw [hstep x (cache.cacheQuery (records 0) x) (hcache' x)]
          simp only [map_pure, bind_pure_comp]

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- Same as `run'_mOfFn_query_mixed`, packaged with a pure verdict post-processing `V` of the
per-repetition results, matching the shape of `Fischlin`'s verifier. -/
private lemma run'_mOfFn_query_mixed_bind {β γ : Type} (n : ℕ)
    (records : Fin n → (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain)
    (hinj : Function.Injective records)
    (hits : Fin n → Option (Fin (2 ^ b)))
    (f : Fin n → Fin (2 ^ b) → β) (V : (Fin n → β) → γ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hcache : ∀ i, cache (records i) = hits i) :
    𝒮[(simulateQ (fischlinImpl ρ b M)
        ((Fin.mOfFn n fun i => do
          let h ← HasQuery.query (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M) (records i)
          pure (f i h)) >>= fun results => pure (V results))).run' cache]
      = 𝒮[(Fin.mOfFn n fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)) >>= fun u => pure (V fun i => f i (u i))] := by
  rw [bind_pure_comp V, simulateQ_map, StateT.run'_map']
  refine (evalSPMF_map_eq_of_evalSPMF_eq
    (run'_mOfFn_query_mixed ρ b M n records hinj hits f cache hcache) V).trans ?_
  rw [Functor.map_map, bind_pure_comp]

omit [SampleableType Chal] in
/-- **Mixed-cache verify run.** The Fischlin verifier's `run'` on a cache storing exactly the
`hits`-marked records: re-queries at hit records read the cached hash; misses sample fresh
uniforms. The `ρ` records are pairwise distinct (their `rep` field is the repetition index),
so within one verify run each record is queried exactly once. -/
private lemma verify_run'_mixed (pk : Stmt) (msg : M)
    (sig : Fin ρ → Commit × Chal × Resp)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hits : Fin ρ → Option (Fin (2 ^ b)))
    (hcache : ∀ i, cache (⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = hits i) :
    𝒮[(simulateQ (fischlinImpl ρ b M)
        ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).verify pk msg sig)).run' cache]
      = 𝒮[(Fin.mOfFn ρ fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)) >>= fun u =>
          pure (((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) &&
            decide ((List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 ≤ S))] := by
  refine (run'_mOfFn_query_mixed_bind ρ b M ρ
    (records := fun i =>
      ⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩)
    (hinj := fun i j h => congrArg FischlinROInput.rep h)
    (hits := hits)
    (f := fun i h => (σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2, h.val))
    (V := fun results => ((List.finRange ρ).all fun i => (results i).1) &&
      decide ((List.finRange ρ).foldl (fun acc i => acc + (results i).2) 0 ≤ S))
    cache hcache).trans ?_
  rfl

/-- The number of hash-value tuples extending the cached `hits` with total sum at most `S`.

Counts full tuples `v : Fin ρ → Fin (2^b)` that agree with every cached hit and have small sum;
each such tuple corresponds to exactly one assignment of the miss positions. For
`hits = fun _ => none` this is `smallSumCount ρ b S` (see `partialSmallSumCount_none`). -/
private def partialSmallSumCount (ρ b : ℕ) (hits : Fin ρ → Option (Fin (2 ^ b))) (S : ℕ) : ℕ :=
  (Finset.univ.filter fun v : Fin ρ → Fin (2 ^ b) =>
    (∀ i h, hits i = some h → v i = h) ∧ ∑ i, (v i).val ≤ S).card

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- With no cached hits, the partial small-sum count is the full small-sum count. -/
private lemma partialSmallSumCount_none :
    partialSmallSumCount ρ b (fun _ => none) S = smallSumCount ρ b S := by
  unfold partialSmallSumCount smallSumCount
  congr 1
  refine Finset.filter_congr fun v _ => ?_
  simp

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Sum the per-repetition fold into a `Finset.sum`. -/
private lemma foldl_add_eq_sum (u : Fin ρ → Fin (2 ^ b)) :
    (List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 = ∑ i, (u i).val := by
  have hgen : ∀ (l : List (Fin ρ)) (init : ℕ),
      l.foldl (fun acc i => acc + (u i).val) init = init + (l.map fun i => (u i).val).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a l ihl => intro init; simp [ihl, Nat.add_assoc]
  rw [hgen, Nat.zero_add, ← List.ofFn_eq_map, List.sum_ofFn]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The product of per-coordinate hit/miss probabilities: zero unless `u` extends the hits,
in which case it is `(2^b)⁻¹` per miss. -/
private lemma prob_extend_hits (hits : Fin ρ → Option (Fin (2 ^ b))) (u : Fin ρ → Fin (2 ^ b)) :
    Pr[= u | Fin.mOfFn ρ fun i =>
        match hits i with
        | some h => (pure h : ProbComp (Fin (2 ^ b)))
        | none => $ᵗ Fin (2 ^ b)]
      = if ∀ i h, hits i = some h → u i = h
          then (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹ ^ (Finset.univ.filter fun i : Fin ρ => hits i = none).card
          else 0 := by
  rw [probOutput_mOfFn]
  by_cases hcomp : ∀ i h, hits i = some h → u i = h
  · rw [if_pos hcomp]
    have hfactor : ∀ i : Fin ρ,
        Pr[= u i | (match hits i with
          | some h => (pure h : ProbComp (Fin (2 ^ b)))
          | none => $ᵗ Fin (2 ^ b))]
          = if hits i = none then (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹ else 1 := by
      intro i
      cases hh : hits i with
      | none =>
          simp only [if_true]
          rw [probOutput_uniformSample, Fintype.card_fin]
      | some h =>
          have hu : u i = h := hcomp i h hh
          rw [probOutput_pure, if_pos hu, if_neg (Option.some_ne_none h)]
    rw [Finset.prod_congr rfl fun i _ => hfactor i, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one]
  · rw [if_neg hcomp]
    push Not at hcomp
    obtain ⟨i, h, hh, hne⟩ := hcomp
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [hh]
    rw [probOutput_pure, if_neg hne]

omit [SampleableType Chal] in
/-- **The ψ leaf (exact).** The probability that the Fischlin verifier accepts on a cache
storing exactly the `hits`-marked records is EXACTLY the σ-verification indicator times the
number of hit-compatible small-sum hash tuples over the miss-space volume `(2^b)^#misses`.

For `hits = fun _ => none` (the all-fresh case) the bound specializes to
`smallSumCount ρ b S / (2^b)^ρ` via `partialSmallSumCount_none`. -/
private lemma verify_probOutput_true_mixed (pk : Stmt) (msg : M)
    (sig : Fin ρ → Commit × Chal × Resp)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hits : Fin ρ → Option (Fin (2 ^ b)))
    (hcache : ∀ i, cache (⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = hits i) :
    Pr[= true | (simulateQ (fischlinImpl ρ b M)
        ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).verify pk msg sig)).run' cache]
      = (if ((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) = true
          then 1 else 0) *
        (partialSmallSumCount ρ b hits S : ℝ≥0∞) /
          (((2 ^ b : ℕ) : ℝ≥0∞)) ^ (Finset.univ.filter fun i : Fin ρ => hits i = none).card := by
  rw [probOutput_def, verify_run'_mixed σ hr ρ b S M pk msg sig cache hits hcache,
    ← probOutput_def, probOutput_bind_eq_sum_fintype]
  by_cases haV :
      ((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) = true
  · -- σ-verification accepted: the verdict is exactly the small-sum event.
    have hterm : ∀ u : Fin ρ → Fin (2 ^ b),
        Pr[= u | Fin.mOfFn ρ fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)] *
          Pr[= true | (pure
            (((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) &&
              decide ((List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 ≤ S)) :
            ProbComp Bool)]
          = if (∀ i h, hits i = some h → u i = h) ∧ ∑ i, (u i).val ≤ S
              then (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹ ^
                (Finset.univ.filter fun i : Fin ρ => hits i = none).card
              else 0 := by
      intro u
      rw [prob_extend_hits ρ b hits u, probOutput_pure, foldl_add_eq_sum ρ b u, haV]
      by_cases h3 : ∀ i h, hits i = some h → u i = h <;>
        by_cases h2 : (∑ i, (u i).val) ≤ S <;>
        simp [h3, h2]
    rw [Finset.sum_congr rfl fun u _ => hterm u, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, if_pos haV, one_mul, div_eq_mul_inv, ← ENNReal.inv_pow]
    rfl
  · -- σ-verification rejected: the verdict is constantly `false`.
    have haV' :
        ((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) = false :=
      Bool.eq_false_iff.mpr haV
    have hterm0 : ∀ u : Fin ρ → Fin (2 ^ b),
        Pr[= u | Fin.mOfFn ρ fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)] *
          Pr[= true | (pure
            (((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) &&
              decide ((List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 ≤ S)) :
            ProbComp Bool)]
          = 0 := by
      intro u
      rw [haV', probOutput_pure]
      simp
    rw [Finset.sum_congr rfl fun u _ => hterm0 u, Finset.sum_const_zero, if_neg haV, zero_mul,
      ENNReal.zero_div]

omit [SampleableType Chal] in
/-- **Accepting verify runs Σ-verify every repetition.** Any `(true, _)` outcome in the support
of the simulated Fischlin verifier implies the per-repetition Σ-protocol checks of the proof:
the Σ-verification bits inside `verify` are deterministic and independent of the oracle
answers, so a `false` bit forces acceptance probability zero. Discharges the `hverSupp`
hypothesis of `knowledgeSoundnessExp_bad_le_misses`. -/
private lemma ksVerify_true_support_allVerified (x : Stmt) (msg : M)
    (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (c' : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (h : (true, c') ∈ support (ksVerify σ hr ρ b S M x msg π cache)) :
    ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true := by
  intro i
  by_contra hne
  have hall : ((List.finRange ρ).all fun j => σ.verify x (π j).1 (π j).2.1 (π j).2.2) ≠ true :=
    fun hAll => hne (List.all_eq_true.mp hAll i (List.mem_finRange i))
  have hmem : true ∈ support ((simulateQ (fischlinImpl ρ b M)
      ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
        σ hr ρ b S M).verify x msg π)).run' cache) := by
    rw [StateT.run', support_map]
    exact ⟨(true, c'), h, rfl⟩
  have hpos := probOutput_pos _ _ hmem
  rw [verify_probOutput_true_mixed σ hr ρ b S M x msg π cache
    (fun j => cache (⟨x, msg, List.ofFn (fun k => (π k).1), j, (π j).2.1, (π j).2.2⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M)) (fun j => rfl),
    if_neg hall, zero_mul, ENNReal.zero_div] at hpos
  exact lt_irrefl 0 hpos

omit [SampleableType Chal] in
/-- `knowledgeSoundnessExp_bad_le_misses` with the verifier-determinism hypothesis discharged:
the knowledge-soundness bad event is bounded by the probability that the verifier accepts
while the extractor's scan misses. -/
private lemma knowledgeSoundnessExp_bad_le_misses' (hss : σ.SpeciallySound)
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M prover x msg] ≤
      Pr[fun out => out.2 = true ∧ fischlinFindWitness σ ρ b M x out.1.1 out.1.2 = none
        | ksSample σ hr ρ b S M prover x msg] :=
  knowledgeSoundnessExp_bad_le_misses σ hr ρ b S M hss prover x msg
    (fun π cache c' h => ksVerify_true_support_allVerified σ hr ρ b S M x msg π cache c' h)

/-- Number of unrevealed coordinates of a partial hash assignment. -/
private def missCard {ρ b : ℕ} (g : Fin ρ → Option (Fin (2 ^ b))) : ℕ :=
  (Finset.univ.filter fun i => g i = none).card

/-- Per-slot potential: the current conditional completion probability of a slot given the
revealed coordinates `g`. An untouched slot has potential exactly
`μ = smallSumCount ρ b S / (2^b)^ρ` (`slotPsi_none`), and revealing one fresh uniform
coordinate is a martingale step (`slotPsi_tower`). -/
private noncomputable def slotPsi (ρ b S : ℕ) (g : Fin ρ → Option (Fin (2 ^ b))) : ℝ≥0∞ :=
  (partialSmallSumCount ρ b g S : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ (missCard g)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Fiberwise decomposition: summing the extension counts over the possible values of a fresh
coordinate recovers the count for the unextended assignment (tower property at the level of
counting). -/
private lemma sum_partialSmallSumCount_update (g : Fin ρ → Option (Fin (2 ^ b))) (i : Fin ρ)
    (hi : g i = none) :
    ∑ u : Fin (2 ^ b), partialSmallSumCount ρ b (Function.update g i (some u)) S
      = partialSmallSumCount ρ b g S := by
  classical
  rw [partialSmallSumCount, Finset.card_eq_sum_card_fiberwise
    (f := fun v : Fin ρ → Fin (2 ^ b) => v i) (t := Finset.univ)
    (fun v _ => Finset.mem_univ _)]
  refine (Finset.sum_congr rfl fun u _ => ?_).symm
  rw [partialSmallSumCount, Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun v _ => ?_
  constructor
  · rintro ⟨⟨hext, hsum⟩, hvi⟩
    refine ⟨fun j h hj => ?_, hsum⟩
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self] at hj
      cases hj
      exact hvi
    · rw [Function.update_of_ne hji] at hj
      exact hext j h hj
  · rintro ⟨hext, hsum⟩
    have hvi : v i = u := hext i u (by rw [Function.update_self])
    refine ⟨⟨fun j h hj => ?_, hsum⟩, hvi⟩
    by_cases hji : j = i
    · subst hji; rw [hi] at hj; cases hj
    · exact hext j h (by rw [Function.update_of_ne hji]; exact hj)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Revealing a fresh coordinate decreases the miss count by exactly one. -/
private lemma missCard_update {ρ' b' : ℕ} (g : Fin ρ' → Option (Fin (2 ^ b'))) (i : Fin ρ')
    (u : Fin (2 ^ b')) (hi : g i = none) :
    missCard g = missCard (Function.update g i (some u)) + 1 := by
  classical
  unfold missCard
  have hset : (Finset.univ.filter fun j : Fin ρ' => Function.update g i (some u) j = none)
      = (Finset.univ.filter fun j : Fin ρ' => g j = none).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    by_cases hji : j = i
    · subst hji; simp [Function.update_self]
    · simp [hji]
  have hmem : i ∈ Finset.univ.filter fun j : Fin ρ' => g j = none :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  rw [hset, Finset.card_erase_of_mem hmem]
  have hpos : 0 < (Finset.univ.filter fun j : Fin ρ' => g j = none).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  omega

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Fresh slot = μ.** The potential of an untouched slot is exactly
`smallSumCount ρ b S / (2^b)^ρ`. -/
private lemma slotPsi_none :
    slotPsi ρ b S (fun _ => none)
      = (smallSumCount ρ b S : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ ρ := by
  unfold slotPsi
  rw [partialSmallSumCount_none ρ b S]
  congr 1
  simp [missCard]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Tower identity.** Averaging the slot potential over a uniformly revealed fresh
coordinate recovers the current slot potential: the per-slot potential is a martingale under
revealing one coordinate. With `g = fun _ => none` this is the open-step identity. -/
private lemma slotPsi_tower (g : Fin ρ → Option (Fin (2 ^ b))) (i : Fin ρ) (hi : g i = none) :
    (∑ u : Fin (2 ^ b), slotPsi ρ b S (Function.update g i (some u)))
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      = slotPsi ρ b S g := by
  classical
  have hmem : i ∈ Finset.univ.filter fun j : Fin ρ => g j = none :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have h1 : 1 ≤ missCard g := Finset.card_pos.mpr ⟨i, hmem⟩
  have hmiss : ∀ u : Fin (2 ^ b),
      missCard (Function.update g i (some u)) = missCard g - 1 := by
    intro u
    have := missCard_update g i u hi
    omega
  have hm : missCard g - 1 + 1 = missCard g := by omega
  unfold slotPsi
  simp only [hmiss, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_partialSmallSumCount_update ρ b S g i hi,
    mul_assoc,
    ← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness)),
    ← pow_succ, hm]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Each extending tuple is determined by its values on the unrevealed coordinates, so the
partial count is at most `(2^b)^missCard g`. -/
private lemma partialSmallSumCount_le_pow (g : Fin ρ → Option (Fin (2 ^ b))) :
    partialSmallSumCount ρ b g S ≤ (2 ^ b) ^ missCard g := by
  classical
  have hle : partialSmallSumCount ρ b g S
      ≤ Fintype.card
          ({j // j ∈ Finset.univ.filter fun j : Fin ρ => g j = none} → Fin (2 ^ b)) := by
    rw [partialSmallSumCount, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun v j => v j.1) (fun v _ => Finset.mem_univ _) ?_
    intro v hv w hw hvw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
    funext j
    by_cases hj : g j = none
    · exact congrFun hvw ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    · obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hj
      rw [hv.1 j h hh, hw.1 j h hh]
  refine hle.trans (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, missCard]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The slot potential is a probability: `slotPsi ρ b S g ≤ 1`. -/
private lemma slotPsi_le_one (g : Fin ρ → Option (Fin (2 ^ b))) : slotPsi ρ b S g ≤ 1 := by
  unfold slotPsi
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  calc (partialSmallSumCount ρ b g S : ℝ≥0∞)
      ≤ (((2 ^ b) ^ missCard g : ℕ) : ℝ≥0∞) :=
        Nat.cast_le.mpr (partialSmallSumCount_le_pow ρ b S g)
    _ = ((2 ^ b : ℕ) : ℝ≥0∞) ^ missCard g := by push_cast; rfl

/-- Update one coordinate of one slot of a multi-slot state. -/
private def updateSlot {ρ' b' : ℕ} {K : Type} [DecidableEq K]
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) (k₀ : K) (i₀ : Fin ρ')
    (u : Fin (2 ^ b')) : K → Fin ρ' → Option (Fin (2 ^ b')) :=
  Function.update st k₀ (Function.update (st k₀) i₀ (some u))

/-- Multi-slot potential: the sum of the live slots' potentials over the touched keys. -/
private noncomputable def Phi (ρ b S : ℕ) {K : Type} (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b))) (dead : K → Prop) [DecidablePred dead] : ℝ≥0∞ :=
  ∑ k ∈ keys, if dead k then 0 else slotPsi ρ b S (st k)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma updateSlot_apply_ne {ρ' b' : ℕ} {K : Type} [DecidableEq K]
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) (k₀ : K) (i₀ : Fin ρ')
    (u : Fin (2 ^ b')) {k : K} (hk : k ≠ k₀) : updateSlot st k₀ i₀ u k = st k :=
  Function.update_of_ne hk _ _

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma updateSlot_apply_self {ρ' b' : ℕ} {K : Type} [DecidableEq K]
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) (k₀ : K) (i₀ : Fin ρ')
    (u : Fin (2 ^ b')) : updateSlot st k₀ i₀ u k₀ = Function.update (st k₀) i₀ (some u) :=
  Function.update_self _ _ _

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Extend = martingale.** Querying a fresh coordinate of a live, already-open slot leaves
the expected potential unchanged. -/
private lemma Phi_extend {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∈ keys) (hdead : ¬dead k₀) (hi : st k₀ i₀ = none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S keys (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      = Phi ρ b S keys st dead := by
  classical
  have hsplit : ∀ u : Fin (2 ^ b),
      Phi ρ b S keys (updateSlot st k₀ i₀ u) dead
        = slotPsi ρ b S (Function.update (st k₀) i₀ (some u))
          + ∑ k ∈ keys.erase k₀, if dead k then 0 else slotPsi ρ b S (st k) := by
    intro u
    rw [Phi, ← Finset.add_sum_erase _ _ hk, if_neg hdead, updateSlot_apply_self]
    congr 1
    refine Finset.sum_congr rfl fun k hk' => ?_
    rw [updateSlot_apply_ne st k₀ i₀ u (Finset.ne_of_mem_erase hk')]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, ENNReal.add_div, slotPsi_tower ρ b S (st k₀) i₀ hi,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
    ENNReal.mul_div_cancel_right (by positivity) (by finiteness), Phi,
    ← Finset.add_sum_erase _ _ hk,
    if_neg hdead]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Open, live case (equality).** Opening a fresh slot at a live key adds exactly
`μ = slotPsi ρ b S (fun _ => none)` to the expected potential. Requires the slot's state to be
untouched (`hfresh`) — exactly the invariant that untouched keys carry all-`none` states. -/
private lemma Phi_open_eq {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∉ keys) (hdead : ¬dead k₀) (hfresh : st k₀ = fun _ => none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      = Phi ρ b S keys st dead + slotPsi ρ b S (fun _ => none) := by
  classical
  have hsplit : ∀ u : Fin (2 ^ b),
      Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead
        = slotPsi ρ b S (Function.update (st k₀) i₀ (some u)) + Phi ρ b S keys st dead := by
    intro u
    rw [Phi, Finset.sum_insert hk, if_neg hdead, updateSlot_apply_self]
    congr 1
    refine Finset.sum_congr rfl fun k hk' => ?_
    rw [updateSlot_apply_ne st k₀ i₀ u (fun h => hk (h ▸ hk'))]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, ENNReal.add_div,
    slotPsi_tower ρ b S (st k₀) i₀ (by rw [hfresh]), hfresh,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
    ENNReal.mul_div_cancel_right (by positivity) (by finiteness), add_comm]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Open, general case (inequality).** Opening a fresh slot adds at most `μ` to the
expected potential (a dead key contributes nothing). -/
private lemma Phi_open_le {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∉ keys) (hfresh : st k₀ = fun _ => none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      ≤ Phi ρ b S keys st dead + slotPsi ρ b S (fun _ => none) := by
  classical
  by_cases hdead : dead k₀
  · have hsplit : ∀ u : Fin (2 ^ b),
        Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead
          = Phi ρ b S keys st dead := by
      intro u
      rw [Phi, Finset.sum_insert hk, if_pos hdead, zero_add]
      refine Finset.sum_congr rfl fun k hk' => ?_
      rw [updateSlot_apply_ne st k₀ i₀ u (fun h => hk (h ▸ hk'))]
    simp only [hsplit]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
      ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]
    exact le_self_add
  · exact le_of_eq (Phi_open_eq ρ b S keys st dead k₀ i₀ hk hdead hfresh)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Kill.** Any step that only grows the dead set (state and keys unchanged) can only
decrease the potential. -/
private lemma Phi_mono_dead {K : Type} (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead dead' : K → Prop) [DecidablePred dead] [DecidablePred dead']
    (h : ∀ k, dead k → dead' k) :
    Phi ρ b S keys st dead' ≤ Phi ρ b S keys st dead := by
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : dead' k
  · simp [hk]
  · rw [if_neg hk, if_neg fun hd => hk (h k hd)]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Extend, deadness-agnostic (inequality).** Querying a fresh coordinate of an already-open
slot cannot increase the expected potential, whether or not the key is dead. -/
private lemma Phi_extend_le {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∈ keys) (hi : st k₀ i₀ = none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S keys (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      ≤ Phi ρ b S keys st dead := by
  classical
  by_cases hdead : dead k₀
  · have hconst : ∀ u : Fin (2 ^ b),
        Phi ρ b S keys (updateSlot st k₀ i₀ u) dead = Phi ρ b S keys st dead := by
      intro u
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hkk : k = k₀
      · subst hkk; simp [hdead]
      · rw [updateSlot_apply_ne st k₀ i₀ u hkk]
    simp only [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
      ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]
  · exact le_of_eq (Phi_extend ρ b S keys st dead k₀ i₀ hk hdead hi)

/-- The lazy random-oracle simulation for a constant-range hash spec: forward `unifSpec`
queries, lazily sample-and-cache hash queries. Abstract analogue of `fischlinImpl`. -/
@[reducible] private def roImpl (b' : ℕ) (T : Type) [DecidableEq T] :
    QueryImpl (unifSpec + (T →ₒ Fin (2 ^ b')))
      (StateT (T →ₒ Fin (2 ^ b')).QueryCache ProbComp) :=
  unifFwdImpl (T →ₒ Fin (2 ^ b')) + randomOracle (spec := T →ₒ Fin (2 ^ b'))

/-- Coupling invariant for the multi-record setting, relative to the deadness predicate `dd`
of the current cache. The cache→state direction is restricted
to relevant records at live slots, and the state→cache direction only requires *some*
relevant record witnessing each revealed cell. -/
private structure INV' (ρ' b' : ℕ) {T K : Type} (relevant : T → Prop) (key : T → K)
    (coord : T → Fin ρ') (dd : K → Prop)
    (cache : (T →ₒ Fin (2 ^ b')).QueryCache) (keys : Finset K)
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) : Prop where
  cached_imp : ∀ (t : T) (u : Fin (2 ^ b')), relevant t → ¬ dd (key t) →
    cache t = some u → st (key t) (coord t) = some u
  revealed_has_record : ∀ (k : K) (i : Fin ρ') (u : Fin (2 ^ b')), ¬ dd k →
    st k i = some u → ∃ t, relevant t ∧ key t = k ∧ coord t = i ∧ cache t = some u
  untouched : ∀ k ∉ keys, st k = fun _ => none

namespace INV'

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Inert step.** Caching a record that is irrelevant, or whose slot is (or becomes)
dead, preserves `INV'` with the ghost state unchanged. Covers the irrelevant, already-dead,
and kill cases of the generalized induction. -/
private lemma cacheQuery_inert {ρ' b' : ℕ} {T K : Type} [DecidableEq T]
    {relevant : T → Prop} {key : T → K} {coord : T → Fin ρ'} {dd dd' : K → Prop}
    {cache : (T →ₒ Fin (2 ^ b')).QueryCache} {keys : Finset K}
    {st : K → Fin ρ' → Option (Fin (2 ^ b'))}
    (hINV : INV' ρ' b' relevant key coord dd cache keys st)
    (hmono : ∀ k, dd k → dd' k)
    (s : T) (hs : cache s = none) (u : Fin (2 ^ b'))
    (hinert : relevant s → dd' (key s)) :
    INV' ρ' b' relevant key coord dd' (cache.cacheQuery s u) keys st := by
  constructor
  · intro t u₀ hrel hlive hcache
    by_cases hts : t = s
    · subst hts
      exact absurd (hinert hrel) hlive
    · rw [QueryCache.cacheQuery_of_ne _ _ hts] at hcache
      exact hINV.cached_imp t u₀ hrel (fun hd => hlive (hmono _ hd)) hcache
  · intro k i u₀ hlive hst
    obtain ⟨t, htrel, htk, hti, htc⟩ :=
      hINV.revealed_has_record k i u₀ (fun hd => hlive (hmono _ hd)) hst
    have hts : t ≠ s := fun h => by rw [h, hs] at htc; simp at htc
    exact ⟨t, htrel, htk, hti, by
      rw [QueryCache.cacheQuery_of_ne _ _ hts]; exact htc⟩
  · exact hINV.untouched

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Reveal step.** Caching a relevant record at a fresh cell updates the ghost state by
writing the sampled value into the cell and marking the key as touched, preserving `INV'`. -/
private lemma cacheQuery_reveal {ρ' b' : ℕ} {T K : Type} [DecidableEq T] [DecidableEq K]
    {relevant : T → Prop} {key : T → K} {coord : T → Fin ρ'} {dd dd' : K → Prop}
    {cache : (T →ₒ Fin (2 ^ b')).QueryCache} {keys : Finset K}
    {st : K → Fin ρ' → Option (Fin (2 ^ b'))}
    (hINV : INV' ρ' b' relevant key coord dd cache keys st)
    (hmono : ∀ k, dd k → dd' k)
    (s : T) (hs : cache s = none) (hrel : relevant s)
    (hstn : st (key s) (coord s) = none) (u : Fin (2 ^ b')) :
    INV' ρ' b' relevant key coord dd' (cache.cacheQuery s u) (insert (key s) keys)
      (updateSlot st (key s) (coord s) u) := by
  constructor
  · intro t u₀ htrel hlive hcache
    by_cases hts : t = s
    · subst hts
      rw [QueryCache.cacheQuery_self] at hcache
      rw [updateSlot_apply_self, Function.update_self]
      exact hcache
    · rw [QueryCache.cacheQuery_of_ne _ _ hts] at hcache
      have hold := hINV.cached_imp t u₀ htrel (fun hd => hlive (hmono _ hd)) hcache
      by_cases hkey : key t = key s
      · by_cases hcoord : coord t = coord s
        · exfalso
          rw [hkey, hcoord, hstn] at hold
          simp at hold
        · rw [hkey, updateSlot_apply_self, Function.update_of_ne hcoord, ← hkey]
          exact hold
      · rw [updateSlot_apply_ne st _ _ u hkey]
        exact hold
  · intro k i u₀ hlive hst
    by_cases hk : k = key s
    · subst hk
      by_cases hi : i = coord s
      · subst hi
        rw [updateSlot_apply_self, Function.update_self] at hst
        refine ⟨s, hrel, rfl, rfl, ?_⟩
        rw [QueryCache.cacheQuery_self]
        exact hst
      · rw [updateSlot_apply_self, Function.update_of_ne hi] at hst
        obtain ⟨t, htrel, htk, hti, htc⟩ :=
          hINV.revealed_has_record (key s) i u₀ (fun hd => hlive (hmono _ hd)) hst
        have hts : t ≠ s := fun h => hi (by rw [← hti, h])
        exact ⟨t, htrel, htk, hti, by
          rw [QueryCache.cacheQuery_of_ne _ _ hts]; exact htc⟩
    · rw [updateSlot_apply_ne st _ _ u hk] at hst
      obtain ⟨t, htrel, htk, hti, htc⟩ :=
        hINV.revealed_has_record k i u₀ (fun hd => hlive (hmono _ hd)) hst
      have hts : t ≠ s := fun h => hk (by rw [← htk, h])
      exact ⟨t, htrel, htk, hti, by
        rw [QueryCache.cacheQuery_of_ne _ _ hts]; exact htc⟩
  · intro k hk
    have hk1 : k ≠ key s := fun h => hk (h ▸ Finset.mem_insert_self _ _)
    have hk2 : k ∉ keys := fun h => hk (Finset.mem_insert_of_mem h)
    rw [updateSlot_apply_ne st _ _ u hk1]
    exact hINV.untouched k hk2

end INV'

end security

end Fischlin
