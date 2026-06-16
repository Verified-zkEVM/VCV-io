/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.Table

/-!
# PRF Tag/Reader Protocol — Cell-Swap Permutations and the Swap-Bridge

Cell-swap permutations on eager tables, their measure preservation under uniform sampling,
and the cache-extension swap-bridge for `singleTableHandler`.

`cellSwap a b` is the involution on a table domain that exchanges the cells `a` and `b`
(identity when `a = b`). Post-composing a uniform table with it preserves the distribution
(`evalDist_uniformSample_comp_cellSwap`, `evalDist_uniformSample_bind_cellSwap`), and when two
tables differ only by a swap of values at the cells `((tag, 0), n)` and `((tag, slotK), n)`,
the `singleTableHandler` simulateQ outputs are pointwise identical
(`singleTableHandler_simulateQ_swap_invariant`). Together these give the swap-bridge
`singleTableHandler_cache_swap_eq`: under a cache with no slot-positive entries and a fresh
slot-0 cell, the cache extensions at `(tag, 0)` and `(tag, slotK)` produce the same output
distribution over a uniform table draw.

## Main results

* `cellSwap` — the two-cell swap involution, with `cellSwap_involution`, `cellSwap_bijective`,
  `cellSwap_right`, and `cellSwap_of_ne`.
* `evalDist_uniformSample_bind_cellSwap` — bind-level measure preservation of the swap.
* `singleTableHandler_cache_swap_eq` — the cache-extension swap-bridge for the slot-positive
  Case M-miss of the direct-coupling aux.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section DirectCouplingSwap

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

namespace UnlinkReduction

/-! ### Cell-swap permutation for the swap-bridge

The permutation argument for the swap-bridge needs a concrete bijection that swaps two cells of
the table domain. `cellSwap a b` is the involution on `D` that swaps `a` and `b` (identity if
`a = b`). Its key properties: bijective (involution), and composing a uniform table with it
preserves the distribution (`evalDist_map_bijective_uniform_cross`). -/

/-- Swap two elements of a type with decidable equality. Identity if `a = b`. -/
def cellSwap {D : Type} [DecidableEq D] (a b : D) : D → D := fun x =>
  if x = a then b else if x = b then a else x

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest]
    [NeZero sessionsPerTag] in
/-- `cellSwap a b` is an involution: applying it twice returns the original. -/
lemma cellSwap_involution {D : Type} [DecidableEq D] (a b : D) (x : D) :
    cellSwap a b (cellSwap a b x) = x := by
  unfold cellSwap
  by_cases hxa : x = a
  · -- x = a: cellSwap a b a = b, then cellSwap a b b = a. (Or if a = b, it stays.)
    rw [hxa]
    by_cases hab : b = a
    · rw [hab]; simp
    · simp [hab]
  · by_cases hxb : x = b
    · rw [hxb]; simp
    · simp [hxa, hxb]

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest]
    [NeZero sessionsPerTag] in
/-- `cellSwap a b` is bijective. -/
lemma cellSwap_bijective {D : Type} [DecidableEq D] (a b : D) :
    Function.Bijective (cellSwap a b) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    have := congrArg (cellSwap a b) h
    rw [cellSwap_involution, cellSwap_involution] at this
    exact this
  · intro y
    exact ⟨cellSwap a b y, cellSwap_involution a b y⟩

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest]
    [NeZero sessionsPerTag] in
/-- `cellSwap a b` sends `b` to `a`. -/
@[simp] lemma cellSwap_right {D : Type} [DecidableEq D] (a b : D) : cellSwap a b b = a := by
  unfold cellSwap
  by_cases hab : b = a <;> simp [hab]

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest]
    [NeZero sessionsPerTag] in
/-- `cellSwap a b` fixes any element distinct from both `a` and `b`. -/
lemma cellSwap_of_ne {D : Type} [DecidableEq D] (a b : D) {x : D} (hxa : x ≠ a) (hxb : x ≠ b) :
    cellSwap a b x = x := by
  simp [cellSwap, hxa, hxb]

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- **Measure-preservation of cell-swap permutation.** Drawing a uniform table `gS` and
post-composing with `cellSwap a b` (which is a bijection on the domain) yields the same
distribution as drawing `gS` directly. The key measure-preserving step underlying the
swap-bridge: averaging any continuation `F` over a uniform `gS` is invariant under
`gS ↦ gS ∘ cellSwap a b`. -/
lemma evalDist_uniformSample_comp_cellSwap [Fintype Nonce]
    (a b : (TagId × Fin sessionsPerTag) × Nonce) :
    𝒟[(fun gS : (TagId × Fin sessionsPerTag) × Nonce → Digest =>
        gS ∘ cellSwap a b) <$> ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] =
      𝒟[$ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)] := by
  classical
  -- `g ↦ g ∘ cellSwap a b` is a bijection on `(D → R)`: its inverse is `g ↦ g ∘ cellSwap a b`
  -- (since cellSwap is an involution).
  have hbij : Function.Bijective
      (fun gS : (TagId × Fin sessionsPerTag) × Nonce → Digest => gS ∘ cellSwap a b) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      have : (fun x => g₁ (cellSwap a b x)) = (fun x => g₂ (cellSwap a b x)) := h
      funext x
      have := congrFun this (cellSwap a b x)
      simpa [cellSwap_involution] using this
    · intro h
      refine ⟨h ∘ cellSwap a b, ?_⟩
      funext x
      simp [Function.comp, cellSwap_involution]
  exact evalDist_map_bijective_uniform_cross
    (α := (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (β := (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (fun gS => gS ∘ cellSwap a b) hbij

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- **Bind-level measure-preservation via `cellSwap`.** For any continuation
`F : (table) → ProbComp α`, drawing a uniform `gS` and applying `F` to `gS` has the same
distribution as drawing a uniform `gS` and applying `F` to `gS ∘ cellSwap a b`. Direct
consequence of `evalDist_uniformSample_comp_cellSwap` combined with `map_bind`. -/
lemma evalDist_uniformSample_bind_cellSwap [Fintype Nonce]
    {α : Type} (a b : (TagId × Fin sessionsPerTag) × Nonce)
    (F : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp α) :
    𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest); F gS)] =
      𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest);
            F (gS ∘ cellSwap a b))] := by
  classical
  have hMapBind :
      ((fun gS : (TagId × Fin sessionsPerTag) × Nonce → Digest => gS ∘ cellSwap a b) <$>
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))) >>= F =
      (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest);
          F (gS ∘ cellSwap a b)) := by
    simp [map_eq_bind_pure_comp, bind_assoc, Function.comp]
  rw [← hMapBind, evalDist_bind, evalDist_bind,
      evalDist_uniformSample_comp_cellSwap (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) a b]

/-! ### Multiset-invariance of `singleTableHandler` under cell-value swap

The pointwise core of the permutation argument: when two tables `g₁, g₂` differ only by a
swap of values at two cells `(tag, 0, n)` and `(tag, slotK, n)` (agreeing everywhere else),
the `singleTableHandler` simulateQ outputs are IDENTICAL (not just distributionally equal).

* Tag queries for `T = tag`: by `hAdv`, read at `sid ≥ slotK + 1 ∉ {0, slotK}`. Tables agree.
* Tag queries for `T ≠ tag`: cells at `(T, ·, ·)` not in the swap pair. Tables agree.
* Reader queries at nonce `n' ≠ n`: cells at `n'` not in the swap pair. Tables agree.
* Reader queries at nonce `n`: existential reads cells at all `(T', sid')`. Swapping values
  at two positions doesn't change the set of values present, so the existential value (mass
  bound by `V`) is the same on both sides. -/

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] in
private lemma singleTableHandler_simulateQ_swap_invariant
    (tag : TagId) (slotK : Fin sessionsPerTag) (hslotK : slotK ≠ 0)
    (n : Nonce)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (s : UnlinkState TagId) (hAdv : slotK.val < s.sessionsUsed tag)
    (g₁ g₂ : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (heq : ∀ x : (TagId × Fin sessionsPerTag) × Nonce,
        x ≠ ((tag, (0 : Fin sessionsPerTag)), n) → x ≠ ((tag, slotK), n) →
        g₁ x = g₂ x)
    (hswap_0 : g₁ ((tag, (0 : Fin sessionsPerTag)), n) = g₂ ((tag, slotK), n))
    (hswap_K : g₁ ((tag, slotK), n) = g₂ ((tag, (0 : Fin sessionsPerTag)), n)) :
    (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g₁) oa).run' s
    = (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g₂) oa).run' s := by
  classical
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b =>
    -- Both sides reduce to `pure b` via `simulateQ_pure` and `StateT.run'`.
    simp [simulateQ_pure]
  | query_bind t k ih =>
    -- Decompose via `singleTable_run'_query_bind'`, then case-split on `t`.
    rw [singleTable_run'_query_bind', singleTable_run'_query_bind']
    -- Goal: (step_g₁ t s) >>= cont_g₁ = (step_g₂ t s) >>= cont_g₂
    -- Strategy: show step_g₁ = step_g₂ pointwise (case-split on `t`), then apply IH on
    -- continuation. The IH carries the swap-invariance to each post-step state.
    cases t with
    | inl T =>
      -- Tag query: handler reads at cell `((T, sessionsUsed T), fresh_nonce)`.
      -- Case-split on whether T's session budget is available.
      by_cases hslot : s.sessionsUsed T < sessionsPerTag
      · -- Free slot: step samples nonce, reads cell, advances state.
        rw [singleTableHandler_tag_run_of_lt _ T s hslot,
            singleTableHandler_tag_run_of_lt _ T s hslot]
        -- Cell read is `((T, ⟨sessionsUsed T, hslot⟩), nonce)`. Show this is NOT in the swap pair.
        have hcell_ne : ∀ nonce : Nonce,
            ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce)
              ≠ ((tag, (0 : Fin sessionsPerTag)), n) ∧
            ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce)
              ≠ ((tag, slotK), n) := by
          intro nonce
          refine ⟨?_, ?_⟩
          · -- Differs from (tag, 0, n): either T ≠ tag, or sid > 0.
            intro h
            by_cases hT : T = tag
            · -- T = tag: by hAdv, sessionsUsed tag > slotK > 0, so sid > 0 ≠ 0.
              subst hT
              have hsidpos : 0 < s.sessionsUsed T := by
                have : (slotK : ℕ) < s.sessionsUsed T := hAdv
                exact Nat.lt_of_le_of_lt (Nat.zero_le _) this
              have hsid : s.sessionsUsed T = 0 := by
                have := congrArg (fun p => (p.1.2 : Fin sessionsPerTag).val) h
                simpa using this
              omega
            · -- T ≠ tag: first components differ.
              exact hT (congrArg (fun p => p.1.1) h)
          · -- Differs from (tag, slotK, n): either T ≠ tag, or sid ≠ slotK.
            intro h
            by_cases hT : T = tag
            · subst hT
              have : (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag) = slotK := by
                exact (congrArg (fun p => (p.1.2 : Fin sessionsPerTag)) h)
              have hsid : s.sessionsUsed T = slotK.val := by
                exact congrArg Fin.val this
              omega
            · exact hT (congrArg (fun p => p.1.1) h)
        have hcell_eq : ∀ nonce : Nonce,
            g₁ ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce)
            = g₂ ((T, (⟨s.sessionsUsed T, hslot⟩ : Fin sessionsPerTag)), nonce) := by
          intro nonce
          exact heq _ (hcell_ne nonce).1 (hcell_ne nonce).2
        -- The bind structure is `(do { let p ← do { ... }; cont p })`. Flatten via bind_assoc
        -- with explicit OracleComp namespace, then bind_congr on the outer `$ᵗ Nonce`.
        change ($ᵗ Nonce >>= fun nonce => pure _) >>= _ =
             ($ᵗ Nonce >>= fun nonce => pure _) >>= _
        rw [bind_assoc, bind_assoc]
        refine bind_congr fun nonce => ?_
        rw [pure_bind, pure_bind, hcell_eq nonce]
        refine ih _ _ ?_
        -- Post-step state preserves hAdv: sessionsUsed tag either unchanged (T ≠ tag) or
        -- increased by 1 (T = tag); in either case ≥ s.sessionsUsed tag > slotK.
        by_cases hT : T = tag
        · subst hT
          change (slotK : ℕ) < (Function.update s.sessionsUsed T (s.sessionsUsed T + 1)) T
          simp
          omega
        · change (slotK : ℕ) < (Function.update s.sessionsUsed T (s.sessionsUsed T + 1)) tag
          rw [Function.update_of_ne (Ne.symm hT)]
          exact hAdv
      · -- Slot exhausted: both sides return `pure (none, s)`. IH on `k none` at state `s` closes.
        rw [singleTableHandler_tag_run_of_not_lt _ T s hslot,
            singleTableHandler_tag_run_of_not_lt _ T s hslot]
        change (simulateQ (singleTableHandler g₁) (k _)).run' s
             = (simulateQ (singleTableHandler g₂) (k _)).run' s
        exact ih _ s hAdv
    | inr transcript =>
      -- Reader query: handler returns `pure (ReaderReply.ofBool (unlinkReaderAccepts ...), s)`.
      rw [singleTableHandler_reader_run, singleTableHandler_reader_run]
      -- Goal: `pure (ofBool h₁, s) >>= cont_g₁ = pure (ofBool h₂, s) >>= cont_g₂`
      -- where h_i = unlinkReaderAccepts (fun slot nc => g_i (slot, nc)) singlePattern transcript.
      by_cases hn : transcript.nonce = n
      · -- Sub-case `transcript.nonce = n`: existential reads cells at `n`, including the swap
        -- pair. Multiset-invariance: `∃ (T', sid'), g((T', sid'), n) = V` is the same for g₁ and
        -- g₂ because the SET of values present at nonce `n` is identical (swap of positions
        -- doesn't change the multiset).
        subst hn
        -- Key claim: `unlinkReaderAccepts` is equal between g₁ and g₂ at this nonce, via the
        -- existential iff: each side can witness the existential by relocating to the other
        -- cached cell when needed.
        have hresp_eq : unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₁ (slot, nc)) (singlePattern sessionsPerTag) transcript
            = unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₂ (slot, nc)) (singlePattern sessionsPerTag) transcript := by
          -- Alias the outer `tag` to avoid name shadowing with the existential's bound variable.
          set tagOut : TagId := tag with htag_def
          unfold unlinkReaderAccepts tagAccepts
          rw [decide_eq_decide]
          simp only [decide_eq_true_iff, singlePattern]
          constructor
          · rintro ⟨T', sid', hsid'⟩
            by_cases hCase0 : (T', sid') = (tagOut, (0 : Fin sessionsPerTag))
            · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = 0 := Prod.mk.inj hCase0
              exact ⟨tagOut, slotK, hswap_0 ▸ hsid'⟩
            · by_cases hCaseK : (T', sid') = (tagOut, slotK)
              · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = slotK := Prod.mk.inj hCaseK
                exact ⟨tagOut, 0, hswap_K ▸ hsid'⟩
              · refine ⟨T', sid', ?_⟩
                have h_g_eq : g₁ ((T', sid'), transcript.nonce) =
                    g₂ ((T', sid'), transcript.nonce) := by
                  refine heq ((T', sid'), transcript.nonce) ?_ ?_
                  · intro h
                    exact hCase0 (congrArg (fun p => p.1) h)
                  · intro h
                    exact hCaseK (congrArg (fun p => p.1) h)
                exact h_g_eq ▸ hsid'
          · rintro ⟨T', sid', hsid'⟩
            by_cases hCase0 : (T', sid') = (tagOut, (0 : Fin sessionsPerTag))
            · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = 0 := Prod.mk.inj hCase0
              exact ⟨tagOut, slotK, hswap_K ▸ hsid'⟩
            · by_cases hCaseK : (T', sid') = (tagOut, slotK)
              · obtain ⟨rfl, rfl⟩ : T' = tagOut ∧ sid' = slotK := Prod.mk.inj hCaseK
                exact ⟨tagOut, 0, hswap_0 ▸ hsid'⟩
              · refine ⟨T', sid', ?_⟩
                have h_g_eq : g₁ ((T', sid'), transcript.nonce) =
                    g₂ ((T', sid'), transcript.nonce) := by
                  refine heq ((T', sid'), transcript.nonce) ?_ ?_
                  · intro h
                    exact hCase0 (congrArg (fun p => p.1) h)
                  · intro h
                    exact hCaseK (congrArg (fun p => p.1) h)
                exact h_g_eq.symm ▸ hsid'
        rw [hresp_eq]
        change (simulateQ (singleTableHandler g₁) (k _)).run' s
             = (simulateQ (singleTableHandler g₂) (k _)).run' s
        exact ih _ s hAdv
      · -- Sub-case `transcript.nonce ≠ n`: cells at `transcript.nonce` are not in swap pair,
        -- so `g₁` and `g₂` agree pointwise there. `unlinkReaderAccepts` value equal.
        -- Pointwise cell-value equality at every cell at `transcript.nonce`:
        have hg_eq : ∀ T' : TagId, ∀ sid' : Fin sessionsPerTag,
            g₁ ((T', sid'), transcript.nonce) = g₂ ((T', sid'), transcript.nonce) := by
          intro T' sid'
          refine heq ((T', sid'), transcript.nonce) ?_ ?_ <;>
            intro h <;> exact hn (congrArg (fun p => p.2) h)
        have hresp_eq : unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₁ (slot, nc)) (singlePattern sessionsPerTag) transcript
            = unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
              (fun slot nc => g₂ (slot, nc)) (singlePattern sessionsPerTag) transcript := by
          unfold unlinkReaderAccepts tagAccepts
          simp only [hg_eq]
        rw [hresp_eq]
        -- Pure-bind: `pure (response, s) >>= cont = cont (response, s)`. Apply IH.
        change (simulateQ (singleTableHandler g₁) (k _)).run' s
             = (simulateQ (singleTableHandler g₂) (k _)).run' s
        exact ih _ s hAdv

/-! ### Swap-bridge for `singleTableHandler` cache extensions

The slot-positive case's Case M-miss needs to bridge between two cache extensions of
`singleTableHandler`:
* LHS: `c.cacheQuery ((tag, 0), n) u` — slot-0 cell cached at `u`.
* RHS: `c.cacheQuery ((tag, slotK), n) u` — slot-K cell cached at `u`.

Under `hcInv` (`c` has no slot-positive entries) and the post-step invariant
`hAdv : slotK.val < s.sessionsUsed tag`, these two cache extensions produce
**distributionally equal** computation outputs. -/

omit [Nonempty TagId] in
/-- **Swap-bridge for `singleTableHandler`.** Under `hcInv` (no slot-positive cache entries),
`hc0` (slot-0 cell of `c` at `n` uncached), and `hAdv` (`sessionsUsed tag` advanced past `slotK`),
the cache extensions at `(tag, 0)` and `(tag, slotK)` produce the same distribution of `oa`
outputs when run through `singleTableHandler` over a uniform `gS`. This is the workhorse for the
slot-positive Case M-miss closure.

**Hypothesis `hc0`.** The slot-0 cell `((tag, 0), n)` must be uncached in `c`. Otherwise a residual
slot-0 entry survives on the right-hand side (the slot-K `cacheQuery` leaves it untouched) while it
is overwritten by `u` on the left, and a reader query at that residual digest separates the two
distributions. The intended call site (Case M-miss) always has this cell fresh.

**Proof structure.** Single measure-preserving permutation argument: let
`φ = cellSwap ((tag, 0), n) ((tag, slotK), n)`. Apply `evalDist_uniformSample_bind_cellSwap` to
rewrite the LHS via `gS ↦ gS ∘ φ`. Then `singleTableHandler_simulateQ_swap_invariant` gives
POINTWISE equality between the rewritten LHS body and the RHS body, because:
* Cells off the swap pair: `gS ∘ φ` and `gS` agree (φ identity outside the pair).
* `((tag, 0), n)`: both tables cache `u`.
* `((tag, slotK), n)`: T_L(gS ∘ φ) exposes `gS((tag, 0), n)` (φ swaps these); T_R(gS) exposes
  `gS((tag, 0), n)` (uncached by `hc0`). -/
lemma singleTableHandler_cache_swap_eq [Fintype Nonce]
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (tag : TagId) (slotK : Fin sessionsPerTag) (hslotK : slotK ≠ 0)
    (n : Nonce) (u : Digest)
    (hcInv : ∀ tag' : TagId, ∀ sid' : Fin sessionsPerTag, sid' ≠ 0 →
        ∀ n' : Nonce, c ((tag', sid'), n') = none)
    (hc0 : c ((tag, (0 : Fin sessionsPerTag)), n) = none)
    (hAdv : slotK.val < s.sessionsUsed tag)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool) :
    𝒟[do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
         (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending
              (c.cacheQuery ((tag, (0 : Fin sessionsPerTag)), n) u) gS)) oa).run' s]
    = 𝒟[do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
           (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending
                (c.cacheQuery ((tag, slotK), n) u) gS)) oa).run' s] := by
  classical
  -- **Permutation argument**: let `φ := cellSwap ((tag, 0), n) ((tag, slotK), n)`. φ is
  -- measure-preserving on uniform `$ᵗ gS`. We rewrite the LHS via `gS → gS ∘ φ` and show that
  -- `T_L(gS ∘ φ)` and `T_R(gS)` give pointwise equal `singleTableHandler` outputs via the
  -- swap-invariance lemma.
  set φ : (TagId × Fin sessionsPerTag) × Nonce → (TagId × Fin sessionsPerTag) × Nonce :=
    cellSwap ((tag, (0 : Fin sessionsPerTag)), n) ((tag, slotK), n) with hφ
  -- Step 1: apply `evalDist_uniformSample_bind_cellSwap` to rewrite LHS with `gS ↦ gS ∘ φ`.
  rw [evalDist_uniformSample_bind_cellSwap (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) ((tag, (0 : Fin sessionsPerTag)), n) ((tag, slotK), n)]
  -- Step 2: pointwise — show the bodies are equal as functions of gS.
  refine congrArg evalDist (bind_congr fun gS => ?_)
  -- For each fixed `gS`, apply the swap-invariance lemma with the two tables.
  apply singleTableHandler_simulateQ_swap_invariant tag slotK hslotK n oa s hAdv
  · -- heq: agreement off the swap pair.
    intro x hx0 hxK
    -- T_L(gS ∘ φ) at x = tableExtending (cacheQuery c slot-0 u) (gS ∘ φ) at x.
    -- T_R(gS) at x = tableExtending (cacheQuery c slot-K u) gS at x.
    rw [OracleComp.tableExtending_cacheQuery, OracleComp.tableExtending_cacheQuery,
        Function.update_of_ne hx0, Function.update_of_ne hxK]
    -- Both reduce to tableExtending c (·) at x; `gS` and `gS ∘ φ` agree at x since x not in the
    -- swap pair.
    change OracleComp.tableExtending c (gS ∘ φ) x = OracleComp.tableExtending c gS x
    unfold OracleComp.tableExtending
    have hφx : φ x = x := by
      rw [hφ]; exact cellSwap_of_ne _ _ hx0 hxK
    change (c x).getD ((gS ∘ φ) x) = (c x).getD (gS x)
    rw [Function.comp_apply, hφx]
  · -- hswap_0: T_L(gS ∘ φ) at ((tag, 0), n) = u = T_R(gS) at ((tag, slotK), n).
    rw [OracleComp.tableExtending_cacheQuery, OracleComp.tableExtending_cacheQuery,
        Function.update_self, Function.update_self]
  · -- hswap_K: T_L(gS ∘ φ) at ((tag, slotK), n) = gS((tag, 0), n) = T_R(gS) at ((tag, 0), n).
    rw [OracleComp.tableExtending_cacheQuery, OracleComp.tableExtending_cacheQuery]
    have hslotK_ne_0 : ((tag, slotK), n) ≠ ((tag, (0 : Fin sessionsPerTag)), n) := by
      intro h
      exact hslotK (congrArg (fun p => p.1.2) h)
    have h0_ne_slotK : ((tag, (0 : Fin sessionsPerTag)), n) ≠ ((tag, slotK), n) :=
      Ne.symm hslotK_ne_0
    rw [Function.update_of_ne hslotK_ne_0, Function.update_of_ne h0_ne_slotK]
    -- Goal: tableExtending c (gS ∘ φ) ((tag, slotK), n) = tableExtending c gS ((tag, 0), n).
    unfold OracleComp.tableExtending
    -- c at ((tag, slotK), n) = none by hcInv; c at ((tag, 0), n) = none by hc0.
    rw [hcInv tag slotK hslotK n, hc0]
    change gS (φ ((tag, slotK), n)) = gS ((tag, (0 : Fin sessionsPerTag)), n)
    have : φ ((tag, slotK), n) = ((tag, (0 : Fin sessionsPerTag)), n) := by
      rw [hφ, cellSwap_right]
    rw [this]

end UnlinkReduction

end DirectCouplingSwap

end PRFTagReader
