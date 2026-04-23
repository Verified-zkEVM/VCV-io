/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Games
import VCVio.HeapSSP.IdenticalUntilBad
import VCVio.HeapSSP.Composition
import VCVio.CryptoFoundations.SigmaProtocol

/-!
# Game-hops for the HeapSSP Fiat-Shamir EUF-CMA proof

Hops H3, H4, H5 on `HeapSSP.Package`s over `Heap (CmaCells …)` state.

## Structural facts

* **H4 is definitional.** `cmaSim := cmaToNma.link nma`, so the program-
  equivalence hop H4 falls out of `Package.run_link_eq_run_shiftLeft`.
  No inter-state bijection is needed.
* **H3 uses the heap-native bridge.** `VCVio/HeapSSP/IdenticalUntilBad.lean`
  provides `advantage_le_expectedSCost_plus_probEvent_bad` parameterised
  by a bijection `φ : Heap Ident ≃ σ × Bool` extracting the bad cell.
  We supply `φ := cmaHeapStateEquiv` that projects `.inr .bad`, and the
  bridge's per-query, init, monotonicity hypotheses are discharged
  cell-by-cell with heap-native rewrite lemmas.
* **Bad preservation on `cmaReal` is one-line.** `cmaReal` never writes
  the `.bad` cell, a structural fact visible from its handler
  definition. The `h_mono₀` hypothesis and the `Pr[bad | cmaReal] = 0`
  corollary are both immediate.

## Hop summary

* **H3**: `| Pr[cmaReal accepts] - Pr[cmaSim accepts] | ≤ qS · ζ_zk + qS
  · (qS + qH) · β`, via
  `Package.advantage_le_expectedSCost_plus_probEvent_bad` instantiated
  at `G₀ = cmaReal`, `G₁ = cmaSim`, `φ = cmaHeapStateEquiv`. The
  HVZK + cache-collision coupling in `cmaReal_cmaSim_tv_sign_le_cmaSignEps`
  and the cache-growth cost bookkeeping in
  `cmaSignEps_expectedSCost_le` remain as `sorry` placeholders pending
  the full distributional argument.
* **H4**: `cmaSim.run A = nma.run (cmaToNma.shiftLeft A)`, a
  direct instance of `Package.run_link_eq_run_shiftLeft`.
* **H5**: forking-lemma bridge (delegated to `Chain.lean`).
-/

universe u

open ENNReal OracleSpec OracleComp ProbComp VCVio.HeapSSP
  OracleComp.ProgramLogic.Relational

namespace FiatShamir.HeapSSP

variable (M : Type) [DecidableEq M]
variable (Commit : Type) [DecidableEq Commit]
variable (Chal : Type) [SampleableType Chal]
variable {Stmt Wit : Type} {rel : Stmt → Wit → Bool}
variable {Resp PrvState : Type}

/-! ### Heap-to-SSP state bijection

The identical-until-bad bridge in
`VCVio/HeapSSP/IdenticalUntilBad.lean` expects a bijection
`φ : Heap Ident ≃ σ × Bool` that projects the designated `.bad` cell.
For the CMA games we take

  `σ := List M × (roSpec ...).QueryCache × Option (Stmt × Wit)`

(the data of the three non-bad cells) and ship the `.bad` cell as the
`Bool` component. -/

/-- The "extracted" state shape used by the identical-until-bad bridge:
signed-message log, RO cache, lazily-sampled keypair. The bijection
`cmaHeapStateEquiv` below makes it `Heap CmaCells`-isomorphic once a
top-level `Bool` bad flag is adjoined. -/
@[reducible] def CmaInnerData : Type :=
  List M × (roSpec M Commit Chal).QueryCache × Option (Stmt × Wit)

/-- Bijection between the composite heap and `CmaInnerData × Bool`, used
to apply the heap-native identical-until-bad bridge. The `.inr .bad`
cell is routed to the `Bool` component; the other three cells make up
`CmaInnerData`. -/
def cmaHeapStateEquiv :
    Heap (CmaCells M Commit Chal Stmt Wit) ≃ CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)
      × Bool where
  toFun h :=
    ((h (Sum.inl .log), h (Sum.inr .roCache), h (Sum.inr .keypair)),
      h (Sum.inr .bad))
  invFun p
    | Sum.inl .log => p.1.1
    | Sum.inr .roCache => p.1.2.1
    | Sum.inr .keypair => p.1.2.2
    | Sum.inr .bad => p.2
  left_inv h := by
    funext i
    cases i with
    | inl a => cases a; rfl
    | inr b => cases b <;> rfl
  right_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl

/-- Designated initial inner data: empty log, empty RO cache, no
keypair. With bad flag `false`, its `φ.symm` image is the empty heap. -/
@[reducible] def cmaInitData :
    CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) :=
  ([], ∅, none)

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- `φ.symm` applied to the initial inner data (with `bad = false`) is
the empty heap. This is the "init equality" witness for the
identical-until-bad bridge. -/
lemma cmaHeapStateEquiv_symm_init :
    (cmaHeapStateEquiv M Commit Chal
        (Stmt := Stmt) (Wit := Wit)).symm
      (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
      = (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)) := by
  funext i
  cases i with
  | inl a => cases a; rfl
  | inr b => cases b <;> rfl

/-! ### Costly-query predicate for H3 -/

/-- The "costly" query predicate for the H3 identical-until-bad hop: a
query into `cmaSpec` is costly iff it targets the `signSpec` summand.
This is the only branch on which `cmaReal` and `cmaSim` disagree. -/
def IsCostlyQuery : (cmaSpec M Commit Chal Resp Stmt).Domain → Prop
  | Sum.inl (Sum.inr _) => True
  | _ => False

instance : DecidablePred (IsCostlyQuery (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) := fun t =>
  match t with
  | Sum.inl (Sum.inl (Sum.inl _)) => isFalse fun h => h
  | Sum.inl (Sum.inl (Sum.inr _)) => isFalse fun h => h
  | Sum.inl (Sum.inr _) => isTrue trivial
  | Sum.inr _ => isFalse fun h => h

/-- The "hash" query predicate: a query into `cmaSpec` is a random-oracle
query iff it targets the `roSpec` summand, i.e. `Sum.inl (Sum.inl (Sum.inr _))`.
Used alongside `IsCostlyQuery` to bound cache growth during the H3 hop:
`cacheCount` at any reachable state is bounded by the number of prior
sign queries plus the number of prior hash queries. -/
def IsHashQuery : (cmaSpec M Commit Chal Resp Stmt).Domain → Prop
  | Sum.inl (Sum.inl (Sum.inr _)) => True
  | _ => False

instance : DecidablePred (IsHashQuery (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) := fun t =>
  match t with
  | Sum.inl (Sum.inl (Sum.inl _)) => isFalse fun h => h
  | Sum.inl (Sum.inl (Sum.inr _)) => isTrue trivial
  | Sum.inl (Sum.inr _) => isFalse fun h => h
  | Sum.inr _ => isFalse fun h => h

/-! ### `h_step_eq_nS`: non-sign queries coincide

On every non-sign query, `cmaReal.impl` and `cmaSim.impl` reduce to the
same expression pointwise on the heap. The simulated side's non-sign
branches route through the link composition to `nma.impl`, which handles
these as "forwarded import queries"; for `unifSpec`, `roSpec`, and
`pkSpec` this forwarding agrees cell-by-cell with `cmaReal`'s direct
handling. -/

/-- The handler components of `cmaReal.impl` and `cmaSim.impl` are
pointwise identical on every non-sign query. Discharged branch-by-branch
after replacing `h` with `(split).symm (split h)`, applying
`Package.link_impl_apply_run`, and collapsing the resulting
`linkReshape <$> …` against the direct `cmaReal` handler.
-/
theorem cmaReal_impl_eq_cmaSim_impl_of_not_isCostlyQuery
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (ht : ¬ IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) t)
    (h : Heap (CmaCells M Commit Chal Stmt Wit)) :
    ((cmaReal M Commit Chal σ hr).impl t).run h =
      ((cmaSim M Commit Chal hr simT).impl t).run h := by
  -- Factor `h = (split).symm (hα, hβ)`; non-costly branches below share the
  -- same outer forwarder / inner reshape pattern. The per-branch work is
  -- then just computing `nma.impl t'` and re-inserting `hα` via `h_split_symm`.
  let hα : Heap (OuterCell M) :=
    (Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit) h).1
  let hβ : Heap (InnerCell M Commit Chal Stmt Wit) :=
    (Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit) h).2
  have h_split_symm :
      (Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit)).symm (hα, hβ)
        = h :=
    (Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit)).left_inv h
  -- Helper: the `(split).symm (hα, hβ.update b v)` reshape produces
  -- `h.update (Sum.inr b) v`, since `hβ.update b v` differs from `hβ` only
  -- at `b`, and `split.symm` routes `Sum.inr b` to `hβ`.
  have h_reshape_inr :
      ∀ (b : InnerCell M Commit Chal Stmt Wit)
        (v : CellSpec.type (Sum.inr b : CmaCells M Commit Chal Stmt Wit)),
        (Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit)).symm
          (hα, hβ.update b v) = h.update (Sum.inr b) v := by
    intro b v
    funext j
    rcases j with j | j
    · simp [hα, Heap.split_symm_apply_inl]
    · by_cases hj : j = b
      · subst hj
        simp [Heap.split_symm_apply_inr, Heap.get_update_self]
      · have hneq : (Sum.inr j : CmaCells M Commit Chal Stmt Wit) ≠ Sum.inr b :=
          fun heq => hj (Sum.inr.injEq _ _ |>.mp heq)
        simp [hβ, Heap.split_symm_apply_inr, Heap.get_update_of_ne hj,
          Heap.get_update_of_ne hneq]
  -- Unfold `cmaSim` and apply the outer-forward reduction lemma; for every
  -- non-costly `t`, `cmaToNma.impl t` is a pure forwarder through the
  -- corresponding `nmaSpec.query`, and `simulateQ nma.impl` on the forwarded
  -- query reduces to `nma.impl t'` which handles the one-cell update.
  -- Direct approach: on the RHS only, rewrite `h = (split).symm (hα, hβ)` and
  -- unfold `cmaSim = cmaToNma.link nma`. Then reduce
  -- `simulateQ nma.impl ((cmaToNma.impl t).run hα)` per branch.
  conv_rhs => rw [← h_split_symm]
  rcases t with ((n | mc) | m) | ⟨⟩
  · -- Unif: `cmaToNma.impl (Sum.inl (Sum.inl (Sum.inl n)))` forwards via
    -- `nmaSpec.query` to `nma.impl`, which samples `unifSpec.query n`.
    change _ = (((cmaToNma M Commit Chal simT).link (nma M Commit Chal hr)).impl
        (Sum.inl (Sum.inl (Sum.inl n)))).run
      ((Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit)).symm (hα, hβ))
    rw [Package.link_impl_apply_run]
    simp only [cmaToNma, nma, cmaReal, StateT.run_mk, bind_pure_comp,
      simulateQ_map, simulateQ_spec_query, StateT.run_map,
      Functor.map_map, Package.linkReshape, h_split_symm]
  · -- RO: `cmaToNma.impl (Sum.inl (Sum.inl (Sum.inr mc)))` forwards to
    -- `nma.impl` on the same tag; case on cache hit/miss.
    have hβcache_eq : hβ .roCache = h (Sum.inr .roCache) := rfl
    change _ = (((cmaToNma M Commit Chal simT).link (nma M Commit Chal hr)).impl
        (Sum.inl (Sum.inl (Sum.inr mc)))).run
      ((Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit)).symm (hα, hβ))
    rw [Package.link_impl_apply_run]
    simp only [cmaToNma, StateT.run_mk, bind_pure_comp,
      simulateQ_map, simulateQ_spec_query, StateT.run_map,
      Functor.map_map, Package.linkReshape]
    rcases hcache : h (Sum.inr .roCache) mc with _ | r
    · -- Cache miss: both sides sample `r ← $ᵗ Chal`, update `.roCache`.
      simp only [cmaReal, nma, StateT.run_mk, hβcache_eq, hcache,
        bind_pure_comp, Functor.map_map]
      congr 1
      funext a
      exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, (h_reshape_inr .roCache _).symm⟩
    · -- Cache hit: return cached `r`, heap unchanged.
      simp only [cmaReal, nma, StateT.run_mk, hβcache_eq, hcache,
        map_pure, h_split_symm]
  · exact (ht True.intro).elim
  · -- PK: `cmaToNma.impl (Sum.inr ())` forwards to `nma.impl (Sum.inr ())`;
    -- case on keypair hit/miss.
    have hβkp_eq : hβ .keypair = h (Sum.inr .keypair) := rfl
    change _ = (((cmaToNma M Commit Chal simT).link (nma M Commit Chal hr)).impl
        (Sum.inr ())).run
      ((Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit)).symm (hα, hβ))
    rw [Package.link_impl_apply_run]
    simp only [cmaToNma, StateT.run_mk, bind_pure_comp,
      simulateQ_map, simulateQ_spec_query, StateT.run_map,
      Functor.map_map, Package.linkReshape]
    rcases hkp : h (Sum.inr .keypair) with _ | ⟨pk₀, sk₀⟩
    · -- Keypair miss: sample `(pk, sk)`, update `.keypair`.
      simp only [cmaReal, nma, StateT.run_mk, hβkp_eq, hkp,
        bind_pure_comp, Functor.map_map]
      congr 1
      funext p
      exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, (h_reshape_inr .keypair _).symm⟩
    · -- Keypair hit: return stored `pk`, heap unchanged.
      simp only [cmaReal, nma, StateT.run_mk, hβkp_eq, hkp,
        map_pure, h_split_symm]

/-! ### `h_mono₀`: `cmaReal` never writes the `.bad` cell

Structural fact visible from `cmaReal`'s handler: the `.inr .bad` cell
is never `.update`-ed by any branch, so every reachable next heap has
the same `.bad` value as the pre-call heap. Strictly stronger than
bad-flag monotonicity. -/

/-- `cmaReal.impl` preserves the `.inr .bad` cell verbatim on every
query and every pre-call heap.

The four branches of `cmaSpec` all produce output heaps that differ
from the input heap only by `Heap.update`s at cells
`Sum.inl .log`, `Sum.inr .roCache`, or `Sum.inr .keypair` (never
`Sum.inr .bad`). Framing via `Heap.get_update_of_ne` closes each
branch after peeling the monadic support. -/
theorem cmaReal_impl_bad_preserved
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (z) (hz : z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run h)) :
    z.2 (Sum.inr .bad) = h (Sum.inr .bad) := by
  have h_roCache_ne_bad :
      (Sum.inr .bad : CmaCells M Commit Chal Stmt Wit)
        ≠ Sum.inr .roCache := by intro heq; injection heq; contradiction
  have h_keypair_ne_bad :
      (Sum.inr .bad : CmaCells M Commit Chal Stmt Wit)
        ≠ Sum.inr .keypair := by intro heq; injection heq; contradiction
  have h_log_ne_bad :
      (Sum.inr .bad : CmaCells M Commit Chal Stmt Wit)
        ≠ Sum.inl .log := by intro heq; injection heq
  rcases t with ((n | mc) | m) | ⟨⟩ <;>
    simp only [cmaReal, StateT.run_mk] at hz
  · -- Uniform branch: `h` unchanged.
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
      exists_prop] at hz
    obtain ⟨_, _, rfl⟩ := hz
    rfl
  · -- RO branch: cache hit (pure), or miss (update `.roCache`).
    rcases hcache : h (Sum.inr .roCache) mc with _ | r
    · rw [hcache] at hz
      simp only [support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨_, _, rfl⟩ := hz
      simp
    · rw [hcache] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rfl
  · -- Sign branch: successive updates to `.keypair`, `.roCache`, `.log`;
    -- none of them touch `.inr .bad`. Case-split on keypair-hit and
    -- cache-hit, destructure the four `∃`-witnesses, and close each leaf
    -- by `simp` via `Heap.get_update_of_ne` at the three non-bad cells.
    rcases hkp : h (Sum.inr .keypair) with _ | ⟨pk₀, sk₀⟩
    · -- Keypair miss: lazily sample (pk, sk) and update `.keypair`.
      rw [hkp] at hz
      -- Flatten the inner `do let (pk, sk) ← hr.gen; pure (pk, sk, h.update …)`
      -- and collapse the outer `pure … >>= fun ⟨pk', sk', h₁⟩ => rest` via
      -- `pure_bind`; the leading `∃` is then over `hr.gen`'s pair.
      simp only [pure_bind, support_bind, Set.mem_iUnion,
        exists_prop] at hz
      obtain ⟨⟨pk, sk⟩, _, h_rest⟩ := hz
      obtain ⟨⟨c, prvSt⟩, _, h_rest⟩ := h_rest
      set h₁ := h.update (Sum.inr .keypair) (some (pk, sk)) with hh₁
      rcases hcache : h₁ (Sum.inr .roCache) (m, c) with _ | ch₀
      · -- RO cache miss: sample challenge and update `.roCache`.
        rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨ch, _, π, _, rfl⟩ := h_rest
        simp [hh₁]
      · -- RO cache hit: use cached challenge `ch₀`.
        rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨π, _, rfl⟩ := h_rest
        simp [hh₁]
    · -- Keypair hit: reuse `(pk₀, sk₀)` with `h₁ = h`.
      rw [hkp] at hz
      simp only [pure_bind, support_bind, Set.mem_iUnion,
        exists_prop] at hz
      obtain ⟨⟨c, prvSt⟩, _, h_rest⟩ := hz
      rcases hcache : h (Sum.inr .roCache) (m, c) with _ | ch₀
      · -- RO cache miss.
        rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨ch, _, π, _, rfl⟩ := h_rest
        simp
      · -- RO cache hit.
        rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨π, _, rfl⟩ := h_rest
        simp
  · -- PK branch.
    rcases hkp : h (Sum.inr .keypair) with _ | ⟨pk₀, sk₀⟩
    · rw [hkp] at hz
      simp only [support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨_, _, rfl⟩ := hz
      simp
    · rw [hkp] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rfl

/-- Monotonicity corollary of `cmaReal_impl_bad_preserved`: once the
`.bad` cell is `true`, it stays `true`. This is the `h_mono₀`
hypothesis of the identical-until-bad bridge at `G₀ = cmaReal`. -/
theorem cmaReal_impl_bad_monotone
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (hbad : h (Sum.inr .bad) = true)
    (z) (hz : z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run h)) :
    z.2 (Sum.inr .bad) = true := by
  rw [cmaReal_impl_bad_preserved M Commit Chal σ hr t h z hz]
  exact hbad

/-! ### Lifting bad-preservation through the whole simulation -/

/-- Lift per-step `.bad`-preservation through the whole simulation: if
`cmaReal.impl` preserves the `.bad` cell on every query, then so does
`simulateQ cmaReal.impl oa` (induction on `oa`). -/
theorem cmaReal_simulateQ_bad_preserved
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) {α : Type}
    (oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (z) (hz : z ∈ support ((simulateQ (cmaReal M Commit Chal σ hr).impl oa).run h)) :
    z.2 (Sum.inr .bad) = h (Sum.inr .bad) := by
  induction oa using OracleComp.inductionOn generalizing h z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      rfl
  | query_bind t cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, support_bind,
        Set.mem_iUnion, exists_prop] at hz
      obtain ⟨⟨u, h'⟩, h_mem, h_z⟩ := hz
      have hp' : h' (Sum.inr .bad) = h (Sum.inr .bad) :=
        cmaReal_impl_bad_preserved M Commit Chal σ hr t h (u, h') h_mem
      have hz' : z.2 (Sum.inr .bad) = h' (Sum.inr .bad) := ih u h' z h_z
      exact hz'.trans hp'

/-- The bad-event probability of any `cmaReal` simulation started from
the empty heap is zero: every reachable output has `.bad = false`. -/
theorem cmaReal_simulateQ_probEvent_bad_eq_zero
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) {α : Type}
    (oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) :
    Pr[fun z : α × Heap (CmaCells M Commit Chal Stmt Wit) =>
        z.2 (Sum.inr .bad) = true |
        (simulateQ (cmaReal M Commit Chal σ hr).impl oa).run Heap.empty] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro z hz
  have :
      z.2 (Sum.inr .bad)
        = (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)) (Sum.inr .bad) :=
    cmaReal_simulateQ_bad_preserved M Commit Chal σ hr oa Heap.empty z hz
  have hempty : (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit))
      (Sum.inr .bad) = false := rfl
  simp [this]

/-! ### `h_step_tv_S`: per-step TV bound on costly queries

Per-state ε equal to `ζ_zk + cacheCount · β` with the cache-hit count
read off the heap's `.inr .roCache` cell; the sign-branch HVZK +
cache-collision coupling is the mathematical heart of H3 and is kept
as `sorry` pending the full distributional argument. -/

/-- Number of cached entries in a random-oracle cache. -/
noncomputable def cacheCount {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal : Type}
    (cache : (roSpec M Commit Chal).QueryCache) : ℕ :=
  cache.toSet.ncard

/-- The empty cache has zero entries. -/
lemma cacheCount_empty {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal : Type} :
    cacheCount (∅ : (roSpec M Commit Chal).QueryCache) = 0 := by
  simp [cacheCount, QueryCache.toSet_empty]

omit [SampleableType Chal] in
/-- `cacheCount` of the initial inner data (empty RO cache) is zero. -/
lemma cacheCount_cmaInitData :
    cacheCount (cmaInitData M Commit Chal
      (Stmt := Stmt) (Wit := Wit)).2.1 = 0 :=
  cacheCount_empty

/-- Per-state ε for the H3 hop, read off `CmaInnerData`'s RO cache. -/
noncomputable def cmaSignEps {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal Stmt Wit : Type}
    (ζ_zk β : ℝ≥0∞) (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    ℝ≥0∞ :=
  ζ_zk + cacheCount s.2.1 * β

/-- **Per-step TV bound for H3 on a sign query.** Core HVZK + cache-
collision coupling. Left as `sorry` pending the HVZK + commit-marginal
coupling proof. -/
theorem cmaReal_cmaSim_tv_sign_le_cmaSignEps
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (m : M) (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    ENNReal.ofReal (tvDist
      (((cmaReal M Commit Chal σ hr).impl
          (Sum.inl (Sum.inr m) : (cmaSpec M Commit Chal Resp Stmt).Domain)).run
          ((cmaHeapStateEquiv M Commit Chal
              (Stmt := Stmt) (Wit := Wit)).symm (s, false)))
      (((cmaSim M Commit Chal hr simT).impl
          (Sum.inl (Sum.inr m))).run
          ((cmaHeapStateEquiv M Commit Chal
              (Stmt := Stmt) (Wit := Wit)).symm (s, false))))
      ≤ cmaSignEps ζ_zk β s := by
  sorry

/-- The `h_step_tv_S` hypothesis of the bridge at
`S = IsCostlyQuery`, `ε = cmaSignEps ζ_zk β`. Non-sign branches are
vacuous; the sign branch delegates to
`cmaReal_cmaSim_tv_sign_le_cmaSignEps`. -/
theorem cmaReal_cmaSim_tv_costly_le_cmaSignEps
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (ht : IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) t)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    ENNReal.ofReal (tvDist
      (((cmaReal M Commit Chal σ hr).impl t).run
        ((cmaHeapStateEquiv M Commit Chal
            (Stmt := Stmt) (Wit := Wit)).symm (s, false)))
      (((cmaSim M Commit Chal hr simT).impl t).run
        ((cmaHeapStateEquiv M Commit Chal
            (Stmt := Stmt) (Wit := Wit)).symm (s, false))))
      ≤ cmaSignEps ζ_zk β s := by
  rcases t with ((_ | _) | m) | ⟨⟩
  · exact (ht).elim
  · exact (ht).elim
  · exact cmaReal_cmaSim_tv_sign_le_cmaSignEps M Commit Chal σ hr simT ζ_zk β hζ_zk
      hHVZK hCommit m s
  · exact (ht).elim

/-! ### Expected cumulative ε cost

Read the cache-count off the heap via `φ ∘ state`. The cache-growth
invariant and sum bound `Σ (qH + i) ≤ qS (qS + qH)` are kept as
`sorry`. -/

/-- Upper bound on the expected cumulative ε cost for the H3 hop,
integrating `cmaSignEps ζ_zk β` over the reachable states of
`simulateQ cmaReal.impl A`, after conjugation through
`cmaHeapStateEquiv`.

The general form accommodates an arbitrary starting `CmaInnerData`
through its current `cacheCount`: the sum over at most `qS` sign
queries plus `qH` hash queries grows the RO cache by at most one per
step (sign calls internally perform one hash lookup), so along any
trace `cacheCount` stays at most `cacheCount s.2.1 + qS + qH`.

Parameters:
* `h_qb` — sign-query budget: `A` issues at most `qS` signing queries.
* `h_qH` — hash-query budget: `A` issues at most `qH` random-oracle
  queries.

At `s = cmaInitData` (empty cache), `cacheCount s.2.1 = 0` and the
bound specializes to the tight form
`qS * ζ_zk + qS * (qS + qH) * β` expected by the H3 hop
(`cmaReal_cmaSim_advantage_le_H3_bound`). -/
theorem cmaSignEps_expectedSCost_le
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (ζ_zk β : ℝ≥0∞) {α : Type}
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (qS qH : ℕ)
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b))
    (h_qH : OracleComp.IsQueryBound A qH
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b))
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    expectedSCost
      (Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)))
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      (cmaSignEps ζ_zk β) A qS (s, false)
      ≤ (qS : ℝ≥0∞) * ζ_zk
        + (qS : ℝ≥0∞) * ((cacheCount s.2.1 : ℝ≥0∞) + qS + qH) * β := by
  sorry

/-! ### Top-level H3 hop

State-dep identical-until-bad bridge instantiated at
`G₀ = cmaReal`, `G₁ = cmaSim`, `φ = cmaHeapStateEquiv`. -/

/-- **H3 hop** via the HeapSSP state-dep identical-until-bad bridge.
`cmaReal` / `cmaSim` are ε(s)-close on sign queries and pointwise
equal on the rest; `cmaReal`'s `.bad` cell is preserved. Threading
through the bridge and bounding `expectedSCost` by
`qS · ζ_zk + qS · (qS + qH) · β` yields the tight H3 bound. -/
theorem cmaReal_cmaSim_advantage_le_H3_bound
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
    (qS qH : ℕ)
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b))
    (h_qH : OracleComp.IsQueryBound A qH
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b)) :
    ENNReal.ofReal ((cmaReal M Commit Chal σ hr).advantage
        (cmaSim M Commit Chal hr simT) A)
      ≤ (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β := by
  -- Set up the bridge arguments.
  set φ := cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit) with hφ
  set s_init := cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit) with hs_init
  have h_init₀ : (cmaReal M Commit Chal σ hr).init
      = pure (φ.symm (s_init, false)) := by
    rw [cmaHeapStateEquiv_symm_init]; rfl
  have h_init₁ : (cmaSim M Commit Chal hr simT).init
      = pure (φ.symm (s_init, false)) := by
    rw [cmaHeapStateEquiv_symm_init, cmaSim_init_eq]
  -- Apply the state-dep bridge.
  have h_bridge := Package.advantage_le_expectedSCost_plus_probEvent_bad
    (cmaReal M Commit Chal σ hr) (cmaSim M Commit Chal hr simT)
    φ s_init h_init₀ h_init₁
    (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (cmaSignEps ζ_zk β)
    (fun t ht s => cmaReal_cmaSim_tv_costly_le_cmaSignEps M Commit Chal σ hr simT ζ_zk β hζ_zk
      hHVZK hCommit t ht s)
    (fun t ht h => cmaReal_impl_eq_cmaSim_impl_of_not_isCostlyQuery M Commit Chal σ hr simT t ht h)
    (by
      intro t h hbad z hz
      -- The monotonicity hypothesis is phrased on `(φ h).2 = true`, i.e. the
      -- extracted bad-bit. Translate back to the heap-cell form used by
      -- `cmaReal_impl_bad_monotone`.
      have hbad' : h (Sum.inr .bad) = true := by
        have : (φ h).2 = h (Sum.inr .bad) := rfl
        simpa [this] using hbad
      have h_out : z.2 (Sum.inr .bad) = true :=
        cmaReal_impl_bad_monotone M Commit Chal σ hr t h hbad' z hz
      change (φ z.2).2 = true
      have : (φ z.2).2 = z.2 (Sum.inr .bad) := rfl
      rw [this]; exact h_out)
    A h_qb
  -- The bad-probability term is zero since `cmaReal` preserves `.bad` and
  -- the init heap has `.bad = false`.
  have h_bad_zero :
      Pr[fun z : Bool × Heap (CmaCells M Commit Chal Stmt Wit) =>
          (φ z.2).2 = true |
          (simulateQ (cmaReal M Commit Chal σ hr).impl A).run
            (φ.symm (s_init, false))] = 0 := by
    rw [cmaHeapStateEquiv_symm_init]
    have h := cmaReal_simulateQ_probEvent_bad_eq_zero M Commit Chal σ hr A
    have heq :
        (fun z : Bool × Heap (CmaCells M Commit Chal Stmt Wit) =>
            (φ z.2).2 = true)
          = fun z => z.2 (Sum.inr .bad) = true := by
      funext z; rfl
    rw [heq]; exact h
  -- Bound expectedSCost via cmaSignEps_expectedSCost_le.
  have h_cacheCount_init : (cacheCount s_init.2.1 : ℝ≥0∞) = 0 := by
    rw [cacheCount_cmaInitData]; simp
  have h_cost_le :
      expectedSCost (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEps ζ_zk β) A qS (s_init, false)
        ≤ (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β := by
    have h_gen :=
      cmaSignEps_expectedSCost_le M Commit Chal σ hr ζ_zk β A qS qH h_qb h_qH s_init
    rw [h_cacheCount_init, zero_add] at h_gen
    exact h_gen
  -- Chain the inequalities.
  calc ENNReal.ofReal ((cmaReal M Commit Chal σ hr).advantage
          (cmaSim M Commit Chal hr simT) A)
      ≤ _ := h_bridge
    _ = expectedSCost (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEps ζ_zk β) A qS (s_init, false) := by
        rw [h_bad_zero, add_zero]
    _ ≤ (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β := h_cost_le

/-! ### H4 hop: program-equivalence via `run_link_eq_run_shiftLeft`

Because `cmaSim := cmaToNma.link nma` by definition, H4 is a direct
instance of the generic link-shift identity. No state bijection. -/

/-- **H4 hop** (program equivalence). Instance of
`Package.run_link_eq_run_shiftLeft` at
`P = cmaToNma`, `Q = nma`. -/
theorem cmaSim_run_eq_nma_run_shiftLeft_cmaToNma
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {α : Type}
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) :
    (cmaSim M Commit Chal hr simT).run A =
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).run
        ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A) :=
  Package.run_link_eq_run_shiftLeft _ _ A

/-- **H4 hop** (runProb form), specialising to `runProb`. -/
theorem cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool) :
    (cmaSim M Commit Chal hr simT).runProb A =
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
        ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A) := by
  unfold Package.runProb
  exact cmaSim_run_eq_nma_run_shiftLeft_cmaToNma M Commit Chal hr simT A

end FiatShamir.HeapSSP
