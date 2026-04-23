/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Games
import VCVio.HeapSSP.IdenticalUntilBad
import VCVio.HeapSSP.Composition
import VCVio.CryptoFoundations.SigmaProtocol
import Mathlib.Data.Real.ENatENNReal

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
  cache-growth cost bookkeeping is discharged below with a validity
  invariant for the cached keypair. The remaining mathematical core is
  the HVZK + cache-collision coupling in
  `cmaReal_cmaSim_tv_sign_le_cmaSignEps`.
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

Per-state ε is `ζ_zk + cacheCount · β` on keypair-valid states, with
the cache-hit count read off the heap's `.inr .roCache` cell; invalid
keypair states use the fallback bound `1` because they are unreachable
from the package init but still visible to the generic bridge's
pointwise step hypothesis. The sign-branch HVZK + cache-collision
coupling is the mathematical heart of H3 and is kept as `sorry`
pending the full distributional argument. -/

/-- Size of a random-oracle cache as an `ENNReal`.

For finite caches this is the ordinary finite cardinality. For arbitrary
function-shaped `QueryCache`s whose graph is infinite, the size is `⊤`.
This avoids the `Set.ncard` junk value (`0` on infinite sets) in
state-dependent security bounds that quantify over all heap states. -/
noncomputable def cacheCount {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal : Type}
    (cache : (roSpec M Commit Chal).QueryCache) : ℝ≥0∞ :=
  (cache.toSet.encard : ℝ≥0∞)

/-- The empty cache has zero entries. -/
lemma cacheCount_empty {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal : Type} :
    cacheCount (∅ : (roSpec M Commit Chal).QueryCache) = 0 := by
  simp [cacheCount, QueryCache.toSet_empty]

lemma cacheCount_cacheQuery_le {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal : Type}
    (cache : (roSpec M Commit Chal).QueryCache) (mc : M × Commit) (r : Chal) :
    cacheCount (cache.cacheQuery mc r) ≤ cacheCount cache + 1 := by
  have hencard :
      (cache.cacheQuery mc r).toSet.encard ≤ cache.toSet.encard + 1 :=
    QueryCache.toSet_encard_cacheQuery_le cache mc r
  change ((cache.cacheQuery mc r).toSet.encard : ℝ≥0∞) ≤
    (cache.toSet.encard : ℝ≥0∞) + (1 : ℝ≥0∞)
  rw [← ENat.toENNReal_one, ← ENat.toENNReal_add]
  exact ENat.toENNReal_mono hencard

theorem cmaReal_impl_cacheCount_le_of_costly_or_hash
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (ht : IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t ∨
      IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (z) (hz : z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run h)) :
    cacheCount (z.2 (Sum.inr .roCache)) ≤
      cacheCount (h (Sum.inr .roCache)) + 1 := by
  rcases t with ((n | mc) | m) | ⟨⟩
  · rcases ht with ht | ht <;> exact ht.elim
  · simp only [cmaReal, StateT.run_mk] at hz
    rcases hcache : h (Sum.inr .roCache) mc with _ | r₀
    · rw [hcache] at hz
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
        exists_prop] at hz
      obtain ⟨r, _, rfl⟩ := hz
      simpa using cacheCount_cacheQuery_le (h (Sum.inr .roCache)) mc r
    · rw [hcache] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact le_self_add
  · simp only [cmaReal, StateT.run_mk] at hz
    rcases hkp : h (Sum.inr .keypair) with _ | ⟨pk₀, sk₀⟩
    · rw [hkp] at hz
      simp only [pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
      obtain ⟨⟨pk, sk⟩, _, h_rest⟩ := hz
      obtain ⟨⟨c, prvSt⟩, _, h_rest⟩ := h_rest
      set h₁ := h.update (Sum.inr .keypair) (some (pk, sk)) with hh₁
      rcases hcache : h₁ (Sum.inr .roCache) (m, c) with _ | ch₀
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨ch, _, π, _, rfl⟩ := h_rest
        simpa [hh₁] using cacheCount_cacheQuery_le (h (Sum.inr .roCache)) (m, c) ch
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨π, _, rfl⟩ := h_rest
        simp [hh₁]
    · rw [hkp] at hz
      simp only [pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
      obtain ⟨⟨c, prvSt⟩, _, h_rest⟩ := hz
      rcases hcache : h (Sum.inr .roCache) (m, c) with _ | ch₀
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨ch, _, π, _, rfl⟩ := h_rest
        simpa using cacheCount_cacheQuery_le (h (Sum.inr .roCache)) (m, c) ch
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨π, _, rfl⟩ := h_rest
        exact le_self_add
  · rcases ht with ht | ht <;> exact ht.elim

theorem cmaReal_impl_cacheCount_le_of_not_costly_not_hash
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (hcost : ¬ IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) t)
    (hhash : ¬ IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) t)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (z) (hz : z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run h)) :
    cacheCount (z.2 (Sum.inr .roCache)) ≤ cacheCount (h (Sum.inr .roCache)) := by
  rcases t with ((n | mc) | m) | ⟨⟩
  · simp only [cmaReal, StateT.run_mk] at hz
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
      exists_prop] at hz
    obtain ⟨_, _, rfl⟩ := hz
    rfl
  · exact (hhash True.intro).elim
  · exact (hcost True.intro).elim
  · simp only [cmaReal, StateT.run_mk] at hz
    rcases hkp : h (Sum.inr .keypair) with _ | ⟨pk₀, sk₀⟩
    · rw [hkp] at hz
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
        exists_prop] at hz
      obtain ⟨_, _, rfl⟩ := hz
      simp
    · rw [hkp] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rfl

theorem cmaReal_implConjugate_cacheCount_le_of_costly_or_hash
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (ht : IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t ∨
      IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (z) (hz : z ∈ support
      ((Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)) t).run
        (s, false))) :
    cacheCount z.2.1.2.1 ≤ cacheCount s.2.1 + 1 := by
  simp only [Package.implConjugate_run_apply, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simpa [Prod.map, cmaHeapStateEquiv] using
    cmaReal_impl_cacheCount_le_of_costly_or_hash M Commit Chal σ hr t ht
      ((cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)).symm (s, false)) w hw

theorem cmaReal_implConjugate_cacheCount_le_of_not_costly_not_hash
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (hcost : ¬ IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) t)
    (hhash : ¬ IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) t)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (z) (hz : z ∈ support
      ((Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)) t).run
        (s, false))) :
    cacheCount z.2.1.2.1 ≤ cacheCount s.2.1 := by
  simp only [Package.implConjugate_run_apply, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simpa [Prod.map, cmaHeapStateEquiv] using
    cmaReal_impl_cacheCount_le_of_not_costly_not_hash M Commit Chal σ hr t hcost hhash
      ((cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)).symm (s, false)) w hw

theorem cmaReal_implConjugate_bad_eq_false
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (z) (hz : z ∈ support
      ((Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)) t).run
        (s, false))) :
    z.2.2 = false := by
  simp only [Package.implConjugate_run_apply, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hbad :=
    cmaReal_impl_bad_preserved M Commit Chal σ hr t
      ((cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)).symm (s, false)) w hw
  simpa [Prod.map, cmaHeapStateEquiv] using hbad

private lemma cacheBudget_self_le (C : ℝ≥0∞) (qS qH : ℕ) :
    C ≤ C + qS + qH := by
  exact (le_self_add : C ≤ C + (qS : ℝ≥0∞)).trans le_self_add

private lemma cacheBudget_after_hash_le {C C' : ℝ≥0∞} (qS qH : ℕ)
    (hqH : 0 < qH) (hC : C' ≤ C + 1) :
    C' + qS + (qH - 1 : ℕ) ≤ C + qS + qH := by
  have hqH : (((qH - 1 : ℕ) : ℝ≥0∞) + 1) = (qH : ℝ≥0∞) := by
    have hnat : (qH - 1) + 1 = qH := Nat.sub_add_cancel hqH
    exact_mod_cast hnat
  calc
    C' + (qS : ℝ≥0∞) + ((qH - 1 : ℕ) : ℝ≥0∞)
        ≤ (C + 1) + (qS : ℝ≥0∞) + ((qH - 1 : ℕ) : ℝ≥0∞) := by
          gcongr
    _ = C + (qS : ℝ≥0∞) + (qH : ℝ≥0∞) := by
          rw [show (C + 1) + (qS : ℝ≥0∞) + ((qH - 1 : ℕ) : ℝ≥0∞) =
            C + (qS : ℝ≥0∞) + (((qH - 1 : ℕ) : ℝ≥0∞) + 1) by
              simp only [add_assoc, add_left_comm, add_comm], hqH]

private lemma cacheBudget_after_sign_le {C C' : ℝ≥0∞} (qS qH : ℕ)
    (hqS : 0 < qS) (hC : C' ≤ C + 1) :
    C' + (qS - 1 : ℕ) + qH ≤ C + qS + qH := by
  have hqS : (((qS - 1 : ℕ) : ℝ≥0∞) + 1) = (qS : ℝ≥0∞) := by
    have hnat : (qS - 1) + 1 = qS := Nat.sub_add_cancel hqS
    exact_mod_cast hnat
  calc
    C' + ((qS - 1 : ℕ) : ℝ≥0∞) + (qH : ℝ≥0∞)
        ≤ (C + 1) + ((qS - 1 : ℕ) : ℝ≥0∞) + (qH : ℝ≥0∞) := by
          gcongr
    _ = C + (qS : ℝ≥0∞) + (qH : ℝ≥0∞) := by
          rw [show (C + 1) + ((qS - 1 : ℕ) : ℝ≥0∞) + (qH : ℝ≥0∞) =
            C + (((qS - 1 : ℕ) : ℝ≥0∞) + 1) + (qH : ℝ≥0∞) by
              simp only [add_assoc, add_left_comm, add_comm], hqS]

private lemma cmaSignEps_accum_step_le
    (ζ_zk β C : ℝ≥0∞) (qS qH : ℕ) (hqS : 0 < qS) :
    ζ_zk + C * β +
        (((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
          ((qS - 1 : ℕ) : ℝ≥0∞) * (C + qS + qH) * β)
      ≤ (qS : ℝ≥0∞) * ζ_zk +
          (qS : ℝ≥0∞) * (C + qS + qH) * β := by
  set B : ℝ≥0∞ := C + qS + qH with hB
  have hqS_cast : (1 : ℝ≥0∞) + ((qS - 1 : ℕ) : ℝ≥0∞) = (qS : ℝ≥0∞) := by
    rw [add_comm]
    have hnat : (qS - 1) + 1 = qS := Nat.sub_add_cancel hqS
    exact_mod_cast hnat
  calc
    ζ_zk + C * β +
        (((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
          ((qS - 1 : ℕ) : ℝ≥0∞) * (C + qS + qH) * β)
        ≤ ζ_zk + B * β +
            (((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
              ((qS - 1 : ℕ) : ℝ≥0∞) * B * β) := by
          gcongr
          rw [hB]
          exact cacheBudget_self_le C qS qH
    _ = ((1 : ℝ≥0∞) + ((qS - 1 : ℕ) : ℝ≥0∞)) * ζ_zk +
          ((1 : ℝ≥0∞) + ((qS - 1 : ℕ) : ℝ≥0∞)) * B * β := by
          ring_nf
    _ = (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * B * β := by
          rw [hqS_cast]
    _ = (qS : ℝ≥0∞) * ζ_zk +
          (qS : ℝ≥0∞) * (C + qS + qH) * β := by
          rw [hB]

private lemma pair_eq_false_of_snd {σ : Type} {p : σ × Bool} (h : p.2 = false) :
    p = (p.1, false) := by
  rcases p with ⟨s, b⟩
  simp only [Prod.mk.injEq, true_and] at h ⊢
  exact h

omit [SampleableType Chal] in
/-- `cacheCount` of the initial inner data (empty RO cache) is zero. -/
lemma cacheCount_cmaInitData :
    cacheCount (cmaInitData M Commit Chal
      (Stmt := Stmt) (Wit := Wit)).2.1 = 0 :=
  cacheCount_empty

/-- Per-state ε for the H3 hop, read off `CmaInnerData`'s RO cache. -/
def CmaInnerData.Valid
    {M : Type} {Commit : Type} {Chal Stmt Wit : Type}
    {rel : Stmt → Wit → Bool}
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) : Prop :=
  match s.2.2 with
  | none => True
  | some (pk, sk) => rel pk sk = true

instance
    {M : Type} {Commit : Type} {Chal Stmt Wit : Type}
    {rel : Stmt → Wit → Bool}
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    Decidable (CmaInnerData.Valid (rel := rel) s) := by
  unfold CmaInnerData.Valid
  cases s.2.2 with
  | none => infer_instance
  | some ps =>
      cases ps
      infer_instance

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- The initial CMA inner state has no cached keypair, hence satisfies the
valid-keypair invariant. -/
lemma cmaInitData_valid :
    CmaInnerData.Valid (rel := rel)
      (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit)) := by
  simp [CmaInnerData.Valid]

/-- Tight state-dependent per-step loss for the H3 hop on reachable states. -/
noncomputable def cmaSignEpsCore {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal Stmt Wit : Type}
    (ζ_zk β : ℝ≥0∞) (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    ℝ≥0∞ :=
  ζ_zk + cacheCount s.2.1 * β

/-- State-dependent per-step loss for the H3 hop.

On reachable states, the cached keypair is either absent or generated by
`hr.gen`, so it satisfies the relation and the loss is the intended
`ζ_zk + cacheCount · β`. The fallback value `1` on invalid keypair states
keeps the pointwise TV obligation true for the generic identical-until-bad
bridge, whose step hypothesis is not reachability-indexed. -/
noncomputable def cmaSignEps {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal Stmt Wit : Type}
    {rel : Stmt → Wit → Bool}
    (ζ_zk β : ℝ≥0∞) (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    ℝ≥0∞ :=
  if CmaInnerData.Valid (rel := rel) s then
    cmaSignEpsCore ζ_zk β s
  else
    1

theorem cmaReal_impl_valid_of_valid
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (hvalid : CmaInnerData.Valid (rel := rel)
      (h (Sum.inl .log), h (Sum.inr .roCache), h (Sum.inr .keypair)))
    (z) (hz : z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run h)) :
    CmaInnerData.Valid (rel := rel)
      (z.2 (Sum.inl .log), z.2 (Sum.inr .roCache), z.2 (Sum.inr .keypair)) := by
  rcases t with ((n | mc) | m) | ⟨⟩
  · simp only [cmaReal, StateT.run_mk] at hz
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
      exists_prop] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hvalid
  · simp only [cmaReal, StateT.run_mk] at hz
    rcases hcache : h (Sum.inr .roCache) mc with _ | r₀
    · rw [hcache] at hz
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
        exists_prop] at hz
      obtain ⟨r, _, rfl⟩ := hz
      simpa [CmaInnerData.Valid] using hvalid
    · rw [hcache] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hvalid
  · simp only [cmaReal, StateT.run_mk] at hz
    rcases hkp : h (Sum.inr .keypair) with _ | ⟨pk₀, sk₀⟩
    · rw [hkp] at hz
      simp only [pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
      obtain ⟨⟨pk, sk⟩, hgen, h_rest⟩ := hz
      obtain ⟨⟨c, prvSt⟩, _, h_rest⟩ := h_rest
      set h₁ := h.update (Sum.inr .keypair) (some (pk, sk)) with hh₁
      have hrel : rel pk sk = true := hr.gen_sound pk sk hgen
      rcases hcache : h₁ (Sum.inr .roCache) (m, c) with _ | ch₀
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨ch, _, π, _, rfl⟩ := h_rest
        simp [CmaInnerData.Valid, hh₁, hrel]
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨π, _, rfl⟩ := h_rest
        simp [CmaInnerData.Valid, hh₁, hrel]
    · rw [hkp] at hz
      simp only [pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
      obtain ⟨⟨c, prvSt⟩, _, h_rest⟩ := hz
      have hrel : rel pk₀ sk₀ = true := by
        simpa [CmaInnerData.Valid, hkp] using hvalid
      rcases hcache : h (Sum.inr .roCache) (m, c) with _ | ch₀
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨ch, _, π, _, rfl⟩ := h_rest
        simp [CmaInnerData.Valid, hkp, hrel]
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨π, _, rfl⟩ := h_rest
        simp [CmaInnerData.Valid, hkp, hrel]
  · simp only [cmaReal, StateT.run_mk] at hz
    rcases hkp : h (Sum.inr .keypair) with _ | ⟨pk₀, sk₀⟩
    · rw [hkp] at hz
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
        exists_prop] at hz
      obtain ⟨⟨pk, sk⟩, hgen, rfl⟩ := hz
      have hrel : rel pk sk = true := hr.gen_sound pk sk hgen
      simp [CmaInnerData.Valid, hrel]
    · rw [hkp] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hvalid

theorem cmaReal_implConjugate_valid_of_valid
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (hvalid : CmaInnerData.Valid (rel := rel) s)
    (z) (hz : z ∈ support
      ((Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)) t).run
        (s, false))) :
    CmaInnerData.Valid (rel := rel) z.2.1 := by
  simp only [Package.implConjugate_run_apply, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simpa [Prod.map, cmaHeapStateEquiv] using
    cmaReal_impl_valid_of_valid M Commit Chal σ hr t
      ((cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)).symm (s, false))
      (by simpa [cmaHeapStateEquiv, CmaInnerData.Valid] using hvalid) w hw

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
      ≤ cmaSignEps (rel := rel) ζ_zk β s := by
  by_cases hvalid : CmaInnerData.Valid (rel := rel) s
  · -- Reachable branch: the cached keypair is generated/valid, so the
    -- real transcript and simulator transcript can be coupled by HVZK,
    -- with simulator-commit cache collisions charged to `cacheCount · β`.
    sorry
  · have htv :
        ENNReal.ofReal (tvDist
          (((cmaReal M Commit Chal σ hr).impl
              (Sum.inl (Sum.inr m) : (cmaSpec M Commit Chal Resp Stmt).Domain)).run
              ((cmaHeapStateEquiv M Commit Chal
                  (Stmt := Stmt) (Wit := Wit)).symm (s, false)))
          (((cmaSim M Commit Chal hr simT).impl
              (Sum.inl (Sum.inr m))).run
              ((cmaHeapStateEquiv M Commit Chal
                  (Stmt := Stmt) (Wit := Wit)).symm (s, false)))) ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      exact tvDist_le_one _ _
    simpa [cmaSignEps, hvalid] using htv

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
      ≤ cmaSignEps (rel := rel) ζ_zk β s := by
  rcases t with ((_ | _) | m) | ⟨⟩
  · exact (ht).elim
  · exact (ht).elim
  · exact cmaReal_cmaSim_tv_sign_le_cmaSignEps M Commit Chal σ hr simT ζ_zk β hζ_zk
      hHVZK hCommit m s
  · exact (ht).elim

theorem cmaReal_cmaSim_tv_costly_le_cmaSignEpsCore_of_valid
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (ht : IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) t)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (hvalid : CmaInnerData.Valid (rel := rel) s) :
    ENNReal.ofReal (tvDist
      (((cmaReal M Commit Chal σ hr).impl t).run
        ((cmaHeapStateEquiv M Commit Chal
            (Stmt := Stmt) (Wit := Wit)).symm (s, false)))
      (((cmaSim M Commit Chal hr simT).impl t).run
        ((cmaHeapStateEquiv M Commit Chal
            (Stmt := Stmt) (Wit := Wit)).symm (s, false))))
      ≤ cmaSignEpsCore ζ_zk β s := by
  have h := cmaReal_cmaSim_tv_costly_le_cmaSignEps M Commit Chal σ hr simT
    ζ_zk β hζ_zk hHVZK hCommit t ht s
  simpa [cmaSignEps, cmaSignEpsCore, hvalid] using h

/-! ### Expected cumulative ε cost

Read the cache-count and keypair-validity invariant off the heap via
`φ ∘ state`. The keypair invariant is essential: the pointwise TV step
uses HVZK, which only applies to generated statement-witness pairs. -/

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
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (h_valid : CmaInnerData.Valid (rel := rel) s) :
    expectedSCost
      (Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)))
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      (cmaSignEps (rel := rel) ζ_zk β) A qS (s, false)
      ≤ (qS : ℝ≥0∞) * ζ_zk
        + (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β := by
  set G := Package.implConjugate (cmaReal M Commit Chal σ hr).impl
    (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)) with hG
  change expectedSCost G
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      (cmaSignEps (rel := rel) ζ_zk β) A qS (s, false)
      ≤ (qS : ℝ≥0∞) * ζ_zk
        + (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β
  induction A using OracleComp.inductionOn generalizing qS qH s with
  | pure x =>
      simp
  | query_bind t cont ih =>
      rw [isQueryBound_query_bind_iff] at h_qb h_qH
      obtain ⟨hcanS, hcontS⟩ := h_qb
      obtain ⟨hcanH, hcontH⟩ := h_qH
      rcases t with ((n | mc) | m) | ⟨⟩
      · -- Uniform query: no charge, no cache growth, budgets unchanged.
        simp only [IsCostlyQuery, IsHashQuery, if_false] at hcanS hcontS hcanH hcontH
        have hnotCost :
            ¬ IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt) (Sum.inl (Sum.inl (Sum.inl n))) := by
          intro h; exact h.elim
        have hnotHash :
            ¬ IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt) (Sum.inl (Sum.inl (Sum.inl n))) := by
          intro h; exact h.elim
        rw [expectedSCost_query_bind,
          expectedSCostStep_free G
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEps (rel := rel) ζ_zk β) _ _ qS (s := s) hnotCost]
        calc
          (∑' z : Fin (n + 1) × CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) × Bool,
              Pr[= z | (G (Sum.inl (Sum.inl (Sum.inl n)))).run (s, false)] *
                expectedSCost G
                  (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                    (Resp := Resp) (Stmt := Stmt))
                  (cmaSignEps (rel := rel) ζ_zk β) (cont z.1) qS z.2)
              ≤ ∑' z : Fin (n + 1) × CmaInnerData M Commit Chal
                    (Stmt := Stmt) (Wit := Wit) × Bool,
                  Pr[= z | (G (Sum.inl (Sum.inl (Sum.inl n)))).run (s, false)] *
                    ((qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β) := by
            refine ENNReal.tsum_le_tsum fun z => ?_
            by_cases hz : z ∈ support ((G (Sum.inl (Sum.inl (Sum.inl n)))).run (s, false))
            · have hbad := cmaReal_implConjugate_bad_eq_false M Commit Chal σ hr
                (Sum.inl (Sum.inl (Sum.inl n))) s z (by simpa [G] using hz)
              have hzstate : z.2 = (z.2.1, false) := pair_eq_false_of_snd hbad
              have hcache := cmaReal_implConjugate_cacheCount_le_of_not_costly_not_hash
                M Commit Chal σ hr (Sum.inl (Sum.inl (Sum.inl n))) hnotCost hnotHash s z
                (by simpa [G] using hz)
              have hbudget :
                  cacheCount z.2.1.2.1 + qS + qH ≤ cacheCount s.2.1 + qS + qH := by
                gcongr
              have hvalid_z := cmaReal_implConjugate_valid_of_valid M Commit Chal σ hr
                (Sum.inl (Sum.inl (Sum.inl n))) s h_valid z (by simpa [G] using hz)
              have hih := ih z.1 (qS := qS) (qH := qH)
                (hcontS z.1) (hcontH z.1) z.2.1 hvalid_z
              have hih' :
                  expectedSCost G
                      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                        (Resp := Resp) (Stmt := Stmt))
                      (cmaSignEps (rel := rel) ζ_zk β) (cont z.1) qS z.2
                    ≤ (qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount z.2.1.2.1 + qS + qH) * β := by
                rw [hzstate]
                exact hih
              have htarget_le :
                  (qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount z.2.1.2.1 + qS + qH) * β
                    ≤ (qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β := by
                gcongr
              gcongr
              exact le_trans hih' htarget_le
            · have hprob :
                  Pr[= z | (G (Sum.inl (Sum.inl (Sum.inl n)))).run (s, false)] = 0 :=
                probOutput_eq_zero_of_not_mem_support hz
              rw [hprob]
              rw [zero_mul, zero_mul]
          _ = (∑' z : Fin (n + 1) × CmaInnerData M Commit Chal
                    (Stmt := Stmt) (Wit := Wit) × Bool,
                  Pr[= z | (G (Sum.inl (Sum.inl (Sum.inl n)))).run (s, false)]) *
                ((qS : ℝ≥0∞) * ζ_zk +
                  (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β) := by
              rw [ENNReal.tsum_mul_right]
          _ ≤ 1 * ((qS : ℝ≥0∞) * ζ_zk +
                  (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β) := by
              gcongr
              exact tsum_probOutput_le_one
          _ = (qS : ℝ≥0∞) * ζ_zk +
                (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β := one_mul _
      · -- Random-oracle query: no sign charge, one unit of hash budget may grow the cache.
        simp only [IsCostlyQuery, IsHashQuery, if_false, if_true] at hcanS hcontS hcanH hcontH
        have hqH_pos : 0 < qH := hcanH
        have hnotCost :
            ¬ IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt) (Sum.inl (Sum.inl (Sum.inr mc))) := by
          intro h; exact h.elim
        rw [expectedSCost_query_bind,
          expectedSCostStep_free G
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEps (rel := rel) ζ_zk β) _ _ qS (s := s) hnotCost]
        calc
          (∑' z : Chal × CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) × Bool,
              Pr[= z | (G (Sum.inl (Sum.inl (Sum.inr mc)))).run (s, false)] *
                expectedSCost G
                  (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                    (Resp := Resp) (Stmt := Stmt))
                  (cmaSignEps (rel := rel) ζ_zk β) (cont z.1) qS z.2)
              ≤ ∑' z : Chal × CmaInnerData M Commit Chal
                    (Stmt := Stmt) (Wit := Wit) × Bool,
                  Pr[= z | (G (Sum.inl (Sum.inl (Sum.inr mc)))).run (s, false)] *
                    ((qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β) := by
            refine ENNReal.tsum_le_tsum fun z => ?_
            by_cases hz : z ∈ support ((G (Sum.inl (Sum.inl (Sum.inr mc)))).run (s, false))
            · have hbad := cmaReal_implConjugate_bad_eq_false M Commit Chal σ hr
                (Sum.inl (Sum.inl (Sum.inr mc))) s z (by simpa [G] using hz)
              have hzstate : z.2 = (z.2.1, false) := pair_eq_false_of_snd hbad
              have hcache := cmaReal_implConjugate_cacheCount_le_of_costly_or_hash
                M Commit Chal σ hr (Sum.inl (Sum.inl (Sum.inr mc))) (Or.inr True.intro) s z
                (by simpa [G] using hz)
              have hbudget :
                  cacheCount z.2.1.2.1 + qS + (qH - 1 : ℕ)
                    ≤ cacheCount s.2.1 + qS + qH :=
                cacheBudget_after_hash_le qS qH hqH_pos hcache
              have hvalid_z := cmaReal_implConjugate_valid_of_valid M Commit Chal σ hr
                (Sum.inl (Sum.inl (Sum.inr mc))) s h_valid z (by simpa [G] using hz)
              have hih := ih z.1 (qS := qS) (qH := qH - 1)
                (hcontS z.1) (hcontH z.1) z.2.1 hvalid_z
              have hih' :
                  expectedSCost G
                      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                        (Resp := Resp) (Stmt := Stmt))
                      (cmaSignEps (rel := rel) ζ_zk β) (cont z.1) qS z.2
                    ≤ (qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) *
                        (cacheCount z.2.1.2.1 + qS + (qH - 1 : ℕ)) * β := by
                rw [hzstate]
                exact hih
              have htarget_le :
                  (qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount z.2.1.2.1 + qS + (qH - 1 : ℕ)) * β
                    ≤ (qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β := by
                gcongr
              gcongr
              exact le_trans hih' htarget_le
            · have hprob :
                  Pr[= z | (G (Sum.inl (Sum.inl (Sum.inr mc)))).run (s, false)] = 0 :=
                probOutput_eq_zero_of_not_mem_support hz
              rw [hprob]
              rw [zero_mul, zero_mul]
          _ = (∑' z : Chal × CmaInnerData M Commit Chal
                    (Stmt := Stmt) (Wit := Wit) × Bool,
                  Pr[= z | (G (Sum.inl (Sum.inl (Sum.inr mc)))).run (s, false)]) *
                ((qS : ℝ≥0∞) * ζ_zk +
                  (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β) := by
              rw [ENNReal.tsum_mul_right]
          _ ≤ 1 * ((qS : ℝ≥0∞) * ζ_zk +
                  (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β) := by
              gcongr
              exact tsum_probOutput_le_one
          _ = (qS : ℝ≥0∞) * ζ_zk +
                (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β := one_mul _
      · -- Signing query: pay current ε and recurse with one less sign budget.
        simp only [IsCostlyQuery, IsHashQuery, if_true, if_false] at hcanS hcontS hcanH hcontH
        have hqS_pos : 0 < qS := hcanS
        have hcost :
            IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt) (Sum.inl (Sum.inr m)) := True.intro
        rw [expectedSCost_query_bind,
          expectedSCostStep_costly_pos G
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEps (rel := rel) ζ_zk β) _ _ qS (s := s) hcost hqS_pos]
        have hsum :
            (∑' z : (Commit × Resp) × CmaInnerData M Commit Chal
                  (Stmt := Stmt) (Wit := Wit) × Bool,
                Pr[= z | (G (Sum.inl (Sum.inr m))).run (s, false)] *
                  expectedSCost G
                    (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                      (Resp := Resp) (Stmt := Stmt))
                    (cmaSignEps (rel := rel) ζ_zk β) (cont z.1) (qS - 1) z.2)
              ≤ ((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
                  ((qS - 1 : ℕ) : ℝ≥0∞) *
                    (cacheCount s.2.1 + qS + qH) * β := by
          calc
            (∑' z : (Commit × Resp) × CmaInnerData M Commit Chal
                  (Stmt := Stmt) (Wit := Wit) × Bool,
                Pr[= z | (G (Sum.inl (Sum.inr m))).run (s, false)] *
                  expectedSCost G
                    (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                      (Resp := Resp) (Stmt := Stmt))
                    (cmaSignEps (rel := rel) ζ_zk β) (cont z.1) (qS - 1) z.2)
                ≤ ∑' z : (Commit × Resp) × CmaInnerData M Commit Chal
                      (Stmt := Stmt) (Wit := Wit) × Bool,
                    Pr[= z | (G (Sum.inl (Sum.inr m))).run (s, false)] *
                      (((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
                        ((qS - 1 : ℕ) : ℝ≥0∞) *
                          (cacheCount s.2.1 + qS + qH) * β) := by
              refine ENNReal.tsum_le_tsum fun z => ?_
              by_cases hz : z ∈ support ((G (Sum.inl (Sum.inr m))).run (s, false))
              · have hbad := cmaReal_implConjugate_bad_eq_false M Commit Chal σ hr
                  (Sum.inl (Sum.inr m)) s z (by simpa [G] using hz)
                have hzstate : z.2 = (z.2.1, false) := pair_eq_false_of_snd hbad
                have hcache := cmaReal_implConjugate_cacheCount_le_of_costly_or_hash
                  M Commit Chal σ hr (Sum.inl (Sum.inr m)) (Or.inl True.intro) s z
                  (by simpa [G] using hz)
                have hbudget :
                    cacheCount z.2.1.2.1 + (qS - 1 : ℕ) + qH
                      ≤ cacheCount s.2.1 + qS + qH :=
                  cacheBudget_after_sign_le qS qH hqS_pos hcache
                have hvalid_z := cmaReal_implConjugate_valid_of_valid M Commit Chal σ hr
                  (Sum.inl (Sum.inr m)) s h_valid z (by simpa [G] using hz)
                have hih := ih z.1 (qS := qS - 1) (qH := qH)
                  (hcontS z.1) (hcontH z.1) z.2.1 hvalid_z
                have hih' :
                    expectedSCost G
                        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                          (Resp := Resp) (Stmt := Stmt))
                        (cmaSignEps (rel := rel) ζ_zk β) (cont z.1) (qS - 1) z.2
                      ≤ ((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
                        ((qS - 1 : ℕ) : ℝ≥0∞) *
                          (cacheCount z.2.1.2.1 + (qS - 1 : ℕ) + qH) * β := by
                  rw [hzstate]
                  exact hih
                have htarget_le :
                    ((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
                        ((qS - 1 : ℕ) : ℝ≥0∞) *
                          (cacheCount z.2.1.2.1 + (qS - 1 : ℕ) + qH) * β
                      ≤ ((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
                        ((qS - 1 : ℕ) : ℝ≥0∞) *
                          (cacheCount s.2.1 + qS + qH) * β := by
                  gcongr
                gcongr
                exact le_trans hih' htarget_le
              · have hprob :
                    Pr[= z | (G (Sum.inl (Sum.inr m))).run (s, false)] = 0 :=
                  probOutput_eq_zero_of_not_mem_support hz
                rw [hprob]
                rw [zero_mul, zero_mul]
            _ = (∑' z : (Commit × Resp) × CmaInnerData M Commit Chal
                      (Stmt := Stmt) (Wit := Wit) × Bool,
                    Pr[= z | (G (Sum.inl (Sum.inr m))).run (s, false)]) *
                  (((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
                    ((qS - 1 : ℕ) : ℝ≥0∞) *
                      (cacheCount s.2.1 + qS + qH) * β) := by
                rw [ENNReal.tsum_mul_right]
            _ ≤ 1 * ((((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk) +
                    ((qS - 1 : ℕ) : ℝ≥0∞) *
                      (cacheCount s.2.1 + qS + qH) * β) := by
                gcongr
                exact tsum_probOutput_le_one
            _ = ((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
                  ((qS - 1 : ℕ) : ℝ≥0∞) *
                    (cacheCount s.2.1 + qS + qH) * β := one_mul _
        calc
          cmaSignEps (rel := rel) ζ_zk β s +
              (∑' z : (Commit × Resp) × CmaInnerData M Commit Chal
                    (Stmt := Stmt) (Wit := Wit) × Bool,
                  Pr[= z | (G (Sum.inl (Sum.inr m))).run (s, false)] *
                    expectedSCost G
                      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                        (Resp := Resp) (Stmt := Stmt))
                      (cmaSignEps (rel := rel) ζ_zk β) (cont z.1) (qS - 1) z.2)
              ≤ cmaSignEps (rel := rel) ζ_zk β s +
                  (((qS - 1 : ℕ) : ℝ≥0∞) * ζ_zk +
                    ((qS - 1 : ℕ) : ℝ≥0∞) *
                      (cacheCount s.2.1 + qS + qH) * β) := by
                gcongr
          _ ≤ (qS : ℝ≥0∞) * ζ_zk +
                (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β := by
                simpa [cmaSignEps, h_valid] using
                  cmaSignEps_accum_step_le ζ_zk β (cacheCount s.2.1) qS qH hqS_pos
      · -- Public-key query: no charge, no cache growth, budgets unchanged.
        simp only [IsCostlyQuery, IsHashQuery, if_false] at hcanS hcontS hcanH hcontH
        have hnotCost :
            ¬ IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt) (Sum.inr ()) := by
          intro h; exact h.elim
        have hnotHash :
            ¬ IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt) (Sum.inr ()) := by
          intro h; exact h.elim
        rw [expectedSCost_query_bind,
          expectedSCostStep_free G
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEps (rel := rel) ζ_zk β) _ _ qS (s := s) hnotCost]
        calc
          (∑' z : Stmt × CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) × Bool,
              Pr[= z | (G (Sum.inr ())).run (s, false)] *
                expectedSCost G
                  (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                    (Resp := Resp) (Stmt := Stmt))
                  (cmaSignEps (rel := rel) ζ_zk β) (cont z.1) qS z.2)
              ≤ ∑' z : Stmt × CmaInnerData M Commit Chal
                    (Stmt := Stmt) (Wit := Wit) × Bool,
                  Pr[= z | (G (Sum.inr ())).run (s, false)] *
                    ((qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β) := by
            refine ENNReal.tsum_le_tsum fun z => ?_
            by_cases hz : z ∈ support ((G (Sum.inr ())).run (s, false))
            · have hbad := cmaReal_implConjugate_bad_eq_false M Commit Chal σ hr
                (Sum.inr ()) s z (by simpa [G] using hz)
              have hzstate : z.2 = (z.2.1, false) := pair_eq_false_of_snd hbad
              have hcache := cmaReal_implConjugate_cacheCount_le_of_not_costly_not_hash
                M Commit Chal σ hr (Sum.inr ()) hnotCost hnotHash s z
                (by simpa [G] using hz)
              have hbudget :
                  cacheCount z.2.1.2.1 + qS + qH ≤ cacheCount s.2.1 + qS + qH := by
                gcongr
              have hvalid_z := cmaReal_implConjugate_valid_of_valid M Commit Chal σ hr
                (Sum.inr ()) s h_valid z (by simpa [G] using hz)
              have hih := ih z.1 (qS := qS) (qH := qH)
                (hcontS z.1) (hcontH z.1) z.2.1 hvalid_z
              have hih' :
                  expectedSCost G
                      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                        (Resp := Resp) (Stmt := Stmt))
                      (cmaSignEps (rel := rel) ζ_zk β) (cont z.1) qS z.2
                    ≤ (qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount z.2.1.2.1 + qS + qH) * β := by
                rw [hzstate]
                exact hih
              have htarget_le :
                  (qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount z.2.1.2.1 + qS + qH) * β
                    ≤ (qS : ℝ≥0∞) * ζ_zk +
                      (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β := by
                gcongr
              gcongr
              exact le_trans hih' htarget_le
            · have hprob :
                  Pr[= z | (G (Sum.inr ())).run (s, false)] = 0 :=
                probOutput_eq_zero_of_not_mem_support hz
              rw [hprob]
              rw [zero_mul, zero_mul]
          _ = (∑' z : Stmt × CmaInnerData M Commit Chal
                    (Stmt := Stmt) (Wit := Wit) × Bool,
                  Pr[= z | (G (Sum.inr ())).run (s, false)]) *
                ((qS : ℝ≥0∞) * ζ_zk +
                  (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β) := by
              rw [ENNReal.tsum_mul_right]
          _ ≤ 1 * ((qS : ℝ≥0∞) * ζ_zk +
                  (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β) := by
              gcongr
              exact tsum_probOutput_le_one
          _ = (qS : ℝ≥0∞) * ζ_zk +
                (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β := one_mul _

/-- Initial-state `cmaSignEpsCore` version of
`cmaSignEps_expectedSCost_le`.

The bridge charges the valid-state core cost, while the inductive cache-growth
bound is more convenient for the total cost `cmaSignEps`. This lemma packages
the invariant rewrite and the empty-cache specialization. -/
theorem cmaSignEpsCore_expectedSCost_le
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
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b)) :
    expectedSCost
        (Package.implConjugate (cmaReal M Commit Chal σ hr).impl
          (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)))
        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        (cmaSignEpsCore ζ_zk β) A qS
        (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
      ≤ (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β := by
  set φ := cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit) with hφ
  set s_init := cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit) with hs_init
  have h_valid_init : CmaInnerData.Valid (rel := rel) s_init := by
    rw [hs_init]
    exact cmaInitData_valid M Commit Chal
  have h_pres_valid :
      ∀ (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
        (p : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) × Bool),
        p.2 = false → CmaInnerData.Valid (rel := rel) p.1 →
          ∀ z ∈ support
              ((Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ t).run p),
            CmaInnerData.Valid (rel := rel) z.2.1 := by
    intro t p hpbad hpvalid z hz
    rcases p with ⟨s, b⟩
    cases b with
    | false =>
        exact cmaReal_implConjugate_valid_of_valid M Commit Chal σ hr t s hpvalid z hz
    | true =>
        cases hpbad
  have h_cacheCount_init : cacheCount s_init.2.1 = 0 := by
    rw [hs_init]
    exact cacheCount_cmaInitData M Commit Chal
  have h_cost_eq :
      expectedSCost (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEpsCore ζ_zk β) A qS (s_init, false)
        =
        expectedSCost (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEps (rel := rel) ζ_zk β) A qS (s_init, false) :=
    expectedSCost_eq_of_inv
      (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      (CmaInnerData.Valid (rel := rel))
      (ε := cmaSignEpsCore ζ_zk β) (ε' := cmaSignEps (rel := rel) ζ_zk β)
      (fun s hs => by simp [cmaSignEps, cmaSignEpsCore, hs])
      h_pres_valid A qS (s_init, false) (by intro _; exact h_valid_init)
  have h_gen :=
    cmaSignEps_expectedSCost_le M Commit Chal σ hr ζ_zk β A qS qH h_qb h_qH
      s_init h_valid_init
  rw [h_cacheCount_init, zero_add] at h_gen
  simpa [hφ, hs_init] using (h_cost_eq ▸ h_gen)

/-! ### Top-level H3 hop

State-dep identical-until-bad bridge instantiated at
`G₀ = cmaReal`, `G₁ = cmaSim`, `φ = cmaHeapStateEquiv`. -/

/-- **H3 bridge with caller-supplied expected-cost bound.**

This factors the HeapSSP identical-until-bad argument from the cache-growth
bookkeeping used to bound `expectedSCost`. The generic
`cmaReal_cmaSim_advantage_le_H3_bound` below supplies that bookkeeping from
global sign/hash query bounds. Specialized chains can instead prove a sharper
expected-cost bound for a factored adversary shape, for example when a final
verification hash occurs after all signing behavior and therefore contributes
zero sign-replacement cost. -/
theorem cmaReal_cmaSim_advantage_le_H3_bound_of_expectedSCost
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
    (qS : ℕ) (εBound : ℝ≥0∞)
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b))
    (h_cost_le :
      expectedSCost
        (Package.implConjugate (cmaReal M Commit Chal σ hr).impl
          (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)))
        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        (cmaSignEpsCore ζ_zk β) A qS
        (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
        ≤ εBound) :
    ENNReal.ofReal ((cmaReal M Commit Chal σ hr).advantage
        (cmaSim M Commit Chal hr simT) A)
      ≤ εBound := by
  set φ := cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit) with hφ
  set s_init := cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit) with hs_init
  have h_init₀ : (cmaReal M Commit Chal σ hr).init
      = pure (φ.symm (s_init, false)) := by
    rw [cmaHeapStateEquiv_symm_init]; rfl
  have h_init₁ : (cmaSim M Commit Chal hr simT).init
      = pure (φ.symm (s_init, false)) := by
    rw [cmaHeapStateEquiv_symm_init, cmaSim_init_eq]
  have h_valid_init : CmaInnerData.Valid (rel := rel) s_init := by
    rw [hs_init]
    exact cmaInitData_valid M Commit Chal
  have h_pres_valid :
      ∀ (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
        (p : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) × Bool),
        p.2 = false → CmaInnerData.Valid (rel := rel) p.1 →
          ∀ z ∈ support
              ((Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ t).run p),
            CmaInnerData.Valid (rel := rel) z.2.1 := by
    intro t p hpbad hpvalid z hz
    rcases p with ⟨s, b⟩
    cases b with
    | false =>
        exact cmaReal_implConjugate_valid_of_valid M Commit Chal σ hr t s hpvalid z hz
    | true =>
        cases hpbad
  have h_bridge := Package.advantage_le_expectedSCost_plus_probEvent_bad_of_inv_preserved
    (cmaReal M Commit Chal σ hr) (cmaSim M Commit Chal hr simT)
    φ s_init h_init₀ h_init₁
    (CmaInnerData.Valid (rel := rel)) h_valid_init h_pres_valid
    (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (cmaSignEpsCore ζ_zk β)
    (fun t ht s hs => cmaReal_cmaSim_tv_costly_le_cmaSignEpsCore_of_valid
      M Commit Chal σ hr simT ζ_zk β hζ_zk hHVZK hCommit t ht s hs)
    (fun t ht h => cmaReal_impl_eq_cmaSim_impl_of_not_isCostlyQuery M Commit Chal σ hr simT t ht h)
    (by
      intro t h hbad z hz
      have hbad' : h (Sum.inr .bad) = true := by
        have : (φ h).2 = h (Sum.inr .bad) := rfl
        simpa [this] using hbad
      have h_out : z.2 (Sum.inr .bad) = true :=
        cmaReal_impl_bad_monotone M Commit Chal σ hr t h hbad' z hz
      change (φ z.2).2 = true
      have : (φ z.2).2 = z.2 (Sum.inr .bad) := rfl
      rw [this]; exact h_out)
    A h_qb
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
  have h_cost_le' :
      expectedSCost (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEpsCore ζ_zk β) A qS (s_init, false) ≤ εBound := by
    simpa [hφ, hs_init] using h_cost_le
  calc ENNReal.ofReal ((cmaReal M Commit Chal σ hr).advantage
          (cmaSim M Commit Chal hr simT) A)
      ≤ _ := h_bridge
    _ = expectedSCost (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEpsCore ζ_zk β) A qS (s_init, false) := by
        rw [h_bad_zero, add_zero]
    _ ≤ εBound := h_cost_le'

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
  have h_valid_init : CmaInnerData.Valid (rel := rel) s_init := by
    rw [hs_init]
    exact cmaInitData_valid M Commit Chal
  have h_pres_valid :
      ∀ (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
        (p : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) × Bool),
        p.2 = false → CmaInnerData.Valid (rel := rel) p.1 →
          ∀ z ∈ support
              ((Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ t).run p),
            CmaInnerData.Valid (rel := rel) z.2.1 := by
    intro t p hpbad hpvalid z hz
    rcases p with ⟨s, b⟩
    cases b with
    | false =>
        exact cmaReal_implConjugate_valid_of_valid M Commit Chal σ hr t s hpvalid z hz
    | true =>
        cases hpbad
  -- Apply the invariant-preserving bridge. The step TV obligation is needed
  -- only on valid/reachable CMA inner states, and the final cost is the tight
  -- valid-state loss `cmaSignEpsCore`.
  have h_bridge := Package.advantage_le_expectedSCost_plus_probEvent_bad_of_inv_preserved
    (cmaReal M Commit Chal σ hr) (cmaSim M Commit Chal hr simT)
    φ s_init h_init₀ h_init₁
    (CmaInnerData.Valid (rel := rel)) h_valid_init h_pres_valid
    (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (cmaSignEpsCore ζ_zk β)
    (fun t ht s hs => cmaReal_cmaSim_tv_costly_le_cmaSignEpsCore_of_valid
      M Commit Chal σ hr simT ζ_zk β hζ_zk hHVZK hCommit t ht s hs)
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
  have h_cacheCount_init : cacheCount s_init.2.1 = 0 := by
    rw [hs_init]
    exact cacheCount_cmaInitData M Commit Chal
  have h_cost_le :
      expectedSCost (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEpsCore ζ_zk β) A qS (s_init, false)
        ≤ (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β := by
    have h_cost_eq :
        expectedSCost (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEpsCore ζ_zk β) A qS (s_init, false)
          =
          expectedSCost (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEps (rel := rel) ζ_zk β) A qS (s_init, false) :=
      expectedSCost_eq_of_inv
        (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        (CmaInnerData.Valid (rel := rel))
        (ε := cmaSignEpsCore ζ_zk β) (ε' := cmaSignEps (rel := rel) ζ_zk β)
        (fun s hs => by simp [cmaSignEps, cmaSignEpsCore, hs])
        h_pres_valid A qS (s_init, false) (by intro _; exact h_valid_init)
    have h_gen :=
      cmaSignEps_expectedSCost_le M Commit Chal σ hr ζ_zk β A qS qH h_qb h_qH
        s_init h_valid_init
    rw [h_cacheCount_init, zero_add] at h_gen
    rw [h_cost_eq]
    exact h_gen
  -- Chain the inequalities.
  calc ENNReal.ofReal ((cmaReal M Commit Chal σ hr).advantage
          (cmaSim M Commit Chal hr simT) A)
      ≤ _ := h_bridge
    _ = expectedSCost (Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEpsCore ζ_zk β) A qS (s_init, false) := by
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
