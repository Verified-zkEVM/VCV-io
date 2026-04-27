/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Facts
import VCVio.HeapSSP.IdenticalUntilBad
import VCVio.HeapSSP.Composition
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.ProgramLogic.Relational.Quantitative
import Mathlib.Data.Real.ENatENNReal

/-!
# Game-hops for the HeapSSP Fiat-Shamir EUF-CMA proof

Hops H3, H4, H5 on `HeapSSP.Package`s over `Heap (CmaCells …)` state.

## Structural facts

* **H4 is definitional.** `cmaSim := cmaToNma.link nma`, so the program-
  equivalence hop H4 falls out of `VCVio.HeapSSP.Package.run_link_eq_run_shiftLeft`.
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
  `VCVio.HeapSSP.Package.advantage_le_expectedSCost_plus_probEvent_bad` instantiated
  at `G₀ = cmaReal`, `G₁ = cmaSim`, `φ = cmaHeapStateEquiv`. The
  cache-growth cost bookkeeping is discharged below with a validity
  invariant for the cached keypair. The remaining mathematical core is
  the HVZK + cache-collision coupling in
  `cmaReal_cmaSim_tv_sign_le_cmaSignEps`.
* **H4**: `cmaSim.run A = nma.run (cmaToNma.shiftLeft A)`, a
  direct instance of `VCVio.HeapSSP.Package.run_link_eq_run_shiftLeft`.
* **H5**: forking-lemma bridge (delegated to `Chain.lean`).
-/

universe u

open ENNReal OracleSpec OracleComp ProbComp VCVio.StateSeparating
  OracleComp.ProgramLogic.Relational

namespace FiatShamir.HeapSSP

variable (M : Type) [DecidableEq M]
variable (Commit : Type) [DecidableEq Commit]
variable (Chal : Type) [SampleableType Chal]
variable {Stmt Wit : Type} {rel : Stmt → Wit → Bool}
variable {Resp PrvState : Type}

/-! ### Heap-to-extracted-state bijection

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

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
@[simp] lemma cmaHeapStateEquiv_symm_log
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) (bad : Bool) :
    (cmaHeapStateEquiv M Commit Chal
        (Stmt := Stmt) (Wit := Wit)).symm (s, bad) (Sum.inl .log) = s.1 := by
  rcases s with ⟨log, cache, keypair⟩
  rfl

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
@[simp] lemma cmaHeapStateEquiv_symm_roCache
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) (bad : Bool) :
    (cmaHeapStateEquiv M Commit Chal
        (Stmt := Stmt) (Wit := Wit)).symm (s, bad) (Sum.inr .roCache) = s.2.1 := by
  rcases s with ⟨log, cache, keypair⟩
  rfl

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
@[simp] lemma cmaHeapStateEquiv_symm_keypair
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) (bad : Bool) :
    (cmaHeapStateEquiv M Commit Chal
        (Stmt := Stmt) (Wit := Wit)).symm (s, bad) (Sum.inr .keypair) = s.2.2 := by
  rcases s with ⟨log, cache, keypair⟩
  rfl

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
@[simp] lemma cmaHeapStateEquiv_symm_bad
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) (bad : Bool) :
    (cmaHeapStateEquiv M Commit Chal
        (Stmt := Stmt) (Wit := Wit)).symm (s, bad) (Sum.inr .bad) = bad := by
  rcases s with ⟨log, cache, keypair⟩
  rfl

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
`VCVio.HeapSSP.Package.link_impl_apply_run`, and collapsing the resulting
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
    rw [VCVio.HeapSSP.Package.link_impl_apply_run]
    simp only [cmaToNma, nma, cmaReal, StateT.run_mk, bind_pure_comp,
      simulateQ_map, simulateQ_spec_query, StateT.run_map,
      Functor.map_map, VCVio.HeapSSP.Package.linkReshape, h_split_symm]
  · -- RO: `cmaToNma.impl (Sum.inl (Sum.inl (Sum.inr mc)))` forwards to
    -- `nma.impl` on the same tag; case on cache hit/miss.
    have hβcache_eq : hβ .roCache = h (Sum.inr .roCache) := rfl
    change _ = (((cmaToNma M Commit Chal simT).link (nma M Commit Chal hr)).impl
        (Sum.inl (Sum.inl (Sum.inr mc)))).run
      ((Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit)).symm (hα, hβ))
    rw [VCVio.HeapSSP.Package.link_impl_apply_run]
    simp only [cmaToNma, StateT.run_mk, bind_pure_comp,
      simulateQ_map, simulateQ_spec_query, StateT.run_map,
      Functor.map_map, VCVio.HeapSSP.Package.linkReshape]
    rcases hcache : h (Sum.inr .roCache) mc with _ | r
    · -- Cache miss: both sides sample `r ← $ᵗ Chal`, update `.roCache`.
      simp only [cmaReal, nma, StateT.run_mk, hβcache_eq, hcache,
        bind_pure_comp, Functor.map_map]
      congr 1
      funext a
      exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, by
        simpa [h_split_symm] using
          (Heap.split_symm_update_inr
            (α := OuterCell M) (β := InnerCell M Commit Chal Stmt Wit)
            (p := (hα, hβ)) .roCache ((h (Sum.inr .roCache)).cacheQuery mc a)).symm⟩
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
    rw [VCVio.HeapSSP.Package.link_impl_apply_run]
    simp only [cmaToNma, StateT.run_mk, bind_pure_comp,
      simulateQ_map, simulateQ_spec_query, StateT.run_map,
      Functor.map_map, VCVio.HeapSSP.Package.linkReshape]
    rcases hkp : h (Sum.inr .keypair) with _ | ⟨pk₀, sk₀⟩
    · -- Keypair miss: sample `(pk, sk)`, update `.keypair`.
      simp only [cmaReal, nma, StateT.run_mk, hβkp_eq, hkp,
        bind_pure_comp, Functor.map_map]
      congr 1
      funext p
      exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, by
        simpa [h_split_symm] using
          (Heap.split_symm_update_inr
            (α := OuterCell M) (β := InnerCell M Commit Chal Stmt Wit)
            (p := (hα, hβ)) .keypair (some p)).symm⟩
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
  simpa [cmaBadRef, CellRef.get] using
    cmaReal_impl_preserves_badCell M Commit Chal σ hr t h z hz

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
  simpa [cmaBadRef, CellRef.get] using
    OracleComp.simulateQ_run_cellPreserved ((cmaReal M Commit Chal σ hr).impl)
      (cmaBadRef M Commit Chal) (cmaReal_impl_preserves_badRef M Commit Chal σ hr)
      oa h z hz

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
pointwise step hypothesis. The sign-branch proof factors through a public
transcript coupling plus a bad-event transport lemma. -/

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
  exact cmaReal_impl_roCacheCount_le_of_costly_or_hash M Commit Chal σ hr t ht h z hz

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
  exact cmaReal_impl_roCacheCount_le_of_not_costly_not_hash M Commit Chal σ hr t
    hcost hhash h z hz

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
      ((VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)) t).run
        (s, false))) :
    cacheCount z.2.1.2.1 ≤ cacheCount s.2.1 + 1 := by
  simp only [VCVio.HeapSSP.Package.implConjugate_run_apply, support_map, Set.mem_image] at hz
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
      ((VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)) t).run
        (s, false))) :
    cacheCount z.2.1.2.1 ≤ cacheCount s.2.1 := by
  simp only [VCVio.HeapSSP.Package.implConjugate_run_apply, support_map, Set.mem_image] at hz
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
      ((VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)) t).run
        (s, false))) :
    z.2.2 = false := by
  simp only [VCVio.HeapSSP.Package.implConjugate_run_apply, support_map, Set.mem_image] at hz
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
      ((VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)) t).run
        (s, false))) :
    CmaInnerData.Valid (rel := rel) z.2.1 := by
  simp only [VCVio.HeapSSP.Package.implConjugate_run_apply, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simpa [Prod.map, cmaHeapStateEquiv] using
    cmaReal_impl_valid_of_valid M Commit Chal σ hr t
      ((cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)).symm (s, false))
      (by simpa [cmaHeapStateEquiv, CmaInnerData.Valid] using hvalid) w hw

/-- Conjugated-step invariant preservation for the reachable CMA inner-state
predicate `CmaInnerData.Valid`. This packages the `p.2 = false` case split
used by the invariant-gated HeapSSP bridge. -/
theorem cmaReal_implConjugate_preserves_valid
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (p : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) × Bool)
    (hpbad : p.2 = false)
    (hpvalid : CmaInnerData.Valid (rel := rel) p.1)
    (z) (hz : z ∈ support
      ((VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)) t).run p)) :
    CmaInnerData.Valid (rel := rel) z.2.1 := by
  rcases p with ⟨s, b⟩
  cases b with
  | false =>
      simpa using
        cmaReal_implConjugate_valid_of_valid M Commit Chal σ hr t s hpvalid z hz
  | true =>
      cases hpbad

/-- Real signing-step distribution for H3 at an extracted CMA state. -/
@[reducible] noncomputable def cmaRealSignStepDist
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    OracleComp unifSpec ((Commit × Resp) × Heap (CmaCells M Commit Chal Stmt Wit)) :=
  (((cmaReal M Commit Chal σ hr).impl
      (Sum.inl (Sum.inr m) : (cmaSpec M Commit Chal Resp Stmt).Domain)).run
      ((cmaHeapStateEquiv M Commit Chal
        (Stmt := Stmt) (Wit := Wit)).symm (s, false)))

/-- Simulated signing-step distribution for H3 at an extracted CMA state. -/
@[reducible] noncomputable def cmaSimSignStepDist
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    OracleComp unifSpec ((Commit × Resp) × Heap (CmaCells M Commit Chal Stmt Wit)) :=
  (((cmaSim M Commit Chal hr simT).impl
      (Sum.inl (Sum.inr m) : (cmaSpec M Commit Chal Resp Stmt).Domain)).run
      ((cmaHeapStateEquiv M Commit Chal
        (Stmt := Stmt) (Wit := Wit)).symm (s, false)))

private structure CmaRealSignGhost
    (Stmt Wit Commit PrvState Chal Resp : Type) where
  pk : Stmt
  sk : Wit
  commit : Commit
  privateState : PrvState
  challenge : Chal
  ghostResponse : Resp
  actualResponse : Resp

private structure CmaSignPublic
    (Stmt Wit Commit Chal Resp : Type) where
  pk : Stmt
  sk : Wit
  commit : Commit
  challenge : Chal
  response : Resp

private def cmaSignPublicOfTranscript
    {Stmt Wit Commit Chal Resp : Type}
    (pk : Stmt) (sk : Wit) (t : Commit × Chal × Resp) :
    CmaSignPublic Stmt Wit Commit Chal Resp where
  pk := pk
  sk := sk
  commit := t.1
  challenge := t.2.1
  response := t.2.2

private def CmaRealSignGhost.public
    {Stmt Wit Commit PrvState Chal Resp : Type}
    (x : CmaRealSignGhost Stmt Wit Commit PrvState Chal Resp) :
    CmaSignPublic Stmt Wit Commit Chal Resp where
  pk := x.pk
  sk := x.sk
  commit := x.commit
  challenge := x.challenge
  response := x.ghostResponse

private noncomputable def cmaSignKeySource
    (hr : GenerableRelation Stmt Wit rel)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    ProbComp (Stmt × Wit) :=
  match s.2.2 with
  | some keypair => pure keypair
  | none => hr.gen

private noncomputable def cmaRealSignGhostDist
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    ProbComp (CmaRealSignGhost Stmt Wit Commit PrvState Chal Resp) := do
  let (pk, sk) ← cmaSignKeySource M Commit Chal hr s
  let (c, prv) ← σ.commit pk sk
  let ch ← $ᵗ Chal
  let ghostResp ← σ.respond pk sk prv ch
  match s.2.1 (m, c) with
  | some cachedCh => do
      let actualResp ← σ.respond pk sk prv cachedCh
      pure {
        pk := pk, sk := sk, commit := c, privateState := prv,
        challenge := ch, ghostResponse := ghostResp, actualResponse := actualResp }
  | none =>
      pure {
        pk := pk, sk := sk, commit := c, privateState := prv,
        challenge := ch, ghostResponse := ghostResp, actualResponse := ghostResp }

private noncomputable def cmaRealSignPublicDist
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    ProbComp (CmaSignPublic Stmt Wit Commit Chal Resp) := do
  let (pk, sk) ← cmaSignKeySource M Commit Chal hr s
  cmaSignPublicOfTranscript pk sk <$> σ.realTranscript pk sk

private noncomputable def cmaSimSignPublicDist
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    ProbComp (CmaSignPublic Stmt Wit Commit Chal Resp) := do
  let (pk, sk) ← cmaSignKeySource M Commit Chal hr s
  let (c, ch, π) ← simT pk
  pure (cmaSignPublicOfTranscript pk sk (c, ch, π))

private def cmaSignKeyedHeap
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (pk : Stmt) (sk : Wit) :
    Heap (CmaCells M Commit Chal Stmt Wit) :=
  let h :=
    (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)).symm (s, false)
  match s.2.2 with
  | some _ => h
  | none => h.update (Sum.inr .keypair) (some (pk, sk))

private def cmaRealSignGhostOut
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (x : CmaRealSignGhost Stmt Wit Commit PrvState Chal Resp) :
    (Commit × Resp) × Heap (CmaCells M Commit Chal Stmt Wit) :=
  let h₁ := cmaSignKeyedHeap M Commit Chal s x.pk x.sk
  let cache := h₁ (Sum.inr .roCache)
  match cache (m, x.commit) with
  | some _ =>
      ((x.commit, x.actualResponse),
        h₁.update (Sum.inl .log) (h₁ (Sum.inl .log) ++ [m]))
  | none =>
      let h₂ := h₁.update (Sum.inr .roCache)
        (cache.cacheQuery (m, x.commit) x.challenge)
      ((x.commit, x.ghostResponse),
        h₂.update (Sum.inl .log) (h₂ (Sum.inl .log) ++ [m]))

private def cmaSimSignPublicOut
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (x : CmaSignPublic Stmt Wit Commit Chal Resp) :
    (Commit × Resp) × Heap (CmaCells M Commit Chal Stmt Wit) :=
  let h₁ := cmaSignKeyedHeap M Commit Chal s x.pk x.sk
  let cache := h₁ (Sum.inr .roCache)
  match cache (m, x.commit) with
  | some _ =>
      ((x.commit, x.response),
        (h₁.update (Sum.inr .bad) true).update (Sum.inl .log)
          ((h₁.update (Sum.inr .bad) true) (Sum.inl .log) ++ [m]))
  | none =>
      let h₂ := h₁.update (Sum.inr .roCache)
        (cache.cacheQuery (m, x.commit) x.challenge)
      ((x.commit, x.response),
        h₂.update (Sum.inl .log) (h₂ (Sum.inl .log) ++ [m]))

private def cmaSimSignPublicBad
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (x : CmaSignPublic Stmt Wit Commit Chal Resp) : Prop :=
  ∃ ch, s.2.1 (m, x.commit) = some ch

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
private lemma cmaSignKeyedHeap_roCache
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (pk : Stmt) (sk : Wit) :
    (cmaSignKeyedHeap M Commit Chal s pk sk) (Sum.inr .roCache) = s.2.1 := by
  rcases s with ⟨log, cache, keypair⟩
  cases keypair <;> rfl

omit [SampleableType Chal] in
private lemma cmaRealSignGhostOut_eq_cmaSimSignPublicOut_of_not_bad
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (x : CmaRealSignGhost Stmt Wit Commit PrvState Chal Resp)
    (y : CmaSignPublic Stmt Wit Commit Chal Resp)
    (hpub : x.public = y)
    (hbad : ¬ cmaSimSignPublicBad M Commit Chal m s y) :
    cmaRealSignGhostOut M Commit Chal m s x =
      cmaSimSignPublicOut M Commit Chal m s y := by
  rcases x with ⟨pk, sk, c, prv, ch, ghostResp, actualResp⟩
  rcases y with ⟨pk', sk', c', ch', resp'⟩
  simp only [CmaRealSignGhost.public, CmaSignPublic.mk.injEq] at hpub
  rcases hpub with ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hmiss : s.2.1 (m, c) = none := by
    cases hcache : s.2.1 (m, c) with
    | none => rfl
    | some ch0 => exact (hbad ⟨ch0, hcache⟩).elim
  have hmiss_heap :
      (cmaSignKeyedHeap M Commit Chal s pk sk) (Sum.inr .roCache) (m, c) = none := by
    rw [cmaSignKeyedHeap_roCache, hmiss]
  simp [cmaRealSignGhostOut, cmaSimSignPublicOut, hmiss_heap]

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
private lemma cmaSignKeySource_sound
    (hr : GenerableRelation Stmt Wit rel)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (hvalid : CmaInnerData.Valid (rel := rel) s)
    (key : Stmt × Wit)
    (hkey : key ∈ support (cmaSignKeySource M Commit Chal hr s)) :
    rel key.1 key.2 = true := by
  rcases s with ⟨log, cache, keypair⟩
  cases keypair with
  | none =>
      exact hr.gen_sound key.1 key.2 hkey
  | some keypair =>
      simp only [cmaSignKeySource, support_pure, Set.mem_singleton_iff] at hkey
      subst hkey
      simpa [CmaInnerData.Valid] using hvalid

omit [DecidableEq M] [DecidableEq Commit] in
private lemma cmaRealSignGhost_public_evalDist_eq_publicDist
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    𝒟[CmaRealSignGhost.public <$>
      cmaRealSignGhostDist M Commit Chal σ hr m s] =
    𝒟[cmaRealSignPublicDist M Commit Chal σ hr s] := by
  rcases s with ⟨log, cache, keypair⟩
  cases keypair with
  | some key =>
      simp only [cmaRealSignGhostDist, cmaRealSignPublicDist, cmaSignKeySource,
        SigmaProtocol.realTranscript, cmaSignPublicOfTranscript, evalDist_bind,
        evalDist_map, map_bind, pure_bind, bind_pure_comp, Functor.map_map]
      refine bind_congr fun cp => ?_
      refine bind_congr fun ch => ?_
      refine bind_congr fun ghostResp => ?_
      cases hcache : cache (m, cp.1) with
      | none =>
          simp only [evalDist_pure, map_pure, Function.comp_apply]
          let y : CmaSignPublic Stmt Wit Commit Chal Resp :=
            { pk := key.1, sk := key.2, commit := cp.1, challenge := ch,
              response := ghostResp }
          change (pure y : SPMF (CmaSignPublic Stmt Wit Commit Chal Resp)) = pure y
          rfl
      | some cachedCh =>
          simp only [evalDist_map, Functor.map_map, Function.comp_apply]
          let y : CmaSignPublic Stmt Wit Commit Chal Resp :=
            { pk := key.1, sk := key.2, commit := cp.1, challenge := ch,
              response := ghostResp }
          change ((fun _ : Resp => y) <$> 𝒟[σ.respond key.1 key.2 cp.2 cachedCh]) =
            (pure y : SPMF (CmaSignPublic Stmt Wit Commit Chal Resp))
          exact spmf_map_const_of_no_failure
            (probFailure_evalDist_eq_zero (σ.respond key.1 key.2 cp.2 cachedCh))
            y
  | none =>
      simp only [cmaRealSignGhostDist, cmaRealSignPublicDist, cmaSignKeySource,
        SigmaProtocol.realTranscript, cmaSignPublicOfTranscript, evalDist_bind,
        evalDist_map, map_bind, bind_pure_comp, Functor.map_map]
      refine bind_congr fun key => ?_
      refine bind_congr fun cp => ?_
      refine bind_congr fun ch => ?_
      refine bind_congr fun ghostResp => ?_
      cases hcache : cache (m, cp.1) with
      | none =>
          simp only [evalDist_pure, map_pure, Function.comp_apply]
          let y : CmaSignPublic Stmt Wit Commit Chal Resp :=
            { pk := key.1, sk := key.2, commit := cp.1, challenge := ch,
              response := ghostResp }
          change (pure y : SPMF (CmaSignPublic Stmt Wit Commit Chal Resp)) = pure y
          rfl
      | some cachedCh =>
          simp only [evalDist_map, Functor.map_map, Function.comp_apply]
          let y : CmaSignPublic Stmt Wit Commit Chal Resp :=
            { pk := key.1, sk := key.2, commit := cp.1, challenge := ch,
              response := ghostResp }
          change ((fun _ : Resp => y) <$> 𝒟[σ.respond key.1 key.2 cp.2 cachedCh]) =
            (pure y : SPMF (CmaSignPublic Stmt Wit Commit Chal Resp))
          exact spmf_map_const_of_no_failure
            (probFailure_evalDist_eq_zero (σ.respond key.1 key.2 cp.2 cachedCh))
            y

omit [DecidableEq M] [DecidableEq Commit] in
private lemma cmaSignPublicDist_tv_le_hvzk
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit))
    (hvalid : CmaInnerData.Valid (rel := rel) s) :
    ENNReal.ofReal (tvDist
      (cmaRealSignPublicDist M Commit Chal σ hr s)
      (cmaSimSignPublicDist M Commit Chal hr simT s)) ≤ ζ_zk := by
  have htop : ζ_zk ≠ ⊤ := ne_top_of_lt hζ_zk
  rcases s with ⟨log, cache, keypair⟩
  cases keypair with
  | some key =>
      have hrel : rel key.1 key.2 = true := by
        simpa [CmaInnerData.Valid] using hvalid
      have htv :
          tvDist
            (cmaRealSignPublicDist M Commit Chal σ hr (log, cache, some key))
            (cmaSimSignPublicDist M Commit Chal hr simT (log, cache, some key))
            ≤ ζ_zk.toReal := by
        calc
          tvDist
            (cmaRealSignPublicDist M Commit Chal σ hr (log, cache, some key))
            (cmaSimSignPublicDist M Commit Chal hr simT (log, cache, some key))
              ≤ tvDist (σ.realTranscript key.1 key.2) (simT key.1) := by
                  simpa [cmaRealSignPublicDist, cmaSimSignPublicDist, cmaSignKeySource,
                    cmaSignPublicOfTranscript, map_eq_bind_pure_comp] using
                    tvDist_map_le
                      (f := cmaSignPublicOfTranscript (Commit := Commit) (Chal := Chal)
                        (Resp := Resp) key.1 key.2)
                      (σ.realTranscript key.1 key.2) (simT key.1)
          _ ≤ ζ_zk.toReal := hHVZK key.1 key.2 hrel
      exact (ENNReal.ofReal_le_iff_le_toReal htop).mpr htv
  | none =>
      rw [cmaRealSignPublicDist, cmaSimSignPublicDist, cmaSignKeySource]
      refine ofReal_tvDist_bind_left_le_const
        (mx := hr.gen)
        (f := fun key : Stmt × Wit =>
          cmaSignPublicOfTranscript key.1 key.2 <$> σ.realTranscript key.1 key.2)
        (g := fun key : Stmt × Wit =>
          cmaSignPublicOfTranscript key.1 key.2 <$> simT key.1)
        (ε := ζ_zk) ?_
      intro key hkey
      have hrel : rel key.1 key.2 = true := hr.gen_sound key.1 key.2 hkey
      have htv :
          tvDist
            (cmaSignPublicOfTranscript key.1 key.2 <$> σ.realTranscript key.1 key.2)
            (cmaSignPublicOfTranscript key.1 key.2 <$> simT key.1)
            ≤ ζ_zk.toReal :=
        (tvDist_map_le
          (f := cmaSignPublicOfTranscript (Commit := Commit) (Chal := Chal)
            (Resp := Resp) key.1 key.2)
          (σ.realTranscript key.1 key.2) (simT key.1)).trans
            (hHVZK key.1 key.2 hrel)
      exact (ENNReal.ofReal_le_iff_le_toReal htop).mpr htv

omit [SampleableType Chal] in
private lemma simTranscript_cacheHit_prob_le_cacheCount_mul
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (β : ℝ≥0∞)
    (hCommit : σ.simCommitPredictability simT β)
    (pk : Stmt) (m : M)
    (cache : (roSpec M Commit Chal).QueryCache) :
    Pr[fun t : Commit × Chal × Resp => ∃ ch, cache (m, t.1) = some ch | simT pk]
      ≤ cacheCount cache * β := by
  classical
  let commitDist : ProbComp Commit := Prod.fst <$> simT pk
  let hit : Commit → Prop := fun c => ∃ ch, cache (m, c) = some ch
  let S : Finset Commit := (finSupport commitDist).filter hit
  have h_event :
      Pr[fun t : Commit × Chal × Resp => ∃ ch, cache (m, t.1) = some ch | simT pk]
        = Pr[hit | commitDist] := by
    simp [commitDist, hit]
  have h_sum :
      Pr[hit | commitDist] = ∑ c ∈ S, Pr[= c | commitDist] := by
    simp [S, probEvent_eq_sum_filter_finSupport]
  have h_sum_le :
      ∑ c ∈ S, Pr[= c | commitDist] ≤ ∑ c ∈ S, β := by
    refine Finset.sum_le_sum fun c hc => ?_
    exact hCommit pk c
  have h_sum_const :
      (∑ c ∈ S, β) = (S.card : ℝ≥0∞) * β := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have h_card_le : (S.card : ℝ≥0∞) ≤ cacheCount cache := by
    let cacheEntryOfHit : (↑(S : Set Commit)) → cache.toSet := fun c =>
      ⟨⟨(m, c.1), Classical.choose ((Finset.mem_filter.mp c.2).2)⟩,
        (Classical.choose_spec ((Finset.mem_filter.mp c.2).2) :
          cache (m, c.1) =
            some (Classical.choose ((Finset.mem_filter.mp c.2).2)))⟩
    have h_inj : Function.Injective cacheEntryOfHit := by
      intro c₁ c₂ h
      apply Subtype.ext
      have hdomain : (m, c₁.1) = (m, c₂.1) :=
        congrArg (fun x : cache.toSet => x.1.1) h
      exact congrArg Prod.snd hdomain
    let e : {c // c ∈ (S : Set Commit)} ↪ cache.toSet := {
      toFun := cacheEntryOfHit
      inj' := h_inj }
    have henc_type : ENat.card {c // c ∈ (S : Set Commit)} ≤ ENat.card cache.toSet :=
      Function.Embedding.encard_le e
    have henc : (S : Set Commit).encard ≤ cache.toSet.encard := by
      simpa using henc_type
    have henc_nat : (S.card : ℕ∞) ≤ cache.toSet.encard := by
      simpa using henc
    change (S.card : ℝ≥0∞) ≤ (cache.toSet.encard : ℝ≥0∞)
    exact ENat.toENNReal_mono henc_nat
  calc
    Pr[fun t : Commit × Chal × Resp => ∃ ch, cache (m, t.1) = some ch | simT pk]
        = Pr[hit | commitDist] := h_event
    _ = ∑ c ∈ S, Pr[= c | commitDist] := h_sum
    _ ≤ ∑ c ∈ S, β := h_sum_le
    _ = (S.card : ℝ≥0∞) * β := h_sum_const
    _ ≤ cacheCount cache * β := mul_le_mul' h_card_le le_rfl

omit [SampleableType Chal] in
private lemma cmaSimSignPublicBad_prob_le_cacheCount_mul
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (β : ℝ≥0∞)
    (hCommit : σ.simCommitPredictability simT β)
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    Pr[cmaSimSignPublicBad M Commit Chal m s |
        cmaSimSignPublicDist M Commit Chal hr simT s]
      ≤ cacheCount s.2.1 * β := by
  rcases s with ⟨log, cache, keypair⟩
  cases keypair with
  | some key =>
      simpa [cmaSimSignPublicDist, cmaSignKeySource, cmaSimSignPublicBad] using
        simTranscript_cacheHit_prob_le_cacheCount_mul M Commit Chal σ simT β hCommit
          key.1 m cache
  | none =>
      rw [cmaSimSignPublicDist, cmaSignKeySource]
      rw [probEvent_bind_eq_tsum]
      calc
        (∑' key : Stmt × Wit,
            Pr[= key | hr.gen] *
              Pr[cmaSimSignPublicBad M Commit Chal m (log, cache, none) |
                (fun t : Commit × Chal × Resp =>
                  ({ pk := key.1, sk := key.2, commit := t.1,
                     challenge := t.2.1, response := t.2.2 } :
                    CmaSignPublic Stmt Wit Commit Chal Resp)) <$> simT key.1])
            ≤ ∑' key : Stmt × Wit, Pr[= key | hr.gen] * (cacheCount cache * β) := by
              exact ENNReal.tsum_le_tsum fun key =>
                mul_le_mul' le_rfl
                  (by
                    simpa [cmaSimSignPublicBad] using
                      simTranscript_cacheHit_prob_le_cacheCount_mul M Commit Chal σ simT β
                        hCommit key.1 m cache)
        _ = (∑' key : Stmt × Wit, Pr[= key | hr.gen]) * (cacheCount cache * β) := by
              rw [ENNReal.tsum_mul_right]
        _ = cacheCount cache * β := by
              rw [HasEvalPMF.tsum_probOutput_eq_one, one_mul]

private lemma cmaRealSignStepDist_evalDist_eq_ghost
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    𝒟[cmaRealSignStepDist M Commit Chal σ hr m s] =
      𝒟[cmaRealSignGhostOut M Commit Chal m s <$>
        cmaRealSignGhostDist M Commit Chal σ hr m s] := by
  rcases s with ⟨log, cache, keypair⟩
  cases keypair with
  | some key =>
      conv_lhs =>
        simp [cmaRealSignStepDist, cmaRealSignGhostDist, cmaSignKeySource,
          cmaReal, StateT.run_mk]
      conv_rhs =>
        simp [cmaRealSignGhostDist, cmaSignKeySource]
      refine bind_congr fun cp => ?_
      cases hcache : cache (m, cp.1) with
      | none =>
          simp [hcache, cmaRealSignGhostOut, cmaSignKeyedHeap]
      | some cachedCh =>
          conv_lhs =>
            simp [hcache, cmaRealSignGhostOut, cmaSignKeyedHeap]
          conv_rhs =>
            simp [hcache, cmaRealSignGhostOut, cmaSignKeyedHeap]
          rw [spmf_bind_bind_const_of_no_failure
            (p := 𝒟[(($ᵗ Chal) : ProbComp Chal)])
            (q := fun ch => 𝒟[σ.respond key.1 key.2 cp.2 ch])
            (r := (fun actualResp =>
              ((cp.1, actualResp),
                ((cmaHeapStateEquiv M Commit Chal
                    (Stmt := Stmt) (Wit := Wit)).symm
                    ((log, cache, some key), false)).update (Sum.inl .log) (log ++ [m]))) <$>
              𝒟[σ.respond key.1 key.2 cp.2 cachedCh])]
          · exact probFailure_evalDist_eq_zero (($ᵗ Chal) : ProbComp Chal)
          · intro ch
            exact probFailure_evalDist_eq_zero (σ.respond key.1 key.2 cp.2 ch)
  | none =>
      conv_lhs =>
        simp [cmaRealSignStepDist, cmaRealSignGhostDist, cmaSignKeySource,
          cmaReal, StateT.run_mk]
      conv_rhs =>
        simp [cmaRealSignGhostDist, cmaSignKeySource]
      refine bind_congr fun key => ?_
      refine bind_congr fun cp => ?_
      cases hcache : cache (m, cp.1) with
      | none =>
          simp [hcache, cmaRealSignGhostOut, cmaSignKeyedHeap]
      | some cachedCh =>
          conv_lhs =>
            simp [hcache, cmaRealSignGhostOut, cmaSignKeyedHeap]
          conv_rhs =>
            simp [hcache, cmaRealSignGhostOut, cmaSignKeyedHeap]
          rw [spmf_bind_bind_const_of_no_failure
            (p := 𝒟[(($ᵗ Chal) : ProbComp Chal)])
            (q := fun ch => 𝒟[σ.respond key.1 key.2 cp.2 ch])
            (r := (fun actualResp =>
              ((cp.1, actualResp),
                (((cmaHeapStateEquiv M Commit Chal
                    (Stmt := Stmt) (Wit := Wit)).symm
                    ((log, cache, none), false)).update (Sum.inr .keypair) (some key)).update
                      (Sum.inl .log) (log ++ [m]))) <$>
              𝒟[σ.respond key.1 key.2 cp.2 cachedCh])]
          · exact probFailure_evalDist_eq_zero (($ᵗ Chal) : ProbComp Chal)
          · intro ch
            exact probFailure_evalDist_eq_zero (σ.respond key.1 key.2 cp.2 ch)

private lemma nma_simulateQ_liftM_unif_run {α : Type}
    (hr : GenerableRelation Stmt Wit rel)
    (oa : ProbComp α)
    (h : Heap (InnerCell M Commit Chal Stmt Wit)) :
    (simulateQ (nma M Commit Chal hr).impl
      (liftM oa : OracleComp (nmaSpec M Commit Chal Stmt) α)).run h =
      (fun a => (a, h)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing h with
  | pure x =>
      simp
  | query_bind t k ih =>
      have hquery :
          (simulateQ (nma M Commit Chal hr).impl
              (liftM (liftM (unifSpec.query t) :
                OracleQuery (nmaSpec M Commit Chal Stmt) (unifSpec.Range t)))).run h =
            (fun a => (a, h)) <$> (liftM (unifSpec.query t) :
              ProbComp (unifSpec.Range t)) := by
        simp only [simulateQ_query, nma]
        change
          (fun p : unifSpec.Range t × Heap (InnerCell M Commit Chal Stmt Wit) =>
              (p.1, p.2)) <$>
              ((fun a : unifSpec.Range t => (a, h)) <$>
                (liftM (unifSpec.query t) : ProbComp (unifSpec.Range t))) =
            (fun a : unifSpec.Range t => (a, h)) <$>
              (liftM (unifSpec.query t) : ProbComp (unifSpec.Range t))
        simp [Functor.map_map]
      simp only [liftM_bind, simulateQ_bind, StateT.run_bind]
      calc
        ((simulateQ (nma M Commit Chal hr).impl
              (liftM (liftM (unifSpec.query t) :
                OracleQuery (nmaSpec M Commit Chal Stmt) (unifSpec.Range t)))).run h >>=
            fun p => (simulateQ (nma M Commit Chal hr).impl (liftM (k p.1))).run p.2)
            = (((fun a => (a, h)) <$>
                (liftM (unifSpec.query t) : ProbComp (unifSpec.Range t))) >>=
                fun p => (simulateQ (nma M Commit Chal hr).impl (liftM (k p.1))).run p.2) := by
                rw [hquery]
        _ = (fun a => (a, h)) <$> (liftM (unifSpec.query t) >>= k) := by
                rw [bind_map_left]
                calc
                  (do
                      let p ← liftM (unifSpec.query t)
                      (simulateQ (nma M Commit Chal hr).impl (liftM (k p))).run h)
                      = (do
                          let p ← liftM (unifSpec.query t)
                          (fun a => (a, h)) <$> k p) := by
                            refine bind_congr fun u => ?_
                            exact ih u h
                  _ = (fun a => (a, h)) <$> (liftM (unifSpec.query t) >>= k) := by
                            simp [map_bind]

private lemma nma_impl_pk_some_run
    (hr : GenerableRelation Stmt Wit rel)
    (pk : Stmt) (sk : Wit)
    (cache : (roSpec M Commit Chal).QueryCache) (bad : Bool) :
    ((nma M Commit Chal hr).impl
      (Sum.inr () : (nmaSpec M Commit Chal Stmt).Domain)).run
        (fun
          | .roCache => cache
          | .keypair => some (pk, sk)
          | .bad => bad) =
      pure (pk,
        (fun
          | .roCache => cache
          | .keypair => some (pk, sk)
          | .bad => bad)) := by
  rfl

private lemma nma_impl_pk_key_run
    (hr : GenerableRelation Stmt Wit rel)
    (key : Stmt × Wit)
    (cache : (roSpec M Commit Chal).QueryCache) (bad : Bool) :
    ((nma M Commit Chal hr).impl
      (Sum.inr () : (nmaSpec M Commit Chal Stmt).Domain)).run
        (fun
          | .roCache => cache
          | .keypair => some key
          | .bad => bad) =
      pure (key.1,
        (fun
          | .roCache => cache
          | .keypair => some key
          | .bad => bad)) := by
  rcases key with ⟨pk, sk⟩
  exact nma_impl_pk_some_run M Commit Chal hr pk sk cache bad

private lemma nma_impl_pk_none_run
    (hr : GenerableRelation Stmt Wit rel)
    (cache : (roSpec M Commit Chal).QueryCache) (bad : Bool) :
    ((nma M Commit Chal hr).impl
      (Sum.inr () : (nmaSpec M Commit Chal Stmt).Domain)).run
        (fun
          | .roCache => cache
          | .keypair => none
          | .bad => bad) =
      (fun key : Stmt × Wit =>
        (key.1,
          Heap.update
            ((fun
              | .roCache => cache
              | .keypair => none
              | .bad => bad) :
            Heap (InnerCell M Commit Chal Stmt Wit))
            .keypair (some key))) <$> hr.gen := by
  rfl

private lemma nma_impl_prog_run
    (hr : GenerableRelation Stmt Wit rel)
    (m : M) (c : Commit) (ch : Chal)
    (h : Heap (InnerCell M Commit Chal Stmt Wit)) :
    ((nma M Commit Chal hr).impl
      (Sum.inl (Sum.inr (m, c, ch)) :
        (nmaSpec M Commit Chal Stmt).Domain)).run h =
      match h .roCache (m, c) with
      | some _ => pure ((), h.update .bad true)
      | none => pure ((), h.update .roCache ((h .roCache).cacheQuery (m, c) ch)) := by
  cases hcache : h .roCache (m, c) <;> simp [nma, hcache]

private lemma cmaSimSignStepDist_evalDist_eq_public
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (m : M)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    𝒟[cmaSimSignStepDist M Commit Chal hr simT m s] =
      𝒟[cmaSimSignPublicOut M Commit Chal m s <$>
        cmaSimSignPublicDist M Commit Chal hr simT s] := by
  rcases s with ⟨log, cache, keypair⟩
  cases keypair with
  | some key =>
      let hα : Heap (OuterCell M) := fun
        | .log => log
      let hβ : Heap (InnerCell M Commit Chal Stmt Wit) := fun
        | .roCache => cache
        | .keypair => some key
        | .bad => false
      have hstart :
          (cmaHeapStateEquiv M Commit Chal
              (Stmt := Stmt) (Wit := Wit)).symm ((log, cache, some key), false) =
            (Heap.split (OuterCell M)
              (InnerCell M Commit Chal Stmt Wit)).symm (hα, hβ) := by
        funext i
        cases i with
        | inl a => cases a; rfl
        | inr b => cases b <;> rfl
      unfold cmaSimSignStepDist
      rw [hstart, VCVio.HeapSSP.Package.link_impl_apply_run]
      conv_lhs =>
        simp [cmaToNma, nma_simulateQ_liftM_unif_run,
          StateT.run_mk, VCVio.HeapSSP.Package.linkReshape, hα]
      conv_rhs =>
        simp [cmaSimSignPublicDist, cmaSignKeySource]
      have hpk :
          ((nma M Commit Chal hr).impl
            (Sum.inr () : (nmaSpec M Commit Chal Stmt).Domain)).run hβ =
            pure (key.1, hβ) := by
        simp [hβ, nma]
      conv_lhs =>
        simp [nma, hβ]
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun x => ?_
      cases hcache : cache (m, x.1) with
      | none =>
          conv_lhs =>
            simp [hcache, hstart, hα, hβ, cmaSignPublicOfTranscript]
          conv_rhs =>
            simp [hcache, hstart, hα, hβ, cmaSimSignPublicOut, cmaSignKeyedHeap,
              cmaSignPublicOfTranscript]
          apply congrArg pure
          apply Prod.ext
          · rfl
          · funext i
            cases i with
            | inl o => cases o; simp [Heap.update]
            | inr c => cases c <;> simp [Heap.update]
      | some cachedCh =>
          conv_lhs =>
            simp [hcache, hstart, hα, hβ, cmaSignPublicOfTranscript]
          conv_rhs =>
            simp [hcache, hstart, hα, hβ, cmaSimSignPublicOut, cmaSignKeyedHeap,
              cmaSignPublicOfTranscript]
          apply congrArg pure
          apply Prod.ext
          · rfl
          · funext i
            cases i with
            | inl o => cases o; simp [Heap.update]
            | inr c => cases c <;> simp [Heap.update]
  | none =>
      let hα : Heap (OuterCell M) := fun
        | .log => log
      let hβ : Heap (InnerCell M Commit Chal Stmt Wit) := fun
        | .roCache => cache
        | .keypair => none
        | .bad => false
      have hstart :
          (cmaHeapStateEquiv M Commit Chal
              (Stmt := Stmt) (Wit := Wit)).symm ((log, cache, none), false) =
            (Heap.split (OuterCell M)
              (InnerCell M Commit Chal Stmt Wit)).symm (hα, hβ) := by
        funext i
        cases i with
        | inl a => cases a; rfl
        | inr b => cases b <;> rfl
      unfold cmaSimSignStepDist
      rw [hstart, VCVio.HeapSSP.Package.link_impl_apply_run]
      conv_lhs =>
        simp [cmaToNma, nma_simulateQ_liftM_unif_run,
          StateT.run_mk, VCVio.HeapSSP.Package.linkReshape, hα]
      conv_rhs =>
        simp [cmaSimSignPublicDist, cmaSignKeySource]
      have hpk :
          ((nma M Commit Chal hr).impl
            (Sum.inr () : (nmaSpec M Commit Chal Stmt).Domain)).run hβ =
            (fun key : Stmt × Wit => (key.1, hβ.update .keypair (some key))) <$> hr.gen := by
        simp [hβ, nma]
      conv_lhs =>
        simp [nma, hβ]
      refine bind_congr fun key => ?_
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun x => ?_
      cases hcache : cache (m, x.1) with
      | none =>
          conv_lhs =>
            simp [hcache, hstart, hα, hβ, Heap.get, cmaSignPublicOfTranscript]
          conv_rhs =>
            simp [hcache, hstart, hα, hβ, Heap.get, cmaSimSignPublicOut, cmaSignKeyedHeap,
              cmaSignPublicOfTranscript]
          apply congrArg pure
          apply Prod.ext
          · rfl
          · funext i
            cases i with
            | inl o => cases o; simp [Heap.update]
            | inr c => cases c <;> simp [Heap.update]
      | some cachedCh =>
          conv_lhs =>
            simp [hcache, hstart, hα, hβ, Heap.get, cmaSignPublicOfTranscript]
          conv_rhs =>
            simp [hcache, hstart, hα, hβ, Heap.get, cmaSimSignPublicOut, cmaSignKeyedHeap,
              cmaSignPublicOfTranscript]
          apply congrArg pure
          apply Prod.ext
          · rfl
          · funext i
            cases i with
            | inl o => cases o; simp [Heap.update]
            | inr c => cases c <;> simp [Heap.update]

/-- **Per-step TV bound for H3 on a sign query.** Core HVZK + cache-
collision coupling. The public transcript distance is charged to HVZK;
simulator commits colliding with the live RO cache are charged to
`cacheCount · β`. -/
theorem cmaReal_cmaSim_tv_sign_le_cmaSignEps
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (m : M) (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit)) :
    ENNReal.ofReal (tvDist
      (cmaRealSignStepDist M Commit Chal σ hr m s)
      (cmaSimSignStepDist M Commit Chal hr simT m s))
      ≤ cmaSignEps (rel := rel) ζ_zk β s := by
  by_cases hvalid : CmaInnerData.Valid (rel := rel) s
  · -- Reachable branch: the cached keypair is generated/valid, so the
    -- real transcript and simulator transcript can be coupled by HVZK,
    -- with simulator-commit cache collisions charged to `cacheCount · β`.
    let realGhost := cmaRealSignGhostDist M Commit Chal σ hr m s
    let simPub := cmaSimSignPublicDist M Commit Chal hr simT s
    let realOut :
        CmaRealSignGhost Stmt Wit Commit PrvState Chal Resp →
          (Commit × Resp) × Heap (CmaCells M Commit Chal Stmt Wit) :=
      cmaRealSignGhostOut M Commit Chal m s
    let simOut :
        CmaSignPublic Stmt Wit Commit Chal Resp →
          (Commit × Resp) × Heap (CmaCells M Commit Chal Stmt Wit) :=
      cmaSimSignPublicOut M Commit Chal m s
    let bad : CmaSignPublic Stmt Wit Commit Chal Resp → Prop :=
      cmaSimSignPublicBad M Commit Chal m s
    have hreal :
        𝒟[cmaRealSignStepDist M Commit Chal σ hr m s] =
          𝒟[realOut <$> realGhost] := by
      simpa [realGhost, realOut] using
        cmaRealSignStepDist_evalDist_eq_ghost M Commit Chal σ hr m s
    have hsim :
        𝒟[cmaSimSignStepDist M Commit Chal hr simT m s] =
          𝒟[simOut <$> simPub] := by
      simpa [simPub, simOut] using
        cmaSimSignStepDist_evalDist_eq_public M Commit Chal hr simT m s
    have hstep :
        ENNReal.ofReal (tvDist
          (cmaRealSignStepDist M Commit Chal σ hr m s)
          (cmaSimSignStepDist M Commit Chal hr simT m s)) =
        ENNReal.ofReal (tvDist (realOut <$> realGhost) (simOut <$> simPub)) := by
      simp [tvDist, hreal, hsim]
    have hprivate :
        ENNReal.ofReal (tvDist (realOut <$> realGhost) (simOut <$> simPub))
          ≤ ENNReal.ofReal (tvDist (CmaRealSignGhost.public <$> realGhost) simPub) +
              Pr[bad | simPub] := by
      exact ofReal_tvDist_map_private_right_bad_le
        (oa := realGhost) (ob := simPub)
        (pub := CmaRealSignGhost.public)
        (fa := realOut) (fb := simOut) (bad := bad)
        (fun x y hpub hbad =>
          cmaRealSignGhostOut_eq_cmaSimSignPublicOut_of_not_bad
            M Commit Chal m s x y hpub hbad)
    have hpublic :
        ENNReal.ofReal (tvDist (CmaRealSignGhost.public <$> realGhost) simPub) ≤ ζ_zk := by
      have hpub_eval :
          𝒟[CmaRealSignGhost.public <$> realGhost] =
            𝒟[cmaRealSignPublicDist M Commit Chal σ hr s] := by
        simpa [realGhost] using
          cmaRealSignGhost_public_evalDist_eq_publicDist M Commit Chal σ hr m s
      have hbound :=
        cmaSignPublicDist_tv_le_hvzk M Commit Chal σ hr simT ζ_zk hζ_zk hHVZK s hvalid
      simpa [tvDist, simPub, hpub_eval] using hbound
    have hbad :
        Pr[bad | simPub] ≤ cacheCount s.2.1 * β := by
      simpa [bad, simPub] using
        cmaSimSignPublicBad_prob_le_cacheCount_mul M Commit Chal σ hr simT β
          hCommit m s
    calc
      ENNReal.ofReal (tvDist
        (cmaRealSignStepDist M Commit Chal σ hr m s)
        (cmaSimSignStepDist M Commit Chal hr simT m s))
          = ENNReal.ofReal (tvDist (realOut <$> realGhost) (simOut <$> simPub)) :=
              hstep
      _ ≤ ENNReal.ofReal (tvDist (CmaRealSignGhost.public <$> realGhost) simPub) +
            Pr[bad | simPub] := hprivate
      _ ≤ ζ_zk + cacheCount s.2.1 * β := add_le_add hpublic hbad
      _ = cmaSignEps (rel := rel) ζ_zk β s := by
            simp [cmaSignEps, cmaSignEpsCore, hvalid]
  · have htv :
        ENNReal.ofReal (tvDist
          (cmaRealSignStepDist M Commit Chal σ hr m s)
          (cmaSimSignStepDist M Commit Chal hr simT m s)) ≤ 1 := by
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
      (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl
        (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)))
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      (cmaSignEps (rel := rel) ζ_zk β) A qS (s, false)
      ≤ (qS : ℝ≥0∞) * ζ_zk
        + (qS : ℝ≥0∞) * (cacheCount s.2.1 + qS + qH) * β := by
  set G := VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl
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
        (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl
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
              ((VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ t).run p),
            CmaInnerData.Valid (rel := rel) z.2.1 := by
    intro t p hpbad hpvalid z hz
    simpa [hφ] using
      cmaReal_implConjugate_preserves_valid M Commit Chal σ hr t p hpbad hpvalid z hz
  have h_cacheCount_init : cacheCount s_init.2.1 = 0 := by
    rw [hs_init]
    exact cacheCount_cmaInitData M Commit Chal
  have h_cost_eq :
      expectedSCost (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEpsCore ζ_zk β) A qS (s_init, false)
        =
        expectedSCost (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEps (rel := rel) ζ_zk β) A qS (s_init, false) :=
    expectedSCost_eq_of_inv
      (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
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
        (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl
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
              ((VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ t).run p),
            CmaInnerData.Valid (rel := rel) z.2.1 := by
    intro t p hpbad hpvalid z hz
    simpa [hφ] using
      cmaReal_implConjugate_preserves_valid M Commit Chal σ hr t p hpbad hpvalid z hz
  have h_bridge :=
    VCVio.HeapSSP.Package.advantage_le_expectedSCost_plus_probEvent_bad_of_inv_preserved
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
      expectedSCost (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEpsCore ζ_zk β) A qS (s_init, false) ≤ εBound := by
    simpa [hφ, hs_init] using h_cost_le
  calc ENNReal.ofReal ((cmaReal M Commit Chal σ hr).advantage
          (cmaSim M Commit Chal hr simT) A)
      ≤ _ := h_bridge
    _ = expectedSCost (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
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
              ((VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ t).run p),
            CmaInnerData.Valid (rel := rel) z.2.1 := by
    intro t p hpbad hpvalid z hz
    simpa [hφ] using
      cmaReal_implConjugate_preserves_valid M Commit Chal σ hr t p hpbad hpvalid z hz
  have h_cacheCount_init : cacheCount s_init.2.1 = 0 := by
    rw [hs_init]
    exact cacheCount_cmaInitData M Commit Chal
  have h_cost_le :
      expectedSCost (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEpsCore ζ_zk β) A qS (s_init, false)
        ≤ (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β := by
    have h_cost_eq :
        expectedSCost (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEpsCore ζ_zk β) A qS (s_init, false)
          =
          expectedSCost (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEps (rel := rel) ζ_zk β) A qS (s_init, false) :=
      expectedSCost_eq_of_inv
        (VCVio.HeapSSP.Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ)
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
  exact cmaReal_cmaSim_advantage_le_H3_bound_of_expectedSCost
    M Commit Chal σ hr simT ζ_zk β hζ_zk hHVZK hCommit A qS
    ((qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β) h_qb h_cost_le

/-! ### H4 hop: program-equivalence via `run_link_eq_run_shiftLeft`

Because `cmaSim := cmaToNma.link nma` by definition, H4 is a direct
instance of the generic link-shift identity. No state bijection. -/

/-- **H4 hop** (program equivalence). Instance of
`VCVio.HeapSSP.Package.run_link_eq_run_shiftLeft` at
`P = cmaToNma`, `Q = nma`. -/
theorem cmaSim_run_eq_nma_run_shiftLeft_cmaToNma
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {α : Type}
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) :
    (cmaSim M Commit Chal hr simT).run A =
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).run
        ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A) :=
  VCVio.HeapSSP.Package.run_link_eq_run_shiftLeft _ _ A

/-- **H4 hop** (runProb form), specialising to `runProb`. -/
theorem cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool) :
    (cmaSim M Commit Chal hr simT).runProb A =
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
        ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A) := by
  unfold VCVio.HeapSSP.Package.runProb
  exact cmaSim_run_eq_nma_run_shiftLeft_cmaToNma M Commit Chal hr simT A

end FiatShamir.HeapSSP
