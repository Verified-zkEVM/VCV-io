/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Games
import VCVio.StateSeparating.CellRef
import Mathlib.Data.Real.ENatENNReal

/-!
# Structural Facts for the HeapSSP Fiat-Shamir CMA Games

This file collects reusable heap facts about the CMA packages: typed references
to important cells, preservation facts for cells that handlers do not write, and
basic random-oracle cache growth bounds.

The statements here are deliberately package-local and theorem-facing. They are
small enough to use directly from hop proofs, but independent of any particular
hybrid argument.
-/

universe u

open ENNReal OracleSpec OracleComp ProbComp VCVio.StateSeparating

namespace FiatShamir.HeapSSP

variable (M : Type) [DecidableEq M]
variable (Commit : Type) [DecidableEq Commit]
variable (Chal : Type) [SampleableType Chal]
variable {Stmt Wit : Type} {rel : Stmt → Wit → Bool}
variable {Resp PrvState : Type}

/-! ## Cell references -/

/-- Reference to the CMA signing-log cell. -/
@[reducible] def cmaLogRef :
    CellRef (CmaCells M Commit Chal Stmt Wit) :=
  ⟨Sum.inl .log⟩

/-- Reference to the CMA random-oracle cache cell. -/
@[reducible] def cmaRoCacheRef :
    CellRef (CmaCells M Commit Chal Stmt Wit) :=
  ⟨Sum.inr .roCache⟩

/-- Reference to the CMA cached-keypair cell. -/
@[reducible] def cmaKeypairRef :
    CellRef (CmaCells M Commit Chal Stmt Wit) :=
  ⟨Sum.inr .keypair⟩

/-- Reference to the CMA bad-flag cell. -/
@[reducible] def cmaBadRef :
    CellRef (CmaCells M Commit Chal Stmt Wit) :=
  ⟨Sum.inr .bad⟩

/-! ## Query classes -/

/-- A CMA query is costly for H3 exactly when it targets the signing oracle. -/
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

/-- A CMA query is a hash query exactly when it targets the random oracle. -/
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

/-! ## Random-oracle cache counts -/

/-- Size of a random-oracle cache as an `ENNReal`.

Finite caches get their ordinary cardinality; infinite graphs map to `⊤`.
-/
noncomputable def cacheCount {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal : Type}
    (cache : (roSpec M Commit Chal).QueryCache) : ℝ≥0∞ :=
  (cache.toSet.encard : ℝ≥0∞)

/-- The empty random-oracle cache has no entries. -/
lemma cacheCount_empty {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal : Type} :
    cacheCount (∅ : (roSpec M Commit Chal).QueryCache) = 0 := by
  simp [cacheCount, QueryCache.toSet_empty]

/-- Adding one cache entry increases `cacheCount` by at most one. -/
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

/-! ## `cmaReal` frame facts -/

/-- Per-query write footprint of `cmaReal.impl`.

Uniform queries write no cells, random-oracle queries may write `.roCache`,
signing queries may write `.keypair`, `.roCache`, and `.log`, and public-key
queries may write `.keypair`. -/
def cmaRealWrites :
    (cmaSpec M Commit Chal Resp Stmt).Domain → Set (CmaCells M Commit Chal Stmt Wit)
  | Sum.inl (Sum.inl (Sum.inl _)) => ∅
  | Sum.inl (Sum.inl (Sum.inr _)) => {Sum.inr .roCache}
  | Sum.inl (Sum.inr _) => {Sum.inr .keypair, Sum.inr .roCache, Sum.inl .log}
  | Sum.inr _ => {Sum.inr .keypair}

/-- One step of `cmaReal.impl` writes only the cells listed in
`cmaRealWrites`. -/
theorem cmaReal_impl_writesOnlyCells
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl.WritesOnlyCells
      ((cmaReal M Commit Chal σ hr).impl)
      (cmaRealWrites (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) (Wit := Wit)) := by
  intro t r hr_not h z hz
  rcases t with ((n | mc) | m) | ⟨⟩ <;>
    simp only [cmaReal, StateT.run_mk] at hz
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
      exists_prop] at hz
    obtain ⟨_, _, rfl⟩ := hz
    rfl
  · rcases hcache : h (Sum.inr .roCache) mc with _ | r₀
    · rw [hcache] at hz
      simp only [support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨_, _, rfl⟩ := hz
      have hne : r.id ≠ (Sum.inr .roCache : CmaCells M Commit Chal Stmt Wit) := by
        intro heq
        exact hr_not (by simp [cmaRealWrites, heq])
      simp [CellRef.get, hne]
    · rw [hcache] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rfl
  · rcases hkp : h (Sum.inr .keypair) with _ | ⟨pk₀, sk₀⟩
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
        have hne_keypair :
            r.id ≠ (Sum.inr .keypair : CmaCells M Commit Chal Stmt Wit) := by
          intro heq
          exact hr_not (by simp [cmaRealWrites, heq])
        have hne_roCache :
            r.id ≠ (Sum.inr .roCache : CmaCells M Commit Chal Stmt Wit) := by
          intro heq
          exact hr_not (by simp [cmaRealWrites, heq])
        have hne_log :
            r.id ≠ (Sum.inl .log : CmaCells M Commit Chal Stmt Wit) := by
          intro heq
          exact hr_not (by simp [cmaRealWrites, heq])
        simp [CellRef.get, hh₁, hne_keypair, hne_roCache, hne_log]
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨π, _, rfl⟩ := h_rest
        have hne_keypair :
            r.id ≠ (Sum.inr .keypair : CmaCells M Commit Chal Stmt Wit) := by
          intro heq
          exact hr_not (by simp [cmaRealWrites, heq])
        have hne_log :
            r.id ≠ (Sum.inl .log : CmaCells M Commit Chal Stmt Wit) := by
          intro heq
          exact hr_not (by simp [cmaRealWrites, heq])
        simp [CellRef.get, hh₁, hne_keypair, hne_log]
    · rw [hkp] at hz
      simp only [pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
      obtain ⟨⟨c, prvSt⟩, _, h_rest⟩ := hz
      rcases hcache : h (Sum.inr .roCache) (m, c) with _ | ch₀
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨ch, _, π, _, rfl⟩ := h_rest
        have hne_roCache :
            r.id ≠ (Sum.inr .roCache : CmaCells M Commit Chal Stmt Wit) := by
          intro heq
          exact hr_not (by simp [cmaRealWrites, heq])
        have hne_log :
            r.id ≠ (Sum.inl .log : CmaCells M Commit Chal Stmt Wit) := by
          intro heq
          exact hr_not (by simp [cmaRealWrites, heq])
        simp [CellRef.get, hne_roCache, hne_log]
      · rw [hcache] at h_rest
        simp only [support_bind, Set.mem_iUnion, exists_prop,
          support_pure, Set.mem_singleton_iff] at h_rest
        obtain ⟨π, _, rfl⟩ := h_rest
        have hne_log :
            r.id ≠ (Sum.inl .log : CmaCells M Commit Chal Stmt Wit) := by
          intro heq
          exact hr_not (by simp [cmaRealWrites, heq])
        simp [CellRef.get, hne_log]
  · rcases hkp : h (Sum.inr .keypair) with _ | ⟨pk₀, sk₀⟩
    · rw [hkp] at hz
      simp only [support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨_, _, rfl⟩ := hz
      have hne_keypair :
          r.id ≠ (Sum.inr .keypair : CmaCells M Commit Chal Stmt Wit) := by
        intro heq
        exact hr_not (by simp [cmaRealWrites, heq])
      simp [CellRef.get, hne_keypair]
    · rw [hkp] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rfl

/-- Cell-write footprint summary for `cmaReal.impl`. -/
def cmaReal_impl_footprint
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl.CellWriteFootprint ((cmaReal M Commit Chal σ hr).impl) where
  writes := cmaRealWrites (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
  sound := cmaReal_impl_writesOnlyCells M Commit Chal σ hr

/-- On a signing or random-oracle query, one `cmaReal.impl` step grows the
random-oracle cache by at most one entry. -/
theorem cmaReal_impl_roCacheCount_le_of_costly_or_hash
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

/-- On queries that are neither signing nor random-oracle queries, one
`cmaReal.impl` step does not grow the random-oracle cache. -/
theorem cmaReal_impl_roCacheCount_le_of_not_costly_not_hash
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

/-- One step of `cmaReal.impl` preserves the bad flag. -/
theorem cmaReal_impl_preserves_badCell
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (z) (hz : z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run h)) :
    (cmaBadRef M Commit Chal).get z.2 = (cmaBadRef M Commit Chal).get h := by
  exact (cmaReal_impl_footprint M Commit Chal σ hr).sound t
    (cmaBadRef M Commit Chal) (by
      rcases t with ((n | mc) | m) | ⟨⟩ <;>
        simp [cmaReal_impl_footprint, cmaRealWrites])
    h z hz

/-- Handler-level form of bad-flag preservation for `cmaReal.impl`. -/
theorem cmaReal_impl_preserves_badRef
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl.PreservesCell
      ((cmaReal M Commit Chal σ hr).impl)
      (cmaBadRef M Commit Chal) := by
  intro t h z hz
  exact cmaReal_impl_preserves_badCell M Commit Chal σ hr t h z hz

/-- Once `cmaReal` has sampled a keypair, a single handler step preserves
that exact keypair. -/
theorem cmaReal_impl_preserves_keypair_some
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (pk : Stmt) (sk : Wit)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (hh : h (Sum.inr .keypair) = some (pk, sk))
    (z) (hz : z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run h)) :
    z.2 (Sum.inr .keypair) = some (pk, sk) := by
  rcases t with ((n | mc) | m) | ⟨⟩
  · simp only [cmaReal, StateT.run_mk, support_bind, Set.mem_iUnion,
      support_pure, Set.mem_singleton_iff, exists_prop] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hh
  · simp only [cmaReal, StateT.run_mk] at hz
    rcases hcache : h (Sum.inr .roCache) mc with _ | r₀
    · rw [hcache] at hz
      simp only [support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨r, _, rfl⟩ := hz
      simp [Heap.update, hh]
    · rw [hcache] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hh
  · simp only [cmaReal, StateT.run_mk] at hz
    rw [hh] at hz
    simp only [pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨⟨c, prvSt⟩, _, h_rest⟩ := hz
    rcases hcache : h (Sum.inr .roCache) (m, c) with _ | ch₀
    · rw [hcache] at h_rest
      simp only [support_bind, Set.mem_iUnion, exists_prop, support_pure,
        Set.mem_singleton_iff] at h_rest
      obtain ⟨ch, _, π, _, rfl⟩ := h_rest
      simp [Heap.update, hh]
    · rw [hcache] at h_rest
      simp only [support_bind, Set.mem_iUnion, exists_prop, support_pure,
        Set.mem_singleton_iff] at h_rest
      obtain ⟨π, _, rfl⟩ := h_rest
      simp [Heap.update, hh]
  · simp only [cmaReal, StateT.run_mk] at hz
    rw [hh] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hh

end FiatShamir.HeapSSP
