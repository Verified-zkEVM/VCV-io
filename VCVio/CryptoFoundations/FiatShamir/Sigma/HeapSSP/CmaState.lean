/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Spec
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.HeapSSP.CellRef
import VCVio.HeapSSP.Heap
import Mathlib.Data.Real.ENatENNReal

/-!
# CMA state for the HeapSSP Fiat-Shamir proof

This file contains the state interface for the HeapSSP CMA games. The
mathematical state is the four-field record `CmaState`: signed-message log,
random-oracle cache, optional keypair, and the bad flag used by the
simulator-programming hop.

The existing `HeapSSP.Package` API stores state as `Heap Ident`, so the file
also provides the small cell directories used to realize the record fields in
packages. Keeping these names here, rather than in `Spec.lean`, prevents the
oracle interface layer from carrying proof-state details.
-/

open ENNReal OracleSpec VCVio.HeapSSP

namespace FiatShamir.HeapSSP

/-- Record view of the CMA state used in the textbook proof narrative. -/
structure CmaState (M Commit Chal Stmt Wit : Type) where
  signed : List M
  roCache : (roSpec M Commit Chal).QueryCache
  keypair : Option (Stmt × Wit)
  bad : Bool

namespace CmaState

/-- Empty initial CMA state. -/
def empty (M Commit Chal Stmt Wit : Type) : CmaState M Commit Chal Stmt Wit where
  signed := []
  roCache := ∅
  keypair := none
  bad := false

end CmaState

/-! ## Heap-backed package cells -/

/-- Outer cell directory for `cmaToNma`: the adversary-visible signed-message log. -/
inductive OuterCell (M : Type) where
  | log

instance (M : Type) : DecidableEq (OuterCell M) := fun a b =>
  match a, b with
  | .log, .log => .isTrue rfl

instance (M : Type) : VCVio.HeapSSP.CellSpec.{0, 0} (OuterCell M) where
  type
    | .log => List M
  default
    | .log => []

/-- Inner cell directory for `nma`: RO cache, optional keypair, and bad flag. -/
inductive InnerCell (M Commit Chal Stmt Wit : Type) where
  | roCache
  | keypair
  | bad

instance (M Commit Chal Stmt Wit : Type) :
    DecidableEq (InnerCell M Commit Chal Stmt Wit) := fun a b =>
  match a, b with
  | .roCache, .roCache => .isTrue rfl
  | .keypair, .keypair => .isTrue rfl
  | .bad, .bad => .isTrue rfl
  | .roCache, .keypair => .isFalse (fun h => by cases h)
  | .roCache, .bad => .isFalse (fun h => by cases h)
  | .keypair, .roCache => .isFalse (fun h => by cases h)
  | .keypair, .bad => .isFalse (fun h => by cases h)
  | .bad, .roCache => .isFalse (fun h => by cases h)
  | .bad, .keypair => .isFalse (fun h => by cases h)

instance (M Commit Chal Stmt Wit : Type) :
    VCVio.HeapSSP.CellSpec.{0, 0} (InnerCell M Commit Chal Stmt Wit) where
  type
    | .roCache => (roSpec M Commit Chal).QueryCache
    | .keypair => Option (Stmt × Wit)
    | .bad => Bool
  default
    | .roCache => ∅
    | .keypair => none
    | .bad => false

/-- Composite cell directory shared by the real and simulated CMA packages. -/
abbrev CmaCells (M Commit Chal Stmt Wit : Type) : Type :=
  OuterCell M ⊕ InnerCell M Commit Chal Stmt Wit

variable (M : Type) [DecidableEq M]
variable (Commit : Type) [DecidableEq Commit]
variable (Chal : Type) [SampleableType Chal]
variable {Stmt Wit : Type}
variable {Resp : Type}

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

Finite caches get their ordinary cardinality; infinite graphs map to `⊤`. -/
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

end FiatShamir.HeapSSP
