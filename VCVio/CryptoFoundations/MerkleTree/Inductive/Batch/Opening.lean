/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module


public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Map

/-!
# Packaged Batch Merkle Openings

This module provides the neutral dependent package shared by batch verification, single-
commitment extractability, and stateful multi-extractability. The selector indexes both payloads,
and the `BatchProof` field itself rules out the empty selector.
-/

@[expose] public section

namespace InductiveMerkleTree

open BinaryTree

universe u v

/-- A nonempty, intrinsically path-pruned batch opening for a fixed Merkle skeleton. -/
structure BatchOpening (Y : Type u) (s : Skeleton) where
  /-- Dense selector for the claimed leaves. -/
  selector : LeafData Bool s
  /-- Claimed values at exactly the selected leaves. -/
  values : SelectedValues Y selector
  /-- Canonical path-pruned authentication frontier. -/
  proof : BatchProof Y selector

/-- Every packaged batch opening selects at least one leaf. -/
theorem BatchOpening.anySelected {Y : Type u} {s : Skeleton} (opening : BatchOpening Y s) :
    opening.selector.anySelected = true :=
  opening.proof.anySelected_of_batchProof

/-- Map every observable value and frontier hash while preserving the dependent selector. -/
def BatchOpening.map {Y : Type u} {Z : Type v} {s : Skeleton}
    (f : Y → Z) (opening : BatchOpening Y s) : BatchOpening Z s where
  selector := opening.selector
  values := opening.values.map f
  proof := opening.proof.map f

@[simp]
theorem BatchOpening.map_selector {Y : Type u} {Z : Type v} {s : Skeleton}
    (f : Y → Z) (opening : BatchOpening Y s) :
    (opening.map f).selector = opening.selector := rfl

@[simp]
theorem BatchOpening.map_id {Y : Type u} {s : Skeleton} (opening : BatchOpening Y s) :
    opening.map id = opening := by
  cases opening
  simp only [BatchOpening.map, SelectedValues.map_id, BatchProof.map_id]

end InductiveMerkleTree
