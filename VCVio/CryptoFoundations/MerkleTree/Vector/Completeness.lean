/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Fawad Haider
-/

import VCVio.CryptoFoundations.MerkleTree.Vector.Defs
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Completeness of vector Merkle trees

This file proves the completeness theorem for the vector-style Merkle tree
construction defined in `VCVio.CryptoFoundations.MerkleTree.Vector.Defs`:
honestly generated proofs verify against honestly built roots.

The proof is split into two pieces:

* `MerkleTree.functional_completeness` is a purely functional statement about
  `getPutativeRoot_with_hash` and `buildMerkleTree_with_hash`, proven by
  induction on the tree depth.
* `MerkleTree.completeness` lifts the functional statement to the monadic API
  by reducing through `simulateQ` of the random oracle.

The auxiliary `buildLayer_neverFails` and `buildMerkleTree_neverFails` lemmas
record that honest tree construction never fails under the random-oracle
simulation, which the completeness reduction relies on.
-/

namespace MerkleTree

open List OracleSpec OracleComp

variable (α : Type _)

@[grind .]
theorem buildLayer_neverFails [DecidableEq α]
    [SampleableType α] [(spec α).DecidableEq]
    (preexisting_cache : (spec α).QueryCache) (n : ℕ)
    (leaves : List.Vector α (2 ^ (n + 1))) : NeverFail
      ((simulateQ (spec α).randomOracle
        (buildLayer α n leaves)).run preexisting_cache) := by
  grind only [buildLayer, = HasEvalSPMF.neverFail_iff, = HasEvalPMF.probFailure_eq_zero]

/--
Building a Merkle tree never results in failure
(no matter what queries have already been made to the oracle before it runs).
-/
@[grind .]
theorem buildMerkleTree_neverFails [DecidableEq α]
    [SampleableType α] {n : ℕ} [(spec α).DecidableEq]
    (leaves : List.Vector α (2 ^ n)) (preexisting_cache : (spec α).QueryCache) :
    NeverFail
      ((simulateQ (spec α).randomOracle
        (buildMerkleTree α n leaves)).run preexisting_cache) := by
  grind only [= HasEvalSPMF.neverFail_iff, = HasEvalPMF.probFailure_eq_zero]

/-- A functional completeness theorem for Merkle proofs built from `buildMerkleTree_with_hash`. -/
theorem functional_completeness {n : ℕ} (leaves : List.Vector α (2 ^ n)) (i : Fin (2 ^ n))
    (hashFn : α × α → α) :
    getPutativeRoot_with_hash (α := α) i leaves[i]
        (generateProof α i (buildMerkleTree_with_hash (α := α) n leaves hashFn)) hashFn =
      getRoot α (buildMerkleTree_with_hash (α := α) n leaves hashFn) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [buildMerkleTree_with_hash, getPutativeRoot_with_hash, getRoot]
    change List.Vector.get leaves 0 = leaves.head
    exact List.Vector.get_zero leaves
  | succ n ih =>
    -- Abbreviate the upper layer and the upper tree.
    let lastLayer := buildLayer_with_hash (α := α) n leaves hashFn
    let upperCache := buildMerkleTree_with_hash (α := α) n lastLayer hashFn
    -- Split on whether `i` is a left or right child at the bottom layer.
    by_cases hsign : i.val % 2 = 0
    · -- Left child: sibling is `i + 1`.
      have hdiv : 2 * (i.val / 2) = i.val := by
        have h := Nat.mod_add_div i.val 2
        -- `i % 2 = 0` implies `2 * (i / 2) = i`.
        simpa [hsign] using h
      have hright : 2 * (i.val / 2) + 1 = i.val + 1 := by grind only
      have hnew :
          hashFn (leaves.get i, leaves.get (siblingIndex i)) =
            lastLayer.get ⟨i.val / 2, by grind only⟩ := by
          simp [lastLayer, buildLayer_with_hash, siblingIndex, hsign, hdiv]
      -- Unfold and apply the induction hypothesis on the upper tree.
      -- `generateProof` and `getRoot` reduce via `Cache.upper_cons` and `Cache.leaves_cons`.
      simp [buildMerkleTree_with_hash, lastLayer, generateProof,
        getPutativeRoot_with_hash, getRoot, hsign, hnew]
      simpa [getRoot, Cache.cons, lastLayer, upperCache] using
        (ih (leaves := lastLayer) (i := ⟨i.val / 2, by grind only⟩))
    · -- Right child: sibling is `i - 1`.
      have hmod1 : i.val % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one i.val with h0 | h1
        · exact (hsign h0).elim
        · exact h1
      have hdiv : 2 * (i.val / 2) = i.val - 1 := by
        have h := Nat.mod_add_div i.val 2
        -- `i % 2 = 1` implies `1 + 2 * (i / 2) = i`.
        have : 1 + 2 * (i.val / 2) = i.val := by simpa [hmod1] using h
        grind only
      have hright : 2 * (i.val / 2) + 1 = i.val := by grind only
      have hnew :
          hashFn (leaves.get (siblingIndex i), leaves.get i) =
            lastLayer.get ⟨i.val / 2, by grind only⟩ := by
        have hiPos : 1 ≤ i.val := by grind only
        have hi' :
            (⟨i.val - 1 + 1, by simp [Nat.sub_add_cancel hiPos]⟩ :
                Fin (2 ^ (n + 1))) =
              i := by
          ext
          simp [Nat.sub_add_cancel hiPos]
        simpa [lastLayer, buildLayer_with_hash, siblingIndex, hmod1, hdiv] using
          congrArg (fun j => hashFn (leaves.get ⟨i.val - 1, by grind only⟩, leaves.get j)) hi'.symm
      simp [buildMerkleTree_with_hash, lastLayer, generateProof,
        getPutativeRoot_with_hash, getRoot, hsign, hnew]
      simpa [getRoot, Cache.cons, lastLayer, upperCache] using
        (ih (leaves := lastLayer) (i := ⟨i.val / 2, by grind only⟩))

/-- Completeness theorem for Merkle trees: for any full binary tree with `2 ^ n` leaves, and for
  any index `i`, the honestly-generated opening proof verifies against the honestly-built root
  with probability one.
-/
theorem completeness [DecidableEq α] [Inhabited α] [SampleableType α] {n : ℕ}
    [(spec α).DecidableEq]
    (leaves : List.Vector α (2 ^ n)) (i : Fin (2 ^ n))
    (preexisting_cache : (spec α).QueryCache) :
    Pr[fun v => v.1 = true | (simulateQ (spec α).randomOracle (do
      let cache ← buildMerkleTree α n leaves
      let proof := generateProof α i cache
      let verified ← (verifyProof (m := OracleComp (spec α)) α i leaves[i]
        (getRoot α cache) proof)
      return verified)).run preexisting_cache] = 1 := by
  refine (probEvent_eq_one_simulateQ_randomOracle_run_iff (spec := spec α)
    (p := fun b : Bool => b = true) _ _).mpr ?_
  intro f _hf
  -- Reduce simulation through the do-block to a deterministic computation, then apply
  -- `functional_completeness`.
  change (simulateQ f (do
    let cache ← buildMerkleTree α n leaves
    let proof := generateProof α i cache
    let verified ← (verifyProof (m := OracleComp (spec α)) α i leaves[i]
      (getRoot α cache) proof)
    return verified) : Id Bool) = (true : Bool)
  simp only [verifyProof, simulateQ_bind, simulateQ_pure,
    simulateQ_buildMerkleTree_eq, simulateQ_getPutativeRoot_eq]
  change ((_ : α) == _) = true
  rw [beq_iff_eq]
  exact functional_completeness α leaves i f

end MerkleTree
