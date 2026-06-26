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

/--
Building one layer of a Merkle tree never results in failure
(no matter what queries have already been made to the oracle before it runs).
-/
@[grind .]
theorem buildLayer_neverFails [DecidableEq α]
    [SampleableType α] [(spec α).DecidableEq]
    (preexisting_cache : (spec α).QueryCache) (n : ℕ)
    (leaves : List.Vector α (2 ^ (n + 1))) : NeverFail
      ((simulateQ (spec α).randomOracle
        (buildLayer α n leaves)).run preexisting_cache) := by
  grind only [buildLayer, = neverFail_iff, = probFailure_of_liftM_PMF]

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
  grind only [= neverFail_iff, = probFailure_of_liftM_PMF]

private lemma buildLayer_with_hash_get_aux {n : ℕ} (leaves : List.Vector α (2 ^ (n + 1)))
    (i : Fin (2 ^ (n + 1))) (hashFn : α × α → α)
    (a b : Fin (2 ^ (n + 1))) (ha : a.val = 2 * (i.val / 2)) (hb : b.val = 2 * (i.val / 2) + 1) :
    hashFn (leaves.get a, leaves.get b) =
      (buildLayer_with_hash (α := α) n leaves hashFn).get ⟨i.val / 2, by grind only⟩ := by
  rw [show a = ⟨2 * (i.val / 2), by omega⟩ from Fin.ext ha,
    show b = ⟨2 * (i.val / 2) + 1, by omega⟩ from Fin.ext hb]
  simp only [buildLayer_with_hash, List.Vector.get_map, List.Vector.get_ofFn]
  congr

/-- A functional completeness theorem for Merkle proofs built from `buildMerkleTree_with_hash`. -/
theorem functional_completeness {n : ℕ} (leaves : List.Vector α (2 ^ n)) (i : Fin (2 ^ n))
    (hashFn : α × α → α) :
    getPutativeRoot_with_hash (α := α) i leaves[i]
        (generateProof α i (buildMerkleTree_with_hash (α := α) n leaves hashFn)) hashFn =
      getRoot α (buildMerkleTree_with_hash (α := α) n leaves hashFn) := by
  induction n with
  | zero =>
    simp [Fin.eq_zero i, buildMerkleTree_with_hash, getPutativeRoot_with_hash, getRoot]
  | succ n ih =>
    let lastLayer := buildLayer_with_hash (α := α) n leaves hashFn
    by_cases hsign : i.val % 2 = 0
    · have hnew := buildLayer_with_hash_get_aux α leaves i hashFn i (siblingIndex i)
        (by omega) (by grind [siblingIndex])
      simp [buildMerkleTree_with_hash, generateProof,
        getPutativeRoot_with_hash, getRoot, hsign, hnew]
      simpa [getRoot, Cache.cons, lastLayer] using
        ih (leaves := lastLayer) (i := ⟨i.val / 2, by grind only⟩)
    · have hnew := buildLayer_with_hash_get_aux α leaves i hashFn (siblingIndex i) i
        (by grind [siblingIndex]) (by omega)
      simp [buildMerkleTree_with_hash, generateProof,
        getPutativeRoot_with_hash, getRoot, hsign, hnew]
      simpa [getRoot, Cache.cons, lastLayer] using
        ih (leaves := lastLayer) (i := ⟨i.val / 2, by grind only⟩)

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
  simp only [evalWithAnswerFn, verifyProof, simulateQ_bind, simulateQ_pure,
    simulateQ_buildMerkleTree_eq, simulateQ_getPutativeRoot_eq]
  change ((_ : α) == _) = true
  exact beq_iff_eq.mpr (functional_completeness α leaves i f)

end MerkleTree
