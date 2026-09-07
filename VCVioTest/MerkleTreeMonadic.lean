/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic

/-!
# Effectful addressed-Merkle canaries

The noncommutative trace distinguishes leaf production from ordered node hashing. The examples
cover traversal and child order, mixed authentication paths, global subtree addressing,
and the height-zero boundary.
-/

public section

namespace VCVioTest.MerkleTreeMonadicCanary

open _root_.PerfectMerkleTree

inductive Event where
  | leaf (index : ℕ)
  | node (height index left right : ℕ)
deriving DecidableEq, Repr

abbrev TraceM := StateM (List Event)

def leafM (index : ℕ) : TraceM ℕ := fun trace =>
  (index + 1, trace ++ [.leaf index])

/-- Address-sensitive and noncommutative, matching `PerfectMerkleTreeCanary.orderedHash`. -/
def nodeM (height index left right : ℕ) : TraceM ℕ := fun trace =>
  (1000 * height + 100 * index + 10 * left + right,
    trace ++ [.node height index left right])

/-- Tree construction is left subtree, right subtree, then parent. -/
example : Id.run ((merkleRootM leafM nodeM 2 0).run []) =
    (13254,
      [.leaf 0, .leaf 1, .node 1 0 1 2,
       .leaf 2, .leaf 3, .node 1 1 3 4,
       .node 2 0 1012 1134]) := by
  decide

/-- A mixed path takes the left branch at the bottom and the right branch above it. -/
example : Id.run ((authPathM leafM nodeM 2 2).run []) =
    ([4, 1012],
      [.leaf 3, .leaf 0, .leaf 1, .node 1 0 1 2]) := by
  decide

/-- Root recovery follows the corresponding mixed left/right path. -/
example : Id.run ((climbM nodeM 2 3 [4, 1012]).run []) =
    (13254, [.node 1 1 3 4, .node 2 0 1012 1134]) := by
  decide

/-- Authentication-path construction retains global addresses in a nonzero height-two subtree. -/
example : Id.run ((authPathM leafM nodeM 6 2).run []) =
    ([8, 1256],
      [.leaf 7, .leaf 4, .leaf 5, .node 1 2 5 6]) := by
  decide

/-- Root recovery retains global addresses in a nonzero height-two subtree. -/
example : Id.run ((climbM nodeM 6 7 [8, 1256]).run []) =
    (16038, [.node 1 3 7 8, .node 2 1 1256 1378]) := by
  decide

/-- Height zero performs exactly one leaf effect and no node hashes. -/
example : Id.run ((merkleRootM leafM nodeM 0 7).run []) = (8, [.leaf 7]) := by
  decide

/-- Height-zero paths and climbs are effect-free. -/
example :
    Id.run ((authPathM leafM nodeM 7 0).run []) = ([], []) ∧
    Id.run ((climbM nodeM 7 8 []).run []) = (8, []) := by
  decide

end VCVioTest.MerkleTreeMonadicCanary
