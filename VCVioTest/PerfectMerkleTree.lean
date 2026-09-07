/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed

/-!
# Perfect Addressed-Merkle Canaries

Concrete examples pin the public behavior of the natural-number adapter over
`AddressedMerkleTree`: global subtree indexing, left/right hash order, authentication-path order,
root reconstruction, and oriented collision extraction. The hashes are deliberately
noncommutative or collision-heavy so that an address, order, or endpoint regression is visible.
-/

public section

namespace VCVioTest.PerfectMerkleTreeCanary

open _root_.PerfectMerkleTree

def leaf (i : ℕ) : ℕ := i + 1

/-- Address-sensitive and noncommutative in its child inputs. -/
def orderedHash (height index left right : ℕ) : ℕ :=
  1000 * height + 100 * index + 10 * left + right

example : orderedHash 1 0 1 2 = 1012 := rfl

example : orderedHash 1 0 1 2 ≠ orderedHash 1 0 2 1 := by decide

/-- The height-two root uses leaves `0` through `3`, in left-to-right order. -/
example : merkleRoot leaf orderedHash 2 0 = 13254 := rfl

/-- A nonzero subtree index selects the global leaves `4` through `7`. -/
example : merkleRoot leaf orderedHash 2 1 = 16038 := rfl

/-- Authentication paths are leaf-first and preserve the sibling side. -/
example : authPath leaf orderedHash 0 2 = [2, 1134] := rfl

example : authPath leaf orderedHash 1 2 = [1, 1134] := rfl

example : authPath leaf orderedHash 2 2 = [4, 1012] := rfl

example : climb orderedHash 0 (leaf 0) (authPath leaf orderedHash 0 2) = 13254 := rfl

example : climb orderedHash 1 (leaf 1) (authPath leaf orderedHash 1 2) = 13254 := rfl

example : climb orderedHash 2 (leaf 2) (authPath leaf orderedHash 2 2) = 13254 := rfl

/-- Every input pair at one address collides, while different addresses remain distinguishable. -/
def addressOnlyHash (height index _left _right : ℕ) : ℕ :=
  100 * height + index

/-- The adversarial leaf first diverges at node `(height = 1, index = 0)`. The extractor keeps
the honest child pair as its first endpoint. -/
example :
    findCollision leaf addressOnlyHash 0 9 (authPath leaf addressOnlyHash 0 2)
      = some (1, (1, 2), (9, 2)) := by
  decide

end VCVioTest.PerfectMerkleTreeCanary
