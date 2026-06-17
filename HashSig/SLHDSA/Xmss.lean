/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Wots

/-!
# Merkle trees and XMSS (FIPS 205 §6)

A small generic binary-Merkle-tree theory (`SLHDSA.Merkle`) parameterized by a leaf-value
function and a position-indexed node hash, with the auth-path consistency lemma
`Merkle.climb_authPath`: climbing from an honest leaf along the honest authentication path
reconstructs the subtree root. This is the deterministic Merkle core reused by both XMSS
(here) and FORS (`HashSig.SLHDSA.Fors`).

On top of it, XMSS (`xmssNode`, `xmssSign`, `xmssPkFromSig`; Algorithms 9–11) instantiates the
leaves with WOTS+ public keys, and `xmssPkFromSig_xmssSign` derives XMSS correctness from
`Merkle.climb_authPath` together with WOTS+ correctness (`wotsPkFromSig_wotsSign`).

## References

- NIST FIPS 205, §6 (Algorithms 9–11)
-/


namespace SLHDSA.Merkle

variable {Y : Type}

/-- The root of a perfect binary subtree of height `z` rooted at index `t`, over a leaf-value
function `leaf` and a position-indexed node hash `nodeHash height index left right`. -/
def merkleRoot (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) : ℕ → ℕ → Y
  | 0, t => leaf t
  | z + 1, t =>
      nodeHash (z + 1) t (merkleRoot leaf nodeHash z (2 * t))
        (merkleRoot leaf nodeHash z (2 * t + 1))

/-- The index of the sibling of node `i` (flip the last bit, written without `xor`). -/
def sibling (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

/-- The authentication path for leaf `idx` over `z` levels, starting at height `base`:
the level-`j` entry is the subtree root of the sibling on the path. -/
def authPath (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (base idx z : ℕ) : List Y :=
  (List.range z).map (fun j => merkleRoot leaf nodeHash (base + j) (sibling (idx / 2 ^ j)))

/-- Climb an authentication path: starting from `node` at position `(base, idx)`, fold each
sibling in (left/right by the parity of the running index) to reconstruct an ancestor. -/
def climb (nodeHash : ℕ → ℕ → Y → Y → Y) (base idx : ℕ) (node : Y) : List Y → Y
  | [] => node
  | a :: auth =>
      climb nodeHash (base + 1) (idx / 2)
        (if idx % 2 = 0 then nodeHash (base + 1) (idx / 2) node a
         else nodeHash (base + 1) (idx / 2) a node) auth

/-- Folding the honest leaf's sibling in reproduces the parent subtree root. -/
private theorem combined_eq (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) (base idx : ℕ) :
    (if idx % 2 = 0
      then nodeHash (base + 1) (idx / 2) (merkleRoot leaf nodeHash base idx)
            (merkleRoot leaf nodeHash base (sibling idx))
      else nodeHash (base + 1) (idx / 2) (merkleRoot leaf nodeHash base (sibling idx))
            (merkleRoot leaf nodeHash base idx))
      = merkleRoot leaf nodeHash (base + 1) (idx / 2) := by
  have hdm := Nat.div_add_mod idx 2
  change _ = nodeHash (base + 1) (idx / 2) (merkleRoot leaf nodeHash base (2 * (idx / 2)))
            (merkleRoot leaf nodeHash base (2 * (idx / 2) + 1))
  by_cases h : idx % 2 = 0
  · rw [if_pos h, sibling, if_pos h]
    have h1 : 2 * (idx / 2) = idx := by omega
    rw [h1]
  · rw [if_neg h, sibling, if_neg h]
    have h2 : 2 * (idx / 2) = idx - 1 := by omega
    have h3 : 2 * (idx / 2) + 1 = idx := by omega
    rw [h3, h2]

/-- **Merkle auth-path consistency.** Climbing the honest authentication path of leaf `idx`
from its honest subtree root reconstructs the height-`(base+z)` ancestor root. -/
theorem climb_authPath (leaf : ℕ → Y) (nodeHash : ℕ → ℕ → Y → Y → Y) :
    ∀ (z base idx : ℕ),
      climb nodeHash base idx (merkleRoot leaf nodeHash base idx)
          (authPath leaf nodeHash base idx z)
        = merkleRoot leaf nodeHash (base + z) (idx / 2 ^ z) := by
  intro z
  induction z with
  | zero =>
    intro base idx
    simp only [authPath, List.range_zero, List.map_nil, climb, Nat.add_zero, pow_zero,
      Nat.div_one]
  | succ z ih =>
    intro base idx
    have hauth : authPath leaf nodeHash base idx (z + 1)
        = merkleRoot leaf nodeHash base (sibling idx)
          :: authPath leaf nodeHash (base + 1) (idx / 2) z := by
      simp only [authPath, List.range_succ_eq_map, List.map_cons, List.map_map, pow_zero,
        Nat.div_one, Nat.add_zero]
      refine congrArg _ (List.map_congr_left fun j _ => ?_)
      simp only [Function.comp_apply]
      have hb : base + (j + 1) = base + 1 + j := by omega
      have hd : idx / 2 ^ (j + 1) = idx / 2 / 2 ^ j := by
        rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
      rw [hb, hd]
    rw [hauth, climb, combined_eq, ih (base + 1) (idx / 2)]
    congr 1
    · omega
    · rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

end SLHDSA.Merkle

namespace SLHDSA

variable {p : Params}

/-! ### XMSS over WOTS+ leaves (FIPS 205 §6) -/

/-- Base WOTS+ address for the leaf at keypair index `t` (type `WOTS_HASH`). -/
def wotsLeafAdrs (adrs : Adrs) (t : ℕ) : Adrs :=
  (adrs.setTypeAndClear .wotsHash).setKeyPairAddress t

/-- The XMSS leaf value at index `t`: the WOTS+ public key of keypair `t`. -/
def xmssLeaf (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (t : ℕ) : prims.Y :=
  wotsPkGen prims sk pk (wotsLeafAdrs adrs t)

/-- The XMSS internal-node hash at tree position `(height z, index t)` (type `TREE`). -/
def xmssNodeHash (prims : Primitives p) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) : prims.Y :=
  prims.H pk (((adrs.setTypeAndClear .tree).setTreeHeight z).setTreeIndex t) l r

/-- The XMSS subtree root at `(height z, index t)` (FIPS 205 Algorithm 9). -/
def xmssNode (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) : prims.Y :=
  Merkle.merkleRoot (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) z t

/-- The XMSS tree root (height `h'`, index `0`) — the value committed by key generation. -/
def xmssRoot (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  xmssNode prims sk pk adrs p.hp 0

/-- An XMSS signature: a WOTS+ signature of the leaf message paired with the authentication
path (`h'` sibling nodes). -/
abbrev XmssSig (p : Params) (prims : Primitives p) := WotsSig p prims × List prims.Y

/-- XMSS signing (FIPS 205 Algorithm 10): WOTS+-sign at leaf `idx` and emit the auth path. -/
def xmssSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) : XmssSig p prims :=
  (wotsSign prims msg sk pk (wotsLeafAdrs adrs idx),
    Merkle.authPath (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) 0 idx p.hp)

/-- XMSS root recovery from a signature (FIPS 205 Algorithm 11): recover the WOTS+ public key
(the leaf) then climb the auth path. -/
def xmssPkFromSig (prims : Primitives p) (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  Merkle.climb (xmssNodeHash prims pk adrs) 0 idx
    (wotsPkFromSig prims sig.1 msg pk (wotsLeafAdrs adrs idx)) sig.2

/-- **XMSS correctness** (FIPS 205, Algorithms 9–11): root recovery from an honest signature at
leaf `idx < 2^{h'}` reproduces the XMSS tree root. Composes WOTS+ correctness with the Merkle
auth-path consistency lemma. -/
theorem xmssPkFromSig_xmssSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp) :
    xmssPkFromSig prims idx (xmssSign prims msg sk pk adrs idx) msg pk adrs
      = xmssRoot prims sk pk adrs := by
  unfold xmssPkFromSig xmssSign xmssRoot xmssNode
  dsimp only
  rw [wotsPkFromSig_wotsSign]
  have key := Merkle.climb_authPath (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs)
    p.hp 0 idx
  rw [Nat.zero_add, Nat.div_eq_of_lt hidx] at key
  exact key

end SLHDSA
