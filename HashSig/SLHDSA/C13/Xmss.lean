/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.C13.WotsC
import HashSig.SLHDSA.Xmss

/-!
# C13 XMSS layer (XMSS over WOTS+C)

A single XMSS Merkle tree (height `h' = 11`) whose leaves are **WOTS+C** public keys, reusing the
generic `SLHDSA.Merkle` core and `SLHDSA.C13.WotsC`. An XMSS+C signature carries the WOTS+C
signature, its grinding **counter**, and the authentication path. `xmssPkFromSig` reproduces the
tree root on an honest signature (`xmssPkFromSig_xmssSign`), composing WOTS+C correctness with
the Merkle auth-path consistency lemma.

## References

- NIST FIPS 205 §6 (XMSS); ePrint 2025/2203 (the C-series leaf OTS)
-/


namespace SLHDSA.C13

open SLHDSA (Adrs)
open SLHDSA.Merkle

/-- Base WOTS+C address for the leaf at keypair index `t` (type `WOTS_HASH`). -/
def wotsLeafAdrs (adrs : Adrs) (t : ℕ) : Adrs :=
  (adrs.setTypeAndClear .wotsHash).setKeyPairAddress t

/-- The XMSS leaf value at index `t`: the WOTS+C public key of keypair `t`. -/
def xmssLeaf (prims : Primitives) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (t : ℕ) : prims.Y :=
  wotsPkGen prims sk pk (wotsLeafAdrs adrs t)

/-- The XMSS internal-node hash at `(height z, index t)` (type `TREE`). -/
def xmssNodeHash (prims : Primitives) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) : prims.Y :=
  prims.H pk (((adrs.setTypeAndClear .tree).setTreeHeight z).setTreeIndex t) l r

/-- The XMSS subtree root at `(height z, index t)`. -/
def xmssNode (prims : Primitives) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) : prims.Y :=
  merkleRoot (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) z t

/-- The XMSS tree root (height `h'`, index `0`). -/
def xmssRoot (prims : Primitives) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  xmssNode prims sk pk adrs params.hp 0

/-- An XMSS+C signature: a WOTS+C signature, its grinding counter, and the auth path. -/
abbrev XmssSig (prims : Primitives) := WotsSig prims × ℕ × List prims.Y

/-- XMSS+C signing at leaf `idx` with WOTS+C counter `count`. -/
def xmssSign (prims : Primitives) (node : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx count : ℕ) : XmssSig prims :=
  (wotsSign prims node sk pk (wotsLeafAdrs adrs idx) count, count,
    authPath (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) 0 idx params.hp)

/-- XMSS+C root recovery: recover the WOTS+C public key (the leaf), then climb the auth path. -/
def xmssPkFromSig (prims : Primitives) (idx : ℕ) (sig : XmssSig prims) (node : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  climb (xmssNodeHash prims pk adrs) 0 idx
    (wotsPkFromSig prims sig.1 node pk (wotsLeafAdrs adrs idx) sig.2.1) sig.2.2

/-- **XMSS+C correctness**: root recovery from an honest signature at leaf `idx < 2^{h'}`
reproduces the XMSS tree root. -/
theorem xmssPkFromSig_xmssSign (prims : Primitives) (node : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx count : ℕ) (hidx : idx < 2 ^ params.hp) :
    xmssPkFromSig prims idx (xmssSign prims node sk pk adrs idx count) node pk adrs
      = xmssRoot prims sk pk adrs := by
  unfold xmssPkFromSig xmssSign xmssRoot xmssNode
  dsimp only
  rw [wotsPkFromSig_wotsSign]
  have key := climb_authPath (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs)
    params.hp 0 idx
  rw [Nat.zero_add, Nat.div_eq_of_lt hidx] at key
  exact key

end SLHDSA.C13
