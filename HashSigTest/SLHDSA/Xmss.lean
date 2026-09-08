/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Xmss

/-!
# Oracle-parametric XMSS canaries

These examples cover distinct observable XMSS contracts: address formation, the encoded node
query, left-to-right subtree evaluation, authentication-path-before-WOTS signing, and
recovery-before-climb verification.
-/

public section

namespace SLHDSA.XmssTest

open OracleComp

variable {p : Params} (core : CorePrimitives p)

example : wotsLeafAdrs ((Adrs.zero.setLayerAddress 7).setTreeAddress 9) 3 =
    { layer := 7, tree := 9, type := 0, word1 := 3, word2 := 0, word3 := 0 } := rfl

example : xmssNodeAdrs ((Adrs.zero.setLayerAddress 7).setTreeAddress 9) 4 6 =
    { layer := 7, tree := 9, type := 2, word1 := 0, word2 := 4, word3 := 6 } := rfl

/-- Height one evaluates the left leaf, then the right leaf, then hashes the ordered pair at the
parent's `TREE` address. -/
example (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    (xmssNodeM core sk pk adrs 1 t : OracleComp (publicHashSpec core) core.Y) = (do
      let left ← xmssLeafM core sk pk adrs (2 * t)
      let right ← xmssLeafM core sk pk adrs (2 * t + 1)
      xmssNodeHashM core pk adrs 1 t left right) := rfl

/-- The ordered children and exact encoded `TREE` address are part of the single public-hash
query identity. -/
example (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) (left right : core.Y) :
    (xmssNodeHashM core pk adrs z t left right :
      OracleComp (publicHashSpec core) core.Y) =
    query (spec := publicHashSpec core)
      (.thash pk (core.adrsToKey (xmssNodeAdrs adrs z t)) [left, right]) := rfl

/-- FIPS 205 Algorithm 10 computes the sibling-only authentication path before the WOTS+
signature. -/
example (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    (xmssSignM core msg sk pk adrs idx :
      OracleComp (publicHashSpec core) (XmssSig p core)) = (do
      let path ← PerfectMerkleTree.intrinsicAuthPathM (xmssLeafM core sk pk adrs)
        (xmssNodeHashM core pk adrs) idx p.hp
      let sig ← wotsSignM core msg sk pk (wotsLeafAdrs adrs idx)
      return XmssSigCore.mk sig path) := rfl

/-- Recovery computes the WOTS+ leaf before climbing the leaf-first authentication path. -/
example (idx : ℕ) (sig : XmssSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    (xmssPkFromSigM core idx sig msg pk adrs :
      OracleComp (publicHashSpec core) core.Y) = (do
      let leaf ← wotsPkFromSigM core sig.wots msg pk (wotsLeafAdrs adrs idx)
      PerfectMerkleTree.climbM (xmssNodeHashM core pk adrs) idx leaf sig.auth.toList) := rfl

/-- The two XMSS signature components are intrinsically fixed: no malformed WOTS+ or
authentication-path length can inhabit the internal representation. -/
example (sig : XmssSigCore p core) :
    sig.wots.toList.length = p.len ∧ sig.auth.toList.length = p.hp := by
  simp

end SLHDSA.XmssTest
