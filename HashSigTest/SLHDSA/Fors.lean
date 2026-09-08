/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Fors

/-!
# Oracle-parametric FORS canaries

These examples cover the three distinct top-level FORS schedules: public-key generation, signing,
and recovery.  They pin tree order, sibling-only authentication paths, omission of a selected-leaf
hash during signing, and final `T_k` compression.
-/

public section

namespace SLHDSA.ForsTest

open OracleComp

variable {p : Params} (prims : Primitives p)

/-- Public-key generation computes roots in increasing `Fin k` order and compresses only after
the complete root vector is available. -/
example (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkGenM prims.core sk pk adrs = (do
      let roots ← Vector.ofFnM fun i : Fin p.k =>
        forsRootM prims.core sk pk adrs i.val
      PublicHash.tl prims.core pk (forsPkAdrs adrs) roots.toList :
      OracleComp (publicHashSpec prims.core) prims.Y) := rfl

/-- Signing processes trees in increasing order. For each selected leaf it evaluates only the
sibling-only authentication path and returns the raw secret; there is no selected-leaf `F` call. -/
example (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    forsSignM prims.core md sk pk adrs =
      (Vector.ofFnM fun i : Fin p.k => do
        let idx := i.val * 2 ^ p.a + forsIdx p md i.val
        let path ← PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWith prims.core (PublicHash.f prims.core pk) sk pk adrs)
          (forsNodeHashWith (PublicHash.h prims.core pk) adrs) idx p.a
        return ForsTreeSigCore.mk (forsSkGenCore prims.core sk pk adrs idx) path :
        OracleComp (publicHashSpec prims.core) (ForsSigCore p prims.core)) := rfl

/-- Recovery performs one `F`, then a leaf-to-root climb, per tree in increasing order, followed
by the final `T_k` compression. -/
example (sig : ForsSigCore p prims.core) (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkFromSigM prims.core sig md pk adrs = (do
      let roots ← Vector.ofFnM fun i : Fin p.k => do
        let idx := i.val * 2 ^ p.a + forsIdx p md i.val
        let leaf ← PublicHash.f prims.core pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk
        PerfectMerkleTree.climbM
          (forsNodeHashWith (PublicHash.h prims.core pk) adrs) idx leaf (sig[i.val]).auth.toList
      PublicHash.tl prims.core pk (forsPkAdrs adrs) roots.toList :
      OracleComp (publicHashSpec prims.core) prims.Y) := rfl

/-- The forest and every tree path have their FIPS lengths in the type, so replacing either
vector by a differently sized path is rejected before recovery can run. -/
example (sig : ForsSigCore p prims.core) :
    sig.toList.length = p.k ∧ ∀ i : Fin p.k, (sig[i.val]).auth.toList.length = p.a := by
  simp

end SLHDSA.ForsTest
