/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.DepthOneCompatibility

/-!
# General internal-scheme canaries

These equations pin the general Algorithms 18--20 composition boundary: top-layer key generation,
digest-derived FORS addressing, and the arbitrary-`d` hypertree call.

The depth canaries pin type-level widths only. No executable `d > 1` primitive instance exists
in the tree yet, so exact-execution coverage of the general path is deferred to the refinement
and KAT slices; until then the arbitrary-depth guarantees are the symbolic correctness and
query-bound theorems.
-/

public section

namespace SLHDSA.GeneralSchemeTest

open OracleComp

variable (vp : ValidatedParams) (core : CorePrimitives vp.params)

/-! ## Intrinsic depth canaries -/

def depthOneParams : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 1, k := 1, lgw := 1 }

def depthTwoParams : Params :=
  { n := 1, h := 2, d := 2, hp := 1, a := 1, k := 1, lgw := 1 }

def depthThreeParams : Params :=
  { n := 1, h := 3, d := 3, hp := 1, a := 1, k := 1, lgw := 1 }

/-- The depth canaries satisfy the full validity predicate, so they exercise exactly the
parameter class the general theorems quantify over. -/
example : depthOneParams.Valid ∧ depthTwoParams.Valid ∧ depthThreeParams.Valid := by decide

/-- The canonical scheme type carries exactly one XMSS component at the compatibility depth. -/
example (depthOneCore : CorePrimitives depthOneParams)
    (sig : SignatureCore depthOneParams depthOneCore) :
    sig.hypertree.toList.length = 1 := by
  simp [depthOneParams]

/-- The canonical scheme type cannot collapse a two-layer signature to one component. -/
example (depthTwoCore : CorePrimitives depthTwoParams)
    (sig : SignatureCore depthTwoParams depthTwoCore) :
    sig.hypertree.toList.length = 2 := by
  simp [depthTwoParams]

/-- The canonical scheme type retains all three components at depth three. -/
example (depthThreeCore : CorePrimitives depthThreeParams)
    (sig : SignatureCore depthThreeParams depthThreeCore) :
    sig.hypertree.toList.length = 3 := by
  simp [depthThreeParams]

/-- The structured scheme signature carries exactly `d` XMSS signatures. -/
example (sig : GeneralScheme.SignatureCore vp core) :
    sig.hypertree.toArray.size = vp.params.d := sig.hypertree.size_toArray

/-- Algorithm 18 delegates root generation to the top-layer general hypertree. -/
example (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    (GeneralScheme.keygenInternalM vp core skSeed skPrf pkSeed :
      OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core)) = (do
        let pkRoot ← GeneralHypertree.rootM vp core skSeed pkSeed
        return (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)) := by
  rfl

/-- The depth-one key-generation entry point agrees with the general program as an exact
free-oracle equation, so no second unconstrained scheme exists. -/
example (hd : vp.params.d = 1) (skSeed : core.SkSeed) (skPrf : core.SkPrf)
    (pkSeed : core.PkSeed) :
    (GeneralScheme.keygenInternalM vp core skSeed skPrf pkSeed :
      OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core)) =
    (slhKeygenInternalM hd core skSeed skPrf pkSeed :
      OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core)) :=
  DepthOneCompatibility.keygenInternalM_eq_slhKeygenInternalM
    vp core hd skSeed skPrf pkSeed

/-- At depth one, general signing has the compatibility schedule followed by the mandatory
discarded XMSS recovery. Removing that recovery changes this exact free-oracle program. -/
example (hd : vp.params.d = 1) (msg : List Byte) (sk : SecretKeyCore core)
    (addrnd : core.Y) :
    ((do
      let sig ← GeneralScheme.signInternalM vp core msg sk addrnd
      return DepthOneCompatibility.schemeSignatureEquiv vp core hd sig) :
        OracleComp (publicHashSpec core) (SignatureCore vp.params core)) =
      ((do
        let R := core.PRFmsg sk.skPrf addrnd msg
        let digest ← PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg
        let parts := splitDigest vp.params digest
        let forsSig ← forsSignM core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs
        let forsPk ←
          forsPkFromSigM core forsSig parts.md.toList sk.pkSeed parts.forsAdrs
        let htSig ←
          htSignM core hd forsPk sk.skSeed sk.pkSeed Adrs.zero 0 parts.idxLeaf.val
        let _ ←
          htPkFromSigM core hd forsPk htSig sk.pkSeed Adrs.zero 0 parts.idxLeaf.val
        return ⟨R, forsSig, htSig⟩) :
          OracleComp (publicHashSpec core) (SignatureCore vp.params core)) :=
  DepthOneCompatibility.signInternalM_toOneLayer_eq vp core hd msg sk addrnd

/-- Under a fixed public-hash implementation, the discarded recovery leaves the returned
depth-one signature unchanged. -/
example (prims : Primitives vp.params) (hd : vp.params.d = 1)
    (msg : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    DepthOneCompatibility.schemeSignatureEquiv vp prims.core hd
        (GeneralScheme.signInternal vp prims msg sk addrnd) =
      slhSignInternal hd prims msg sk addrnd :=
  DepthOneCompatibility.signInternal_toOneLayer_eq vp prims hd msg sk addrnd

/-- General depth-one verification is exactly the compatibility verification program. -/
example (hd : vp.params.d = 1) [DecidableEq core.Y]
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core)
    (pk : PublicKeyCore core) :
    (GeneralScheme.verifyInternalM vp core msg sig pk :
      OracleComp (publicHashSpec core) Bool) =
    (slhVerifyInternalM hd core msg
      (DepthOneCompatibility.schemeSignatureEquiv vp core hd sig) pk :
        OracleComp (publicHashSpec core) Bool) :=
  DepthOneCompatibility.verifyInternalM_eq_slhVerifyInternalM vp core hd msg sig pk

/-- Algorithm 19 retains every digest output and passes the typed parts to the general
hypertree, rather than resetting the tree address to zero. -/
example (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    (GeneralScheme.signInternalM vp core msg sk addrnd :
      OracleComp (publicHashSpec core) (GeneralScheme.SignatureCore vp core)) = (do
        let R := core.PRFmsg sk.skPrf addrnd msg
        let digest ← PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg
        let parts := splitDigest vp.params digest
        let forsSig ← forsSignM core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs
        let forsPk ←
          forsPkFromSigM core forsSig parts.md.toList sk.pkSeed parts.forsAdrs
        let htSig ← GeneralHypertree.signM vp core forsPk sk.skSeed sk.pkSeed parts
        return ⟨R, forsSig, htSig⟩) := by
  rfl

/-- Algorithm 20 follows the same digest-derived FORS and hypertree schedule. -/
example [DecidableEq core.Y] (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core) :
    (GeneralScheme.verifyInternalM vp core msg sig pk :
      OracleComp (publicHashSpec core) Bool) = (do
        let digest ← PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg
        let parts := splitDigest vp.params digest
        let forsPk ← forsPkFromSigM core sig.fors parts.md.toList pk.pkSeed parts.forsAdrs
        GeneralHypertree.verifyM vp core forsPk sig.hypertree pk.pkSeed parts pk.pkRoot) := by
  rfl

/-- Honest internal signatures verify at every validated hypertree depth. -/
example (prims : Primitives vp.params) [DecidableEq prims.Y]
    (msg : List Byte) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf)
    (pkSeed : prims.PkSeed) (addrnd : prims.Y) :
    GeneralScheme.verifyInternal vp prims msg
        (GeneralScheme.signInternal vp prims msg
          (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).2 addrnd)
        (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).1 = true := by
  exact GeneralScheme.verifyInternal_signInternal vp prims msg skSeed skPrf pkSeed addrnd

end SLHDSA.GeneralSchemeTest
