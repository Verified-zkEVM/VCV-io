/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.GeneralScheme

/-!
# One-layer compatibility for the general SLH-DSA construction

This module relates the arbitrary-depth Algorithms 12--13 and 18--20 to the explicit
single-layer compatibility API when `d = 1`.  The signature representations are equivalent, and
key generation, root recovery, and verification agree as explicit-public-hash programs.

Signing requires a more precise statement.  FIPS 205 Algorithm 12 recovers the layer-zero root
even when that root is discarded at `d = 1`, whereas the compatibility signer returns
immediately after XMSS signing.  The general signer therefore has the same deterministic output
but a strictly longer free-oracle trace.  The theorems below expose that extra recovery instead of
claiming equality of the two oracle programs.

## References

- NIST FIPS 205, Section 7, Algorithms 12--13
- NIST FIPS 205, Section 9, Algorithms 18--20
-/

@[expose] public section

namespace SLHDSA.DepthOneCompatibility

open OracleComp

/-- At depth one, the intrinsic general-hypertree signature is equivalent to the compatibility
single XMSS signature. The two types are definitionally equal at every depth (both are
`Vector (XmssSigCore p core) p.d`), so this is `Equiv.refl`; the abbreviation marks the API
boundary where a genuine representation conversion would sit, and its evidence argument keeps
callers at the depth-one surface. -/
abbrev hypertreeSignatureEquiv (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (_hd : vp.params.d = 1) :
    GeneralHypertree.Signature vp core ≃ HtSigCore vp.params core :=
  Equiv.refl _

/-- At depth one, the typed initial hypertree address is layer zero, tree zero, exactly as in the
one-layer API. -/
theorem initial_toAdrs_eq_htAdrs_zero (vp : ValidatedParams) (hd : vp.params.d = 1)
    (parts : DigestParts vp.params) :
    (LayerPosition.initial vp parts).toAdrs = htAdrs Adrs.zero 0 := by
  simp [LayerPosition.toAdrs, htAdrs,
    DigestParts.idxTree_eq_zero_of_d_eq_one vp.valid hd parts]

/-- General and compatibility one-layer root generation are the same free-oracle program. -/
theorem rootM_eq_htRootM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (hd : vp.params.d = 1) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (sk : core.SkSeed) (pk : core.PkSeed) :
    (GeneralHypertree.rootM vp core sk pk : m core.Y) =
      (htRootM core hd sk pk Adrs.zero 0 : m core.Y) := by
  simp [GeneralHypertree.rootM, GeneralHypertree.rootWith, htRootM, htRootWith,
    GeneralHypertree.layerAdrs, htAdrs, hd]

/-- Exact free-oracle trace of depth-one general hypertree signing.  Compared with `htSignM`, the
right-hand side performs the FIPS-mandated recovery of the just-created XMSS signature and discards
the recovered root. -/
theorem signM_toOneLayer_eq (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (hd : vp.params.d = 1) {m : Type → Type*} [Monad m] [LawfulMonad m]
    [HasQuery (publicHashSpec core) m] (msg : core.Y) (sk : core.SkSeed)
    (pk : core.PkSeed) (parts : DigestParts vp.params) :
    ((do
      let sig ← GeneralHypertree.signM vp core msg sk pk parts
      return hypertreeSignatureEquiv vp core hd sig) : m (HtSigCore vp.params core)) =
      ((do
        let sig ← htSignM core hd msg sk pk Adrs.zero 0 parts.idxLeaf.val
        let _ ← htPkFromSigM core hd msg sig pk Adrs.zero 0 parts.idxLeaf.val
        return sig) : m (HtSigCore vp.params core)) := by
  rcases vp with ⟨⟨n, h, d, hp, a, k, lgw⟩, hvalid⟩
  dsimp at hd ⊢
  subst d
  have hsingle (sig : XmssSigCore _ core) :
      #v[sig] = HtSigCore.singleLayer rfl sig := by
    apply Vector.ext
    intro i hi
    simp [HtSigCore.singleLayer]
  simp [GeneralHypertree.signM, GeneralHypertree.signFromPositionM,
    GeneralHypertree.signFromPositionWith,
    initial_toAdrs_eq_htAdrs_zero, htSignM, htPkFromSigM,
    htSignWith, htPkFromSigWith, hsingle]

/-- General depth-one root recovery is exactly the compatibility free-oracle program after
converting the intrinsic singleton signature. -/
theorem pkFromSigM_eq_htPkFromSigM (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (hd : vp.params.d = 1)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sig : GeneralHypertree.Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    (GeneralHypertree.pkFromSigM vp core msg sig pk parts : m core.Y) =
      (htPkFromSigM core hd msg (hypertreeSignatureEquiv vp core hd sig) pk Adrs.zero 0
        parts.idxLeaf.val : m core.Y) := by
  rcases vp with ⟨⟨n, h, d, hp, a, k, lgw⟩, hvalid⟩
  dsimp at hd ⊢
  subst d
  simp [GeneralHypertree.pkFromSigM, GeneralHypertree.recoverFromPositionM,
    GeneralHypertree.recoverFromPositionWith,
    initial_toAdrs_eq_htAdrs_zero, htPkFromSigM, htPkFromSigWith,
    HtSigCore.getSingleLayer, Vector.head]

/-- General depth-one verification is exactly the compatibility free-oracle program after
converting the intrinsic singleton signature. -/
theorem verifyM_eq_htVerifyM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (hd : vp.params.d = 1) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (msg : core.Y) (sig : GeneralHypertree.Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : core.Y) :
    (GeneralHypertree.verifyM vp core msg sig pk parts pkRoot : m Bool) =
      (htVerifyM core hd msg (hypertreeSignatureEquiv vp core hd sig) pk Adrs.zero 0
        parts.idxLeaf.val pkRoot : m Bool) := by
  simp [GeneralHypertree.verifyM, htVerifyM, pkFromSigM_eq_htPkFromSigM vp core hd]

/-! ## Deterministic-output compatibility -/

/-- The general depth-one top root is the compatibility one-layer root. -/
theorem root_eq_htRoot (vp : ValidatedParams) (prims : Primitives vp.params)
    (hd : vp.params.d = 1) (sk : prims.SkSeed) (pk : prims.PkSeed) :
    GeneralHypertree.root vp prims sk pk = htRoot prims hd sk pk Adrs.zero 0 := by
  change simulateQ (PublicHash.impl prims)
      (GeneralHypertree.rootM vp prims.core sk pk :
        OracleComp (publicHashSpec prims.core) prims.Y) =
    simulateQ (PublicHash.impl prims)
      (htRootM prims.core hd sk pk Adrs.zero 0 :
        OracleComp (publicHashSpec prims.core) prims.Y)
  rw [rootM_eq_htRootM vp prims.core hd]

/-- Although the two signing programs have different free-oracle traces, their outputs agree under
every fixed deterministic public-hash interpretation. -/
theorem sign_toOneLayer_eq (vp : ValidatedParams) (prims : Primitives vp.params)
    (hd : vp.params.d = 1) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    hypertreeSignatureEquiv vp prims.core hd (GeneralHypertree.sign vp prims msg sk pk parts) =
      htSign prims hd msg sk pk Adrs.zero 0 parts.idxLeaf.val := by
  have h := congrArg (simulateQ (PublicHash.impl prims))
    (signM_toOneLayer_eq vp prims.core hd
      (m := OracleComp (publicHashSpec prims.core)) msg sk pk parts)
  change hypertreeSignatureEquiv vp prims.core hd
      (simulateQ (PublicHash.impl prims)
        (GeneralHypertree.signM vp prims.core msg sk pk parts :
          OracleComp (publicHashSpec prims.core)
            (GeneralHypertree.Signature vp prims.core))).run =
    (simulateQ (PublicHash.impl prims)
      (htSignM prims.core hd msg sk pk Adrs.zero 0 parts.idxLeaf.val :
        OracleComp (publicHashSpec prims.core) (HtSigCore vp.params prims.core))).run
  have hr := congrArg Id.run h
  simpa only [simulateQ_bind, simulateQ_pure, Id.run_bind, Id.run_pure] using hr

/-- Deterministic depth-one root recovery agrees after signature conversion. -/
theorem pkFromSig_eq_htPkFromSig (vp : ValidatedParams) (prims : Primitives vp.params)
    (hd : vp.params.d = 1) (msg : prims.Y)
    (sig : GeneralHypertree.Signature vp prims.core) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    GeneralHypertree.pkFromSig vp prims msg sig pk parts =
      htPkFromSig prims hd msg (hypertreeSignatureEquiv vp prims.core hd sig) pk Adrs.zero 0
        parts.idxLeaf.val := by
  change simulateQ (PublicHash.impl prims)
      (GeneralHypertree.pkFromSigM vp prims.core msg sig pk parts :
        OracleComp (publicHashSpec prims.core) prims.Y) =
    simulateQ (PublicHash.impl prims)
      (htPkFromSigM prims.core hd msg (hypertreeSignatureEquiv vp prims.core hd sig) pk
        Adrs.zero 0 parts.idxLeaf.val : OracleComp (publicHashSpec prims.core) prims.Y)
  rw [pkFromSigM_eq_htPkFromSigM vp prims.core hd]

/-- Deterministic depth-one verification agrees after signature conversion. -/
theorem verify_eq_htVerify (vp : ValidatedParams) (prims : Primitives vp.params)
    (hd : vp.params.d = 1) [DecidableEq prims.Y]
    (msg : prims.Y) (sig : GeneralHypertree.Signature vp prims.core) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : prims.Y) :
    GeneralHypertree.verify vp prims msg sig pk parts pkRoot =
      htVerify prims hd msg (hypertreeSignatureEquiv vp prims.core hd sig) pk Adrs.zero 0
        parts.idxLeaf.val pkRoot := by
  change simulateQ (PublicHash.impl prims)
      (GeneralHypertree.verifyM vp prims.core msg sig pk parts pkRoot :
        OracleComp (publicHashSpec prims.core) Bool) =
    simulateQ (PublicHash.impl prims)
      (htVerifyM prims.core hd msg (hypertreeSignatureEquiv vp prims.core hd sig) pk
        Adrs.zero 0 parts.idxLeaf.val pkRoot : OracleComp (publicHashSpec prims.core) Bool)
  rw [verifyM_eq_htVerifyM vp prims.core hd]

/-! ## Internal-scheme compatibility -/

/-- At depth one, the structured general signature is equivalent to the compatibility
representation. As with `hypertreeSignatureEquiv`, the types are definitionally equal at every
depth, so this is `Equiv.refl` with an evidence argument marking the depth-one boundary. -/
abbrev schemeSignatureEquiv (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (_hd : vp.params.d = 1) :
    GeneralScheme.SignatureCore vp core ≃ SignatureCore vp.params core :=
  Equiv.refl _

/-- General and compatibility depth-one key generation are the same free-oracle program. -/
theorem keygenInternalM_eq_slhKeygenInternalM (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (hd : vp.params.d = 1)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    (GeneralScheme.keygenInternalM vp core skSeed skPrf pkSeed :
      m (PublicKeyCore core × SecretKeyCore core)) =
      (slhKeygenInternalM hd core skSeed skPrf pkSeed :
        m (PublicKeyCore core × SecretKeyCore core)) := by
  simp [GeneralScheme.keygenInternalM, slhKeygenInternalM,
    rootM_eq_htRootM vp core hd]

/-- Exact free-oracle trace of general internal signing at depth one.  This is the compatibility
Algorithm 19 schedule followed by the one additional, discarded XMSS recovery required by the
general Algorithm 12. -/
theorem signInternalM_toOneLayer_eq (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (hd : vp.params.d = 1)
    {m : Type → Type*} [Monad m] [LawfulMonad m] [HasQuery (publicHashSpec core) m]
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    ((do
      let sig ← GeneralScheme.signInternalM vp core msg sk addrnd
      return schemeSignatureEquiv vp core hd sig) : m (SignatureCore vp.params core)) =
      ((do
        let R := core.PRFmsg sk.skPrf addrnd msg
        let digest ← PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg
        let parts := splitDigest vp.params digest
        let forsSig ← forsSignM core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs
        let forsPk ← forsPkFromSigM core forsSig parts.md.toList sk.pkSeed parts.forsAdrs
        let htSig ← htSignM core hd forsPk sk.skSeed sk.pkSeed Adrs.zero 0 parts.idxLeaf.val
        let _ ← htPkFromSigM core hd forsPk htSig sk.pkSeed Adrs.zero 0 parts.idxLeaf.val
        return ⟨R, forsSig, htSig⟩) : m (SignatureCore vp.params core)) := by
  rcases vp with ⟨⟨n, h, d, hp, a, k, lgw⟩, hvalid⟩
  dsimp at hd ⊢
  subst d
  have hsingle (oneSig : XmssSigCore _ core) :
      #v[oneSig] = HtSigCore.singleLayer rfl oneSig := by
    apply Vector.ext
    intro i hi
    simp [HtSigCore.singleLayer]
  simp [GeneralScheme.signInternalM,
    GeneralHypertree.signM, GeneralHypertree.signFromPositionM,
    GeneralHypertree.signFromPositionWith,
    initial_toAdrs_eq_htAdrs_zero,
    htSignM, htPkFromSigM, htSignWith, htPkFromSigWith,
    hsingle, monad_norm]

/-- General and compatibility depth-one verification are the same free-oracle program after
signature conversion. -/
theorem verifyInternalM_eq_slhVerifyInternalM (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (hd : vp.params.d = 1)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    [DecidableEq core.Y] (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core)
    (pk : PublicKeyCore core) :
    (GeneralScheme.verifyInternalM vp core msg sig pk : m Bool) =
      (slhVerifyInternalM hd core msg (schemeSignatureEquiv vp core hd sig) pk : m Bool) := by
  simp [GeneralScheme.verifyInternalM, slhVerifyInternalM, schemeSignatureEquiv,
    verifyM_eq_htVerifyM vp core hd]

/-- Deterministic general key generation specializes to compatibility key generation. -/
theorem keygenInternal_eq_slhKeygenInternal (vp : ValidatedParams)
    (prims : Primitives vp.params) (hd : vp.params.d = 1)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed =
      slhKeygenInternal hd prims skSeed skPrf pkSeed := by
  change (simulateQ (PublicHash.impl prims)
      (GeneralScheme.keygenInternalM vp prims.core skSeed skPrf pkSeed :
        OracleComp (publicHashSpec prims.core)
          (PublicKeyCore prims.core × SecretKeyCore prims.core))).run =
    (simulateQ (PublicHash.impl prims)
      (slhKeygenInternalM hd prims.core skSeed skPrf pkSeed :
        OracleComp (publicHashSpec prims.core)
          (PublicKeyCore prims.core × SecretKeyCore prims.core))).run
  rw [keygenInternalM_eq_slhKeygenInternalM vp prims.core hd]

/-- Deterministic general signing specializes to compatibility signing after signature
conversion.  This is output equality, not free-oracle-program equality; the exact additional
recovery appears in `signInternalM_toOneLayer_eq`. -/
theorem signInternal_toOneLayer_eq (vp : ValidatedParams)
    (prims : Primitives vp.params) (hd : vp.params.d = 1)
    (msg : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    schemeSignatureEquiv vp prims.core hd
        (GeneralScheme.signInternal vp prims msg sk addrnd) =
      slhSignInternal hd prims msg sk addrnd := by
  have h := congrArg (simulateQ (PublicHash.impl prims))
    (signInternalM_toOneLayer_eq vp prims.core hd
      (m := OracleComp (publicHashSpec prims.core)) msg sk addrnd)
  change schemeSignatureEquiv vp prims.core hd
      (simulateQ (PublicHash.impl prims)
        (GeneralScheme.signInternalM vp prims.core msg sk addrnd :
          OracleComp (publicHashSpec prims.core)
            (GeneralScheme.SignatureCore vp prims.core))).run =
    (simulateQ (PublicHash.impl prims)
      (slhSignInternalM hd prims.core msg sk addrnd :
        OracleComp (publicHashSpec prims.core) (SignatureCore vp.params prims.core))).run
  have hr := congrArg Id.run h
  simpa only [slhSignInternalM, simulateQ_bind, simulateQ_pure,
    Id.run_bind, Id.run_pure] using hr

/-- Deterministic general verification specializes to compatibility verification after
signature conversion. -/
theorem verifyInternal_eq_slhVerifyInternal (vp : ValidatedParams)
    (prims : Primitives vp.params) (hd : vp.params.d = 1) [DecidableEq prims.Y]
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core)
    (pk : PublicKeyCore prims.core) :
    GeneralScheme.verifyInternal vp prims msg sig pk =
      slhVerifyInternal hd prims msg (schemeSignatureEquiv vp prims.core hd sig) pk := by
  change (simulateQ (PublicHash.impl prims)
      (GeneralScheme.verifyInternalM vp prims.core msg sig pk :
        OracleComp (publicHashSpec prims.core) Bool)).run =
    (simulateQ (PublicHash.impl prims)
      (slhVerifyInternalM hd prims.core msg (schemeSignatureEquiv vp prims.core hd sig) pk :
        OracleComp (publicHashSpec prims.core) Bool)).run
  rw [verifyInternalM_eq_slhVerifyInternalM vp prims.core hd]

end SLHDSA.DepthOneCompatibility
