/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Hypertree
public import HashSig.SLHDSA.Position

/-!
# Depth-one SLH-DSA compatibility scheme

The compatibility specialization of the SLH-DSA signature scheme to parameters satisfying
`d = 1`, assembled from FORS (`HashSig.SLHDSA.Fors`) and the single-layer hypertree
(`HashSig.SLHDSA.Hypertree`). The general Algorithms 18--20 in
`HashSig.SLHDSA.GeneralScheme` are the canonical scheme path. These wrappers preserve the
explicit depth-one API required by specialized security developments.

The compatibility programs depend only on `CorePrimitives` and issue `H_msg` and every tweakable
hash as an explicit `HasQuery` operation:

- `slhKeygenInternalM` / `slhSignInternalM` / `slhVerifyInternalM` (Algorithms 18–20),
- `slhKeygenInternal` / `slhSignInternal` / `slhVerifyInternal`, the deterministic
  `PublicHash.impl` interpretations of those programs,
- `splitDigest`, the typed message-digest split into `md`, `idxTree`, and `idxLeaf` (§9), and
- `emptyContextMessage`, the FIPS 205 external-message encoding used by the compatibility external
  scheme in `HashSig.SLHDSA.RandomOracle`.

Signing follows FIPS 205 Algorithm 19 literally: after `H_msg`, it creates the FORS signature,
recovers the FORS public key from that signature, and signs the recovered value with the
hypertree. It does not independently regenerate the FORS public key.

The deterministic correctness result `slhVerifyInternal_slhSignInternal` proves that every
honestly generated signature verifies for every fixed total public-hash answer function. This is
not a cached-random-oracle theorem; a probabilistic experiment must choose and thread that
semantics separately.

## References

- NIST FIPS 205, §9 (Algorithms 18–22, 24), §10 (external API), §4.1 (the H_msg digest split)
-/

@[expose] public section


open OracleComp OracleSpec

namespace SLHDSA

variable {p : Params}
variable (hd : p.d = 1)

/-- The SLH-DSA public key over an implementation-independent context: public seed and
hypertree root. -/
structure PublicKeyCore (core : CorePrimitives p) where
  /-- Public seed `PK.seed`. -/
  pkSeed : core.PkSeed
  /-- Hypertree root `PK.root`. -/
  pkRoot : core.Y

/-- The SLH-DSA secret key over an implementation-independent context. It carries the public
material required by signing. -/
structure SecretKeyCore (core : CorePrimitives p) where
  /-- Secret seed `SK.seed`. -/
  skSeed : core.SkSeed
  /-- Message-PRF key `SK.prf`. -/
  skPrf : core.SkPrf
  /-- Public seed `PK.seed`. -/
  pkSeed : core.PkSeed
  /-- Hypertree root `PK.root`. -/
  pkRoot : core.Y

/-- An intrinsically shaped SLH-DSA signature (`R ‖ SIG_FORS ‖ SIG_HT`). -/
structure SignatureCore (p : Params) (core : CorePrimitives p) where
  /-- Message randomizer `R`. -/
  randomness : core.Y
  /-- Exactly `k` intrinsically shaped FORS tree signatures. -/
  fors : ForsSigCore p core
  /-- Exactly `d` intrinsically shaped XMSS signatures. -/
  hypertree : HtSigCore p core

/-! ### Depth-one compatibility algorithms -/

/-- Depth-one compatibility specialization of internal key generation. The public root is
computed by the explicit-query hypertree program. -/
def slhKeygenInternalM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    m (PublicKeyCore core × SecretKeyCore core) := do
  let pkRoot ← htRootM core hd skSeed pkSeed Adrs.zero 0
  return (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)

/-- Depth-one compatibility specialization of internal signing. Its public-hash schedule is
`H_msg`, FORS signing, recovery of the FORS public key from that signature, then hypertree
signing. In particular, signing does not call `forsPkGenM`. -/
def slhSignInternalM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    m (SignatureCore p core) := do
  let R := core.PRFmsg sk.skPrf addrnd msg
  let digest ← PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg
  let parts := splitDigest p digest
  let forsSig ← forsSignM core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs
  let forsPk ← forsPkFromSigM core forsSig parts.md.toList sk.pkSeed parts.forsAdrs
  let htSig ← htSignM core hd forsPk sk.skSeed sk.pkSeed Adrs.zero 0 parts.idxLeaf.val
  return ⟨R, forsSig, htSig⟩

/-- Depth-one compatibility specialization of internal verification. Its public-hash schedule is
`H_msg`, FORS public-key recovery, then hypertree recovery and comparison with `PK.root`. -/
def slhVerifyInternalM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (msg : List Byte) (sig : SignatureCore p core) (pk : PublicKeyCore core) : m Bool := do
  let digest ← PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg
  let parts := splitDigest p digest
  let forsPk ← forsPkFromSigM core sig.fors parts.md.toList pk.pkSeed parts.forsAdrs
  htVerifyM core hd forsPk sig.hypertree pk.pkSeed Adrs.zero 0 parts.idxLeaf.val pk.pkRoot

/-! ### Pure deterministic interpretations -/

/-- Pure internal key generation is the deterministic interpretation of
`slhKeygenInternalM`. -/
def slhKeygenInternal (prims : Primitives p) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf)
    (pkSeed : prims.PkSeed) : PublicKeyCore prims.core × SecretKeyCore prims.core :=
  simulateQ (PublicHash.impl prims)
    (slhKeygenInternalM hd prims.core skSeed skPrf pkSeed :
      OracleComp (publicHashSpec prims.core)
        (PublicKeyCore prims.core × SecretKeyCore prims.core))

/-- Pure internal signing is the deterministic interpretation of `slhSignInternalM`. -/
def slhSignInternal (prims : Primitives p) (msg : List Byte) (sk : SecretKeyCore prims.core)
    (addrnd : prims.Y) : SignatureCore p prims.core :=
  simulateQ (PublicHash.impl prims)
    (slhSignInternalM hd prims.core msg sk addrnd :
      OracleComp (publicHashSpec prims.core) (SignatureCore p prims.core))

/-- Pure internal verification is the deterministic interpretation of
`slhVerifyInternalM`. -/
def slhVerifyInternal (prims : Primitives p) [DecidableEq prims.Y] (msg : List Byte)
    (sig : SignatureCore p prims.core) (pk : PublicKeyCore prims.core) : Bool :=
  simulateQ (PublicHash.impl prims)
    (slhVerifyInternalM hd prims.core msg sig pk : OracleComp (publicHashSpec prims.core) Bool)

/-! ### Naturality -/

private theorem queryHom_hmsg (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    F.toMonadHom (PublicHash.hmsg core r pkSeed pkRoot msg) =
      PublicHash.hmsg core r pkSeed pkRoot msg := by
  change F.toMonadHom
      (query (spec := publicHashSpec core) (.hmsg r pkSeed pkRoot msg)) =
    query (spec := publicHashSpec core) (.hmsg r pkSeed pkRoot msg)
  exact HasQuery.map_query F _

/-- Query-preserving monad morphisms commute with depth-one internal key generation. -/
theorem slhKeygenInternalM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    F.toMonadHom (slhKeygenInternalM hd core skSeed skPrf pkSeed) =
      slhKeygenInternalM hd core skSeed skPrf pkSeed := by
  simp [slhKeygenInternalM, htRootM_natural core hd F]

/-- Query-preserving monad morphisms commute with depth-one internal signing. -/
theorem slhSignInternalM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    F.toMonadHom (slhSignInternalM hd core msg sk addrnd) =
      slhSignInternalM hd core msg sk addrnd := by
  simp [slhSignInternalM, queryHom_hmsg core F,
    forsSignM_natural core F, forsPkFromSigM_natural core F, htSignM_natural core hd F]

/-- Query-preserving monad morphisms commute with depth-one internal verification. -/
theorem slhVerifyInternalM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n] [DecidableEq core.Y]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : List Byte) (sig : SignatureCore p core) (pk : PublicKeyCore core) :
    F.toMonadHom (slhVerifyInternalM hd core msg sig pk) =
      slhVerifyInternalM hd core msg sig pk := by
  simp [slhVerifyInternalM, queryHom_hmsg core F,
    forsPkFromSigM_natural core F, htVerifyM_natural core hd F]

/-! ### Structural query bounds -/

/-- Structural public-hash budget for internal key generation. -/
def slhKeygenInternalQueryBound (p : Params) : ℕ :=
  xmssNodeQueryBound p p.hp

/-- Structural public-hash budget for the complete internal signing schedule: one `H_msg`, FORS
signing and recovery from that signature, then hypertree signing.  The WOTS+ term is made uniform
by allowing every chain its full `w - 1` steps. -/
def slhSignInternalQueryBound (p : Params) : ℕ :=
  1 + ((p.k * ((2 ^ p.a - 1) + (2 ^ p.a - p.a - 1)) +
      (p.k * (p.a + 1) + 1)) +
    (p.len * (p.w - 1) + xmssAuthPathQueryBound p p.hp))

/-- Structural public-hash budget for verification. Intrinsic signature shapes fix every
authentication-path length at the type level, so the budget depends only on the parameters:
one `H_msg`, `k * (a + 1) + 1` FORS recovery calls, and a hypertree term using the maximum
WOTS+ chain budget plus the `h'`-step XMSS authentication path. -/
def slhVerifyInternalQueryBound (p : Params) : ℕ :=
  1 + (p.k * (p.a + 1) + 1) + (p.len * (p.w - 1) + 1 + p.hp)

private theorem publicHash_hmsg_isTotalQueryBound_one (core : CorePrimitives p)
    (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    IsTotalQueryBound
      (PublicHash.hmsg core r pkSeed pkRoot msg :
        OracleComp (publicHashSpec core) (Bytes p.m)) 1 := by
  simp [PublicHash.hmsg, IsTotalQueryBound]

/-- Internal key generation inherits the complete hypertree-root budget. -/
theorem slhKeygenInternalM_isTotalQueryBound (core : CorePrimitives p)
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    IsTotalQueryBound
      (slhKeygenInternalM hd core skSeed skPrf pkSeed :
        OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core))
      (slhKeygenInternalQueryBound p) := by
  simpa [slhKeygenInternalM, slhKeygenInternalQueryBound] using
    isTotalQueryBound_bind (htRootM_isTotalQueryBound core hd skSeed pkSeed Adrs.zero 0)
      (fun pkRoot => show IsTotalQueryBound
        (pure (PublicKeyCore.mk pkSeed pkRoot,
          SecretKeyCore.mk skSeed skPrf pkSeed pkRoot) :
          OracleComp (publicHashSpec core) _) 0 from trivial)

private theorem htSignM_isTotalQueryBound_coarse (core : CorePrimitives p)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    IsTotalQueryBound
      (htSignM core hd msg sk pk adrs idxTree idxLeaf :
        OracleComp (publicHashSpec core) (HtSigCore p core))
      (p.len * (p.w - 1) + xmssAuthPathQueryBound p p.hp) := by
  apply (htSignM_isTotalQueryBound core hd msg sk pk adrs idxTree idxLeaf).mono
  have hsum :
      (∑ i : Fin p.len, chainStepsCore core msg i.val) ≤ p.len * (p.w - 1) := by
    calc
      (∑ i : Fin p.len, chainStepsCore core msg i.val) ≤
          ∑ _ : Fin p.len, (p.w - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            exact chainStepsCore_le core msg i.val
      _ = p.len * (p.w - 1) := by simp
  omega

/-- Internal signing follows and bounds the whole FIPS 205 Algorithm 19 public-hash schedule:
one `H_msg` query, sibling-only FORS signing, FORS recovery from the generated signature, and
hypertree signing.  The theorem counts calls in the free oracle program.  It is an upper bound,
not a count of distinct lazy-random-oracle cache misses or fresh samples. -/
theorem slhSignInternalM_isTotalQueryBound (core : CorePrimitives p)
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    IsTotalQueryBound
      (slhSignInternalM hd core msg sk addrnd :
        OracleComp (publicHashSpec core) (SignatureCore p core))
      (slhSignInternalQueryBound p) := by
  let R := core.PRFmsg sk.skPrf addrnd msg
  have hbound := isTotalQueryBound_bind
    (publicHash_hmsg_isTotalQueryBound_one core R sk.pkSeed sk.pkRoot msg) fun digest =>
      let parts := splitDigest p digest
      isTotalQueryBound_bind
        (forsSignM_then_forsPkFromSigM_isTotalQueryBound
          core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs) fun sigAndPk =>
            isTotalQueryBound_bind
              (htSignM_isTotalQueryBound_coarse hd core sigAndPk.2 sk.skSeed sk.pkSeed
                Adrs.zero 0 parts.idxLeaf.val) fun htSig =>
                  show IsTotalQueryBound
                    (pure ⟨R, sigAndPk.1, htSig⟩ :
                      OracleComp (publicHashSpec core) (SignatureCore p core)) 0 from trivial
  simpa [slhSignInternalM, slhSignInternalQueryBound, R, bind_assoc] using hbound

private theorem htVerifyM_isTotalQueryBound_coarse (core : CorePrimitives p)
    [DecidableEq core.Y] (msg : core.Y) (sig : HtSigCore p core)
    (pk : core.PkSeed) (adrs : Adrs) (idxTree idxLeaf : ℕ) (pkRoot : core.Y) :
    IsTotalQueryBound
      (htVerifyM core hd msg sig pk adrs idxTree idxLeaf pkRoot :
        OracleComp (publicHashSpec core) Bool)
      (p.len * (p.w - 1) + 1 + p.hp) := by
  apply (htVerifyM_isTotalQueryBound core hd msg sig pk adrs idxTree idxLeaf pkRoot).mono
  have hsum :
      (∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) ≤
        p.len * (p.w - 1) := by
    calc
      (∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) ≤
          ∑ _ : Fin p.len, (p.w - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            omega
      _ = p.len * (p.w - 1) := by simp
  omega

/-- Verification is bounded by one `H_msg` query, FORS recovery for the supplied paths, and
hypertree recovery with a coarse full-WOTS chain allowance. This counts free-oracle calls, not
distinct random-oracle cache misses. -/
theorem slhVerifyInternalM_isTotalQueryBound (core : CorePrimitives p) [DecidableEq core.Y]
    (msg : List Byte) (sig : SignatureCore p core) (pk : PublicKeyCore core) :
    IsTotalQueryBound
      (slhVerifyInternalM hd core msg sig pk : OracleComp (publicHashSpec core) Bool)
      (slhVerifyInternalQueryBound p) := by
  have hbound := isTotalQueryBound_bind
    (publicHash_hmsg_isTotalQueryBound_one core sig.randomness pk.pkSeed pk.pkRoot msg)
      fun digest =>
      let parts := splitDigest p digest
      isTotalQueryBound_bind
        (forsPkFromSigM_isTotalQueryBound core sig.fors parts.md.toList pk.pkSeed
          parts.forsAdrs) fun forsPk =>
            htVerifyM_isTotalQueryBound_coarse hd core forsPk sig.hypertree pk.pkSeed Adrs.zero 0
              parts.idxLeaf.val pk.pkRoot
  simpa [slhVerifyInternalM, slhVerifyInternalQueryBound, Nat.add_assoc] using hbound

/-! ### Deterministic interpretations -/

@[simp]
theorem simulateQ_slhKeygenInternalM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    simulateQ answer
        (slhKeygenInternalM hd core skSeed skPrf pkSeed :
          OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core)) =
      slhKeygenInternal (p := p) hd (PublicHash.withPublicHash core answer) skSeed skPrf
        pkSeed := by
  simp [slhKeygenInternal, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_slhKeygenInternalM (prims : Primitives p)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    simulateQ (PublicHash.impl prims)
        (slhKeygenInternalM hd prims.core skSeed skPrf pkSeed :
          OracleComp (publicHashSpec prims.core)
            (PublicKeyCore prims.core × SecretKeyCore prims.core)) =
      slhKeygenInternal hd prims skSeed skPrf pkSeed := rfl

@[simp]
theorem simulateQ_slhSignInternalM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    simulateQ answer
        (slhSignInternalM hd core msg sk addrnd :
          OracleComp (publicHashSpec core) (SignatureCore p core)) =
      slhSignInternal (p := p) hd (PublicHash.withPublicHash core answer) msg sk addrnd := by
  simp [slhSignInternal, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_slhSignInternalM (prims : Primitives p)
    (msg : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (slhSignInternalM hd prims.core msg sk addrnd :
          OracleComp (publicHashSpec prims.core) (SignatureCore p prims.core)) =
      slhSignInternal hd prims msg sk addrnd := rfl

@[simp]
theorem simulateQ_slhVerifyInternalM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) [DecidableEq core.Y]
    (msg : List Byte) (sig : SignatureCore p core) (pk : PublicKeyCore core) :
    simulateQ answer
        (slhVerifyInternalM hd core msg sig pk : OracleComp (publicHashSpec core) Bool) =
      slhVerifyInternal (p := p) hd (PublicHash.withPublicHash core answer) msg sig pk := by
  simp [slhVerifyInternal, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_slhVerifyInternalM (prims : Primitives p) [DecidableEq prims.Y]
    (msg : List Byte) (sig : SignatureCore p prims.core) (pk : PublicKeyCore prims.core) :
    simulateQ (PublicHash.impl prims)
        (slhVerifyInternalM hd prims.core msg sig pk :
          OracleComp (publicHashSpec prims.core) Bool) =
      slhVerifyInternal hd prims msg sig pk := rfl

/-- Fixed-answer correctness of the depth-one compatibility programs. Key generation, signing, and
verification use one total deterministic answer function. This theorem does not install or make
a claim about random-oracle caching. -/
theorem simulateQ_slhVerifyInternalM_slhSignInternalM_withPublicHash
    (core : CorePrimitives p) (answer : QueryImpl (publicHashSpec core) Id)
    [DecidableEq core.Y]
    (msg : List Byte) (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed)
    (addrnd : core.Y) :
    simulateQ answer (do
      let (pk, sk) ← slhKeygenInternalM hd core skSeed skPrf pkSeed
      let sig ← slhSignInternalM hd core msg sk addrnd
      slhVerifyInternalM hd core msg sig pk) = true := by
  simp only [slhKeygenInternalM, slhSignInternalM, slhVerifyInternalM,
    simulateQ_bind, simulateQ_pure,
    simulateQ_htRootM_withPublicHash core hd, simulateQ_forsSignM_withPublicHash,
    simulateQ_forsPkFromSigM_withPublicHash, simulateQ_htSignM_withPublicHash core hd,
    simulateQ_htVerifyM_withPublicHash core hd]
  exact htVerify_htSign (PublicHash.withPublicHash core answer) hd _ skSeed pkSeed Adrs.zero 0 _
    (splitDigest p _).idxLeaf.isLt

/-- **Deterministic correctness core**: an honestly generated signature verifies, for every
choice of seeds, randomizer, and deterministic public-hash implementation. -/
theorem slhVerifyInternal_slhSignInternal (prims : Primitives p) [DecidableEq prims.Y]
    (msg : List Byte) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed)
    (addrnd : prims.Y) :
    slhVerifyInternal hd prims msg
        (slhSignInternal hd prims msg (slhKeygenInternal hd prims skSeed skPrf pkSeed).2 addrnd)
        (slhKeygenInternal hd prims skSeed skPrf pkSeed).1 = true := by
  have h := simulateQ_slhVerifyInternalM_slhSignInternalM_withPublicHash
    hd prims.core (PublicHash.impl prims) msg skSeed skPrf pkSeed addrnd
  change ((do
    let (pk, sk) ← slhKeygenInternal hd prims skSeed skPrf pkSeed
    let sig ← slhSignInternal hd prims msg sk addrnd
    slhVerifyInternal hd prims msg sig pk) : Id Bool) = true
  simpa only [simulateQ_bind, simulateQ_slhKeygenInternalM,
    simulateQ_slhSignInternalM, simulateQ_slhVerifyInternalM] using h

/-! ### External-message encoding (FIPS 205 §10) -/

/-- FIPS 205 external-message encoding for the empty-context API:
`M' = 0x00 || 0x00 || M`. Internal algorithms consume `M'`; callers of the generic
signature API supply the raw message `M`. -/
def emptyContextMessage (msg : List Byte) : List Byte :=
  0x00 :: 0x00 :: msg

end SLHDSA
