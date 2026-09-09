/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.HypertreeGeneral
public import HashSig.SLHDSA.Scheme

/-!
# General internal SLH-DSA scheme (FIPS 205 Algorithms 18--20)

This module is the arbitrary-`d` construction boundary.  It retains every output of `H_msg`, uses
the digest-derived FORS address, and invokes the general hypertree from the typed layer-zero
position.  Key generation computes the root of the top-layer XMSS tree.

The structured key and signature types are the canonical types owned by `SLHDSA.Scheme`; this
module implements the algorithms without introducing a parallel wire representation.  The
proof-required `d = 1` API is an explicit compatibility surface for depth-one security consumers.

## References

- NIST FIPS 205, Section 9, Algorithms 18--20
-/

@[expose] public section

namespace SLHDSA.GeneralScheme

open OracleComp

/-- The canonical structured internal signature, indexed by a validated parameter set here so the
general Algorithms 18--20 can use it without defining a second representation. -/
abbrev SignatureCore (vp : ValidatedParams) (core : CorePrimitives vp.params) :=
  SLHDSA.SignatureCore vp.params core

/-- FIPS Algorithm 18: derive the public root from layer `d - 1`, tree zero. The pair is
returned as `(PK, SK)`, the repository-wide keygen convention; FIPS 205 lists `(SK, PK)`. -/
def keygenInternalM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    m (PublicKeyCore core × SecretKeyCore core) := do
  let pkRoot ← GeneralHypertree.rootM vp core skSeed pkSeed
  return (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)

/-- FIPS Algorithm 19: randomized internal signing for every validated parameter set. -/
def signInternalM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    m (SignatureCore vp core) := do
  let R := core.PRFmsg sk.skPrf addrnd msg
  let digest ← PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg
  let parts := splitDigest vp.params digest
  let forsSig ← forsSignM core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs
  let forsPk ← forsPkFromSigM core forsSig parts.md.toList sk.pkSeed parts.forsAdrs
  let htSig ← GeneralHypertree.signM vp core forsPk sk.skSeed sk.pkSeed parts
  return ⟨R, forsSig, htSig⟩

/-- FIPS Algorithm 20: recover the FORS and hypertree roots along the same typed position
trajectory used by signing. -/
def verifyInternalM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (msg : List Byte) (sig : SignatureCore vp core) (pk : PublicKeyCore core) : m Bool := do
  let digest ← PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg
  let parts := splitDigest vp.params digest
  let forsPk ← forsPkFromSigM core sig.fors parts.md.toList pk.pkSeed parts.forsAdrs
  GeneralHypertree.verifyM vp core forsPk sig.hypertree pk.pkSeed parts pk.pkRoot

/-! ## Naturality -/

private theorem queryHom_hmsg {p : Params} (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    F.toMonadHom (PublicHash.hmsg core r pkSeed pkRoot msg) =
      PublicHash.hmsg core r pkSeed pkRoot msg := by
  change F.toMonadHom
      (query (spec := publicHashSpec core) (.hmsg r pkSeed pkRoot msg)) =
    query (spec := publicHashSpec core) (.hmsg r pkSeed pkRoot msg)
  exact HasQuery.map_query F _

/-- Query-preserving monad morphisms commute with general internal key generation. -/
theorem keygenInternalM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    F.toMonadHom (keygenInternalM vp core skSeed skPrf pkSeed) =
      keygenInternalM vp core skSeed skPrf pkSeed := by
  simp [keygenInternalM, GeneralHypertree.rootM_natural vp core F]

/-- Query-preserving monad morphisms commute with general internal signing. -/
theorem signInternalM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    F.toMonadHom (signInternalM vp core msg sk addrnd) =
      signInternalM vp core msg sk addrnd := by
  simp [signInternalM, queryHom_hmsg core F, forsSignM_natural core F,
    forsPkFromSigM_natural core F, GeneralHypertree.signM_natural vp core F]

/-- Query-preserving monad morphisms commute with general internal verification. -/
theorem verifyInternalM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    [DecidableEq core.Y]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : List Byte) (sig : SignatureCore vp core) (pk : PublicKeyCore core) :
    F.toMonadHom (verifyInternalM vp core msg sig pk) =
      verifyInternalM vp core msg sig pk := by
  simp [verifyInternalM, queryHom_hmsg core F, forsPkFromSigM_natural core F,
    GeneralHypertree.verifyM_natural vp core F]

/-! ## Fixed-answer completeness -/

/-- Arbitrary-depth internal SLH-DSA completeness for one fixed total public-hash answer
function.  Key generation, signing, FORS recovery, hypertree signing, and verification all share
the same deterministic interpretation. -/
theorem simulateQ_verifyInternalM_signInternalM_withPublicHash
    (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (answer : QueryImpl (publicHashSpec core) Id) [DecidableEq core.Y]
    (msg : List Byte) (skSeed : core.SkSeed) (skPrf : core.SkPrf)
    (pkSeed : core.PkSeed) (addrnd : core.Y) :
    simulateQ answer (do
      let (pk, sk) ← keygenInternalM vp core skSeed skPrf pkSeed
      let sig ← signInternalM vp core msg sk addrnd
      verifyInternalM vp core msg sig pk) = true := by
  simp only [keygenInternalM, signInternalM, verifyInternalM,
    simulateQ_bind, simulateQ_pure,
    GeneralHypertree.simulateQ_rootM_withPublicHash,
    simulateQ_forsSignM_withPublicHash, simulateQ_forsPkFromSigM_withPublicHash,
    GeneralHypertree.simulateQ_signM_withPublicHash,
    GeneralHypertree.simulateQ_verifyM_withPublicHash]
  exact GeneralHypertree.verify_sign vp (PublicHash.withPublicHash core answer) _ skSeed pkSeed _

/-! ## Pure deterministic interpretations -/

def keygenInternal (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    PublicKeyCore prims.core × SecretKeyCore prims.core :=
  simulateQ (PublicHash.impl prims)
    (keygenInternalM vp prims.core skSeed skPrf pkSeed :
      OracleComp (publicHashSpec prims.core)
        (PublicKeyCore prims.core × SecretKeyCore prims.core))

def signInternal (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    SignatureCore vp prims.core :=
  simulateQ (PublicHash.impl prims)
    (signInternalM vp prims.core msg sk addrnd :
      OracleComp (publicHashSpec prims.core) (SignatureCore vp prims.core))

def verifyInternal (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y]
    (msg : List Byte) (sig : SignatureCore vp prims.core) (pk : PublicKeyCore prims.core) : Bool :=
  simulateQ (PublicHash.impl prims)
    (verifyInternalM vp prims.core msg sig pk : OracleComp (publicHashSpec prims.core) Bool)

@[simp]
theorem simulateQ_keygenInternalM (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    simulateQ (PublicHash.impl prims)
        (keygenInternalM vp prims.core skSeed skPrf pkSeed :
          OracleComp (publicHashSpec prims.core)
            (PublicKeyCore prims.core × SecretKeyCore prims.core)) =
      keygenInternal vp prims skSeed skPrf pkSeed := rfl

@[simp]
theorem simulateQ_signInternalM (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : List Byte) (sk : SecretKeyCore prims.core) (addrnd : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (signInternalM vp prims.core msg sk addrnd :
          OracleComp (publicHashSpec prims.core) (SignatureCore vp prims.core)) =
      signInternal vp prims msg sk addrnd := rfl

@[simp]
theorem simulateQ_verifyInternalM (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y]
    (msg : List Byte) (sig : SignatureCore vp prims.core) (pk : PublicKeyCore prims.core) :
    simulateQ (PublicHash.impl prims)
        (verifyInternalM vp prims.core msg sig pk :
          OracleComp (publicHashSpec prims.core) Bool) =
      verifyInternal vp prims msg sig pk := rfl

/-! ## Pure API equations

The three equations below are what a consumer of the pure interpretations rewrites with.  None of
them is available by `rfl` downstream: `keygenInternalM` and `verifyInternalM` are `do` blocks over
`publicHashSpec`, and their interpretation under `simulateQ (PublicHash.impl prims)` reduces only
once the `bind` law — and, where an `H_msg` query is made, the handler equation for it — has fired.
Each proof names the rewrites its own equation needs and no more: `verifyInternal_eq` names both,
`keygenInternal_fst` only the `bind` law, because key generation makes no `H_msg` query at all, and
`verifyInternal_eq_decide` names neither, being the previous equation composed with
`GeneralHypertree.verify_eq_decide`.  Each closes the remainder inside this module, where the pure
definitions' bodies are available.  Downstream the verification reduction is additionally stopped
inside the component loops by `Vector.ofFnM`, whose body an importer cannot unfold. -/

/-- The public key FIPS 205 Algorithm 18 publishes: the public seed it was given, and the general
hypertree's top-layer root under the secret seed.

This is the first component of the returned pair, which this repository orders `(PK, SK)` where
FIPS 205 lists `(SK, PK)`.  The second component is not stated, because no consumer of this
equation reads it; `keygenInternalM`'s own `do` block exhibits it. -/
theorem keygenInternal_fst (vp : ValidatedParams) (prims : Primitives vp.params)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    (keygenInternal vp prims skSeed skPrf pkSeed).1 =
      ⟨pkSeed, GeneralHypertree.root vp prims skSeed pkSeed⟩ := by
  unfold keygenInternal keygenInternalM GeneralHypertree.root
  simp only [simulateQ_bind]
  rfl

/-- FIPS 205 Algorithm 20 in one equation: split the digest the signature's *own* randomizer
produces against the public key, recover the FORS public key from the FORS half of the signature at
the digest-derived FORS address, and hand that to the general hypertree verifier at the same digest.

The randomizer is the forged signature's, not a queried one, and the public key is whatever the
verifier was handed; nothing here is honest.  Only the `H_msg` query is discharged by this
equation — the FORS and hypertree halves stay in their own pure interpretations, which have their
own equations. -/
theorem verifyInternal_eq (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (msg : List Byte) (sig : SignatureCore vp prims.core)
    (pk : PublicKeyCore prims.core) :
    verifyInternal vp prims msg sig pk =
      (let parts := splitDigest vp.params (prims.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg)
       GeneralHypertree.verify vp prims
         (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs)
         sig.hypertree pk.pkSeed parts pk.pkRoot) := by
  unfold verifyInternal verifyInternalM GeneralHypertree.verify forsPkFromSig
  simp only [simulateQ_bind, PublicHash.simulateQ_hmsg]
  rfl

/-- The same equation with the final comparison of FIPS 205 Algorithm 20 exposed: verification is
the decision of whether the recovered hypertree root is the published one.  This is
`verifyInternal_eq` composed with `GeneralHypertree.verify_eq_decide`, and it is the form a case
split on a verifying signature consumes. -/
theorem verifyInternal_eq_decide (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (msg : List Byte) (sig : SignatureCore vp prims.core)
    (pk : PublicKeyCore prims.core) :
    verifyInternal vp prims msg sig pk =
      (let parts := splitDigest vp.params (prims.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg)
       decide (GeneralHypertree.pkFromSig vp prims
         (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs)
         sig.hypertree pk.pkSeed parts = pk.pkRoot)) := by
  rw [verifyInternal_eq, GeneralHypertree.verify_eq_decide]

/-! ## Completeness -/

/-- **General internal SLH-DSA correctness**: every honestly generated arbitrary-depth
signature verifies for every choice of seeds, randomizer, message, and deterministic public-hash
implementation. -/
theorem verifyInternal_signInternal (vp : ValidatedParams)
    (prims : Primitives vp.params) [DecidableEq prims.Y]
    (msg : List Byte) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf)
    (pkSeed : prims.PkSeed) (addrnd : prims.Y) :
    verifyInternal vp prims msg
        (signInternal vp prims msg (keygenInternal vp prims skSeed skPrf pkSeed).2 addrnd)
        (keygenInternal vp prims skSeed skPrf pkSeed).1 = true := by
  have h := simulateQ_verifyInternalM_signInternalM_withPublicHash
    vp prims.core (PublicHash.impl prims) msg skSeed skPrf pkSeed addrnd
  change ((do
    let (pk, sk) ← keygenInternal vp prims skSeed skPrf pkSeed
    let sig ← signInternal vp prims msg sk addrnd
    verifyInternal vp prims msg sig pk) : Id Bool) = true
  simpa only [simulateQ_bind, simulateQ_keygenInternalM,
    simulateQ_signInternalM, simulateQ_verifyInternalM] using h

end SLHDSA.GeneralScheme
