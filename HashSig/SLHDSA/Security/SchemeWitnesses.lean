/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ForsWitnesses
public import HashSig.SLHDSA.Security.HypertreeWitnesses
public import HashSig.SLHDSA.GeneralScheme

/-!
# Scheme-level witness dispatch

An SLH-DSA signature that verifies against a public key routes into exactly one of two witness
families, and which one is decided by a single equality: whether the FORS public key the signature
recovers at the position its *own* digest names is the honest FORS public key there.  When it is,
that equality is exactly the hypothesis `HashSig.SLHDSA.Security.ForsWitnesses`' extractor takes at
that instance address, and the FORS half goes there.  When it is not, the hypertree half recovers
the published root from a layer-zero message differing from the honest one at that leaf, which is
what the layer walk of `HashSig.SLHDSA.Security.HypertreeWitnesses` takes.

The digest is the one FIPS 205 Algorithm 20 computes from the signature's own randomizer, the
public seed, the published root and the message; `schemeParts` names it once, so the statements
below spell one expression rather than repeating that four-argument `H_msg` call.

## What is proved, and what is not

Everything here is deterministic.  No probability, adversary, advantage, game hop or signing
transcript appears, and no statement mentions a query log.  In particular the dispatch establishes
neither of the two transcript facts a reduction also needs — that the forged message was never
queried, and that the FORS leaf index the `fPreimage` branch names was never opened.  Both are
statements about a signing log, and neither is derivable from a signature and a public key.

The `target` argument is the caller's choice of FORS tree, and `findWitness` passes it to
`findForsWitness` unchanged.  It is honoured on that extractor's `fPreimage` branch alone: the two
other branches are decided by the recovered root vector and by the per-tree leaf images, whatever
`target` is.  A reader expecting the ITSR-selected tree to *decide* which FORS branch fires is
therefore wrong, and no declaration here supplies such a tree — computing one needs the signing log.

## The route

Verification is, by `GeneralScheme.verifyInternal_eq_decide`, the decision of whether the recovered
hypertree root is the published one.  Recovery starts from the FORS public key `forsPkFromSig`
rebuilds from the FORS half of the signature at `schemeParts …`'s own FORS address.  Comparing that
value with `forsPkGen prims sk pk.pkSeed`'s at the same address is a decidable equality, so
`verifyInternal_cases` splits on it and hands the second branch the root match unchanged.

Branch **(A)** — the two FORS public keys agree — is exactly `findForsWitness_sound`'s hypothesis,
so the FORS extractor applies at the digest-derived address and digest.

Branch **(B)** — they differ — supplies the layer walk with both of its hypotheses.  The forged
layer-zero message is the recovered FORS public key; the honest one is
`forsPkGen prims sk pk.pkSeed (schemeParts …).forsAdrs`.  **Why that honest message is well
defined** is the one step here that is not immediate: `forsPkGen` at an instance address depends on
the digest only through the FORS address, which carries `idxTree` and `idxLeaf` and not `md`.  The
honest FORS public key at a bottom position is therefore a function of the honest secret seed, the
public seed and the position alone — the value an honest signer would place at that leaf for
*every* message routed there, including messages never signed.  That is what makes branch (B) a
deterministic inclusion rather than a claim about a transcript.

## Correspondence with the EasyCrypt development

The case split is `valid_MFORSTWESNPRF <- pkFORS' = pkFORS` (`SPHINCS_PLUS.ec:2230`), and the split
on it is `Pr[mu_split …valid_MFORSTWESNPRF]` (`:4327`) inside `EUFCMA_SPHINCS_PLUS_FX`
(`:4287-4298`).  Its true half is bounded by the FORS game, through
`LeqPr_EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_VT_MFORSTWESNPRF` (`:3129-3132`) into
`EUF_CMA_MFORSTWESNPRF`; its false half by the hypertree one, through
`LeqPr_EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_VF_FLSLXMSSMTTWESNPRF` (`:3468-3471`) into
`EUF_NAGCMA_FLSLXMSSMTTWESNPRF` — a *non-adaptive* game, not the adaptive one the FORS half
reaches.  The direction agrees with the dispatch: a public-key match goes to FORS, a mismatch to
the hypertree.

**One qualifier, which the correspondence is not sound without.**  `SPHINCS_PLUS.ec:2230` lives in
`EUF_CMA_SPHINCSPLUSTWFS_NPRFNPRF_V` (`:2186`), which is reached *after* both PRF hops have replaced
the secret-key and message-key derivations by random sampling.  `verifyInternal_cases` is stated at
`forsPkGen prims sk pk.pkSeed`, with the FORS secret values still derived from the secret seed by
`prims.PRF` — before either hop.  The correspondence is "the same case split, one game earlier", and
`verifyInternal_cases` is not `valid_MFORSTWESNPRF`.

## What branch (A) inherits from the FORS reordering

`HashSig.SLHDSA.Security.ForsWitnesses` records that its three-way split is a *reordering* of the
source's four-way one and not a restriction of it, and states the containments in both directions.
Read against the source's *events*, both of its leaf-level branches are strictly contained: its `H`
branch forces every recovered root to be honest, hence the ITSR-selected tree's, hence
`valid_TRHTCR`; its `F` branch forces every tree's leaf image to agree, hence that tree's, hence
`valid_OpenPRE`; and both containments are strict, because a forgery can satisfy the source's
one-tree event while some other tree diverges.  Restricted to forgeries whose two root vectors
agree, the `H` comparison turns around against the source's *cases* — "some tree's image differs"
is strictly wider than "the selected tree's image differs" — while the `F` branch stays strictly
narrower.

What the dispatch adds, and what a later slice must not assume: the composite's own two branches are
decided by one equality, so they are disjoint and exhaustive; the FORS arm's three are disjoint and
exhaustive too, being the three outcomes of one function.  What is *not* preserved is the source's
assignment of forgeries to cases, so a transcription of its `mu_split` coefficients would be
unsound here.  What is preserved is that each branch still yields a witness against a different
component hash, so the three FORS games a later slice has to reach are the same three; which
forgeries reach which is what changes.  Whether the source's summand coefficients survive that
change is not established here and must not be assumed from it.

## Labels

*Deterministic inclusion* — a statement whose free objects are a primitive bundle, seeds, a public
key, a message, a signature, a digest split, and witness data:

* `schemeParts` and `schemeParts_eq`;
* `verifyInternal_cases`;
* `Witness`, `Witness.Valid`, `Witness.valid_fors`, `Witness.valid_hypertree`;
* `findWitness`, `findWitness_eq_fors_of_pk`, `findWitness_eq_hypertree_of_ne`,
  `findWitness_sound`, `findWitness_isSome`.

*Transcript transport* — a statement about a role ledger of `HashSig.SLHDSA.Security`:

* `mem_forsLeafAddresses_of_parts`, `mem_forsTreeAddresses_of_parts`,
  `mem_forsRootAddresses_of_parts`;
* `forsLeafAdrsKey_injective_of_parts`, `forsTreeAdrsKey_injective_of_parts`,
  `forsRootAdrsKey_injective_of_parts`.

Those eighteen are the module's whole public interface.  The one further declaration,
`digestParts_ext_of_bottom`, is `private`: it reads the two digest indices back out of a typed
bottom position and is used only by the three encoded-distinctness lemmas.

## Ledger placement, and the two arms' different needs

The `hypertree` arm needs no bridge at all.  `HypertreeWitness.Valid` names its addresses at
`(LayerPosition.initial vp (schemeParts …)).advance w.layer …`, which is a `LayerPosition`, so
`XmssWitnesses`' `mem_xmssNodeAddresses_of_leaf` and `wotsLeafAdrs_eq_wotsInstanceAdrs`,
`ReachableTargets`' `mem_wotsPkAddresses` and `WotsWitnesses`' `mem_wotsStepAddresses_of_lt` apply
to it unchanged.  Restating them here would duplicate them; `HashSigTest.SLHDSA.SchemeWitnesses`
pins those four.  `WotsWitnesses`' `wotsPreimageAdrs_mem_optionalWotsAddresses` is deliberately not
among them: its ledger is `optionalWotsAddresses vp select`, built from a reduction's per-instance
`select` function, and the dispatch has no such function to supply.

The `fors` arm does need one.  Its addresses are rooted at `DigestParts.forsAdrs`, while the three
FORS ledger lemmas are stated at `BottomPosition.forsAdrs`.  `BottomPosition.ofDigestParts` carries
no `@[expose]`, and no equation projects its two fields, so the identification runs through the
`@[simp]` equation `BottomPosition.forsAdrs_ofDigestParts` rather than by unfolding.  The three
membership lemmas below are that rewrite composed with the corresponding `ForsWitnesses` or
`ReachableTargets` statement; the three encoded-distinctness ones compose it with a `ForsWitnesses`
injectivity lemma, and the leaf and internal-node ones additionally reshape the global leaf index
into the `i * t + j` and `i * 2 ^ (a - z) + j` forms those two ledgers list.

The three encoded-distinctness lemmas consume `EncodedTargetLedgerConditions`, so a concrete profile
discharges them through `approvedEncodedTargetLedgerConditions` and the SHA-2 zero fallback is never
treated as unreachable.

**No cross-role claim is made, and none is available.**  The `fors` arm attacks the `forsF`,
`forsH` and `forsTl` ledgers and the `hypertree` arm the `xmssH`, `wotsTl`, `wotsFTcr` and
`wotsFPre` ones; the two sets are disjoint, so there is no role at which a witness from one arm and
a witness from the other could collide, and no lemma below relates them.
`EncodedTargetLedgerConditions` is per-role and does not give cross-role encoded disjointness, as
`HashSig.SLHDSA.Security.TraceTargets` records.

## Game shapes

No game-shape bridge is restated here.  `Witness.valid_fors` reduces its arm to `ForsWitness.Valid`
at the digest-derived address and digest, which is exactly the hypothesis of
`forsWitness_valid_tlCollision_eval`, `forsWitness_valid_hCollision_eval` and
`forsWitness_valid_fPreimage_eval`; `Witness.valid_hypertree` reduces the other arm through
`HypertreeWitness.valid_iff` to `XmssWitness.Valid` at a named position, which is the hypothesis of
`xmssWitness_valid_hCollision_eval` and, through `XmssWitness.valid_wots`, of
`wotsWitness_valid_tlCollision_eval`, `wotsWitness_valid_fPreimage_eval` and
`wotsWitness_valid_fCollision_eval`.  Those are all seven of the lane's `_eval` bridges, one per
leaf branch, and `HashSigTest.SLHDSA.SchemeWitnesses` pins each composition at a concrete bundle.

## Orientation of the distinctness conjuncts

A composite witness reaches seven leaf branches: the FORS arm's three constructors, and the
hypertree arm's `XmssWitness.hCollision` together with the three constructors of the `WotsWitness`
its other constructor carries.  They do not agree on which side of a disequality the submitted value
goes, and two of them state no disequality at all.

* Submitted-first, three: `ForsWitness.Valid`'s `tlCollision` (`recovered ≠ forsHonestRoots …`),
  `WotsWitness.Valid`'s `tlCollision` (`recovered ≠ honestTops`) and its `fCollision`
  (`value ≠ chain …`).
* Honest-first, two: `ForsWitness.Valid`'s `hCollision` and `XmssWitness.Valid`'s `hCollision`, both
  reading `… honestChildren … ≠ c`, inherited from `PerfectMerkleTree.findCollision_sound`.
* No distinctness conjunct, two: `ForsWitness.Valid`'s `fPreimage`, an open-preimage condition whose
  game states none, and `WotsWitness.Valid`'s `fPreimage`, whose two remaining conjuncts are the
  step bound and the step identification.

A consumer submitting to a game that tests the submitted message first applies `Ne.symm` on the two
honest-first branches, and on neither of the other five.  Each merged module records the orientation
of its own branches; it is restated here because a consumer of `Witness.Valid` meets all seven
through one predicate.

## References

- NIST FIPS 205, §9, Algorithms 18--20
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`SPHINCS_PLUS.ec`)
-/

public section

namespace SLHDSA.Security

open GeneralHypertree

variable {vp : ValidatedParams} {prims : Primitives vp.params}

/-! ## The digest a signature produces against a public key -/

/-- The FIPS 205 Algorithm 20 digest split, from the signature's own randomizer.

Both indices and the FORS message come from this one value, so the FORS instance a signature is
checked against is chosen by the signature, not by the caller. -/
def schemeParts (vp : ValidatedParams) (prims : Primitives vp.params) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (pk : PublicKeyCore prims.core) :
    DigestParts vp.params :=
  splitDigest vp.params (prims.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg)

/-- Unfolding equation for `schemeParts`. -/
@[simp] theorem schemeParts_eq (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core)
    (pk : PublicKeyCore prims.core) :
    schemeParts vp prims msg sig pk =
      splitDigest vp.params (prims.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg) := by rfl

/-! ## The scheme-level dichotomy -/

/-- **The dispatch.**  A signature that verifies against a public key either recovers, at the FORS
address its own digest names, the FORS public key the secret seed generates there, or it does not —
and then its hypertree half carries the value it *did* recover all the way to the published root.

The recovered-root equation is not special to the second branch — it follows from `hverify` alone,
through `verifyInternal_eq_decide` — and it is stated there because that is the branch which
consumes it.  Nothing is hidden by the placement.

Neither `sk` nor `pk` is constrained: the statement holds for any secret seed and any public key the
verifier accepted, and the honest identification `pk.pkRoot = GeneralHypertree.root vp prims sk
pk.pkSeed` is not a hypothesis.  A consumer supplies it where the second branch is used, because it
is what turns the recovered-root equation into the layer walk's own hypothesis through
`recoverFromPosition_of_pkFromSig`; `findWitness_isSome` is that consumer.

*Deterministic inclusion.* -/
theorem verifyInternal_cases [DecidableEq prims.Y] (sk : prims.SkSeed) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (pk : PublicKeyCore prims.core)
    (hverify : GeneralScheme.verifyInternal vp prims msg sig pk = true) :
    (forsPkFromSig prims sig.fors (schemeParts vp prims msg sig pk).md.toList pk.pkSeed
        (schemeParts vp prims msg sig pk).forsAdrs =
      forsPkGen prims sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs) ∨
    (forsPkFromSig prims sig.fors (schemeParts vp prims msg sig pk).md.toList pk.pkSeed
        (schemeParts vp prims msg sig pk).forsAdrs ≠
      forsPkGen prims sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs ∧
     pkFromSig vp prims
        (forsPkFromSig prims sig.fors (schemeParts vp prims msg sig pk).md.toList pk.pkSeed
          (schemeParts vp prims msg sig pk).forsAdrs)
        sig.hypertree pk.pkSeed (schemeParts vp prims msg sig pk) = pk.pkRoot) := by
  rw [GeneralScheme.verifyInternal_eq_decide, decide_eq_true_eq] at hverify
  rw [schemeParts_eq]
  by_cases h : forsPkFromSig prims sig.fors
      (splitDigest vp.params (prims.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg)).md.toList
      pk.pkSeed
      (splitDigest vp.params (prims.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg)).forsAdrs =
    forsPkGen prims sk pk.pkSeed
      (splitDigest vp.params (prims.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg)).forsAdrs
  · exact Or.inl h
  · exact Or.inr ⟨h, hverify⟩

/-! ## The composite witness -/

/-- A witness against one SLH-DSA component hash, in whichever of the two families the signature's
own FORS public key routes it to.

The two arms carry the merged witness types unchanged.  There is no arm for `H_msg`: an
interleaved-target-subset-resilience win is not a witness against a component tweak — its witness is
the forged randomizer-message pair itself, and its winning condition is a statement about a signing
transcript, which `Witness.Valid` has no argument for. -/
inductive Witness (vp : ValidatedParams) (prims : Primitives vp.params) where
  /-- A FORS witness at the instance address the signature's digest names. -/
  | fors (w : ForsWitness vp.params prims)
  /-- A hypertree witness on the full-depth walk from the layer-zero position that digest names. -/
  | hypertree (w : HypertreeWitness vp prims vp.params.d)

/-- The winning condition a composite witness asserts, against the honest key material that `sk`
generates under the public seed `pk.pkSeed`, at the digest the signature produces against `pk`.

The two arms are the merged predicates at arguments this predicate computes:

* `fors w` asserts `w`'s own condition at the FORS instance address `(schemeParts …).forsAdrs` and
  the FORS message `(schemeParts …).md`;
* `hypertree w` asserts `w`'s own condition on the walk of `vp.params.d` layers from
  `LayerPosition.initial vp (schemeParts …)`, whose honest starting message is
  `forsPkGen prims sk pk.pkSeed (schemeParts …).forsAdrs` — the honest FORS public key at that
  bottom position, computed from `sk` here rather than read off any signature.

`pk` is taken whole rather than as a seed, because both of its components enter: `pk.pkSeed` is the
public seed the honest key material is generated under, and `pk.pkRoot` is one of the four inputs
`H_msg` forms the digest from.  The published root is not an honest object a witness attacks, in the
way `idx` and the forged message are not attacked objects of `XmssWitness.Valid`; it is a forged
input to the digest.

There are no conjuncts of the composite's own.  Every conjunct a consumer meets belongs to a merged
predicate, and each merged module's canaries falsify its own; what this predicate adds is the
*arguments* each arm is evaluated at, which `HashSigTest.SLHDSA.SchemeWitnesses` falsifies by
re-evaluating every extracted witness at the other forgery site.  The arm selection is a property of
`findWitness` and not of this predicate — this predicate reads a signature only through the digest,
so at two signatures sharing a randomizer and a message it cannot separate the arms at all, and that
fixture exhibits exactly such a pair, taking different arms, with each one's witness valid against
the other.

This is a statement about hash values and computed honest partners only.  It does not say that any
honest object it names was committed as a game target, that any execution queried one, that the
message was never signed, or — in the FORS `fPreimage` case — that the named leaf index was never
opened. -/
def Witness.Valid (sk : prims.SkSeed) (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) : Witness vp prims → Prop
  | .fors w =>
      w.Valid sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs
        (schemeParts vp prims msg sig pk).md.toList
  | .hypertree w =>
      w.Valid sk pk.pkSeed (LayerPosition.initial vp (schemeParts vp prims msg sig pk))
        (forsPkGen prims sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs) vp.params.d
        (by simp)

/-- Unfolding equation for the FORS arm.  The address and the FORS message are the digest's own. -/
@[simp] theorem Witness.valid_fors (sk : prims.SkSeed) (pk : PublicKeyCore prims.core)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core)
    (w : ForsWitness vp.params prims) :
    (Witness.fors w).Valid sk pk msg sig ↔
      w.Valid sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs
        (schemeParts vp prims msg sig pk).md.toList := Iff.rfl

/-- Unfolding equation for the hypertree arm.  The honest starting message is the honest FORS public
key at the digest's bottom position, read off the honest tree rather than supplied. -/
@[simp] theorem Witness.valid_hypertree (sk : prims.SkSeed) (pk : PublicKeyCore prims.core)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core)
    (w : HypertreeWitness vp prims vp.params.d) :
    (Witness.hypertree w).Valid sk pk msg sig ↔
      w.Valid sk pk.pkSeed (LayerPosition.initial vp (schemeParts vp prims msg sig pk))
        (forsPkGen prims sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs) vp.params.d
        (by simp) := Iff.rfl

/-! ## The extractor -/

/-- Compute a composite witness from a signature, a message, a public key and the honest secret
seed: the FORS extractor when the recovered FORS public key is the honest one at the digest's
address, and the layer walk otherwise.

The guard is the equality `verifyInternal_cases` splits on, recomputed here from `sk`; nothing about
the signature's validity is tested, and the caller's `hverify` enters only through
`findWitness_isSome`.  The FORS branch is total, so it returns `some`; the hypertree branch is not,
because the layer walk returns nothing when no layer's recovered root is that layer's honest root
and when the XMSS search finds nothing at the layer that matches.  A total dispatch would have to
invent a witness for those cases, so the result is an `Option` and `findWitness_isSome` closes it.

`target` is passed to `findForsWitness` unchanged; as that module records, it is honoured on the
`fPreimage` branch alone. -/
def findWitness [DecidableEq prims.Y] (sk : prims.SkSeed) (pk : PublicKeyCore prims.core)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core)
    (target : Fin vp.params.k) : Option (Witness vp prims) :=
  if forsPkFromSig prims sig.fors (schemeParts vp prims msg sig pk).md.toList pk.pkSeed
        (schemeParts vp prims msg sig pk).forsAdrs =
      forsPkGen prims sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs then
    some (.fors (findForsWitness prims sig.fors (schemeParts vp prims msg sig pk).md.toList sk
      pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs target))
  else
    (findHypertreeWitness vp prims sk pk.pkSeed
      (LayerPosition.initial vp (schemeParts vp prims msg sig pk)) vp.params.d (by simp)
      (forsPkFromSig prims sig.fors (schemeParts vp prims msg sig pk).md.toList pk.pkSeed
        (schemeParts vp prims msg sig pk).forsAdrs)
      (forsPkGen prims sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs)
      sig.hypertree).map .hypertree

/-- The FORS arm fires exactly when the recovered FORS public key is the honest one there.  The body
is not exposed, so this equation is what a consumer rewrites with. -/
theorem findWitness_eq_fors_of_pk [DecidableEq prims.Y] (sk : prims.SkSeed)
    (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (target : Fin vp.params.k)
    (hpk : forsPkFromSig prims sig.fors (schemeParts vp prims msg sig pk).md.toList pk.pkSeed
        (schemeParts vp prims msg sig pk).forsAdrs =
      forsPkGen prims sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs) :
    findWitness sk pk msg sig target =
      some (.fors (findForsWitness prims sig.fors (schemeParts vp prims msg sig pk).md.toList sk
        pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs target)) := by
  rw [findWitness, if_pos hpk]

/-- And the hypertree arm fires exactly when it is not, on the full-depth walk from the digest's
layer-zero position between the recovered FORS public key and the honest one. -/
theorem findWitness_eq_hypertree_of_ne [DecidableEq prims.Y] (sk : prims.SkSeed)
    (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (target : Fin vp.params.k)
    (hpk : forsPkFromSig prims sig.fors (schemeParts vp prims msg sig pk).md.toList pk.pkSeed
        (schemeParts vp prims msg sig pk).forsAdrs ≠
      forsPkGen prims sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs) :
    findWitness sk pk msg sig target =
      (findHypertreeWitness vp prims sk pk.pkSeed
        (LayerPosition.initial vp (schemeParts vp prims msg sig pk)) vp.params.d (by simp)
        (forsPkFromSig prims sig.fors (schemeParts vp prims msg sig pk).md.toList pk.pkSeed
          (schemeParts vp prims msg sig pk).forsAdrs)
        (forsPkGen prims sk pk.pkSeed (schemeParts vp prims msg sig pk).forsAdrs)
        sig.hypertree).map .hypertree := by
  rw [findWitness, if_neg hpk]

/-- **Extractor soundness.**  Whatever `findWitness` returns satisfies `Witness.Valid` against the
honest key material at `pk.pkSeed` and the digest the signature produces against `pk`.

There is no verification hypothesis and no root hypothesis, and `pk` is arbitrary.  Each arm's
guard is the hypothesis its own extractor takes: the FORS arm's is the public-key equality this
extractor tests, and the hypertree arm's are the per-layer root matches `findHypertreeWitness`
tests, which is why `findHypertreeWitness_sound` needs none.  The intended instantiation is the
honest key pair `⟨pkSeed, GeneralHypertree.root vp prims sk pkSeed⟩`, at which `findWitness_isSome`
also applies; nothing here requires it.

*Deterministic inclusion.* -/
theorem findWitness_sound [DecidableEq prims.Y] (sk : prims.SkSeed)
    (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (target : Fin vp.params.k)
    {w : Witness vp prims} (hw : findWitness sk pk msg sig target = some w) :
    w.Valid sk pk msg sig := by
  rw [findWitness] at hw
  split at hw
  · rename_i hpk
    rw [Option.some.injEq] at hw
    subst hw
    rw [Witness.valid_fors]
    exact findForsWitness_sound prims sig.fors _ sk pk.pkSeed _ target hpk
  · rw [Option.map_eq_some_iff] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [Witness.valid_hypertree]
    exact findHypertreeWitness_sound vp prims sk pk.pkSeed _ vp.params.d (by simp) _ _ _ hu

/-- **Extractor completeness.**  Against the honest public key, every signature that verifies yields
a witness.

The FORS arm is total, so the public-key match returns `some` outright.  On the mismatch,
`verifyInternal_cases` supplies both hypotheses the layer walk needs: the disequality is the walk's
two distinct messages, and the recovered-root equation becomes `recoverFromPosition`'s through
`recoverFromPosition_of_pkFromSig`, which is where the honest identification of the published root
is used.  The byte laws are `findXmssWitness_isSome`'s argument for its WOTS+ half.

*Deterministic inclusion.* -/
theorem findWitness_isSome [DecidableEq prims.Y] (laws : prims.core.ByteLaws) (sk : prims.SkSeed)
    (pkSeed : prims.PkSeed) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (target : Fin vp.params.k)
    (hverify : GeneralScheme.verifyInternal vp prims msg sig
      ⟨pkSeed, GeneralHypertree.root vp prims sk pkSeed⟩ = true) :
    (findWitness sk ⟨pkSeed, GeneralHypertree.root vp prims sk pkSeed⟩ msg sig target).isSome := by
  rcases verifyInternal_cases sk msg sig ⟨pkSeed, root vp prims sk pkSeed⟩ hverify with hpk | hpk
  · rw [findWitness_eq_fors_of_pk sk _ msg sig target hpk]
    exact Option.isSome_some
  · rw [findWitness_eq_hypertree_of_ne sk _ msg sig target hpk.1, Option.isSome_map]
    exact findHypertreeWitness_isSome vp prims laws sk pkSeed _ vp.params.d (by simp) _ _ hpk.1 _
      (recoverFromPosition_of_pkFromSig vp prims sk pkSeed _ _ _ hpk.2)

/-! ## Ledger membership at the digest-derived FORS address

*Transcript transport.*  The three FORS ledger lemmas are stated at a `BottomPosition`; the FORS
arm's addresses are rooted at a `DigestParts`.  These three are that identification, and nothing
else. -/

/-- The FORS leaf address a digest names in tree `i` is a listed `forsF` target. -/
theorem mem_forsLeafAddresses_of_parts (parts : DigestParts vp.params) (md : List Byte)
    (i : Fin vp.params.k) :
    forsNodeAdrs parts.forsAdrs 0 (forsSigLeafIndex vp.params md i.val) ∈
      forsLeafAddresses vp := by
  rw [← BottomPosition.forsAdrs_ofDigestParts vp parts]
  exact mem_forsLeafAddresses_of_digest (BottomPosition.ofDigestParts vp parts) md i

/-- Every internal node of height `0 < z ≤ a` on the root path of the leaf a digest names in tree
`i` is a listed `forsH` target. -/
theorem mem_forsTreeAddresses_of_parts (parts : DigestParts vp.params) (md : List Byte)
    (i : Fin vp.params.k) {z : ℕ} (hz : 0 < z) (hza : z ≤ vp.params.a) :
    forsNodeAdrs parts.forsAdrs z (forsSigLeafIndex vp.params md i.val / 2 ^ z) ∈
      forsTreeAddresses vp := by
  rw [← BottomPosition.forsAdrs_ofDigestParts vp parts]
  exact mem_forsTreeAddresses_of_digest (BottomPosition.ofDigestParts vp parts) md i hz hza

/-- The FORS root-compression address a digest names is a listed `forsTl` target. -/
theorem mem_forsRootAddresses_of_parts (parts : DigestParts vp.params) :
    forsPkAdrs parts.forsAdrs ∈ forsRootAddresses vp := by
  rw [← BottomPosition.forsAdrs_ofDigestParts vp parts]
  exact mem_forsRootAddresses vp (BottomPosition.ofDigestParts vp parts)

/-! ## Encoded distinctness at the digest-derived FORS address

*Transcript transport.*  Two forgeries attack the same encoded FORS tweak only if their digests
name the same bottom position and the same coordinate inside it.  Each of the three is the
corresponding `ForsWitnesses` lemma read through `BottomPosition.forsAdrs_ofDigestParts`, with the
digest's two indices recovered from the resulting position equality. -/

/-- Read the two digest indices back out of a typed bottom position.  `BottomPosition.ofDigestParts`
is not exposed, so this goes through the `forsAdrs` projection equations of both records. -/
private theorem digestParts_ext_of_bottom {parts parts' : DigestParts vp.params}
    (h : BottomPosition.ofDigestParts vp parts = BottomPosition.ofDigestParts vp parts') :
    parts.idxTree = parts'.idxTree ∧ parts.idxLeaf = parts'.idxLeaf := by
  have htree := congrArg (fun q : BottomPosition vp => q.forsAdrs.tree) h
  have hleaf := congrArg (fun q : BottomPosition vp => q.forsAdrs.getKeyPairAddress) h
  simp only [BottomPosition.forsAdrs_ofDigestParts, DigestParts.forsAdrs_tree,
    DigestParts.forsAdrs_keyPair] at htree hleaf
  exact ⟨Fin.ext htree, Fin.ext hleaf⟩

/-- Under the encoded-ledger conditions, two FORS leaf targets named by two digests carry equal
encoded tweaks only when the two digests agree on both indices, the two FORS trees agree, and the
two local leaves agree. -/
theorem forsLeafAdrsKey_injective_of_parts
    (conditions : EncodedTargetLedgerConditions vp prims)
    {parts parts' : DigestParts vp.params} {md md' : List Byte} {i i' : Fin vp.params.k}
    (hkey : prims.adrsToKey (forsNodeAdrs parts.forsAdrs 0 (forsSigLeafIndex vp.params md i.val)) =
      prims.adrsToKey (forsNodeAdrs parts'.forsAdrs 0 (forsSigLeafIndex vp.params md' i'.val))) :
    parts.idxTree = parts'.idxTree ∧ parts.idxLeaf = parts'.idxLeaf ∧ i = i' ∧
      forsIdx vp.params md i.val = forsIdx vp.params md' i'.val := by
  have hb : forsIdx vp.params md i.val < vp.params.t := forsIdx_lt vp.params md i.val
  have hb' : forsIdx vp.params md' i'.val < vp.params.t := forsIdx_lt vp.params md' i'.val
  have hshape : ∀ (q : DigestParts vp.params) (n : List Byte) (j : Fin vp.params.k),
      forsNodeAdrs q.forsAdrs 0 (forsSigLeafIndex vp.params n j.val) =
        forsNodeAdrs (BottomPosition.ofDigestParts vp q).forsAdrs 0
          (j.val * vp.params.t + forsIdx vp.params n j.val) := by
    intro q n j
    rw [BottomPosition.forsAdrs_ofDigestParts, forsSigLeafIndex_eq]
    rfl
  rw [hshape parts md i, hshape parts' md' i'] at hkey
  have hcoord := forsLeafAdrsKey_injective (vp := vp) conditions
    (a₁ := ((BottomPosition.ofDigestParts vp parts, i), ⟨forsIdx vp.params md i.val, hb⟩))
    (a₂ := ((BottomPosition.ofDigestParts vp parts', i'), ⟨forsIdx vp.params md' i'.val, hb'⟩))
    hkey
  simp only [Prod.mk.injEq, Fin.mk.injEq] at hcoord
  obtain ⟨htree, hleaf⟩ := digestParts_ext_of_bottom hcoord.1.1
  exact ⟨htree, hleaf, hcoord.1.2, hcoord.2⟩

/-- Under the encoded-ledger conditions, two FORS internal-node targets named by two digests carry
equal encoded tweaks only when the two digests agree on both indices, the two FORS trees agree, the
two heights agree, and the two node indices inside the tree agree. -/
theorem forsTreeAdrsKey_injective_of_parts
    (conditions : EncodedTargetLedgerConditions vp prims)
    {parts parts' : DigestParts vp.params} {md md' : List Byte} {i i' : Fin vp.params.k}
    {z z' : ℕ} (hz : 0 < z) (hza : z ≤ vp.params.a) (hz' : 0 < z') (hza' : z' ≤ vp.params.a)
    (hkey : prims.adrsToKey
        (forsNodeAdrs parts.forsAdrs z (forsSigLeafIndex vp.params md i.val / 2 ^ z)) =
      prims.adrsToKey
        (forsNodeAdrs parts'.forsAdrs z' (forsSigLeafIndex vp.params md' i'.val / 2 ^ z'))) :
    parts.idxTree = parts'.idxTree ∧ parts.idxLeaf = parts'.idxLeaf ∧ i = i' ∧ z = z' ∧
      forsIdx vp.params md i.val / 2 ^ z = forsIdx vp.params md' i'.val / 2 ^ z' := by
  obtain ⟨heq, hlt⟩ := forsSigLeafIndex_div_lt vp.params md i.val z hza
  obtain ⟨heq', hlt'⟩ := forsSigLeafIndex_div_lt vp.params md' i'.val z' hza'
  rw [heq, heq', ← BottomPosition.forsAdrs_ofDigestParts vp parts,
    ← BottomPosition.forsAdrs_ofDigestParts vp parts'] at hkey
  have hcoord := forsTreeAdrsKey_injective (vp := vp) conditions hz hza hlt hz' hza' hlt' hkey
  obtain ⟨htree, hleaf⟩ := digestParts_ext_of_bottom hcoord.1
  exact ⟨htree, hleaf, hcoord.2.1, hcoord.2.2.1, hcoord.2.2.2⟩

/-- Under the encoded-ledger conditions, two FORS root-compression targets named by two digests
carry equal encoded tweaks only when the two digests agree on both indices. -/
theorem forsRootAdrsKey_injective_of_parts
    (conditions : EncodedTargetLedgerConditions vp prims)
    {parts parts' : DigestParts vp.params}
    (hkey : prims.adrsToKey (forsPkAdrs parts.forsAdrs) =
      prims.adrsToKey (forsPkAdrs parts'.forsAdrs)) :
    parts.idxTree = parts'.idxTree ∧ parts.idxLeaf = parts'.idxLeaf := by
  rw [← BottomPosition.forsAdrs_ofDigestParts vp parts,
    ← BottomPosition.forsAdrs_ofDigestParts vp parts'] at hkey
  exact digestParts_ext_of_bottom (forsRootAdrsKey_injective (vp := vp) conditions hkey)

end SLHDSA.Security
