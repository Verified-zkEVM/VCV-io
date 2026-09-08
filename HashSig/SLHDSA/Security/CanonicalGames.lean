/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security
public import HashSig.SLHDSA.Security.TargetCounts
public import HashSig.SLHDSA.Fors
public import HashSig.SLHDSA.Position
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.OpenPREFromTCRDSPR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPRFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTOpenPREFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPREFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUDFinalValidity

/-!
# Canonical SLH-DSA component games

This module instantiates VCVio's generic source-final-validity tweakable-hash games and the
keyed-hash ITSR game with the SLH-DSA primitive families of `HashSig.SLHDSA.Security`, the
encoded-address tweak space `Primitives.AdrsKey`, and the formula-derived target caps
`targetCount` of `HashSig.SLHDSA.Security.TargetCounts`.

The game assignments are:

* standalone SM-DT-OpenPRE for FORS `F`, together with the standalone SM-DT-DSPR and SM-DT-TCR
  games attacked by the library's OpenPRE-to-DSPR and OpenPRE-to-TCR reductions (`Problem.toDSPR`
  and `Problem.toTCR`; the quantitative bound relating them is conditional on
  `SM_DT_OpenPRE_SourceFinalValidity.CountingInterface`), all at the target cap
  `targetCount p .forsF`;
* collection SM-DT-TCR for FORS `H`, FORS `T_k`, WOTS+ `F`, WOTS+ `T_len`, and XMSS `H`;
* collection SM-DT-UD and SM-DT-PRE for WOTS+ `F`, sampling the hidden input uniformly from the
  whole node type; and
* keyed-hash ITSR for `H_msg`, keyed by the message randomizer.

Every tweakable-hash game takes `Primitives.AdrsKey` as its tweak and uses the source
final-validity presentation of the EasyCrypt development rather than the rejection-on-arrival one;
its target cap is `targetCount p role`.  The seven collection games take
`Primitives.thashCollection` as their collection oracle; the three FORS-`F` games are standalone
(`Problem.standalone`, empty collection), as are the source's `FP_OpenPRE`, `FP_DSPR`, and `FP_TCR`
clones.  This module constructs no reductions and states no inequality.

## Exposure

The seven collection problems are `@[expose]`d because a downstream adversary's collection query
carries a `Vector prims.Y arity` at type `(problem).thColl.Msg arity`, which type-checks directly
only when the record body is available (an opaque record would force a `cast` along a `thColl.Msg`
projection equation into every collection query and every reduction's oracle simulation).  The
three standalone problems, the `H_msg` keyed family, the ITSR problem, and `hmsgIndices` are opaque
and are consumed through exported equations such as `*_th`, `*_thColl`, `*_inputGen`,
`*_numTargets`, `*_eq_toDSPR`/`*_eq_toTCR`, `hmsgKeyedHash_*`, `hmsgItsrProblem_*`,
`hmsgIndices_length`, and `mem_hmsgIndices`.

## Follow-ups

The `T_ℓ` collection problems `forsTlTcrCProblem` and `wotsTlTcrCProblem` coincide structurally
with `(prims.thashTcrProblem arity cap).toSourceFinalValidity`, the source-final-validity image of
the reject-on-arrival problem packaged by `HashSig.SLHDSA.Security`.  That tie is not provable from
`HashSig` today: `SM_DT_TCR_Problem.toSourceFinalValidity` is `@[reducible]` but not exposed and
VCVio exports no projection lemmas for it, so neither `rfl` nor a propositional proof goes through
across the module boundary.  Once VCVio exposes or provides projection lemmas for
`SM_DT_TCR_Problem.toSourceFinalValidity` and `SM_DT_PRE_Problem.toSourceFinalValidity`, state
`forsTlTcrCProblem_eq_toSourceFinalValidity` and `wotsTlTcrCProblem_eq_toSourceFinalValidity` here
so the `SM_DT_TCR_advantage_toSourceFinalValidity` theorems transfer to these games.

## References

- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified"
- NIST FIPS 205, §4.1 (the hash roles), §5 (WOTS+ chains), §8 (FORS), §9 (`H_msg` and the digest
  split)
-/

public section

open CollisionResistance OracleComp OracleSpec ENNReal

namespace SLHDSA.Security.CanonicalGames

variable {p : Params} (prims : Primitives p)

/-! ## Primitive evaluation bridges -/

/-- The `F` family evaluates the one-input member of `Thash` at an encoded address. -/
@[simp]
theorem fHash_eval [SampleableType prims.PkSeed] (pkSeed : prims.PkSeed)
    (tweak : prims.AdrsKey) (input : prims.Y) :
    (prims.fHash).eval pkSeed tweak input = prims.Thash pkSeed tweak [input] := rfl

/-- The `H` family evaluates the ordered two-input member of `Thash`. -/
@[simp]
theorem hHash_eval [SampleableType prims.PkSeed] (pkSeed : prims.PkSeed)
    (tweak : prims.AdrsKey) (input : prims.Y × prims.Y) :
    (prims.hHash).eval pkSeed tweak input =
      prims.Thash pkSeed tweak [input.1, input.2] := rfl

/-- A fixed-arity collection member evaluates `Thash` on exactly the vector's entries. -/
@[simp]
theorem thashMember_eval [SampleableType prims.PkSeed] (arity : ℕ)
    (pkSeed : prims.PkSeed) (tweak : prims.AdrsKey) (input : Vector prims.Y arity) :
    (prims.thashMember arity).eval pkSeed tweak input =
      prims.Thash pkSeed tweak input.toList := rfl

/-! ## FORS games -/

/-- FORS-`F` open preimage resistance with no collection oracle and uniformly sampled target
inputs.  Its cap is the FORS leaf count `2 ^ h * k * 2 ^ a`. -/
def forsFOpenPreProblem [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey
      prims.Y prims.Y :=
  .standalone prims.fHash ($ᵗ prims.Y) (targetCount p .forsF)

/-- FORS-`F` decisional second-preimage resistance with no collection oracle. -/
def forsFDsprProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_DSPR_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey
      prims.Y prims.Y :=
  .standalone prims.fHash (targetCount p .forsF)

/-- FORS-`F` target-collision resistance with no collection oracle. -/
def forsFTcrProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey
      prims.Y prims.Y :=
  .standalone prims.fHash (targetCount p .forsF)

/-- FORS-`H` target-collision resistance in the shared `Thash` collection. -/
-- Exposed: a downstream adversary's collection query is typed at `thColl.Msg arity`.
@[expose] def forsHTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (prims.Y × prims.Y) prims.Y where
  th := prims.hHash
  thColl := prims.thashCollection
  numTargets := targetCount p .forsH

/-- FORS-`T_k` target-collision resistance at arity `p.k` in the shared collection. -/
-- Exposed: a downstream adversary's collection query is typed at `thColl.Msg arity`.
@[expose] def forsTlTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y p.k) prims.Y where
  th := prims.thashMember p.k
  thColl := prims.thashCollection
  numTargets := targetCount p .forsTl

/-! ## WOTS+ and XMSS games -/

/-- WOTS+-`F` undetectability in the shared collection.  The hidden input is sampled uniformly
from the whole node type and the ideal response uniformly from the output type: FIPS 205
Algorithm 5 feeds `F` an `n`-byte node, so the subspace parameter is the node type itself. -/
-- Exposed: a downstream adversary's collection query is typed at `thColl.Msg arity`.
@[expose] def wotsFUdCProblem [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    TweakableHash.SM_DT_UD_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      prims.Y prims.Y prims.Y where
  th := prims.fHash
  emb := id
  emb_injective := Function.injective_id
  inputGen := $ᵗ prims.Y
  outputGen := $ᵗ prims.Y
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsFUd

/-- WOTS+-`F` target-collision resistance in the shared collection. -/
-- Exposed: a downstream adversary's collection query is typed at `thColl.Msg arity`.
@[expose] def wotsFTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      prims.Y prims.Y where
  th := prims.fHash
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsFTcr

/-- WOTS+-`F` preimage resistance in the shared collection, sampling over the whole node type. -/
-- Exposed: a downstream adversary's collection query is typed at `thColl.Msg arity`.
@[expose] def wotsFPreCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_PRE_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      prims.Y prims.Y prims.Y where
  th := prims.fHash
  emb := id
  emb_injective := Function.injective_id
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsFPre

/-- WOTS+-`T_len` target-collision resistance at arity `p.len` in the shared collection. -/
-- Exposed: a downstream adversary's collection query is typed at `thColl.Msg arity`.
@[expose] def wotsTlTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y p.len) prims.Y where
  th := prims.thashMember p.len
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsTl

/-- XMSS-`H` target-collision resistance in the shared collection. -/
-- Exposed: a downstream adversary's collection query is typed at `thColl.Msg arity`.
@[expose] def xmssHTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (prims.Y × prims.Y) prims.Y where
  th := prims.hHash
  thColl := prims.thashCollection
  numTargets := targetCount p .xmssH

/-! ## Standalone-game field equations

The three FORS-`F` problems are opaque; these equations are their public interface. -/

/-- The FORS-`F` open-preimage game attacks the `F` family. -/
@[simp]
theorem forsFOpenPreProblem_th [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    (forsFOpenPreProblem prims).th = prims.fHash := by rfl

/-- The FORS-`F` open-preimage game samples target inputs uniformly from the node type. -/
@[simp]
theorem forsFOpenPreProblem_inputGen [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    (forsFOpenPreProblem prims).inputGen = $ᵗ prims.Y := by rfl

/-- The FORS-`F` open-preimage game has no collection oracle. -/
@[simp]
theorem forsFOpenPreProblem_thColl [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    (forsFOpenPreProblem prims).thColl =
      TweakableHashCollection.empty prims.PkSeed prims.AdrsKey prims.Y := by rfl

/-- The FORS-`F` DSPR game attacks the `F` family. -/
@[simp]
theorem forsFDsprProblem_th [SampleableType prims.PkSeed] :
    (forsFDsprProblem prims).th = prims.fHash := by rfl

/-- The FORS-`F` DSPR game has no collection oracle. -/
@[simp]
theorem forsFDsprProblem_thColl [SampleableType prims.PkSeed] :
    (forsFDsprProblem prims).thColl =
      TweakableHashCollection.empty prims.PkSeed prims.AdrsKey prims.Y := by rfl

/-- The FORS-`F` TCR game attacks the `F` family. -/
@[simp]
theorem forsFTcrProblem_th [SampleableType prims.PkSeed] :
    (forsFTcrProblem prims).th = prims.fHash := by rfl

/-- The FORS-`F` TCR game has no collection oracle. -/
@[simp]
theorem forsFTcrProblem_thColl [SampleableType prims.PkSeed] :
    (forsFTcrProblem prims).thColl =
      TweakableHashCollection.empty prims.PkSeed prims.AdrsKey prims.Y := by rfl

/-! ## Target-cap bridges -/

/-- The FORS-`F` open-preimage cap is `targetCount p .forsF`. -/
@[simp]
theorem forsFOpenPreProblem_numTargets [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    (forsFOpenPreProblem prims).numTargets = targetCount p .forsF := by rfl

/-- The FORS-`F` DSPR cap is `targetCount p .forsF`. -/
@[simp]
theorem forsFDsprProblem_numTargets [SampleableType prims.PkSeed] :
    (forsFDsprProblem prims).numTargets = targetCount p .forsF := by rfl

/-- The FORS-`F` TCR cap is `targetCount p .forsF`. -/
@[simp]
theorem forsFTcrProblem_numTargets [SampleableType prims.PkSeed] :
    (forsFTcrProblem prims).numTargets = targetCount p .forsF := by rfl

/-- The FORS-`H` TCR cap is `targetCount p .forsH`. -/
@[simp]
theorem forsHTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (forsHTcrCProblem prims).numTargets = targetCount p .forsH := rfl

/-- The FORS-`T_k` TCR cap is `targetCount p .forsTl`. -/
@[simp]
theorem forsTlTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (forsTlTcrCProblem prims).numTargets = targetCount p .forsTl := rfl

/-- The WOTS+-`F` undetectability cap is `targetCount p .wotsFUd`. -/
@[simp]
theorem wotsFUdCProblem_numTargets [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    (wotsFUdCProblem prims).numTargets = targetCount p .wotsFUd := rfl

/-- The WOTS+-`F` TCR cap is `targetCount p .wotsFTcr`. -/
@[simp]
theorem wotsFTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (wotsFTcrCProblem prims).numTargets = targetCount p .wotsFTcr := rfl

/-- The WOTS+-`F` preimage cap is `targetCount p .wotsFPre`. -/
@[simp]
theorem wotsFPreCProblem_numTargets [SampleableType prims.PkSeed] :
    (wotsFPreCProblem prims).numTargets = targetCount p .wotsFPre := rfl

/-- The WOTS+-`T_len` TCR cap is `targetCount p .wotsTl`. -/
@[simp]
theorem wotsTlTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (wotsTlTcrCProblem prims).numTargets = targetCount p .wotsTl := rfl

/-- The XMSS-`H` TCR cap is `targetCount p .xmssH`. -/
@[simp]
theorem xmssHTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (xmssHTcrCProblem prims).numTargets = targetCount p .xmssH := rfl

/-! ## Distributional instances -/

/-- The FORS-`F` open-preimage game samples its target inputs uniformly, which is the hypothesis
recorded by `SM_DT_OpenPRE_SourceFinalValidity.CountingInterface`. -/
theorem forsFOpenPreProblem_hasUniformInputs [SampleableType prims.PkSeed]
    [SampleableType prims.Y] : (forsFOpenPreProblem prims).HasUniformInputs := by rfl

/-- The WOTS+-`F` undetectability game draws its hidden input uniformly from the node type. -/
theorem wotsFUdCProblem_hasUniformInputs [SampleableType prims.PkSeed]
    [SampleableType prims.Y] : (wotsFUdCProblem prims).HasUniformInputs := rfl

/-- The WOTS+-`F` undetectability game's ideal response is uniform on the node type. -/
theorem wotsFUdCProblem_hasUniformOutputs [SampleableType prims.PkSeed]
    [SampleableType prims.Y] : (wotsFUdCProblem prims).HasUniformOutputs := rfl

/-! ## Game identities

The library's OpenPRE-to-DSPR and OpenPRE-to-TCR reductions attack the DSPR and TCR games at the
same attacked member, collection, and cap as the OpenPRE game they start from
(`Problem.toDSPR`, `Problem.toTCR`); the two standalone problems above are those induced games.
The quantitative bound `OpenPRE ≤ (DSPR − SPprob) + 3·TCR` is conditional on
`SM_DT_OpenPRE_SourceFinalValidity.CountingInterface` and is not stated here.  Downstream, a
hypothesis quantified over adversaries against `forsFDsprProblem prims` transports to
`(forsFOpenPreProblem prims).toDSPR` along these equations. -/

/-- The FORS-`F` DSPR game is the one the OpenPRE-to-DSPR reduction attacks. -/
theorem forsFDsprProblem_eq_toDSPR [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    forsFDsprProblem prims = (forsFOpenPreProblem prims).toDSPR := by rfl

/-- The FORS-`F` TCR game is the one the OpenPRE-to-TCR reduction attacks. -/
theorem forsFTcrProblem_eq_toTCR [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    forsFTcrProblem prims = (forsFOpenPreProblem prims).toTCR := by rfl

/-! ## Attacked-member bridges -/

/-- The WOTS+-`F` preimage game attacks the construction's own encoded-address `F` evaluation. -/
@[simp]
theorem wotsFPreCProblem_eval_adrsToKey [SampleableType prims.PkSeed]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : prims.Y) :
    (wotsFPreCProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.F pkSeed address input := rfl

/-- The WOTS+-`F` undetectability game attacks the construction's own `F` evaluation. -/
@[simp]
theorem wotsFUdCProblem_eval_adrsToKey [SampleableType prims.PkSeed] [SampleableType prims.Y]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : prims.Y) :
    (wotsFUdCProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.F pkSeed address input := rfl

/-- The FORS-`F` open-preimage game attacks the construction's own `F` evaluation. -/
theorem forsFOpenPreProblem_eval_adrsToKey [SampleableType prims.PkSeed] [SampleableType prims.Y]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : prims.Y) :
    (forsFOpenPreProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.F pkSeed address input := by rfl

/-- The FORS-`H` game uses the construction's ordered left/right node evaluation. -/
@[simp]
theorem forsHTcrCProblem_eval_adrsToKey [SampleableType prims.PkSeed]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : prims.Y × prims.Y) :
    (forsHTcrCProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.H pkSeed address input.1 input.2 := rfl

/-- The XMSS-`H` game uses the construction's ordered left/right node evaluation. -/
@[simp]
theorem xmssHTcrCProblem_eval_adrsToKey [SampleableType prims.PkSeed]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : prims.Y × prims.Y) :
    (xmssHTcrCProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.H pkSeed address input.1 input.2 := rfl

/-- The FORS-`T_k` game fixes the collection member to the `p.k`-node root compression. -/
@[simp]
theorem forsTlTcrCProblem_eval_adrsToKey [SampleableType prims.PkSeed]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : Vector prims.Y p.k) :
    (forsTlTcrCProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.Tl pkSeed address input.toList := rfl

/-- The WOTS+-`T_len` game fixes the collection member to the `p.len`-node compression. -/
@[simp]
theorem wotsTlTcrCProblem_eval_adrsToKey [SampleableType prims.PkSeed]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : Vector prims.Y p.len) :
    (wotsTlTcrCProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.Tl pkSeed address input.toList := rfl

/-! ## `H_msg` ITSR

`H_msg(R, PK.seed, PK.root, M)` selects one leaf in each of the `k` FORS trees of one bottom-layer
FORS instance.  The ITSR key is the randomizer `R`, sampled independently for every target query,
and the hash input carries the public `H_msg` parameters together with the message at the internal
Algorithm 19/20 boundary (`signInternalM`).  A semantic index names one selected FORS leaf: the
instance by its `(idxTree, idxLeaf)` position, then the tree and the leaf within it.  In the
EasyCrypt development the ITSR index map lists, for each of the `k` trees, the triple of the
instance index, the tree number, and the leaf selected by the digest; here the flat instance index
is split into the `(idxTree, idxLeaf)` components `splitDigest` produces.  The EasyCrypt `MCO`
keyed hash takes only the message; this instantiation follows FIPS 205 Algorithm 19 and includes
`PK.seed` and `PK.root` in the input, so the assumption is on the FIPS `H_msg` and, at any fixed
`PK.seed` and `PK.root`, implies the source's. -/

/-- Public `H_msg` parameters and the internal message.  The ITSR key is the message randomizer,
sampled by the game independently of this input. -/
structure HmsgITSRInput (PkSeed Y : Type) where
  /-- `PK.seed`. -/
  pkSeed : PkSeed
  /-- `PK.root`. -/
  pkRoot : Y
  /-- The message at the internal Algorithm 19/20 boundary. -/
  request : List Byte
deriving DecidableEq

/-- One FORS leaf selected by an `H_msg` digest: the bottom-layer instance by tree and leaf
position, the FORS tree within that instance, and the leaf within that tree. -/
structure HmsgIndex (p : Params) where
  /-- The bottom-layer XMSS tree (`idx_tree`). -/
  idxTree : Fin (2 ^ (p.h - p.hp))
  /-- The leaf of that tree (`idx_leaf`), which names the FORS instance. -/
  idxLeaf : Fin (2 ^ p.hp)
  /-- The FORS tree within the instance. -/
  tree : Fin p.k
  /-- The selected leaf within that FORS tree. -/
  leaf : Fin (2 ^ p.a)
deriving DecidableEq, Repr

/-- The `k` FORS leaves selected by a digest: `splitDigest` locates the instance and `forsIdx`
reads the `i`-th base-`2^a` digit of `md` as the leaf of tree `i`. -/
def hmsgIndices (p : Params) (digest : Bytes p.m) : List (HmsgIndex p) :=
  let parts := splitDigest p digest
  (List.finRange p.k).map fun i =>
    ⟨parts.idxTree, parts.idxLeaf, i,
      ⟨forsIdx p parts.md.toList i.val, forsIdx_lt p parts.md.toList i.val⟩⟩

/-- Every digest selects exactly `k` semantic indices, one per FORS tree. -/
theorem hmsgIndices_length (p : Params) (digest : Bytes p.m) :
    (hmsgIndices p digest).length = p.k := by
  simp [hmsgIndices]

/-- Membership in a digest's index list: the index names the instance `splitDigest` locates and
its leaf is the base-`2^a` digit of `md` at its tree number.  The ITSR winning relation is
membership in `indices`, so this is the characterisation a reduction reads. -/
theorem mem_hmsgIndices (p : Params) (digest : Bytes p.m) (idx : HmsgIndex p) :
    idx ∈ hmsgIndices p digest ↔
      idx.idxTree = (splitDigest p digest).idxTree ∧
        idx.idxLeaf = (splitDigest p digest).idxLeaf ∧
        idx.leaf.val = forsIdx p (splitDigest p digest).md.toList idx.tree.val := by
  obtain ⟨t, l, i, f⟩ := idx
  simp only [hmsgIndices, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj⟩
    cases hj
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, hf⟩
    exact ⟨i, by rw [HmsgIndex.mk.injEq]; exact ⟨rfl, rfl, rfl, Fin.ext hf.symm⟩⟩

/-- `H_msg` as a keyed hash family whose key generator samples the per-message randomizer
uniformly. -/
def hmsgKeyedHash [SampleableType prims.Y] :
    KeyedHashFamily prims.Y (HmsgITSRInput prims.PkSeed prims.Y) (Bytes p.m) where
  keygen := $ᵗ prims.Y
  hash := fun randomizer input => prims.Hmsg randomizer input.pkSeed input.pkRoot input.request

/-- The `H_msg` keyed family samples its key, the randomizer, uniformly. -/
@[simp]
theorem hmsgKeyedHash_keygen [SampleableType prims.Y] :
    (hmsgKeyedHash prims).keygen = $ᵗ prims.Y := by rfl

/-- The `H_msg` keyed family hashes with the bundle's own `H_msg`. -/
@[simp]
theorem hmsgKeyedHash_hash [SampleableType prims.Y] (randomizer : prims.Y)
    (input : HmsgITSRInput prims.PkSeed prims.Y) :
    (hmsgKeyedHash prims).hash randomizer input =
      prims.Hmsg randomizer input.pkSeed input.pkRoot input.request := by rfl

/-- Generic ITSR instantiated with `H_msg` and the FIPS digest-to-FORS-leaf map. -/
def hmsgItsrProblem [SampleableType prims.Y] :
    KeyedHash.ITSRProblem prims.Y (HmsgITSRInput prims.PkSeed prims.Y) (Bytes p.m)
      (HmsgIndex p) where
  khf := hmsgKeyedHash prims
  indices := hmsgIndices p

/-- The ITSR problem's keyed family is `hmsgKeyedHash`. -/
@[simp]
theorem hmsgItsrProblem_khf [SampleableType prims.Y] :
    (hmsgItsrProblem prims).khf = hmsgKeyedHash prims := by rfl

/-- The ITSR problem hashes with the bundle's own `H_msg`. -/
theorem hmsgItsrProblem_hash [SampleableType prims.Y] (randomizer : prims.Y)
    (input : HmsgITSRInput prims.PkSeed prims.Y) :
    (hmsgItsrProblem prims).khf.hash randomizer input =
      prims.Hmsg randomizer input.pkSeed input.pkRoot input.request := by rfl

/-- The ITSR problem samples the randomizer uniformly for every target query. -/
theorem hmsgItsrProblem_keygen [SampleableType prims.Y] :
    (hmsgItsrProblem prims).khf.keygen = $ᵗ prims.Y := by rfl

/-- The ITSR problem's semantic-index map is `hmsgIndices`. -/
@[simp]
theorem hmsgItsrProblem_indices [SampleableType prims.Y] (digest : Bytes p.m) :
    (hmsgItsrProblem prims).indices digest = hmsgIndices p digest := by rfl

end SLHDSA.Security.CanonicalGames
