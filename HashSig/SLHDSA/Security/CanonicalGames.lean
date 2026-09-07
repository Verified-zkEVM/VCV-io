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
  games it reduces to (`Problem.toDSPR` and `Problem.toTCR`), all at the target cap
  `targetCount p .forsF`;
* collection SM-DT-TCR for FORS `H`, FORS `T_k`, WOTS+ `F`, WOTS+ `T_len`, and XMSS `H`;
* collection SM-DT-UD and SM-DT-PRE for WOTS+ `F`, sampling the hidden input uniformly from the
  whole node type; and
* keyed-hash ITSR for `H_msg`, keyed by the message randomizer.

Every tweakable-hash game takes `Primitives.AdrsKey` as its tweak, `Primitives.thashCollection` as
its collection oracle, and the source final-validity presentation of the EasyCrypt development
rather than the rejection-on-arrival one; its target cap is `targetCount p role`.  This module
constructs no reductions and states no inequality.

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
@[expose] def forsFOpenPreProblem [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey
      prims.Y prims.Y :=
  .standalone prims.fHash ($ᵗ prims.Y) (targetCount p .forsF)

/-- FORS-`F` decisional second-preimage resistance with no collection oracle. -/
@[expose] def forsFDsprProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_DSPR_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey
      prims.Y prims.Y :=
  .standalone prims.fHash (targetCount p .forsF)

/-- FORS-`F` target-collision resistance with no collection oracle. -/
@[expose] def forsFTcrProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey
      prims.Y prims.Y :=
  .standalone prims.fHash (targetCount p .forsF)

/-- FORS-`H` target-collision resistance in the shared `Thash` collection. -/
@[expose] def forsHTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (prims.Y × prims.Y) prims.Y where
  th := prims.hHash
  thColl := prims.thashCollection
  numTargets := targetCount p .forsH

/-- FORS-`T_k` target-collision resistance at arity `p.k` in the shared collection. -/
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
@[expose] def wotsFTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      prims.Y prims.Y where
  th := prims.fHash
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsFTcr

/-- WOTS+-`F` preimage resistance in the shared collection, sampling over the whole node type. -/
@[expose] def wotsFPreCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_PRE_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      prims.Y prims.Y prims.Y where
  th := prims.fHash
  emb := id
  emb_injective := Function.injective_id
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsFPre

/-- WOTS+-`T_len` target-collision resistance at arity `p.len` in the shared collection. -/
@[expose] def wotsTlTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y p.len) prims.Y where
  th := prims.thashMember p.len
  thColl := prims.thashCollection
  numTargets := targetCount p .wotsTl

/-- XMSS-`H` target-collision resistance in the shared collection. -/
@[expose] def xmssHTcrCProblem [SampleableType prims.PkSeed] :
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Problem ℕ prims.PkSeed prims.AdrsKey
      (prims.Y × prims.Y) prims.Y where
  th := prims.hHash
  thColl := prims.thashCollection
  numTargets := targetCount p .xmssH

/-! ## Target-cap bridges -/

@[simp]
theorem forsFOpenPreProblem_numTargets [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    (forsFOpenPreProblem prims).numTargets = targetCount p .forsF := rfl

@[simp]
theorem forsFDsprProblem_numTargets [SampleableType prims.PkSeed] :
    (forsFDsprProblem prims).numTargets = targetCount p .forsF := rfl

@[simp]
theorem forsFTcrProblem_numTargets [SampleableType prims.PkSeed] :
    (forsFTcrProblem prims).numTargets = targetCount p .forsF := rfl

@[simp]
theorem forsHTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (forsHTcrCProblem prims).numTargets = targetCount p .forsH := rfl

@[simp]
theorem forsTlTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (forsTlTcrCProblem prims).numTargets = targetCount p .forsTl := rfl

@[simp]
theorem wotsFUdCProblem_numTargets [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    (wotsFUdCProblem prims).numTargets = targetCount p .wotsFUd := rfl

@[simp]
theorem wotsFTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (wotsFTcrCProblem prims).numTargets = targetCount p .wotsFTcr := rfl

@[simp]
theorem wotsFPreCProblem_numTargets [SampleableType prims.PkSeed] :
    (wotsFPreCProblem prims).numTargets = targetCount p .wotsFPre := rfl

@[simp]
theorem wotsTlTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (wotsTlTcrCProblem prims).numTargets = targetCount p .wotsTl := rfl

@[simp]
theorem xmssHTcrCProblem_numTargets [SampleableType prims.PkSeed] :
    (xmssHTcrCProblem prims).numTargets = targetCount p .xmssH := rfl

/-! ## Distributional instances -/

/-- The FORS-`F` open-preimage game samples its target inputs uniformly, which is the hypothesis
recorded by `SM_DT_OpenPRE_SourceFinalValidity.CountingInterface`. -/
theorem forsFOpenPreProblem_hasUniformInputs [SampleableType prims.PkSeed]
    [SampleableType prims.Y] : (forsFOpenPreProblem prims).HasUniformInputs := rfl

/-- The WOTS+-`F` undetectability game draws its hidden input uniformly from the node type. -/
theorem wotsFUdCProblem_hasUniformInputs [SampleableType prims.PkSeed]
    [SampleableType prims.Y] : (wotsFUdCProblem prims).HasUniformInputs := rfl

/-- The WOTS+-`F` undetectability game's ideal response is uniform on the node type. -/
theorem wotsFUdCProblem_hasUniformOutputs [SampleableType prims.PkSeed]
    [SampleableType prims.Y] : (wotsFUdCProblem prims).HasUniformOutputs := rfl

/-! ## Game identities

The FORS-`F` OpenPRE game reduces to the DSPR and TCR games at the same attacked member, collection,
and cap; the two standalone problems above are those induced games. -/

/-- The FORS-`F` DSPR game is the one the OpenPRE-to-DSPR reduction attacks. -/
theorem forsFDsprProblem_eq_toDSPR [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    forsFDsprProblem prims = (forsFOpenPreProblem prims).toDSPR := rfl

/-- The FORS-`F` TCR game is the one the OpenPRE-to-TCR reduction attacks. -/
theorem forsFTcrProblem_eq_toTCR [SampleableType prims.PkSeed] [SampleableType prims.Y] :
    forsFTcrProblem prims = (forsFOpenPreProblem prims).toTCR := rfl

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
@[simp]
theorem forsFOpenPreProblem_eval_adrsToKey [SampleableType prims.PkSeed] [SampleableType prims.Y]
    (pkSeed : prims.PkSeed) (address : Adrs) (input : prims.Y) :
    (forsFOpenPreProblem prims).th.eval pkSeed (prims.adrsToKey address) input =
      prims.F pkSeed address input := rfl

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
is split into the `(idxTree, idxLeaf)` components `splitDigest` produces. -/

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
@[expose] def hmsgIndices (p : Params) (digest : Bytes p.m) : List (HmsgIndex p) :=
  let parts := splitDigest p digest
  (List.finRange p.k).map fun i =>
    ⟨parts.idxTree, parts.idxLeaf, i,
      ⟨forsIdx p parts.md.toList i.val, forsIdx_lt p parts.md.toList i.val⟩⟩

/-- Every digest selects exactly `k` semantic indices, one per FORS tree. -/
theorem hmsgIndices_length (p : Params) (digest : Bytes p.m) :
    (hmsgIndices p digest).length = p.k := by
  simp [hmsgIndices]

/-- `H_msg` as a keyed hash family whose key generator samples the per-message randomizer
uniformly. -/
@[expose] def hmsgKeyedHash [SampleableType prims.Y] :
    KeyedHashFamily prims.Y (HmsgITSRInput prims.PkSeed prims.Y) (Bytes p.m) where
  keygen := $ᵗ prims.Y
  hash := fun randomizer input => prims.Hmsg randomizer input.pkSeed input.pkRoot input.request

/-- Generic ITSR instantiated with `H_msg` and the FIPS digest-to-FORS-leaf map. -/
@[expose] def hmsgItsrProblem [SampleableType prims.Y] :
    KeyedHash.ITSRProblem prims.Y (HmsgITSRInput prims.PkSeed prims.Y) (Bytes p.m)
      (HmsgIndex p) where
  khf := hmsgKeyedHash prims
  indices := hmsgIndices p

@[simp]
theorem hmsgItsrProblem_hash [SampleableType prims.Y] (randomizer : prims.Y)
    (input : HmsgITSRInput prims.PkSeed prims.Y) :
    (hmsgItsrProblem prims).khf.hash randomizer input =
      prims.Hmsg randomizer input.pkSeed input.pkRoot input.request := rfl

@[simp]
theorem hmsgItsrProblem_keygen [SampleableType prims.Y] :
    (hmsgItsrProblem prims).khf.keygen = $ᵗ prims.Y := rfl

@[simp]
theorem hmsgItsrProblem_indices [SampleableType prims.Y] (digest : Bytes p.m) :
    (hmsgItsrProblem prims).indices digest = hmsgIndices p digest := rfl

end SLHDSA.Security.CanonicalGames
