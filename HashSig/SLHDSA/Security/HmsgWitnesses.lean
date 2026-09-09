/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ForsWitnesses

/-!
# The `H_msg` ITSR bridge

`H_msg(R, PK.seed, PK.root, M)` names, through `hmsgIndices`, one FORS leaf in each of the `k`
trees of one bottom-layer FORS instance.  This module connects that index list to the FORS
coordinates the rest of the lane speaks in, and connects an ITSR target transcript to a list of
signing queries at one key pair.

Everything here is deterministic.  No probability, adversary, advantage or game hop appears, and
no `ProbComp` is run.  The ITSR *winning condition* does appear, because it is a decidable
predicate on a list and a pair; what does not appear is the experiment that samples the keys.

## The one contested correspondence

`HashSig.SLHDSA.Security.CanonicalGames` keys `hmsgKeyedHash` on the randomizer and takes as its
hashed input the whole record `⟨PK.seed, PK.root, M⟩`.  The EasyCrypt development's `MCO` clone
instantiates the same abstract keyed-hash theory at `in_t <- msg`: the message **alone**.  The two
games are therefore not the same game, and this module is where the difference is stated, proved
and bounded.  `hmsgNarrowItsrProblem` transcribes the source's shape — keyed on the randomizer,
over the message alone, at a public seed and root fixed once and for all — so that the difference
can be written as a relation between two Lean objects rather than as a remark.

**What is equivalent.**  `wins_embedTargets_iff` is an `Iff`.  Along the embedding
`M ↦ ⟨PK.seed, PK.root, M⟩` at one fixed key pair, a wide win *is* a narrow win and a narrow win
*is* a wide win.  Neither direction is lossy: the embedding is injective, so freshness transports
both ways (`mem_embedTargets_iff`), and the two hashed values are equal by definition, so the
selected indices agree on the nose (`targetIndexSet_embedTargets`).  A reduction all of whose
`H_msg` inputs carry one key pair therefore gains nothing and loses nothing from the widening.

**What is strictly stronger.**  The wide game is not confined to one key pair, and the extra room
is real, not bookkeeping.  `notMem_embedTargets_of_ne` says a candidate whose seed or root differs
from the embedding's is fresh *for free*, against any transcript, without the adversary doing
anything; and `wins_of_hmsg_agree` turns that free freshness into a win as soon as the digest at
the two key pairs agrees.  In particular, for an `H_msg` that ignores its `PK.seed` and `PK.root`
arguments the wide game falls to one target query — query `⟨s', r', M⟩`, receive the key `R`, and
return `(R, ⟨s, r, M⟩)` — while the narrow game at every fixed key pair is untouched, since the
narrow game never sees a second key pair to move to.  So wide-hardness implies narrow-hardness at
every fixed key pair, and the converse fails: as an assumption, the FIPS-shaped one is strictly
the stronger.

**What would be lost if a reduction needed the converse.**  A reduction that wanted to discharge a
Lean SLH-DSA bound from the source's assumption alone — that is, to conclude wide-hardness from
narrow-hardness — cannot, and no amount of care in stating the bridge would let it.  What such a
reduction must do instead is stay inside one fibre, and that is a property of how it forms its
inputs, not of any lemma here.  `embedTargets` and the candidate side of `wins_embedTargets_iff`
share one `(pkSeed, pkRoot)` argument pair for exactly that reason: a reduction that let the two
drift apart would be a type error rather than a review question.

**Direction of the assumption, stated once.**  Assuming the FIPS `H_msg` interleaved-target-subset
resilient is assuming more than the source assumes of `mco`.  A formalisation may assume more; it
may not claim the source's assumption suffices.  Nothing in this module claims that.

**FIPS states no such property.**  The final (August 2024) FIPS 205 gives `H_msg` the signature
`𝔹ⁿ × 𝔹ⁿ × 𝔹ⁿ × 𝔹* → 𝔹ᵐ` in §4.1 and calls it with all four arguments at Algorithm 19 line 5
(signing) and Algorithm 20 line 8 (verification), and says nothing anywhere about interleaved
target subset resilience: the words *interleaved*, *resilience* and *ITSR* do not occur in the
document.  §10.2 goes the other way and says that collisions on the functions instantiating
`H_msg`, `PRF`, `PRF_msg`, `F`, `H` and `T_l` are believed to have no adverse effect on SLH-DSA's
security — qualified in its own footnote, which excepts applications needing message-bound
signatures.  The ITSR assumption is therefore imported from the SPHINCS+ analysis, not read off the
standard, and this module's correspondence claims are against the EasyCrypt development.

## The index-to-coordinate maps

An `HmsgIndex` carries four fields: the two digest indices that name the FORS instance, the FORS
tree inside it, and the leaf inside that tree.  The lane's FORS statements are indexed instead by
an instance address and a *global* leaf number running continuously across the `k` trees.
`HmsgIndex.forsAdrs` and `HmsgIndex.globalLeaf` are those two coordinates, and
`HmsgIndex.ext_of_coords` says the pair determines the index, which is what makes "this coordinate
was opened by no query" a statement about *this* index rather than about some index sharing its
coordinate.

`HmsgIndex.forsAdrs` repeats the body of `DigestParts.forsAdrs` rather than calling it, because an
`HmsgIndex` carries no `md` and a `DigestParts` cannot be built from one without inventing that
field.  The repetition is not left to inspection: `forsAdrs_eq_of_indices` proves the two agree
whenever the two indices do, and `forsAdrs_of_mem` is that equation at a digest the index belongs
to.  `globalLeaf` is grounded the same way, against `forsSigLeafIndex`, which
`HashSig.SLHDSA.Security.ForsWitnesses` derives from FIPS 205 Algorithm 16 line 4 and Algorithm 17
line 5.  A shift applied to `globalLeaf` and to `globalLeaf_of_mem` together type-checks and proves;
what refuses it is that the right-hand side is a separately reviewed definition with its own
citation, and that `HashSigTest.SLHDSA.HmsgWitnesses` evaluates the resulting FORS leaf address
against a table of `Adrs` records written out by hand.

## First, not last

`findUncoveredIndex` is `List.find?`, so it returns the *first* index of the candidate's own list
that no target covers.  `FORS_ES.ec` selects the FORS tree it attacks with `find`, which is also
first-match, so first is the source's choice and not an arbitrary one.  Soundness alone does not
distinguish first from last — `List.findLast?` would satisfy every soundness statement here
unchanged — so the choice is pinned by `findUncoveredIndex_eq_some_iff`, which additionally says
that every index *before* the returned one is covered.  That is the statement a `findLast?` variant
fails.

## What the uncovered index does and does not say

`coord_unrevealed_of_notMem` is deliberately stated at the level of a FORS *coordinate* — an
instance address together with a global leaf number — and not at the level of a secret *value*.
"The signer never revealed this value" is not derivable and is not true in general: two
`forsSkGenCore` calls at two different coordinates may collide, and nothing in the development
excludes it.  Neither is the game-level reading derivable here: turning a coordinate into a
position in an OpenPRE target list needs an index function from coordinates to list positions,
which no module on this branch supplies.  What is available, and what the OpenPRE winning condition
asks for, is that the coordinate itself was opened by no query, and that is what is proved.

The source proves no such lemma in isolation: the corresponding step is folded into the `conseq`
that discharges the OpenPRE postcondition and closed by SMT over the concrete opened-index list.
There is no named source lemma to point at, and this docstring does not invent one.

## Labels

*Deterministic inclusion* — a statement whose free objects are a primitive bundle, seeds, an
address, a digest, an index and naturals:

* `HmsgIndex.forsAdrs`, `forsAdrs_layer`, `forsAdrs_tree`, `forsAdrs_type`, `forsAdrs_keyPair`,
  `forsAdrs_eq_of_indices`, `forsAdrs_of_mem`, `forsAdrs_eq_bottom`;
* `HmsgIndex.globalLeaf`, `globalLeaf_eq`, `globalLeaf_lt`, `globalLeaf_div_pow_a`,
  `globalLeaf_of_mem`, `HmsgIndex.ext_of_coords`;
* `hmsgNarrowItsrProblem`, `hmsgNarrowItsrProblem_hash`, `hmsgNarrowItsrProblem_keygen`,
  `hmsgNarrowItsrProblem_indices`, `indexSet_embed`;
* `wins_of_hmsg_agree`;
* `findUncoveredIndex`, `findUncoveredIndex_eq_find?`, `findUncoveredIndex_eq_some_iff`,
  `mem_indexSet_of_findUncoveredIndex`, `notMem_targetIndexSet_of_findUncoveredIndex`,
  `wins_of_findUncoveredIndex_eq_none`, `itsr_wins_or_uncovered`, `uncoveredTarget`,
  `uncoveredTarget_eq`, `uncoveredTarget_globalLeaf`;
* `forsSign_getElem_sk`.

*Transcript transport* — a statement about a query list or an ITSR target transcript:

* `embedTargets`, `embedTargets_eq`, `mem_embedTargets_iff`, `notMem_embedTargets_of_notMem`,
  `notMem_embedTargets_of_ne`, `targetIndexSet_embedTargets`,
  `mem_targetIndexSet_embedTargets_iff`, `wins_embedTargets_iff`;
* `forsSign_reveals_of_mem_hmsgIndices`, `coord_unrevealed_of_notMem`.

Those forty-one are the module's whole interface; none is `private` and none carries `@[expose]`.

## References

- NIST FIPS 205, §4.1, §9 Algorithms 16, 17, 19 and 20, §10.2
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`FORS_ES.ec`, `KeyedHashFunctions.eca`)
-/

public section

namespace SLHDSA.Security.CanonicalGames

variable {p : Params}

/-! ## The FORS coordinate an ITSR index names

These extend `HmsgIndex`, so they live in its namespace; the transcript statements below are in
`SLHDSA.Security` with the rest of the lane. -/

/-- The FORS instance address an ITSR index names: layer zero, the digest's tree index, type
`FORS_TREE`, and the digest's leaf index as the key-pair address.

This is the body of `DigestParts.forsAdrs`, repeated because an `HmsgIndex` carries no FORS
message and so cannot produce a `DigestParts` without inventing one.  `forsAdrs_eq_of_indices`
below is the equation that keeps the repetition honest. -/
def HmsgIndex.forsAdrs {p : Params} (idx : HmsgIndex p) : Adrs :=
  ((Adrs.zero.setTreeAddress idx.idxTree.val).setTypeAndClear .forsTree).setKeyPairAddress
    idx.idxLeaf.val

@[simp] theorem HmsgIndex.forsAdrs_layer {p : Params} (idx : HmsgIndex p) :
    idx.forsAdrs.layer = 0 := by rfl

@[simp] theorem HmsgIndex.forsAdrs_tree {p : Params} (idx : HmsgIndex p) :
    idx.forsAdrs.tree = idx.idxTree.val := by rfl

@[simp] theorem HmsgIndex.forsAdrs_type {p : Params} (idx : HmsgIndex p) :
    idx.forsAdrs.type = AddrType.forsTree.toCode := by rfl

@[simp] theorem HmsgIndex.forsAdrs_keyPair {p : Params} (idx : HmsgIndex p) :
    idx.forsAdrs.getKeyPairAddress = idx.idxLeaf.val := by rfl

/-- The repeated body agrees with `DigestParts.forsAdrs` whenever the two digest indices do.
An index carries no other data the address reads. -/
theorem HmsgIndex.forsAdrs_eq_of_indices {p : Params} (idx : HmsgIndex p)
    (parts : DigestParts p) (htree : idx.idxTree = parts.idxTree)
    (hleaf : idx.idxLeaf = parts.idxLeaf) : idx.forsAdrs = parts.forsAdrs := by
  rw [HmsgIndex.forsAdrs, DigestParts.forsAdrs, htree, hleaf]

/-- Every index a digest selects names that digest's own FORS instance address. -/
theorem HmsgIndex.forsAdrs_of_mem {p : Params} {digest : Bytes p.m} {idx : HmsgIndex p}
    (h : idx ∈ hmsgIndices p digest) : idx.forsAdrs = (splitDigest p digest).forsAdrs := by
  rw [mem_hmsgIndices] at h
  exact idx.forsAdrs_eq_of_indices _ h.1 h.2.1

/-- The same address, read through the typed bottom position the lane's FORS ledger lemmas are
stated at.  `BottomPosition.ofDigestParts` is not exposed and no equation projects its fields, so
the identification runs through the `@[simp]` equation `BottomPosition.forsAdrs_ofDigestParts`. -/
theorem HmsgIndex.forsAdrs_eq_bottom {vp : ValidatedParams} {digest : Bytes vp.params.m}
    {idx : HmsgIndex vp.params} (h : idx ∈ hmsgIndices vp.params digest) :
    idx.forsAdrs =
      (BottomPosition.ofDigestParts vp (splitDigest vp.params digest)).forsAdrs := by
  rw [HmsgIndex.forsAdrs_of_mem h, BottomPosition.forsAdrs_ofDigestParts]

/-- The global FORS leaf number an ITSR index names, running continuously across the `k` trees:
tree `i`'s local leaf `j` sits at `i * 2 ^ a + j`.  `globalLeaf_of_mem` grounds this against
`forsSigLeafIndex`, which carries the FIPS citation. -/
def HmsgIndex.globalLeaf {p : Params} (idx : HmsgIndex p) : ℕ :=
  idx.tree.val * 2 ^ p.a + idx.leaf.val

/-- Unfolding equation for `globalLeaf`. -/
theorem HmsgIndex.globalLeaf_eq {p : Params} (idx : HmsgIndex p) :
    idx.globalLeaf = idx.tree.val * 2 ^ p.a + idx.leaf.val := by rfl

/-- Global leaf numbers stay inside the instance's `k * 2 ^ a` leaves. -/
theorem HmsgIndex.globalLeaf_lt {p : Params} (idx : HmsgIndex p) :
    idx.globalLeaf < p.k * 2 ^ p.a := by
  have hleaf : idx.leaf.val < 2 ^ p.a := idx.leaf.isLt
  have htree : idx.tree.val + 1 ≤ p.k := idx.tree.isLt
  have hstep : (idx.tree.val + 1) * 2 ^ p.a ≤ p.k * 2 ^ p.a := Nat.mul_le_mul_right _ htree
  have hexp : (idx.tree.val + 1) * 2 ^ p.a = idx.tree.val * 2 ^ p.a + 2 ^ p.a := by ring
  rw [HmsgIndex.globalLeaf_eq]
  omega

/-- Dividing the tree height out of a global leaf number gives the FORS tree back. -/
theorem HmsgIndex.globalLeaf_div_pow_a {p : Params} (idx : HmsgIndex p) :
    idx.globalLeaf / 2 ^ p.a = idx.tree.val := by
  rw [HmsgIndex.globalLeaf_eq, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos p.a),
    Nat.div_eq_of_lt idx.leaf.isLt, Nat.zero_add]

/-- Every index a digest selects names the global leaf `forsSigLeafIndex` gives its FORS tree on
that digest's FORS message. -/
theorem HmsgIndex.globalLeaf_of_mem {p : Params} {digest : Bytes p.m} {idx : HmsgIndex p}
    (h : idx ∈ hmsgIndices p digest) :
    idx.globalLeaf = forsSigLeafIndex p (splitDigest p digest).md.toList idx.tree.val := by
  rw [mem_hmsgIndices] at h
  rw [HmsgIndex.globalLeaf_eq, forsSigLeafIndex_eq, h.2.2]

/-- **The coordinate determines the index.**  Two ITSR indices with the same FORS instance address
and the same global leaf number are the same index.

The address supplies the two digest indices, through the `Adrs` projections; the global leaf
supplies the FORS tree, by dividing the tree height out, and then the leaf inside it.  Without
this, "no query opened this coordinate" would be weaker than "no query selected this index". -/
theorem HmsgIndex.ext_of_coords {p : Params} {idx idx' : HmsgIndex p}
    (hadrs : idx.forsAdrs = idx'.forsAdrs) (hleaf : idx.globalLeaf = idx'.globalLeaf) :
    idx = idx' := by
  have htree : idx.idxTree.val = idx'.idxTree.val := by
    simpa using congrArg Adrs.tree hadrs
  have hkp : idx.idxLeaf.val = idx'.idxLeaf.val := by
    simpa using congrArg Adrs.getKeyPairAddress hadrs
  have hfors : idx.tree.val = idx'.tree.val := by
    rw [← HmsgIndex.globalLeaf_div_pow_a idx, ← HmsgIndex.globalLeaf_div_pow_a idx', hleaf]
  have hlf : idx.leaf.val = idx'.leaf.val := by
    rw [HmsgIndex.globalLeaf_eq, HmsgIndex.globalLeaf_eq, hfors] at hleaf
    omega
  obtain ⟨t, l, i, f⟩ := idx
  obtain ⟨t', l', i', f'⟩ := idx'
  simp only at htree hkp hfors hlf
  simp only [HmsgIndex.mk.injEq]
  exact ⟨Fin.ext htree, Fin.ext hkp, Fin.ext hfors, Fin.ext hlf⟩

end SLHDSA.Security.CanonicalGames


namespace SLHDSA.Security

open CanonicalGames KeyedHash

variable {p : Params}

/-! ## The source's shape, and the widening

`hmsgNarrowItsrProblem` is the EasyCrypt `MCO_ITSR` clone transcribed: `key_t` the randomizer,
`in_t` the message alone, `out_t` the digest, `g` the FIPS digest-to-FORS-leaf map.  It exists so
that the difference between the two games can be *proved* rather than described. -/

/-- The ITSR problem of the EasyCrypt `MCO` clone, at one public seed and root fixed outside the
game: keyed on the message randomizer, hashing the message alone.

The `pkSeed` and `pkRoot` arguments are parameters of the *problem*, not of the hashed input.  That
is precisely the source's shape, where the message-compression function takes a key and a message
and no public key material at all, and the clone sets its input type to the message type. -/
def hmsgNarrowItsrProblem (prims : Primitives p) [SampleableType prims.Y] (pkSeed : prims.PkSeed)
    (pkRoot : prims.Y) : ITSRProblem prims.Y (List Byte) (Bytes p.m) (HmsgIndex p) where
  khf := { keygen := $ᵗ prims.Y, hash := fun randomizer request =>
    prims.Hmsg randomizer pkSeed pkRoot request }
  indices := hmsgIndices p

/-- The narrow problem hashes with the bundle's own `H_msg` at its fixed key pair. -/
@[simp] theorem hmsgNarrowItsrProblem_hash (prims : Primitives p) [SampleableType prims.Y]
    (pkSeed : prims.PkSeed) (pkRoot : prims.Y) (randomizer : prims.Y) (request : List Byte) :
    (hmsgNarrowItsrProblem prims pkSeed pkRoot).khf.hash randomizer request =
      prims.Hmsg randomizer pkSeed pkRoot request := by rfl

/-- The narrow problem samples the randomizer uniformly, as the wide one does. -/
@[simp] theorem hmsgNarrowItsrProblem_keygen (prims : Primitives p) [SampleableType prims.Y]
    (pkSeed : prims.PkSeed) (pkRoot : prims.Y) :
    (hmsgNarrowItsrProblem prims pkSeed pkRoot).khf.keygen = $ᵗ prims.Y := by rfl

/-- The narrow problem's semantic-index map is `hmsgIndices`, as the wide one's is. -/
@[simp] theorem hmsgNarrowItsrProblem_indices (prims : Primitives p) [SampleableType prims.Y]
    (pkSeed : prims.PkSeed) (pkRoot : prims.Y) (digest : Bytes p.m) :
    (hmsgNarrowItsrProblem prims pkSeed pkRoot).indices digest = hmsgIndices p digest := by rfl

/-- Read a list of signing queries — randomizer and message — as an ITSR target transcript at one
public seed and root.

*Transcript transport.*  Both `pkSeed` and `pkRoot` are supplied once and shared by every entry, so
a caller cannot embed two queries at two key pairs, and cannot embed targets at one key pair and a
candidate at another without saying so. -/
def embedTargets (prims : Primitives p) (pkSeed : prims.PkSeed) (pkRoot : prims.Y)
    (queries : ITSRTranscript prims.Y (List Byte)) :
    ITSRTranscript prims.Y (HmsgITSRInput prims.PkSeed prims.Y) :=
  queries.map fun q => (q.1, ⟨pkSeed, pkRoot, q.2⟩)

/-- Unfolding equation for `embedTargets`.  The body is not exposed, so this is what a consumer
that needs the `List.map` shape rewrites with. -/
theorem embedTargets_eq (prims : Primitives p) (pkSeed : prims.PkSeed) (pkRoot : prims.Y)
    (queries : ITSRTranscript prims.Y (List Byte)) :
    embedTargets prims pkSeed pkRoot queries =
      queries.map fun q => (q.1, ⟨pkSeed, pkRoot, q.2⟩) := by rfl

/-- **Membership transports both ways** along the embedding, because sending a message to
`⟨PK.seed, PK.root, M⟩` at a fixed key pair is injective.  This is the whole content of the
widening on the freshness conjunct. -/
theorem mem_embedTargets_iff {prims : Primitives p} (pkSeed : prims.PkSeed) (pkRoot : prims.Y)
    (queries : ITSRTranscript prims.Y (List Byte)) (randomizer : prims.Y) (request : List Byte) :
    (randomizer, (⟨pkSeed, pkRoot, request⟩ : HmsgITSRInput prims.PkSeed prims.Y)) ∈
        embedTargets prims pkSeed pkRoot queries ↔ (randomizer, request) ∈ queries := by
  rw [embedTargets_eq, List.mem_map]
  constructor
  · rintro ⟨⟨q1, q2⟩, hq, hqe⟩
    cases hqe
    exact hq
  · exact fun h => ⟨(randomizer, request), h, rfl⟩

/-- Pair freshness transports across the widening: a signing pair the log does not contain gives an
ITSR pair the embedded transcript does not contain.

*Transcript transport.*  This is the direction a reduction uses, and the only place the widening is
load-bearing on the freshness conjunct. -/
theorem notMem_embedTargets_of_notMem {prims : Primitives p} (pkSeed : prims.PkSeed)
    (pkRoot : prims.Y) {queries : ITSRTranscript prims.Y (List Byte)} {randomizer : prims.Y}
    {request : List Byte} (h : (randomizer, request) ∉ queries) :
    (randomizer, (⟨pkSeed, pkRoot, request⟩ : HmsgITSRInput prims.PkSeed prims.Y)) ∉
      embedTargets prims pkSeed pkRoot queries :=
  fun hmem => h ((mem_embedTargets_iff pkSeed pkRoot queries randomizer request).mp hmem)

/-- **Freshness off the fibre is free, and worth nothing on its own.**  A candidate whose public
seed or published root is not the one the transcript was embedded at is fresh against *every*
embedded transcript, whatever its randomizer and message, and without the adversary having done
anything.

This is where the widened game is wider than the source's, and it is stated so that a consumer
cannot mistake this freshness for the earned kind: it comes with no coverage, and
`wins_of_hmsg_agree` says what has to hold as well before it becomes a win. -/
theorem notMem_embedTargets_of_ne {prims : Primitives p} (pkSeed : prims.PkSeed)
    (pkRoot : prims.Y) (queries : ITSRTranscript prims.Y (List Byte)) (randomizer : prims.Y)
    (input : HmsgITSRInput prims.PkSeed prims.Y)
    (h : input.pkSeed ≠ pkSeed ∨ input.pkRoot ≠ pkRoot) :
    (randomizer, input) ∉ embedTargets prims pkSeed pkRoot queries := by
  rw [embedTargets_eq]
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨⟨q1, q2⟩, _, hqe⟩ := hmem
  rw [Prod.mk.injEq] at hqe
  rcases h with h | h <;> exact h (by rw [← hqe.2])

/-- One embedded pair selects the indices the narrow problem selects from the same pair.  The two
hashes are the same `H_msg` call at the same four arguments and the two index maps are both
`hmsgIndices`, so this is the coverage half of the widening in one line. -/
theorem indexSet_embed {prims : Primitives p} [SampleableType prims.Y] (pkSeed : prims.PkSeed)
    (pkRoot : prims.Y) (randomizer : prims.Y) (request : List Byte) :
    (hmsgItsrProblem prims).indexSet
        (randomizer, (⟨pkSeed, pkRoot, request⟩ : HmsgITSRInput prims.PkSeed prims.Y)) =
      (hmsgNarrowItsrProblem prims pkSeed pkRoot).indexSet (randomizer, request) := by
  rw [ITSRProblem.indexSet, ITSRProblem.indexSet, hmsgItsrProblem_khf, hmsgKeyedHash_hash,
    hmsgNarrowItsrProblem_hash, hmsgItsrProblem_indices, hmsgNarrowItsrProblem_indices]

/-- The embedded transcript selects exactly the indices the query list selects at that key pair. -/
theorem targetIndexSet_embedTargets {prims : Primitives p} [SampleableType prims.Y]
    (pkSeed : prims.PkSeed) (pkRoot : prims.Y)
    (queries : ITSRTranscript prims.Y (List Byte)) :
    (hmsgItsrProblem prims).targetIndexSet (embedTargets prims pkSeed pkRoot queries) =
      (hmsgNarrowItsrProblem prims pkSeed pkRoot).targetIndexSet queries := by
  rw [ITSRProblem.targetIndexSet, ITSRProblem.targetIndexSet, embedTargets_eq, List.flatMap_map]
  exact congrArg queries.flatMap (funext fun q => indexSet_embed pkSeed pkRoot q.1 q.2)

/-- Membership in the embedded transcript's index set, in the form a reduction reads: some query's
digest at that key pair selects the index. -/
theorem mem_targetIndexSet_embedTargets_iff {prims : Primitives p} [SampleableType prims.Y]
    (pkSeed : prims.PkSeed) (pkRoot : prims.Y) (queries : ITSRTranscript prims.Y (List Byte))
    (idx : HmsgIndex p) :
    idx ∈ (hmsgItsrProblem prims).targetIndexSet (embedTargets prims pkSeed pkRoot queries) ↔
      ∃ q ∈ queries, idx ∈ hmsgIndices p (prims.Hmsg q.1 pkSeed pkRoot q.2) := by
  rw [targetIndexSet_embedTargets, ITSRProblem.targetIndexSet, List.mem_flatMap]
  rfl

/-- **The fibre equivalence.**  At one fixed public seed and root, the widened winning condition
and the source's coincide, in both directions.

Freshness transports both ways because the embedding is injective (`mem_embedTargets_iff`);
coverage transports both ways because the two problems hash to the same digest and select the same
indices from it (`targetIndexSet_embedTargets`).  This is the precise sense in which the deviation
recorded by `HashSig.SLHDSA.Security.CanonicalGames` costs nothing: it costs nothing *inside one
fibre*, and `notMem_embedTargets_of_ne` and `wins_of_hmsg_agree` are what happens outside one.

*Transcript transport.* -/
theorem wins_embedTargets_iff {prims : Primitives p} [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y] (pkSeed : prims.PkSeed) (pkRoot : prims.Y)
    (queries : ITSRTranscript prims.Y (List Byte)) (randomizer : prims.Y) (request : List Byte) :
    (hmsgItsrProblem prims).Wins (embedTargets prims pkSeed pkRoot queries)
        (randomizer, ⟨pkSeed, pkRoot, request⟩) ↔
      (hmsgNarrowItsrProblem prims pkSeed pkRoot).Wins queries (randomizer, request) := by
  rw [ITSRProblem.Wins, ITSRProblem.Wins, targetIndexSet_embedTargets,
    indexSet_embed pkSeed pkRoot randomizer request]
  constructor
  · rintro ⟨hfresh, hcov⟩
    exact ⟨fun hmem => hfresh ((mem_embedTargets_iff pkSeed pkRoot queries randomizer
      request).mpr hmem), hcov⟩
  · rintro ⟨hfresh, hcov⟩
    exact ⟨fun hmem => hfresh ((mem_embedTargets_iff pkSeed pkRoot queries randomizer
      request).mp hmem), hcov⟩

/-- **The widened game admits wins the source's game has no room for.**  Whenever one randomizer
gives the same digest at two distinct `H_msg` inputs, the single-target transcript at the second is
already a win at the first.

Instantiated at two inputs carrying the same message and different key material, this is a
one-query break of the widened game for any `H_msg` that ignores its `PK.seed` and `PK.root`
arguments — a bundle whose narrow problem at every fixed key pair is whatever it was, since the
narrow game has no second key pair to move to.  So narrow hardness does not imply wide hardness,
and the widened assumption is strictly the stronger of the two.

*Deterministic inclusion.* -/
theorem wins_of_hmsg_agree {prims : Primitives p} [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y] (randomizer : prims.Y)
    (input input' : HmsgITSRInput prims.PkSeed prims.Y) (hne : input ≠ input')
    (hdigest : prims.Hmsg randomizer input.pkSeed input.pkRoot input.request =
      prims.Hmsg randomizer input'.pkSeed input'.pkRoot input'.request) :
    (hmsgItsrProblem prims).Wins [(randomizer, input')] (randomizer, input) := by
  refine ⟨?_, ?_⟩
  · simp only [List.mem_singleton, Prod.mk.injEq, not_and]
    exact fun _ => hne
  · intro i hi
    rw [ITSRProblem.targetIndexSet, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      ITSRProblem.indexSet, hmsgItsrProblem_khf, hmsgKeyedHash_hash]
    rw [ITSRProblem.indexSet, hmsgItsrProblem_khf, hmsgKeyedHash_hash, hdigest] at hi
    exact hi

/-! ## The uncovered index -/

/-- The first FORS leaf the candidate's own digest selects that no target's digest selects.

`List.find?` returns the first match, which is the source's choice at the corresponding step, and
`findUncoveredIndex_eq_some_iff` pins that choice: soundness alone would be satisfied by a
last-match variant. -/
def findUncoveredIndex (prims : Primitives p) [SampleableType prims.Y] [DecidableEq prims.PkSeed]
    [DecidableEq prims.Y]
    (targets : ITSRTranscript prims.Y (HmsgITSRInput prims.PkSeed prims.Y))
    (candidate : prims.Y × HmsgITSRInput prims.PkSeed prims.Y) : Option (HmsgIndex p) :=
  ((hmsgItsrProblem prims).indexSet candidate).find?
    fun i => decide (i ∉ (hmsgItsrProblem prims).targetIndexSet targets)

/-- Unfolding equation for `findUncoveredIndex`.  The body is not exposed, so this is what a
consumer that needs the `List.find?` shape rewrites with. -/
theorem findUncoveredIndex_eq_find? (prims : Primitives p) [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    (targets : ITSRTranscript prims.Y (HmsgITSRInput prims.PkSeed prims.Y))
    (candidate : prims.Y × HmsgITSRInput prims.PkSeed prims.Y) :
    findUncoveredIndex prims targets candidate =
      ((hmsgItsrProblem prims).indexSet candidate).find?
        fun i => decide (i ∉ (hmsgItsrProblem prims).targetIndexSet targets) := by rfl

/-- **Which uncovered index comes back.**  The returned index is uncovered, it occurs in the
candidate's own index list, and every index *before* it there is covered.

The last conjunct is what distinguishes `List.find?` from `List.findLast?`; every other statement
about `findUncoveredIndex` in this module holds of both. -/
theorem findUncoveredIndex_eq_some_iff {prims : Primitives p} [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    (targets : ITSRTranscript prims.Y (HmsgITSRInput prims.PkSeed prims.Y))
    (candidate : prims.Y × HmsgITSRInput prims.PkSeed prims.Y) (idx : HmsgIndex p) :
    findUncoveredIndex prims targets candidate = some idx ↔
      idx ∉ (hmsgItsrProblem prims).targetIndexSet targets ∧
        ∃ before after, (hmsgItsrProblem prims).indexSet candidate = before ++ idx :: after ∧
          ∀ j ∈ before, j ∈ (hmsgItsrProblem prims).targetIndexSet targets := by
  rw [findUncoveredIndex_eq_find?, List.find?_eq_some_iff_append]
  simp

/-- The returned index is one the candidate's own digest selects. -/
theorem mem_indexSet_of_findUncoveredIndex {prims : Primitives p} [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    {targets : ITSRTranscript prims.Y (HmsgITSRInput prims.PkSeed prims.Y)}
    {candidate : prims.Y × HmsgITSRInput prims.PkSeed prims.Y} {idx : HmsgIndex p}
    (h : findUncoveredIndex prims targets candidate = some idx) :
    idx ∈ (hmsgItsrProblem prims).indexSet candidate := by
  rw [findUncoveredIndex_eq_find?] at h
  exact List.mem_of_find?_eq_some h

/-- The returned index is covered by no target. -/
theorem notMem_targetIndexSet_of_findUncoveredIndex {prims : Primitives p}
    [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    {targets : ITSRTranscript prims.Y (HmsgITSRInput prims.PkSeed prims.Y)}
    {candidate : prims.Y × HmsgITSRInput prims.PkSeed prims.Y} {idx : HmsgIndex p}
    (h : findUncoveredIndex prims targets candidate = some idx) :
    idx ∉ (hmsgItsrProblem prims).targetIndexSet targets := by
  rw [findUncoveredIndex_eq_find?] at h
  simpa using List.find?_some h

/-- No uncovered index means every selected index is covered, which together with pair freshness is
the whole winning condition. -/
theorem wins_of_findUncoveredIndex_eq_none {prims : Primitives p} [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    {targets : ITSRTranscript prims.Y (HmsgITSRInput prims.PkSeed prims.Y)}
    {candidate : prims.Y × HmsgITSRInput prims.PkSeed prims.Y} (hfresh : candidate ∉ targets)
    (h : findUncoveredIndex prims targets candidate = none) :
    (hmsgItsrProblem prims).Wins targets candidate := by
  rw [findUncoveredIndex_eq_find?, List.find?_eq_none] at h
  exact ⟨hfresh, fun i hi => by simpa using h i hi⟩

/-- **The dichotomy.**  A pair the transcript does not contain either wins the ITSR game outright or
exhibits, computably, one FORS leaf of its own that no target covers.

Both branches are used downstream and neither is the interesting one on its own: the win is what a
reduction reports, and the uncovered index is what feeds the lane's FORS extractor its `target`
argument, through `uncoveredTarget`.

*Deterministic inclusion.* -/
theorem itsr_wins_or_uncovered {prims : Primitives p} [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    (targets : ITSRTranscript prims.Y (HmsgITSRInput prims.PkSeed prims.Y))
    (candidate : prims.Y × HmsgITSRInput prims.PkSeed prims.Y) (hfresh : candidate ∉ targets) :
    (hmsgItsrProblem prims).Wins targets candidate ∨
      ∃ idx, findUncoveredIndex prims targets candidate = some idx ∧
        idx ∈ (hmsgItsrProblem prims).indexSet candidate ∧
        idx ∉ (hmsgItsrProblem prims).targetIndexSet targets := by
  rcases h : findUncoveredIndex prims targets candidate with _ | idx
  · exact Or.inl (wins_of_findUncoveredIndex_eq_none hfresh h)
  · exact Or.inr ⟨idx, rfl, mem_indexSet_of_findUncoveredIndex h,
      notMem_targetIndexSet_of_findUncoveredIndex h⟩

/-- The FORS tree an uncovered index names, which is the `target` argument the lane's FORS
extractor takes.  It is the source's selected tree number at the corresponding step.

It is a projection and nothing more; it is named so that a reduction hands the extractor a value
with a stated provenance rather than a raw `Fin`, and `uncoveredTarget_globalLeaf` ties it back to
the coordinate the same index names. -/
def uncoveredTarget {p : Params} (idx : HmsgIndex p) : Fin p.k := idx.tree

/-- Unfolding equation for `uncoveredTarget`.  The body is not exposed, so a consumer that wants to
see the FORS tree behind the name rewrites with this.

Not `@[simp]`, for the reason `HashSig.SLHDSA.Security.SchemeWitnesses` gives for `schemeParts_eq`:
the definition exists to name a value with a stated provenance, and a `simp` set that rewrote the
name away would put the bare projection back into every goal a consumer states. -/
theorem uncoveredTarget_eq {p : Params} (idx : HmsgIndex p) :
    uncoveredTarget idx = idx.tree := by rfl

/-- The selected tree is what dividing the tree height out of the global leaf gives back, so the
`target` handed to the FORS extractor and the coordinate the uncovered index names agree.

Not `@[simp]` either, and for a second reason: its right-hand side is the wrapper, so as a rewrite
rule it would replace a plain projection by a named one. -/
theorem uncoveredTarget_globalLeaf {p : Params} (idx : HmsgIndex p) :
    idx.globalLeaf / 2 ^ p.a = (uncoveredTarget idx).val :=
  HmsgIndex.globalLeaf_div_pow_a idx

/-! ## What a signing query reveals -/

/-- The secret value honest FORS signing reveals in tree `i` is the one at that tree's global leaf
index.  FIPS 205 Algorithm 16 line 4. -/
theorem forsSign_getElem_sk (prims : Primitives p) (md : List Byte) (sk : prims.SkSeed)
    (pkSeed : prims.PkSeed) (adrs : Adrs) (i : Fin p.k) :
    ((forsSign prims md sk pkSeed adrs)[i.val]).sk =
      forsSkGenCore prims.core sk pkSeed adrs (forsSigLeafIndex p md i.val) := by
  rw [forsSign_eq_ofFn, Vector.getElem_ofFn, forsSigLeafIndex_eq]

/-- **What `hmsgIndices` reads as.**  Each index a digest selects names a FORS coordinate, and the
secret value honest signing on that digest reveals at that index's tree is the secret value at that
coordinate.

*Transcript transport.*  This is the reading that makes an uncovered index mean something: the
indices a query's digest selects are exactly the coordinates that query's signature opens. -/
theorem forsSign_reveals_of_mem_hmsgIndices (prims : Primitives p) (sk : prims.SkSeed)
    (pkSeed : prims.PkSeed) {digest : Bytes p.m} {idx : HmsgIndex p}
    (h : idx ∈ hmsgIndices p digest) :
    ((forsSign prims (splitDigest p digest).md.toList sk pkSeed
        (splitDigest p digest).forsAdrs)[idx.tree.val]).sk =
      forsSkGenCore prims.core sk pkSeed idx.forsAdrs idx.globalLeaf := by
  rw [forsSign_getElem_sk prims _ sk pkSeed _ idx.tree, HmsgIndex.forsAdrs_of_mem h,
    HmsgIndex.globalLeaf_of_mem h]

/-- **The uncovered coordinate was opened by no query.**  If an index is covered by no embedded
target, then no signing query and no FORS tree of that query land on its instance address together
with its global leaf number.

*Transcript transport.*  Stated at the coordinate, not at the secret value and not at a game target
list; the module docstring says why neither of those is available here.  The proof is by
contraposition: a query and a tree that did land there rebuild an index the query's digest selects,
which `HmsgIndex.ext_of_coords` identifies with this one. -/
theorem coord_unrevealed_of_notMem {prims : Primitives p} [SampleableType prims.Y]
    (pkSeed : prims.PkSeed) (pkRoot : prims.Y)
    {queries : ITSRTranscript prims.Y (List Byte)} {idx : HmsgIndex p}
    (huncov :
      idx ∉ (hmsgItsrProblem prims).targetIndexSet (embedTargets prims pkSeed pkRoot queries))
    {q : prims.Y × List Byte} (hq : q ∈ queries) (i : Fin p.k) :
    ¬ ((splitDigest p (prims.Hmsg q.1 pkSeed pkRoot q.2)).forsAdrs = idx.forsAdrs ∧
        forsSigLeafIndex p (splitDigest p (prims.Hmsg q.1 pkSeed pkRoot q.2)).md.toList i.val =
          idx.globalLeaf) := by
  rintro ⟨hadrs, hleafidx⟩
  refine huncov ?_
  have hjmem :
      (⟨(splitDigest p (prims.Hmsg q.1 pkSeed pkRoot q.2)).idxTree,
        (splitDigest p (prims.Hmsg q.1 pkSeed pkRoot q.2)).idxLeaf, i,
        ⟨forsIdx p (splitDigest p (prims.Hmsg q.1 pkSeed pkRoot q.2)).md.toList i.val,
          forsIdx_lt p (splitDigest p (prims.Hmsg q.1 pkSeed pkRoot q.2)).md.toList i.val⟩⟩ :
          HmsgIndex p) ∈ hmsgIndices p (prims.Hmsg q.1 pkSeed pkRoot q.2) := by
    rw [mem_hmsgIndices]
    exact ⟨rfl, rfl, rfl⟩
  have hjadrs := HmsgIndex.forsAdrs_of_mem hjmem
  have hjleaf := HmsgIndex.globalLeaf_of_mem hjmem
  rw [hadrs] at hjadrs
  rw [hleafidx] at hjleaf
  rw [← HmsgIndex.ext_of_coords hjadrs hjleaf]
  exact (mem_targetIndexSet_embedTargets_iff pkSeed pkRoot queries _).mpr ⟨q, hq, hjmem⟩

end SLHDSA.Security
