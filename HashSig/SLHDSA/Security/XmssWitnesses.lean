/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.WotsWitnesses

/-!
# XMSS witnesses

Deterministic translations of one XMSS root match into a concrete witness against one named
component hash: an ordered-pair collision of `H` at an exact `TREE` internal-node address, or one
of the three WOTS+ witnesses of `HashSig.SLHDSA.Security.WotsWitnesses` at the leaf the signature
opens.  The case analysis is the Lean counterpart of the `valid_WOTSTWES`/`valid_TCRPKCO`/
`valid_TCRTRH` split of the EasyCrypt SPHINCS+ development, specialised to one XMSS tree
(`FL_SL_XMSS_MT_ES.ec`, the three case flags at `:3268-3269`, `:3270-3271` and `:3272-3273`).

## What is proved, and what is not

The `H`-collision half is not new here.  `SLHDSA.xmssPkFromSig_binding` (`Xmss.lean:812`) already
proves it, over the intrinsic `XmssSigCore` — whose authentication path is `Vector core.Y p.hp`,
so it carries no path-length hypothesis — and this module consumes it unchanged.  What is added is
exhaustiveness: `xmssPkFromSig_cases` says that when the binding lemma's leaf hypothesis fails the
signature recovers the *honest* WOTS+ public key at that leaf, which is the hypothesis
`wotsPkFromSig_cases` takes, and `xmssPkFromSig_forgeryCases` composes it with the WOTS+
extractor pair (`findWotsWitness_isSome`, `findWotsWitness_sound`), whose three outcomes are
`wotsPkFromSig_cases`' three.

Every *deterministic-inclusion* statement below has its free objects drawn from a parameter record
or a primitive bundle over one, seeds, a structural address, natural-number indices, messages, and
signature or witness data, together with the structural side conditions their proofs need: the
`p.Valid` and `prims.core.ByteLaws` arguments of the two declarations whose *proofs* invoke the
WOTS+ extractor's *completeness* lemma, `xmssPkFromSig_forgeryCases` and `findXmssWitness_isSome`
— five declarations invoke the extractor itself, but `findWotsWitness_isSome` is what takes those
two and `findWotsWitness_sound` takes neither — the `DecidableEq prims.Y` instance the extractor
here and its five lemmas take, and the `SampleableType prims.PkSeed` instance on the game-shape
bridge.  Not all of them mention all of those.  Eight of the sixteen mention an `XmssSigCore` —
`xmssPkFromSig_cases`, `xmssPkFromSig_forgeryCases`, `findXmssWitness`, its two shape equations and
its three lemmas — and the other eight do not.  Of those eight only the game-shape bridge names a
game at all, and what it names is a `Problem` record, never an experiment or an advantage.

The honest secret seed is not confined to one lemma: fourteen of the sixteen take one, the two
exceptions being `xmssNodeIndex_lt`, which is arithmetic on the leaf index, and the `XmssWitness`
inductive, which carries no honest object at all.  That is because every honest partner an XMSS
witness attacks — the honest child pair at a `TREE` node, the honest WOTS+ chain ends at the opened
leaf, the honest WOTS+ signature at that leaf on the honest message — is a function of the honest
tree, and the honest tree is what `sk` generates.

The three *transcript-transport* statements are about the role ledgers of a `ValidatedParams`.
`wotsLeafAdrs_eq_wotsInstanceAdrs` takes a layer position alone and states no membership: it
identifies the address an XMSS witness names with the one a slice-1 ledger is indexed by, which is
what lets the WOTS+ ledger lemmas apply unchanged.  `mem_xmssNodeAddresses_of_leaf` takes a layer
position, a node height and that height's two bounds.  `xmssNodeAdrsKey_injective` takes a
primitive bundle, an `EncodedTargetLedgerConditions`, and two coordinate tuples with their own
range hypotheses; the tuples are implicit arguments rather than bound by a lambda, so they are free
in the statement.  None of the three mentions a signature or a secret seed.  Nothing here
constructs an adversary, states an advantage, performs a game hop, or claims that any honest
execution queried the honest value a witness attacks.  In particular a witness lemma is **not** a
reduction: that the game's target was committed before the forgery was seen is a
simulation-fidelity obligation of the later program-level slice, not a fact established here.

The one-layer split proved here is not the whole hypertree translation.  Each of the source's three
flags is an existential over the `d` layers, and each reduction then picks one layer with a `find`
(`:2112`, `:2398`, `:2685`); that the three between them cover every forgery is discharged inline
at `:5332-5337`.  That walk is deliberately absent here: it is a statement about a vector of `d`
XMSS signatures, not about one, and every statement in this module is about one XMSS signature at
one named leaf.

## Labels

*Deterministic inclusion* — a statement whose only free objects are a parameter record or a
`prims` over one, seeds, addresses, natural-number indices, messages, and signature or witness
data:

* the definition `xmssHonestChildren` with its equation `xmssHonestChildren_eq`, and the index
  fact `xmssNodeIndex_lt`;
* `xmssPkFromSig_cases`, `xmssPkFromSig_forgeryCases`;
* `XmssWitness`, `XmssWitness.Valid` and its two unfolding equations
  `XmssWitness.valid_hCollision`, `XmssWitness.valid_wots`;
* `findXmssWitness`, `findXmssWitness_eq_wots_of_leaf`, `findXmssWitness_eq_node_of_leaf_ne`,
  `findXmssWitness_sound_of_leaf`, `findXmssWitness_sound`, `findXmssWitness_isSome`;
* the game-shape bridge `xmssWitness_valid_hCollision_eval`.

These sixteen and the three below are the module's whole interface: nineteen declarations in all,
of which fifteen are theorems, three are `def`s and one is an inductive.  There is no private
declaration.

*Transcript transport* — a statement about a role ledger of `HashSig.SLHDSA.Security`:

* `wotsLeafAdrs_eq_wotsInstanceAdrs`, `mem_xmssNodeAddresses_of_leaf`, `xmssNodeAdrsKey_injective`.

The `wots` branch's own three ledgers are slice-1 objects, defined in
`HashSig.SLHDSA.Security.ReachableTargets`: `wotsStepAddresses`, `optionalWotsAddresses` and
`wotsPkAddresses`.  They are reached by `WotsWitnesses`' `mem_wotsStepAddresses_of_lt` and
`wotsPreimageAdrs_mem_optionalWotsAddresses`, and by `ReachableTargets`' own `mem_wotsPkAddresses`
— which `WotsWitnesses` likewise uses directly rather than restating.  All three membership lemmas
are stated at `wotsInstanceAdrs pos`, and an XMSS witness names
`wotsLeafAdrs pos.toAdrs pos.leaf.val`; the two are the same address, which is what
`wotsLeafAdrs_eq_wotsInstanceAdrs` records.  Nothing is restated.

`xmssNodeAdrsKey_injective` consumes `EncodedTargetLedgerConditions` rather than assuming a fresh
injectivity hypothesis, so a concrete profile discharges it through
`approvedEncodedTargetLedgerConditions`; the SHA-2 zero fallback is therefore never treated as
unreachable.

## The case analysis

Fix a leaf index `idx < 2 ^ h'`, an XMSS signature `sig`, a forged message `msg`, an honest message
`msg' ≠ msg`, and the honest key material `(sk, pk)` at the tree address `adrs`.  Recovery
reconstructs the WOTS+ public key of leaf `idx` from `sig.wots` and then climbs `sig.auth`; key
generation builds the same tree from the honest leaves.  A root match therefore equates the climb
of the recovered leaf with the honest root.  Either the recovered leaf differs from the honest one,
and `PerfectMerkleTree.climb_binding` extracts an `H`-collision at an internal node of height
`0 < z ≤ h'` on that leaf's root path — or it agrees, and the signature recovers the honest WOTS+
public key at `wotsLeafAdrs adrs idx`, which is exactly `wotsPkFromSig_cases`' hypothesis and
splits three further ways: a `T_len` second preimage at `wotsPkAdrs (wotsLeafAdrs adrs idx)`, and
the two chain outcomes.

The comparison with the source is branch by branch, and at a fixed layer each of the source's three
flags is a conjunction this module reproduces exactly.

* `valid_TCRTRH` (`:3272-3273`) asks that the layer's recovered root equal the honest one *and*
  its recovered leaf differ.  The first conjunct is `xmssPkFromSig_cases`' hypothesis `hroot`, the
  second is the case it splits on, so under that hypothesis the `H` branch fires on exactly the
  layers `valid_TCRTRH` names.  Its extractor is `R_SMDTTCRCTRH_EUFNAGCMA`'s procedure `find`
  (`:2597`) — the reduction is an `Adv_SMDTTCRC` and has no `forge` of its own; `forge` belongs to
  the adversary and is called at `:2646`.  Inside that procedure the layer is selected by the list
  `find` at `:2685-2686`, whose predicate is literally those two conjuncts, and the collision
  extraction runs to `:2711`.
* `valid_TCRPKCO` (`:3270-3271`) asks that the layer's recovered leaf equal the honest one *and*
  its recovered chain-end vector differ.  That is `wotsPkFromSig_cases`' first disjunct, which is
  the `T_len` branch, with the leaf equality written out as the equality of the two `T_len` images
  and the two conjuncts in the other order.  It needs no hypothesis of this module's.
* `valid_WOTSTWES` (`:3268-3269`) asks that the layer's recovered chain-end vector equal the
  honest one *and* the message signed at that layer differ.  Since the leaf is the compression of
  the chain ends, the first conjunct implies the leaf agrees too, so this is the remaining case
  here — leaf and chain ends both honest, messages distinct.  It splits two ways rather than one:
  `WOTS_TW_ES.ec` resolves a WOTS forgery into a chain preimage or a chain collision separately, at
  `nhchwcoll_hchwpre` (`:1299`), between the predicates `is_chwcoll` (`:595`) and `is_chwpre`
  (`:640`), and `WotsWitness` carries that resolution in its constructors.

So at a fixed layer, and for `valid_TCRTRH` under the root hypothesis its first conjunct supplies,
the correspondence is one-to-one on the first two flags and two-to-one on the third, and strict in
neither direction.  What the source has and this module does not is the layer walk: each flag is an
existential over `0 ≤ i < d`, and nothing here chooses a layer.

`MultiExtractability` is deliberately not imported, for the reason
`HashSig.SLHDSA.Security.ForsWitnesses` gives: it is a probabilistic shared-ROM game over
sequential checkpoints and pruned batch openings, whereas the collision needed here is against one
fixed honest tree, which is exactly what `PerfectMerkleTree.findCollision` and `climb_binding`
give.

## Address roles

`xmssNodeAddresses` is the only one of the six structural ledgers whose members carry the `TREE`
type code (`type_of_mem_xmssNodeAddresses`), so — unlike the FORS `H` case, where
`disjoint_forsLeafAddresses_forsTreeAddresses` separates two `FORS_TREE` ledgers by the tree-height
word alone — the `0 < z` bound an `hCollision` witness carries is *not* what keeps it out of
another role's ledger.  It is load-bearing for two other reasons: `xmssNodeAddresses` lists only
the coordinates of `perfectInternalCoords h'`, which start at height one, so `0 < z` is what places
the address in the ledger at all; and `xmssHonestChildren`'s `z - 1` would truncate at zero, so
that at `z = 0` it would name the children of the height-one node instead of anything at height
zero.  A height-zero `TREE` address is unlisted rather than misattributed: the leaf
of an XMSS tree is a WOTS+ public key, addressed by `wotsPkAdrs (wotsLeafAdrs adrs idx)` under the
`WOTS_PK` type code, and never by `xmssNodeAdrs adrs 0 idx`.

## References

- NIST FIPS 205, §6 (Algorithms 9–11)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`FL_SL_XMSS_MT_ES.ec`, `WOTS_TW_ES.ec`)
-/

public section

namespace SLHDSA.Security

open CanonicalGames

variable {p : Params}

/-! ## The honest child pair

An XMSS internal node's honest partner is the pair of honest subtree roots one level below it.
Naming it separates the Merkle argument from the WOTS+ one. -/

/-- The honest child pair of the XMSS internal node at height `z`, index `t`: the two honest
subtree roots one level below.  Meaningful only at `0 < z`.  Every statement below that names it
as an honest partner asserts that bound; the one statement below that names it without asserting
the bound is its own unfolding equation, which is definitional and holds at every height.  At
`z = 0` truncated subtraction leaves `z - 1 = 0`, so it returns the two leaves `2 * t` and
`2 * t + 1` — the children of the height-*one* node at `t`, not of any node at height zero — and
an XMSS leaf is a WOTS+ public key, addressed under `WOTS_PK`, rather than a `TREE` target. -/
def xmssHonestChildren (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (z t : ℕ) : prims.Y × prims.Y :=
  PerfectMerkleTree.honestChildren (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) z t

/-- Unfolding equation for `xmssHonestChildren`, in the construction's own vocabulary: the two
height-`z - 1` subtree roots of FIPS 205 Algorithm 9. -/
theorem xmssHonestChildren_eq (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (z t : ℕ) :
    xmssHonestChildren prims sk pk adrs z t =
      (xmssNode prims sk pk adrs (z - 1) (2 * t), xmssNode prims sk pk adrs (z - 1) (2 * t + 1)) :=
  by simp only [xmssHonestChildren, PerfectMerkleTree.honestChildren, xmssNode_eq_merkleRoot]

/-- At any height `z ≤ h'`, the ancestor of leaf `idx` carries the index `idx / 2 ^ z`, and that
index is below `2 ^ (h' - z)`, which is the coordinate shape `xmssNodeAddresses` lists through
`perfectInternalCoords`.  It is also the shape the authentication path of FIPS 205 Algorithm 10 is
indexed by, whose height-`z` entry is the sibling of that same quotient. -/
theorem xmssNodeIndex_lt (p : Params) {idx z : ℕ} (hidx : idx < 2 ^ p.hp) (hz : z ≤ p.hp) :
    idx / 2 ^ z < 2 ^ (p.hp - z) := by
  refine Nat.div_lt_of_lt_mul ?_
  rw [← pow_add]
  exact lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ## The two branches -/

/-- **XMSS leaf dichotomy.**  A signature at leaf `idx < 2 ^ h'` that recovers the honest XMSS root
either recovers the honest WOTS+ public key at that leaf, or exhibits an `H`-collision at an
internal node of height `0 < z ≤ h'` on the leaf's root path — at exactly the address
`xmssNodeAdrs adrs z (idx / 2 ^ z)`, between the honest child pair there and a second, different
pair.

The proof splits on whether the recovered leaf equals the honest one.  It is exhaustive by
construction: the split is a decision on a proposition and its negation, and the collision half is
`xmssPkFromSig_binding` (`Xmss.lean:812`) with `xmssLeaf_eq_wotsPkGen` used to read the honest leaf
as a WOTS+ public key.

Together with its root hypothesis, the collision branch is the `valid_TCRTRH` case of
`FL_SL_XMSS_MT_ES.ec:3272-3273`, whose extractor is `R_SMDTTCRCTRH_EUFNAGCMA`'s procedure `find`
(`:2597`) — which calls the adversary's `forge` at `:2646` and selects the layer with the list
`find` at `:2685-2686`; the other branch is the hypothesis of `wotsPkFromSig_cases`,
under which the source's remaining two flags are decided.

*Deterministic inclusion.* -/
theorem xmssPkFromSig_cases (prims : Primitives p) (idx : ℕ) (hidx : idx < 2 ^ p.hp)
    (sig : XmssSig p prims) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (hroot : xmssPkFromSig prims idx sig msg pk adrs = xmssRoot prims sk pk adrs) :
    wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx) =
        wotsPkGen prims sk pk (wotsLeafAdrs adrs idx) ∨
      ∃ (z : ℕ) (c : prims.Y × prims.Y), 0 < z ∧ z ≤ p.hp ∧
        xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z) ≠ c ∧
        prims.H pk (xmssNodeAdrs adrs z (idx / 2 ^ z))
            (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)).1
            (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)).2 =
          prims.H pk (xmssNodeAdrs adrs z (idx / 2 ^ z)) c.1 c.2 := by
  by_cases hleaf : xmssLeaf prims sk pk adrs idx =
      wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx)
  · rw [xmssLeaf_eq_wotsPkGen] at hleaf
    exact Or.inl hleaf.symm
  · obtain ⟨z, c, hzpos, hzle, hne, hcoll⟩ :=
      xmssPkFromSig_binding prims msg sk pk adrs idx hidx sig hroot hleaf
    exact Or.inr ⟨z, c, hzpos, hzle, by rw [xmssHonestChildren_eq]; exact hne,
      by rw [xmssHonestChildren_eq]; exact hcoll⟩

/-! ## The extracted witness

`XmssWitness` packages the outcomes as the data a reduction submits: an adversarial child pair
together with the height that names its tweak, or a `WotsWitness` at the opened leaf.  Every honest
object a witness attacks is an argument of `XmssWitness.Valid` and never a constructor field:
`Valid` takes the honest secret seed, the public seed, the tree address, the leaf index and the
honest message, and from them *computes* the honest child pair at the named node, the honest WOTS+
chain ends at the opened leaf, and the honest WOTS+ signature there on the honest message.

That computation is the identification a source-final-validity game needs: its winning condition
compares the submitted value against the challenge *recorded* at the named target, so a pair of
arbitrary distinct values with equal images is not a win.  `XmssWitness.Valid` therefore carries
the hash-value half of that winning condition — against partners the predicate names rather than
quantifies over — together with the height bounds that place the address in a role ledger, and
nothing beyond that.  It does not assert that the honest object was recorded as a game target, or
anything about the rest of a transcript; those are program-level obligations of the reduction.

The `wots` branch delegates to `WotsWitness.Valid` rather than restating its three cases.  What
this module contributes there is the *instantiation*: `WotsWitness.Valid` takes the honest chain
ends, the honest signature and the honest message as arguments, and an arbitrary choice of those
would identify nothing.  Here they are `wotsPkGenTops prims sk pk (wotsLeafAdrs adrs idx)` and
`wotsSign prims honestMsg sk pk (wotsLeafAdrs adrs idx)` — the honest WOTS+ key material at the
leaf the *forged* signature opens, computed from `sk`. -/

/-- A witness against one XMSS or WOTS+ component hash at a fixed tree address and leaf index.

The `hCollision` constructor carries only the value a reduction submits together with the height
that names its tweak; the node's horizontal index is not carried, because the leaf index already
fixes it.  The `wots` constructor carries a `WotsWitness`, whose own constructors name the chain
index and hash-address step where those are needed.  Every honest object a witness attacks is
supplied to `XmssWitness.Valid`, which reads it off the honest tree. -/
inductive XmssWitness (p : Params) (prims : Primitives p) where
  /-- An `H`-collision at the height-`height` node of the opened leaf's root path.  `children` is
  the submitted pair; the honest pair it collides with is not carried here but computed by
  `XmssWitness.Valid` from the honest tree. -/
  | hCollision (height : ℕ) (children : prims.Y × prims.Y)
  /-- A WOTS+ witness at the leaf the signature opens. -/
  | wots (witness : WotsWitness p prims)

/-- The winning condition each witness asserts, against the honest XMSS tree that `sk` generates at
`adrs` under the public seed `pk`, at the leaf index `idx` — the one the forged signature opens, in
the intended use — and the honest message `honestMsg` signed at that leaf.

* `hCollision z c` asserts an `H`-collision at `xmssNodeAdrs adrs z (idx / 2 ^ z)` between `c` and
  `xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)`, the honest child pair there, and pins
  `0 < z ≤ h'`.  Both bounds are load-bearing: `z ≤ h'` and `0 < z`, together with the leaf bound
  a `LayerPosition` carries, are what place the address in the `xmssH` ledger — `idx` here is an
  unbounded `ℕ`, so the two height bounds alone do not bound `idx / 2 ^ z` by `2 ^ (h' - z)`; and
  `0 < z` also excludes `z = 0`, the height at which `xmssHonestChildren`'s `z - 1` truncates.
  Neither separates the address from another role's ledger; the `TREE` type code does that on its
  own.
* `wots w` asserts `w`'s own winning condition at `wotsLeafAdrs adrs idx`, against the honest chain
  ends `wotsPkGenTops prims sk pk (wotsLeafAdrs adrs idx)` and the honest WOTS+ signature
  `wotsSign prims honestMsg sk pk (wotsLeafAdrs adrs idx)` on `honestMsg`.  Those two are computed
  from the honest secret seed rather than supplied, which is what makes the `wots` branch an attack
  on named honest values.

The `hCollision` distinctness reads honest-first, `xmssHonestChildren … ≠ c`, inherited from
`PerfectMerkleTree.findCollision_sound`, whose `c₁ ≠ c₂` names the honest pair first; the
`tlCollision` and `fCollision` cases inside `WotsWitness.Valid` both read submitted-first
(`recovered ≠ honestTops` and `value ≠ chain …`).  Nothing turns on it — a consumer that wants a
game's order applies `Ne.symm` — but the two orientations do not agree.

This is a statement about hash values only.  It does not say that the honest child pair, the honest
chain ends or the honest signature was committed as a game target, nor that any execution queried
them. -/
def XmssWitness.Valid {p : Params} {prims : Primitives p} (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) (honestMsg : prims.Y) : XmssWitness p prims → Prop
  | .hCollision z c =>
      0 < z ∧ z ≤ p.hp ∧
        xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z) ≠ c ∧
        prims.H pk (xmssNodeAdrs adrs z (idx / 2 ^ z))
            (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)).1
            (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)).2 =
          prims.H pk (xmssNodeAdrs adrs z (idx / 2 ^ z)) c.1 c.2
  | .wots w =>
      w.Valid pk (wotsLeafAdrs adrs idx) (wotsPkGenTops prims sk pk (wotsLeafAdrs adrs idx))
        (wotsSign prims honestMsg sk pk (wotsLeafAdrs adrs idx)) honestMsg

/-- Unfolding equation for the `H`-collision branch of `XmssWitness.Valid`.  The first pair is the
honest child pair at the named node, read off the honest tree rather than supplied by the
witness. -/
@[simp] theorem XmssWitness.valid_hCollision {prims : Primitives p} (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (honestMsg : prims.Y) (z : ℕ)
    (c : prims.Y × prims.Y) :
    (XmssWitness.hCollision z c).Valid sk pk adrs idx honestMsg ↔
      0 < z ∧ z ≤ p.hp ∧
        xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z) ≠ c ∧
        prims.H pk (xmssNodeAdrs adrs z (idx / 2 ^ z))
            (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)).1
            (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)).2 =
          prims.H pk (xmssNodeAdrs adrs z (idx / 2 ^ z)) c.1 c.2 := Iff.rfl

/-- Unfolding equation for the WOTS+ branch of `XmssWitness.Valid`, exhibiting the three honest
objects it computes: the honest chain ends and the honest signature at the opened leaf, and the
honest message that signature signs. -/
@[simp] theorem XmssWitness.valid_wots {prims : Primitives p} (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (honestMsg : prims.Y)
    (w : WotsWitness p prims) :
    (XmssWitness.wots w).Valid sk pk adrs idx honestMsg ↔
      w.Valid pk (wotsLeafAdrs adrs idx) (wotsPkGenTops prims sk pk (wotsLeafAdrs adrs idx))
        (wotsSign prims honestMsg sk pk (wotsLeafAdrs adrs idx)) honestMsg := Iff.rfl

/-- **XMSS forgery dichotomy, four-way after unfolding.**  A signature at leaf `idx < 2 ^ h'` on a
forged message `msg` that recovers the honest XMSS root yields, for any honest message
`msg' ≠ msg`, either an `H`-collision at an internal node of the opened leaf's root path, or a
`WotsWitness` against the honest WOTS+ key material at that leaf.

Unfolding the second disjunct through `WotsWitness.Valid` splits it three further ways — a `T_len`
second preimage at `wotsPkAdrs (wotsLeafAdrs adrs idx)`, an `F`-preimage of the honest revealed
chain value, and an `F`-collision at a chain step — so the composite is four-way in all.  It is
stated in two parts rather than four because the three WOTS+ outcomes are `WotsWitnesses`' own and
restating them here would duplicate them.

The four branches are `valid_TCRTRH` (`FL_SL_XMSS_MT_ES.ec:3272-3273`), `valid_TCRPKCO`
(`:3270-3271`) and the two resolutions of `valid_WOTSTWES` (`:3268-3269`, resolved in
`WOTS_TW_ES.ec` at `nhchwcoll_hchwpre`, `:1299`), each specialised to one layer.

*Deterministic inclusion.* -/
theorem xmssPkFromSig_forgeryCases (valid : p.Valid) (prims : Primitives p)
    (laws : prims.core.ByteLaws) (idx : ℕ) (hidx : idx < 2 ^ p.hp) (sig : XmssSig p prims)
    (msg msg' : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (hne : msg ≠ msg')
    (hroot : xmssPkFromSig prims idx sig msg pk adrs = xmssRoot prims sk pk adrs) :
    (∃ (z : ℕ) (c : prims.Y × prims.Y), 0 < z ∧ z ≤ p.hp ∧
        xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z) ≠ c ∧
        prims.H pk (xmssNodeAdrs adrs z (idx / 2 ^ z))
            (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)).1
            (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)).2 =
          prims.H pk (xmssNodeAdrs adrs z (idx / 2 ^ z)) c.1 c.2) ∨
      ∃ w : WotsWitness p prims,
        w.Valid pk (wotsLeafAdrs adrs idx) (wotsPkGenTops prims sk pk (wotsLeafAdrs adrs idx))
          (wotsSign prims msg' sk pk (wotsLeafAdrs adrs idx)) msg' := by
  classical
  rcases xmssPkFromSig_cases prims idx hidx sig msg sk pk adrs hroot with hwots | hcoll
  · refine Or.inr ?_
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (findWotsWitness_isSome valid prims laws
      sig.wots msg (wotsSign prims msg' sk pk (wotsLeafAdrs adrs idx)) msg' pk
      (wotsLeafAdrs adrs idx) hne)
    refine ⟨w, ?_⟩
    have hsound := findWotsWitness_sound prims sig.wots msg
      (wotsSign prims msg' sk pk (wotsLeafAdrs adrs idx)) msg' pk (wotsLeafAdrs adrs idx)
      (by rw [hwots, wotsPkFromSig_wotsSign]) hw
    rwa [wotsPkFromSigTops_wotsSign] at hsound
  · exact Or.inl hcoll

/-- Compute an XMSS witness from a signature at leaf `idx` on the forged message `msg`, against the
honest key material at `adrs` and the honest message `msg'`: the `H`-collision on the opened leaf's
root path when the recovered leaf differs from the honest one, and otherwise the WOTS+ witness at
that leaf.

The branch is decided by the recovered leaf alone, not by the recovered root.  So unlike the WOTS+
and FORS extractors, this one never returns a witness that fails its own validity check on a
signature which misses the honest root — but what it returns on such a signature is decided by the
leaf test, and it is not always `none`.

With the recovered leaf *different* from the honest one the Merkle branch is taken, and there a
root mismatch does give `none`: `PerfectMerkleTree.findCollisionAddressed` descends from the root,
recursing only where the two openings' child pairs agree and returning `some` only where they
first differ under an equal parent, so a `some` already implies the root match.  With the recovered
leaf the *honest* one — an authentication path that misses the honest tree above a correctly
recovered leaf — the WOTS+ branch is taken, and whatever it returns there is valid all the same,
because its guard is the leaf test and that test is already `findWotsWitness_sound`'s own
hypothesis.  That is `findXmssWitness_sound_of_leaf` below, which beside the `some w` its
conclusion is about takes the leaf test and nothing else: a caller holding a leaf match and no root
match cites it rather than reproving it.  It says nothing about whether anything is returned:
existence on this branch is `findXmssWitness_isSome`'s, and what buys it there is `hne : msg ≠ msg'`
together with the validated parameters and the byte laws — never the root, as that theorem's proof
shows, though no statement here isolates the existence half.  At `msg = msg'` every chain's two step
counts agree, so the search can run out and give `none` however the climb went.

Over a 768-case sweep at the toy bundle of `HashSigTest.SLHDSA.XmssWitnesses` — sixteen chain-`3`
perturbations by three authentication-path choices, level `0`, level `1` or none, by sixteen path
perturbations, all of them on two distinct messages — 608 cases miss the honest root; the 552 of
those that take the Merkle branch all return `none`, the 56 that take the WOTS+ branch all return
a witness, and no case in the sweep returns an invalid one.  The 768 are cases, not distinct
signatures: the path mask is inert at the `none` level and mask `0` reproduces the honest path at
every level, so they realise 496 signatures.  The malformed-forgery canary there pins both halves.
`findXmssWitness_sound` carries the root hypothesis for a different reason, recorded on that
theorem.

The honest WOTS+ signature the second branch compares against is recomputed here from `sk` rather
than taken as an argument, so a caller cannot substitute a different one. -/
def findXmssWitness (prims : Primitives p) [DecidableEq prims.Y] (idx : ℕ)
    (sig : XmssSig p prims) (msg msg' : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : Option (XmssWitness p prims) :=
  let leafAdrs := wotsLeafAdrs adrs idx
  let recovered := wotsPkFromSig prims sig.wots msg pk leafAdrs
  if xmssLeaf prims sk pk adrs idx = recovered then
    (findWotsWitness prims sig.wots msg (wotsSign prims msg' sk pk leafAdrs) msg' pk
      leafAdrs).map .wots
  else
    (PerfectMerkleTree.findCollision (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs)
      idx recovered sig.auth.toList).map fun w => .hCollision w.1 w.2.2

/-- The extractor takes its WOTS+ branch exactly when the recovered leaf is the honest one.  The
bodies are not exposed, so this equation is what a consumer rewrites with. -/
theorem findXmssWitness_eq_wots_of_leaf (prims : Primitives p) [DecidableEq prims.Y] (idx : ℕ)
    (sig : XmssSig p prims) (msg msg' : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs)
    (hleaf : xmssLeaf prims sk pk adrs idx =
      wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx)) :
    findXmssWitness prims idx sig msg msg' sk pk adrs =
      (findWotsWitness prims sig.wots msg (wotsSign prims msg' sk pk (wotsLeafAdrs adrs idx)) msg'
        pk (wotsLeafAdrs adrs idx)).map .wots := by
  rw [findXmssWitness]; simp only [hleaf, if_pos]

/-- The extractor takes its Merkle branch exactly when the recovered leaf differs from the honest
one. -/
theorem findXmssWitness_eq_node_of_leaf_ne (prims : Primitives p) [DecidableEq prims.Y] (idx : ℕ)
    (sig : XmssSig p prims) (msg msg' : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs)
    (hleaf : xmssLeaf prims sk pk adrs idx ≠
      wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx)) :
    findXmssWitness prims idx sig msg msg' sk pk adrs =
      (PerfectMerkleTree.findCollision (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs)
        idx (wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx))
        sig.auth.toList).map fun w => .hCollision w.1 w.2.2 := by
  rw [findXmssWitness]; simp only [hleaf, if_false]

/-- **Extractor soundness on the WOTS+ branch, without the root.**  When the recovered leaf is the
honest one — the test `findXmssWitness` performs itself — whatever the extractor returns satisfies
`XmssWitness.Valid` against the honest XMSS tree at `adrs`, the opened leaf `idx` and the honest
message `msg'`.  Beside the `some w` the conclusion is about, the leaf test is the only hypothesis:
no root match, no leaf bound `hidx`, no message distinctness, no `p.Valid` and no `ByteLaws`.  It is
what reaches `findWotsWitness_sound`'s public-key hypothesis, through `wotsPkFromSig_wotsSign`.

This is the half of `findXmssWitness_sound` that survives a root mismatch, and that theorem's WOTS+
branch is this lemma applied.  A caller holding a leaf match and no root match — an authentication
path that misses the honest tree above a correctly recovered leaf, which is what `authForgery` of
`HashSigTest.SLHDSA.XmssWitnesses` is — has no root hypothesis to supply and needs none.  Nothing
here says anything is returned; existence is `findXmssWitness_isSome`'s and needs `hne`.

*Deterministic inclusion.* -/
theorem findXmssWitness_sound_of_leaf (prims : Primitives p) [DecidableEq prims.Y] (idx : ℕ)
    (sig : XmssSig p prims) (msg msg' : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs)
    (hleaf : xmssLeaf prims sk pk adrs idx =
      wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx))
    {w : XmssWitness p prims} (hw : findXmssWitness prims idx sig msg msg' sk pk adrs = some w) :
    w.Valid sk pk adrs idx msg' := by
  rw [findXmssWitness_eq_wots_of_leaf prims idx sig msg msg' sk pk adrs hleaf,
    Option.map_eq_some_iff] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  rw [xmssLeaf_eq_wotsPkGen] at hleaf
  have hsound := findWotsWitness_sound prims sig.wots msg
    (wotsSign prims msg' sk pk (wotsLeafAdrs adrs idx)) msg' pk (wotsLeafAdrs adrs idx)
    (by rw [← hleaf, wotsPkFromSig_wotsSign]) hu
  rw [XmssWitness.valid_wots]
  rwa [wotsPkFromSigTops_wotsSign] at hsound

/-- **Extractor soundness.**  The witness `findXmssWitness` returns satisfies `XmssWitness.Valid`
against the honest XMSS tree at `adrs`, the opened leaf `idx` and the honest message `msg'`.

The root hypothesis is used only by the Merkle branch, where
`PerfectMerkleTree.findCollision_oriented` needs it to identify the first pair returned with the
honest child pair at the node named; the WOTS+ branch is `findXmssWitness_sound_of_leaf`, which
this proof calls and which takes neither the root hypothesis nor the leaf bound, being guarded by
the leaf test the extractor performs itself.  The leaf bound `hidx` is likewise used only by the
Merkle branch, to place the opened leaf inside the honest tree.

`findCollision` looks unconditionally oriented — it reads its first pair off the honest tree, and
`findCollision_sound` already pins the address to `idx / 2 ^ h` without a root hypothesis — but
`findCollision_oriented`, which is what this proof calls, bundles orientation with existence and
takes the root hypothesis, as does the kernel `findCollisionAddressed_oriented` it delegates to, so
there is nothing weaker to appeal to.  The same hypothesis appears for the same reason on
`HashSig.SLHDSA.Security.findForsTreeCollision_sound`.  It costs nothing here:
`findXmssWitness_isSome` needs the root match for existence in any case, so a caller that wants a
witness at all is already holding it.

As `XmssWitness.Valid` records, this says nothing about whether those honest objects were committed
as game targets.

*Deterministic inclusion.* -/
theorem findXmssWitness_sound (prims : Primitives p) [DecidableEq prims.Y] (idx : ℕ)
    (hidx : idx < 2 ^ p.hp) (sig : XmssSig p prims) (msg msg' : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs)
    (hroot : xmssPkFromSig prims idx sig msg pk adrs = xmssRoot prims sk pk adrs)
    {w : XmssWitness p prims} (hw : findXmssWitness prims idx sig msg msg' sk pk adrs = some w) :
    w.Valid sk pk adrs idx msg' := by
  by_cases hleaf : xmssLeaf prims sk pk adrs idx =
      wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx)
  · exact findXmssWitness_sound_of_leaf prims idx sig msg msg' sk pk adrs hleaf hw
  · rw [findXmssWitness_eq_node_of_leaf_ne prims idx sig msg msg' sk pk adrs hleaf,
      Option.map_eq_some_iff] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have hlen : sig.auth.toList.length = p.hp := by simp
    have hclimb : PerfectMerkleTree.climb (xmssNodeHash prims pk adrs) idx
        (wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx)) sig.auth.toList =
        PerfectMerkleTree.merkleRoot (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs)
          p.hp (idx / 2 ^ p.hp) := by
      rw [Nat.div_eq_of_lt hidx]
      simpa only [xmssPkFromSig_eq_climb, xmssRoot_eq_node, xmssNode_eq_merkleRoot] using hroot
    obtain ⟨z, c, hor⟩ := PerfectMerkleTree.findCollision_oriented
      (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) p.hp idx _ _ hlen hclimb hleaf
    rw [hor, Option.some.injEq] at hu
    subst hu
    obtain ⟨hzpos, hzle, hne, hcoll⟩ := PerfectMerkleTree.findCollision_sound
      (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) p.hp idx _ _ hlen z _ c hor
    refine ⟨hzpos, hzle, ?_, ?_⟩
    · rw [xmssHonestChildren]; exact hne
    · rw [xmssHonestChildren]
      simpa only [xmssNodeHash_eq_h, PerfectMerkleTree.honestChildren] using hcoll

/-- **Extractor completeness.**  On two distinct messages, at a leaf inside the tree, against a
signature that recovers the honest root, the search always returns a witness: either the recovered
leaf differs from the honest one and `PerfectMerkleTree.findCollision_oriented` supplies the
collision, or it agrees and `findWotsWitness_isSome` supplies a WOTS+ witness.

The two halves need different hypotheses.  The Merkle half needs the root match and the leaf bound
and not the message distinctness; the WOTS+ half needs the message distinctness, the validated
parameters and the byte laws, and neither the root match nor the leaf bound.

*Deterministic inclusion.* -/
theorem findXmssWitness_isSome (valid : p.Valid) (prims : Primitives p) [DecidableEq prims.Y]
    (laws : prims.core.ByteLaws) (idx : ℕ) (hidx : idx < 2 ^ p.hp) (sig : XmssSig p prims)
    (msg msg' : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (hne : msg ≠ msg')
    (hroot : xmssPkFromSig prims idx sig msg pk adrs = xmssRoot prims sk pk adrs) :
    (findXmssWitness prims idx sig msg msg' sk pk adrs).isSome := by
  rw [findXmssWitness]
  split
  · rw [Option.isSome_map]
    exact findWotsWitness_isSome valid prims laws sig.wots msg
      (wotsSign prims msg' sk pk (wotsLeafAdrs adrs idx)) msg' pk (wotsLeafAdrs adrs idx) hne
  · rename_i hleaf
    have hlen : sig.auth.toList.length = p.hp := by simp
    have hclimb : PerfectMerkleTree.climb (xmssNodeHash prims pk adrs) idx
        (wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx)) sig.auth.toList =
        PerfectMerkleTree.merkleRoot (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs)
          p.hp (idx / 2 ^ p.hp) := by
      rw [Nat.div_eq_of_lt hidx]
      simpa only [xmssPkFromSig_eq_climb, xmssRoot_eq_node, xmssNode_eq_merkleRoot] using hroot
    obtain ⟨z, c, hor⟩ := PerfectMerkleTree.findCollision_oriented
      (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs) p.hp idx _ _ hlen hclimb hleaf
    rw [Option.isSome_map, hor, Option.isSome_some]

/-! ## Ledger membership and encoded distinctness

*Transcript transport.*  Every address an XMSS witness names at a reachable layer position is a
member of the slice-1 role ledger it is submitted against, and — under
`EncodedTargetLedgerConditions` — distinct addresses of that ledger carry distinct encoded tweaks.

Only the `hCollision` branch has a ledger of its own here: it attacks `xmssH`, whose ledger is
`xmssNodeAddresses` (`mem_xmssNodeAddresses_of_leaf`, `xmssNodeAdrsKey_injective`).  The `wots`
branch's three ledgers are slice-1 objects of `HashSig.SLHDSA.Security.ReachableTargets`, reached
by `WotsWitnesses`' membership lemmas and by `mem_wotsPkAddresses` directly, at the address
`wotsInstanceAdrs pos`, which `wotsLeafAdrs_eq_wotsInstanceAdrs` identifies with the address an
XMSS witness names.

These are statements about the ledgers, not about any execution: nothing here says a logged query
carried the witness values. -/

variable {vp : ValidatedParams}

/-- The WOTS+ base address an XMSS witness names at a reachable layer position is the ledger's own
`wotsInstanceAdrs`.  This is what lets the three WOTS+ ledger and encoded-distinctness lemmas of
`HashSig.SLHDSA.Security.WotsWitnesses` be applied to the `wots` branch without restatement. -/
theorem wotsLeafAdrs_eq_wotsInstanceAdrs (pos : LayerPosition vp) :
    wotsLeafAdrs pos.toAdrs pos.leaf.val = wotsInstanceAdrs pos := rfl

/-- Every internal node of height `0 < z ≤ h'` on the root path of the leaf a reachable layer
position opens is a listed `xmssH` target.  The horizontal index bound is `xmssNodeIndex_lt`
applied to `pos.leaf.isLt`, so the caller supplies only the two height bounds. -/
theorem mem_xmssNodeAddresses_of_leaf (pos : LayerPosition vp) {z : ℕ} (hz : 0 < z)
    (hzh : z ≤ vp.params.hp) :
    xmssNodeAdrs pos.toAdrs z (pos.leaf.val / 2 ^ z) ∈ xmssNodeAddresses vp :=
  mem_xmssNodeAddresses_of_position vp pos hz hzh
    (xmssNodeIndex_lt vp.params pos.leaf.isLt hzh)

/-- Under the encoded-ledger conditions, distinct XMSS internal-node coordinates carry distinct
encoded tweaks: two `hCollision` witnesses at different `(tree, height, index)` tuples attack
different tweaks of `xmssHTcrCProblem`.

The coordinate is stated in the bounded form a witness produces — `0 < z ≤ h'` and a horizontal
index below `2 ^ (h' - z)` — because those are exactly the coordinates `xmssNodeAddresses` lists.
The conditions are consumed, not assumed afresh: `approvedEncodedTargetLedgerConditions` discharges
them for every approved profile, so the SHA-2 zero fallback is never treated as unreachable. -/
theorem xmssNodeAdrsKey_injective {prims : Primitives vp.params}
    (conditions : EncodedTargetLedgerConditions vp prims)
    {coord coord' : LayerTreeCoord vp} {z z' j j' : ℕ}
    (hz : 0 < z) (hzh : z ≤ vp.params.hp) (hj : j < 2 ^ (vp.params.hp - z))
    (hz' : 0 < z') (hzh' : z' ≤ vp.params.hp) (hj' : j' < 2 ^ (vp.params.hp - z'))
    (hkey : prims.adrsToKey (xmssNodeAdrs coord.toAdrs z j) =
      prims.adrsToKey (xmssNodeAdrs coord'.toAdrs z' j')) :
    coord = coord' ∧ z = z' ∧ j = j' := by
  have hnodup : ((allXmssTrees vp).product (perfectInternalCoords vp.params.hp)).Nodup :=
    (allXmssTrees_nodup vp).product (perfectInternalCoords_nodup vp.params.hp)
  have hmemc : (coord, (z, j)) ∈
      (allXmssTrees vp).product (perfectInternalCoords vp.params.hp) := by
    simp [mem_perfectInternalCoords_of_bounds hz hzh hj]
  have hmemd : (coord', (z', j')) ∈
      (allXmssTrees vp).product (perfectInternalCoords vp.params.hp) := by
    simp [mem_perfectInternalCoords_of_bounds hz' hzh' hj']
  have hinj := (encodeTargets_nodup_iff_injOn prims (xmssNodeAddresses vp)
    (xmssNodeAddresses_nodup vp)).1 conditions.xmssH
  have hadrs := hinj _ (mem_xmssNodeAddresses vp coord hz hzh hj) _
    (mem_xmssNodeAddresses vp coord' hz' hzh' hj') hkey
  have hcoord := (List.nodup_map_iff_inj_on hnodup).1 (xmssNodeAddresses_nodup vp)
    (coord, (z, j)) hmemc (coord', (z', j')) hmemd hadrs
  simp only [Prod.mk.injEq] at hcoord
  exact ⟨hcoord.1, hcoord.2.1, hcoord.2.2⟩

/-! ## Game shapes

`XmssWitness.Valid` is stated in the construction's own vocabulary (`prims.H` at a structural
`Adrs`, and `WotsWitness.Valid` for the other branch).  The bridge below rewrites the
`hCollision` branch into `xmssHTcrCProblem`'s `eval` vocabulary at the encoded tweak, using
`CanonicalGames.xmssHTcrCProblem_eval_adrsToKey`.  That equation is already on the slice-6 base, so
this module adds no new `Problem`-`eval` equation of its own; the bridge below is a consumer of
slice 6's.  The proof names the rewrite explicitly rather than relying on its `@[simp]` attribute,
because the sibling bridges of `CanonicalGames` do not all carry one.  It rewrites *both* sides of
the hash equation, so the equation it concludes is stated in the game's vocabulary; the remaining
conjuncts are carried through unchanged and stay in the construction's — the two height bounds,
which are ledger-placement conditions no game states, and the distinctness, which names
`xmssHonestChildren` directly.  It changes presentation only: no game is played and no advantage is
stated.

There is no `wots`-branch bridge here.  `HashSig.SLHDSA.Security.WotsWitnesses` already supplies
one per WOTS+ constructor — `wotsWitness_valid_tlCollision_eval`, `wotsWitness_valid_fPreimage_eval`
and `wotsWitness_valid_fCollision_eval` — and `XmssWitness.valid_wots` reduces the branch to
exactly their hypothesis, at the base address `wotsLeafAdrs adrs idx`. -/

variable (prims : Primitives p)

/-- The `H`-collision branch, read in `xmssHTcrCProblem`'s vocabulary: the submitted pair and the
honest child pair at the named node are distinct and evaluate equally at the encoded node tweak.
The game's message type is the ordered pair `prims.Y × prims.Y`, so the two children are supplied
as one message and their order is part of the claim. -/
theorem xmssWitness_valid_hCollision_eval [SampleableType prims.PkSeed] (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (honestMsg : prims.Y) (z : ℕ)
    (c : prims.Y × prims.Y) (h : (XmssWitness.hCollision z c).Valid sk pk adrs idx honestMsg) :
    0 < z ∧ z ≤ p.hp ∧
      xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z) ≠ c ∧
      (xmssHTcrCProblem prims).th.eval pk (prims.adrsToKey (xmssNodeAdrs adrs z (idx / 2 ^ z)))
          (xmssHonestChildren prims sk pk adrs z (idx / 2 ^ z)) =
        (xmssHTcrCProblem prims).th.eval pk
          (prims.adrsToKey (xmssNodeAdrs adrs z (idx / 2 ^ z))) c :=
  ⟨h.1, h.2.1, h.2.2.1, by
    rw [xmssHTcrCProblem_eval_adrsToKey, xmssHTcrCProblem_eval_adrsToKey]
    exact h.2.2.2⟩

end SLHDSA.Security
