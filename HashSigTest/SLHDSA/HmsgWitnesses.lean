module
public import HashSig.SLHDSA.Security.HmsgWitnesses
public import HashSig.SLHDSA.GeneralScheme

/-!
# SLH-DSA `H_msg` ITSR bridge canaries

Executable checks that the two coordinate maps an `HmsgIndex` supplies are the ones the lane's FORS
statements are indexed by, that the widening of the hashed input from a message to
`⟨PK.seed, PK.root, M⟩` costs nothing inside one key pair and buys the adversary something outside
one, and that the first-uncovered-index extractor returns the index it claims to — all evaluated at
values, not restated from the theorems.

## The profile is the scheme-dispatch fixture's, and why it is copied rather than imported

The bundle below is the one `HashSigTest.SLHDSA.SchemeWitnesses` builds — the same seven
parameters, the same six byte maps, the same three honest seeds and second public seed, the same
published root — so the two executables run on one profile, and a reviewer can check that by
diffing the two blocks.  It is copied rather than imported because a `lean_exe` root must own its
`main`, and a module that imports the other one cannot declare `main` at all: the attempt reports
`` `main` has already been declared``, and had it not, the executable would silently link the
imported `main` and run the other fixture.  The lane has no shared fixture module yet, and adding
one would edit a merged, reviewed file from inside this pull request.

That diff has exactly four entries, all deliberate.  The failure message names this executable.
`toy` carries no `@[expose]` here, because removing that attribute in this file produces no errors
at all.  And the two remaining attribute comments carry this file's own measured error counts and
error text rather than the other fixture's — every attribute comment here was written by removing
the attribute and reading what Lean said.

## What the profile already supplies, and the one thing it does not

Everything the coverage canaries need was already in it.  `k = 2` gives every digest two semantic
indices, so "every index covered" and "some index covered" are different events and
`List.find?`'s first-match choice is visible; `a = 1` gives two leaves per FORS tree, so the four
global leaves `0, 1, 2, 3` are distinct and the tree offset in `globalLeaf` is load-bearing; the
public seed is a byte rather than a unit and `H_msg` reads all four of its FIPS arguments, so the
`⟨PK.seed, PK.root, M⟩` record is not inert and a candidate can be moved off the honest key pair.

The one addition is `blindPrimitives`: the same bundle with a single field replaced by an `H_msg`
that ignores the seed and root it is handed.  Nothing in the scheme-dispatch fixture needed such a
bundle, and the strictness of the widening cannot be exhibited without one.

## The fixture's six pairs

One forged pair and five signing queries, all at the honest key pair.  The forged message produces
the digest `[0xBB, 0x27, 0xAB]`, which names layer-zero tree three, leaf three, and selects FORS
tree zero's local leaf one and FORS tree one's local leaf zero.  Four of the queries realise all
four coverage patterns against that pair of indices:

* `qBoth` reproduces the forged digest exactly under a different randomizer *and* a different
  message, so it covers both indices while leaving the pair fresh — the fixture's win;
* `qFirst` sits at the same FORS instance and covers the first index only;
* `qSecond` sits at the same FORS instance and covers the second index only;
* `qOther` sits at a different FORS instance and covers neither.

The fifth, `qHonestOnly`, covers both indices at the honest key pair *without* reproducing the
digest — coverage is a relation between selected indices, not between digests, and a fixture whose
only win came from a digest collision would not have shown that.  It is also what makes the fibre
equivalence's key pair falsifiable: at either of the two moved key pairs it covers neither index, so
reading the source-shaped side anywhere but at the honest key pair changes the answer.  Without it
the equivalence canary passed under a mutant that read that side at a different public seed, because
`qBoth`'s digest collision is an additive one that survives moving the seed and the root.

`qSecond` and `qOther` share a randomizer and differ only in their message, which is asserted: ITSR
freshness is *pair* freshness, and a fixture in which no two queries shared a key could not show
that.

## Which conjunct each canary falsifies

`ITSRProblem.Wins` has two conjuncts and both are falsified on their own.  Against `[qC, qBoth]`
the candidate is one of the targets, so freshness fails while coverage is asserted to hold; against
`[qOther]`, `[qFirst]` or `[qSecond]` coverage fails while freshness is asserted to hold; against
`[qBoth]` both hold and the pair wins.

`findUncoveredIndex_eq_some_iff` has three parts, and the third — that every index before the
returned one is covered — is the one soundness does not decide.  Four target sets separate them:
with only the second index covered the first comes back; with only the first covered the second
comes back; with neither covered the first comes back and the second is required *not* to, which is
the case a last-match extractor would get wrong; with both covered nothing comes back.

`HmsgIndex.ext_of_coords` takes two hypotheses and neither is idle: over all sixty-four semantic
indices of this profile the pair `(instance address, global leaf)` is injective, while the address
alone is not, the global leaf alone is not, and neither is the address paired with the *local* leaf
— the naive reading of `globalLeaf` with the tree offset dropped.

`coord_unrevealed_of_notMem` denies a conjunction of two, and both halves are exercised by
different queries in one transcript: `qFirst` sits at the uncovered index's own instance address and
misses on the leaf, `qOther` misses on the address.  The converse is asserted too — for the index
that *is* covered, some query and tree do land on its coordinate — so the lemma is not vacuous.

`wins_of_hmsg_agree` takes two hypotheses and both are falsified: with the two inputs equal the win
fails on freshness, and at the fixture's own bundle, where the two digests differ, it fails on
coverage.

## The naive identifications this fixture is built to reject

* *That `globalLeaf` is the local leaf.*  Rejected by evaluating the FORS leaf address at the
  extracted coordinate against a table of four `Adrs` records written out by hand — layer zero,
  layer-zero tree three, `FORS_TREE`, key-pair address three, height zero, global index — rather
  than against `forsSigLeafIndex`.  A shift applied to `globalLeaf` and to its bridge together
  type-checks, proves, and fails at that table.
* *That `findUncoveredIndex` returns "an" uncovered index.*  Rejected by the empty-transcript case,
  where both are uncovered and the returned one is required to be the earlier.
* *That the ITSR candidate may carry any `(PK.seed, PK.root)`.*  Rejected by the two off-fibre
  candidates, which are asserted to be fresh — for free, against a transcript that contains their
  underlying pair — and asserted still not to win.
* *That the widened game is the source's game.*  Rejected by `blindPrimitives`, which agrees with
  the fixture's bundle on every source-shaped case the fixture runs and still loses the widened game
  to a single target query, which the fixture's own bundle refuses.

## The pins

Every one of the thirty-five theorems the library module exports appears as an `example` at this
bundle's types, with generic arguments where the statement has them.  Seven further `example`s are
the profile's own `decide` pins, inherited with the copied block.
-/

public section

namespace SLHDSA.HmsgWitnessesTest

open Security Security.CanonicalGames GeneralHypertree KeyedHash

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"H_msg ITSR check failed: {label}")

/-! ## The toy profile

Two hypertree layers of height two, two FORS trees of height one, `w = 16`, `len = 4`. -/

-- Exposed, and what that attribute is for was read off the errors its removal produces in this
-- file.  Without `@[expose]` on `toyParams`, 41 errors, the first inside the bundle at
-- `yToBytes := id`, where `id` will not take the type `Bytes 1 → Bytes toyParams.n`.  `toy` below
-- needs no exposure of its own here, and neither do the secret map, the tweak map, the randomizer
-- or the digest map.  Nothing outside this executable consumes any of them.
/-- Two layers of height two, two FORS trees of height one. -/
@[expose] def toyParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 4 }

theorem toyValid : toyParams.Valid := by decide

/-- The validated form of `toyParams`.  Unexposed: the only declaration that mentions it is the
`BottomPosition.ofDigestParts` pin below, which is an `example` and so unfolds what it needs
without exposure.  Removing the attribute gives no errors at all. -/
def toy : ValidatedParams := ⟨toyParams, toyValid⟩

example : toyParams.w = 16 := by decide
example : toyParams.len = 4 := by decide
example : toyParams.m = 3 := by decide
example : toyParams.digestBytes = 1 := by decide
example : toyParams.treeIdxBytes = 1 := by decide
example : toyParams.leafIdxBytes = 1 := by decide
example : toyParams.t = 2 := by decide

/-- The exclusive-or fold through which the toy `H_msg` and `PRF_msg` read a message.  Two messages
with equal folds therefore share a digest; `checkToyBundle` exhibits such a pair and asserts the
digests agree, and separately asserts that messages with different folds do not. -/
def byteFold (m : List Byte) : UInt8 := m.foldl (fun acc b => acc ^^^ b) 0

/-- A nonlinear byte mix.  Without it the digest bytes are linear in their inputs and their low bits
— the two hypertree indices — collapse to constants at a fixed key pair, which would make the
digest-derived position inert. -/
def mixByte (x : UInt8) : UInt8 := ((x * (181 : UInt8)) ^^^ (x >>> (3 : UInt8))) + 97

/-- The per-address secret values the toy `PRF` hands out.  Both seeds and all six address words
enter, so no two addresses and no two key pairs share secret material. -/
def toySecret (seed sk : UInt8) (a : Adrs) : UInt8 :=
  UInt8.ofNat ((seed.toNat * 19 + sk.toNat * 23 + a.layer * 101 + a.tree * 53 + a.type * 61 +
    a.word1 * 37 + a.word2 * 11 + a.word3 * 7 + 5) % 256)

/-- A per-address byte mixed into every `Thash` output, taking the public seed and all six address
words, so the same children at two different layers, trees, types or nodes hash differently. -/
def toyTweak (seed : UInt8) (a : Adrs) : UInt8 :=
  UInt8.ofNat ((seed.toNat * 17 + a.layer * 131 + a.tree * 71 + a.type * 41 + a.word1 * 29 +
    a.word2 * 43 + a.word3 * 97) % 256)

/-- The toy `PRF_msg`: the message randomizer FIPS 205 Algorithm 19 line 3 derives.  It reads the
per-signature `addrnd`, so two signings of one message under two different randomness values differ.
`checkToyBundle` asserts that. -/
def toyRandomizer (skPrf addrnd : UInt8) (msg : List Byte) : UInt8 :=
  mixByte (UInt8.ofNat
    ((skPrf.toNat * 13 + addrnd.toNat * 47 + (byteFold msg).toNat * 5 + 1) % 256))

/-- Byte `i` of the toy `H_msg` digest.  All four FIPS inputs enter every byte — the randomizer, the
public seed, the published root and the message fold — so the FORS message and both hypertree
indices move when any of them moves.  `checkToyBundle` asserts each of the four separately. -/
def toyDigestByte (r seed root : UInt8) (msg : List Byte) (i : ℕ) : UInt8 :=
  mixByte (UInt8.ofNat ((r.toNat * (6 * i + 37) + seed.toNat * (10 * i + 53) +
    root.toNat * (14 * i + 89) + (byteFold msg).toNat * (22 * i + 149) + (30 * i + 7)) % 256))

-- Exposed and `@[reducible]`, for two different reasons, each read off the errors that removing
-- that attribute alone produces in this file.  Exposed, for code generation: without it, 51 errors,
-- the first at `instance : DecidableEq toyPrimitives.Y` just below, reading `Compilation failed,
-- locally inferred compilation type differs from type that would be inferred in other modules` and
-- naming `toyPrimitives ↦ 2`, with the rest following it down the compiled declarations.
-- Reducible, because its carrier types have to unfold to `Bytes 1` for instance resolution to
-- reach them: without it, three errors and only these — `byteOf`'s `y[0]` finds no
-- `GetElem toyPrimitives.Y ℕ` instance and cannot prove its index valid, and `wideWins` finds no
-- `DecidableEq (HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)`.  Nothing outside this
-- executable consumes it.
/-- The toy bundle: one byte per node, a collapsing order- and address-sensitive `Thash`, and an
`H_msg` that depends on all four of its arguments. -/
@[expose, reducible] def toyPrimitives : Primitives toyParams where
  PkSeed := Bytes 1
  SkSeed := Bytes 1
  SkPrf := Bytes 1
  Y := Bytes 1
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun pk sk adrs => Vector.replicate 1 (toySecret pk[0] sk[0] adrs)
  PRFmsg := fun skPrf addrnd msg => Vector.replicate 1 (toyRandomizer skPrf[0] addrnd[0] msg)
  yToBytes := id
  Thash := fun pk adrs children =>
    Vector.replicate 1
      ((children.foldl (fun (acc : UInt8) (y : Bytes 1) => (acc <<< 2) ^^^ (y[0] >>> 1))
        (0 : UInt8)) ^^^ toyTweak pk[0] adrs)
  Hmsg := fun r pk root msg =>
    Vector.ofFn fun i => toyDigestByte r[0] pk[0] root[0] msg i.val

instance : DecidableEq toyPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 1))

instance : SampleableType toyPrimitives.PkSeed := inferInstanceAs (SampleableType (Bytes 1))

instance : SampleableType toyPrimitives.Y := inferInstanceAs (SampleableType (Bytes 1))

theorem toyByteLaws : toyPrimitives.core.ByteLaws := ⟨fun _ _ h => h⟩

/-- A one-byte node. -/
def node (x : UInt8) : toyPrimitives.Y := Vector.replicate 1 x

/-- The byte inside a node. -/
def byteOf (y : toyPrimitives.Y) : UInt8 := y[0]

/-! ## Honest key material -/

/-- The honest secret seed. -/
def skSeed : toyPrimitives.SkSeed := node 0x11

/-- The honest message-PRF key. -/
def skPrf : toyPrimitives.SkPrf := node 0x22

/-- The honest public seed, which is a byte rather than a unit, so the `pkSeed` argument of every
statement below is load-bearing. -/
def pkSeed : toyPrimitives.PkSeed := node 0x33

/-- A second public seed, used only to assert that the first one is load-bearing. -/
def otherPkSeed : toyPrimitives.PkSeed := node 0x99

/-- The published hypertree root. -/
def pkRoot : toyPrimitives.Y := GeneralHypertree.root toy toyPrimitives skSeed pkSeed


/-! ## The ITSR fixture data

One candidate pair and four target pairs, all at the honest key pair, chosen so that the four
coverage patterns a canary needs are all realised: both of the candidate's indices covered, only the
first covered, only the second covered, and neither. -/

/-- The randomizer FIPS 205 Algorithm 19 line 3 derives for a message under a chosen `addrnd`. -/
def rOf (addrnd : UInt8) (msg : List Byte) : toyPrimitives.Y :=
  toyPrimitives.PRFmsg skPrf (node addrnd) msg

/-- The Algorithm 19 line 5 digest a randomizer and a message produce at the honest key pair. -/
def digestOf (r : toyPrimitives.Y) (msg : List Byte) : Bytes toyParams.m :=
  toyPrimitives.Hmsg r pkSeed pkRoot msg

/-- A signing query, as the pair the ITSR game records: the randomizer the signer sampled and the
message it signed. -/
def queryOf (addrnd : UInt8) (msg : List Byte) : toyPrimitives.Y × List Byte :=
  (rOf addrnd msg, msg)

/-- The forged message.  Its digest is `[0xBB, 0x27, 0xAB]`, naming layer-zero tree three, leaf
three, and opening FORS tree zero at its local leaf one and FORS tree one at its local leaf zero. -/
def msgC : List Byte := [0x0A, 0x0B]

/-- The forged pair. -/
def qC : toyPrimitives.Y × List Byte := queryOf 0x66 msgC

/-- A query whose digest is the forged one exactly, under a different randomizer and a different
message.  Both of the forged pair's indices are covered by this one query, and the two pairs still
differ, so it is the fixture's win. -/
def qBoth : toyPrimitives.Y × List Byte := queryOf 0x99 [0x21]

/-- A query at the same FORS instance whose FORS message opens tree zero at the forged local leaf
and tree one somewhere else, so it covers the forged pair's *first* index only. -/
def qFirst : toyPrimitives.Y × List Byte := queryOf 0x77 [0x01, 0x02]

/-- A query at the same FORS instance whose FORS message opens tree one at the forged local leaf and
tree zero somewhere else, so it covers the forged pair's *second* index only. -/
def qSecond : toyPrimitives.Y × List Byte := queryOf 0x77 [0x13]

/-- A query at a different FORS instance altogether, covering neither. -/
def qOther : toyPrimitives.Y × List Byte := queryOf 0x11 [0x05]

/-- A query that covers both of the forged pair's indices at the honest key pair while producing a
*different* digest, and covers neither at either of the two moved key pairs.  It is what makes the
fibre equivalence's key pair falsifiable: reading its source-shaped side anywhere but at the honest
key pair changes the answer. -/
def qHonestOnly : toyPrimitives.Y × List Byte := queryOf 0x00 [0x03]

/-- The forged digest. -/
def digestC : Bytes toyParams.m := digestOf qC.1 qC.2

/-- The forged digest's split. -/
def partsC : DigestParts toyParams := splitDigest toyParams digestC

/-- The forged pair read as an ITSR candidate at the honest key pair. -/
def candidateC : toyPrimitives.Y × HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y :=
  (qC.1, ⟨pkSeed, pkRoot, qC.2⟩)

/-- The forged pair read at a *different* public seed.  Its message and randomizer are the forged
ones; only the seed moves. -/
def candidateOffSeed : toyPrimitives.Y × HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y :=
  (qC.1, ⟨otherPkSeed, pkRoot, qC.2⟩)

/-- A second published root, used only to move the fourth `H_msg` argument. -/
def otherPkRoot : toyPrimitives.Y := node (byteOf pkRoot + 1)

/-- The forged pair read at a different published root. -/
def candidateOffRoot : toyPrimitives.Y × HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y :=
  (qC.1, ⟨pkSeed, otherPkRoot, qC.2⟩)

/-- Embed a query list at the honest key pair. -/
def embed (queries : List (toyPrimitives.Y × List Byte)) :
    ITSRTranscript toyPrimitives.Y (HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y) :=
  embedTargets toyPrimitives pkSeed pkRoot queries

/-- Whether the wide game's winning condition holds, as a boolean. -/
def wideWins (queries : List (toyPrimitives.Y × List Byte))
    (candidate : toyPrimitives.Y × HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y) : Bool :=
  decide ((hmsgItsrProblem toyPrimitives).Wins (embed queries) candidate)

/-- Whether the source-shaped game's winning condition holds at a chosen key pair, as a
boolean. -/
def narrowWinsAt (ps : toyPrimitives.PkSeed) (pr : toyPrimitives.Y)
    (queries : List (toyPrimitives.Y × List Byte))
    (candidate : toyPrimitives.Y × List Byte) : Bool :=
  decide ((hmsgNarrowItsrProblem toyPrimitives ps pr).Wins queries candidate)

/-- Whether the source-shaped game's winning condition holds at the honest key pair, as a
boolean. -/
def narrowWins (queries : List (toyPrimitives.Y × List Byte))
    (candidate : toyPrimitives.Y × List Byte) : Bool :=
  narrowWinsAt pkSeed pkRoot queries candidate

/-! ## Every `HmsgIndex` of the profile

Sixty-four in all: four layer-zero trees, four leaves in each, two FORS trees, two leaves in each.
The coordinate sweeps below run over all of them. -/

/-- All sixty-four semantic indices of the toy profile. -/
def allIndices : List (HmsgIndex toyParams) :=
  (List.finRange (2 ^ (toyParams.h - toyParams.hp))).flatMap fun t =>
    (List.finRange (2 ^ toyParams.hp)).flatMap fun l =>
      (List.finRange toyParams.k).flatMap fun i =>
        (List.finRange (2 ^ toyParams.a)).map fun j => ⟨t, l, i, j⟩

/-- The FORS leaf address at global index `j` inside the forged instance, written out by hand:
layer zero, layer-zero tree three, type `FORS_TREE`, key-pair address three, height zero, and the
global leaf in the tree-index word.  Not built from `forsNodeAdrs`, so a change in how a global
index reaches the address moves this table. -/
def forgedLeafAdrsTable (j : ℕ) : Adrs := ⟨0, 3, AddrType.forsTree.toCode, 3, 0, j⟩

/-- The FORS instance address of the forged digest, written out by hand. -/
def forgedForsAdrsTable : Adrs := ⟨0, 3, AddrType.forsTree.toCode, 3, 0, 0⟩

/-- The first index the forged digest selects, written out by hand: layer-zero tree three, leaf
three, FORS tree zero, local leaf one. -/
def forgedIndex0 : HmsgIndex toyParams :=
  ⟨⟨3, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩

/-- The second: the same instance, FORS tree one, local leaf zero. -/
def forgedIndex1 : HmsgIndex toyParams :=
  ⟨⟨3, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩⟩

/-- The two together, in the order `hmsgIndices` produces them. -/
def forgedIndexTable : List (HmsgIndex toyParams) := [forgedIndex0, forgedIndex1]

/-- Which of the forged pair's two indices a query list covers. -/
def coversPattern (queries : List (toyPrimitives.Y × List Byte)) : Bool × Bool :=
  let selected := (hmsgItsrProblem toyPrimitives).targetIndexSet (embed queries)
  (decide (forgedIndex0 ∈ selected), decide (forgedIndex1 ∈ selected))

/-- The fixture's bundle with one field changed: an `H_msg` that ignores the `PK.seed` and
`PK.root` it is handed and hashes at the fixture's own key pair instead.

Every other field, and every carrier type, is the fixture's own, and its source-shaped problem at
*any* key pair is the fixture's source-shaped problem at the honest one — `checkStrictness` asserts
that on the fixture's cases rather than assuming it — while its widened game admits the one-query
break `wins_of_hmsg_agree` describes. -/
-- Exposed and `@[reducible]`, both measured the way the bundle above was.  Exposed: without it,
-- nine errors — the three instances just below report `Compilation failed, locally inferred
-- compilation type differs from type that would be inferred in other modules` naming
-- `blindPrimitives`, `checkStrictness` follows, and `main` and the root `main` then fail as
-- `consider marking it as 'noncomputable'`.  Reducible: without it, exactly one error, `failed to
-- synthesize instance of type class Decidable ((hmsgNarrowItsrProblem blindPrimitives pkSeed
-- pkRoot).Wins queries qC)` inside `checkStrictness`.
@[expose, reducible] def blindPrimitives : Primitives toyParams :=
  { toyPrimitives with Hmsg := fun r _ _ msg => toyPrimitives.Hmsg r pkSeed pkRoot msg }

instance : SampleableType blindPrimitives.Y := inferInstanceAs (SampleableType (Bytes 1))

instance : DecidableEq blindPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 1))

instance : DecidableEq blindPrimitives.PkSeed := inferInstanceAs (DecidableEq (Bytes 1))

/-! ## The canaries -/

/-- The bundle's own liveness, and the fixture's coverage pattern.

The first six properties are the two message-derived maps: each of `H_msg`'s four FIPS inputs is
moved on its own and the digest is required to move with it, and `PRF_msg` is moved in each of its
two.  The rest fix the shape the coverage canaries rely on: the forged digest names two indices,
they are the hand-written pair, four queries realise all four coverage patterns against them, a
fifth covers both without reproducing the digest, and two of the six pairs share a randomizer. -/
def checkFixture : IO Unit := do
  ensure "H_msg moves with the randomizer"
    (toyPrimitives.Hmsg (node 0x01) pkSeed pkRoot msgC !=
      toyPrimitives.Hmsg (node 0x02) pkSeed pkRoot msgC)
  ensure "H_msg moves with the message" (digestOf qC.1 msgC != digestOf qC.1 [0x21])
  ensure "H_msg moves with the public seed"
    (toyPrimitives.Hmsg qC.1 pkSeed pkRoot msgC != toyPrimitives.Hmsg qC.1 otherPkSeed pkRoot msgC)
  ensure "H_msg moves with the published root"
    (toyPrimitives.Hmsg qC.1 pkSeed pkRoot msgC != toyPrimitives.Hmsg qC.1 pkSeed otherPkRoot msgC)
  ensure "PRF_msg moves with addrnd" (rOf 0x11 msgC != rOf 0x22 msgC)
  ensure "PRF_msg moves with the message" (rOf 0x11 msgC != rOf 0x11 [0x21])
  ensure "the forged digest is the hand-written one"
    (digestC.toList == [0xBB, 0x27, 0xAB] && partsC.md.toList == [0xBB] &&
      partsC.idxTree.val == 3 && partsC.idxLeaf.val == 3)
  ensure "the forged digest selects the two hand-written indices"
    (hmsgIndices toyParams digestC == forgedIndexTable)
  ensure "one query reproduces the forged digest under a different pair"
    (digestOf qBoth.1 qBoth.2 == digestC && qBoth != qC && qBoth.1 != qC.1 && qBoth.2 != qC.2)
  ensure "the two one-sided queries sit at the forged FORS instance"
    (((splitDigest toyParams (digestOf qFirst.1 qFirst.2)).forsAdrs == partsC.forsAdrs) &&
      ((splitDigest toyParams (digestOf qSecond.1 qSecond.2)).forsAdrs == partsC.forsAdrs))
  ensure "the unrelated query sits at a different FORS instance"
    ((splitDigest toyParams (digestOf qOther.1 qOther.2)).forsAdrs != partsC.forsAdrs)
  ensure "the four target sets realise the four coverage patterns"
    (coversPattern [qBoth] == (true, true) && coversPattern [qFirst] == (true, false) &&
      coversPattern [qSecond] == (false, true) && coversPattern [qOther] == (false, false))
  ensure "a fifth query covers both indices without reproducing the digest"
    (coversPattern [qHonestOnly] == (true, true) &&
      digestOf qHonestOnly.1 qHonestOnly.2 != digestC)
  ensure "the six queries are pairwise distinct"
    ([qC, qBoth, qFirst, qSecond, qOther, qHonestOnly].Pairwise (· != ·))
  ensure "two of them share a randomizer and differ only in their message"
    (qSecond.1 == qOther.1 && qSecond.2 != qOther.2)
  ensure "and the winning query shares neither with the forged pair"
    (qBoth.1 != qC.1 && qBoth.2 != qC.2)
  ensure "there are sixty-four semantic indices and they are distinct"
    (allIndices.length == 64 && allIndices.Nodup)

/-- The two coordinate maps, against tables written out by hand.

`HmsgIndex.forsAdrs` is required to agree with the digest's own `DigestParts.forsAdrs` *and* with
a hand-written `Adrs` record; `HmsgIndex.globalLeaf` is required to agree with `forsSigLeafIndex`
*and* with a hand-written `tree · 2 ^ a + leaf`; and the FORS leaf address the pair produces is
required to agree with a hand-written table of four `Adrs` records.  The last is what a shift
applied to `globalLeaf` and to its bridge together has to survive, and does not. -/
def checkCoordinates : IO Unit := do
  ensure "the forged instance address is the hand-written one"
    (partsC.forsAdrs == forgedForsAdrsTable)
  for idx in hmsgIndices toyParams digestC do
    ensure "the index's instance address is the digest's"
      (idx.forsAdrs == partsC.forsAdrs && idx.forsAdrs == forgedForsAdrsTable)
    ensure "the index's global leaf is forsSigLeafIndex at its tree"
      (idx.globalLeaf == forsSigLeafIndex toyParams partsC.md.toList idx.tree.val)
    ensure "the index's global leaf is the hand-written tree offset plus leaf"
      (idx.globalLeaf == idx.tree.val * 2 ^ toyParams.a + idx.leaf.val)
    ensure "the index's FORS leaf address is the hand-written one"
      (forsNodeAdrs idx.forsAdrs 0 idx.globalLeaf == forgedLeafAdrsTable idx.globalLeaf)
    ensure "dividing the tree height out of the global leaf gives the target back"
      (idx.globalLeaf / 2 ^ toyParams.a == (uncoveredTarget idx).val &&
        (uncoveredTarget idx) == idx.tree)
  ensure "the four global leaves of the instance carry four distinct hand-written addresses"
    (((List.range 4).map forgedLeafAdrsTable).Nodup &&
      ((List.range 4).all fun j => forsNodeAdrs partsC.forsAdrs 0 j == forgedLeafAdrsTable j))
  ensure "every global leaf stays inside the instance"
    (allIndices.all fun idx => decide (idx.globalLeaf < toyParams.k * 2 ^ toyParams.a))

/-- `HmsgIndex.ext_of_coords`, and the two naive identifications it rules out.

The pair `(instance address, global leaf)` is required to be injective over all sixty-four indices;
each half on its own is required *not* to be, so neither hypothesis of the lemma is idle; and the
pair `(instance address, local leaf)` — the global leaf with the tree offset dropped — is required
not to be injective either, which is what makes `k = 2` load-bearing. -/
def checkExtOfCoords : IO Unit := do
  ensure "address and global leaf together determine the index"
    ((allIndices.map fun idx => (idx.forsAdrs, idx.globalLeaf)).Nodup)
  ensure "the address alone does not"
    (!(allIndices.map fun idx => idx.forsAdrs).Nodup)
  ensure "the global leaf alone does not"
    (!(allIndices.map fun idx => idx.globalLeaf).Nodup)
  ensure "and neither does the address with the tree offset dropped"
    (!(allIndices.map fun idx => (idx.forsAdrs, idx.leaf.val)).Nodup)

/-- The widening, at the fixture's own values.

Membership transports in both directions; a candidate whose seed or root is not the embedding's is
absent from the embedded transcript *whatever* its randomizer and message, which is the free
freshness the module docstring warns about; and the embedded transcript's index set is the query
list's. -/
def checkEmbedding : IO Unit := do
  ensure "an embedded query is in the embedded transcript"
    ([qC, qBoth, qFirst, qSecond, qOther].all fun q =>
      decide ((q.1, (⟨pkSeed, pkRoot, q.2⟩ : HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) ∈
        embed [qC, qBoth, qFirst, qSecond, qOther]))
  ensure "a pair the query list omits is absent from the embedded transcript"
    (decide (candidateC ∉ embed [qBoth, qFirst, qSecond, qOther]))
  ensure "the embedded transcript has one entry per query"
    ((embed [qBoth, qFirst, qSecond, qOther]).length == 4)
  ensure "a candidate at another public seed is absent for free"
    (decide (candidateOffSeed ∉ embed [qC, qBoth, qFirst, qSecond, qOther]))
  ensure "a candidate at another published root is absent for free"
    (decide (candidateOffRoot ∉ embed [qC, qBoth, qFirst, qSecond, qOther]))
  ensure "and its underlying pair is nevertheless one of the queries"
    (decide (qC ∈ [qC, qBoth, qFirst, qSecond, qOther]))
  ensure "the embedded transcript selects what the query list selects"
    ((hmsgItsrProblem toyPrimitives).targetIndexSet (embed [qFirst, qSecond]) ==
      (hmsgNarrowItsrProblem toyPrimitives pkSeed pkRoot).targetIndexSet [qFirst, qSecond])
  ensure "membership in the embedded index set is membership in some query's digest"
    (forgedIndexTable.all fun idx =>
      decide (idx ∈ (hmsgItsrProblem toyPrimitives).targetIndexSet (embed [qBoth])) ==
        decide (∃ q ∈ [qBoth], idx ∈ hmsgIndices toyParams (digestOf q.1 q.2)))

/-- The two conjuncts of the winning condition, each falsified on its own, and one candidate that
wins.

Freshness fails and coverage holds: the candidate is one of the targets.  Coverage fails and
freshness holds: the candidate is fresh against a transcript at another FORS instance.  Both hold:
one query reproduces the forged digest under a different pair.  The off-fibre candidates fail on
coverage while holding on freshness, which is the widening's extra room made falsifiable. -/
def checkWins : IO Unit := do
  ensure "the candidate wins against a transcript that covers both of its indices"
    (wideWins [qBoth] candidateC)
  ensure "freshness fails when the candidate is one of the targets"
    (!wideWins [qC, qBoth] candidateC &&
      decide (candidateC ∈ embed [qC, qBoth]) &&
      (forgedIndexTable.all fun idx =>
        decide (idx ∈ (hmsgItsrProblem toyPrimitives).targetIndexSet (embed [qC, qBoth]))))
  ensure "coverage fails against a transcript at another instance, and freshness holds"
    (!wideWins [qOther] candidateC && decide (candidateC ∉ embed [qOther]))
  ensure "coverage fails when only one of the two indices is covered"
    (!wideWins [qFirst] candidateC && !wideWins [qSecond] candidateC)
  ensure "an off-fibre candidate is fresh and still does not win"
    (decide (candidateOffSeed ∉ embed [qC, qBoth]) && !wideWins [qC, qBoth] candidateOffSeed &&
      decide (candidateOffRoot ∉ embed [qC, qBoth]) && !wideWins [qC, qBoth] candidateOffRoot)

/-- The fibre equivalence, evaluated in both directions at every fixture transcript.

At the honest key pair the widened winning condition and the source-shaped one agree on all seven
of the fixture's target lists: two on which the forged pair wins, one on which freshness fails, and
four on which coverage fails.  Neither direction is vacuous: both values occur.  The last check is
what pins the key pair the source-shaped side is read at. -/
def checkFibreEquivalence : IO Unit := do
  let cases := [[qBoth], [qHonestOnly], [qC, qBoth], [qOther], [qFirst], [qSecond], []]
  for queries in cases do
    ensure "the widened and source-shaped winning conditions agree at the honest key pair"
      (wideWins queries candidateC == narrowWins queries qC)
  ensure "and both values occur among those cases"
    ((cases.any fun queries => wideWins queries candidateC) &&
      (cases.any fun queries => !wideWins queries candidateC))
  ensure "the source-shaped side is read at the honest key pair and nowhere else"
    (wideWins [qHonestOnly] candidateC &&
      !narrowWinsAt otherPkSeed pkRoot [qHonestOnly] qC &&
      !narrowWinsAt pkSeed otherPkRoot [qHonestOnly] qC)

/-- Which uncovered index comes back, and that it is the first.

Four target sets: one covering only the candidate's second index, so the first is returned; one
covering only its first, so the second is returned; one covering neither, where a last-match
extractor would return the second and this one returns the first; and one covering both, where
nothing is returned and the pair wins.  The third is the case soundness alone does not decide.  Two
sweeps over the same four then require whatever comes back to be uncovered, to be an index the
candidate selects, and to name its own FORS tree. -/
def checkFindUncovered : IO Unit := do
  ensure "with only the second index covered, the first comes back"
    (findUncoveredIndex toyPrimitives (embed [qSecond]) candidateC == some forgedIndex0)
  ensure "with only the first index covered, the second comes back"
    (findUncoveredIndex toyPrimitives (embed [qFirst]) candidateC == some forgedIndex1)
  ensure "with neither covered, the first comes back and not the last"
    (findUncoveredIndex toyPrimitives (embed [qOther]) candidateC == some forgedIndex0 &&
      findUncoveredIndex toyPrimitives (embed [qOther]) candidateC != some forgedIndex1 &&
      findUncoveredIndex toyPrimitives (embed []) candidateC == some forgedIndex0)
  ensure "with both covered, nothing comes back and the pair wins"
    (findUncoveredIndex toyPrimitives (embed [qBoth]) candidateC == none &&
      wideWins [qBoth] candidateC)
  ensure "the returned index is uncovered and is one the candidate selects"
    ([[qSecond], [qFirst], [qOther], []].all fun queries =>
      match findUncoveredIndex toyPrimitives (embed queries) candidateC with
      | none => true
      | some idx =>
          decide (idx ∈ (hmsgItsrProblem toyPrimitives).indexSet candidateC) &&
            decide (idx ∉ (hmsgItsrProblem toyPrimitives).targetIndexSet (embed queries)))
  ensure "and the target it names is its own FORS tree"
    ([[qSecond], [qFirst], [qOther], []].all fun queries =>
      match findUncoveredIndex toyPrimitives (embed queries) candidateC with
      | none => true
      | some idx => uncoveredTarget idx == idx.tree)

/-- The strictness of the widening, exhibited.

`blindPrimitives` differs from the fixture's bundle in one field: its `H_msg` ignores the `PK.seed`
and `PK.root` it is handed and hashes at the fixture's own key pair instead.  Its source-shaped
problem at *any* key pair is therefore the fixture's bundle's at the honest one — the two are
asserted to agree on every randomizer and message the fixture uses, and their winning conditions on
four of its target lists — while its widened game falls to a single target query, which the
fixture's own bundle refuses.  That is the separation: source-shaped hardness does not carry to the
widened game.  The last two checks falsify the two hypotheses the win rests on, one each. -/
def checkStrictness : IO Unit := do
  ensure "the blind bundle agrees with the fixture's at the honest key pair"
    ([qC, qBoth, qFirst, qSecond, qOther].all fun q =>
      blindPrimitives.Hmsg q.1 pkSeed pkRoot q.2 == toyPrimitives.Hmsg q.1 pkSeed pkRoot q.2)
  ensure "so the two source-shaped games agree on the fixture's cases"
    ([[qBoth], [qC, qBoth], [qOther], []].all fun queries =>
      decide ((hmsgNarrowItsrProblem blindPrimitives pkSeed pkRoot).Wins queries qC) ==
        narrowWins queries qC)
  ensure "the blind bundle loses the widened game to one target query"
    (decide ((hmsgItsrProblem blindPrimitives).Wins [(qC.1, ⟨otherPkSeed, pkRoot, qC.2⟩)]
      (qC.1, ⟨pkSeed, pkRoot, qC.2⟩)))
  ensure "the fixture's own bundle does not"
    (!decide ((hmsgItsrProblem toyPrimitives).Wins [(qC.1, ⟨otherPkSeed, pkRoot, qC.2⟩)]
      (qC.1, ⟨pkSeed, pkRoot, qC.2⟩)))
  ensure "the win needs the two inputs to differ"
    (!decide ((hmsgItsrProblem blindPrimitives).Wins [(qC.1, ⟨pkSeed, pkRoot, qC.2⟩)]
      (qC.1, ⟨pkSeed, pkRoot, qC.2⟩)))
  ensure "and it needs the two digests to agree"
    (blindPrimitives.Hmsg qC.1 otherPkSeed pkRoot qC.2 == blindPrimitives.Hmsg qC.1 pkSeed pkRoot
        qC.2 &&
      toyPrimitives.Hmsg qC.1 otherPkSeed pkRoot qC.2 != toyPrimitives.Hmsg qC.1 pkSeed pkRoot qC.2)

/-- What honest signing reveals at the indices a digest selects.

For each index the forged digest selects, the secret value honest FORS signing puts in that index's
FORS tree is the one at that index's coordinate; moving the coordinate by one moves the value; and
the four coordinates of the instance carry four distinct secret values, so the coordinate is what
the value depends on. -/
def checkReveals : IO Unit := do
  let sig := forsSign toyPrimitives partsC.md.toList skSeed pkSeed partsC.forsAdrs
  for idx in hmsgIndices toyParams digestC do
    ensure "the revealed value is the one at the index's coordinate"
      (sig[idx.tree.val].sk ==
        forsSkGenCore toyPrimitives.core skSeed pkSeed idx.forsAdrs idx.globalLeaf)
    ensure "and not the one at the next coordinate"
      (sig[idx.tree.val].sk !=
        forsSkGenCore toyPrimitives.core skSeed pkSeed idx.forsAdrs (idx.globalLeaf + 1))
  ensure "the four coordinates of the instance carry four distinct secret values"
    (((List.range 4).map fun j =>
      forsSkGenCore toyPrimitives.core skSeed pkSeed partsC.forsAdrs j).Nodup)
  ensure "and the instance address is load-bearing in them"
    (forsSkGenCore toyPrimitives.core skSeed pkSeed partsC.forsAdrs 0 !=
      forsSkGenCore toyPrimitives.core skSeed pkSeed
        (splitDigest toyParams (digestOf qOther.1 qOther.2)).forsAdrs 0)

/-- The uncovered coordinate, and both ways a query can miss it.

Against a transcript covering the forged pair's first index only, the second is uncovered, and no
query and FORS tree land on its coordinate.  The two queries in that transcript miss it for
different reasons — one sits at the forged instance and misses on the leaf, the other sits at
another instance and misses on the address — so both halves of the conjunction the lemma denies are
exercised.  The other direction is asserted as well: for the index that *is* covered, some query
and tree do land on its coordinate, so the conjunction the lemma denies is satisfiable at this
fixture and its denial is not vacuous. -/
def checkUncoveredCoordinate : IO Unit := do
  let queries := [qFirst, qOther]
  let uncovered := forgedIndex1
  let covered := forgedIndex0
  ensure "the second index is uncovered against that transcript"
    (decide (uncovered ∉ (hmsgItsrProblem toyPrimitives).targetIndexSet (embed queries)) &&
      decide (covered ∈ (hmsgItsrProblem toyPrimitives).targetIndexSet (embed queries)))
  ensure "no query and tree land on the uncovered coordinate"
    (queries.all fun q =>
      (List.finRange toyParams.k).all fun i =>
        !((splitDigest toyParams (digestOf q.1 q.2)).forsAdrs == uncovered.forsAdrs &&
          forsSigLeafIndex toyParams (splitDigest toyParams (digestOf q.1 q.2)).md.toList i.val ==
            uncovered.globalLeaf))
  ensure "the first query misses on the leaf, at the same instance address"
    ((splitDigest toyParams (digestOf qFirst.1 qFirst.2)).forsAdrs == uncovered.forsAdrs &&
      (List.finRange toyParams.k).all fun i =>
        forsSigLeafIndex toyParams (splitDigest toyParams (digestOf qFirst.1 qFirst.2)).md.toList
          i.val != uncovered.globalLeaf)
  ensure "the second query misses on the address"
    ((splitDigest toyParams (digestOf qOther.1 qOther.2)).forsAdrs != uncovered.forsAdrs)
  ensure "and some query and tree do land on the covered coordinate"
    (queries.any fun q =>
      (List.finRange toyParams.k).any fun i =>
        (splitDigest toyParams (digestOf q.1 q.2)).forsAdrs == covered.forsAdrs &&
          forsSigLeafIndex toyParams (splitDigest toyParams (digestOf q.1 q.2)).md.toList i.val ==
            covered.globalLeaf)

/-! ## The library statements, pinned at this bundle

Every theorem the module exports appears below at the toy bundle's own types.  The arguments are
generic where the statement is, so what is pinned is the statement's shape and not a value; the
`checkFixture` sweep above is what pins the values. -/

section Pins

variable (pkS : toyPrimitives.PkSeed) (pkR : toyPrimitives.Y) (r : toyPrimitives.Y)
  (m : List Byte) (queries : ITSRTranscript toyPrimitives.Y (List Byte))
  (targets : ITSRTranscript toyPrimitives.Y (HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y))
  (candidate : toyPrimitives.Y × HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)
  (idx idx' : HmsgIndex toyParams) (digest : Bytes toyParams.m) (parts : DigestParts toyParams)
  (adrs : Adrs) (i : Fin toyParams.k)

example : idx.forsAdrs.layer = 0 := HmsgIndex.forsAdrs_layer idx

example : idx.forsAdrs.tree = idx.idxTree.val := HmsgIndex.forsAdrs_tree idx

example : idx.forsAdrs.type = AddrType.forsTree.toCode := HmsgIndex.forsAdrs_type idx

example : idx.forsAdrs.getKeyPairAddress = idx.idxLeaf.val := HmsgIndex.forsAdrs_keyPair idx

example (htree : idx.idxTree = parts.idxTree) (hleaf : idx.idxLeaf = parts.idxLeaf) :
    idx.forsAdrs = parts.forsAdrs := HmsgIndex.forsAdrs_eq_of_indices idx parts htree hleaf

example (h : idx ∈ hmsgIndices toyParams digest) :
    idx.forsAdrs = (splitDigest toyParams digest).forsAdrs := HmsgIndex.forsAdrs_of_mem h

example (h : idx ∈ hmsgIndices toy.params digest) :
    idx.forsAdrs = (BottomPosition.ofDigestParts toy (splitDigest toy.params digest)).forsAdrs :=
  HmsgIndex.forsAdrs_eq_bottom h

example : idx.globalLeaf = idx.tree.val * 2 ^ toyParams.a + idx.leaf.val :=
  HmsgIndex.globalLeaf_eq idx

example : idx.globalLeaf < toyParams.k * 2 ^ toyParams.a := HmsgIndex.globalLeaf_lt idx

example : idx.globalLeaf / 2 ^ toyParams.a = idx.tree.val := HmsgIndex.globalLeaf_div_pow_a idx

example (h : idx ∈ hmsgIndices toyParams digest) :
    idx.globalLeaf = forsSigLeafIndex toyParams (splitDigest toyParams digest).md.toList
      idx.tree.val := HmsgIndex.globalLeaf_of_mem h

example (hadrs : idx.forsAdrs = idx'.forsAdrs) (hleaf : idx.globalLeaf = idx'.globalLeaf) :
    idx = idx' := HmsgIndex.ext_of_coords hadrs hleaf

example : (hmsgNarrowItsrProblem toyPrimitives pkS pkR).khf.hash r m =
    toyPrimitives.Hmsg r pkS pkR m := hmsgNarrowItsrProblem_hash toyPrimitives pkS pkR r m

example : (hmsgNarrowItsrProblem toyPrimitives pkS pkR).khf.keygen = $ᵗ toyPrimitives.Y :=
  hmsgNarrowItsrProblem_keygen toyPrimitives pkS pkR

example : (hmsgNarrowItsrProblem toyPrimitives pkS pkR).indices digest =
    hmsgIndices toyParams digest := hmsgNarrowItsrProblem_indices toyPrimitives pkS pkR digest

example : embedTargets toyPrimitives pkS pkR queries =
    queries.map (fun q => (q.1, ⟨pkS, pkR, q.2⟩)) := embedTargets_eq toyPrimitives pkS pkR queries

example : (r, (⟨pkS, pkR, m⟩ : HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) ∈
    embedTargets toyPrimitives pkS pkR queries ↔ (r, m) ∈ queries :=
  mem_embedTargets_iff pkS pkR queries r m

example (h : (r, m) ∉ queries) :
    (r, (⟨pkS, pkR, m⟩ : HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) ∉
      embedTargets toyPrimitives pkS pkR queries := notMem_embedTargets_of_notMem pkS pkR h

example (input : HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)
    (h : input.pkSeed ≠ pkS ∨ input.pkRoot ≠ pkR) :
    (r, input) ∉ embedTargets toyPrimitives pkS pkR queries :=
  notMem_embedTargets_of_ne pkS pkR queries r input h

example : (hmsgItsrProblem toyPrimitives).indexSet
      (r, (⟨pkS, pkR, m⟩ : HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) =
    (hmsgNarrowItsrProblem toyPrimitives pkS pkR).indexSet (r, m) := indexSet_embed pkS pkR r m

example : (hmsgItsrProblem toyPrimitives).targetIndexSet
      (embedTargets toyPrimitives pkS pkR queries) =
    (hmsgNarrowItsrProblem toyPrimitives pkS pkR).targetIndexSet queries :=
  targetIndexSet_embedTargets pkS pkR queries

example : idx ∈ (hmsgItsrProblem toyPrimitives).targetIndexSet
      (embedTargets toyPrimitives pkS pkR queries) ↔
    ∃ q ∈ queries, idx ∈ hmsgIndices toyParams (toyPrimitives.Hmsg q.1 pkS pkR q.2) :=
  mem_targetIndexSet_embedTargets_iff pkS pkR queries idx

example : (hmsgItsrProblem toyPrimitives).Wins (embedTargets toyPrimitives pkS pkR queries)
      (r, ⟨pkS, pkR, m⟩) ↔
    (hmsgNarrowItsrProblem toyPrimitives pkS pkR).Wins queries (r, m) :=
  wins_embedTargets_iff pkS pkR queries r m

example (input input' : HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y) (hne : input ≠ input')
    (hdigest : toyPrimitives.Hmsg r input.pkSeed input.pkRoot input.request =
      toyPrimitives.Hmsg r input'.pkSeed input'.pkRoot input'.request) :
    (hmsgItsrProblem toyPrimitives).Wins [(r, input')] (r, input) :=
  wins_of_hmsg_agree r input input' hne hdigest

example : findUncoveredIndex toyPrimitives targets candidate =
    ((hmsgItsrProblem toyPrimitives).indexSet candidate).find?
      (fun i => decide (i ∉ (hmsgItsrProblem toyPrimitives).targetIndexSet targets)) :=
  findUncoveredIndex_eq_find? toyPrimitives targets candidate

example : findUncoveredIndex toyPrimitives targets candidate = some idx ↔
    idx ∉ (hmsgItsrProblem toyPrimitives).targetIndexSet targets ∧
      ∃ before after, (hmsgItsrProblem toyPrimitives).indexSet candidate = before ++ idx :: after ∧
        ∀ j ∈ before, j ∈ (hmsgItsrProblem toyPrimitives).targetIndexSet targets :=
  findUncoveredIndex_eq_some_iff targets candidate idx

example (h : findUncoveredIndex toyPrimitives targets candidate = some idx) :
    idx ∈ (hmsgItsrProblem toyPrimitives).indexSet candidate :=
  mem_indexSet_of_findUncoveredIndex h

example (h : findUncoveredIndex toyPrimitives targets candidate = some idx) :
    idx ∉ (hmsgItsrProblem toyPrimitives).targetIndexSet targets :=
  notMem_targetIndexSet_of_findUncoveredIndex h

example (hfresh : candidate ∉ targets)
    (h : findUncoveredIndex toyPrimitives targets candidate = none) :
    (hmsgItsrProblem toyPrimitives).Wins targets candidate :=
  wins_of_findUncoveredIndex_eq_none hfresh h

example (hfresh : candidate ∉ targets) :
    (hmsgItsrProblem toyPrimitives).Wins targets candidate ∨
      ∃ j, findUncoveredIndex toyPrimitives targets candidate = some j ∧
        j ∈ (hmsgItsrProblem toyPrimitives).indexSet candidate ∧
        j ∉ (hmsgItsrProblem toyPrimitives).targetIndexSet targets :=
  itsr_wins_or_uncovered targets candidate hfresh

example : uncoveredTarget idx = idx.tree := uncoveredTarget_eq idx

example : idx.globalLeaf / 2 ^ toyParams.a = (uncoveredTarget idx).val :=
  uncoveredTarget_globalLeaf idx

example (sk : toyPrimitives.SkSeed) :
    ((forsSign toyPrimitives m sk pkS adrs)[i.val]).sk =
      forsSkGenCore toyPrimitives.core sk pkS adrs (forsSigLeafIndex toyParams m i.val) :=
  forsSign_getElem_sk toyPrimitives m sk pkS adrs i

example (sk : toyPrimitives.SkSeed) (h : idx ∈ hmsgIndices toyParams digest) :
    ((forsSign toyPrimitives (splitDigest toyParams digest).md.toList sk pkS
        (splitDigest toyParams digest).forsAdrs)[idx.tree.val]).sk =
      forsSkGenCore toyPrimitives.core sk pkS idx.forsAdrs idx.globalLeaf :=
  forsSign_reveals_of_mem_hmsgIndices toyPrimitives sk pkS h

example (huncov : idx ∉ (hmsgItsrProblem toyPrimitives).targetIndexSet
      (embedTargets toyPrimitives pkS pkR queries))
    (q : toyPrimitives.Y × List Byte) (hq : q ∈ queries) :
    ¬ ((splitDigest toyParams (toyPrimitives.Hmsg q.1 pkS pkR q.2)).forsAdrs = idx.forsAdrs ∧
        forsSigLeafIndex toyParams
          (splitDigest toyParams (toyPrimitives.Hmsg q.1 pkS pkR q.2)).md.toList i.val =
            idx.globalLeaf) :=
  coord_unrevealed_of_notMem pkS pkR huncov hq i

end Pins

def main : IO Unit := do
  checkFixture
  checkCoordinates
  checkExtOfCoords
  checkEmbedding
  checkWins
  checkFibreEquivalence
  checkFindUncovered
  checkStrictness
  checkReveals
  checkUncoveredCoordinate
  IO.println "SLH-DSA H_msg ITSR bridge tests: PASS"

end SLHDSA.HmsgWitnessesTest

def main : IO Unit := SLHDSA.HmsgWitnessesTest.main
