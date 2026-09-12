/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.SufResidual

/-!
# SLH-DSA deterministic strong-unforgeability residual canaries

Executable checks that the reading of a signing log in `HashSig.SLHDSA.Security.SufResidual` is the
one the library's two log predicates give, that it is per-message and not per-log, and that the
residual's two branches are different events with different consequences at the `H_msg` target
transcript — all evaluated at values, not restated from the theorems.

## The profile is the scheme-dispatch fixture's, and why it is copied rather than imported

The block below is the one `HashSigTest.SLHDSA.SchemeWitnesses` builds and
`HashSigTest.SLHDSA.HmsgWitnesses` copies — the same seven parameters, the same six byte maps, the
same three honest seeds, the same published root — so the three executables run on one profile, and
a reviewer can check that by diffing the blocks.  It is copied rather than imported because a
`lean_exe` root must own its `main`, and a module that imports another fixture cannot declare one:
the attempt reports `` `main` has already been declared``, and had it not, this executable would
have linked the imported `main` and run the other fixture.  The lane has no shared fixture module,
and adding one would edit merged, reviewed files from inside this pull request.

Diffed against the `H_msg` bridge fixture's copy of the block, from its section heading to `pkRoot`,
there are four hunks.  Three attribute comments carry this file's own measured error counts and
error text — every attribute comment here was written by removing the attribute and reading what
Lean said.  There are four measured figures across those three comments, because the third carries
one for each of its two attributes: 45, 61, a hundred errors plus the line saying the ceiling was
reached, and 15.  Three of the four have a counterpart standing in the same place in that file — 45
against its 41, the hundred-plus-ceiling against its 51, 15 against its 3 — and none of the three
coincides; `toy`'s 61 has no counterpart at all, because that file leaves `toy` unexposed.  The
error text differs as well, because these comments quote the error rather than paraphrasing it.  Two
docstrings in the copied block name the group in *this* file that asserts what they describe.  `toy`
carries `@[expose]` here, where that file leaves it unexposed, because the three `DecidableEq`
instances below are stated at `toy.params`.  And `otherPkSeed`, which exists there to move a
candidate off the honest key pair, is dropped: every statement in the library module reads its
public seed and published root off one `pk`, so there is no second key pair to move to, and testing
that there is would be re-testing the `H_msg` bridge.

## What this fixture adds

A signing log, which no earlier fixture in the lane has needed.  Three entries on two messages, with
the twice-signed message's two entries separated by the other message's, so that a reading of
`loggedSignatures` that stopped at the first match, took only the last, or ignored the message would
show up.  Alongside it, the log FIPS 205 §9.2's deterministic variant would produce for the same
three queries, which is the shape the EasyCrypt development's message-keyed signer has.

A third log, longer than either, whose only purpose is to be longer: it signs one message three
times and repeats one of those entries.  Both other logs stop at two signatures per message and at
three entries, so a reading that reordered or collapsed a list only once it grew past those sizes
would be invisible to every check written against them.  Six checks read this log.  Four are
hand-written values, one for each list this file reads a log into: the signatures at a message,
their randomizers, the pair transcript, and that transcript embedded at the honest key pair.  Each
of the four differs from its own reverse *and* carries a repeat, so each refuses reordering,
collapsing and truncation together, up to the longest list its own reader produces anywhere here —
three entries for the first two, four for the other two.  The other two read the log through the two
`Bool` predicates, at the one message it queries that its first entry does not and at the one pair
it holds only in its last entry; between them they refuse every truncation of either predicate that
a fourth entry makes visible, and `checkPredicates` records which truncations no log here makes
visible at all.  No list this file reads a log into is longer than four, so a reading that waited
for a fourth signature at one message, or for a fifth entry in a transcript, would need a longer log
again.

Four forgeries, and three `DecidableEq` instances.  The instances are the fixture's own: the library
module carries `DecidableEq` on the signature type as a hypothesis because no such instance exists
on this branch, and these build it field by field at this bundle and nowhere else.

Two pins name their validated parameters explicitly, as `(vp := toy)`, and what that argument is for
was read off the errors its removal produces.  Dropping it from both gives two errors, both
`Type mismatch`, no synthesis failure at all, and a metavariable standing where `pk` should be.
Naming the bundle in its place gives a different report — four errors, two
`failed to synthesize instance of type class` for
`SampleableType (Primitives.toCorePrimitives ?m).Y`, with a metavariable where the bundle should be,
and two application type mismatches on the membership hypothesis — because a bundle at `toyParams`
does not say which `vp` has `vp.params = toyParams`.  Naming the bundle as well changes nothing:
with `(prims := toyPrimitives)` alongside, and without it, the file elaborates with no output.  The
reason is not the `[SampleableType prims.Y]` binder these two theorems carry, because
`findUncoveredIndex_eq_none_of_mem_loggedRandomizers` carries it too and is pinned below with no
named argument; and on copies of that statement, giving it either or both of the two `DecidableEq`
binders the other two carry leaves it needing nothing still.  What the two that do need it have in
common is a conclusion stated through `hmsgItsrProblem`'s `Wins`: a copy carrying all three binders
whose conclusion is about `findUncoveredIndex` needs no named argument, negated or not, and one
whose conclusion is about `Wins` needs it, negated or not.  The other twenty pins need nothing.

## Which conjunct, and which combination, each canary falsifies

The library's two log predicates have four combinations and `checkPredicates` exhibits all four.
Three are realised by fixture data: an unqueried message with a fresh pair, a queried message with a
fresh pair, and a replayed pair.  The fourth — an unqueried message whose exact pair is nevertheless
in the log — is asserted unreachable over every entry of the log rather than omitted, because that
is what makes the queried/unqueried split exhaustive inside the success event.

`sameMessage_condition_iff`'s right-hand side is a conjunction of two, and each is falsified alone:
at the unqueried message the first fails while the second holds, at a replayed pair the second fails
while the first holds, and at the residual both hold.

`ITSRProblem.Wins` has two conjuncts.  On the branch where the forged randomizer was logged at the
message, freshness fails — and coverage is asserted *separately* still to hold, because "the winning
condition fails" would otherwise not say which conjunct failed, and the point of that branch is that
it is freshness and only freshness.

`components_ne_of_ne_of_randomizer_eq` concludes a disjunction of two, and each disjunct is realised
by a different forgery: one perturbs the FORS half and leaves the hypertree half alone, the other
the reverse, and both are asserted in both directions.

## The naive identifications this fixture is built to reject

* *That the signatures a log returned for a message can be read off the log without the message.*
  Rejected by the cross forgery, whose randomizer the log does record — at the other message — and
  which is asserted to leave both the pair and the embedded candidate fresh.  A `loggedRandomizers`
  that swept the whole log would put it on the other branch, and every soundness statement in the
  module would still hold, weakened.
* *That one entry per message is enough.*  Rejected by asserting that both signatures at the
  twice-signed message are listed, and that the list is exactly the hand-written pair in query
  order.  A first-match or last-match reading satisfies every one-way statement in the module.
* *That the residual needs the message to have been queried before pair freshness can fail.*
  Rejected the other way round: the fresh-randomizer forgery sits at a queried message and is
  nevertheless fresh at the transcript, which is why the module's dichotomy takes the
  strong-unforgeability condition alone and not the queried/unqueried split.
* *That the second branch is merely not proved.*  Rejected by asserting that the candidate is one of
  the recorded targets, that the winning condition fails, that coverage nevertheless holds, and that
  the first-uncovered-index extractor returns `none` — while for the fresh forgery it returns an
  index.
* *That the digest agreement on the second branch is an artefact of the toy `H_msg`.*  Rejected by
  asserting that the two forgeries which keep the first logged signature's randomizer split to its
  digest and open its two FORS leaves, and that the two which carry a different randomizer do
  neither.

## The pins

Every one of the twenty-two theorems the library module exports appears as an `example` at this
bundle's types, with generic arguments where the statement has them.  Seven further `example`s are
the profile's own `decide` pins, inherited with the copied block.
-/

public section

namespace SLHDSA.SufResidualTest

open Security Security.CanonicalGames KeyedHash OracleSpec

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"SUF residual check failed: {label}")

/-! ## The toy profile

Two hypertree layers of height two, two FORS trees of height one, `w = 16`, `len = 4`. -/

-- Exposed, and what that attribute is for was read off the errors its removal produces in this
-- file.  Without `@[expose]` on `toyParams`, 43 errors, the first inside the bundle at
-- `yToBytes := id`: `Type mismatch: id has type ?m → ?m but is expected to have type
-- `Bytes 1 → Bytes toyParams.n`.  The secret map, the tweak map, the randomizer and the digest map
-- need no exposure of their own here.  Nothing outside this executable consumes any of them.
/-- Two layers of height two, two FORS trees of height one. -/
@[expose] def toyParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 4 }

theorem toyValid : toyParams.Valid := by decide

-- Exposed here, where the `H_msg` bridge fixture leaves it unexposed, because this file states
-- three `DecidableEq` instances whose types are written at `toy.params`: without the attribute,
-- 58 errors, the first at the `ForsTreeSigCore` instance below, `Application type mismatch: the
-- argument toyPrimitives.core has type CorePrimitives toyParams but is expected to have type
-- CorePrimitives toy.params`.
/-- The validated form of `toyParams`. -/
@[expose] def toy : ValidatedParams := ⟨toyParams, toyValid⟩

example : toyParams.w = 16 := by decide
example : toyParams.len = 4 := by decide
example : toyParams.m = 3 := by decide
example : toyParams.digestBytes = 1 := by decide
example : toyParams.treeIdxBytes = 1 := by decide
example : toyParams.leafIdxBytes = 1 := by decide
example : toyParams.t = 2 := by decide

/-- The exclusive-or fold through which the toy `H_msg` and `PRF_msg` read a message.  Two messages
with equal folds therefore share a digest at a fixed key pair and a fixed randomizer; the three
messages this file uses have pairwise different folds, and `checkFixture` asserts it for the two
that are signed. -/
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
`checkFixture` asserts that. -/
def toyRandomizer (skPrf addrnd : UInt8) (msg : List Byte) : UInt8 :=
  mixByte (UInt8.ofNat
    ((skPrf.toNat * 13 + addrnd.toNat * 47 + (byteFold msg).toNat * 5 + 1) % 256))

/-- Byte `i` of the toy `H_msg` digest.  All four FIPS inputs enter every byte — the randomizer, the
public seed, the published root and the message fold — so the FORS message and both hypertree
indices move when any of them moves.  The one this file needs is the randomizer:
`checkSameRandomizer` asserts that a forgery carrying a new randomizer splits to a different digest
and one carrying a logged randomizer to the same digest, which is what makes the residual's two
branches different events. -/
def toyDigestByte (r seed root : UInt8) (msg : List Byte) (i : ℕ) : UInt8 :=
  mixByte (UInt8.ofNat ((r.toNat * (6 * i + 37) + seed.toNat * (10 * i + 53) +
    root.toNat * (14 * i + 89) + (byteFold msg).toNat * (22 * i + 149) + (30 * i + 7)) % 256))

-- Exposed and `@[reducible]`, for two different reasons, each read off the errors that removing
-- that attribute alone produces in this file.  Exposed, for code generation: without it the build
-- runs into Lean's hundred-error ceiling — 100 errors and the line saying the ceiling was reached,
-- so the count is a floor and not a total.  The first is at `instance : DecidableEq
-- toyPrimitives.Y` just below: `Compilation failed, locally inferred compilation type differs from
-- type that would be inferred in other modules`, naming `toyPrimitives ↦ 2`, with the rest after it
-- down the compiled declarations.  Reducible, because its carrier types have to unfold to `Bytes 1`
-- for instance resolution to reach them: without it, 13 errors and only these — two at `byteOf`,
-- whose `y[0]` finds no `GetElem toyPrimitives.Y ℕ` instance and then cannot prove its index valid;
-- two `BEq (ITSRTranscript toyPrimitives.Y (HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y))`,
-- one for each embedded-transcript value pin in `checkBranches`; four `Decidable (… ∈
-- embeddedTargets)` membership goals in the same group; three `DecidableEq (HmsgITSRInput
-- toyPrimitives.PkSeed toyPrimitives.Y)`, one in `checkBranches` and two in the pins; and two
-- `DecidableEq toyPrimitives.PkSeed`, both in the pins.  Nothing outside this executable
-- consumes it.
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

/-- The published hypertree root. -/
def pkRoot : toyPrimitives.Y := GeneralHypertree.root toy toyPrimitives skSeed pkSeed


/-- The honest public key. -/
def honestPk : PublicKeyCore toyPrimitives.core := ⟨pkSeed, pkRoot⟩

/-- The honest secret key. -/
def secretKey : SecretKeyCore toyPrimitives.core := ⟨skSeed, skPrf, pkSeed, pkRoot⟩

/-! ## Deciding signature equality

`SignatureAlg.signingLogContains` and `QueryLog.wasQueried` are `Bool`-valued, so the whole library
module runs on a `DecidableEq` for the signature type, which it carries as a hypothesis because none
exists: neither `SLHDSA.SignatureCore` nor `ForsTreeSigCore` nor `XmssSigCore` derives one, and
`HashSig` declares none.  These three build it at this bundle, field by field, and nowhere else. -/

instance : DecidableEq (ForsTreeSigCore toy.params toyPrimitives.core) := fun a b =>
  decidable_of_iff (a.sk = b.sk ∧ a.auth = b.auth)
    ⟨fun h => by cases a; cases b; simp only at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl,
     fun h => h ▸ ⟨rfl, rfl⟩⟩

instance : DecidableEq (XmssSigCore toy.params toyPrimitives.core) := fun a b =>
  decidable_of_iff (a.wots = b.wots ∧ a.auth = b.auth)
    ⟨fun h => by cases a; cases b; simp only at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl,
     fun h => h ▸ ⟨rfl, rfl⟩⟩

instance : DecidableEq (GeneralScheme.SignatureCore toy toyPrimitives.core) := fun a b =>
  decidable_of_iff (a.randomness = b.randomness ∧ a.fors = b.fors ∧ a.hypertree = b.hypertree)
    ⟨fun h => by
      cases a; cases b; simp only at h
      obtain ⟨h1, h2, h3⟩ := h; subst h1; subst h2; subst h3; rfl,
     fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩

/-! ## The signing log

Three signing queries on two messages, and a third message that is never signed.  The two queries
on `msgP` use different per-signature randomness, which is what FIPS 205 Algorithm 19's hedged
default does and what makes the residual's second branch reachable at all; `checkFixture` asserts
that the two signatures they produce differ, and differ in their randomizers. -/

/-- The message signed twice. -/
def msgP : List Byte := [0x01, 0x02]

/-- A second signed message. -/
def msgQ : List Byte := [0x05]

/-- A message the log never carries. -/
def msgU : List Byte := [0x07, 0x09]

/-- The first honest signature on `msgP`, under one `addrnd`. -/
def sigP1 : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives msgP secretKey (node 0x41)

/-- The second honest signature on `msgP`, under a different `addrnd`. -/
def sigP2 : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives msgP secretKey (node 0x42)

/-- The honest signature on `msgQ`. -/
def sigQ : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives msgQ secretKey (node 0x43)

/-- The signing log.  The `msgQ` entry sits between the two `msgP` entries, so a reading of
`loggedSignatures` that stopped at the first match, or that ignored the message, would show up. -/
def signingLog : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  [⟨msgP, sigP1⟩, ⟨msgQ, sigQ⟩, ⟨msgP, sigP2⟩]

/-- FIPS 205 §9.2's deterministic variant on `msgP`: `opt_rand` is `PK.seed` rather than a fresh
`addrnd`, so signing `msgP` twice is the same call. -/
def detSigP : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives msgP secretKey pkSeed

/-- The same variant on `msgQ`. -/
def detSigQ : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives msgQ secretKey pkSeed

/-- The log FIPS 205's deterministic variant would produce for the same three queries: `opt_rand` is
`PK.seed` at every signing, so the two queries on `msgP` are the same call and return the same
signature.  This is the shape the EasyCrypt development's message-keyed signer has. -/
def deterministicLog :
    QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  [⟨msgP, detSigP⟩, ⟨msgQ, detSigQ⟩, ⟨msgP, detSigP⟩]

/-- A longer log, and the only one that signs one message three times.  Its `msgP` entries are the
deterministic signature twice and then a hedged one, so each of the four lists this file reads a log
into differs from its own reverse and carries a repeat here: `loggedSignatures` and
`loggedRandomizers` at that message are three long, `logQueries` and its embedding at the honest key
pair are four-entry transcripts.  No list either log above produces has both properties: those two
stop at two signatures per message and at three entries, their repeats are all palindromic, and
`signingLog`'s three pairs are pairwise distinct.  All four lists are pinned by value on this log —
the first two in `checkLoggedSignatures` and `checkRandomizers`, the transcript in
`checkRandomizers`, its embedding in `checkBranches` — and the two `Bool` predicates are read on it
in `checkPredicates`, which is the only place either of them sees a log of four entries. -/
def thriceSignedLog :
    QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  [⟨msgP, detSigP⟩, ⟨msgQ, detSigQ⟩, ⟨msgP, detSigP⟩, ⟨msgP, sigP1⟩]

/-! ## The forgeries

Four, all offered against the honest public key.  None of the library module's statements has a
verification hypothesis, so a forgery here does not have to verify — but which ones do is measured,
so that the branch the residual sends each to is not an artefact of offering nonsense.  Three
verify: the one the honest signer produced under fresh randomness, and the two built by perturbing a
logged signature in one of its two halves.  The fourth, which carries the randomizer the log
recorded at the other message, does not, and is asserted not to. -/

/-- A strong forgery on the *queried* message `msgP`: the honest signer run again under randomness
the log does not carry.  It verifies, and its exact pair is not in the log, which is the whole of
the strong-unforgeability freshness condition. -/
def forgeryFresh : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives msgP secretKey (node 0x51)

/-- A forgery carrying the first logged signature's randomizer and a perturbed FORS half. -/
def forgeryFors : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP1 with
      fors := sigP1.fors.set 0 { sigP1.fors[0] with sk := node (byteOf sigP1.fors[0].sk + 1) } }

/-- A forgery carrying the first logged signature's randomizer and a perturbed hypertree half. -/
def forgeryHt : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP1 with
      hypertree := sigP1.hypertree.set 0
        { sigP1.hypertree[0] with
            auth := sigP1.hypertree[0].auth.set 0 (node (byteOf sigP1.hypertree[0].auth[0] + 1)) } }

/-- A forgery on `msgP` carrying the randomizer the log recorded at `msgQ`.  The randomizer occurs
in the log, but not paired with `msgP`, so this pair is fresh; a reading of `loggedRandomizers` that
swept the whole log rather than the entries at one message would put it on the other branch. -/
def forgeryCross : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP1 with randomness := sigQ.randomness }

/-- The FORS public key `verifyInternal` recovers from a signature, which it then hands to the
hypertree as its layer-0 WOTS+ message.  Its arguments are the signature's FORS half, the digest
split and the honest public seed, so on two signatures whose splits agree — the seed being a fixture
constant — it is a function of the FORS half alone. -/
def recoveredForsPk (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) (msg : List Byte) :
    toyPrimitives.Y :=
  forsPkFromSig toyPrimitives sig.fors (schemeParts toy toyPrimitives msg sig honestPk).md.toList
    pkSeed (schemeParts toy toyPrimitives msg sig honestPk).forsAdrs

/-- The forged pair read as an ITSR candidate at the honest key pair. -/
def candidateOf (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) (msg : List Byte) :
    toyPrimitives.Y × HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y :=
  (sig.randomness, ⟨pkSeed, pkRoot, msg⟩)

/-- The transcript a reduction records from the signing log, embedded at the honest key pair. -/
def embeddedTargets :
    ITSRTranscript toyPrimitives.Y (HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y) :=
  embedTargets toyPrimitives pkSeed pkRoot (logQueries signingLog)

/-! ## The checks -/

/-- The fixture's own data: that hedged signing separates the two queries on one message, which of
the four forgeries verify against the honest public key and that the fourth does not, that each
fabricated forgery differs from the signature it was built from in exactly the intended half, and
that the cross forgery's randomizer is the one the log recorded at the *other* message.  Eighteen
properties. -/
def checkFixture : IO Unit := do
  ensure "hedged signing gives the two queries on one message different randomizers"
    (sigP1.randomness != sigP2.randomness)
  ensure "and different signatures"
    (sigP1 != sigP2)
  ensure "the three logged signatures verify"
    (GeneralScheme.verifyInternal toy toyPrimitives msgP sigP1 honestPk &&
      GeneralScheme.verifyInternal toy toyPrimitives msgP sigP2 honestPk &&
      GeneralScheme.verifyInternal toy toyPrimitives msgQ sigQ honestPk)
  ensure "the fresh-randomizer forgery verifies too"
    (GeneralScheme.verifyInternal toy toyPrimitives msgP forgeryFresh honestPk)
  ensure "its randomizer is neither of the two logged at that message"
    (forgeryFresh.randomness != sigP1.randomness && forgeryFresh.randomness != sigP2.randomness)
  ensure "and it is not one of the logged signatures"
    (forgeryFresh != sigP1 && forgeryFresh != sigP2 && forgeryFresh != sigQ)
  ensure "the FORS-perturbed forgery keeps the randomizer and the hypertree half"
    (forgeryFors.randomness == sigP1.randomness && forgeryFors.hypertree == sigP1.hypertree)
  ensure "and moves the FORS half"
    (forgeryFors.fors != sigP1.fors && forgeryFors != sigP1)
  ensure "the hypertree-perturbed forgery keeps the randomizer and the FORS half"
    (forgeryHt.randomness == sigP1.randomness && forgeryHt.fors == sigP1.fors)
  ensure "and moves the hypertree half"
    (forgeryHt.hypertree != sigP1.hypertree && forgeryHt != sigP1)
  ensure "both forgeries built from a logged signature verify as well"
    (GeneralScheme.verifyInternal toy toyPrimitives msgP forgeryFors honestPk &&
      GeneralScheme.verifyInternal toy toyPrimitives msgP forgeryHt honestPk)
  ensure "the cross forgery carries the randomizer the log recorded at the other message"
    (forgeryCross.randomness == sigQ.randomness)
  ensure "which is neither of the two recorded at this one"
    (forgeryCross.randomness != sigP1.randomness && forgeryCross.randomness != sigP2.randomness)
  ensure "and the cross forgery is the one that does not verify"
    (!GeneralScheme.verifyInternal toy toyPrimitives msgP forgeryCross honestPk)
  ensure "the three messages are pairwise distinct"
    (msgP != msgQ && msgP != msgU && msgQ != msgU)
  ensure "the deterministic variant is a different signature from either hedged one"
    (detSigP != sigP1 && detSigP != sigP2)
  ensure "and it verifies as well"
    (GeneralScheme.verifyInternal toy toyPrimitives msgP detSigP honestPk)
  ensure "the two logged messages differ in their exclusive-or fold, so their digests differ"
    (byteFold msgP != byteFold msgQ)

/-- What the log says at each message.  `loggedSignatures` is asserted against a hand-written list
at each of the three messages, in query order, and the two entries at `msgP` are both required to be
present: a reading that kept only the first, or only the last, fails here and is otherwise sound.
`mem_loggedSignatures` is exercised in both directions.  The list is pinned once more on
`thriceSignedLog`, where it is three long — the only place this file evaluates that list at a
length the other two logs never reach.  A reader that misbehaves only there is refused by this pin
and, through the randomizers it maps to, by `checkRandomizers`'s pin on the same log.  Ten
properties. -/
def checkLoggedSignatures : IO Unit := do
  ensure "the log has three entries on two distinct messages"
    (signingLog.length == 3 && (signingLog.map fun e => e.1).eraseDups.length == 2)
  ensure "both signatures at the twice-signed message are listed, in query order"
    (loggedSignatures signingLog msgP == [sigP1, sigP2])
  ensure "the first is not the only one"
    (decide (sigP2 ∈ loggedSignatures signingLog msgP))
  ensure "and the last is not the only one"
    (decide (sigP1 ∈ loggedSignatures signingLog msgP))
  ensure "the once-signed message lists one"
    (loggedSignatures signingLog msgQ == [sigQ])
  ensure "the unsigned message lists none"
    (loggedSignatures signingLog msgU == [])
  ensure "a signature at one message is not listed at the other"
    (!decide (sigQ ∈ loggedSignatures signingLog msgP) &&
      !decide (sigP1 ∈ loggedSignatures signingLog msgQ))
  ensure "the fresh-randomizer forgery is listed nowhere"
    (!decide (forgeryFresh ∈ loggedSignatures signingLog msgP) &&
      !decide (forgeryFresh ∈ loggedSignatures signingLog msgQ))
  ensure "listing is exact-entry membership, both ways"
    (decide ((⟨msgP, sigP2⟩ : (_ : List Byte) × _) ∈ signingLog) &&
      !decide ((⟨msgQ, sigP2⟩ : (_ : List Byte) × _) ∈ signingLog))
  ensure "a message signed three times lists all three, in query order"
    (loggedSignatures thriceSignedLog msgP == [detSigP, detSigP, sigP1])

/-- The two library predicates on a log, at all four combinations of their values.  Three are
realised by fixture data; the fourth — an unqueried message whose exact pair is nevertheless in the
log — is asserted unreachable over every entry of the log rather than omitted, because that is what
makes the library's queried/unqueried split exhaustive.  The replay case names both signatures the
log holds at that message, one of which is its first entry and the other its last, so a
`signingLogContains` that read only one end of the log fails here.  The two conjuncts of the
same-message condition are then falsified one at a time.

The last two read the same two predicates on the four-entry log, the only log here either of them
sees above three entries.  `wasQueried` is read at the one message that log queries and its first
entry does not, and `signingLogContains` at the one pair it holds only in its last entry.  Three
readings of the truncation family are refused there and nowhere else: a `wasQueried` that keeps only
the head once the log reaches four, and a `signingLogContains` that keeps only the head or drops the
last entry once it does.  Three more the file cannot reach at all, and the reason is the shape of
the logs rather than the shape of the checks: a `wasQueried` that drops its last entry, and one that
drops its first, are invisible at every threshold, because no log here carries a message at its
first entry only or at its last entry only; and a `signingLogContains` that drops its first entry is
invisible from four up, because this log's first pair is repeated at its third entry.  All three
would need a further log.  Reordering and collapsing are invisible to both predicates everywhere,
and no log could change that: `wasQueried` is non-emptiness of the entries at a message and
`signingLogContains` is membership of one pair, and neither can depend on the order of a log or on
repeats in it.  Ten properties. -/
def checkPredicates : IO Unit := do
  ensure "an unqueried message with a fresh pair: an ordinary existential forgery"
    (!signingLog.wasQueried msgU &&
      !SignatureAlg.signingLogContains signingLog msgU forgeryFresh)
  ensure "a queried message with a fresh pair: the residual"
    (signingLog.wasQueried msgP &&
      !SignatureAlg.signingLogContains signingLog msgP forgeryFresh)
  ensure "a queried message with a logged pair: a replay, at either entry it has there"
    (signingLog.wasQueried msgP && SignatureAlg.signingLogContains signingLog msgP sigP1 &&
      SignatureAlg.signingLogContains signingLog msgP sigP2)
  ensure "the fourth combination is unreachable: every logged pair's message is queried"
    (signingLog.all fun e => signingLog.wasQueried e.1)
  ensure "the same-message condition holds exactly at the residual"
    ((signingLog.wasQueried msgP &&
        !SignatureAlg.signingLogContains signingLog msgP forgeryFresh) &&
      !(signingLog.wasQueried msgU &&
        !SignatureAlg.signingLogContains signingLog msgU forgeryFresh) &&
      !(signingLog.wasQueried msgP && !SignatureAlg.signingLogContains signingLog msgP sigP1))
  ensure "its first conjunct fails alone at the unqueried message"
    (decide (loggedSignatures signingLog msgU = []) &&
      !decide (forgeryFresh ∈ loggedSignatures signingLog msgU))
  ensure "its second conjunct fails alone at a replayed pair"
    (decide (loggedSignatures signingLog msgP ≠ []) &&
      decide (sigP1 ∈ loggedSignatures signingLog msgP))
  ensure "and both hold at the residual"
    (decide (loggedSignatures signingLog msgP ≠ []) &&
      !decide (forgeryFresh ∈ loggedSignatures signingLog msgP))
  ensure "the four-entry log queries the message its head does not carry"
    (thriceSignedLog.wasQueried msgQ && !thriceSignedLog.wasQueried msgU)
  ensure "and contains the pair only its last entry carries, and no signature it never held"
    (SignatureAlg.signingLogContains thriceSignedLog msgP sigP1 &&
      !SignatureAlg.signingLogContains thriceSignedLog msgP sigP2)

/-- The randomizers, and the pair transcript.  The transcript is asserted against a hand-written
list; membership in it is asserted to be per-message, not per-log, by the cross forgery, whose
randomizer is in the transcript but not paired with the message it is offered at.  Both lists are
pinned again on `thriceSignedLog`: the randomizers at the thrice-signed message, which are three
long and carry a repeat, and the transcript, whose four entries carry a repeat.  Those are the
longest lists either reader produces in this file, and each differs from its own reverse, so between
them these two pins refuse every reordering, collapsing and truncation of the two readers that any
log here can reach.  What they do not reach is a reader that waits for a fourth randomizer at one
message or a fifth entry in a transcript.  Twelve properties. -/
def checkRandomizers : IO Unit := do
  ensure "the twice-signed message carries two distinct randomizers"
    (loggedRandomizers signingLog msgP == [sigP1.randomness, sigP2.randomness] &&
      (loggedRandomizers signingLog msgP).eraseDups.length == 2)
  ensure "the once-signed message carries one"
    (loggedRandomizers signingLog msgQ == [sigQ.randomness])
  ensure "the unsigned message carries none"
    (loggedRandomizers signingLog msgU == [])
  ensure "the fresh forgery's randomizer is not among them"
    (!decide (forgeryFresh.randomness ∈ loggedRandomizers signingLog msgP))
  ensure "the FORS-perturbed forgery's randomizer is"
    (decide (forgeryFors.randomness ∈ loggedRandomizers signingLog msgP))
  ensure "the cross forgery's randomizer is recorded, but at the other message"
    (!decide (forgeryCross.randomness ∈ loggedRandomizers signingLog msgP) &&
      decide (forgeryCross.randomness ∈ loggedRandomizers signingLog msgQ))
  ensure "a message signed three times lists its randomizer twice and then the other, in order"
    (loggedRandomizers thriceSignedLog msgP ==
      [detSigP.randomness, detSigP.randomness, sigP1.randomness])
  ensure "the transcript is the hand-written projection of the log"
    (logQueries signingLog ==
      [(sigP1.randomness, msgP), (sigQ.randomness, msgQ), (sigP2.randomness, msgP)])
  ensure "the cross forgery's pair is absent from it although its randomizer is present"
    (!decide ((forgeryCross.randomness, msgP) ∈ logQueries signingLog) &&
      decide ((forgeryCross.randomness, msgQ) ∈ logQueries signingLog))
  ensure "no pair at the unsigned message is in it, whatever randomizer it carries"
    ([sigP1.randomness, sigP2.randomness, sigQ.randomness, forgeryFresh.randomness].all
      fun r => !decide ((r, msgU) ∈ logQueries signingLog))
  ensure "and the two pairs at the twice-signed message are"
    (decide ((sigP1.randomness, msgP) ∈ logQueries signingLog) &&
      decide ((sigP2.randomness, msgP) ∈ logQueries signingLog))
  ensure "a four-entry log's transcript keeps every query, repeats included"
    (logQueries thriceSignedLog ==
      [(detSigP.randomness, msgP), (detSigQ.randomness, msgQ), (detSigP.randomness, msgP),
        (sigP1.randomness, msgP)])

/-- What each branch does at the embedded transcript.  The transcript itself is pinned by value
first, which fixes its length, its order and its multiplicity together; and because embedding
`signingLog`'s transcript cannot show a collapse — that transcript's three pairs are distinct — the
embeddings of the other two logs are pinned beside it: `thriceSignedLog`'s four-entry transcript,
which carries a repeat and differs from its reverse, and `deterministicLog`'s three-entry one, which
carries a repeat and is its own reverse.  None of the three subsumes another: the first is the only
one that refuses a reversal at exactly three entries, the third the only one that refuses a collapse
there, and the second the only one that reaches four.  Then, on the fresh branch the candidate is
absent and the bridge's dichotomy is run to see which alternative it takes; on the logged branch the
candidate is present, the winning condition fails, and — asserted separately, because otherwise "the
winning condition fails" would not say *which* conjunct failed — the coverage conjunct still holds
and the first-uncovered-index extractor returns nothing.  The index list the coverage check
quantifies over is separately asserted to have length two, because `List.all` over `[]` is `true`.
Each of those five is written with the FORS-perturbed forgery, and each carries to the
hypertree-perturbed one, because the two are asserted to offer the same candidate — which they do
because they carry the same randomizer, and which is what makes this branch reachable twice.
Thirteen properties. -/
def checkBranches : IO Unit := do
  ensure "the embedded transcript is the log's three queries at the honest key pair, in order"
    (embeddedTargets ==
      [(sigP1.randomness, ⟨pkSeed, pkRoot, msgP⟩), (sigQ.randomness, ⟨pkSeed, pkRoot, msgQ⟩),
        (sigP2.randomness, ⟨pkSeed, pkRoot, msgP⟩)])
  ensure "embedding a four-entry transcript keeps its repeat, in order"
    (embedTargets toyPrimitives pkSeed pkRoot (logQueries thriceSignedLog) ==
      [(detSigP.randomness, ⟨pkSeed, pkRoot, msgP⟩), (detSigQ.randomness, ⟨pkSeed, pkRoot, msgQ⟩),
        (detSigP.randomness, ⟨pkSeed, pkRoot, msgP⟩), (sigP1.randomness, ⟨pkSeed, pkRoot, msgP⟩)])
  ensure "and embedding the deterministic log's three-entry transcript keeps its repeat too"
    (embedTargets toyPrimitives pkSeed pkRoot (logQueries deterministicLog) ==
      [(detSigP.randomness, ⟨pkSeed, pkRoot, msgP⟩), (detSigQ.randomness, ⟨pkSeed, pkRoot, msgQ⟩),
        (detSigP.randomness, ⟨pkSeed, pkRoot, msgP⟩)])
  ensure "the fresh forgery's candidate is not one of them"
    (!decide (candidateOf forgeryFresh msgP ∈ embeddedTargets))
  ensure "nor is any candidate at the unsigned message"
    ([sigP1.randomness, sigP2.randomness, sigQ.randomness, forgeryFresh.randomness].all
      fun r => !decide ((r, (⟨pkSeed, pkRoot, msgU⟩ :
        HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) ∈ embeddedTargets))
  ensure "the FORS-perturbed forgery's candidate is one of them"
    (decide (candidateOf forgeryFors msgP ∈ embeddedTargets))
  ensure "and the hypertree-perturbed forgery offers that same candidate"
    (candidateOf forgeryHt msgP == candidateOf forgeryFors msgP)
  ensure "so its winning condition fails"
    (!decide ((hmsgItsrProblem toyPrimitives).Wins embeddedTargets (candidateOf forgeryFors msgP)))
  ensure "the candidate selects two FORS leaves, so that quantification is not over nothing"
    (((hmsgItsrProblem toyPrimitives).indexSet (candidateOf forgeryFors msgP)).length == 2)
  ensure "and it fails on freshness alone: every index it selects is covered"
    (((hmsgItsrProblem toyPrimitives).indexSet (candidateOf forgeryFors msgP)).all
      fun i => decide (i ∈ (hmsgItsrProblem toyPrimitives).targetIndexSet embeddedTargets))
  ensure "so the first-uncovered-index extractor returns nothing"
    (findUncoveredIndex toyPrimitives embeddedTargets (candidateOf forgeryFors msgP) == none)
  ensure "the cross forgery's candidate is absent, so its branch is the fresh one"
    (!decide (candidateOf forgeryCross msgP ∈ embeddedTargets))
  ensure "the fresh forgery's candidate selects an index no target covers"
    ((findUncoveredIndex toyPrimitives embeddedTargets (candidateOf forgeryFresh msgP)).isSome)

/-- What two signatures with one randomizer share.  The digest split agrees for the two forgeries
that keep the logged signature's randomizer and disagrees for the two that carry a different one, so
the agreement is not an artefact of the profile; the pair of FORS leaves that digest opens follows
the split, and is asserted for all four; and the component disequality is exhibited on each of its
two disjuncts by a different forgery.

The last three are about what the pair hands the hypertree.  Neither disjunct of that disequality
decides the recovered FORS public key: the forgery that moves only the hypertree half recovers the
logged signature's key, so does the one that moves the FORS half, and a third FORS half — the second
tree's secret bumped — recovers a different one.  That is the module's reason for saying the WOTS+
guard is met on some of the branch's pairs rather than on all of them.  Eleven properties. -/
def checkSameRandomizer : IO Unit := do
  ensure "the FORS-perturbed forgery splits to the logged signature's digest"
    (schemeParts toy toyPrimitives msgP forgeryFors honestPk ==
      schemeParts toy toyPrimitives msgP sigP1 honestPk)
  ensure "so does the hypertree-perturbed one"
    (schemeParts toy toyPrimitives msgP forgeryHt honestPk ==
      schemeParts toy toyPrimitives msgP sigP1 honestPk)
  ensure "the fresh-randomizer forgery does not"
    (schemeParts toy toyPrimitives msgP forgeryFresh honestPk !=
      schemeParts toy toyPrimitives msgP sigP1 honestPk)
  ensure "nor does the cross forgery"
    (schemeParts toy toyPrimitives msgP forgeryCross honestPk !=
      schemeParts toy toyPrimitives msgP sigP1 honestPk)
  ensure "a shared digest means the same two FORS leaves are opened, for both that share one"
    (hmsgIndices toyParams (toyPrimitives.Hmsg forgeryFors.randomness pkSeed pkRoot msgP) ==
        hmsgIndices toyParams (toyPrimitives.Hmsg sigP1.randomness pkSeed pkRoot msgP) &&
      hmsgIndices toyParams (toyPrimitives.Hmsg forgeryHt.randomness pkSeed pkRoot msgP) ==
        hmsgIndices toyParams (toyPrimitives.Hmsg sigP1.randomness pkSeed pkRoot msgP))
  ensure "and a different digest opens a different pair, for both that carry one"
    (hmsgIndices toyParams (toyPrimitives.Hmsg forgeryFresh.randomness pkSeed pkRoot msgP) !=
        hmsgIndices toyParams (toyPrimitives.Hmsg sigP1.randomness pkSeed pkRoot msgP) &&
      hmsgIndices toyParams (toyPrimitives.Hmsg forgeryCross.randomness pkSeed pkRoot msgP) !=
        hmsgIndices toyParams (toyPrimitives.Hmsg sigP1.randomness pkSeed pkRoot msgP))
  ensure "one forgery realises the first disjunct of the component disequality"
    (forgeryFors.fors != sigP1.fors && forgeryFors.hypertree == sigP1.hypertree)
  ensure "and another the second"
    (forgeryHt.hypertree != sigP1.hypertree && forgeryHt.fors == sigP1.fors)
  ensure "moving the hypertree half alone leaves the recovered FORS public key where it was"
    (recoveredForsPk forgeryHt msgP == recoveredForsPk sigP1 msgP)
  ensure "and moving the FORS half need not move it either"
    (recoveredForsPk forgeryFors msgP == recoveredForsPk sigP1 msgP &&
      forgeryFors.fors != sigP1.fors)
  ensure "though another FORS half does move it: the second tree's secret bumped by one"
    (recoveredForsPk
        { sigP1 with
            fors := sigP1.fors.set 1
              { sigP1.fors[1] with sk := node (byteOf sigP1.fors[1].sk + 1) } } msgP !=
      recoveredForsPk sigP1 msgP)

/-- The formulation difference the module is about, measured.  Under FIPS 205's hedged default the
log at a twice-signed message carries two randomizers, so pair freshness there is two disequalities
and the residual's second branch is reachable; under its deterministic variant, which is the shape
the EasyCrypt development's message-keyed signer has, the same three queries leave one.  The
deterministic log's transcript is pinned too, because `signingLog`'s three pairs are distinct and a
`logQueries` that de-duplicated would be invisible on it; this log and `thriceSignedLog` are the two
that carry a repeated entry.  The same holds of `loggedRandomizers`,
whose two deterministic entries at that message are equal, so that list is pinned by value rather
than only through `eraseDups`.  Seven properties. -/
def checkVariants : IO Unit := do
  ensure "the deterministic variant's two queries on one message are one signature"
    (loggedSignatures deterministicLog msgP == [detSigP, detSigP])
  ensure "so its log carries one randomizer at that message"
    ((loggedRandomizers deterministicLog msgP).eraseDups.length == 1)
  ensure "listed once per query, so the list itself carries the repeat"
    (loggedRandomizers deterministicLog msgP == [detSigP.randomness, detSigP.randomness])
  ensure "while the hedged log carries two"
    ((loggedRandomizers signingLog msgP).eraseDups.length == 2)
  ensure "both logs record the same number of queries at that message"
    ((loggedSignatures deterministicLog msgP).length ==
      (loggedSignatures signingLog msgP).length)
  ensure "and the deterministic variant's own randomizer differs from both hedged ones"
    (detSigP.randomness != sigP1.randomness && detSigP.randomness != sigP2.randomness)
  ensure "the deterministic variant's transcript still records both queries at that message"
    (logQueries deterministicLog ==
      [(detSigP.randomness, msgP), (detSigQ.randomness, msgQ), (detSigP.randomness, msgP)])

/-! ## The library statements, pinned at this bundle

Every theorem the module exports appears below at the toy bundle's own types, with generic arguments
where the statement has them, so what is pinned is the statement's shape and not a value; the check
groups above are what pin the values.  There are twenty-two, one per exported theorem; the three
exported definitions appear inside them. -/

section Pins

variable (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core))
  (msg : List Byte) (sig sig' : GeneralScheme.SignatureCore toy toyPrimitives.core)
  (pk : PublicKeyCore toyPrimitives.core) (r : toyPrimitives.Y)

example : loggedSignatures log msg =
    log.filterMap fun e => if e.1 = msg then some e.2 else none :=
  loggedSignatures_eq log msg

example : sig ∈ loggedSignatures log msg ↔ (⟨msg, sig⟩ : (_ : List Byte) × _) ∈ log :=
  mem_loggedSignatures

example : SignatureAlg.signingLogContains log msg sig = true ↔ sig ∈ loggedSignatures log msg :=
  signingLogContains_eq_true_iff log msg sig

example : log.wasQueried msg = true ↔ loggedSignatures log msg ≠ [] :=
  wasQueried_eq_true_iff log msg

example (h : sig ∈ loggedSignatures log msg) : log.wasQueried msg = true :=
  wasQueried_eq_true_of_mem_loggedSignatures h

example : (log.wasQueried msg && !SignatureAlg.signingLogContains log msg sig) = true ↔
    loggedSignatures log msg ≠ [] ∧ sig ∉ loggedSignatures log msg :=
  sameMessage_condition_iff log msg sig

example (h : (log.wasQueried msg && !SignatureAlg.signingLogContains log msg sig) = true) :
    ∃ s ∈ loggedSignatures log msg, s ≠ sig :=
  exists_ne_of_sameMessage h

example (h : log.wasQueried msg = false) : loggedSignatures log msg = [] :=
  loggedSignatures_eq_nil_of_not_wasQueried h

example : loggedRandomizers log msg =
    (loggedSignatures log msg).map fun s => s.randomness :=
  loggedRandomizers_eq log msg

example : r ∈ loggedRandomizers log msg ↔ ∃ s ∈ loggedSignatures log msg, s.randomness = r :=
  mem_loggedRandomizers

example : logQueries log = log.map fun e => (e.2.randomness, e.1) := logQueries_eq log

example : (r, msg) ∈ logQueries log ↔ r ∈ loggedRandomizers log msg := mem_logQueries_iff

example (h : log.wasQueried msg = false) : (r, msg) ∉ logQueries log :=
  notMem_logQueries_of_not_wasQueried h r

example (h : log.wasQueried msg = false) :
    (r, (⟨pk.pkSeed, pk.pkRoot, msg⟩ :
        HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) ∉
      embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries log) :=
  notMem_embedTargets_of_not_wasQueried pk h r

example (h : r ∉ loggedRandomizers log msg) :
    (r, (⟨pk.pkSeed, pk.pkRoot, msg⟩ :
        HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) ∉
      embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries log) :=
  notMem_embedTargets_of_notMem_loggedRandomizers pk h

example (h : r ∈ loggedRandomizers log msg) :
    (r, (⟨pk.pkSeed, pk.pkRoot, msg⟩ :
        HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) ∈
      embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries log) :=
  mem_embedTargets_of_mem_loggedRandomizers pk h

example (h : r ∈ loggedRandomizers log msg) :
    ¬ (hmsgItsrProblem toyPrimitives).Wins
      (embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries log))
      (r, ⟨pk.pkSeed, pk.pkRoot, msg⟩) :=
  not_wins_of_mem_loggedRandomizers (vp := toy) pk h

example (h : r ∈ loggedRandomizers log msg) :
    findUncoveredIndex toyPrimitives
      (embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries log))
      (r, ⟨pk.pkSeed, pk.pkRoot, msg⟩) = none :=
  findUncoveredIndex_eq_none_of_mem_loggedRandomizers pk h

example (h : r ∉ loggedRandomizers log msg) :
    (hmsgItsrProblem toyPrimitives).Wins
        (embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries log))
        (r, ⟨pk.pkSeed, pk.pkRoot, msg⟩) ∨
      ∃ idx, findUncoveredIndex toyPrimitives
          (embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries log))
          (r, ⟨pk.pkSeed, pk.pkRoot, msg⟩) = some idx ∧
        idx ∈ (hmsgItsrProblem toyPrimitives).indexSet (r, ⟨pk.pkSeed, pk.pkRoot, msg⟩) ∧
        idx ∉ (hmsgItsrProblem toyPrimitives).targetIndexSet
          (embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries log)) :=
  wins_or_uncovered_of_notMem_loggedRandomizers (vp := toy) pk h

example (h : sig.randomness = sig'.randomness) :
    schemeParts toy toyPrimitives msg sig pk = schemeParts toy toyPrimitives msg sig' pk :=
  schemeParts_eq_of_randomizer_eq msg sig sig' pk h

example (hne : sig ≠ sig') (hr : sig.randomness = sig'.randomness) :
    sig.fors ≠ sig'.fors ∨ sig.hypertree ≠ sig'.hypertree :=
  components_ne_of_ne_of_randomizer_eq hne hr

example (hfresh : SignatureAlg.signingLogContains log msg sig = false) :
    (sig.randomness, (⟨pk.pkSeed, pk.pkRoot, msg⟩ :
          HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) ∉
        embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries log) ∨
      ∃ s ∈ loggedSignatures log msg, s.randomness = sig.randomness ∧ s ≠ sig ∧
        schemeParts toy toyPrimitives msg sig pk = schemeParts toy toyPrimitives msg s pk ∧
        (sig.fors ≠ s.fors ∨ sig.hypertree ≠ s.hypertree) :=
  itsrFresh_or_sameRandomizer log msg sig pk hfresh

end Pins

/-- Run the seven check groups in order, then report. -/
def main : IO Unit := do
  checkFixture
  checkLoggedSignatures
  checkPredicates
  checkRandomizers
  checkBranches
  checkSameRandomizer
  checkVariants
  IO.println "SLH-DSA SUF residual tests: PASS"

end SLHDSA.SufResidualTest

/-- Entry point for `slhdsa_suf_residual_tests`. -/
def main : IO Unit := SLHDSA.SufResidualTest.main
