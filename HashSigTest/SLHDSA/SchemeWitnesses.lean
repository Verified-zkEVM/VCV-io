/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.SchemeWitnesses
public import HashSig.SLHDSA.Security.EncodedTargets

/-!
# SLH-DSA scheme witness dispatch canaries

Executable checks that a verifying SLH-DSA signature routes into the *right arm* of the composite
witness type, and that the witness it yields there attacks honest key material computed at the
position the signature's own digest names — evaluated at the values, not restated from the theorems.

No collision is exhibitable under an approved instantiation, so the canaries run over a toy
primitive bundle whose `Thash` folds its input with a two-bit shift and drops the low bit of every
child, then exclusive-ors a tweak derived from the whole address and the public seed.

## Why the bundle is new rather than inherited

The bundle the hypertree canaries of this lane use cannot serve here, and the reason is the point of
this fixture.  Its `H_msg` and its `PRF_msg` are both constant and its public seed is a unit, so a
dispatch canary built on it would be inert: every message would produce one digest, every digest
would name one FORS instance and one layer-zero position, and no re-evaluation at "another site"
would move anything.  This bundle's `H_msg` reads all four of its FIPS inputs — the randomizer, the
public seed, the published root and the message — and its `PRF_msg` reads the per-signature
`addrnd`; `checkToyBundle` moves each of those six inputs on its own and requires the digest or the
randomizer to move with it.  The public seed is a byte rather than a unit, so it is load-bearing in
`H_msg`, in the secret map and in every tweak.

The profile is `k = 2` and `d = 2`, which is what makes the two FORS trees and the two hypertree
layers separable: with one FORS tree the global leaf index and the local one coincide, and with one
layer there is no other layer to re-evaluate a witness at.

The toy `H_msg` reads the message only through the exclusive-or of its bytes.  That is a deliberate
weakness: it is what lets the fixture exhibit a signature that verifies for a message the signer
never signed, which is the situation the dispatch exists for, in a bundle with no collision
resistance to appeal to.

## The two forgery sites

Two digests, at two different bottom positions with two different FORS messages, each named by one
signature's own randomizer.  Site A is layer-zero tree one, leaf three; site B is tree two, leaf
zero.  Every honest value either arm attacks therefore differs between them, and every extraction
canary re-evaluates its witness at the other site and requires that to fail.

## The signatures, and which arm each takes

* **A** is the honest signature on site A's message.  Its recovered FORS public key is the honest
  one, so it takes the FORS arm, and the extractor returns the `F`-preimage of the honest leaf image
  at the caller's chosen tree.  The same signature is offered against a second message with the same
  byte fold: the digest, the verification outcome and the extracted witness all agree, which pins
  that the dispatch reads the message only through `H_msg`.
* **D** carries a FORS half whose tree-zero revealed value moves that tree's *leaf image* but not
  the recovered public key — the toy hashes drop the moved bit twice over.  It still takes the FORS
  arm, and the extractor returns the `H`-collision the move creates instead.
* **B** carries a FORS half whose recovered public key does move, under an honest hypertree
  signature on that recovered value.  It takes the hypertree arm and diverges at layer zero.
* **C** carries the same FORS half, a perturbed layer-zero component whose recovered root misses
  layer zero's honest root, and an honest top-layer signature on the root that component does
  recover.  It takes the hypertree arm and diverges at layer one.
* **E** carries the same FORS half under the hypertree signature on the *honest* FORS public key.
  It verifies all the same, and the extractor returns an XMSS `H`-collision at layer one rather than
  a WOTS+ witness, which is the branch whose assertion set differs.
* **N** perturbs the top-layer component as well, so no layer's recovered root is that layer's
  honest root.  It does not verify and the extractor returns nothing.

`sigD` and `sigB` share a randomizer and a message, hence a digest, an instance address and every
honest value; they differ only in their FORS halves, and they take different arms.  That pair is
what pins that the arm is decided by the FORS public-key comparison and by nothing else.

## What `Witness.Valid` cannot see, and what is checked instead

`Witness.Valid` reads the signature only through the digest its randomizer produces.  A FORS witness
extracted from `sigD` therefore *does* satisfy `Witness.Valid` against `sigB`, and
`checkArmSelection` asserts that it holds rather than pretending it should not: the arm selection is
a property of `findWitness`, not of the predicate.  What the canaries falsify about the predicate
is the *arguments* each arm is evaluated at — the FORS instance address and FORS message for one
arm, the position and honest running message for the other — by re-evaluating each witness at the
other site,
at the other layer, and at the message the forged signature actually carries there.  That last one
is the naive identification the fixture is designed to defeat: it is what a reader reaches for who
takes the honest partner off the signature instead of computing it from the secret seed, and it is
required to fail.

Two re-evaluations at this fixture are inert, and both are asserted to hold rather than passed over,
with the reason asserted alongside.  Moving a WOTS+ `F`-preimage witness's honest running message to
the other layer's does not discriminate, because that branch reads the honest message only through
the WOTS+ step count at the extracted chain and the two layers' honest messages give the same count
there; the canary asserts that equality next to it, and asserts that the naive message's count
differs.  An XMSS `H`-collision witness never reads the honest running message at all.

## The other canaries

`checkToyBundle` is the fixture's own liveness and the agreement of every hand-written table with
the library's computation of it: the four positions, the two honest-running-message tables, the
global FORS leaf index, and the four honest values the re-evaluations recompute.  The global FORS
leaf addresses are additionally matched against a table of `Adrs` records written out by hand, so a
change in how the global index reaches the address is caught there rather than only through
`forsSigLeafIndex`.

`checkSchemeEquations` evaluates the two equations this pull request adds to `SLHDSA.GeneralScheme`
at every signature the fixture builds.  `checkHonestPartner` pins that the honest layer-zero partner
depends on the digest's *position* and not on its FORS message, which is what makes the hypertree
arm's honest starting message well defined for a message the signer never signed.
`checkFabricated` is the tally: four hand-built witnesses accepted and ten rejected, the rejected
ones covering both sites, both layer relabellings, both FORS height bounds, a wrong preimage value
and a `T_k` "second preimage" of the honest root vector itself.  There is no out-of-range layer
fabrication, and there cannot be one: `HypertreeWitness.layer` is a `Fin toyParams.d`, so a label at
or beyond `d` does not elaborate.

The `example`s pin the library statements at this bundle — the three new `GeneralScheme` equations,
the dispatch, both shape equations, both unfolding equations, soundness, completeness, the three
ledger bridges, the two the hypertree arm does not need, three encoded-distinctness bridges under
the SHA-2 and SHAKE encoders, and all seven of the lane's `_eval` bridges reached through the
composite predicate.
-/

public section

namespace SLHDSA.SchemeWitnessesTest

open Security Security.CanonicalGames Concrete GeneralHypertree

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"Scheme witness check failed: {label}")

/-! ## The toy profile

Two hypertree layers of height two, two FORS trees of height one, `w = 16`, `len = 4`. -/

-- Exposed: the profile and its validated form have to reduce inside the `decide` pins below and
-- inside the bundle they index, and the bundle itself has to reduce for the `Fin` bounds of the
-- hand-written positions.  Neither the secret map, the tweak map, the randomizer, the digest map
-- nor any of the four positions needs exposure of its own.  Nothing outside this executable
-- consumes them.
/-- Two layers of height two, two FORS trees of height one. -/
@[expose] def toyParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 4 }

theorem toyValid : toyParams.Valid := by decide

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

/-- The honest public key. -/
def honestPk : PublicKeyCore toyPrimitives.core := ⟨pkSeed, pkRoot⟩

/-- The honest secret key. -/
def secretKey : SecretKeyCore toyPrimitives.core := ⟨skSeed, skPrf, pkSeed, pkRoot⟩
/-! ## The two forgery sites

Two digests, each named by one signature's own randomizer, at two different bottom positions and
two different FORS messages.  Every table below is written out by hand and asserted to agree with
the library's computation of it in `checkToyBundle`. -/

/-- The randomizer for a message under a chosen `addrnd`, as FIPS 205 Algorithm 19 line 3
computes it. -/
def rOf (addrnd : UInt8) (msg : List Byte) : toyPrimitives.Y :=
  toyPrimitives.PRFmsg skPrf (node addrnd) msg

/-- The digest split a randomizer and a message produce against the honest public key. -/
def digestOf (r : toyPrimitives.Y) (msg : List Byte) : DigestParts toyParams :=
  splitDigest toyParams (toyPrimitives.Hmsg r pkSeed pkRoot msg)

/-- Site A's per-signature randomness. -/
def addrndA : UInt8 := 0x44

/-- Site A's message. -/
def msgA : List Byte := [0x01, 0x02]

/-- A second message with the same exclusive-or fold, hence the same digest under the toy
`H_msg`. -/
def msgA' : List Byte := [0x02, 0x01]

/-- Site B's per-signature randomness. -/
def addrndB : UInt8 := 0x66

/-- Site B's message. -/
def msgB : List Byte := [0x05]

/-- Site B's randomizer. -/
def rB : toyPrimitives.Y := rOf addrndB msgB

/-- Site A's digest split: FORS message `0xFB`, layer-zero tree one, leaf three. -/
def partsA : DigestParts toyParams := digestOf (rOf addrndA msgA) msgA

/-- Site B's digest split: FORS message `0xB8`, layer-zero tree two, leaf zero. -/
def partsB : DigestParts toyParams := digestOf rB msgB

/-- Site A's layer-zero position, written out. -/
def posA0 : LayerPosition toy := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩⟩

/-- Site A's top-layer position, written out. -/
def posA1 : LayerPosition toy := ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩

/-- Site B's layer-zero position, written out. -/
def posB0 : LayerPosition toy := ⟨⟨0, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩⟩

/-- Site B's top-layer position, written out. -/
def posB1 : LayerPosition toy := ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩⟩

/-- Site A's positions by layer.  The catch-all makes the function total; every caller reads a
`Fin toyParams.d` or one of the two literals. -/
def posOfA : ℕ → LayerPosition toy
  | 0 => posA0
  | _ => posA1

/-- Site B's positions by layer. -/
def posOfB : ℕ → LayerPosition toy
  | 0 => posB0
  | _ => posB1

/-! ## Honest key material, recomputed

Every honest value a witness attacks is recomputed here from the construction's own primitives —
`PerfectMerkleTree.merkleRoot`, `toyPrimitives.F`, `.H`, `.Tl`, `.PRF` and the address builders —
rather than read off the witness modules' helpers.  `checkToyBundle` asserts the two agree wherever
the library also computes one. -/

/-- The honest FORS secret value at a global leaf index, recomputed from the bundle's `PRF`. -/
def honestForsSecret (adrs : Adrs) (t : ℕ) : toyPrimitives.Y :=
  toyPrimitives.PRF pkSeed skSeed (forsSkAdrs adrs t)

/-- The honest FORS root vector at an instance address, recomputed as `k` Merkle roots of
height `a`. -/
def honestForsRoots (adrs : Adrs) : Vector toyPrimitives.Y toyParams.k :=
  Vector.ofFn fun i : Fin toyParams.k =>
    PerfectMerkleTree.merkleRoot (forsLeaf toyPrimitives skSeed pkSeed adrs)
      (forsNodeHash toyPrimitives pkSeed adrs) toyParams.a i.val

/-- The honest FORS child pair at an internal node, recomputed as two Merkle roots one height
down. -/
def honestForsChildren (adrs : Adrs) (z t : ℕ) : toyPrimitives.Y × toyPrimitives.Y :=
  (PerfectMerkleTree.merkleRoot (forsLeaf toyPrimitives skSeed pkSeed adrs)
      (forsNodeHash toyPrimitives pkSeed adrs) (z - 1) (2 * t),
    PerfectMerkleTree.merkleRoot (forsLeaf toyPrimitives skSeed pkSeed adrs)
      (forsNodeHash toyPrimitives pkSeed adrs) (z - 1) (2 * t + 1))

/-- The global FORS leaf index a digest opens in tree `i`, written out as
`tree · 2 ^ a + local leaf` rather than taken from `forsSigLeafIndex`.  At `a = 1` and `k = 2` the
four global indices are `0`, `1`, `2` and `3`, and `checkToyBundle` evaluates the address of each
against a hand-written table. -/
def globalLeafAt (md : List Byte) (i : ℕ) : ℕ := i * 2 ^ toyParams.a + forsIdx toyParams md i

/-- The honest WOTS+ signature at a leaf's base address on an honest message. -/
def honestWotsSig (la : Adrs) (hmsg : toyPrimitives.Y) : WotsSig toyParams toyPrimitives.core :=
  wotsSign toyPrimitives hmsg skSeed pkSeed la

/-- The honest WOTS+ chain ends there, advanced from the honest signature rather than taken from
`wotsPkGenTops`. -/
def honestWotsTops (la : Adrs) (hmsg : toyPrimitives.Y) :
    Vector toyPrimitives.Y toyParams.len :=
  Vector.ofFn fun i : Fin toyParams.len =>
    chain toyPrimitives pkSeed (wotsChainAdrs la i.val) (honestWotsSig la hmsg)[i.val]
      (chainStepsCore toyPrimitives.core hmsg i.val)
      (toyParams.w - 1 - chainStepsCore toyPrimitives.core hmsg i.val)

/-- The honest chain value at a hash address, advanced from the honest revealed value. -/
def honestChainValue (la : Adrs) (hmsg : toyPrimitives.Y) (i : Fin toyParams.len) (step : ℕ) :
    toyPrimitives.Y :=
  chain toyPrimitives pkSeed (wotsChainAdrs la i.val) (honestWotsSig la hmsg)[i.val]
    (chainStepsCore toyPrimitives.core hmsg i.val)
    (step - chainStepsCore toyPrimitives.core hmsg i.val)

/-- The honest XMSS child pair at an internal node, recomputed from `PerfectMerkleTree`. -/
def honestXmssChildren (adrs : Adrs) (z t : ℕ) : toyPrimitives.Y × toyPrimitives.Y :=
  (PerfectMerkleTree.merkleRoot (xmssLeaf toyPrimitives skSeed pkSeed adrs)
      (xmssNodeHash toyPrimitives pkSeed adrs) (z - 1) (2 * t),
    PerfectMerkleTree.merkleRoot (xmssLeaf toyPrimitives skSeed pkSeed adrs)
      (xmssNodeHash toyPrimitives pkSeed adrs) (z - 1) (2 * t + 1))

/-- The honest XMSS root of the tree at a position. -/
def honestRootAt (pos : LayerPosition toy) : toyPrimitives.Y :=
  xmssRoot toyPrimitives skSeed pkSeed pos.toAdrs

/-- Site A's honest running messages by layer: the honest FORS public key at its bottom position,
then the honest XMSS root one layer down. -/
def honestMsgA : ℕ → toyPrimitives.Y
  | 0 => forsPkGen toyPrimitives skSeed pkSeed partsA.forsAdrs
  | _ => honestRootAt posA0

/-- Site B's honest running messages by layer. -/
def honestMsgB : ℕ → toyPrimitives.Y
  | 0 => forsPkGen toyPrimitives skSeed pkSeed partsB.forsAdrs
  | _ => honestRootAt posB0

/-! ## Re-evaluating a witness at chosen arguments

Each `…Holds` function recomputes the condition its constructor asserts from the honest values
above, at an address, an index and an honest message supplied as arguments.  Taking those as
arguments is what lets the canaries run the *same* witness at the other forgery site and at the
other layer, and watch it fail. -/

/-- The nine conjuncts of `WotsWitness.Valid`. -/
def wotsWitnessHolds (la : Adrs) (hmsg : toyPrimitives.Y) :
    WotsWitness toyParams toyPrimitives → Bool
  | .tlCollision recovered =>
      (recovered != honestWotsTops la hmsg) &&
        (toyPrimitives.Tl pkSeed (wotsPkAdrs la) recovered.toList ==
          toyPrimitives.Tl pkSeed (wotsPkAdrs la) (honestWotsTops la hmsg).toList)
  | .fPreimage i step value =>
      decide (step < toyParams.w - 1) &&
        decide (step + 1 = chainStepsCore toyPrimitives.core hmsg i.val) &&
        (toyPrimitives.F pkSeed ((wotsChainAdrs la i.val).setHashAddress step) value ==
          (honestWotsSig la hmsg)[i.val])
  | .fCollision i step value =>
      decide (step < toyParams.w - 1) &&
        decide (chainStepsCore toyPrimitives.core hmsg i.val ≤ step) &&
        (value != honestChainValue la hmsg i step) &&
        (toyPrimitives.F pkSeed ((wotsChainAdrs la i.val).setHashAddress step) value ==
          toyPrimitives.F pkSeed ((wotsChainAdrs la i.val).setHashAddress step)
            (honestChainValue la hmsg i step))

/-- The thirteen conjuncts of `XmssWitness.Valid`: four on `hCollision` and the nine above on the
`wots` branch. -/
def xmssWitnessHolds (adrs : Adrs) (idx : ℕ) (hmsg : toyPrimitives.Y) :
    XmssWitness toyParams toyPrimitives → Bool
  | .hCollision z c =>
      decide (0 < z) && decide (z ≤ toyParams.hp) &&
        (honestXmssChildren adrs z (idx / 2 ^ z) != c) &&
        (toyPrimitives.H pkSeed (xmssNodeAdrs adrs z (idx / 2 ^ z))
              (honestXmssChildren adrs z (idx / 2 ^ z)).1
              (honestXmssChildren adrs z (idx / 2 ^ z)).2 ==
          toyPrimitives.H pkSeed (xmssNodeAdrs adrs z (idx / 2 ^ z)) c.1 c.2)
  | .wots wt => wotsWitnessHolds (wotsLeafAdrs adrs idx) hmsg wt

/-- The seven conjuncts of `ForsWitness.Valid`: two on `tlCollision`, four on `hCollision` and one
on `fPreimage`. -/
def forsWitnessHolds (adrs : Adrs) (md : List Byte) :
    ForsWitness toyParams toyPrimitives → Bool
  | .tlCollision recovered =>
      (recovered != honestForsRoots adrs) &&
        (toyPrimitives.Tl pkSeed (forsPkAdrs adrs) recovered.toList ==
          toyPrimitives.Tl pkSeed (forsPkAdrs adrs) (honestForsRoots adrs).toList)
  | .hCollision i z c =>
      decide (0 < z) && decide (z ≤ toyParams.a) &&
        (honestForsChildren adrs z (globalLeafAt md i.val / 2 ^ z) != c) &&
        (toyPrimitives.H pkSeed (forsNodeAdrs adrs z (globalLeafAt md i.val / 2 ^ z))
              (honestForsChildren adrs z (globalLeafAt md i.val / 2 ^ z)).1
              (honestForsChildren adrs z (globalLeafAt md i.val / 2 ^ z)).2 ==
          toyPrimitives.H pkSeed (forsNodeAdrs adrs z (globalLeafAt md i.val / 2 ^ z)) c.1 c.2)
  | .fPreimage i value =>
      toyPrimitives.F pkSeed (forsNodeAdrs adrs 0 (globalLeafAt md i.val)) value ==
        toyPrimitives.F pkSeed (forsNodeAdrs adrs 0 (globalLeafAt md i.val))
          (honestForsSecret adrs (globalLeafAt md i.val))

/-- The one conjunct of `HypertreeWitness.Valid` at a full-depth walk, read through a position
table and an honest-running-message table supplied as arguments. -/
def hypertreeWitnessHolds (posOf : ℕ → LayerPosition toy) (msgOf : ℕ → toyPrimitives.Y)
    (w : HypertreeWitness toy toyPrimitives toyParams.d) : Bool :=
  xmssWitnessHolds (posOf w.layer.val).toAdrs (posOf w.layer.val).leaf.val (msgOf w.layer.val)
    w.witness

/-- `Witness.Valid`'s arm selection, evaluated: the FORS arm at an instance address and FORS
message, the hypertree arm at a position table and an honest-running-message table.  All four are
arguments, so the same witness can be offered at the other forgery site. -/
def witnessHolds (adrs : Adrs) (md : List Byte) (posOf : ℕ → LayerPosition toy)
    (msgOf : ℕ → toyPrimitives.Y) : Witness toy toyPrimitives → Bool
  | .fors w => forsWitnessHolds adrs md w
  | .hypertree w => hypertreeWitnessHolds posOf msgOf w

/-- `witnessHolds` at site A's four arguments. -/
def holdsA (w : Witness toy toyPrimitives) : Bool :=
  witnessHolds partsA.forsAdrs partsA.md.toList posOfA honestMsgA w

/-- `witnessHolds` at site B's four arguments. -/
def holdsB (w : Witness toy toyPrimitives) : Bool :=
  witnessHolds partsB.forsAdrs partsB.md.toList posOfB honestMsgB w

/-! ## Naming the constructor a witness carries

The extraction canaries pin the constructor as well as the arm, because which re-evaluations
discriminate depends on it. -/

/-- The FORS constructor and its coordinates. -/
def describeFors : ForsWitness toyParams toyPrimitives → String
  | .tlCollision _ => "fors.tlCollision"
  | .hCollision i z _ => s!"fors.hCollision tree={i.val} height={z}"
  | .fPreimage i _ => s!"fors.fPreimage tree={i.val}"

/-- The WOTS+ constructor and its coordinates. -/
def describeWots : WotsWitness toyParams toyPrimitives → String
  | .tlCollision _ => "wots.tlCollision"
  | .fPreimage i st _ => s!"wots.fPreimage chain={i.val} step={st}"
  | .fCollision i st _ => s!"wots.fCollision chain={i.val} step={st}"

/-- The XMSS constructor and its coordinates. -/
def describeXmss : XmssWitness toyParams toyPrimitives → String
  | .hCollision z _ => s!"xmss.hCollision height={z}"
  | .wots w => describeWots w

/-- The composite arm, and inside it the constructor. -/
def describe : Witness toy toyPrimitives → String
  | .fors w => describeFors w
  | .hypertree w => s!"hypertree layer={w.layer.val} " ++ describeXmss w.witness

/-! ## The signatures

Six in all.  Five verify against the honest public key: two route to the FORS arm and three to the
hypertree arm, and the three hypertree ones split between the two layers.  The sixth verifies
against nothing and is the case where the extractor returns `none`. -/

/-- **Forgery A**, the honest signature on `msgA`.  Its recovered FORS public key is the honest one,
so it routes to the FORS arm; the toy `H_msg` reads the message only through the exclusive-or of its
bytes, so the same signature verifies for `msgA'` as well, which is what makes a routed forgery on
an unsigned message exhibitable in a fixture with no collision resistance. -/
def sigA : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives msgA secretKey (node addrndA)

/-- The honest FORS signature at site B, which the two hypertree forgeries perturb. -/
def honestForsB : ForsSigCore toyParams toyPrimitives.core :=
  forsSign toyPrimitives partsB.md.toList skSeed pkSeed partsB.forsAdrs

/-- The honest FORS public key at site B's instance address. -/
def honestForsPkB : toyPrimitives.Y := forsPkGen toyPrimitives skSeed pkSeed partsB.forsAdrs

/-- A FORS signature whose tree-zero revealed value moves the tree-zero *leaf image* but not the
recovered public key: the toy `F` drops the low bit of its input, and the toy `H` then drops the low
bit of each child, so the perturbed leaf climbs to the same tree-zero root.  A signature carrying
this still routes to the FORS arm. -/
def collapsedFors : ForsSigCore toyParams toyPrimitives.core :=
  honestForsB.set 0 { honestForsB[0] with sk := node (byteOf honestForsB[0].sk + 2) }

/-- A FORS signature whose tree-one revealed value does move the recovered public key. -/
def forgedFors : ForsSigCore toyParams toyPrimitives.core :=
  honestForsB.set 1 { honestForsB[1] with sk := node (byteOf honestForsB[1].sk + 1) }

/-- The FORS public key `forgedFors` recovers, which differs from the honest one. -/
def forgedForsPk : toyPrimitives.Y :=
  forsPkFromSig toyPrimitives forgedFors partsB.md.toList pkSeed partsB.forsAdrs

/-- **Forgery D**: `collapsedFors` under an honest hypertree signature on the honest FORS public
key.  It verifies and routes to the FORS arm, where the moved leaf image yields an `H`-collision
rather than the honest signature's `F`-preimage. -/
def sigD : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  ⟨rB, collapsedFors,
    GeneralHypertree.sign toy toyPrimitives honestForsPkB skSeed pkSeed partsB⟩

/-- **Forgery B**: `forgedFors` under an honest hypertree signature on the FORS public key it
recovers.  The honest hypertree signer signs whatever message it is given, so the walk's layer-zero
recovery is that layer's honest root and the divergence is at layer zero. -/
def sigB : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  ⟨rB, forgedFors, GeneralHypertree.sign toy toyPrimitives forgedForsPk skSeed pkSeed partsB⟩

/-- The honest layer-zero XMSS signature on the forged FORS public key at site B. -/
def xmss0 : XmssSig toyParams toyPrimitives.core :=
  xmssSign toyPrimitives forgedForsPk skSeed pkSeed posB0.toAdrs posB0.leaf.val

/-- The same with its first authentication node moved, so its recovered root misses layer zero's
honest root and the walk cannot stop there. -/
def xmss0Perturbed : XmssSig toyParams toyPrimitives.core :=
  { xmss0 with auth := xmss0.auth.set 0 (node (byteOf xmss0.auth[0] + 2)) }

/-- The root the perturbed layer-zero component recovers, which the layer above must sign. -/
def divergedRoot : toyPrimitives.Y :=
  xmssPkFromSig toyPrimitives posB0.leaf.val xmss0Perturbed forgedForsPk pkSeed posB0.toAdrs

/-- **Forgery C**: the same FORS half, a perturbed layer-zero component, and an honest top-layer
signature on the root that component recovers.  The walk reaches the published root, misses at
layer zero, and diverges at layer one. -/
def sigC : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  ⟨rB, forgedFors,
    #v[xmss0Perturbed,
      xmssSign toyPrimitives divergedRoot skSeed pkSeed posB1.toAdrs posB1.leaf.val]⟩

/-- **Forgery E**, which is not one: `forgedFors` under the hypertree signature on the *honest*
FORS public key.  Verification fails and the walk finds no layer whose recovered root is that
layer's honest root, so the extractor returns nothing. -/
def sigE : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  ⟨rB, forgedFors,
    GeneralHypertree.sign toy toyPrimitives honestForsPkB skSeed pkSeed partsB⟩

/-- The two FORS trees, as extraction targets. -/
def tree0 : Fin toyParams.k := ⟨0, by decide⟩

/-- The second FORS tree. -/
def tree1 : Fin toyParams.k := ⟨1, by decide⟩

/-- A FORS signature as bytes, for comparison: `ForsSigCore` carries no `BEq`. -/
def forsBytes (f : ForsSigCore toyParams toyPrimitives.core) : List (List UInt8) :=
  f.toList.map fun tr => byteOf tr.sk :: tr.auth.toList.map byteOf

/-- A signature whose top-layer component is perturbed as well, so no layer's recovered root is
that layer's honest root.  It does not verify and the extractor returns nothing. -/
def sigN : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  ⟨rB, forgedFors,
    #v[xmss0Perturbed,
      (fun x : XmssSig toyParams toyPrimitives.core =>
          { x with auth := x.auth.set 1 (node (byteOf x.auth[1] + 1)) })
        (xmssSign toyPrimitives divergedRoot skSeed pkSeed posB1.toAdrs posB1.leaf.val)]⟩

/-! ## The bundle behaves as advertised -/

/-- The hand-written FORS leaf addresses at site B: layer zero, tree two, `FORS_TREE`, key-pair
zero, height zero, and the global leaf index in the tree-index word.  Written out rather than built
by `forsNodeAdrs`, so a change in how the global index reaches the address moves this table. -/
def forsLeafAdrsTable (j : ℕ) : Adrs := ⟨0, 2, AddrType.forsTree.toCode, 0, 0, j⟩

/-- Fifteen fixture properties.

The first six are the liveness of the two message-derived maps, which the previous fixture in this
lane could not exercise: its `H_msg` and `PRF_msg` were both constant and its public seed was a
unit.  Each of `H_msg`'s four FIPS inputs is moved on its own and the digest is required to move
with it, and `PRF_msg` is moved in each of its two.  The seventh is the exclusive-or fold's
collision, which is what makes a routed forgery on an unsigned message exhibitable here.

The next four separate the two forgery sites — different FORS instance address, different FORS
message, different layer-zero position and different top-layer position — and pin that both FORS
trees and both hypertree layers are live: the four global FORS leaves of a site carry four distinct
addresses, matched against a table written out by hand, and the two layers' honest roots and honest
running messages differ.

The last four are the agreement checks.  Every honest value the canaries evaluate is recomputed
here from the construction's primitives, and each is asserted equal to the witness modules' own
computation of it, so the canaries check the extractor against tables written independently of the
library's and known to match it. -/
def checkToyBundle : IO Unit := do
  ensure "H_msg moves with the randomizer"
    (splitDigest toyParams (toyPrimitives.Hmsg (node 0x01) pkSeed pkRoot msgB) !=
      splitDigest toyParams (toyPrimitives.Hmsg (node 0x02) pkSeed pkRoot msgB))
  ensure "H_msg moves with the message"
    (digestOf rB msgA != digestOf rB msgB)
  ensure "H_msg moves with the public seed"
    (splitDigest toyParams (toyPrimitives.Hmsg rB pkSeed pkRoot msgB) !=
      splitDigest toyParams (toyPrimitives.Hmsg rB otherPkSeed pkRoot msgB))
  ensure "H_msg moves with the published root"
    (splitDigest toyParams (toyPrimitives.Hmsg rB pkSeed pkRoot msgB) !=
      splitDigest toyParams (toyPrimitives.Hmsg rB pkSeed (node (byteOf pkRoot + 1)) msgB))
  ensure "PRF_msg moves with addrnd" (rOf addrndA msgB != rOf addrndB msgB)
  ensure "PRF_msg moves with the message" (rOf addrndB msgA != rOf addrndB msgB)
  ensure "and so the two sites' randomizers differ" (rOf addrndA msgA != rB)
  ensure "the two site-A messages differ but share a digest"
    (msgA != msgA' && byteFold msgA == byteFold msgA' &&
      digestOf (rOf addrndA msgA) msgA == digestOf (rOf addrndA msgA') msgA')
  ensure "the two sites differ in address and FORS message"
    (partsA.forsAdrs != partsB.forsAdrs && partsA.md != partsB.md)
  ensure "the two sites' positions differ at both layers"
    (posOfA 0 != posOfB 0 && posOfA 1 != posOfB 1)
  ensure "the four global FORS leaf addresses at site B are the hand-written ones"
    (((List.range 4).all fun j => forsNodeAdrs partsB.forsAdrs 0 j == forsLeafAdrsTable j) &&
      ((List.range 4).map forsLeafAdrsTable).Nodup)
  ensure "both hypertree layers are live at both sites"
    (honestRootAt (posOfA 0) != honestRootAt (posOfA 1) &&
      honestRootAt (posOfB 0) != honestRootAt (posOfB 1) &&
      honestMsgA 0 != honestMsgA 1 && honestMsgB 0 != honestMsgB 1)
  ensure "the hand-written positions agree with initial and next"
    (posOfA 0 == LayerPosition.initial toy partsA &&
      posOfA 1 == (LayerPosition.initial toy partsA).advance 1 (by decide) &&
      posOfB 0 == LayerPosition.initial toy partsB &&
      posOfB 1 == (LayerPosition.initial toy partsB).advance 1 (by decide))
  ensure "the hand-written honest running messages agree with honestLayerMsg"
    ((honestMsgA 0 ==
        honestLayerMsg toy toyPrimitives skSeed pkSeed (LayerPosition.initial toy partsA)
          (forsPkGen toyPrimitives skSeed pkSeed partsA.forsAdrs) 0 (by decide)) &&
      (honestMsgA 1 ==
        honestLayerMsg toy toyPrimitives skSeed pkSeed (LayerPosition.initial toy partsA)
          (forsPkGen toyPrimitives skSeed pkSeed partsA.forsAdrs) 1 (by decide)) &&
      (honestMsgB 0 ==
        honestLayerMsg toy toyPrimitives skSeed pkSeed (LayerPosition.initial toy partsB)
          (forsPkGen toyPrimitives skSeed pkSeed partsB.forsAdrs) 0 (by decide)) &&
      (honestMsgB 1 ==
        honestLayerMsg toy toyPrimitives skSeed pkSeed (LayerPosition.initial toy partsB)
          (forsPkGen toyPrimitives skSeed pkSeed partsB.forsAdrs) 1 (by decide)))
  ensure "the hand-written global leaf index agrees with forsSigLeafIndex"
    (((List.range 2).all fun i =>
        globalLeafAt partsA.md.toList i == forsSigLeafIndex toyParams partsA.md.toList i) &&
      ((List.range 2).all fun i =>
        globalLeafAt partsB.md.toList i == forsSigLeafIndex toyParams partsB.md.toList i))
  ensure "the recomputed honest values agree with the witness modules'"
    ((honestForsRoots partsB.forsAdrs == forsHonestRoots toyPrimitives skSeed pkSeed
        partsB.forsAdrs) &&
      (honestForsChildren partsB.forsAdrs 1 0 ==
        forsHonestChildren toyPrimitives skSeed pkSeed partsB.forsAdrs 1 0) &&
      (honestForsSecret partsB.forsAdrs 2 ==
        forsSkGenCore toyPrimitives.core skSeed pkSeed partsB.forsAdrs 2) &&
      (honestXmssChildren posB0.toAdrs 1 0 ==
        xmssHonestChildren toyPrimitives skSeed pkSeed posB0.toAdrs 1 0) &&
      (honestWotsTops (wotsLeafAdrs posB0.toAdrs posB0.leaf.val) (honestMsgB 0) ==
        wotsPkGenTops toyPrimitives skSeed pkSeed (wotsLeafAdrs posB0.toAdrs posB0.leaf.val)))

/-! ## The two merged-module equations, evaluated -/

/-- Key generation publishes the seed it was given and the general hypertree's root, and
verification is the decision of whether the recovered root is the published one.  Both are the
equations this pull request adds to `SLHDSA.GeneralScheme`, evaluated at each of the six signatures
the fixture builds rather than restated. -/
def checkSchemeEquations : IO Unit := do
  let generated := (GeneralScheme.keygenInternal toy toyPrimitives skSeed skPrf pkSeed).1
  ensure "keygen publishes the seed and the hypertree root"
    (generated.pkSeed == pkSeed && generated.pkRoot == pkRoot)
  for entry in [(msgA, sigA), (msgA', sigA), (msgB, sigD), (msgB, sigB), (msgB, sigC),
      (msgB, sigN)] do
    let msg := entry.1
    let sig := entry.2
    let parts := schemeParts toy toyPrimitives msg sig honestPk
    let recovered := forsPkFromSig toyPrimitives sig.fors parts.md.toList pkSeed parts.forsAdrs
    ensure "verification is the hypertree verifier at the digest"
      (GeneralScheme.verifyInternal toy toyPrimitives msg sig honestPk ==
        GeneralHypertree.verify toy toyPrimitives recovered sig.hypertree pkSeed parts pkRoot)
    ensure "verification is the decision on the recovered root"
      (GeneralScheme.verifyInternal toy toyPrimitives msg sig honestPk ==
        decide (GeneralHypertree.pkFromSig toy toyPrimitives recovered sig.hypertree pkSeed parts =
          pkRoot))

/-! ## The FORS arm -/

/-- One FORS-arm canary.  The signature verifies, its recovered FORS public key is the honest one at
the digest's instance address — which is what routes it here — and the extractor reports the FORS
constructor named.  The returned witness is evaluated at its own site and at the other one, and the
second is required to fail. -/
def checkForsArm (name : String) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) (target : Fin toyParams.k)
    (branch : String) (own other : Witness toy toyPrimitives → Bool) : IO Unit := do
  let parts := schemeParts toy toyPrimitives msg sig honestPk
  ensure s!"{name}: verifies" (GeneralScheme.verifyInternal toy toyPrimitives msg sig honestPk)
  ensure s!"{name}: recovers the honest FORS public key"
    (forsPkFromSig toyPrimitives sig.fors parts.md.toList pkSeed parts.forsAdrs ==
      forsPkGen toyPrimitives skSeed pkSeed parts.forsAdrs)
  match findWitness skSeed honestPk msg sig target with
  | none => throw (IO.userError s!"Scheme witness check failed: {name}: no witness")
  | some w => do
      ensure s!"{name}: reports {branch}" (describe w == branch)
      ensure s!"{name}: holds at its own site" (own w)
      ensure s!"{name}: fails at the other site" (!other w)

/-- The honest signature routes to the FORS arm and the extractor honours `target` there: at each of
the two FORS trees it returns the `F`-preimage of that tree's honest leaf image, and the value it
returns is the honest secret at the hand-computed global leaf index — read through the hand-written
address table rather than through `forsSigLeafIndex`.

The same signature is then offered against `msgA'`, a different message with the same exclusive-or
fold.  Verification, the digest and the extracted witness all agree, which pins that the dispatch
reads the message only through `H_msg`. -/
def checkHonestForgery : IO Unit := do
  for target in [tree0, tree1] do
    checkForsArm s!"A tree {target.val}" msgA sigA target
      s!"fors.fPreimage tree={target.val}" holdsA holdsB
    match findWitness skSeed honestPk msgA sigA target with
    | some (.fors (.fPreimage i value)) => do
        ensure s!"A tree {target.val}: the extracted tree is the target" (i == target)
        ensure s!"A tree {target.val}: the value is the honest secret at the global leaf"
          (value == honestForsSecret partsA.forsAdrs (globalLeafAt partsA.md.toList target.val))
    | _ => throw (IO.userError s!"Scheme witness check failed: A tree {target.val}: wrong shape")
  ensure "the colliding message gives the same digest"
    (schemeParts toy toyPrimitives msgA sigA honestPk ==
      schemeParts toy toyPrimitives msgA' sigA honestPk)
  ensure "the colliding message verifies too"
    (GeneralScheme.verifyInternal toy toyPrimitives msgA' sigA honestPk)
  ensure "the colliding message extracts the same witness"
    ((findWitness skSeed honestPk msgA' sigA tree0).map describe ==
      (findWitness skSeed honestPk msgA sigA tree0).map describe)

/-- A signature whose FORS half moves one tree's leaf image without moving the recovered public key
still routes to the FORS arm, and the extractor returns the `H`-collision that move creates rather
than the honest signature's `F`-preimage.  `target` is not honoured on that branch, which is what
this canary pins by asking for the same witness at both targets. -/
def checkCollapsedForgery : IO Unit := do
  for target in [tree0, tree1] do
    checkForsArm s!"D tree {target.val}" msgB sigD target "fors.hCollision tree=0 height=1"
      holdsB holdsA

/-! ## The hypertree arm -/

/-- One hypertree-arm canary, for the case where the extractor returns a WOTS+ `F`-preimage.

The signature verifies, its recovered FORS public key differs from the honest one — which is what
routes it here — and the extractor reports the layer and the WOTS+ chain and step named.  The
returned witness is then re-evaluated against three deliberately wrong arguments, one at a time:
the other layer's tree address, the other layer's leaf, and — this is the naive identification the
canary exists to defeat — the message the forged signature actually carries at this layer, which is
the value a reader would reach for if the honest partner were read off the signature instead of
computed from `sk`.  All three are required to fail, as is moving to the other layer as a whole.

Moving the honest running message to the *other layer's* honest one is a fourth re-evaluation, and
at this fixture it is inert, so it is asserted to hold rather than to fail.  The reason is exact and
is asserted with it: `WotsWitness.Valid`'s `fPreimage` branch reads the honest message only through
`chainStepsCore` at the extracted chain — the honest revealed value there is the honest chain
advanced by exactly that many steps — and the two layers' honest running messages have the same
step count at that chain.  The naive message does not: its step count differs, which is why that
move discriminates and this one does not. -/
def checkHypertreeArm (name : String) (sig : GeneralScheme.SignatureCore toy toyPrimitives.core)
    (layer : ℕ) (chainIdx step : ℕ) (naive : toyPrimitives.Y) : IO Unit := do
  let parts := schemeParts toy toyPrimitives msgB sig honestPk
  ensure s!"{name}: verifies" (GeneralScheme.verifyInternal toy toyPrimitives msgB sig honestPk)
  ensure s!"{name}: recovers a FORS public key that is not the honest one"
    (forsPkFromSig toyPrimitives sig.fors parts.md.toList pkSeed parts.forsAdrs !=
      forsPkGen toyPrimitives skSeed pkSeed parts.forsAdrs)
  match findWitness skSeed honestPk msgB sig tree0 with
  | none => throw (IO.userError s!"Scheme witness check failed: {name}: no witness")
  | some (.fors _) =>
      throw (IO.userError s!"Scheme witness check failed: {name}: routed to the FORS arm")
  | some (.hypertree w) => do
      ensure s!"{name}: reports layer {layer}" (w.layer.val == layer)
      ensure s!"{name}: reports the WOTS+ F-preimage at chain {chainIdx} step {step}"
        (describeXmss w.witness == s!"wots.fPreimage chain={chainIdx} step={step}")
      let other := 1 - layer
      ensure s!"{name}: holds at its own layer"
        (xmssWitnessHolds (posOfB layer).toAdrs (posOfB layer).leaf.val (honestMsgB layer)
          w.witness)
      ensure s!"{name}: fails at the other layer's tree address"
        (!xmssWitnessHolds (posOfB other).toAdrs (posOfB layer).leaf.val (honestMsgB layer)
          w.witness)
      ensure s!"{name}: fails at the other layer's leaf"
        (!xmssWitnessHolds (posOfB layer).toAdrs (posOfB other).leaf.val (honestMsgB layer)
          w.witness)
      ensure s!"{name}: fails at the message the signature carries there"
        (!xmssWitnessHolds (posOfB layer).toAdrs (posOfB layer).leaf.val naive w.witness)
      ensure s!"{name}: fails at the other layer as a whole"
        (!xmssWitnessHolds (posOfB other).toAdrs (posOfB other).leaf.val (honestMsgB other)
          w.witness)
      ensure s!"{name}: the other layer's honest message is inert at chain {chainIdx}, and holds"
        (chainStepsCore toyPrimitives.core (honestMsgB other) chainIdx ==
            chainStepsCore toyPrimitives.core (honestMsgB layer) chainIdx &&
          xmssWitnessHolds (posOfB layer).toAdrs (posOfB layer).leaf.val (honestMsgB other)
            w.witness)
      ensure s!"{name}: the naive message is not inert at chain {chainIdx}"
        (chainStepsCore toyPrimitives.core naive chainIdx !=
          chainStepsCore toyPrimitives.core (honestMsgB layer) chainIdx)
      ensure s!"{name}: the other site's honest message discriminates exactly when it must"
        (hypertreeWitnessHolds posOfB honestMsgA w ==
          (chainStepsCore toyPrimitives.core (honestMsgA layer) chainIdx ==
            chainStepsCore toyPrimitives.core (honestMsgB layer) chainIdx))
      ensure s!"{name}: holds at its own site and fails at the other"
        (holdsB (.hypertree w) && !holdsA (.hypertree w))

/-- The hypertree-arm canary for the case where the extractor returns an XMSS `H`-collision.  That
branch of `XmssWitness.Valid` never reads the honest running message, so the two message
re-evaluations of `checkHypertreeArm` cannot discriminate and are asserted to hold instead; what
discriminates is the tree address and, because the two layers' leaves give different node indices
at the extracted height, the leaf. -/
def checkHypertreeCollision (name : String)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) (layer height : ℕ) : IO Unit := do
  let parts := schemeParts toy toyPrimitives msgB sig honestPk
  ensure s!"{name}: verifies" (GeneralScheme.verifyInternal toy toyPrimitives msgB sig honestPk)
  ensure s!"{name}: recovers a FORS public key that is not the honest one"
    (forsPkFromSig toyPrimitives sig.fors parts.md.toList pkSeed parts.forsAdrs !=
      forsPkGen toyPrimitives skSeed pkSeed parts.forsAdrs)
  match findWitness skSeed honestPk msgB sig tree0 with
  | none => throw (IO.userError s!"Scheme witness check failed: {name}: no witness")
  | some (.fors _) =>
      throw (IO.userError s!"Scheme witness check failed: {name}: routed to the FORS arm")
  | some (.hypertree w) => do
      ensure s!"{name}: reports layer {layer}" (w.layer.val == layer)
      ensure s!"{name}: reports the XMSS collision at height {height}"
        (describeXmss w.witness == s!"xmss.hCollision height={height}")
      let other := 1 - layer
      ensure s!"{name}: holds at its own layer"
        (xmssWitnessHolds (posOfB layer).toAdrs (posOfB layer).leaf.val (honestMsgB layer)
          w.witness)
      ensure s!"{name}: fails at the other layer's tree address"
        (!xmssWitnessHolds (posOfB other).toAdrs (posOfB layer).leaf.val (honestMsgB layer)
          w.witness)
      ensure s!"{name}: the two layers' leaves give different node indices at height {height}"
        ((posOfB layer).leaf.val / 2 ^ height != (posOfB other).leaf.val / 2 ^ height)
      ensure s!"{name}: fails at the other layer's leaf"
        (!xmssWitnessHolds (posOfB layer).toAdrs (posOfB other).leaf.val (honestMsgB layer)
          w.witness)
      ensure s!"{name}: the honest running message is inert, and holds"
        (xmssWitnessHolds (posOfB layer).toAdrs (posOfB layer).leaf.val (honestMsgB other)
            w.witness &&
          xmssWitnessHolds (posOfB layer).toAdrs (posOfB layer).leaf.val divergedRoot w.witness)
      ensure s!"{name}: fails at the other layer as a whole"
        (!xmssWitnessHolds (posOfB other).toAdrs (posOfB other).leaf.val (honestMsgB other)
          w.witness)
      ensure s!"{name}: holds at its own site and fails at the other"
        (holdsB (.hypertree w) && !holdsA (.hypertree w))

/-- A signature that does not verify and whose walk matches at no layer: the extractor returns
nothing, at both targets.  This is the case a total dispatch would have to invent a witness for. -/
def checkNoWitness : IO Unit := do
  ensure "N: does not verify"
    (!GeneralScheme.verifyInternal toy toyPrimitives msgB sigN honestPk)
  for target in [tree0, tree1] do
    ensure s!"N: no witness at target {target.val}"
      ((findWitness skSeed honestPk msgB sigN target).isNone)

/-! ## Arm selection, and what the composite predicate can and cannot see -/

/-- Two signatures at one digest.  `sigD` and `sigB` share a randomizer and a message, so they share
a digest, an instance address, a FORS message, a layer-zero position and every honest value; they
differ only in their FORS halves.  One routes to the FORS arm and the other to the hypertree arm, so
the arm is decided by the FORS public-key comparison and by nothing else.

The second half of this canary pins what `Witness.Valid` does *not* see.  Offered against `sigB`,
the FORS witness extracted from `sigD` still holds — and it must, because `Witness.Valid` reads the
signature only through the digest its randomizer produces, and the two digests are equal.  The arm
selection is a property of `findWitness`, not of the predicate, and the pin above is what checks it;
asserting a rejection here would be asserting something false. -/
def checkArmSelection : IO Unit := do
  ensure "the two site-B signatures share a digest"
    (schemeParts toy toyPrimitives msgB sigD honestPk ==
      schemeParts toy toyPrimitives msgB sigB honestPk)
  ensure "they differ only in the FORS half"
    (sigD.randomness == sigB.randomness && forsBytes sigD.fors != forsBytes sigB.fors)
  match findWitness skSeed honestPk msgB sigD tree0,
      findWitness skSeed honestPk msgB sigB tree0 with
  | some (.fors wD), some (.hypertree wB) => do
      ensure "the FORS witness of one holds against the other, at the shared digest"
        (holdsB (.fors wD))
      ensure "and so does the hypertree witness" (holdsB (.hypertree wB))
      ensure "each fails at the other site" (!holdsA (.fors wD) && !holdsA (.hypertree wB))
  | _, _ => throw (IO.userError "Scheme witness check failed: arm selection: wrong arms")

/-- The honest layer-zero partner is the honest FORS public key at the digest's *position*, and not
anything read off a signature: it does not depend on the FORS message at all.  Two digest splits at
one position with different FORS messages therefore share an instance address and an honest FORS
public key while opening different FORS leaves, and a witness at one is not a witness at the other.

That independence is what makes the hypertree arm's honest starting message well defined for a
message the signer never signed, and it is the step the module docstring calls out. -/
def checkHonestPartner : IO Unit := do
  let left : DigestParts toyParams :=
    { md := Vector.replicate toyParams.digestBytes 0x00, idxTree := ⟨2, by decide⟩,
      idxLeaf := ⟨0, by decide⟩ }
  let right : DigestParts toyParams :=
    { md := Vector.replicate toyParams.digestBytes 0xC0, idxTree := ⟨2, by decide⟩,
      idxLeaf := ⟨0, by decide⟩ }
  ensure "the two splits differ in the FORS message only" (left.md != right.md)
  ensure "they share the instance address" (left.forsAdrs == right.forsAdrs)
  ensure "and the honest FORS public key"
    (forsPkGen toyPrimitives skSeed pkSeed left.forsAdrs ==
      forsPkGen toyPrimitives skSeed pkSeed right.forsAdrs)
  ensure "while opening different FORS leaves"
    (globalLeafAt left.md.toList 0 != globalLeafAt right.md.toList 0)
  ensure "the honest FORS public keys of the two sites differ"
    (forsPkGen toyPrimitives skSeed pkSeed partsA.forsAdrs !=
      forsPkGen toyPrimitives skSeed pkSeed partsB.forsAdrs)

/-! ## Fabricated witnesses -/

/-- A witness the extractor did not return, offered at a site.  A `Fin toyParams.d` label makes an
out-of-range layer a build error rather than a rejected run, so no fabrication below carries one. -/
def checkFabricated : IO Unit := do
  match findWitness skSeed honestPk msgA sigA tree0, findWitness skSeed honestPk msgB sigD tree0,
      findWitness skSeed honestPk msgB sigB tree0, findWitness skSeed honestPk msgB sigC tree0 with
  | some (.fors wA), some (.fors wD), some (.hypertree wB), some (.hypertree wC) => do
      let accepted : List (String × Bool) :=
        [("A's FORS witness at site A", holdsA (.fors wA)),
         ("D's FORS witness at site B", holdsB (.fors wD)),
         ("B's hypertree witness at site B", holdsB (.hypertree wB)),
         ("C's hypertree witness at site B", holdsB (.hypertree wC))]
      let rejected : List (String × Bool) :=
        [("A's FORS witness at site B", holdsB (.fors wA)),
         ("D's FORS witness at site A", holdsA (.fors wD)),
         ("B's hypertree witness at site A", holdsA (.hypertree wB)),
         ("C's hypertree witness at site A", holdsA (.hypertree wC)),
         ("B's hypertree witness relabelled to layer one",
            holdsB (.hypertree ⟨⟨1, by decide⟩, wB.witness⟩)),
         ("C's hypertree witness relabelled to layer zero",
            holdsB (.hypertree ⟨⟨0, by decide⟩, wC.witness⟩)),
         ("a height-zero FORS collision",
            holdsB (.fors (.hCollision tree0 0 (node 0, node 0)))),
         ("a FORS collision above the tree height",
            holdsB (.fors (.hCollision tree0 2 (node 0, node 0)))),
         ("an F-preimage of the wrong value",
            holdsB (.fors (.fPreimage tree0 (node (byteOf (honestForsSecret partsB.forsAdrs
              (globalLeafAt partsB.md.toList 0)) + 2))))),
         ("a T_k second preimage of the honest root vector",
            holdsB (.fors (.tlCollision (honestForsRoots partsB.forsAdrs))))]
      for entry in accepted do
        ensure s!"fabricated: {entry.1} is accepted" entry.2
      for entry in rejected do
        ensure s!"fabricated: {entry.1} is rejected" (!entry.2)
      ensure "the tally is four accepted and ten rejected"
        (accepted.length == 4 && rejected.length == 10)
  | _, _, _, _ => throw (IO.userError "Scheme witness check failed: fabricated: wrong arms")

/-! ## Statement pins

The `example`s below pin the library statements at this bundle, so a change to any of them that the
executable cannot see is still a build error here. -/

/-- The published key generation returns. -/
example : (GeneralScheme.keygenInternal toy toyPrimitives skSeed skPrf pkSeed).1 =
    ⟨pkSeed, GeneralHypertree.root toy toyPrimitives skSeed pkSeed⟩ :=
  GeneralScheme.keygenInternal_fst toy toyPrimitives skSeed skPrf pkSeed

/-- Verification is the general hypertree verifier at the digest the signature's own randomizer
produces. -/
example (msg : List Byte) (sig : GeneralScheme.SignatureCore toy toyPrimitives.core)
    (pk : PublicKeyCore toyPrimitives.core) :
    GeneralScheme.verifyInternal toy toyPrimitives msg sig pk =
      (let parts := splitDigest toyParams
         (toyPrimitives.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg)
       GeneralHypertree.verify toy toyPrimitives
         (forsPkFromSig toyPrimitives sig.fors parts.md.toList pk.pkSeed parts.forsAdrs)
         sig.hypertree pk.pkSeed parts pk.pkRoot) :=
  GeneralScheme.verifyInternal_eq toy toyPrimitives msg sig pk

/-- And it is the decision of whether the recovered hypertree root is the published one. -/
example (msg : List Byte) (sig : GeneralScheme.SignatureCore toy toyPrimitives.core)
    (pk : PublicKeyCore toyPrimitives.core) :
    GeneralScheme.verifyInternal toy toyPrimitives msg sig pk =
      (let parts := splitDigest toyParams
         (toyPrimitives.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg)
       decide (GeneralHypertree.pkFromSig toy toyPrimitives
         (forsPkFromSig toyPrimitives sig.fors parts.md.toList pk.pkSeed parts.forsAdrs)
         sig.hypertree pk.pkSeed parts = pk.pkRoot)) :=
  GeneralScheme.verifyInternal_eq_decide toy toyPrimitives msg sig pk

/-- The digest split a signature produces against a public key. -/
example (msg : List Byte) (sig : GeneralScheme.SignatureCore toy toyPrimitives.core)
    (pk : PublicKeyCore toyPrimitives.core) :
    schemeParts toy toyPrimitives msg sig pk =
      splitDigest toyParams (toyPrimitives.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg) :=
  schemeParts_eq toy toyPrimitives msg sig pk

/-- **The dispatch.**  A verifying signature either recovers the honest FORS public key at the
position its own digest names, or supplies a hypertree signature reaching the published root from
the value it did recover.  Neither the secret seed nor the public key is constrained. -/
example (sk : toyPrimitives.SkSeed) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core)
    (pk : PublicKeyCore toyPrimitives.core)
    (hverify : GeneralScheme.verifyInternal toy toyPrimitives msg sig pk = true) :
    (forsPkFromSig toyPrimitives sig.fors (schemeParts toy toyPrimitives msg sig pk).md.toList
        pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs =
      forsPkGen toyPrimitives sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs) ∨
    (forsPkFromSig toyPrimitives sig.fors (schemeParts toy toyPrimitives msg sig pk).md.toList
        pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs ≠
      forsPkGen toyPrimitives sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs ∧
     GeneralHypertree.pkFromSig toy toyPrimitives
        (forsPkFromSig toyPrimitives sig.fors (schemeParts toy toyPrimitives msg sig pk).md.toList
          pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs)
        sig.hypertree pk.pkSeed (schemeParts toy toyPrimitives msg sig pk) = pk.pkRoot) :=
  verifyInternal_cases (vp := toy) (prims := toyPrimitives) sk msg sig pk hverify

/-- The FORS arm fires exactly on the public-key match. -/
example (sk : toyPrimitives.SkSeed) (pk : PublicKeyCore toyPrimitives.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) (target : Fin toy.params.k)
    (hpk : forsPkFromSig toyPrimitives sig.fors (schemeParts toy toyPrimitives msg sig pk).md.toList
        pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs =
      forsPkGen toyPrimitives sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs) :
    findWitness sk pk msg sig target =
      some (.fors (findForsWitness toyPrimitives sig.fors
        (schemeParts toy toyPrimitives msg sig pk).md.toList sk pk.pkSeed
        (schemeParts toy toyPrimitives msg sig pk).forsAdrs target)) :=
  findWitness_eq_fors_of_pk (vp := toy) (prims := toyPrimitives) sk pk msg sig target hpk

/-- And the hypertree arm exactly on the mismatch. -/
example (sk : toyPrimitives.SkSeed) (pk : PublicKeyCore toyPrimitives.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) (target : Fin toy.params.k)
    (hpk : forsPkFromSig toyPrimitives sig.fors (schemeParts toy toyPrimitives msg sig pk).md.toList
        pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs ≠
      forsPkGen toyPrimitives sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs) :
    findWitness sk pk msg sig target =
      (findHypertreeWitness toy toyPrimitives sk pk.pkSeed
        (LayerPosition.initial toy (schemeParts toy toyPrimitives msg sig pk)) toy.params.d
        (by simp)
        (forsPkFromSig toyPrimitives sig.fors (schemeParts toy toyPrimitives msg sig pk).md.toList
          pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs)
        (forsPkGen toyPrimitives sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs)
        sig.hypertree).map .hypertree :=
  findWitness_eq_hypertree_of_ne (vp := toy) (prims := toyPrimitives) sk pk msg sig target hpk

/-- Extractor soundness at this bundle, with no verification hypothesis and an arbitrary public
key. -/
example (sk : toyPrimitives.SkSeed) (pk : PublicKeyCore toyPrimitives.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) (target : Fin toyParams.k)
    {w : Witness toy toyPrimitives} (hw : findWitness sk pk msg sig target = some w) :
    w.Valid sk pk msg sig :=
  findWitness_sound (vp := toy) (prims := toyPrimitives) sk pk msg sig target hw

/-- Extractor completeness at this bundle, with the byte laws discharged by the fixture. -/
example (sk : toyPrimitives.SkSeed) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) (target : Fin toyParams.k)
    (hverify : GeneralScheme.verifyInternal toy toyPrimitives msg sig
      ⟨pkSeed, GeneralHypertree.root toy toyPrimitives sk pkSeed⟩ = true) :
    (findWitness sk ⟨pkSeed, GeneralHypertree.root toy toyPrimitives sk pkSeed⟩ msg sig
      target).isSome :=
  findWitness_isSome (vp := toy) (prims := toyPrimitives) toyByteLaws sk pkSeed msg sig target
    hverify

/-- The FORS arm's unfolding equation, at the digest-derived address and FORS message. -/
example (sk : toyPrimitives.SkSeed) (pk : PublicKeyCore toyPrimitives.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core)
    (w : ForsWitness toyParams toyPrimitives) :
    (Witness.fors w).Valid sk pk msg sig ↔
      w.Valid sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk).forsAdrs
        (schemeParts toy toyPrimitives msg sig pk).md.toList :=
  Witness.valid_fors (vp := toy) (prims := toyPrimitives) sk pk msg sig w

/-- The hypertree arm's, at the digest-derived layer-zero position and the honest FORS public key
there. -/
example (sk : toyPrimitives.SkSeed) (pk : PublicKeyCore toyPrimitives.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core)
    (w : HypertreeWitness toy toyPrimitives toy.params.d) :
    (Witness.hypertree w).Valid sk pk msg sig ↔
      w.Valid sk pk.pkSeed (LayerPosition.initial toy (schemeParts toy toyPrimitives msg sig pk))
        (forsPkGen toyPrimitives sk pk.pkSeed
          (schemeParts toy toyPrimitives msg sig pk).forsAdrs) toy.params.d (by simp) :=
  Witness.valid_hypertree (vp := toy) (prims := toyPrimitives) sk pk msg sig w

/-! ### Ledger pins

The toy profile is inside the approved address bounds, so it serves the ledger and encoded-tweak
pins as well as the extraction canaries; no second parameter record is introduced. -/

theorem toyApprovedAddressBounds : ApprovedAddressBounds toy.params :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    by decide, by decide⟩

/-- The FORS leaf address the `fPreimage` arm names at a digest is a listed `forsF` target. -/
example (parts : DigestParts toy.params) (md : List Byte) (i : Fin toy.params.k) :
    forsNodeAdrs parts.forsAdrs 0 (forsSigLeafIndex toy.params md i.val) ∈ forsLeafAddresses toy :=
  mem_forsLeafAddresses_of_parts (vp := toy) parts md i

/-- The FORS internal-node address the `hCollision` arm names is a listed `forsH` target. -/
example (parts : DigestParts toy.params) (md : List Byte) (i : Fin toy.params.k) {z : ℕ}
    (hz : 0 < z) (hza : z ≤ toy.params.a) :
    forsNodeAdrs parts.forsAdrs z (forsSigLeafIndex toy.params md i.val / 2 ^ z) ∈
      forsTreeAddresses toy :=
  mem_forsTreeAddresses_of_parts (vp := toy) parts md i hz hza

/-- The FORS root-compression address the `tlCollision` arm names is a listed `forsTl` target. -/
example (parts : DigestParts toy.params) : forsPkAdrs parts.forsAdrs ∈ forsRootAddresses toy :=
  mem_forsRootAddresses_of_parts (vp := toy) parts

/-- The hypertree arm needs no bridge: its addresses are named at a `LayerPosition`, so slice 1's
membership lemma applies to the advanced position unchanged. -/
example (parts : DigestParts toy.params) (j : ℕ)
    (hj : (LayerPosition.initial toy parts).layer.val + j < toy.params.d) {z : ℕ} (hz : 0 < z)
    (hzh : z ≤ toy.params.hp) :
    xmssNodeAdrs ((LayerPosition.initial toy parts).advance j hj).toAdrs z
        (((LayerPosition.initial toy parts).advance j hj).leaf.val / 2 ^ z) ∈
      xmssNodeAddresses toy :=
  mem_xmssNodeAddresses_of_leaf ((LayerPosition.initial toy parts).advance j hj) hz hzh

/-- And so does the WOTS+ public-key address, through `wotsLeafAdrs_eq_wotsInstanceAdrs`. -/
example (parts : DigestParts toy.params) (j : ℕ)
    (hj : (LayerPosition.initial toy parts).layer.val + j < toy.params.d) :
    wotsPkAdrs (wotsLeafAdrs ((LayerPosition.initial toy parts).advance j hj).toAdrs
        ((LayerPosition.initial toy parts).advance j hj).leaf.val) ∈ wotsPkAddresses toy := by
  rw [wotsLeafAdrs_eq_wotsInstanceAdrs]
  exact mem_wotsPkAddresses toy _

/-- Under the SHA-2 encoder, two FORS leaf targets named by two digests carry equal encoded tweaks
only when the two digests agree on both indices and the two FORS coordinates agree. -/
example {parts parts' : DigestParts toy.params} {md md' : List Byte} {i i' : Fin toy.params.k}
    (hkey : (sha2Primitives toy.params).adrsToKey
        (forsNodeAdrs parts.forsAdrs 0 (forsSigLeafIndex toy.params md i.val)) =
      (sha2Primitives toy.params).adrsToKey
        (forsNodeAdrs parts'.forsAdrs 0 (forsSigLeafIndex toy.params md' i'.val))) :
    parts.idxTree = parts'.idxTree ∧ parts.idxLeaf = parts'.idxLeaf ∧ i = i' ∧
      forsIdx toy.params md i.val = forsIdx toy.params md' i'.val :=
  forsLeafAdrsKey_injective_of_parts
    (sha2EncodedTargetLedgerConditions toy toyApprovedAddressBounds) hkey

/-- The same for FORS internal nodes. -/
example {parts parts' : DigestParts toy.params} {md md' : List Byte} {i i' : Fin toy.params.k}
    {z z' : ℕ} (hz : 0 < z) (hza : z ≤ toy.params.a) (hz' : 0 < z') (hza' : z' ≤ toy.params.a)
    (hkey : (sha2Primitives toy.params).adrsToKey
        (forsNodeAdrs parts.forsAdrs z (forsSigLeafIndex toy.params md i.val / 2 ^ z)) =
      (sha2Primitives toy.params).adrsToKey
        (forsNodeAdrs parts'.forsAdrs z' (forsSigLeafIndex toy.params md' i'.val / 2 ^ z'))) :
    parts.idxTree = parts'.idxTree ∧ parts.idxLeaf = parts'.idxLeaf ∧ i = i' ∧ z = z' ∧
      forsIdx toy.params md i.val / 2 ^ z = forsIdx toy.params md' i'.val / 2 ^ z' :=
  forsTreeAdrsKey_injective_of_parts
    (sha2EncodedTargetLedgerConditions toy toyApprovedAddressBounds) hz hza hz' hza' hkey

/-- And for FORS root compressions, under the SHAKE encoder. -/
example {parts parts' : DigestParts toy.params}
    (hkey : (shakePrimitives toy.params).adrsToKey (forsPkAdrs parts.forsAdrs) =
      (shakePrimitives toy.params).adrsToKey (forsPkAdrs parts'.forsAdrs)) :
    parts.idxTree = parts'.idxTree ∧ parts.idxLeaf = parts'.idxLeaf :=
  forsRootAdrsKey_injective_of_parts
    (shakeEncodedTargetLedgerConditions toy toyApprovedAddressBounds.toCanonicalAddressBounds) hkey

/-! ### Game-shape pins

`Witness.Valid` is stated in the construction's own vocabulary.  These seven `example`s compose its
two unfolding equations with the lane's seven `_eval` bridges — one per leaf branch — so a consumer
holding a composite witness reaches each canonical game's `eval` at the encoded tweak in one step.
No bridge is restated in the library; these pin that none needs to be. -/

-- Exposed: the two abbreviations below have to unfold for the hypertree-arm pins, whose hypothesis
-- comes back from `HypertreeWitness.valid_iff` spelled with `advance` and `honestLayerMsg` rather
-- than with these names.  Nothing outside this executable consumes them.
/-- The position a hypertree-arm label names on the walk from a digest's layer-zero position. -/
@[expose] def armPos (parts : DigestParts toy.params) (layer : Fin toy.params.d) :
    LayerPosition toy :=
  (LayerPosition.initial toy parts).advance layer.val (by simp)

/-- The honest running message there, under a secret seed and a public seed. -/
@[expose] def armMsg (sk : toyPrimitives.SkSeed) (pks : toyPrimitives.PkSeed)
    (parts : DigestParts toy.params) (layer : Fin toy.params.d) : toyPrimitives.Y :=
  honestLayerMsg toy toyPrimitives sk pks (LayerPosition.initial toy parts)
    (forsPkGen toyPrimitives sk pks parts.forsAdrs) layer.val (by simp)

variable (sk : toyPrimitives.SkSeed) (pk : PublicKeyCore toyPrimitives.core) (msg : List Byte)
  (sig : GeneralScheme.SignatureCore toy toyPrimitives.core)

/-- The FORS arm's `T_k` branch, in `forsTlTcrCProblem`'s vocabulary. -/
example (recovered : Vector toyPrimitives.Y toy.params.k)
    (h : (Witness.fors (.tlCollision recovered)).Valid sk pk msg sig) :
    recovered ≠ forsHonestRoots toyPrimitives sk pk.pkSeed
        (schemeParts toy toyPrimitives msg sig pk).forsAdrs ∧
      (forsTlTcrCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            (forsPkAdrs (schemeParts toy toyPrimitives msg sig pk).forsAdrs)) recovered =
        (forsTlTcrCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            (forsPkAdrs (schemeParts toy toyPrimitives msg sig pk).forsAdrs))
          (forsHonestRoots toyPrimitives sk pk.pkSeed
            (schemeParts toy toyPrimitives msg sig pk).forsAdrs) :=
  forsWitness_valid_tlCollision_eval toyPrimitives sk pk.pkSeed _ _ recovered
    ((Witness.valid_fors (vp := toy) (prims := toyPrimitives) sk pk msg sig _).mp h)

/-- The FORS arm's `H` branch, in `forsHTcrCProblem`'s vocabulary. -/
example (i : Fin toy.params.k) (z : ℕ) (c : toyPrimitives.Y × toyPrimitives.Y)
    (h : (Witness.fors (.hCollision i z c)).Valid sk pk msg sig) :
    0 < z ∧ z ≤ toy.params.a ∧
      forsHonestChildren toyPrimitives sk pk.pkSeed
          (schemeParts toy toyPrimitives msg sig pk).forsAdrs z
          (forsSigLeafIndex toy.params (schemeParts toy toyPrimitives msg sig pk).md.toList i.val /
            2 ^ z) ≠ c ∧
      (forsHTcrCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            (forsNodeAdrs (schemeParts toy toyPrimitives msg sig pk).forsAdrs z
              (forsSigLeafIndex toy.params
                (schemeParts toy toyPrimitives msg sig pk).md.toList i.val / 2 ^ z)))
          (forsHonestChildren toyPrimitives sk pk.pkSeed
            (schemeParts toy toyPrimitives msg sig pk).forsAdrs z
            (forsSigLeafIndex toy.params
              (schemeParts toy toyPrimitives msg sig pk).md.toList i.val / 2 ^ z)) =
        (forsHTcrCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            (forsNodeAdrs (schemeParts toy toyPrimitives msg sig pk).forsAdrs z
              (forsSigLeafIndex toy.params
                (schemeParts toy toyPrimitives msg sig pk).md.toList i.val / 2 ^ z))) c :=
  forsWitness_valid_hCollision_eval toyPrimitives sk pk.pkSeed _ _ i z c
    ((Witness.valid_fors (vp := toy) (prims := toyPrimitives) sk pk msg sig _).mp h)

/-- The FORS arm's `F` branch, in `forsFOpenPreProblem`'s vocabulary — an open-preimage condition,
with no distinctness conjunct. -/
example (i : Fin toy.params.k) (value : toyPrimitives.Y)
    (h : (Witness.fors (.fPreimage i value)).Valid sk pk msg sig) :
    (forsFOpenPreProblem toyPrimitives).th.eval pk.pkSeed
        (toyPrimitives.adrsToKey
          (forsNodeAdrs (schemeParts toy toyPrimitives msg sig pk).forsAdrs 0
            (forsSigLeafIndex toy.params
              (schemeParts toy toyPrimitives msg sig pk).md.toList i.val))) value =
      (forsFOpenPreProblem toyPrimitives).th.eval pk.pkSeed
        (toyPrimitives.adrsToKey
          (forsNodeAdrs (schemeParts toy toyPrimitives msg sig pk).forsAdrs 0
            (forsSigLeafIndex toy.params
              (schemeParts toy toyPrimitives msg sig pk).md.toList i.val)))
        (forsSkGenCore toyPrimitives.core sk pk.pkSeed
          (schemeParts toy toyPrimitives msg sig pk).forsAdrs
          (forsSigLeafIndex toy.params
            (schemeParts toy toyPrimitives msg sig pk).md.toList i.val)) :=
  forsWitness_valid_fPreimage_eval toyPrimitives sk pk.pkSeed _ _ i value
    ((Witness.valid_fors (vp := toy) (prims := toyPrimitives) sk pk msg sig _).mp h)

/-- The hypertree arm's XMSS `H` branch, in `xmssHTcrCProblem`'s vocabulary, at the position the
label names. -/
example (layer : Fin toy.params.d) (z : ℕ) (c : toyPrimitives.Y × toyPrimitives.Y)
    (h : (Witness.hypertree ⟨layer, .hCollision z c⟩).Valid sk pk msg sig) :
    0 < z ∧ z ≤ toy.params.hp ∧
      xmssHonestChildren toyPrimitives sk pk.pkSeed
          (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs z
          ((armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val / 2 ^ z) ≠ c ∧
      (xmssHTcrCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            (xmssNodeAdrs (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs z
              ((armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val / 2 ^ z)))
          (xmssHonestChildren toyPrimitives sk pk.pkSeed
            (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs z
            ((armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val / 2 ^ z)) =
        (xmssHTcrCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            (xmssNodeAdrs (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs z
              ((armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val / 2 ^ z))) c :=
  xmssWitness_valid_hCollision_eval toyPrimitives sk pk.pkSeed _ _ _ z c
    ((HypertreeWitness.valid_iff sk pk.pkSeed
        (LayerPosition.initial toy (schemeParts toy toyPrimitives msg sig pk)) _ toy.params.d
        (by simp) _).mp
      ((Witness.valid_hypertree (vp := toy) (prims := toyPrimitives) sk pk msg sig _).mp h))

/-- The hypertree arm's WOTS+ `T_len` branch, in `wotsTlTcrCProblem`'s vocabulary. -/
example (layer : Fin toy.params.d) (recovered : Vector toyPrimitives.Y toy.params.len)
    (h : (Witness.hypertree ⟨layer, .wots (.tlCollision recovered)⟩).Valid sk pk msg sig) :
    recovered ≠ wotsPkGenTops toyPrimitives sk pk.pkSeed
        (wotsLeafAdrs (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
          (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val) ∧
      (wotsTlTcrCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            (wotsPkAdrs (wotsLeafAdrs
              (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
              (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val))) recovered =
        (wotsTlTcrCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            (wotsPkAdrs (wotsLeafAdrs
              (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
              (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val)))
          (wotsPkGenTops toyPrimitives sk pk.pkSeed
            (wotsLeafAdrs (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
              (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val)) :=
  wotsWitness_valid_tlCollision_eval toyPrimitives pk.pkSeed _ _ recovered
    ((XmssWitness.valid_wots sk pk.pkSeed _ _ _ _).mp
      ((HypertreeWitness.valid_iff sk pk.pkSeed
        (LayerPosition.initial toy (schemeParts toy toyPrimitives msg sig pk)) _ toy.params.d
        (by simp) _).mp
        ((Witness.valid_hypertree (vp := toy) (prims := toyPrimitives) sk pk msg sig _).mp h)))

/-- The hypertree arm's WOTS+ `F`-preimage branch, in `wotsFPreCProblem`'s vocabulary. -/
example (layer : Fin toy.params.d) (i : Fin toy.params.len) (step : ℕ) (value : toyPrimitives.Y)
    (h : (Witness.hypertree ⟨layer, .wots (.fPreimage i step value)⟩).Valid sk pk msg sig) :
    step < toy.params.w - 1 ∧
      step + 1 = chainStepsCore toyPrimitives.core
        (armMsg sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk) layer) i.val ∧
      (wotsFPreCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            ((wotsChainAdrs (wotsLeafAdrs
                (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
                (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val)
              i.val).setHashAddress step)) value =
        (wotsSign toyPrimitives
          (armMsg sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk) layer) sk pk.pkSeed
          (wotsLeafAdrs (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
            (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val))[i.val] :=
  wotsWitness_valid_fPreimage_eval toyPrimitives pk.pkSeed _ _ _ i step value
    ((XmssWitness.valid_wots sk pk.pkSeed _ _ _ _).mp
      ((HypertreeWitness.valid_iff sk pk.pkSeed
        (LayerPosition.initial toy (schemeParts toy toyPrimitives msg sig pk)) _ toy.params.d
        (by simp) _).mp
        ((Witness.valid_hypertree (vp := toy) (prims := toyPrimitives) sk pk msg sig _).mp h)))

/-- The hypertree arm's WOTS+ `F`-collision branch, in `wotsFTcrCProblem`'s vocabulary. -/
example (layer : Fin toy.params.d) (i : Fin toy.params.len) (step : ℕ) (value : toyPrimitives.Y)
    (h : (Witness.hypertree ⟨layer, .wots (.fCollision i step value)⟩).Valid sk pk msg sig) :
    step < toy.params.w - 1 ∧
      chainStepsCore toyPrimitives.core
        (armMsg sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk) layer) i.val ≤ step ∧
      value ≠ chain toyPrimitives pk.pkSeed
          (wotsChainAdrs (wotsLeafAdrs
            (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
            (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val) i.val)
          (wotsSign toyPrimitives
            (armMsg sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk) layer) sk pk.pkSeed
            (wotsLeafAdrs (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
              (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val))[i.val]
          (chainStepsCore toyPrimitives.core
            (armMsg sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk) layer) i.val)
          (step - chainStepsCore toyPrimitives.core
            (armMsg sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk) layer) i.val) ∧
      (wotsFTcrCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            ((wotsChainAdrs (wotsLeafAdrs
                (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
                (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val)
              i.val).setHashAddress step)) value =
        (wotsFTcrCProblem toyPrimitives).th.eval pk.pkSeed
          (toyPrimitives.adrsToKey
            ((wotsChainAdrs (wotsLeafAdrs
                (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
                (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val)
              i.val).setHashAddress step))
          (chain toyPrimitives pk.pkSeed
            (wotsChainAdrs (wotsLeafAdrs
              (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
              (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val) i.val)
            (wotsSign toyPrimitives
              (armMsg sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk) layer) sk pk.pkSeed
              (wotsLeafAdrs (armPos (schemeParts toy toyPrimitives msg sig pk) layer).toAdrs
                (armPos (schemeParts toy toyPrimitives msg sig pk) layer).leaf.val))[i.val]
            (chainStepsCore toyPrimitives.core
              (armMsg sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk) layer) i.val)
            (step - chainStepsCore toyPrimitives.core
              (armMsg sk pk.pkSeed (schemeParts toy toyPrimitives msg sig pk) layer) i.val)) :=
  wotsWitness_valid_fCollision_eval toyPrimitives pk.pkSeed _ _ _ i step value
    ((XmssWitness.valid_wots sk pk.pkSeed _ _ _ _).mp
      ((HypertreeWitness.valid_iff sk pk.pkSeed
        (LayerPosition.initial toy (schemeParts toy toyPrimitives msg sig pk)) _ toy.params.d
        (by simp) _).mp
        ((Witness.valid_hypertree (vp := toy) (prims := toyPrimitives) sk pk msg sig _).mp h)))

def main : IO Unit := do
  checkToyBundle
  checkSchemeEquations
  checkHonestForgery
  checkCollapsedForgery
  checkHypertreeArm "B" sigB 0 2 0 forgedForsPk
  checkHypertreeArm "C" sigC 1 2 0 divergedRoot
  checkHypertreeCollision "E" sigE 1 1
  checkNoWitness
  checkArmSelection
  checkHonestPartner
  checkFabricated
  IO.println "SLH-DSA scheme witness tests: PASS"

end SLHDSA.SchemeWitnessesTest

def main : IO Unit := SLHDSA.SchemeWitnessesTest.main
