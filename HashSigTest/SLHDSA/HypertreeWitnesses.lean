/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.HypertreeWitnesses
public import HashSig.SLHDSA.Security.EncodedTargets

/-!
# SLH-DSA hypertree witness canaries

Executable checks that the hypertree layer walk selects the *right layer*, and that the witness it
returns there really attacks the honest key material of that layer's tree — evaluated at the
values, not restated from the theorems.

No collision is exhibitable under an approved instantiation, so the extraction canaries run over a
toy primitive bundle whose `Thash` folds its input with a two-bit shift and drops the low bit of
every child, then exclusive-ors a tweak derived from the whole address, layer and tree words
included.  Its secret map takes the layer and the tree words as well as the key-pair and chain
words, rather than the key-pair and chain alone, so that the three trees are not copies of one
another; `checkToyBundle` asserts the consequence the canaries use.  The witness lemmas are stated
for an arbitrary `Primitives` bundle, so this is in scope; it is a falsifiability fixture, not a
claim about any approved profile.

The profile has **three** layers of height two, which is the point: at `d = 3` there is a layer —
the middle one — whose neighbours in both directions are in range, so an index one off is not
caught by the bound alone.  The trajectory the digest parts fix is `(layer 0, tree 6, leaf 3)`,
`(layer 1, tree 1, leaf 2)`, `(layer 2, tree 0, leaf 1)` — three positions differing in all three
coordinates, so a layer read one too high or one too low moves the tree address, the leaf *and* the
honest running message together.

## The three forgeries

One per divergence layer, each a full-depth hypertree signature that recovers the published root
from a forged message.  At the divergence layer the component is the honest XMSS signer applied to
the *running* message arriving there — a signature the honest signer never produced at that
message, which recovers that tree's honest root all the same.  Below it the components carry a
perturbed authentication path, so their recovered roots miss their layers' honest roots and the
walk cannot stop early.  Above it the components are the honest hypertree signature's own, which is
sound because the running message arriving one layer up is that tree's honest root either way.

`checkLayer` runs one of them.  It pins that the walk reaches the published root, that the message
signed at the divergence layer is not the honest one there and that that layer's own recovery is
the honest root; it pins the layer *and the constructor* the extractor reports; evaluates the
returned witness at that layer's tree address, leaf and honest running message; and then
re-evaluates the *same* witness four more times per neighbouring layer: once for each of those
three arguments, changing one at a time, and once with all three moved together, which is
`HypertreeWitness.Valid` as a whole.  Each of the four is required to fail.

All three re-evaluations bite only because all three forgeries extract an `fPreimage` witness,
which is why the constructor is pinned rather than assumed.  `checkLayerH` runs the other case and
says what changes there.

## The other canaries

`checkLayerH` is the fourth extraction canary and the only one that reaches the `hCollision`
branch: a layer-zero component whose WOTS+ part is fabricated rather than signed, whose
authentication path is the honest one for the forged message, and which recovers layer zero's
honest root all the same.  Its assertion set is matched to that branch, because two of
`checkLayer`'s three re-evaluations do not discriminate an `hCollision` witness and one of them
never can.  `XmssWitness.Valid`'s `hCollision` branch does not mention the honest message at all,
so the honest-message re-evaluation is inert at every layer; and the leaf enters only as
`idx / 2 ^ z`, so at the extracted height `z = 1` the leaves `3` and `2` of layers zero and one
share the node index `1` and the leaf re-evaluation is inert between them, while layer two's leaf
`1` gives node index `0` and does discriminate.  What discriminates at both neighbours is the tree
address.  The leaf inertness is asserted to *hold*, so it is pinned rather than passed over; it
turns on this fixture's two leaves sharing a node index, and it fails if the trajectory changes.
The honest-message inertness is not asserted, because it would not be an independent assertion:
`xmssWitnessHolds` takes the honest message as an argument and its `hCollision` branch never reads
it, so re-evaluating the same witness at a neighbouring layer's honest message is the same
computation as the check that the witness holds at its own layer.  A pin on it would test
`xmssWitnessHolds` against `XmssWitness.Valid`, not the extractor.

`checkNoWitness` closes both ways the search can return nothing.  The honest hypertree signature
extracted against the message it actually signs matches at layer zero and still returns nothing,
because at `msg = msg'` every chain's two step counts agree and the WOTS+ chain search runs out;
re-running the same walk against a *distinct* second message returns a layer-zero witness, which is
what pins that layer zero was reached rather than missed.  It also pins that the honest walk
reaches the published root, so that nothing coming back cannot be blamed on a walk that never got
there.  And a walk whose three layers all miss their honest roots reaches the last layer without a
match and stops.

`checkEarlyMatch` runs a walk that matches at layer zero and then misses the published root.  A
witness comes back and holds, which is `findHypertreeWitness_sound` carrying no top-root
hypothesis.

`checkFabricatedWitnesses` is the tally: nine runs of `hypertreeWitnessHolds`, three accepted and
six rejected.  The six are the in-range layer shifts, and they falsify the one conjunct
`HypertreeWitness.Valid` has — the XMSS condition at the position and honest message the label
names.  There is no out-of-range fabrication, and there cannot be one: `HypertreeWitness.layer` is
a `Fin toyParams.d`, so a label at or beyond `d` is not a witness at this walk length and does not
elaborate.  What used to be two run-time rejections is a build error now, exercised by the mutation
that widens the label's index rather than by an `ensure`.

The `example`s pin the theorem statements at that bundle, including the nine declarations with no
consumer inside the library, and the ledger and encoded-tweak lemmas at the same profile — which
is inside the approved address bounds, so no second parameter record is introduced.
-/

public section

namespace SLHDSA.HypertreeWitnessesTest

open Security Concrete GeneralHypertree

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"Hypertree witness check failed: {label}")

/-! ## The toy profile

Three layers of height two, one FORS tree of height one, `w = 16`, `len = 4`. -/

-- Exposed: the profile, its validated form, the digest parts and the three positions all have to
-- reduce inside the `decide` pins below and inside the exposed bundle they configure, and each
-- position's `next` bound is discharged by `decide` from the one below it.  Neither the secret map
-- nor the tweak map needs exposure of its own.  Nothing outside this executable consumes them.
/-- Three layers of height two: six hypertree bits, four leaves per tree. -/
@[expose] def toyParams : Params :=
  { n := 1, h := 6, d := 3, hp := 2, a := 1, k := 1, lgw := 4 }

theorem toyValid : toyParams.Valid := by decide

/-- The validated form of `toyParams`. -/
@[expose] def toy : ValidatedParams := ⟨toyParams, toyValid⟩

example : toyParams.w = 16 := by decide
example : toyParams.len = 4 := by decide
example : toyParams.m = 3 := by decide

/-- The per-chain secret values the toy `PRF` hands out.  The layer and tree words enter as well
as the key-pair and chain words, so the three layers' trees are not copies of one another. -/
def toySecret (layer tree kp chain : ℕ) : UInt8 :=
  UInt8.ofNat ((layer * 101 + tree * 53 + kp * 37 + chain * 11 + 7) % 256)

/-- A per-address byte mixed into every `Thash` output, taking all six address words, so that the
same children at two different layers, trees or nodes hash differently. -/
def toyTweak (a : Adrs) : UInt8 :=
  UInt8.ofNat ((a.layer * 131 + a.tree * 71 + a.type * 61 + a.word1 * 29 + a.word2 * 43 +
    a.word3 * 97) % 256)

/-- The toy bundle: one byte per node, a collapsing order- and address-sensitive `Thash`. -/
@[expose, reducible] def toyPrimitives : Primitives toyParams where
  PkSeed := Unit
  SkSeed := Unit
  SkPrf := Unit
  Y := Bytes 1
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ _ adrs =>
    Vector.replicate 1 (toySecret adrs.layer adrs.tree adrs.word1 adrs.word2)
  PRFmsg := fun _ _ _ => Vector.replicate 1 0
  yToBytes := id
  Thash := fun _ adrs children =>
    Vector.replicate 1
      ((children.foldl (fun (acc : UInt8) (y : Bytes 1) => (acc <<< 2) ^^^ (y[0] >>> 1))
        (0 : UInt8)) ^^^ toyTweak adrs)
  Hmsg := fun _ _ _ _ => Vector.replicate toyParams.m 0

instance : DecidableEq toyPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 1))

theorem toyByteLaws : toyPrimitives.core.ByteLaws := ⟨fun _ _ h => h⟩

/-- A one-byte node. -/
def node (x : UInt8) : toyPrimitives.Y := Vector.replicate 1 x

/-- The byte inside a node. -/
def byteOf (y : toyPrimitives.Y) : UInt8 := y[0]

/-! ## The trajectory -/

/-- The digest parts fixing the trajectory: layer-zero tree six, leaf three. -/
@[expose] def parts : DigestParts toyParams :=
  { md := Vector.replicate toyParams.digestBytes 0, idxTree := ⟨6, by decide⟩,
    idxLeaf := ⟨3, by decide⟩ }

/-- The layer-zero position: tree six, leaf three. -/
@[expose] def pos0 : LayerPosition toy := LayerPosition.initial toy parts

/-- The layer-one position: tree one, leaf two. -/
@[expose] def pos1 : LayerPosition toy := pos0.next (by decide)

/-- The top-layer position: tree zero, leaf one. -/
@[expose] def pos2 : LayerPosition toy := pos1.next (by decide)

example : (pos0.layer.val, pos0.tree.val, pos0.leaf.val) = (0, 6, 3) := by decide
example : (pos1.layer.val, pos1.tree.val, pos1.leaf.val) = (1, 1, 2) := by decide
example : (pos2.layer.val, pos2.tree.val, pos2.leaf.val) = (2, 0, 1) := by decide

/-- The three positions by layer, written out rather than iterated.  This is the second computation
of what `LayerPosition.advance` computes; `checkToyBundle` asserts they agree at all three layers.
The catch-all is what makes the function total; nothing calls it above layer two, because every
caller reads a `Fin toyParams.d` or one of the three literals. -/
def posOf : ℕ → LayerPosition toy
  | 0 => pos0
  | 1 => pos1
  | _ => pos2

/-! ## Messages and honest key material -/

/-- The forged top-level message, whose chain lengths are `[0, 15, 0, 15]`. -/
def forgedMsg : toyPrimitives.Y := node 0x0F

/-- The honestly signed top-level message, whose chain lengths are `[3, 0, 1, 11]`. -/
def honestMsg : toyPrimitives.Y := node 0x30

theorem forgedMsg_ne_honestMsg : forgedMsg ≠ honestMsg := fun h =>
  absurd (congrArg (fun v : toyPrimitives.Y => v.toList) h) (by decide)

/-- The honest XMSS root of the tree at layer `i`. -/
def honestRoot (i : ℕ) : toyPrimitives.Y :=
  xmssRoot toyPrimitives () () (posOf i).toAdrs

/-- The honest message signed at layer `i`, written out rather than recursed.  This is the second
computation of what `honestLayerMsg` computes, and its catch-all is totality for the same reason
`posOf`'s is. -/
def honestMsgAt : ℕ → toyPrimitives.Y
  | 0 => honestMsg
  | 1 => honestRoot 0
  | _ => honestRoot 1

/-- The honest XMSS signature at layer `i`, on the honest message signed there. -/
def honestXmssSig (i : ℕ) : XmssSig toyParams toyPrimitives :=
  xmssSign toyPrimitives (honestMsgAt i) () () (posOf i).toAdrs (posOf i).leaf.val

/-- The honest hypertree signature, assembled layer by layer rather than taken from the signer.
`checkToyBundle` asserts it is the one `GeneralHypertree.sign` produces. -/
def honestHtSig : Signature toy toyPrimitives.core :=
  #v[honestXmssSig 0, honestXmssSig 1, honestXmssSig 2]

/-- One XMSS signature as bytes, for comparison. -/
def sigBytes (s : XmssSig toyParams toyPrimitives) : List UInt8 :=
  (s.wots.toList.map byteOf) ++ (s.auth.toList.map byteOf)

/-- One hypertree signature as bytes, for comparison. -/
def htBytes (s : Signature toy toyPrimitives.core) : List (List UInt8) :=
  s.toList.map sigBytes

/-- Perturb bit two of an authentication path's height-zero entry.  `H` drops the low bit of each
child, so bit two is the lowest one that survives two levels of the climb; the recovered root
therefore misses the honest one, which the canaries assert rather than assume. -/
def spoil (s : XmssSig toyParams toyPrimitives) : XmssSig toyParams toyPrimitives :=
  { s with auth := Vector.ofFn fun k : Fin toyParams.hp =>
      if k.val = 0 then node (byteOf s.auth[0] ^^^ 4) else s.auth[k.val] }

/-- XMSS root recovery at layer `i`'s position. -/
def recoverAt (i : ℕ) (s : XmssSig toyParams toyPrimitives) (m : toyPrimitives.Y) :
    toyPrimitives.Y :=
  xmssPkFromSig toyPrimitives (posOf i).leaf.val s m () (posOf i).toAdrs

/-- The honest XMSS signing algorithm at layer `i`'s position, on an arbitrary message. -/
def signAt (i : ℕ) (m : toyPrimitives.Y) : XmssSig toyParams toyPrimitives :=
  xmssSign toyPrimitives m () () (posOf i).toAdrs (posOf i).leaf.val

/-- Layer zero's diverging component: signed on the forged message, path perturbed. -/
def bad0 : XmssSig toyParams toyPrimitives := spoil (signAt 0 forgedMsg)

/-- The message the walk hands to layer one after `bad0`. -/
def run1 : toyPrimitives.Y := recoverAt 0 bad0 forgedMsg

/-- Layer one's diverging component: signed on `run1`, path perturbed. -/
def bad1 : XmssSig toyParams toyPrimitives := spoil (signAt 1 run1)

/-- The message the walk hands to layer two after `bad1`. -/
def run2 : toyPrimitives.Y := recoverAt 1 bad1 run1

/-- The forgery that meets the honest hypertree at layer zero. -/
def forgery0 : Signature toy toyPrimitives.core :=
  #v[signAt 0 forgedMsg, honestXmssSig 1, honestXmssSig 2]

/-- The forgery that meets it at layer one. -/
def forgery1 : Signature toy toyPrimitives.core := #v[bad0, signAt 1 run1, honestXmssSig 2]

/-- The forgery that meets it at the top layer. -/
def forgery2 : Signature toy toyPrimitives.core := #v[bad0, bad1, signAt 2 run2]

/-- The full-depth search from the layer-zero position, on the forged and honest messages. -/
def extract (s : Signature toy toyPrimitives.core) :
    Option (HypertreeWitness toy toyPrimitives toyParams.d) :=
  findHypertreeWitness toy toyPrimitives () () pos0 toyParams.d (by decide) forgedMsg honestMsg s

/-- The fixture's three layers, as the `Fin toyParams.d` labels a witness carries.  A label outside
this range is not a `HypertreeWitness` at this walk length and cannot be written down at all. -/
def allLayers : List (Fin toyParams.d) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

/-- A tag naming the layer and the constructor a search returned. -/
def tag : Option (HypertreeWitness toy toyPrimitives toyParams.d) -> String
  | none => "none"
  | some ⟨l, .hCollision z _⟩ => s!"layer {l.val} hCollision {z}"
  | some ⟨l, .wots (.tlCollision _)⟩ => s!"layer {l.val} tlCollision"
  | some ⟨l, .wots (.fPreimage i st _)⟩ => s!"layer {l.val} fPreimage {i.val} {st}"
  | some ⟨l, .wots (.fCollision i st _)⟩ => s!"layer {l.val} fCollision {i.val} {st}"

/-! ## Witness validity, evaluated

`xmssWitnessHolds` re-evaluates the condition each `XmssWitness` constructor asserts, at an
address, a leaf and an honest message supplied as arguments, and from honest values recomputed
here rather than read off `XmssWitness.Valid` or `WotsWitness.Valid`.  Taking those three as
arguments is what lets the layer canaries below run the *same* witness at a neighbouring layer's
address, at a neighbouring layer's leaf, and against a neighbouring layer's honest message, and
watch each one fail on its own.

`hypertreeWitnessHolds` supplies those three from the layer, through `posOf` and `honestMsgAt` —
which are written out by hand, so they are a second computation of what `LayerPosition.advance` and
`honestLayerMsg` compute.  `checkToyBundle` asserts the two agree at all three layers.  It adds no
bound of its own: the label is a `Fin toyParams.d` and the bound is in its type. -/

/-- The honest WOTS+ signature at a leaf's base address on an honest message. -/
def honestWotsSig (la : Adrs) (hmsg : toyPrimitives.Y) : WotsSig toyParams toyPrimitives.core :=
  wotsSign toyPrimitives hmsg () () la

/-- The honest WOTS+ chain ends there, advanced from the honest signature rather than taken from
`wotsPkGenTops`; `checkToyBundle` asserts the two agree. -/
def honestWotsTops (la : Adrs) (hmsg : toyPrimitives.Y) :
    Vector toyPrimitives.Y toyParams.len :=
  Vector.ofFn fun i : Fin toyParams.len =>
    chain toyPrimitives () (wotsChainAdrs la i.val) (honestWotsSig la hmsg)[i.val]
      (chainStepsCore toyPrimitives.core hmsg i.val)
      (toyParams.w - 1 - chainStepsCore toyPrimitives.core hmsg i.val)

/-- The honest chain value at a hash address, advanced from the honest revealed value. -/
def honestChainValue (la : Adrs) (hmsg : toyPrimitives.Y) (i : Fin toyParams.len) (step : ℕ) :
    toyPrimitives.Y :=
  chain toyPrimitives () (wotsChainAdrs la i.val) (honestWotsSig la hmsg)[i.val]
    (chainStepsCore toyPrimitives.core hmsg i.val)
    (step - chainStepsCore toyPrimitives.core hmsg i.val)

/-- The honest child pair of an XMSS node, recomputed from `PerfectMerkleTree.merkleRoot` rather
than taken from `xmssHonestChildren`. -/
def honestChildPair (adrs : Adrs) (z t : ℕ) : toyPrimitives.Y × toyPrimitives.Y :=
  (PerfectMerkleTree.merkleRoot (xmssLeaf toyPrimitives () () adrs)
      (xmssNodeHash toyPrimitives () adrs) (z - 1) (2 * t),
    PerfectMerkleTree.merkleRoot (xmssLeaf toyPrimitives () () adrs)
      (xmssNodeHash toyPrimitives () adrs) (z - 1) (2 * t + 1))

/-- The nine conjuncts of `WotsWitness.Valid`, evaluated at a WOTS+ base address and an honest
message: two on `tlCollision`, three on `fPreimage` and four on `fCollision`. -/
def wotsWitnessHolds (la : Adrs) (hmsg : toyPrimitives.Y) :
    WotsWitness toyParams toyPrimitives → Bool
  | .tlCollision recovered =>
      (recovered != honestWotsTops la hmsg) &&
        (toyPrimitives.Tl () (wotsPkAdrs la) recovered.toList ==
          toyPrimitives.Tl () (wotsPkAdrs la) (honestWotsTops la hmsg).toList)
  | .fPreimage i step value =>
      decide (step < toyParams.w - 1) &&
        decide (step + 1 = chainStepsCore toyPrimitives.core hmsg i.val) &&
        (toyPrimitives.F () ((wotsChainAdrs la i.val).setHashAddress step) value ==
          (honestWotsSig la hmsg)[i.val])
  | .fCollision i step value =>
      decide (step < toyParams.w - 1) &&
        decide (chainStepsCore toyPrimitives.core hmsg i.val ≤ step) &&
        (value != honestChainValue la hmsg i step) &&
        (toyPrimitives.F () ((wotsChainAdrs la i.val).setHashAddress step) value ==
          toyPrimitives.F () ((wotsChainAdrs la i.val).setHashAddress step)
            (honestChainValue la hmsg i step))

/-- The thirteen conjuncts of `XmssWitness.Valid`, evaluated at a tree address, a leaf and an
honest message: four on `hCollision` and `wotsWitnessHolds`' nine on the `wots` branch. -/
def xmssWitnessHolds (adrs : Adrs) (idx : ℕ) (hmsg : toyPrimitives.Y) :
    XmssWitness toyParams toyPrimitives → Bool
  | .hCollision z c =>
      decide (0 < z) && decide (z ≤ toyParams.hp) &&
        (honestChildPair adrs z (idx / 2 ^ z) != c) &&
        (toyPrimitives.H () (xmssNodeAdrs adrs z (idx / 2 ^ z))
              (honestChildPair adrs z (idx / 2 ^ z)).1
              (honestChildPair adrs z (idx / 2 ^ z)).2 ==
          toyPrimitives.H () (xmssNodeAdrs adrs z (idx / 2 ^ z)) c.1 c.2)
  | .wots wt => wotsWitnessHolds (wotsLeafAdrs adrs idx) hmsg wt

/-- The one conjunct of `HypertreeWitness.Valid` at the full-depth walk from `pos0`: the XMSS
condition at the address, leaf and honest message that layer names.  The layer bound is not
evaluated here because it is not a conjunct — the label is a `Fin toyParams.d`, so the bound is in
the witness's type and an out-of-range label is a build error rather than a rejected run. -/
def hypertreeWitnessHolds (w : HypertreeWitness toy toyPrimitives toyParams.d) : Bool :=
  xmssWitnessHolds (posOf w.layer.val).toAdrs (posOf w.layer.val).leaf.val
    (honestMsgAt w.layer.val) w.witness

/-! ## The bundle behaves as advertised -/

/-- Seven fixture properties, in seven `ensure` sites, one of them a three-layer loop.

The three honest XMSS roots are pairwise distinct, and so are the three honest running messages, so
a witness read at the wrong layer is read against a different honest partner.  The four honest
leaves of each of the three trees are pairwise distinct, so no two leaves of one tree share one.
The hand-written `posOf` agrees with `LayerPosition.advance` and the hand-written `honestMsgAt`
with `honestLayerMsg`, at all three layers, so the layer canaries below check the extractor against
a table that is written independently of the library's and known to match it.

Those two agreement checks are load-bearing, not documentation, and it is worth saying what they
carry now that the library also carries part of it.  When `HypertreeWitness.layer` was a bare `ℕ`,
shifting the extractor's label and `HypertreeWitness.Valid`'s reading of it *together* — labelling
the base case `⟨1, ·⟩` and reading `w.layer - 1` — re-proved `findHypertreeWitness_sound` by the
same induction, and the executable was the only thing that noticed.  The label is a `Fin layers`
now, so that particular shift no longer elaborates — but the class is not closed by the type.  The
reflection `t ↦ layers - 1 - t`, counting the layer from the top of the walk instead of from the
walk's start, agrees with the identity at walk length one, which is the only place `Fin layers` pins
anything, and it re-proves the library.  What stops it is in this module: the statement pins below
restate the two shape equations and `HypertreeWitness.Valid`'s body with the label read raw, so the
reflection is a build error *here* at five sites; and renumbering those pins with it leaves
`checkLayer`'s pin failing at run time with `layer 0: layer index is 0`, the reflected extractor
reporting layer two for the layer-zero divergence.  These checks stay because they are what caught
this class, because they cost nothing, and because they check the numbering a second way, not
through `HypertreeWitness.Valid`: `checkLayer`'s `w.layer == layer` pin compares against the label
the fixture *built* the divergence at, and `hypertreeWitnessHolds` reads `posOf` and `honestMsgAt`.
Renumbering those two tables to match some other labelling makes them stop agreeing with `advance`
and `honestLayerMsg` at the fixed layers `0`, `1` and `2`, and the agreement check fails.  Without
them the executable would be a restatement of the library at whatever numbering the library
happened to use; with them it is an independent one.  The hand-written honest chain ends agree with
`wotsPkGenTops`, which is what `XmssWitness.Valid` names.  And the hand-assembled honest hypertree
signature is the one `GeneralHypertree.sign` produces. -/
def checkToyBundle : IO Unit := do
  ensure "honest roots distinct"
    (honestRoot 0 != honestRoot 1 && honestRoot 1 != honestRoot 2 &&
      honestRoot 0 != honestRoot 2)
  ensure "honest running messages distinct"
    (honestMsgAt 0 != honestMsgAt 1 && honestMsgAt 1 != honestMsgAt 2 &&
      honestMsgAt 0 != honestMsgAt 2)
  for i in [0, 1, 2] do
    let leaves := (List.range 4).map fun t => xmssLeaf toyPrimitives () () (posOf i).toAdrs t
    ensure s!"leaves of tree {i} distinct" (leaves.Nodup)
  ensure "posOf agrees with advance"
    (posOf 0 == pos0.advance 0 (by decide) && posOf 1 == pos0.advance 1 (by decide) &&
      posOf 2 == pos0.advance 2 (by decide))
  ensure "honestMsgAt agrees with honestLayerMsg"
    (honestMsgAt 0 == honestLayerMsg toy toyPrimitives () () pos0 honestMsg 0 (by decide) &&
      honestMsgAt 1 == honestLayerMsg toy toyPrimitives () () pos0 honestMsg 1 (by decide) &&
      honestMsgAt 2 == honestLayerMsg toy toyPrimitives () () pos0 honestMsg 2 (by decide))
  ensure "honest chain ends agree with wotsPkGenTops"
    (((List.range 3).all fun j =>
      let la := wotsLeafAdrs (posOf j).toAdrs (posOf j).leaf.val
      honestWotsTops la (honestMsgAt j) == wotsPkGenTops toyPrimitives () () la))
  ensure "assembled honest signature is the signer's"
    (htBytes honestHtSig == htBytes (GeneralHypertree.sign toy toyPrimitives honestMsg () () parts))

/-! ## The three layer canaries -/

/-- One layer canary.  `sig` recovers the published root from the forged message, and the first
layer whose own recovered root is that layer's honest root is `layer`.  The check pins the layer
and the constructor the extractor reports, evaluates the returned witness at that layer's address,
leaf and honest message, and then re-evaluates the *same* witness against each other layer's
address, each other layer's leaf and each other layer's honest message, one at a time, and against
each other layer as a whole, which moves all three together; every one of those four is required to
fail.

The three positions of this fixture differ in all of layer, tree and leaf — `(0, 6, 3)`, `(1, 1,
2)` and `(2, 0, 1)` — so a layer read one too high or one too low moves the tree address, the leaf
and the honest running message together.

Whether each of the three re-evaluations then isolates one of them depends on which `XmssWitness`
constructor came back, which is why `branch` is pinned rather than left open.  All three callers
extract an `fPreimage` witness, and for that constructor all three do bite: `WotsWitness.Valid`'s
`fPreimage` branch reads the address through `wotsChainAdrs`, the leaf through `wotsLeafAdrs`, and
the honest message through both `chainStepsCore` and the honest WOTS+ signature.  For an
`hCollision` witness they do not, and `checkLayerH` runs that case with its own assertion set. -/
def checkLayer (name : String) (layer : Fin toyParams.d) (branch : String)
    (running : toyPrimitives.Y) (component : XmssSig toyParams toyPrimitives)
    (sig : Signature toy toyPrimitives.core) : IO Unit := do
  ensure s!"{name}: recovers the published root"
    (pkFromSig toy toyPrimitives forgedMsg sig () parts ==
      GeneralHypertree.root toy toyPrimitives () ())
  ensure s!"{name}: the message signed there is not the honest one"
    (running != honestMsgAt layer.val)
  ensure s!"{name}: and that layer's recovery is the honest root"
    (recoverAt layer.val component running == honestRoot layer.val)
  match extract sig with
  | none => throw (IO.userError s!"Hypertree witness check failed: {name}: no witness")
  | some w =>
      ensure s!"{name}: layer index is {layer.val}" (w.layer == layer)
      ensure s!"{name}: the branch is {branch}" (tag (some w) == branch)
      ensure s!"{name}: witness holds at its layer" (hypertreeWitnessHolds w)
      for other in allLayers do
        unless other == layer do
          ensure s!"{name}: fails against layer {other.val}'s honest message"
            (!xmssWitnessHolds (posOf layer.val).toAdrs (posOf layer.val).leaf.val
              (honestMsgAt other.val) w.witness)
          ensure s!"{name}: fails at layer {other.val}'s tree address"
            (!xmssWitnessHolds (posOf other.val).toAdrs (posOf layer.val).leaf.val
              (honestMsgAt layer.val) w.witness)
          ensure s!"{name}: fails at layer {other.val}'s leaf"
            (!xmssWitnessHolds (posOf layer.val).toAdrs (posOf other.val).leaf.val
              (honestMsgAt layer.val) w.witness)
          ensure s!"{name}: fails as a whole at layer {other.val}"
            (!hypertreeWitnessHolds ⟨other, w.witness⟩)

/-- The forged message is signed at layer zero by the honest XMSS signer, so layer zero's recovered
root is already that layer's honest root and the layers above it are the honest signature's own. -/
def checkLayer0 : IO Unit :=
  checkLayer "layer 0" ⟨0, by decide⟩ "layer 0 fPreimage 0 2" forgedMsg (signAt 0 forgedMsg)
    forgery0

/-- Layer zero's authentication path is perturbed, so its recovered root misses that layer's honest
root; the running message it hands up is signed at layer one by the honest XMSS signer. -/
def checkLayer1 : IO Unit :=
  checkLayer "layer 1" ⟨1, by decide⟩ "layer 1 fPreimage 1 13" run1 (signAt 1 run1) forgery1

/-- Both lower layers' authentication paths are perturbed, so the walk reaches the top layer before
meeting the honest hypertree, and the top layer's tree is the one whose root the public key
publishes. -/
def checkLayer2 : IO Unit :=
  checkLayer "layer 2" ⟨2, by decide⟩ "layer 2 fPreimage 1 4" run2 (signAt 2 run2) forgery2

/-- The fabricated layer-zero component that produces an `H`-collision witness: four WOTS+ chain
values that are not the honest signer's, carried on the honest authentication path for the forged
message.  Its recovered root is layer zero's honest root all the same, which is what the search
stops on, and what comes back is an `hCollision` at height one rather than a WOTS+ witness. -/
def collidingComponent : XmssSig toyParams toyPrimitives :=
  { wots := Vector.ofFn fun i : Fin toyParams.len => node (UInt8.ofNat (112 + i.val)),
    auth := (signAt 0 forgedMsg).auth }

/-- The forgery that meets the honest hypertree at layer zero through a fabricated leaf. -/
def forgeryH : Signature toy toyPrimitives.core :=
  #v[collidingComponent, honestXmssSig 1, honestXmssSig 2]

/-- The `hCollision` layer canary: the one extraction canary that does not return a WOTS+ witness.

Its point is that `checkLayer`'s three re-evaluations are not all discriminating for every witness
shape, and this is the shape they are not discriminating for.  Which of them bite is read off
`XmssWitness.Valid`'s `hCollision` branch, not guessed:

* the tree address enters through `xmssNodeAdrs adrs z (idx / 2 ^ z)` and through
  `xmssHonestChildren`, so the address re-evaluation fails at both neighbouring layers;
* the leaf enters only as `idx / 2 ^ z`.  The extracted height is `z = 1` and this fixture's leaves
  are `3`, `2` and `1`, so layers zero and one share the node index `1` and the leaf re-evaluation
  is *inert* between them, while layer two's node index is `0` and it does fail there;
* the honest message does not appear in the branch at all, so the honest-message re-evaluation is
  inert at every layer, and no fixture can make it otherwise.

The leaf inertness is asserted to *hold*, so it is pinned rather than skipped: it turns on the
fixture's leaves `3` and `2` quotienting to the same node index at `z = 1`, and a different
trajectory breaks it.  The honest-message inertness is *not* asserted, and the reason is that it
would not be an independent assertion: `xmssWitnessHolds` takes the honest message as an argument
and this branch never reads it, so `xmssWitnessHolds adrs idx (honestMsgAt other) w.witness` and
`xmssWitnessHolds adrs idx (honestMsgAt 0) w.witness` are the same evaluation — and the second is
what `hypertreeWitnessHolds w` already asserts, the layer having been pinned to zero just before.
A pin on it would fail only if `xmssWitnessHolds` or `XmssWitness.Valid` changed, not if the
extractor did.  `hypertreeWitnessHolds` at each other layer
— which moves all three arguments together — is still required to fail. -/
def checkLayerH : IO Unit := do
  ensure "hCollision: recovers the published root"
    (pkFromSig toy toyPrimitives forgedMsg forgeryH () parts ==
      GeneralHypertree.root toy toyPrimitives () ())
  ensure "hCollision: the component is not the honest signer's"
    (sigBytes collidingComponent != sigBytes (signAt 0 forgedMsg))
  ensure "hCollision: and layer zero's recovery is the honest root"
    (recoverAt 0 collidingComponent forgedMsg == honestRoot 0)
  match extract forgeryH with
  | none => throw (IO.userError "Hypertree witness check failed: hCollision: no witness")
  | some w =>
      ensure "hCollision: the branch is hCollision at height one"
        (tag (some w) == "layer 0 hCollision 1")
      ensure "hCollision: layer index is 0" (w.layer.val == 0)
      ensure "hCollision: witness holds at its layer" (hypertreeWitnessHolds w)
      for other in [(⟨1, by decide⟩ : Fin toyParams.d), ⟨2, by decide⟩] do
        ensure s!"hCollision: fails at layer {other.val}'s tree address"
          (!xmssWitnessHolds (posOf other.val).toAdrs (posOf 0).leaf.val (honestMsgAt 0) w.witness)
        ensure s!"hCollision: fails as a whole at layer {other.val}"
          (!hypertreeWitnessHolds ⟨other, w.witness⟩)
      ensure "hCollision: inert at layer 1's leaf, which shares its node index"
        (xmssWitnessHolds (posOf 0).toAdrs (posOf 1).leaf.val (honestMsgAt 0) w.witness)
      ensure "hCollision: fails at layer 2's leaf, which does not"
        (!xmssWitnessHolds (posOf 0).toAdrs (posOf 2).leaf.val (honestMsgAt 0) w.witness)

/-! ## What the search does when no layer matches, and when one matches early -/

/-- The honest hypertree signature, extracted against the message it actually signs.  Every layer's
recovered root is that layer's honest root, so the search stops at layer zero — and returns nothing
all the same, because at `msg = msg'` every chain's two step counts agree and the WOTS+ chain
search runs out.  That is `findHypertreeWitness_isSome`'s message-distinctness hypothesis being
necessary: the walk does reach the published root, and it does match at layer zero, so the other
way of returning nothing — no layer matching at all — is not available either, and nothing coming
back cannot be blamed on a walk that never got there; and re-running the same signature at the same
walk against a *distinct* second message returns a witness at layer zero, which is what pins that
the branch taken was layer zero's rather than a failure to match.

The second half runs a walk none of whose layers matches: three copies of the perturbed layer-zero
signature, which miss the honest root at all three layers, so the search reaches the last layer
without a match and stops.
Those are the only two ways nothing comes back. -/
def checkNoWitness : IO Unit := do
  ensure "honest walk reaches the published root"
    (pkFromSig toy toyPrimitives honestMsg honestHtSig () parts ==
      GeneralHypertree.root toy toyPrimitives () ())
  ensure "honest walk against its own message returns nothing"
    (findHypertreeWitness toy toyPrimitives () () pos0 toyParams.d (by decide) honestMsg honestMsg
      honestHtSig).isNone
  ensure "honest walk matches at layer zero"
    (xmssPkFromSig toyPrimitives pos0.leaf.val honestHtSig[0] honestMsg () pos0.toAdrs ==
      honestRoot 0)
  match findHypertreeWitness toy toyPrimitives () () pos0 toyParams.d (by decide) honestMsg
      forgedMsg honestHtSig with
  | none => throw (IO.userError "Hypertree witness check failed: honest walk, distinct message")
  | some w =>
      ensure "honest walk against a distinct message stops at layer zero" (w.layer.val == 0)
      ensure "and that witness holds against that message"
        (xmssWitnessHolds pos0.toAdrs pos0.leaf.val forgedMsg w.witness)
  ensure "a walk matching at no layer returns nothing"
    (findHypertreeWitness toy toyPrimitives () () pos0 toyParams.d (by decide) forgedMsg honestMsg
      (Vector.replicate toyParams.d bad0)).isNone
  let m1 := recoverAt 0 bad0 forgedMsg
  let m2 := recoverAt 1 bad0 m1
  ensure "and layer 0 of that walk misses its honest root" (m1 != honestRoot 0)
  ensure "and layer 1 of that walk misses its honest root" (m2 != honestRoot 1)
  ensure "and layer 2 of that walk misses its honest root"
    (recoverAt 2 bad0 m2 != honestRoot 2)

/-- A walk that matches at layer zero and then misses the published root: the forged message is
signed honestly at layer zero, and the top layer's authentication path is perturbed.  The search
stops at layer zero and its witness is valid there, which is `findHypertreeWitness_sound` carrying
no top-root hypothesis. -/
def checkEarlyMatch : IO Unit := do
  let sig : Signature toy toyPrimitives.core :=
    #v[signAt 0 forgedMsg, honestXmssSig 1, spoil (honestXmssSig 2)]
  ensure "early match: the walk misses the published root"
    (pkFromSig toy toyPrimitives forgedMsg sig () parts !=
      GeneralHypertree.root toy toyPrimitives () ())
  match extract sig with
  | none => throw (IO.userError "Hypertree witness check failed: early match: no witness")
  | some w =>
      ensure "early match: stops at layer zero" (w.layer.val == 0)
      ensure "early match: witness holds there" (hypertreeWitnessHolds w)

/-! ## Fabricated witnesses

Nine witnesses run through `hypertreeWitnessHolds`, three accepted and six rejected.  The three
accepted are the extractor's own answers at the three layers.  The six rejected are the in-range
layer shifts, and they falsify the one conjunct `HypertreeWitness.Valid` has: the XMSS condition at
the position and honest message the label names.  The per-argument separation — address, leaf,
honest message — is `checkLayer`'s.

An out-of-range fabrication is not among them because it is not writable.  `HypertreeWitness.layer`
is a `Fin toyParams.d`, so `⟨3, w⟩` and `⟨9, w⟩` — which this tally used to carry, as the two
rejections that isolated the old bound conjunct — are type errors rather than rejected runs.  The
bound is exercised at build time instead, by the mutation that widens the label's index. -/
/-- The tally: nine runs of `hypertreeWitnessHolds`, three accepted and six rejected. -/
def checkFabricatedWitnesses : IO Unit := do
  let mut accepted := 0
  let mut rejected := 0
  for (layer, sig) in
      [((⟨0, by decide⟩ : Fin toyParams.d), forgery0), (⟨1, by decide⟩, forgery1),
        (⟨2, by decide⟩, forgery2)] do
    match extract sig with
    | none => throw (IO.userError "Hypertree witness check failed: fabrication base missing")
    | some w =>
        ensure s!"fabrication base {layer.val} accepted" (hypertreeWitnessHolds w)
        accepted := accepted + 1
        for other in allLayers do
          unless other == layer do
            ensure s!"fabrication {layer.val}->{other.val} rejected"
              (!hypertreeWitnessHolds ⟨other, w.witness⟩)
            rejected := rejected + 1
  ensure "three accepted" (accepted == 3)
  ensure "six rejected" (rejected == 6)

/-! ## Statement pins

The theorems this module ships, elaborated at the toy profile.  Nine declarations have no consumer
inside the library and nothing else in the tree elaborates them — every name declared in
`HashSig.SLHDSA.Security.HypertreeWitnesses` that occurs exactly once in the code of `HashSig/`,
which is its own declaration line, nothing there importing that module: the two extractor shape
equations, the two extractor lemmas `findHypertreeWitness_sound` and `findHypertreeWitness_isSome`,
the `atLayer` bridge, the top-level walk, the cross-layer encoded-distinctness lemma, the
honest-signer bridge `signFromPosition_getElem`, and `LayerPosition.advance_ne`.  Each is pinned
here.  `HypertreeWitness.valid_iff` is not among them — `findHypertreeWitness_sound` rewrites with
it — and neither is `HypertreeWitness.layer_lt`, which is what `HypertreeWitness.Valid` forms its
position with; both are pinned all the same, in the form a consumer meets them.  The honest-signer
bridge is pinned as the layer-`j` component read against `honestLayerMsg`, and all three WOTS+
cross-layer separations are composed here the way the module docstring says they compose:
`wotsPkAdrsKey_injective` against `advance_ne` directly, `wotsOptionalStepAdrsKey_injective`
through the `congrArg Prod.fst` its `WotsChainCoord` conclusion needs, and
`wotsStepAdrsKey_injective` through the `congrArg (·.1.1)` its pair-valued conclusion needs.

Two of these pins carry more than their statements.  The extractor's dichotomy pin writes both
shape equations' labels out literally and the soundness pin writes `Valid`'s body with
`w.layer.val` read raw against `HypertreeWitness.layer_lt`, so a relabelling of the extractor that
the library's own `Fin layers` type admits — the reflection `t ↦ layers - 1 - t` — stops
elaborating at these five sites, in this module, before the canaries run. -/

example (pos : LayerPosition toy) (layers : ℕ)
    (hlayers : pos.layer.val + layers = toy.params.d) (msg msg' : toyPrimitives.Y)
    (hne : msg ≠ msg') (sigs : Vector (XmssSig toyParams toyPrimitives) layers)
    (hroot : recoverFromPosition toy toyPrimitives () pos layers hlayers msg sigs =
      xmssRoot toyPrimitives () () (layerAdrs (toyParams.d - 1) 0)) :
    ∃ (j : ℕ) (hj : j < layers) (m : toyPrimitives.Y),
      m ≠ honestLayerMsg toy toyPrimitives () () pos msg' j (by omega) ∧
        xmssPkFromSig toyPrimitives (pos.advance j (by omega)).leaf.val sigs[j] m ()
            (pos.advance j (by omega)).toAdrs =
          xmssRoot toyPrimitives () () (pos.advance j (by omega)).toAdrs :=
  recoverFromPosition_binding toy toyPrimitives () () pos layers hlayers msg msg' hne sigs hroot

/-- The top-level walk, read at a `Fin d` layer through `LayerPosition.atLayer`.  The distinctness
conjunct is dropped here so that the `atLayer` rewrite is the only content the pin carries. -/
example (msg msg' : toyPrimitives.Y) (hne : msg ≠ msg') (sig : Signature toy toyPrimitives.core)
    (hroot : pkFromSig toy toyPrimitives msg sig () parts =
      GeneralHypertree.root toy toyPrimitives () ()) :
    ∃ (j : Fin toy.params.d) (m : toyPrimitives.Y),
      xmssPkFromSig toyPrimitives (LayerPosition.atLayer toy parts j).leaf.val sig[j.val] m ()
          (LayerPosition.atLayer toy parts j).toAdrs =
        xmssRoot toyPrimitives () () (LayerPosition.atLayer toy parts j).toAdrs := by
  obtain ⟨j, hj, m, -, heq⟩ :=
    pkFromSig_binding toy toyPrimitives () () parts msg msg' hne sig hroot
  have hadv : (LayerPosition.initial toy parts).advance j (by change 0 + j < toy.params.d; omega) =
      LayerPosition.atLayer toy parts ⟨j, hj⟩ :=
    LayerPosition.advance_initial_eq_atLayer toy parts j (by change 0 + j < toy.params.d; omega)
  exact ⟨⟨j, hj⟩, m, by rw [← hadv]; exact heq⟩

/-- The extractor's dichotomy, from its two shape equations: at two or more remaining layers it
either stops here or moves up one position. -/
example (pos : LayerPosition toy) (layers : ℕ)
    (hlayers : pos.layer.val + (layers + 2) = toy.params.d) (msg msg' : toyPrimitives.Y)
    (sigs : Vector (XmssSig toyParams toyPrimitives) (layers + 2)) :
    findHypertreeWitness toy toyPrimitives () () pos (layers + 2) hlayers msg msg' sigs =
      if xmssPkFromSig toyPrimitives pos.leaf.val sigs.head msg () pos.toAdrs =
          xmssRoot toyPrimitives () () pos.toAdrs then
        (findXmssWitness toyPrimitives pos.leaf.val sigs.head msg msg' () () pos.toAdrs).map
          (⟨⟨0, Nat.succ_pos (layers + 1)⟩, ·⟩)
      else
        (findHypertreeWitness toy toyPrimitives () () (pos.next (by omega)) (layers + 1)
            (by simp only [LayerPosition.next_layer_val]; omega)
            (xmssPkFromSig toyPrimitives pos.leaf.val sigs.head msg () pos.toAdrs)
            (xmssRoot toyPrimitives () () pos.toAdrs) sigs.tail).map
          fun w => ⟨⟨w.layer.val + 1, Nat.succ_lt_succ w.layer.isLt⟩, w.witness⟩ := by
  by_cases h : xmssPkFromSig toyPrimitives pos.leaf.val sigs.head msg () pos.toAdrs =
      xmssRoot toyPrimitives () () pos.toAdrs
  · rw [if_pos h]
    exact findHypertreeWitness_eq_of_root toy toyPrimitives () () pos (layers + 1) hlayers msg
      msg' sigs h
  · rw [if_neg h]
    exact findHypertreeWitness_eq_next_of_ne toy toyPrimitives () () pos layers hlayers msg msg'
      sigs h

/-- Extractor soundness, destructured through the unfolding equation: a consumer recovers the
`XmssWitness` condition at the position and honest message the reported layer names, with the
position formed through `HypertreeWitness.layer_lt` rather than through a bound `Valid` supplies. -/
example (pos : LayerPosition toy) (layers : ℕ)
    (hlayers : pos.layer.val + layers = toy.params.d) (msg msg' : toyPrimitives.Y)
    (sigs : Vector (XmssSig toyParams toyPrimitives) layers)
    (w : HypertreeWitness toy toyPrimitives layers)
    (hw : findHypertreeWitness toy toyPrimitives () () pos layers hlayers msg msg' sigs =
      some w) :
    w.witness.Valid () () (pos.advance w.layer.val (w.layer_lt pos hlayers)).toAdrs
      (pos.advance w.layer.val (w.layer_lt pos hlayers)).leaf.val
      (honestLayerMsg toy toyPrimitives () () pos msg' w.layer.val (w.layer_lt pos hlayers)) :=
  (HypertreeWitness.valid_iff () () pos msg' layers hlayers w).mp
    (findHypertreeWitness_sound toy toyPrimitives () () pos layers hlayers msg msg' sigs hw)

/-- Extractor completeness at the toy bundle: two distinct messages and a walk reaching the honest
top root always yield a witness. -/
example (pos : LayerPosition toy) (layers : ℕ)
    (hlayers : pos.layer.val + layers = toy.params.d) (msg msg' : toyPrimitives.Y)
    (hne : msg ≠ msg')
    (sigs : Vector (XmssSig toyParams toyPrimitives) layers)
    (hroot : recoverFromPosition toy toyPrimitives () pos layers hlayers msg sigs =
      xmssRoot toyPrimitives () () (layerAdrs (toyParams.d - 1) 0)) :
    (findHypertreeWitness toy toyPrimitives () () pos layers hlayers msg msg' sigs).isSome :=
  findHypertreeWitness_isSome toy toyPrimitives toyByteLaws () () pos layers hlayers msg msg' hne
    sigs hroot

/-- The same at the fixture's own two messages, with the distinctness hypothesis discharged by
`forgedMsg_ne_honestMsg` rather than assumed.  This is the form the layer canaries rest on: any
full-depth walk from `pos0` on `forgedMsg` that reaches the honest top root yields a witness. -/
example (sigs : Vector (XmssSig toyParams toyPrimitives) toyParams.d)
    (hroot : recoverFromPosition toy toyPrimitives () pos0 toyParams.d (by decide) forgedMsg sigs =
      xmssRoot toyPrimitives () () (layerAdrs (toyParams.d - 1) 0)) :
    (findHypertreeWitness toy toyPrimitives () () pos0 toyParams.d (by decide) forgedMsg honestMsg
      sigs).isSome :=
  findHypertreeWitness_isSome toy toyPrimitives toyByteLaws () () pos0 toyParams.d (by decide)
    forgedMsg honestMsg forgedMsg_ne_honestMsg sigs hroot

/-- The honest running message is what the honest signer signs there.  This is the bridge the
module docstring points at wherever it calls `honestLayerMsg` a witness's honest partner; without
it that identification is a gloss.  `checkToyBundle` evaluates the same content at this fixture,
since `honestXmssSig i` is `xmssSign` on `honestMsgAt i` at `posOf i` and the assembled signature
is asserted to be the signer's. -/
example (msg : toyPrimitives.Y) (j : ℕ) (hj : pos0.layer.val + j < toyParams.d) :
    (signFromPosition toy toyPrimitives () () false pos0 toyParams.d (by decide) msg)[j]'
        (by have h0 : pos0.layer.val = 0 := by decide
            omega) =
      xmssSign toyPrimitives (honestLayerMsg toy toyPrimitives () () pos0 msg j hj) () ()
        (pos0.advance j hj).toAdrs (pos0.advance j hj).leaf.val :=
  signFromPosition_getElem toy toyPrimitives () () false pos0 toyParams.d (by decide) msg j
    (by have h0 : pos0.layer.val = 0 := by decide
        omega)

/-! ## Ledger pins

The toy profile is inside the approved address bounds, so it serves the ledger and encoded-tweak
pins as well as the extraction canaries; no second parameter record is introduced. -/

theorem toyApprovedAddressBounds : ApprovedAddressBounds toyParams :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    by decide, by decide⟩

/-- Every XMSS internal node an `hCollision` witness can name at a layer the walk reaches is a
listed `xmssH` target.  Slice 1's membership lemma applies to the advanced position unchanged. -/
example (j : ℕ) (hj : pos0.layer.val + j < toyParams.d) {z : ℕ} (hz : 0 < z)
    (hzh : z ≤ toyParams.hp) :
    xmssNodeAdrs (pos0.advance j hj).toAdrs z ((pos0.advance j hj).leaf.val / 2 ^ z) ∈
      xmssNodeAddresses toy :=
  mem_xmssNodeAddresses_of_leaf (pos0.advance j hj) hz hzh

/-- And the WOTS+ public-key address a `wots` witness names there is a listed `T_len` target. -/
example (j : ℕ) (hj : pos0.layer.val + j < toyParams.d) :
    wotsPkAdrs (wotsLeafAdrs (pos0.advance j hj).toAdrs (pos0.advance j hj).leaf.val) ∈
      wotsPkAddresses toy := by
  rw [wotsLeafAdrs_eq_wotsInstanceAdrs]
  exact mem_wotsPkAddresses toy _

/-- Under the SHA-2 encoder, XMSS internal-node targets at two layers of one walk carry equal
encoded tweaks only at the same layer, height and node index. -/
example (pos : LayerPosition toy) {j j' z z' i i' : ℕ}
    (hj : pos.layer.val + j < toyParams.d) (hj' : pos.layer.val + j' < toyParams.d)
    (hz : 0 < z) (hzh : z ≤ toyParams.hp) (hi : i < 2 ^ (toyParams.hp - z))
    (hz' : 0 < z') (hzh' : z' ≤ toyParams.hp) (hi' : i' < 2 ^ (toyParams.hp - z'))
    (hkey : (sha2Primitives toyParams).adrsToKey (xmssNodeAdrs (pos.advance j hj).toAdrs z i) =
      (sha2Primitives toyParams).adrsToKey (xmssNodeAdrs (pos.advance j' hj').toAdrs z' i')) :
    j = j' ∧ z = z' ∧ i = i' :=
  advance_xmssNodeAdrsKey_injective
    (sha2EncodedTargetLedgerConditions toy toyApprovedAddressBounds) pos hj hj' hz hzh hi hz' hzh'
    hi' hkey

/-- The same under the SHAKE encoder. -/
example (pos : LayerPosition toy) {j j' z z' i i' : ℕ}
    (hj : pos.layer.val + j < toyParams.d) (hj' : pos.layer.val + j' < toyParams.d)
    (hz : 0 < z) (hzh : z ≤ toyParams.hp) (hi : i < 2 ^ (toyParams.hp - z))
    (hz' : 0 < z') (hzh' : z' ≤ toyParams.hp) (hi' : i' < 2 ^ (toyParams.hp - z'))
    (hkey : (shakePrimitives toyParams).adrsToKey (xmssNodeAdrs (pos.advance j hj).toAdrs z i) =
      (shakePrimitives toyParams).adrsToKey (xmssNodeAdrs (pos.advance j' hj').toAdrs z' i')) :
    j = j' ∧ z = z' ∧ i = i' :=
  advance_xmssNodeAdrsKey_injective
    (shakeEncodedTargetLedgerConditions toy toyApprovedAddressBounds.toCanonicalAddressBounds) pos
    hj hj' hz hzh hi hz' hzh' hi' hkey

/-- Cross-layer separation for the `tlCollision` branch, whose ledger `wotsPkAddresses` is indexed
by the `LayerPosition` itself.  No lemma of this module composes it: `wotsPkAdrsKey_injective`
contradicts `LayerPosition.advance_ne` in one step, which is what the module docstring claims and
what this pins. -/
example (pos : LayerPosition toy) {j j' : ℕ}
    (hj : pos.layer.val + j < toyParams.d) (hj' : pos.layer.val + j' < toyParams.d) (hne : j ≠ j')
    (hkey : (sha2Primitives toyParams).adrsToKey
          (wotsPkAdrs (wotsInstanceAdrs (pos.advance j hj))) =
        (sha2Primitives toyParams).adrsToKey
          (wotsPkAdrs (wotsInstanceAdrs (pos.advance j' hj')))) : False :=
  LayerPosition.advance_ne pos hj hj' hne
    (wotsPkAdrsKey_injective (sha2EncodedTargetLedgerConditions toy toyApprovedAddressBounds) hkey)

/-- And for the `fCollision` branch, whose ledger `wotsStepAddresses` is indexed by a
`WotsChainCoord` paired with the step, so the position comes out of a pair equality. -/
example (pos : LayerPosition toy) {j j' : ℕ} (i i' : Fin toy.params.len)
    (s s' : Fin (toy.params.w - 1))
    (hj : pos.layer.val + j < toyParams.d) (hj' : pos.layer.val + j' < toyParams.d) (hne : j ≠ j')
    (hkey : (sha2Primitives toyParams).adrsToKey (wotsStepAdrs (pos.advance j hj, i) s) =
        (sha2Primitives toyParams).adrsToKey (wotsStepAdrs (pos.advance j' hj', i') s')) :
    False := by
  refine LayerPosition.advance_ne pos hj hj' hne ?_
  have h := wotsStepAdrsKey_injective
    (sha2EncodedTargetLedgerConditions toy toyApprovedAddressBounds)
    (a₁ := (⟨pos.advance j hj, i⟩, s)) (a₂ := (⟨pos.advance j' hj', i'⟩, s')) hkey
  exact congrArg (fun c => c.1.1) h

/-- And for the `fPreimage` branch, whose ledger `optionalWotsAddresses` is indexed by the
`WotsChainCoord` a selection picks a step of.  `wotsOptionalStepAdrsKey_injective` concludes that
coordinate equality directly, so one `congrArg Prod.fst` projects the position out. -/
example (pos : LayerPosition toy) {j j' : ℕ} (i i' : Fin toy.params.len)
    (select : WotsChainCoord toy → Option (Fin (toy.params.w - 1)))
    {s s' : Fin (toy.params.w - 1)}
    (hj : pos.layer.val + j < toyParams.d) (hj' : pos.layer.val + j' < toyParams.d) (hne : j ≠ j')
    (hc : select (pos.advance j hj, i) = some s) (hd : select (pos.advance j' hj', i') = some s')
    (hkey : (sha2Primitives toyParams).adrsToKey (wotsStepAdrs (pos.advance j hj, i) s) =
        (sha2Primitives toyParams).adrsToKey (wotsStepAdrs (pos.advance j' hj', i') s')) :
    False := by
  refine LayerPosition.advance_ne pos hj hj' hne ?_
  exact congrArg Prod.fst (wotsOptionalStepAdrsKey_injective
    (sha2EncodedTargetLedgerConditions toy toyApprovedAddressBounds) select hc hd hkey)

def main : IO Unit := do
  checkToyBundle
  checkLayer0
  checkLayer1
  checkLayer2
  checkLayerH
  checkNoWitness
  checkEarlyMatch
  checkFabricatedWitnesses
  IO.println "SLH-DSA hypertree witness tests: PASS \
    (layer extraction at all three layers of a depth-three profile, each pinned against the \
     neighbouring layers' addresses, leaves and honest messages, plus an `hCollision` extraction \
     with the assertion set its branch supports, and the no-match, early-match and \
     fabricated-witness canaries)"

end SLHDSA.HypertreeWitnessesTest

def main : IO Unit := SLHDSA.HypertreeWitnessesTest.main
