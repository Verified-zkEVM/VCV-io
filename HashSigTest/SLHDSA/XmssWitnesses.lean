/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.XmssWitnesses
public import HashSigTest.SLHDSA.EncoderFixtures

/-!
# SLH-DSA XMSS witness canaries

Executable checks that the XMSS witness extractor really produces witnesses, and that what it
produces really satisfies the collision or preimage equation — evaluated at the values, not
restated from the theorems.

No collision is exhibitable under an approved instantiation, so the extraction canaries run over a
toy primitive bundle whose `Thash` folds its input with a two-bit shift and drops the low bit of
every child, then exclusive-ors a per-address tweak.  Four properties of that bundle carry the
canaries: it collides readily; its four honest leaf images are pairwise distinct, so no two leaves
share an honest partner; it is *order sensitive*, so a witness stated with its two children swapped
fails by evaluation; and it is *address sensitive*, so a witness stated at a neighbouring node or
at a neighbouring leaf's WOTS+ address fails too.  `checkToyBundle` asserts all four, in five
checks.  The witness lemmas are stated for an arbitrary `Primitives` bundle, so this is in scope;
it is a falsifiability fixture, not a claim about any approved profile.

Over that bundle the checks build honest XMSS key material for a tree of height two — four WOTS+
leaves, `w = 16`, `len = 4` — and six named signatures at leaf `3` on a forged message, four of
which recover the honest XMSS root.  `nodeForgery` yields the `H`-collision at height one,
`rootForgery` the `H`-collision at the tree height `h' = 2`, `tlForgery` the `T_len` second
preimage at the opened leaf, `chainForgery` the `F`-collision at a chain step, `badForgery`
nothing at all, and `authForgery` — the only one that perturbs the authentication path rather than
the WOTS+ signature — a valid `F`-preimage in spite of missing the honest root.  A seventh
signature, the honest one on the forged message, is built inside `checkPreimage` and yields the
`F`-preimage at a chain step.  Each returned witness is checked against its equation by
evaluation.

Seven identifications are separated along the way: that the `H` partner is the honest child pair at
the node named; that its two children are taken left to right rather than opened-leaf first; that
the node index is the *ancestor* index `idx / 2 ^ z` rather than the leaf index; that the
`F`-preimage address is one below the honest digit rather than at it; that the WOTS+ partners are
read off the honest signature on the *honest* message rather than on the forged one; that the
`F`-collision partner is the honest revealed value *advanced* to the named step rather than that
value itself; and that both chain equations are read at the opened leaf's WOTS+ address rather than
a neighbouring leaf's.

Two negative canaries close the other direction.  The honest signature on the honest message
recovers the honest leaf and the honest root and still returns nothing: the same signature stands on
both sides, so the `T_len` test passes and the search reaches the chains, where at `msg = msg'`
every chain's two digits agree and `findWotsChainWitness`'s `a < b` guard fails at every index;
that is `findXmssWitness_isSome`'s `hne` being necessary, and re-running the same signature at the
same leaf against a *distinct* second message returns a WOTS+ witness, which is what pins the
branch.  And on a signature that misses the honest root the outcome is decided by the leaf test,
not by the root: `none` where the recovered leaf differs and the Merkle branch is taken, and — on
two distinct messages — a *valid* WOTS+ witness where the recovered leaf is honest and only the
authentication path is wrong.  Distinctness is what makes that second half a witness rather than a
`none`; validity holds of whatever comes back either way.

A third group fabricates eighteen witnesses — four accepted and fourteen rejected — which between
them falsify all thirteen conjuncts of `witnessHolds`.

The `example`s pin the theorem statements at that bundle and at approved profiles.  The last group
is kernel-checked rather than run: on a profile whose layer-zero tree indices overflow SHA-2's
compressed eight-byte tree field, two distinct listed XMSS internal-node targets encode to the same
all-zero key, so `xmssNodeAdrsKey_injective`'s `EncodedTargetLedgerConditions` hypothesis is
load-bearing rather than decorative.
-/

public section

namespace SLHDSA.XmssWitnessesTest

open Security Concrete EncoderFixtures

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"XMSS witness check failed: {label}")

/-! ## The toy bundle

One byte per node, one XMSS tree of height two, so four WOTS+ leaves; `w = 16` and `len = 4`, so
each leaf runs four chains of at most fifteen `F` steps.  `Thash` folds its children left to right
as `acc ↦ (acc <<< 2) ^^^ (child >>> 1)` and exclusive-ors a tweak derived from the address, so
`F x = (x >>> 1) ^^^ tw` and `H l r = (((l >>> 1) <<< 2) ^^^ (r >>> 1)) ^^^ tw`.  Dropping each
child's low bit is what makes collisions cheap; the `<<< 2` is what makes the fold order sensitive;
the tweak is what makes it address sensitive. -/

-- Exposed: the toy fixture's arithmetic has to reduce inside the exposed bundle below and inside
-- the `decide` pins, so the parameter record and the bundle it configures are exposed.  Neither
-- the secret map nor the tweak map needs exposure of its own.  Nothing outside this executable
-- consumes them.
@[expose] def toyParams : Params :=
  { n := 1, h := 2, d := 1, hp := 2, a := 1, k := 1, lgw := 4 }

theorem toyValid : toyParams.Valid := by decide

example : toyParams.w = 16 := by decide
example : toyParams.len = 4 := by decide

/-- The per-chain secret values the toy `PRF` hands out, indexed by the key-pair word and the chain
word of the `WOTS_PRF` address — which `wotsSkAdrs` sets to the leaf index and the chain index.
The affine map separates all sixteen `(leaf, chain)` pairs of this profile; `checkToyBundle`
asserts the consequence the canaries actually use, that the four honest leaf images are pairwise
distinct. -/
def toySecret (i : ℕ) : UInt8 := UInt8.ofNat ((i * 37 + 11) % 256)

/-- A per-address byte mixed into every `Thash` output, so that the same children at two different
addresses hash differently.  Without it the address a witness names would be invisible to
evaluation and the canaries could not reject a witness stated at a neighbouring node or at a
neighbouring leaf's WOTS address. -/
def toyTweak (a : Adrs) : UInt8 :=
  UInt8.ofNat ((a.type * 61 + a.word1 * 29 + a.word2 * 43 + a.word3 * 97) % 256)

@[expose, reducible] def toyPrimitives : Primitives toyParams where
  PkSeed := Unit
  SkSeed := Unit
  SkPrf := Unit
  Y := Bytes 1
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ _ adrs => Vector.replicate 1 (toySecret (adrs.word1 * 8 + adrs.word2))
  PRFmsg := fun _ _ _ => Vector.replicate 1 0
  yToBytes := id
  Thash := fun _ adrs children =>
    Vector.replicate 1
      ((children.foldl (fun (acc : UInt8) (y : Bytes 1) => (acc <<< 2) ^^^ (y[0] >>> 1))
        (0 : UInt8)) ^^^ toyTweak adrs)
  Hmsg := fun _ _ _ _ => Vector.replicate toyParams.m 0

instance : DecidableEq toyPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 1))

/-- The toy node encoding is the identity, so the bundle is byte coherent — which is what
`findXmssWitness_isSome` needs to reach `chainStepsCore_two_encodings`. -/
theorem toyByteLaws : toyPrimitives.core.ByteLaws := ⟨fun _ _ h => h⟩

/-- A one-byte node. -/
def node (x : UInt8) : toyPrimitives.Y := Vector.replicate 1 x

/-- The byte inside a node. -/
def byteOf (y : toyPrimitives.Y) : UInt8 := y[0]

/-- The XMSS tree address: layer zero, tree zero. -/
def baseAdrs : Adrs := (Adrs.zero.setLayerAddress 0).setTreeAddress 0

/-! ## The opened leaf

Leaf `3`, whose two properties give the canaries below their power.  It is **odd**, so it is the
*second* child of its parent and the honest child pair, taken left to right, is
`(leaf 2, leaf 3)` — not the `(opened leaf, sibling)` pair a partner keyed on the opened leaf would
name.  At an even leaf those two coincide and the swap canary would be blind.  And it is **not
zero**, so the height-one node index `3 / 2 = 1` differs from the leaf index itself, which is what
lets a canary reject a witness read at the un-divided index. -/
def leafIdx : ℕ := 3

/-- The WOTS+ base address of the opened leaf. -/
def leafAdrs : Adrs := wotsLeafAdrs baseAdrs leafIdx

example : leafIdx / 2 ^ 1 = 1 := by decide
example : leafIdx / 2 ^ 2 = 0 := by decide

/-! ## The two messages

`0x0F` is the forged message and `0x30` the honestly signed one.  Their chain-length vectors are
`[0, 15, 0, 15]` and `[3, 0, 1, 11]`.

Two features are load-bearing.  Chain `3`'s forged digit is `w - 1 = 15`, so recovery applies no
`F` step to it and its recovered chain end is the signature value itself: perturbing that one byte
is how every scenario below moves the recovered WOTS+ public key by a controlled amount, and chain
`3` is the last chain of the `T_len` fold, whose contribution is unshifted.  And chain `0`'s forged
digit `0` is strictly below its honest digit `3`, which is the condition `findWotsChainWitness`
acts on. -/
def forgedMsg : toyPrimitives.Y := node 0x0F
def honestMsg : toyPrimitives.Y := node 0x30

example : chainLengthsCore toyPrimitives.core forgedMsg = [0, 15, 0, 15] := by decide
example : chainLengthsCore toyPrimitives.core honestMsg = [3, 0, 1, 11] := by decide

theorem forgedMsg_ne_honestMsg : forgedMsg ≠ honestMsg := fun h =>
  absurd (congrArg (fun v : toyPrimitives.Y => v.toList) h) (by decide)

/-! ## Honest key material -/

/-- The honest XMSS leaf value at index `t`: the WOTS+ public key of keypair `t`. -/
def honestLeaf (t : ℕ) : toyPrimitives.Y := xmssLeaf toyPrimitives () () baseAdrs t

/-- The honest child pair of the XMSS node at height `z`, index `t`, recomputed from
`PerfectMerkleTree.merkleRoot` rather than taken from `xmssHonestChildren`. -/
def honestChildPair (z t : ℕ) : toyPrimitives.Y × toyPrimitives.Y :=
  (PerfectMerkleTree.merkleRoot (xmssLeaf toyPrimitives () () baseAdrs)
      (xmssNodeHash toyPrimitives () baseAdrs) (z - 1) (2 * t),
    PerfectMerkleTree.merkleRoot (xmssLeaf toyPrimitives () () baseAdrs)
      (xmssNodeHash toyPrimitives () baseAdrs) (z - 1) (2 * t + 1))

/-- The honest WOTS+ signature at the opened leaf on the honest message.  This is the object
`XmssWitness.Valid` recomputes for the two chain branches, and the one the identification canaries
separate from the honest signature on the *forged* message. -/
def honestLeafSig : WotsSig toyParams toyPrimitives.core :=
  wotsSign toyPrimitives honestMsg () () leafAdrs

/-- The honest WOTS+ chain ends at the opened leaf, recomputed by advancing the honest signature's
revealed values to the top rather than taken from `wotsPkGenTops`.  That the two agree is
`wotsPkFromSigTops_wotsSign`. -/
def honestTops : Vector toyPrimitives.Y toyParams.len :=
  Vector.ofFn fun i : Fin toyParams.len =>
    chain toyPrimitives () (wotsChainAdrs leafAdrs i.val) honestLeafSig[i.val]
      (chainStepsCore toyPrimitives.core honestMsg i.val)
      (toyParams.w - 1 - chainStepsCore toyPrimitives.core honestMsg i.val)

/-- The honest chain value at hash-address `step` of chain `i`, advanced from the value the honest
signature reveals.  This is the value `WotsWitness.Valid` names as the `fCollision` partner. -/
def honestChainValue (i : Fin toyParams.len) (step : ℕ) : toyPrimitives.Y :=
  chain toyPrimitives () (wotsChainAdrs leafAdrs i.val) honestLeafSig[i.val]
    (chainStepsCore toyPrimitives.core honestMsg i.val)
    (step - chainStepsCore toyPrimitives.core honestMsg i.val)

/-- The honest WOTS+ signature at the opened leaf on the *forged* message.  It is not an honest
partner of anything a witness attacks; it is the base the forgeries below perturb, and the
identification canaries check that no witness equation is satisfied against it. -/
def forgedMsgSig : WotsSig toyParams toyPrimitives.core :=
  wotsSign toyPrimitives forgedMsg () () leafAdrs

/-- The honest authentication path of the opened leaf. -/
def honestAuth : Vector toyPrimitives.Y toyParams.hp :=
  (xmssSign toyPrimitives forgedMsg () () baseAdrs leafIdx).auth

/-! ## The six signatures

All six sign the forged message at leaf `3`; four recover the honest XMSS root and two do not.
Five carry the honest authentication path — four perturbing chain `3` of `forgedMsgSig`, whose
recovered chain end is the signature value itself, and one perturbing chain `0` — while the sixth
leaves `forgedMsgSig` alone and perturbs the authentication path instead.

Chain `3`'s contribution to the `T_len` fold is `y >>> 1` unshifted, so flipping bit `b + 1` of
that byte flips bit `b` of the recovered WOTS+ public key — the opened leaf.  Bit `0` of a leaf is
dropped by `H` at its parent, bit `0` of that parent is dropped by `H` at the root, and bit `1` of
the leaf survives one level and is dropped at the next.  Hence the ladder below. -/

/-- Replace chain `3` of the honest signature on the forged message by that value exclusive-ored
with `t`. -/
def perturbTop (t : UInt8) : WotsSig toyParams toyPrimitives.core :=
  Vector.ofFn fun i : Fin toyParams.len =>
    if i.val = 3 then node (byteOf forgedMsgSig[3] ^^^ t) else forgedMsgSig[i.val]

/-- An XMSS signature at the opened leaf carrying the honest authentication path. -/
def xmssSigOf (w : WotsSig toyParams toyPrimitives.core) : XmssSig toyParams toyPrimitives :=
  { wots := w, auth := honestAuth }

/-- `t = 1`: bit `1` of chain `3` is untouched, so the recovered chain ends differ from the honest
ones while their `T_len` compression — the opened leaf — does not.  The extractor takes its WOTS+
branch and returns a `T_len` second preimage. -/
def tlForgery : XmssSig toyParams toyPrimitives := xmssSigOf (perturbTop 1)

/-- `t = 2`: the opened leaf differs from the honest one in bit `0`, which `H` drops at the parent,
so the height-one node and the tree root are unchanged.  The extractor returns the `H`-collision at
height one. -/
def nodeForgery : XmssSig toyParams toyPrimitives := xmssSigOf (perturbTop 2)

/-- `t = 4`: the opened leaf differs in bit `1`, which reaches the height-one node as a difference
in bit `0`; leaf `3` is that node's right child, so `H` reads it as `r >>> 1`.  The height-one node
is in turn the root's right child, so its bit `0` is dropped in the same way and the root is
unchanged.  The extractor therefore finds its collision one level higher, at the tree root — the
top of the `0 < z ≤ h'` range. -/
def rootForgery : XmssSig toyParams toyPrimitives := xmssSigOf (perturbTop 4)

/-- `t = 8`: the opened leaf differs in bit `2`, which reaches the height-one node as a difference
in bit `1` and the root as a difference in bit `0`.  This one does not recover the honest XMSS
root. -/
def badForgery : XmssSig toyParams toyPrimitives := xmssSigOf (perturbTop 8)

/-- Chain `0`'s signature value, chosen so that advancing it from the forged digit `0` to the
honest digit `3` lands on the honest revealed value exclusive-ored with `2`.  That difference is in
bit `1`, so it survives one `F` step as a difference in bit `0` and is dropped by the next: the two
chains therefore diverge at step `3` and collide at step `4`, one step *above* the honest digit.

The step matters.  At a collision sitting exactly at the honest digit the chain advance would be
the identity and the honest partner `XmssWitness.Valid` computes would coincide with the honest
revealed value itself, so the canaries could not tell the computed partner from that naive one. -/
def chainForgery : XmssSig toyParams toyPrimitives :=
  xmssSigOf (Vector.ofFn fun i : Fin toyParams.len =>
    if i.val = 0 then node 144 else forgedMsgSig[i.val])

/-- The honest WOTS+ signature on the forged message under an authentication path whose height-zero
entry is perturbed in bit `1`.  The recovered leaf is therefore the honest one while the climb
misses the honest root — the case a root mismatch alone does not decide, since the extractor
branches on the leaf.  It is the only signature here whose authentication path is not the honest
one. -/
def authForgery : XmssSig toyParams toyPrimitives :=
  { wots := forgedMsgSig,
    auth := Vector.ofFn fun j : Fin toyParams.hp =>
      if j.val = 0 then node (byteOf honestAuth[0] ^^^ 2) else honestAuth[j.val] }

/-! ## Witness validity, evaluated

`witnessHolds` re-evaluates the condition each constructor asserts, from the honest values
recomputed above rather than from `XmssWitness.Valid` or `WotsWitness.Valid`, including the four
identifications: the `hCollision` partner is the honest child pair at the node named, its two
children are supplied in left-to-right order, that node's index is `leafIdx / 2 ^ z` rather than
`leafIdx`, and the three WOTS+ partners are the honest key material at `leafAdrs` on `honestMsg`.
It is deliberately a separate computation from the two library predicates: the checks below run it
on the extractor's actual output.

It has thirteen conjuncts: four on `hCollision`, and — through the `wots` branch — two on
`tlCollision`, three on `fPreimage` and four on `fCollision`. -/
def witnessHolds : XmssWitness toyParams toyPrimitives → Bool
  | .hCollision z c =>
      let t := leafIdx / 2 ^ z
      decide (0 < z) && decide (z ≤ toyParams.hp) &&
        (honestChildPair z t != c) &&
        (toyPrimitives.H () (xmssNodeAdrs baseAdrs z t) (honestChildPair z t).1
            (honestChildPair z t).2 ==
          toyPrimitives.H () (xmssNodeAdrs baseAdrs z t) c.1 c.2)
  | .wots (.tlCollision recovered) =>
      (recovered != honestTops) &&
        (toyPrimitives.Tl () (wotsPkAdrs leafAdrs) recovered.toList ==
          toyPrimitives.Tl () (wotsPkAdrs leafAdrs) honestTops.toList)
  | .wots (.fPreimage i step value) =>
      decide (step < toyParams.w - 1) &&
        decide (step + 1 = chainStepsCore toyPrimitives.core honestMsg i.val) &&
        (toyPrimitives.F () ((wotsChainAdrs leafAdrs i.val).setHashAddress step) value ==
          honestLeafSig[i.val])
  | .wots (.fCollision i step value) =>
      decide (step < toyParams.w - 1) &&
        decide (chainStepsCore toyPrimitives.core honestMsg i.val ≤ step) &&
        (value != honestChainValue i step) &&
        (toyPrimitives.F () ((wotsChainAdrs leafAdrs i.val).setHashAddress step) value ==
          toyPrimitives.F () ((wotsChainAdrs leafAdrs i.val).setHashAddress step)
            (honestChainValue i step))

/-- A tag naming which constructor the extractor returned, so a canary can pin the branch. -/
def witnessTag : Option (XmssWitness toyParams toyPrimitives) → String
  | none => "none"
  | some (.hCollision z _) => s!"hCollision {z}"
  | some (.wots (.tlCollision _)) => "tlCollision"
  | some (.wots (.fPreimage i step _)) => s!"fPreimage {i.val} {step}"
  | some (.wots (.fCollision i step _)) => s!"fCollision {i.val} {step}"

def extract (sig : XmssSig toyParams toyPrimitives) :
    Option (XmssWitness toyParams toyPrimitives) :=
  findXmssWitness toyPrimitives leafIdx sig forgedMsg honestMsg () () baseAdrs

/-! ## The bundle behaves as advertised -/

/-- The five checks that assert the four bundle properties the canaries below lean on.  `F` drops
the low bit of its input and adds the address tweak.  The four honest leaf images are pairwise
distinct, so no two leaves share an honest partner.  `H` is order sensitive at the node the
collision canary names.  The tweak separates that node's address from the one at the same height
with the leaf index as its index, and from the one a height up.  And the tweak separates the
opened leaf's WOTS+ chain address from a neighbouring leaf's. -/
def checkToyBundle : IO Unit := do
  ensure "F drops the low bit and adds the address tweak"
    ((List.range 256).all fun x =>
      toyPrimitives.F () ((wotsChainAdrs leafAdrs 0).setHashAddress 4) (node (UInt8.ofNat x)) ==
        node ((UInt8.ofNat x >>> 1) ^^^
          toyTweak ((wotsChainAdrs leafAdrs 0).setHashAddress 4)))
  ensure "the four honest leaf images are pairwise distinct"
    (((List.range 4).map honestLeaf).eraseDups.length == 4)
  ensure "H is order sensitive at the node the collision canary names"
    (toyPrimitives.H () (xmssNodeAdrs baseAdrs 1 1) (honestLeaf 2) (honestLeaf 3) !=
      toyPrimitives.H () (xmssNodeAdrs baseAdrs 1 1) (honestLeaf 3) (honestLeaf 2))
  ensure "the tweak separates the collision node from the un-divided index and from a height up"
    ((toyTweak (xmssNodeAdrs baseAdrs 1 1) != toyTweak (xmssNodeAdrs baseAdrs 1 leafIdx)) &&
      (toyTweak (xmssNodeAdrs baseAdrs 1 1) != toyTweak (xmssNodeAdrs baseAdrs 2 1)))
  ensure "the tweak separates the opened leaf's chain address from a neighbouring leaf's"
    (toyTweak ((wotsChainAdrs leafAdrs 0).setHashAddress 4) !=
      toyTweak ((wotsChainAdrs (wotsLeafAdrs baseAdrs 2) 0).setHashAddress 4))

/-! ## Positive canaries -/

/-- The opened leaf differs from the honest one in bit `0`, which `H` drops, so the height-one node
is unchanged and the extractor returns the collision there between the honest child pair
`(leaf 2, leaf 3)` and the forged pair `(leaf 2, forged leaf 3)`.

The node is `(height 1, index 1)`.  The leaf index itself is `3`, and the opened leaf is that
node's *right* child, so the honest pair taken left to right is `(leaf 2, leaf 3)` rather than the
opened-leaf-first `(leaf 3, leaf 2)`.  This one fixture therefore separates the ancestor index from
the leaf index and the honest child order from the opened-leaf-first one; the last three checks
guard exactly that. -/
def checkNodeCollision : IO Unit := do
  ensure "the node forgery recovers the honest XMSS root"
    (xmssPkFromSig toyPrimitives leafIdx nodeForgery forgedMsg () baseAdrs ==
      xmssRoot toyPrimitives () () baseAdrs)
  ensure "the node forgery's recovered leaf differs from the honest one"
    (wotsPkFromSig toyPrimitives nodeForgery.wots forgedMsg () leafAdrs != honestLeaf leafIdx)
  let witness := extract nodeForgery
  ensure "the node forgery yields an H-collision at height 1" (witnessTag witness == "hCollision 1")
  match witness with
  | none => ensure "the node forgery yields a witness" false
  | some w =>
      ensure "the height-one collision satisfies its equation" (witnessHolds w)
      match w with
      | .hCollision z c =>
          ensure "the height-one collision names the ancestor index 1"
            (decide (leafIdx / 2 ^ z = 1))
          ensure "the height-one collision is between the expected pairs"
            ((honestChildPair z 1 == (honestLeaf 2, honestLeaf 3)) &&
              (c.1 == honestLeaf 2) && (c.2 != honestLeaf 3))
          ensure "the honest pair swapped does not satisfy the collision equation"
            (toyPrimitives.H () (xmssNodeAdrs baseAdrs z 1) (honestChildPair z 1).2
                (honestChildPair z 1).1 !=
              toyPrimitives.H () (xmssNodeAdrs baseAdrs z 1) c.1 c.2)
          ensure "the un-divided leaf index does not satisfy the collision equation"
            (toyPrimitives.H () (xmssNodeAdrs baseAdrs z leafIdx)
                (honestChildPair z leafIdx).1 (honestChildPair z leafIdx).2 !=
              toyPrimitives.H () (xmssNodeAdrs baseAdrs z leafIdx) c.1 c.2)
      | _ => ensure "the node forgery's witness is a collision" false

/-- The same leaf perturbed one bit higher collides at the tree root instead: the height-one node
changes, so the extractor climbs past it and returns the collision at height `h'`.  This is the
upper end of the `0 < z ≤ h'` range, and its index is the tree root's own index `0`. -/
def checkRootCollision : IO Unit := do
  ensure "the root forgery recovers the honest XMSS root"
    (xmssPkFromSig toyPrimitives leafIdx rootForgery forgedMsg () baseAdrs ==
      xmssRoot toyPrimitives () () baseAdrs)
  let witness := extract rootForgery
  ensure "the root forgery yields an H-collision at height 2, the tree height"
    (witnessTag witness == "hCollision 2")
  match witness with
  | none => ensure "the root forgery yields a witness" false
  | some w =>
      ensure "the tree-root collision satisfies its equation" (witnessHolds w)
      match w with
      | .hCollision z c =>
          ensure "the tree-root collision names index 0" (decide (leafIdx / 2 ^ z = 0))
          ensure "the tree-root collision's honest pair is the two height-one nodes"
            (honestChildPair z 0 ==
              (PerfectMerkleTree.merkleRoot (xmssLeaf toyPrimitives () () baseAdrs)
                  (xmssNodeHash toyPrimitives () baseAdrs) 1 0,
                PerfectMerkleTree.merkleRoot (xmssLeaf toyPrimitives () () baseAdrs)
                  (xmssNodeHash toyPrimitives () baseAdrs) 1 1))
          ensure "the tree-root collision's submitted pair differs in its right child only"
            ((c.1 == (honestChildPair z 0).1) && (c.2 != (honestChildPair z 0).2))
      | _ => ensure "the root forgery's witness is a collision" false

/-- Perturbing chain `3` in bit `0` leaves the `T_len` compression — the opened leaf — untouched
while changing the recovered chain-end vector, so the extractor takes its WOTS+ branch and returns
a `T_len` second preimage at `wotsPkAdrs leafAdrs`. -/
def checkTlCollision : IO Unit := do
  ensure "the T_len forgery recovers the honest XMSS root"
    (xmssPkFromSig toyPrimitives leafIdx tlForgery forgedMsg () baseAdrs ==
      xmssRoot toyPrimitives () () baseAdrs)
  ensure "the T_len forgery's recovered leaf is the honest one"
    (wotsPkFromSig toyPrimitives tlForgery.wots forgedMsg () leafAdrs == honestLeaf leafIdx)
  let witness := extract tlForgery
  ensure "the T_len forgery yields a T_len second preimage" (witnessTag witness == "tlCollision")
  match witness with
  | some w =>
      ensure "the T_len second preimage satisfies its equation" (witnessHolds w)
      match w with
      | .wots (.tlCollision recovered) =>
          ensure "the recovered chain ends differ from the honest ones exactly at chain 3"
            ((recovered[3]! != honestTops[3]!) &&
              ((List.range 3).all fun i => recovered[i]! == honestTops[i]!))
      | _ => ensure "the T_len forgery's witness is a T_len second preimage" false
  | none => ensure "the T_len forgery yields a witness" false

/-- The honest signature on the forged message recovers the honest leaf and the honest root, so the
extractor takes its WOTS+ branch, finds the recovered chain ends honest, and falls through to
chain `0` — the first chain whose forged digit `0` is below its honest digit `3`.  Advancing the
revealed value there by three steps lands on the honest revealed value, so the witness is an
`F`-preimage at hash-address `2`, the address the honest signer applied `F` at to reach it.

The three closing checks are the identifications: the address is `b - 1` and not `b`, the partner
is the honest signature on the *honest* message and not on the forged one, and the chain lives at
the opened leaf's WOTS+ address and not at a neighbour's. -/
def checkPreimage : IO Unit := do
  let honestForgery := xmssSigOf forgedMsgSig
  ensure "the honest signature on the forged message recovers the honest XMSS root"
    (xmssPkFromSig toyPrimitives leafIdx honestForgery forgedMsg () baseAdrs ==
      xmssRoot toyPrimitives () () baseAdrs)
  let witness := extract honestForgery
  ensure "it yields an F-preimage at chain 0, hash-address 2"
    (witnessTag witness == "fPreimage 0 2")
  match witness with
  | some w =>
      ensure "the F-preimage satisfies its equation" (witnessHolds w)
      match w with
      | .wots (.fPreimage i step value) =>
          ensure "the preimage address is one below the honest digit"
            (decide (step + 1 = chainStepsCore toyPrimitives.core honestMsg i.val))
          ensure "the honest digit is not itself the preimage address"
            (toyPrimitives.F ()
                ((wotsChainAdrs leafAdrs i.val).setHashAddress
                  (chainStepsCore toyPrimitives.core honestMsg i.val)) value !=
              honestLeafSig[i.val])
          ensure "the honest signature on the forged message is not the preimage target"
            ((honestLeafSig[i.val] != forgedMsgSig[i.val]) &&
              (toyPrimitives.F () ((wotsChainAdrs leafAdrs i.val).setHashAddress step) value !=
                forgedMsgSig[i.val]))
          ensure "a neighbouring leaf's chain address does not satisfy the preimage equation"
            (toyPrimitives.F ()
                ((wotsChainAdrs (wotsLeafAdrs baseAdrs 2) i.val).setHashAddress step) value !=
              honestLeafSig[i.val])
      | _ => ensure "the fall-through witness is an F-preimage" false
  | none => ensure "the honest signature on the forged message yields a witness" false

/-- Chain `0`'s signature value is chosen so that advancing it to the honest digit misses the
honest revealed value by bit `1`.  The two chains then diverge for one more step and collide at
hash-address `4`, one above the honest digit `3` — so the honest partner is the honest revealed
value *advanced by one step*, and not that value itself.

The last three checks are what separate the computed partner from the naive one: the advance is not
the identity, the naive partner fails the collision equation, and a neighbouring leaf's chain
address fails it too. -/
def checkChainCollision : IO Unit := do
  ensure "the chain forgery recovers the honest XMSS root"
    (xmssPkFromSig toyPrimitives leafIdx chainForgery forgedMsg () baseAdrs ==
      xmssRoot toyPrimitives () () baseAdrs)
  ensure "the chain forgery's recovered leaf is the honest one"
    (wotsPkFromSig toyPrimitives chainForgery.wots forgedMsg () leafAdrs == honestLeaf leafIdx)
  let witness := extract chainForgery
  ensure "the chain forgery yields an F-collision at chain 0, hash-address 4"
    (witnessTag witness == "fCollision 0 4")
  match witness with
  | some w =>
      ensure "the F-collision satisfies its equation" (witnessHolds w)
      match w with
      | .wots (.fCollision i step value) =>
          ensure "the collision sits strictly above the honest digit"
            (decide (chainStepsCore toyPrimitives.core honestMsg i.val < step))
          ensure "the honest partner is the advanced value, not the revealed one"
            (honestChainValue i step != honestLeafSig[i.val])
          ensure "the revealed value does not satisfy the collision equation"
            (toyPrimitives.F () ((wotsChainAdrs leafAdrs i.val).setHashAddress step) value !=
              toyPrimitives.F () ((wotsChainAdrs leafAdrs i.val).setHashAddress step)
                honestLeafSig[i.val])
          ensure "a neighbouring leaf's chain address does not satisfy the collision equation"
            (toyPrimitives.F ()
                ((wotsChainAdrs (wotsLeafAdrs baseAdrs 2) i.val).setHashAddress step) value !=
              toyPrimitives.F ()
                ((wotsChainAdrs (wotsLeafAdrs baseAdrs 2) i.val).setHashAddress step)
                (chain toyPrimitives () (wotsChainAdrs (wotsLeafAdrs baseAdrs 2) i.val)
                  (wotsSign toyPrimitives honestMsg () () (wotsLeafAdrs baseAdrs 2))[i.val]
                  (chainStepsCore toyPrimitives.core honestMsg i.val)
                  (step - chainStepsCore toyPrimitives.core honestMsg i.val)))
      | _ => ensure "the chain forgery's witness is an F-collision" false
  | none => ensure "the chain forgery yields a witness" false

/-! ## Negative canaries -/

/-- The honest signature on the *honest* message, extracted against that same message.  It
recovers the honest root and the honest leaf, so the extractor takes its WOTS+ branch — and returns
`none` anyway.  The two signatures `findWotsWitness` compares are the same one here, so its `T_len`
test passes and the search reaches the chains; there, at `msg = msg'`, a chain's forged and honest
digits are the same number, so `findWotsChainWitness`'s `a < b` guard fails at every index and
`findSome?` runs out.  What this fixture exhibits is therefore `findXmssWitness_isSome`'s
`hne : msg ≠ msg'` being necessary: a signature can recover the honest root and still yield no
witness when the second message is not distinct from the first.

`none` on its own does not say which branch produced it — the Merkle branch returns `none` too — so
the branch is pinned twice over.  The recovered leaf is checked equal to the honest one, which is
the test the extractor branches on; and the same signature at the same leaf is re-extracted against
a *distinct* second message, where the guard does fire.  There the search reaches chain `1`, whose
digit is `0` under `honestMsg` and `15` under `forgedMsg`, and returns the `F`-preimage at
hash-address `14` — a WOTS+ witness, never an `H`-collision.  Neither outcome is read off a
rendered tag: one is `Option.isNone`, the other a constructor pattern. -/
def checkHonestSignature : IO Unit := do
  let honestSig := xmssSign toyPrimitives honestMsg () () baseAdrs leafIdx
  ensure "the honest signature recovers the honest XMSS root"
    (xmssPkFromSig toyPrimitives leafIdx honestSig honestMsg () baseAdrs ==
      xmssRoot toyPrimitives () () baseAdrs)
  ensure "the honest signature's recovered leaf is the honest one, so the WOTS+ branch is taken"
    (wotsPkFromSig toyPrimitives honestSig.wots honestMsg () leafAdrs == honestLeaf leafIdx)
  ensure "at a second message equal to the first the extractor returns nothing"
    (findXmssWitness toyPrimitives leafIdx honestSig honestMsg honestMsg () () baseAdrs).isNone
  match findXmssWitness toyPrimitives leafIdx honestSig honestMsg forgedMsg () () baseAdrs with
  | some (.wots (.fPreimage i step value)) =>
      ensure "a distinct second message fires the guard at chain 1, hash-address 14"
        ((i.val == 1) && (step == 14))
      ensure "and that F-preimage holds against the honest signature on the distinct message"
        (toyPrimitives.F () ((wotsChainAdrs leafAdrs i.val).setHashAddress step) value ==
          forgedMsgSig[i.val])
  | _ =>
      ensure "a distinct second message yields a WOTS+ F-preimage, never an H-collision" false

/-- Both halves of what the extractor does on a signature that misses the honest root.  The branch
is chosen by the recovered *leaf*, so the root mismatch by itself decides nothing, and the two
halves come out differently.

`badForgery` perturbs chain `3` in bit `3`, moving the opened leaf in bit `2` — far enough that the
height-one node and the tree root both change.  Its recovered leaf differs from the honest one, so
the Merkle branch is taken; the two openings never meet and it returns `none`.  That is not an
accident of this fixture: `PerfectMerkleTree.findCollisionAddressed` descends from the root and
returns `some` only where the two openings first differ under an equal parent, so a `some` already
implies the root match.

`authForgery` keeps the honest WOTS+ signature on the forged message and perturbs the height-zero
authentication-path entry instead.  Its recovered leaf is the honest one, so the *WOTS+* branch is
taken although the climb misses the root — and the witness it returns is valid, its guard being the
leaf test, which is `findWotsWitness_sound`'s own hypothesis.  So a missed root does not mean
`none`: over a 768-case sweep — sixteen chain-`3` perturbations by three authentication-path
choices, level `0`, level `1` or none, by sixteen path perturbations, all of them extracted here
against a second message distinct from the first — 608 cases miss the honest root, the 552 of those
that take the Merkle branch return `none`, the 56 that take the WOTS+ branch return a witness, and
none of the 768 returns an invalid one.  Cases, not distinct signatures: the path mask is inert at
the `none` level and mask `0` reproduces the honest path at every level, so the 768 realise 496
signatures.  Distinctness is doing work in the WOTS+ half — re-extract `authForgery` against
`forgedMsg` itself and it returns `none`, with the same missed root and the same honest leaf.

This is the shape `findXmssWitness_sound`'s root hypothesis is *stated against*, though as the
paragraph above shows the Merkle branch does not need it.  Both halves are a *weaker* gap than the
WOTS+ and FORS extractors have: those return a `T_len` witness that then fails its own equation,
whereas neither branch here returns an invalid witness. -/
def checkMalformedForgery : IO Unit := do
  ensure "the malformed forgery does not recover the honest XMSS root"
    (xmssPkFromSig toyPrimitives leafIdx badForgery forgedMsg () baseAdrs !=
      xmssRoot toyPrimitives () () baseAdrs)
  ensure "the malformed forgery's recovered leaf differs from the honest one"
    (wotsPkFromSig toyPrimitives badForgery.wots forgedMsg () leafAdrs != honestLeaf leafIdx)
  ensure "the malformed forgery yields no witness" (extract badForgery).isNone
  ensure "the perturbed authentication path does not recover the honest XMSS root either"
    (xmssPkFromSig toyPrimitives leafIdx authForgery forgedMsg () baseAdrs !=
      xmssRoot toyPrimitives () () baseAdrs)
  ensure "the perturbed authentication path leaves the recovered leaf honest"
    (wotsPkFromSig toyPrimitives authForgery.wots forgedMsg () leafAdrs == honestLeaf leafIdx)
  match extract authForgery with
  | some (.wots (.fPreimage i step value)) =>
      ensure "the perturbed authentication path yields the F-preimage at chain 0, hash-address 2"
        ((i.val == 0) && (step == 2))
      ensure "and that witness is valid, in spite of the missed root"
        (witnessHolds (.wots (.fPreimage i step value)))
  | _ =>
      ensure "the perturbed authentication path yields a valid WOTS+ witness, not none" false

/-- `witnessHolds` itself has to be able to fail, and has to accept.  Eighteen witnesses are
fabricated: six `hCollision`s, three `tlCollision`s, four `fPreimage`s and five `fCollision`s.
Four — one per constructor — are checked *accepted*; the other fourteen are rejected.

`witnessHolds` has thirteen conjuncts in all: four on `hCollision`, two on `tlCollision`, three on
`fPreimage`, four on `fCollision`.  The fourteen rejections falsify all thirteen —

* the `hCollision` hash equation, by a collision whose `H` image differs and by the genuine
  collision with its two children swapped — the second only because `H` is order sensitive, so it
  is the left-to-right identification that rejects it;
* the `hCollision` distinctness, by a collision submitted at the honest child pair itself: both its
  bounds hold and its hash equation is an identity, so the distinctness is the only conjunct it
  fails;
* the `0 < z` bound, by the genuine collision moved to height zero, where `xmssHonestChildren`'s
  `z - 1` would truncate and the address is not listed in any ledger;
* the `z ≤ h'` bound, by the genuine collision moved above the tree height;
* the `tlCollision` distinctness, by a `T_len` witness at the honest chain ends themselves;
* the `tlCollision` hash equality, by a chain-end vector whose compression differs;
* the `fPreimage` address, by a preimage at the honest digit rather than one below it;
* the `fPreimage` equation, by a preimage of the wrong value;
* the `fPreimage` step bound, by a preimage at hash-address `w - 1`;
* the `fCollision` step bound, by the genuine collision moved to hash-address `w - 1`;
* the `fCollision` digit bound, by a collision below the honest digit;
* the `fCollision` distinctness, by a collision submitted at the honest chain value itself;
* the `fCollision` equation, by a collision whose `F` image differs.

Eleven of the fourteen rejections fail exactly one conjunct.  The two out-of-range heights fail
two, because the honest child pair is recomputed at whatever height the witness names, so their
hash equation misses as well.  The `fPreimage` at hash-address `w - 1` fails all three: its step
bound cannot be broken on its own — `step + 1 = b` and `chainStepsCore_le` already imply it, which
is why `HashSig.SLHDSA.Security.WotsWitnesses` records that conjunct as redundant and kept — and
moving the address also moves the tweak, so the preimage equation misses too.

Every other conjunct of the three WOTS+ branches *is* falsified on its own, including both of the
`fCollision` step bounds: the collision moved to `w - 1` keeps the honest partner it collides with,
and the one below the honest digit collides with the partner truncated subtraction names there. -/
def checkFabricatedWitnesses : IO Unit := do
  let zero : Fin toyParams.len := ⟨0, by decide⟩
  let genuinePair : toyPrimitives.Y × toyPrimitives.Y :=
    (honestLeaf 2, node (byteOf (honestLeaf 3) ^^^ 1))
  let topsWith : UInt8 → Vector toyPrimitives.Y toyParams.len := fun x =>
    Vector.ofFn fun i : Fin toyParams.len => if i.val = 3 then node x else honestTops[i.val]
  -- `hCollision`
  ensure "the genuine height-one collision is accepted"
    (witnessHolds (.hCollision 1 genuinePair))
  ensure "a fabricated collision with a different H image is rejected"
    (witnessHolds (.hCollision 1 (honestLeaf 2, node (byteOf (honestLeaf 3) ^^^ 2))) == false)
  ensure "a collision at height zero is rejected"
    (witnessHolds (.hCollision 0 genuinePair) == false)
  ensure "a collision above the tree height is rejected"
    (witnessHolds (.hCollision 3 genuinePair) == false)
  ensure "the genuine collision with its two children swapped is rejected"
    (witnessHolds (.hCollision 1 (genuinePair.2, genuinePair.1)) == false)
  ensure "the honest child pair is not the opened-leaf-first pair"
    (honestChildPair 1 (leafIdx / 2) != (honestLeaf 3, honestLeaf 2))
  ensure "a collision submitted at the honest child pair itself is rejected"
    (witnessHolds (.hCollision 1 (honestChildPair 1 (leafIdx / 2))) == false)
  -- `tlCollision`
  ensure "the genuine T_len second preimage is accepted"
    (witnessHolds (.wots (.tlCollision (topsWith (byteOf honestTops[3] ^^^ 1)))))
  ensure "a fabricated T_len second preimage equal to the honest chain ends is rejected"
    (witnessHolds (.wots (.tlCollision honestTops)) == false)
  ensure "a fabricated T_len second preimage that compresses differently is rejected"
    (witnessHolds (.wots (.tlCollision (topsWith (byteOf honestTops[3] ^^^ 2)))) == false)
  -- `fPreimage`
  ensure "the genuine F-preimage is accepted"
    (witnessHolds (.wots (.fPreimage zero 2 (node 179))))
  ensure "a fabricated preimage at the honest digit rather than one below it is rejected"
    (witnessHolds (.wots (.fPreimage zero 3 (node 116))) == false)
  ensure "a fabricated preimage of the wrong value is rejected"
    (witnessHolds (.wots (.fPreimage zero 2 (node 180))) == false)
  ensure "a fabricated preimage at hash-address w - 1 is rejected"
    (witnessHolds (.wots (.fPreimage zero 15 (node 179))) == false)
  -- `fCollision`
  ensure "the genuine F-collision is accepted"
    (witnessHolds (.wots (.fCollision zero 4 (node 91))))
  ensure "a fabricated collision at hash-address w - 1 is rejected"
    (witnessHolds (.wots (.fCollision zero 15
      (node (byteOf (honestChainValue zero 15) ^^^ 1)))) == false)
  ensure "a fabricated collision below the honest digit is rejected"
    (witnessHolds (.wots (.fCollision zero 2
      (node (byteOf (honestChainValue zero 2) ^^^ 1)))) == false)
  ensure "a fabricated collision at the honest chain value itself is rejected"
    (witnessHolds (.wots (.fCollision zero 4 (honestChainValue zero 4))) == false)
  ensure "a fabricated collision whose F image differs is rejected"
    (witnessHolds (.wots (.fCollision zero 4 (node 92))) == false)

/-! ## Statement pins at the toy bundle -/

/-- A shape pin for `xmssPkFromSig_cases`: at a signature which recovers the honest XMSS root, one
of the two branches holds.  The collision branch is restated with its hash equation moved in front
of the side conditions `xmssPkFromSig_cases` states before it, so it has to be reassembled rather
than passed through, and every conjunct the theorem supplies is bound and used here.  That is not
the order the games read: `SM_DT_TCR_SourceFinalValidity`'s experiment tests its side condition
first and the hash equation last (`SMDTTCRFinalValidity.lean:105`).  Deleting the `H` equality from
the second disjunct, which is the security content of that branch, breaks this pin. -/
example (sig : XmssSig toyParams toyPrimitives) (msg : toyPrimitives.Y) (idx : ℕ)
    (hidx : idx < 2 ^ toyParams.hp)
    (hroot : xmssPkFromSig toyPrimitives idx sig msg () baseAdrs =
      xmssRoot toyPrimitives () () baseAdrs) :
    wotsPkFromSig toyPrimitives sig.wots msg () (wotsLeafAdrs baseAdrs idx) =
        wotsPkGen toyPrimitives () () (wotsLeafAdrs baseAdrs idx) ∨
      (∃ (z : ℕ) (c : toyPrimitives.Y × toyPrimitives.Y),
        toyPrimitives.H () (xmssNodeAdrs baseAdrs z (idx / 2 ^ z))
              (xmssHonestChildren toyPrimitives () () baseAdrs z (idx / 2 ^ z)).1
              (xmssHonestChildren toyPrimitives () () baseAdrs z (idx / 2 ^ z)).2 =
            toyPrimitives.H () (xmssNodeAdrs baseAdrs z (idx / 2 ^ z)) c.1 c.2 ∧
          0 < z ∧ z ≤ toyParams.hp ∧
            xmssHonestChildren toyPrimitives () () baseAdrs z (idx / 2 ^ z) ≠ c) := by
  rcases xmssPkFromSig_cases toyPrimitives idx hidx sig msg () () baseAdrs hroot with
    hwots | ⟨z, c, hz, hzh, hne, hcoll⟩
  · exact Or.inl hwots
  · exact Or.inr ⟨z, c, hcoll, hz, hzh, hne⟩

/-- The extractor's soundness at the toy bundle, for every signature and message pair at a leaf
inside the tree: the only hypothesis is the root match.  It is stated schematically rather than at
`nodeForgery` because the library definitions are not exposed, so a kernel `decide` on the concrete
root match does not reduce; that instance of the hypothesis is what `checkNodeCollision` evaluates
at run time. -/
example (sig : XmssSig toyParams toyPrimitives) (msg msg' : toyPrimitives.Y) (idx : ℕ)
    (hidx : idx < 2 ^ toyParams.hp)
    (hroot : xmssPkFromSig toyPrimitives idx sig msg () baseAdrs =
      xmssRoot toyPrimitives () () baseAdrs)
    {w : XmssWitness toyParams toyPrimitives}
    (hw : findXmssWitness toyPrimitives idx sig msg msg' () () baseAdrs = some w) :
    w.Valid () () baseAdrs idx msg' :=
  findXmssWitness_sound toyPrimitives idx hidx sig msg msg' () () baseAdrs hroot hw

/-- Extractor completeness at the toy bundle: on two distinct messages, at a leaf inside the tree,
against a signature that recovers the honest root, the search always returns a witness.  The byte
laws are discharged from the toy bundle's identity node encoding. -/
example (sig : XmssSig toyParams toyPrimitives) (idx : ℕ) (hidx : idx < 2 ^ toyParams.hp)
    (hroot : xmssPkFromSig toyPrimitives idx sig forgedMsg () baseAdrs =
      xmssRoot toyPrimitives () () baseAdrs) :
    (findXmssWitness toyPrimitives idx sig forgedMsg honestMsg () () baseAdrs).isSome :=
  findXmssWitness_isSome toyValid toyPrimitives toyByteLaws idx hidx sig forgedMsg honestMsg
    () () baseAdrs forgedMsg_ne_honestMsg hroot

/-- The identification a source-final-validity game needs, read off the extractor's soundness lemma
alone: a returned `hCollision` collides with the honest child pair at the node it names, and not
with an unconstrained second pair.  The proof is the intended downstream path — the extractor bodies
are not exposed, so the unfolding equation is what a consumer rewrites with. -/
example (sig : XmssSig toyParams toyPrimitives) (msg msg' : toyPrimitives.Y) (idx : ℕ)
    (hidx : idx < 2 ^ toyParams.hp) (z : ℕ) (c : toyPrimitives.Y × toyPrimitives.Y)
    (hroot : xmssPkFromSig toyPrimitives idx sig msg () baseAdrs =
      xmssRoot toyPrimitives () () baseAdrs)
    (hw : findXmssWitness toyPrimitives idx sig msg msg' () () baseAdrs =
      some (.hCollision z c)) :
    toyPrimitives.H () (xmssNodeAdrs baseAdrs z (idx / 2 ^ z))
        (xmssHonestChildren toyPrimitives () () baseAdrs z (idx / 2 ^ z)).1
        (xmssHonestChildren toyPrimitives () () baseAdrs z (idx / 2 ^ z)).2 =
      toyPrimitives.H () (xmssNodeAdrs baseAdrs z (idx / 2 ^ z)) c.1 c.2 := by
  have h := findXmssWitness_sound toyPrimitives idx hidx sig msg msg' () () baseAdrs hroot hw
  rw [XmssWitness.valid_hCollision] at h
  exact h.2.2.2

/-- The same for the WOTS+ branch: a returned `wots` witness attacks the honest WOTS+ key material
at the opened leaf, computed from the honest secret seed and the honest message — not carried by
the witness.  This is the identification that makes the branch a named attack rather than an
arbitrary one. -/
example (sig : XmssSig toyParams toyPrimitives) (msg msg' : toyPrimitives.Y) (idx : ℕ)
    (hidx : idx < 2 ^ toyParams.hp) (u : WotsWitness toyParams toyPrimitives)
    (hroot : xmssPkFromSig toyPrimitives idx sig msg () baseAdrs =
      xmssRoot toyPrimitives () () baseAdrs)
    (hw : findXmssWitness toyPrimitives idx sig msg msg' () () baseAdrs = some (.wots u)) :
    u.Valid () (wotsLeafAdrs baseAdrs idx)
      (wotsPkGenTops toyPrimitives () () (wotsLeafAdrs baseAdrs idx))
      (wotsSign toyPrimitives msg' () () (wotsLeafAdrs baseAdrs idx)) msg' := by
  have h := findXmssWitness_sound toyPrimitives idx hidx sig msg msg' () () baseAdrs hroot hw
  rwa [XmssWitness.valid_wots] at h

/-- The one pin for the three declarations nothing else in the tree elaborates: the two extractor
shape equations and `xmssPkFromSig_forgeryCases`.

The shape equations are used as the dichotomy they encode — every run of the extractor is one of
the two branches, and which one is decided by the leaf test alone, with no root hypothesis in
sight.  `xmssPkFromSig_forgeryCases` is unfolded to the literal four-way split, through
`WotsWitness.Valid`'s three `Iff.rfl` equations; that four-way form is the propositional one a
later `conseq` post-condition reads, and it is the only place the correspondence with
`valid_TCRTRH`, `valid_TCRPKCO` and the two resolutions of `valid_WOTSTWES` is a theorem rather
than prose.  Deleting a conjunct from any of the three would otherwise go unnoticed. -/
example (sig : XmssSig toyParams toyPrimitives) (msg msg' : toyPrimitives.Y) (idx : ℕ)
    (hidx : idx < 2 ^ toyParams.hp) (hne : msg ≠ msg')
    (hroot : xmssPkFromSig toyPrimitives idx sig msg () baseAdrs =
      xmssRoot toyPrimitives () () baseAdrs) :
    (findXmssWitness toyPrimitives idx sig msg msg' () () baseAdrs =
          (findWotsWitness toyPrimitives sig.wots msg
            (wotsSign toyPrimitives msg' () () (wotsLeafAdrs baseAdrs idx)) msg' ()
            (wotsLeafAdrs baseAdrs idx)).map .wots ∨
        findXmssWitness toyPrimitives idx sig msg msg' () () baseAdrs =
          (PerfectMerkleTree.findCollision (xmssLeaf toyPrimitives () () baseAdrs)
            (xmssNodeHash toyPrimitives () baseAdrs) idx
            (wotsPkFromSig toyPrimitives sig.wots msg () (wotsLeafAdrs baseAdrs idx))
            sig.auth.toList).map fun w => .hCollision w.1 w.2.2) ∧
      ((∃ (z : ℕ) (c : toyPrimitives.Y × toyPrimitives.Y), 0 < z ∧ z ≤ toyParams.hp ∧
            xmssHonestChildren toyPrimitives () () baseAdrs z (idx / 2 ^ z) ≠ c ∧
            toyPrimitives.H () (xmssNodeAdrs baseAdrs z (idx / 2 ^ z))
                (xmssHonestChildren toyPrimitives () () baseAdrs z (idx / 2 ^ z)).1
                (xmssHonestChildren toyPrimitives () () baseAdrs z (idx / 2 ^ z)).2 =
              toyPrimitives.H () (xmssNodeAdrs baseAdrs z (idx / 2 ^ z)) c.1 c.2) ∨
        (∃ recovered : Vector toyPrimitives.Y toyParams.len,
            recovered ≠ wotsPkGenTops toyPrimitives () () (wotsLeafAdrs baseAdrs idx) ∧
            toyPrimitives.Tl () (wotsPkAdrs (wotsLeafAdrs baseAdrs idx)) recovered.toList =
              toyPrimitives.Tl () (wotsPkAdrs (wotsLeafAdrs baseAdrs idx))
                (wotsPkGenTops toyPrimitives () () (wotsLeafAdrs baseAdrs idx)).toList) ∨
        (∃ (i : Fin toyParams.len) (step : ℕ) (value : toyPrimitives.Y),
            step < toyParams.w - 1 ∧ step + 1 = chainStepsCore toyPrimitives.core msg' i.val ∧
            toyPrimitives.F ()
                ((wotsChainAdrs (wotsLeafAdrs baseAdrs idx) i.val).setHashAddress step) value =
              (wotsSign toyPrimitives msg' () () (wotsLeafAdrs baseAdrs idx))[i.val]) ∨
        ∃ (i : Fin toyParams.len) (step : ℕ) (value : toyPrimitives.Y),
          step < toyParams.w - 1 ∧ chainStepsCore toyPrimitives.core msg' i.val ≤ step ∧
          value ≠ chain toyPrimitives () (wotsChainAdrs (wotsLeafAdrs baseAdrs idx) i.val)
              (wotsSign toyPrimitives msg' () () (wotsLeafAdrs baseAdrs idx))[i.val]
              (chainStepsCore toyPrimitives.core msg' i.val)
              (step - chainStepsCore toyPrimitives.core msg' i.val) ∧
          toyPrimitives.F ()
              ((wotsChainAdrs (wotsLeafAdrs baseAdrs idx) i.val).setHashAddress step) value =
            toyPrimitives.F ()
              ((wotsChainAdrs (wotsLeafAdrs baseAdrs idx) i.val).setHashAddress step)
              (chain toyPrimitives () (wotsChainAdrs (wotsLeafAdrs baseAdrs idx) i.val)
                (wotsSign toyPrimitives msg' () () (wotsLeafAdrs baseAdrs idx))[i.val]
                (chainStepsCore toyPrimitives.core msg' i.val)
                (step - chainStepsCore toyPrimitives.core msg' i.val))) := by
  refine ⟨?_, ?_⟩
  · by_cases hleaf : xmssLeaf toyPrimitives () () baseAdrs idx =
        wotsPkFromSig toyPrimitives sig.wots msg () (wotsLeafAdrs baseAdrs idx)
    · exact Or.inl
        (findXmssWitness_eq_wots_of_leaf toyPrimitives idx sig msg msg' () () baseAdrs hleaf)
    · exact Or.inr
        (findXmssWitness_eq_node_of_leaf_ne toyPrimitives idx sig msg msg' () () baseAdrs hleaf)
  · rcases xmssPkFromSig_forgeryCases toyValid toyPrimitives toyByteLaws idx hidx sig msg msg'
      () () baseAdrs hne hroot with hcoll | ⟨w, hw⟩
    · exact Or.inl hcoll
    · cases w with
      | tlCollision recovered =>
          rw [WotsWitness.valid_tlCollision] at hw
          exact Or.inr (Or.inl ⟨recovered, hw⟩)
      | fPreimage i step value =>
          rw [WotsWitness.valid_fPreimage] at hw
          exact Or.inr (Or.inr (Or.inl ⟨i, step, value, hw⟩))
      | fCollision i step value =>
          rw [WotsWitness.valid_fCollision] at hw
          exact Or.inr (Or.inr (Or.inr ⟨i, step, value, hw⟩))

/-! ## Ledger pins on approved profiles -/

/-- Two layers of height two, two FORS trees of height two, `w = 16`, `len = 4`. -/
def twoLayerParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 2, k := 2, lgw := 4 }

def twoLayer : ValidatedParams := ⟨twoLayerParams, by decide⟩

theorem twoLayerApprovedAddressBounds : ApprovedAddressBounds twoLayerParams :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    by decide, by decide⟩

/-- Every XMSS internal node an `hCollision` witness can name at a reachable layer position is a
listed `xmssH` target. -/
example (pos : LayerPosition twoLayer) {z : ℕ} (hz : 0 < z) (hzh : z ≤ twoLayerParams.hp) :
    xmssNodeAdrs pos.toAdrs z (pos.leaf.val / 2 ^ z) ∈ xmssNodeAddresses twoLayer :=
  mem_xmssNodeAddresses_of_leaf pos hz hzh

/-- The WOTS+ base address a `wots` witness names at a reachable layer position is the ledger's own
`wotsInstanceAdrs`, so the three WOTS+ ledger lemmas apply to it unchanged.  Here for the `T_len`
compression address, which `mem_wotsPkAddresses` already lists. -/
example (pos : LayerPosition twoLayer) :
    wotsPkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) ∈ wotsPkAddresses twoLayer := by
  rw [wotsLeafAdrs_eq_wotsInstanceAdrs]
  exact mem_wotsPkAddresses twoLayer pos

/-- And for a chain-step address, which `mem_wotsStepAddresses_of_lt` lists. -/
example (pos : LayerPosition twoLayer) (i : Fin twoLayerParams.len) {t : ℕ}
    (ht : t < twoLayerParams.w - 1) :
    (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val).setHashAddress t ∈
      wotsStepAddresses twoLayer := by
  rw [wotsLeafAdrs_eq_wotsInstanceAdrs]
  exact mem_wotsStepAddresses_of_lt pos i ht

/-- Under the SHA-2 encoder at an approved-bounds profile, distinct XMSS internal-node coordinates
carry distinct encoded tweaks, in the bounded coordinate shape a witness produces. -/
example {coord coord' : LayerTreeCoord twoLayer} {z z' j j' : ℕ}
    (hz : 0 < z) (hzh : z ≤ twoLayerParams.hp) (hj : j < 2 ^ (twoLayerParams.hp - z))
    (hz' : 0 < z') (hzh' : z' ≤ twoLayerParams.hp) (hj' : j' < 2 ^ (twoLayerParams.hp - z'))
    (hkey : (sha2Primitives twoLayerParams).adrsToKey (xmssNodeAdrs coord.toAdrs z j) =
      (sha2Primitives twoLayerParams).adrsToKey (xmssNodeAdrs coord'.toAdrs z' j')) :
    coord = coord' ∧ z = z' ∧ j = j' :=
  xmssNodeAdrsKey_injective
    (sha2EncodedTargetLedgerConditions twoLayer twoLayerApprovedAddressBounds)
    hz hzh hj hz' hzh' hj' hkey

/-- The same under the SHAKE encoder. -/
example {coord coord' : LayerTreeCoord twoLayer} {z z' j j' : ℕ}
    (hz : 0 < z) (hzh : z ≤ twoLayerParams.hp) (hj : j < 2 ^ (twoLayerParams.hp - z))
    (hz' : 0 < z') (hzh' : z' ≤ twoLayerParams.hp) (hj' : j' < 2 ^ (twoLayerParams.hp - z'))
    (hkey : (shakePrimitives twoLayerParams).adrsToKey (xmssNodeAdrs coord.toAdrs z j) =
      (shakePrimitives twoLayerParams).adrsToKey (xmssNodeAdrs coord'.toAdrs z' j')) :
    coord = coord' ∧ z = z' ∧ j = j' :=
  xmssNodeAdrsKey_injective (shakeEncodedTargetLedgerConditions twoLayer
    twoLayerApprovedAddressBounds.toCanonicalAddressBounds) hz hzh hj hz' hzh' hj' hkey

/-! ## The encoded-distinctness hypothesis is load-bearing

`Concrete.sha2AdrsKey` sends every address outside its checked domain to the all-zero key, which is
the genuine key of the all-zero WOTS-hash address rather than a sentinel.  On a profile whose
layer-zero tree indices overflow the compressed eight-byte tree field, two distinct listed XMSS
internal-node targets therefore share a tweak, and `xmssNodeAdrsKey_injective` is false without its
`EncodedTargetLedgerConditions` argument.

`HashSigTest.SLHDSA.EncodedTargets.deep_sha2_conditions_false` already refutes the *hypothesis* at
the same profile and the same ledger.  What is stated here is the refutation of this module's
*conclusion*, which is a different statement: it exhibits the two coordinates and their shared key
rather than deriving a contradiction from the conditions record.  The profile itself, its
tree-index bound, and the SHA-2 out-of-domain fallback come from
`HashSigTest.SLHDSA.EncoderFixtures`, which shares them with the encoded-target canaries. -/

example : deep.params.hp = 9 := by decide
example : layerTreeHeight deep 0 = 90 := by decide

/-- A layer-zero tree coordinate of the `deep` profile at a tree index the compressed field cannot
hold. -/
-- Exposed: `deepCoord_tree` closes by `rfl`, which needs this to reduce.
@[expose] def deepCoord (t : ℕ) (ht : t < 2 ^ 64 + 2) : LayerTreeCoord deep :=
  ⟨⟨0, by decide⟩, ⟨t, deep_tree_bound t ht⟩⟩

theorem deepCoord_tree (t : ℕ) (ht : t < 2 ^ 64 + 2) :
    (xmssNodeAdrs (deepCoord t ht).toAdrs 1 0).tree = t := rfl

/-- Two distinct listed XMSS internal-node targets of the `deep` profile carry the same encoded
SHA-2 tweak, namely the all-zero key: their layer-zero tree indices exceed the compressed
eight-byte tree field, and the checked compression falls back to that key rather than to a
sentinel. -/
theorem deep_xmssNode_sha2_alias :
    ∃ c₁ c₂ : LayerTreeCoord deep,
      xmssNodeAdrs c₁.toAdrs 1 0 ∈ xmssNodeAddresses deep ∧
        xmssNodeAdrs c₂.toAdrs 1 0 ∈ xmssNodeAddresses deep ∧
        c₁ ≠ c₂ ∧
        (sha2Primitives deep.params).adrsToKey (xmssNodeAdrs c₁.toAdrs 1 0) =
          (sha2Primitives deep.params).adrsToKey (xmssNodeAdrs c₂.toAdrs 1 0) := by
  have hz : (0 : ℕ) < 1 := by norm_num
  have hzh : (1 : ℕ) ≤ deep.params.hp := by decide
  have hidx : (0 : ℕ) < 2 ^ (deep.params.hp - 1) := Nat.two_pow_pos _
  refine ⟨deepCoord (2 ^ 64) (by norm_num), deepCoord (2 ^ 64 + 1) (by norm_num),
    mem_xmssNodeAddresses deep _ hz hzh hidx, mem_xmssNodeAddresses deep _ hz hzh hidx, ?_, ?_⟩
  · intro h
    have h₁ := deepCoord_tree (2 ^ 64) (by norm_num)
    have h₂ := deepCoord_tree (2 ^ 64 + 1) (by norm_num)
    rw [h] at h₁
    omega
  · have hfits : ∀ t : ℕ, 2 ^ 64 ≤ t → ∀ ht : t < 2 ^ 64 + 2,
        Adrs.Fits 8 (xmssNodeAdrs (deepCoord t ht).toAdrs 1 0).tree = false := by
      intro t hle ht
      rw [deepCoord_tree, Adrs.Fits, decide_eq_false_iff_not, not_lt]
      norm_num
      omega
    rw [adrsToKey_sha2, adrsToKey_sha2,
      sha2AdrsKey_eq_zero_of_tree_overflow _ (hfits (2 ^ 64) (le_refl _) _),
      sha2AdrsKey_eq_zero_of_tree_overflow _ (hfits (2 ^ 64 + 1) (by norm_num) _)]

/-- Consequently `xmssNodeAdrsKey_injective`'s conclusion is false for the SHA-2 bundle at this
profile: its `EncodedTargetLedgerConditions` hypothesis is load-bearing. -/
theorem deep_xmssNode_sha2_not_injective :
    ¬ ∀ (c₁ c₂ : LayerTreeCoord deep),
        (sha2Primitives deep.params).adrsToKey (xmssNodeAdrs c₁.toAdrs 1 0) =
          (sha2Primitives deep.params).adrsToKey (xmssNodeAdrs c₂.toAdrs 1 0) → c₁ = c₂ := by
  intro hinj
  obtain ⟨c₁, c₂, _, _, hne, hkey⟩ := deep_xmssNode_sha2_alias
  exact hne (hinj c₁ c₂ hkey)

def main : IO Unit := do
  checkToyBundle
  checkNodeCollision
  checkRootCollision
  checkTlCollision
  checkPreimage
  checkChainCollision
  checkHonestSignature
  checkMalformedForgery
  checkFabricatedWitnesses
  IO.println "SLH-DSA XMSS witness tests: PASS \
    (H-collision extraction at both tree heights, T_len second preimage, F-preimage and \
     F-collision extraction at the opened leaf, the honest-signature, malformed-input, and \
     fabricated-witness canaries)"

end SLHDSA.XmssWitnessesTest

def main : IO Unit := SLHDSA.XmssWitnessesTest.main
