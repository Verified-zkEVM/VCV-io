/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.EncodedTargets
public import HashSig.SLHDSA.Security.ForsWitnesses
public import HashSigTest.SLHDSA.EncoderFixtures

/-!
# SLH-DSA FORS witness canaries

Executable checks that the FORS witness extractor really produces witnesses, and that what it
produces really satisfies the collision or preimage equation — evaluated at the values, not
restated from the theorems.

No collision is exhibitable under an approved instantiation, so the extraction canaries run over a
toy primitive bundle whose `Thash` folds its input with a two-bit shift and drops the low bit of
every node, then exclusive-ors a per-address tweak.  Two properties of that bundle carry the
canaries: it collides readily, and it is *order sensitive* and *address sensitive*, so a witness
stated with its two children swapped, or at a neighbouring address, fails by evaluation.  The
witness lemmas are stated for an arbitrary `Primitives` bundle, so this is in scope; it is a
falsifiability fixture, not a claim about any approved profile.

Over that bundle the checks build honest FORS key material at a two-tree profile of height two and
four forgeries that all recover the honest FORS public key, and confirm that the extractor returns
the `H`-collision at height one, the `H`-collision at the tree height `a = 2`, the `F`-preimage,
and the `T_k` second preimage respectively, each satisfying its equation by evaluation — including
the three identifications the games need: that the collision partner is the honest child pair at
the node named, that its two children are taken left to right rather than opened-leaf first, and
that both the collision and the preimage name the *global* FORS leaf index rather than the
tree-local one.  Two negative canaries close the other direction: an honest signature yields no
collision at any tree, and a forgery whose recovered public key differs yields a `T_k` witness that
fails its own validity check — which is exactly why `findForsWitness_sound` carries the public-key
hypothesis.  A third group fabricates nine witnesses — eight at tree `1`, and one `T_k` witness,
which carries no tree coordinate: the two genuine ones are checked *accepted* and the other seven
rejected, between them falsifying six of `witnessHolds`' seven conjuncts.  The seventh, the `T_k`
hash equality, is falsified by the malformed-forgery canary instead, on the witness the extractor
itself returns.

The `example`s pin the theorem statements at that bundle and at approved profiles.  The last group
is kernel-checked rather than run: on a profile whose layer-zero tree indices overflow SHA-2's
compressed eight-byte tree field, two distinct listed FORS leaf targets encode to the same
all-zero key, so `forsLeafAdrsKey_injective`'s `EncodedTargetLedgerConditions` hypothesis is
load-bearing rather than decorative.
-/

public section

namespace SLHDSA.ForsWitnessesTest

open Security Concrete EncoderFixtures

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"FORS witness check failed: {label}")

/-! ## The toy bundle

One byte per node, two FORS trees of height two, so eight FORS leaves at global indices `0`–`7`.
`Thash` folds its children left to right as `acc ↦ (acc <<< 2) ^^^ (child >>> 1)` and exclusive-ors
a tweak derived from the address, so `F x = (x >>> 1) ^^^ tw` and
`H l r = (((l >>> 1) <<< 2) ^^^ (r >>> 1)) ^^^ tw`.  Dropping each child's low bit is what makes
collisions cheap; the `<<< 2` is what makes the fold order sensitive; the tweak is what makes it
address sensitive. -/

-- Exposed: the toy fixture's arithmetic has to reduce inside the exposed bundle below and inside
-- the `decide` pins, so the parameter record and the bundle it configures are exposed.  Neither
-- the secret table nor the tweak map needs exposure of its own.  Nothing outside this executable
-- consumes them.
@[expose] def toyParams : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 2, k := 2, lgw := 2 }

theorem toyValid : toyParams.Valid := by decide

example : toyParams.t = 4 := by decide
example : toyParams.digestBytes = 1 := by decide

/-- The per-leaf secret values the toy `PRF` hands out, indexed by the tree-index word of the
`FORS_PRF` address — which `forsSkAdrs` sets to the global FORS leaf index.

Every value is secret-sensitive here, because `F` reveals `s >>> 1` at every leaf and each leaf
image feeds its tree's root.  The low bit of each secret is *not* observable: `F` drops it.  The
eight values are chosen so that the eight images `toySecret t >>> 1` are pairwise distinct, which
is what lets the canaries below tell the global leaf index `5` apart from the tree-local index
`1`. -/
def toySecret : ℕ → UInt8
  | 0 => 5
  | 1 => 18
  | 2 => 33
  | 3 => 71
  | 4 => 104
  | 5 => 150
  | 6 => 201
  | _ => 233

/-- A per-address byte mixed into every `Thash` output, so that the same children at two different
addresses hash differently.  Without it the address a witness names would be invisible to
evaluation and the canaries could not reject a witness stated at a neighbouring node. -/
def toyTweak (a : Adrs) : UInt8 :=
  UInt8.ofNat ((a.type * 61 + a.word1 * 29 + a.word2 * 43 + a.word3 * 97) % 256)

@[expose, reducible] def toyPrimitives : Primitives toyParams where
  PkSeed := Unit
  SkSeed := Unit
  SkPrf := Unit
  Y := Bytes 1
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ _ adrs => Vector.replicate 1 (toySecret adrs.word3)
  PRFmsg := fun _ _ _ => Vector.replicate 1 0
  yToBytes := id
  Thash := fun _ adrs children =>
    Vector.replicate 1
      ((children.foldl (fun (acc : UInt8) (y : Bytes 1) => (acc <<< 2) ^^^ (y[0] >>> 1))
        (0 : UInt8)) ^^^ toyTweak adrs)
  Hmsg := fun _ _ _ _ => Vector.replicate toyParams.m 0

instance : DecidableEq toyPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 1))

/-- A one-byte node. -/
def node (x : UInt8) : toyPrimitives.Y := Vector.replicate 1 x

/-- The byte inside a node. -/
def byteOf (y : toyPrimitives.Y) : UInt8 := y[0]

/-- The FORS instance address: a `FORS_TREE` address at key pair one, so the key-pair word is
nonzero and therefore visible to `toyTweak`. -/
def baseAdrs : Adrs :=
  ((Adrs.zero.setTreeAddress 0).setTypeAndClear .forsTree).setKeyPairAddress 1

/-! ## The digest

One byte, `0x90`, whose two base-`4` digits are `2` and `1`: tree `0` opens its local leaf `2`,
global index `2`, and tree `1` opens its local leaf `1`, global index `5`.

Two properties of global index `5` give the canaries below their power.  It is **odd**, so the
opened leaf is the *second* child of its parent and the honest child pair, taken left to right, is
`(leaf 4, leaf 5)` — not the `(opened leaf, sibling)` pair a partner keyed on the opened leaf
would name.  At an even index those two coincide and the swap canary would be blind.  And it lies
in the **second** tree, where the global FORS numbering and tree `1`'s local numbering differ, so
a witness stated at the local index `1` names a different address and different honest values. -/
def digest : List Byte := [0x90]

example : forsIdx toyParams digest 0 = 2 := by decide
example : forsIdx toyParams digest 1 = 1 := by decide

/-- The global FORS leaf index tree `i` opens, recomputed here rather than taken from
`forsSigLeafIndex`. -/
def globalLeaf (i : ℕ) : ℕ := i * 2 ^ toyParams.a + forsIdx toyParams digest i

example : globalLeaf 0 = 2 := by decide
example : globalLeaf 1 = 5 := by decide

/-! ## Honest key material -/

/-- The honest leaf image at global index `t`. -/
def honestLeaf (t : ℕ) : toyPrimitives.Y := forsLeaf toyPrimitives () () baseAdrs t

/-- The honest FORS root of tree `i`. -/
def honestRoot (i : ℕ) : toyPrimitives.Y := forsRoot toyPrimitives () () baseAdrs i

/-- The honest root vector, recomputed from `forsRoot` rather than taken from
`forsHonestRoots`. -/
def honestRoots : Vector toyPrimitives.Y toyParams.k :=
  Vector.ofFn fun i : Fin toyParams.k => honestRoot i.val

/-- The honest child pair of the FORS node at height `z`, global index `t`, recomputed from
`PerfectMerkleTree.merkleRoot` rather than taken from `forsHonestChildren`. -/
def honestChildPair (z t : ℕ) : toyPrimitives.Y × toyPrimitives.Y :=
  (PerfectMerkleTree.merkleRoot (forsLeaf toyPrimitives () () baseAdrs)
      (forsNodeHash toyPrimitives () baseAdrs) (z - 1) (2 * t),
    PerfectMerkleTree.merkleRoot (forsLeaf toyPrimitives () () baseAdrs)
      (forsNodeHash toyPrimitives () baseAdrs) (z - 1) (2 * t + 1))

/-- The honest FORS signature on `digest`. -/
def honestSig : ForsSigCore toyParams toyPrimitives.core :=
  forsSign toyPrimitives digest () () baseAdrs

/-! ## The four forgeries and the malformed one

Four of the five recover the honest FORS public key; `badForgery` does not, and is what the
malformed-input canary uses.  Each replaces one revealed secret value or one authentication node —
except `collisionForgery`, which is built on top of `preimageForgery` and so differs from the
honest signature in two fields. -/

/-- Replace tree `i`'s revealed secret value. -/
def withSecret (sig : ForsSigCore toyParams toyPrimitives.core) (i : ℕ) (value : toyPrimitives.Y) :
    ForsSigCore toyParams toyPrimitives.core :=
  Vector.ofFn fun j : Fin toyParams.k =>
    if j.val = i then { sig[j.val] with sk := value } else sig[j.val]

/-- Replace one node of tree `i`'s authentication path. -/
def withAuth (sig : ForsSigCore toyParams toyPrimitives.core) (i level : ℕ)
    (value : toyPrimitives.Y) : ForsSigCore toyParams toyPrimitives.core :=
  Vector.ofFn fun j : Fin toyParams.k =>
    if j.val = i then
      { sig[j.val] with
        auth := Vector.ofFn fun l : Fin toyParams.a =>
          if l.val = level then value else (sig[j.val]).auth[l.val] }
    else sig[j.val]

/-- A second `F`-preimage of tree `0`'s honest leaf image: `F` drops the low bit, so flipping it
leaves the leaf image, both roots, and the FORS public key unchanged. -/
def secondPreimage : toyPrimitives.Y := node (toySecret (globalLeaf 0) ^^^ 1)

/-- A revealed secret value for tree `1` whose leaf image differs from the honest one in the low
bit only.  `H` drops the low bit of each child, so the parent node at height one is unchanged and
the recovered root is still honest — the forgery therefore recovers the honest public key while
colliding `H` at that node. -/
def collidingSecret : toyPrimitives.Y :=
  node (2 * ((byteOf (honestLeaf (globalLeaf 1)) ^^^
    toyTweak (forsNodeAdrs baseAdrs 0 (globalLeaf 1))) ^^^ 1))

/-- Tree `0`'s secret replaced by a second preimage: every leaf image is honest, so the extractor
finds no collision and falls through to the `F`-preimage branch. -/
def preimageForgery : ForsSigCore toyParams toyPrimitives.core :=
  withSecret honestSig 0 secondPreimage

/-- Tree `1`'s secret replaced by a colliding one, on top of the preimage forgery: tree `1`'s leaf
image now differs from the honest one, so the extractor returns the `H`-collision. -/
def collisionForgery : ForsSigCore toyParams toyPrimitives.core :=
  withSecret preimageForgery 1 collidingSecret

/-- A tree-`1` secret whose leaf image differs from the honest one in bit *one*.  `H` drops the low
bit of each child, so that difference reaches the height-one node — where leaf `5` is the right
child, contributing `r >>> 1` — as a difference in bit *zero*; and the height-one node is in turn
the root's left child, whose low bit is dropped in the same way, so the tree root is unchanged.
The extractor therefore finds its collision one level higher, at the tree root node, which is the
top of the `0 < z ≤ a` range. -/
def highCollidingSecret : toyPrimitives.Y :=
  node (2 * ((byteOf (honestLeaf (globalLeaf 1)) ^^^
    toyTweak (forsNodeAdrs baseAdrs 0 (globalLeaf 1))) ^^^ 2))

/-- Tree `1`'s secret replaced by the one that collides at the tree root rather than at the node
above the leaf. -/
def highCollisionForgery : ForsSigCore toyParams toyPrimitives.core :=
  withSecret honestSig 1 highCollidingSecret

/-- Tree `1`'s top authentication node perturbed in bit one: `H` drops the low bit of each child,
so the recovered root differs from the honest one in its low bit alone and the `T_k` compression
is unchanged. -/
def tlForgery : ForsSigCore toyParams toyPrimitives.core :=
  withAuth honestSig 1 1 (node (byteOf (honestSig[1]).auth[1] ^^^ 2))

/-- The same node perturbed in bit two, which survives the `T_k` compression: this one does not
recover the honest FORS public key at all. -/
def badForgery : ForsSigCore toyParams toyPrimitives.core :=
  withAuth honestSig 1 1 (node (byteOf (honestSig[1]).auth[1] ^^^ 4))

/-! ## Witness validity, evaluated

`witnessHolds` re-evaluates the condition each constructor asserts, from the honest values
recomputed above rather than from `ForsWitness.Valid`, including the three identifications: the
`hCollision` partner is the honest child pair at the node named, its two children are supplied in
left-to-right order, and both the `hCollision` and `fPreimage` addresses use the global FORS leaf
index.  It is deliberately a separate computation from `ForsWitness.Valid`: the checks below run
it on the extractor's actual output. -/

def witnessHolds : ForsWitness toyParams toyPrimitives → Bool
  | .tlCollision recovered =>
      (recovered != honestRoots) &&
        (toyPrimitives.Tl () (forsPkAdrs baseAdrs) recovered.toList ==
          toyPrimitives.Tl () (forsPkAdrs baseAdrs) honestRoots.toList)
  | .hCollision i z c =>
      let t := globalLeaf i.val / 2 ^ z
      decide (0 < z) && decide (z ≤ toyParams.a) &&
        (honestChildPair z t != c) &&
        (toyPrimitives.H () (forsNodeAdrs baseAdrs z t) (honestChildPair z t).1
            (honestChildPair z t).2 ==
          toyPrimitives.H () (forsNodeAdrs baseAdrs z t) c.1 c.2)
  | .fPreimage i value =>
      toyPrimitives.F () (forsNodeAdrs baseAdrs 0 (globalLeaf i.val)) value ==
        toyPrimitives.F () (forsNodeAdrs baseAdrs 0 (globalLeaf i.val))
          (forsSkGenCore toyPrimitives.core () () baseAdrs (globalLeaf i.val))

/-- A tag naming which constructor a witness is, so a canary can pin the branch. -/
def witnessTag : ForsWitness toyParams toyPrimitives → String
  | .tlCollision _ => "tlCollision"
  | .hCollision i z _ => s!"hCollision {i.val} {z}"
  | .fPreimage i _ => s!"fPreimage {i.val}"

/-- The same for the per-tree search, which can return nothing. -/
def treeWitnessTag : Option (ForsWitness toyParams toyPrimitives) → String
  | none => "none"
  | some w => witnessTag w

def extractTree (sig : ForsSigCore toyParams toyPrimitives.core) (i : Fin toyParams.k) :
    Option (ForsWitness toyParams toyPrimitives) :=
  findForsTreeCollision toyPrimitives sig digest () () baseAdrs i

def extract (sig : ForsSigCore toyParams toyPrimitives.core) (target : Fin toyParams.k) :
    ForsWitness toyParams toyPrimitives :=
  findForsWitness toyPrimitives sig digest () () baseAdrs target

/-! ## The bundle behaves as advertised -/

/-- The four bundle properties the canaries below lean on.  `F` drops the low bit of its input and
adds the address tweak.  The eight honest leaf images are pairwise distinct, so no two leaves share
an honest partner.  `H` is order sensitive at the node the collision canary names.  And the tweak
separates that node's address both from the one at the same height with another index and from the
one at the same index a height up, and separates global leaf `5`'s address from the address a
tree-local numbering would give that leaf. -/
def checkToyBundle : IO Unit := do
  ensure "F drops the low bit and adds the address tweak"
    ((List.range 256).all fun x =>
      toyPrimitives.F () (forsNodeAdrs baseAdrs 0 5) (node (UInt8.ofNat x)) ==
        node ((UInt8.ofNat x >>> 1) ^^^ toyTweak (forsNodeAdrs baseAdrs 0 5)))
  ensure "the eight honest leaf images are pairwise distinct"
    (((List.range 8).map honestLeaf).eraseDups.length == 8)
  ensure "H is order sensitive at the node the collision canary names"
    (toyPrimitives.H () (forsNodeAdrs baseAdrs 1 2) (honestLeaf 4) (honestLeaf 5) !=
      toyPrimitives.H () (forsNodeAdrs baseAdrs 1 2) (honestLeaf 5) (honestLeaf 4))
  ensure "the tweak separates the node the collision canary names from its neighbours"
    ((toyTweak (forsNodeAdrs baseAdrs 1 2) != toyTweak (forsNodeAdrs baseAdrs 1 0)) &&
      (toyTweak (forsNodeAdrs baseAdrs 1 2) != toyTweak (forsNodeAdrs baseAdrs 2 2)) &&
      (toyTweak (forsNodeAdrs baseAdrs 0 5) != toyTweak (forsNodeAdrs baseAdrs 0 1)))

/-! ## Positive canaries -/

/-- Tree `1`: the forged leaf image differs from the honest one in the low bit only, which `H`
drops, so the parent at height one is unchanged and the extractor returns the collision there
between the honest child pair `(leaf 4, leaf 5)` and the forged pair `(leaf 4, forged leaf 5)`.

The node is `(height 1, global index 2)`.  Tree `1`'s local numbering would call it
`(height 1, index 0)`, and the opened leaf `5` is the node's *right* child, so the honest pair
taken left to right is `(leaf 4, leaf 5)` rather than the opened-leaf-first `(leaf 5, leaf 4)`.
This one fixture therefore separates the global node index from the local one and the honest child
order from the opened-leaf-first one; the last three checks guard exactly that. -/
def checkTreeCollision : IO Unit := do
  let witness := extractTree collisionForgery ⟨1, by decide⟩
  ensure "tree 1 yields an H-collision at height 1"
    (treeWitnessTag witness == "hCollision 1 1")
  match witness with
  | none => ensure "tree 1 yields a witness" false
  | some w =>
      ensure "the tree-1 collision satisfies its equation" (witnessHolds w)
      match w with
      | .hCollision _ z c =>
          ensure "the tree-1 collision names the global node index 2"
            (decide (globalLeaf 1 / 2 ^ z = 2))
          ensure "the tree-1 collision is between the expected pairs"
            ((honestChildPair z 2 == (honestLeaf 4, honestLeaf 5)) &&
              (c.1 == honestLeaf 4) && (c.2 != honestLeaf 5))
          ensure "the honest pair swapped does not satisfy the collision equation"
            (toyPrimitives.H () (forsNodeAdrs baseAdrs z 2) (honestChildPair z 2).2
                (honestChildPair z 2).1 !=
              toyPrimitives.H () (forsNodeAdrs baseAdrs z 2) c.1 c.2)
          ensure "the tree-local node index does not satisfy the collision equation"
            (toyPrimitives.H () (forsNodeAdrs baseAdrs z (forsIdx toyParams digest 1 / 2 ^ z))
                (honestChildPair z (forsIdx toyParams digest 1 / 2 ^ z)).1
                (honestChildPair z (forsIdx toyParams digest 1 / 2 ^ z)).2 !=
              toyPrimitives.H () (forsNodeAdrs baseAdrs z (forsIdx toyParams digest 1 / 2 ^ z))
                c.1 c.2)
      | _ => ensure "the tree-1 witness is a collision" false

/-- The same leaf perturbed one bit higher collides at the tree root instead: the height-one node
changes, so the extractor climbs past it and returns the collision at height `a`.  This is the
upper end of the `0 < z ≤ a` range, and its node index is tree `1`'s own root index. -/
def checkTreeRootCollision : IO Unit := do
  ensure "the high-collision forgery recovers the honest FORS public key"
    (forsPkFromSig toyPrimitives highCollisionForgery digest () baseAdrs ==
      forsPkGen toyPrimitives () () baseAdrs)
  let witness := extractTree highCollisionForgery ⟨1, by decide⟩
  ensure "tree 1 yields an H-collision at height 2, the tree height"
    (treeWitnessTag witness == "hCollision 1 2")
  match witness with
  | none => ensure "tree 1 yields a witness" false
  | some w =>
      ensure "the tree-root collision satisfies its equation" (witnessHolds w)
      match w with
      | .hCollision _ z _ =>
          ensure "the tree-root collision names global node index 1, tree 1's own root"
            (decide (globalLeaf 1 / 2 ^ z = 1))
      | _ => ensure "the tree-root witness is a collision" false

/-- Tree `0`'s revealed secret value is a second preimage of the honest leaf image, so no tree
yields a collision and the extractor falls through to the `F`-preimage branch at whichever tree
the caller names. -/
def checkPreimage : IO Unit := do
  ensure "the preimage forgery recovers the honest FORS public key"
    (forsPkFromSig toyPrimitives preimageForgery digest () baseAdrs ==
      forsPkGen toyPrimitives () () baseAdrs)
  ensure "no tree of the preimage forgery yields a collision"
    ((treeWitnessTag (extractTree preimageForgery ⟨0, by decide⟩) == "none") &&
      (treeWitnessTag (extractTree preimageForgery ⟨1, by decide⟩) == "none"))
  let w0 := extract preimageForgery ⟨0, by decide⟩
  ensure "target 0 yields an F-preimage" (witnessTag w0 == "fPreimage 0")
  ensure "the tree-0 preimage satisfies its equation" (witnessHolds w0)
  match w0 with
  | .fPreimage _ value =>
      ensure "the tree-0 preimage is the tampered value, not the honest secret"
        ((value == secondPreimage) &&
          (value != forsSkGenCore toyPrimitives.core () () baseAdrs (globalLeaf 0)))
  | _ => ensure "the tree-0 witness is a preimage" false
  let w1 := extract preimageForgery ⟨1, by decide⟩
  ensure "target 1 yields an F-preimage" (witnessTag w1 == "fPreimage 1")
  ensure "the honest secret value at tree 1 is itself a valid preimage witness" (witnessHolds w1)
  match w1 with
  | .fPreimage _ value =>
      ensure "the tree-1 preimage is the honest secret value, which needs no distinctness"
        (value == forsSkGenCore toyPrimitives.core () () baseAdrs (globalLeaf 1))
      ensure "the tree-local leaf index does not satisfy the preimage equation"
        (toyPrimitives.F () (forsNodeAdrs baseAdrs 0 (forsIdx toyParams digest 1)) value !=
          toyPrimitives.F () (forsNodeAdrs baseAdrs 0 (forsIdx toyParams digest 1))
            (forsSkGenCore toyPrimitives.core () () baseAdrs (forsIdx toyParams digest 1)))
  | _ => ensure "the tree-1 witness is a preimage" false

/-- The whole-instance extractor prefers the collision: on a forgery that carries both a second
preimage at tree `0` and a colliding leaf at tree `1`, it returns tree `1`'s `H`-collision. -/
def checkInstanceCollision : IO Unit := do
  ensure "the collision forgery recovers the honest FORS public key"
    (forsPkFromSig toyPrimitives collisionForgery digest () baseAdrs ==
      forsPkGen toyPrimitives () () baseAdrs)
  let w := extract collisionForgery ⟨0, by decide⟩
  ensure "the instance extractor returns tree 1's collision"
    (witnessTag w == "hCollision 1 1")
  ensure "the instance collision satisfies its equation" (witnessHolds w)

/-- Perturbing tree `1`'s top authentication node in bit one changes the recovered root vector but
not its `T_k` image, so the extractor returns the `T_k` second preimage. -/
def checkInstanceTlCollision : IO Unit := do
  ensure "the T_k forgery recovers the honest FORS public key"
    (forsPkFromSig toyPrimitives tlForgery digest () baseAdrs ==
      forsPkGen toyPrimitives () () baseAdrs)
  ensure "the T_k forgery recovers a different root vector"
    (forsRecoveredRoots toyPrimitives tlForgery digest () baseAdrs != honestRoots)
  let w := extract tlForgery ⟨0, by decide⟩
  ensure "the instance extractor returns a T_k second preimage" (witnessTag w == "tlCollision")
  ensure "the T_k second preimage satisfies its equation" (witnessHolds w)

/-! ## Negative canaries -/

/-- The honest signature has an honest leaf image at every tree, so no tree yields a collision and
the fall-through witness is the honest secret value — a valid open-preimage witness, which only
the absence of a distinctness conjunct admits. -/
def checkHonestSignature : IO Unit := do
  ensure "no tree of the honest signature yields a collision"
    ((treeWitnessTag (extractTree honestSig ⟨0, by decide⟩) == "none") &&
      (treeWitnessTag (extractTree honestSig ⟨1, by decide⟩) == "none"))
  let w := extract honestSig ⟨1, by decide⟩
  ensure "the honest signature yields an F-preimage" (witnessTag w == "fPreimage 1")
  ensure "that witness satisfies its equation" (witnessHolds w)

/-- Perturbing tree `1`'s top authentication node in bit two survives the `T_k` compression, so the
forgery does not recover the honest FORS public key.  The extractor still returns a `T_k` witness —
it only compares root vectors — but that witness fails its own equation.  This is why
`findForsWitness_sound` carries the public-key hypothesis. -/
def checkMalformedForgery : IO Unit := do
  ensure "the malformed forgery does not recover the honest FORS public key"
    (forsPkFromSig toyPrimitives badForgery digest () baseAdrs !=
      forsPkGen toyPrimitives () () baseAdrs)
  let w := extract badForgery ⟨0, by decide⟩
  ensure "the malformed forgery still produces a T_k witness" (witnessTag w == "tlCollision")
  ensure "the malformed T_k witness fails its own equation" (!witnessHolds w)

/-- `witnessHolds` itself has to be able to fail, and has to accept.  Nine witnesses are
fabricated: eight at tree `1`, and one `T_k` witness, which carries no tree coordinate.  The two
genuine ones — the height-one collision and the preimage at the honest secret value — are checked
*accepted*; the other seven are rejected.

`witnessHolds` has seven conjuncts in all: two on the `tlCollision` branch, four on `hCollision`,
one on `fPreimage`.  The seven rejections falsify six of them —

* the `hCollision` hash equation, by a collision whose `H` image differs and by the genuine
  collision with its two children swapped — the second only because `H` is order sensitive, so it
  is the left-to-right identification that rejects it;
* the `hCollision` distinctness, by a collision submitted at the honest child pair itself: both its
  bounds hold and its hash equation is an identity, so the distinctness is the only conjunct it
  fails;
* the `0 < z` bound, by the genuine collision moved to height zero, where the address is a FORS
  *leaf* address and `forsHonestChildren`'s `height - 1` would truncate;
* the `z ≤ a` bound, by the genuine collision moved above the tree height;
* the `fPreimage` equation, by a preimage of the wrong value;
* the `tlCollision` distinctness, by a `T_k` witness at the honest root vector itself, whose `T_k`
  image is of course equal.

The height-zero and above-height fabrications miss the hash equation as well, because the honest
child pair is recomputed at whatever height the witness names; it is the bounds that say what is
wrong with them.

The seventh conjunct, the `tlCollision` hash equality, is falsified by `checkMalformedForgery`
rather than here: the witness the extractor returns from `badForgery` carries a root vector that
differs from the honest one *and* compresses differently.

The remaining identification, the *global* rather than tree-local index, is checked where the
genuine witnesses are extracted: at the node index by `checkTreeCollision` and at the leaf index by
`checkPreimage`. -/
def checkFabricatedWitnesses : IO Unit := do
  let two : Fin toyParams.k := ⟨1, by decide⟩
  let genuinePair : toyPrimitives.Y × toyPrimitives.Y :=
    (honestLeaf 4, node (byteOf (honestLeaf 5) ^^^ 1))
  ensure "the genuine tree-1 collision is accepted"
    (witnessHolds (.hCollision two 1 genuinePair))
  ensure "a fabricated collision with a different H image is rejected"
    (witnessHolds (.hCollision two 1 (honestLeaf 4, node (byteOf (honestLeaf 5) ^^^ 2))) == false)
  ensure "a collision at height zero is rejected"
    (witnessHolds (.hCollision two 0 genuinePair) == false)
  ensure "a collision above the tree height is rejected"
    (witnessHolds (.hCollision two 3 genuinePair) == false)
  ensure "the genuine collision with its two children swapped is rejected"
    (witnessHolds (.hCollision two 1 (genuinePair.2, genuinePair.1)) == false)
  ensure "the honest child pair is not the opened-leaf-first pair"
    (honestChildPair 1 (globalLeaf 1 / 2) != (honestLeaf 5, honestLeaf 4))
  ensure "a collision submitted at the honest child pair itself is rejected"
    (witnessHolds (.hCollision two 1 (honestChildPair 1 (globalLeaf 1 / 2))) == false)
  ensure "the genuine tree-1 preimage is accepted"
    (witnessHolds (.fPreimage two (node (toySecret (globalLeaf 1)))))
  ensure "a fabricated preimage of the wrong value is rejected"
    (witnessHolds (.fPreimage two (node (toySecret (globalLeaf 0)))) == false)
  ensure "a fabricated T_k second preimage equal to the honest roots is rejected"
    (witnessHolds (.tlCollision honestRoots) == false)

/-! ## Statement pins at the toy bundle -/

/-- A shape pin for `forsPkFromSig_cases`: at a signature which recovers the honest FORS public
key, one of the three branches holds.  The two collision branches are restated with their hash
equation moved in front of the side conditions `forsPkFromSig_cases` states before it, so each has
to be reassembled rather than passed through, and every conjunct the theorem supplies is bound and
used here.  That is not the order the games read: both source-final-validity experiments test
their side condition first and the hash equation last (`m ≠ mj ∧ eval = eval`; `j ∉ opened`, then
`eval = eval`).  Deleting the `T_k` equality from the first disjunct or the `H` equality from the
second, which is the security content of those two branches, breaks this pin. -/
example (sig : ForsSigCore toyParams toyPrimitives.core) (md : List Byte)
    (hpk : forsPkFromSig toyPrimitives sig md () baseAdrs =
      forsPkGen toyPrimitives () () baseAdrs) :
    (toyPrimitives.Tl () (forsPkAdrs baseAdrs)
            (forsRecoveredRoots toyPrimitives sig md () baseAdrs).toList =
          toyPrimitives.Tl () (forsPkAdrs baseAdrs)
            (forsHonestRoots toyPrimitives () () baseAdrs).toList ∧
        forsRecoveredRoots toyPrimitives sig md () baseAdrs ≠
          forsHonestRoots toyPrimitives () () baseAdrs) ∨
      (∃ (i : Fin toyParams.k) (z : ℕ) (c : toyPrimitives.Y × toyPrimitives.Y),
        toyPrimitives.H ()
              (forsNodeAdrs baseAdrs z (forsSigLeafIndex toyParams md i.val / 2 ^ z))
              (forsHonestChildren toyPrimitives () () baseAdrs z
                (forsSigLeafIndex toyParams md i.val / 2 ^ z)).1
              (forsHonestChildren toyPrimitives () () baseAdrs z
                (forsSigLeafIndex toyParams md i.val / 2 ^ z)).2 =
            toyPrimitives.H ()
              (forsNodeAdrs baseAdrs z (forsSigLeafIndex toyParams md i.val / 2 ^ z)) c.1 c.2 ∧
          0 < z ∧ z ≤ toyParams.a ∧
            forsHonestChildren toyPrimitives () () baseAdrs z
              (forsSigLeafIndex toyParams md i.val / 2 ^ z) ≠ c) ∨
      (∀ i : Fin toyParams.k,
        toyPrimitives.F () (forsNodeAdrs baseAdrs 0 (forsSigLeafIndex toyParams md i.val))
            (sig[i.val]).sk =
          toyPrimitives.F () (forsNodeAdrs baseAdrs 0 (forsSigLeafIndex toyParams md i.val))
            (forsSkGenCore toyPrimitives.core () () baseAdrs
              (forsSigLeafIndex toyParams md i.val))) := by
  rcases forsPkFromSig_cases toyPrimitives sig md () () baseAdrs hpk with
    ⟨hne, htl⟩ | ⟨i, z, c, hz, hza, hne, hcoll⟩ | hall
  · exact Or.inl ⟨htl, hne⟩
  · exact Or.inr (Or.inl ⟨i, z, c, hcoll, hz, hza, hne⟩)
  · exact Or.inr (Or.inr hall)

/-- The extractor's soundness at the toy bundle, for every signature, digest and target: the only
hypothesis is the public-key match.  It is stated schematically rather than at
`collisionForgery` because the library definitions are not exposed, so a kernel `decide` on the
concrete public-key match does not reduce; that instance of the hypothesis is what
`checkInstanceCollision` evaluates at run time. -/
example (sig : ForsSigCore toyParams toyPrimitives.core) (md : List Byte)
    (target : Fin toyParams.k)
    (hpk : forsPkFromSig toyPrimitives sig md () baseAdrs =
      forsPkGen toyPrimitives () () baseAdrs) :
    (findForsWitness toyPrimitives sig md () () baseAdrs target).Valid () () baseAdrs md :=
  findForsWitness_sound toyPrimitives sig md () () baseAdrs target hpk

/-- The identification a source-final-validity game needs, read off the per-tree extractor's
soundness lemma alone: a returned `hCollision` collides with the honest child pair at the node it
names, and not with an unconstrained second pair.  The proof is the intended downstream path — the
extractor bodies are not exposed, so the unfolding equation is what a consumer rewrites with. -/
example (sig : ForsSigCore toyParams toyPrimitives.core) (md : List Byte) (i : Fin toyParams.k)
    (z : ℕ) (c : toyPrimitives.Y × toyPrimitives.Y)
    (hroot : (forsRecoveredRoots toyPrimitives sig md () baseAdrs)[i.val] =
      (forsHonestRoots toyPrimitives () () baseAdrs)[i.val])
    (hw : findForsTreeCollision toyPrimitives sig md () () baseAdrs i =
      some (.hCollision i z c)) :
    toyPrimitives.H () (forsNodeAdrs baseAdrs z (forsSigLeafIndex toyParams md i.val / 2 ^ z))
        (forsHonestChildren toyPrimitives () () baseAdrs z
          (forsSigLeafIndex toyParams md i.val / 2 ^ z)).1
        (forsHonestChildren toyPrimitives () () baseAdrs z
          (forsSigLeafIndex toyParams md i.val / 2 ^ z)).2 =
      toyPrimitives.H () (forsNodeAdrs baseAdrs z (forsSigLeafIndex toyParams md i.val / 2 ^ z))
        c.1 c.2 := by
  have h := findForsTreeCollision_sound toyPrimitives sig md () () baseAdrs i hroot hw
  rw [ForsWitness.valid_hCollision] at h
  exact h.2.2.2

/-! ## Ledger pins on approved profiles -/

/-- Two layers of height two, two FORS trees of height two, `w = 16`, `len = 4`. -/
def twoLayerParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 2, k := 2, lgw := 4 }

def twoLayer : ValidatedParams := ⟨twoLayerParams, by decide⟩

theorem twoLayerApprovedAddressBounds : ApprovedAddressBounds twoLayerParams :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    by decide, by decide⟩

/-- Every FORS leaf address a witness can name at a reachable bottom position is a listed `forsF`
target. -/
example (pos : BottomPosition twoLayer) (md : List Byte) (i : Fin twoLayerParams.k) :
    forsNodeAdrs pos.forsAdrs 0 (forsSigLeafIndex twoLayerParams md i.val) ∈
      forsLeafAddresses twoLayer :=
  mem_forsLeafAddresses_of_digest pos md i

/-- Every FORS internal node a witness can name at a reachable bottom position is a listed `forsH`
target. -/
example (pos : BottomPosition twoLayer) (md : List Byte) (i : Fin twoLayerParams.k) {z : ℕ}
    (hz : 0 < z) (hza : z ≤ twoLayerParams.a) :
    forsNodeAdrs pos.forsAdrs z (forsSigLeafIndex twoLayerParams md i.val / 2 ^ z) ∈
      forsTreeAddresses twoLayer :=
  mem_forsTreeAddresses_of_digest pos md i hz hza

/-- The `T_k` witness address at a reachable bottom position is a listed `forsTl` target. -/
example (pos : BottomPosition twoLayer) :
    forsPkAdrs pos.forsAdrs ∈ forsRootAddresses twoLayer :=
  mem_forsRootAddresses twoLayer pos

/-- Under the SHA-2 encoder at an approved-bounds profile, distinct FORS leaf coordinates carry
distinct encoded tweaks. -/
example : Function.Injective
    fun coord : (BottomPosition twoLayer × Fin twoLayerParams.k) × Fin twoLayerParams.t =>
      (sha2Primitives twoLayerParams).adrsToKey
        (forsNodeAdrs coord.1.1.forsAdrs 0 (coord.1.2.val * twoLayerParams.t + coord.2.val)) :=
  forsLeafAdrsKey_injective
    (sha2EncodedTargetLedgerConditions twoLayer twoLayerApprovedAddressBounds)

/-- The same for the FORS internal-node addresses, in the bounded coordinate shape a witness
produces. -/
example {pos pos' : BottomPosition twoLayer} {i i' : Fin twoLayerParams.k} {z z' j j' : ℕ}
    (hz : 0 < z) (hza : z ≤ twoLayerParams.a) (hj : j < 2 ^ (twoLayerParams.a - z))
    (hz' : 0 < z') (hza' : z' ≤ twoLayerParams.a) (hj' : j' < 2 ^ (twoLayerParams.a - z'))
    (hkey : (sha2Primitives twoLayerParams).adrsToKey
        (forsNodeAdrs pos.forsAdrs z (i.val * 2 ^ (twoLayerParams.a - z) + j)) =
      (sha2Primitives twoLayerParams).adrsToKey
        (forsNodeAdrs pos'.forsAdrs z' (i'.val * 2 ^ (twoLayerParams.a - z') + j'))) :
    pos = pos' ∧ i = i' ∧ z = z' ∧ j = j' :=
  forsTreeAdrsKey_injective
    (sha2EncodedTargetLedgerConditions twoLayer twoLayerApprovedAddressBounds)
    hz hza hj hz' hza' hj' hkey

/-- And for the FORS root-compression addresses, under the SHAKE encoder. -/
example : Function.Injective fun pos : BottomPosition twoLayer =>
    (shakePrimitives twoLayerParams).adrsToKey (forsPkAdrs pos.forsAdrs) :=
  forsRootAdrsKey_injective (shakeEncodedTargetLedgerConditions twoLayer
    twoLayerApprovedAddressBounds.toCanonicalAddressBounds)

/-! ## The encoded-distinctness hypothesis is load-bearing

`Concrete.sha2AdrsKey` sends every address outside its checked domain to the all-zero key, which is
the genuine key of the all-zero WOTS-hash address rather than a sentinel.  On a profile whose
layer-zero tree indices overflow the compressed eight-byte tree field, two distinct listed FORS
leaf targets therefore share a tweak, and `forsLeafAdrsKey_injective` is false without its
`EncodedTargetLedgerConditions` argument. -/

example : deep.params.k = 14 := by decide
example : deep.params.t = 4096 := by decide

/-- A bottom position of the `deep` profile at a tree index the compressed field cannot hold.  The
profile itself, its tree-index bound, and the SHA-2 out-of-domain fallback come from
`HashSigTest.SLHDSA.EncoderFixtures`, which shares them with the encoded-target canaries. -/
-- Exposed: `deepLeafCoord_tree` closes by `rfl`, which needs both of these to reduce.
@[expose] def deepBottom (t : ℕ) (ht : t < 2 ^ 64 + 2) : BottomPosition deep :=
  ⟨⟨t, deep_tree_bound t ht⟩, ⟨0, Nat.two_pow_pos _⟩⟩

@[expose] def deepLeafCoord (t : ℕ) (ht : t < 2 ^ 64 + 2) :
    (BottomPosition deep × Fin deep.params.k) × Fin deep.params.t :=
  ((deepBottom t ht, ⟨0, by decide⟩), ⟨0, by decide⟩)

theorem deepLeafCoord_tree (t : ℕ) (ht : t < 2 ^ 64 + 2) :
    (forsNodeAdrs (deepLeafCoord t ht).1.1.forsAdrs 0
      ((deepLeafCoord t ht).1.2.val * deep.params.t + (deepLeafCoord t ht).2.val)).tree = t := rfl

/-- Two distinct listed FORS leaf targets of the `deep` profile carry the same encoded SHA-2
tweak, namely the all-zero key: their layer-zero tree indices exceed the compressed eight-byte
tree field, and the checked compression falls back to that key rather than to a sentinel. -/
theorem deep_forsLeaf_sha2_alias :
    ∃ c₁ c₂ : (BottomPosition deep × Fin deep.params.k) × Fin deep.params.t,
      forsNodeAdrs c₁.1.1.forsAdrs 0 (c₁.1.2.val * deep.params.t + c₁.2.val) ∈
          forsLeafAddresses deep ∧
        forsNodeAdrs c₂.1.1.forsAdrs 0 (c₂.1.2.val * deep.params.t + c₂.2.val) ∈
          forsLeafAddresses deep ∧
        c₁ ≠ c₂ ∧
        (sha2Primitives deep.params).adrsToKey
            (forsNodeAdrs c₁.1.1.forsAdrs 0 (c₁.1.2.val * deep.params.t + c₁.2.val)) =
          (sha2Primitives deep.params).adrsToKey
            (forsNodeAdrs c₂.1.1.forsAdrs 0 (c₂.1.2.val * deep.params.t + c₂.2.val)) := by
  refine ⟨deepLeafCoord (2 ^ 64) (by norm_num), deepLeafCoord (2 ^ 64 + 1) (by norm_num),
    mem_forsLeafAddresses deep _ _ _, mem_forsLeafAddresses deep _ _ _, ?_, ?_⟩
  · intro h
    have h₁ := deepLeafCoord_tree (2 ^ 64) (by norm_num)
    have h₂ := deepLeafCoord_tree (2 ^ 64 + 1) (by norm_num)
    rw [h] at h₁
    omega
  · have hfits : ∀ t : ℕ, 2 ^ 64 ≤ t → ∀ ht : t < 2 ^ 64 + 2,
        Adrs.Fits 8 (forsNodeAdrs (deepLeafCoord t ht).1.1.forsAdrs 0
          ((deepLeafCoord t ht).1.2.val * deep.params.t + (deepLeafCoord t ht).2.val)).tree =
            false := by
      intro t hle ht
      rw [deepLeafCoord_tree, Adrs.Fits, decide_eq_false_iff_not, not_lt]
      norm_num
      omega
    rw [adrsToKey_sha2, adrsToKey_sha2,
      sha2AdrsKey_eq_zero_of_tree_overflow _ (hfits (2 ^ 64) (le_refl _) _),
      sha2AdrsKey_eq_zero_of_tree_overflow _ (hfits (2 ^ 64 + 1) (by norm_num) _)]

/-- Consequently `forsLeafAdrsKey_injective` is false for the SHA-2 bundle at this profile: its
`EncodedTargetLedgerConditions` hypothesis is load-bearing. -/
theorem deep_forsLeaf_sha2_not_injective :
    ¬ Function.Injective
        fun coord : (BottomPosition deep × Fin deep.params.k) × Fin deep.params.t =>
          (sha2Primitives deep.params).adrsToKey
            (forsNodeAdrs coord.1.1.forsAdrs 0 (coord.1.2.val * deep.params.t + coord.2.val)) := by
  intro hinj
  obtain ⟨c₁, c₂, _, _, hne, hkey⟩ := deep_forsLeaf_sha2_alias
  exact hne (hinj hkey)

def main : IO Unit := do
  checkToyBundle
  checkTreeCollision
  checkTreeRootCollision
  checkPreimage
  checkInstanceCollision
  checkInstanceTlCollision
  checkHonestSignature
  checkMalformedForgery
  checkFabricatedWitnesses
  IO.println "SLH-DSA FORS witness tests: PASS \
    (H-collision extraction at both tree heights, F-preimage extraction, T_k second preimage, \
     the honest-signature, malformed-input, and fabricated-witness canaries)"

end SLHDSA.ForsWitnessesTest

def main : IO Unit := SLHDSA.ForsWitnessesTest.main
