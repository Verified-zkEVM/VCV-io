/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.XmssWitnesses
public import HashSig.SLHDSA.HypertreeGeneral

/-!
# Hypertree witnesses

The layer walk: a hypertree signature that recovers the honest public root from a forged message
must, at one of its `d` layers, present an XMSS signature that recovers the honest XMSS root of
that layer's tree from a message differing from the one the honest hypertree signs there.  That
layer's signature is then one XMSS forgery at one named tree address, which
`HashSig.SLHDSA.Security.XmssWitnesses` translates into a witness against `H`, `T_len` or `F`.

## What is proved, and what is not

The walk is `recoverFromPosition_binding`, proved by two-step induction on the number of remaining
layers, and `pkFromSig_binding` is its instance at the digest-derived layer-zero position.  The
extractor `findHypertreeWitness` computes the layer and the witness together, and its soundness
lemma places the witness at the position the returned layer names.

What is *not* proved is any statement about the layer the walk selects beyond its bound: the
extractor stops at the first layer whose recovered root is the honest one, and that is visible in
its two shape equations, but no theorem here says the selected layer is minimal, and none is
needed — a witness at any such layer is a witness.  Nothing here constructs an adversary, states
an advantage, performs a game hop, or claims that any honest execution queried a value a witness
attacks; those are program-level obligations of the later slice.

The plan for this slice also lists an unoriented divergence lemma, over two arbitrary signature
vectors, with both messages existentially quantified.  It is deliberately absent.  Its second
message is bound by the existential, so it cannot be identified with the honest one afterwards,
and the binding form below is therefore not a corollary of it but a separate induction; and a
statement that names no honest partner cannot feed a witness predicate.  The binding form is the
exhaustiveness the source discharges inline.

## Labels

*Deterministic inclusion* — a statement whose only free objects are a validated parameter record
or a `prims` over one, seeds, positions and addresses, natural-number indices, messages, and
signature or witness data, together with the structural side conditions their statements or proofs
need: the `DigestParts` the layer-zero position is parsed from, which three of them take —
`advance_initial_eq_atLayer`, `recoverFromPosition_of_pkFromSig` and `pkFromSig_binding`; the
`DecidableEq prims.Y` instance the extractor and its four lemmas take; and the
`prims.core.ByteLaws` argument `findHypertreeWitness_isSome` alone takes, which is what reaches the
WOTS+ extractor's completeness lemma.  The honest secret seed is taken by fourteen of the
twenty-four: the honest running message and its three equations, the walk and its two companions,
the validity predicate and its unfolding equation, and the extractor and its four lemmas.  The
seven position-arithmetic declarations, the witness type and the two ledger statements do not take
one, because none of them names an honest object.  The `p.Valid` argument its predecessors carry is
absent throughout: a `ValidatedParams` supplies it.

The declarations are:

* the position arithmetic `LayerPosition.next_congr`, `LayerPosition.advance` and its four
  equations `advance_zero`, `advance_next`, `advance_layer_val`, `advance_succ`, and the bridge
  `advance_initial_eq_atLayer`;
* the honest running message `honestLayerMsg` with `honestLayerMsg_zero`, `honestLayerMsg_succ`
  and `honestLayerMsg_next`;
* the walk `recoverFromPosition_binding`, its top-level hypothesis bridge
  `recoverFromPosition_of_pkFromSig`, and its top-level instance `pkFromSig_binding`;
* `HypertreeWitness`, `HypertreeWitness.Valid` and its unfolding equation
  `HypertreeWitness.valid_iff`;
* `findHypertreeWitness`, its two shape equations `findHypertreeWitness_eq_of_root` and
  `findHypertreeWitness_eq_next_of_ne`, and its two lemmas `findHypertreeWitness_sound` and
  `findHypertreeWitness_isSome`.

*Transcript transport* — a statement about the slice-1 coordinates and ledgers of
`HashSig.SLHDSA.Security`:

* `layerTreeCoord_advance_ne` names no ledger and asserts no membership: it separates the slice-1
  tree coordinate two different layers of one walk carry, which is what the next one needs;
* `advance_xmssNodeAdrsKey_injective` is about the encoded tweaks of the `xmssH` ledger.

Two private `Vector` lemmas, `getElem_zero_eq_head` and `getElem_succ_eq_tail`, carry the
head-and-tail bookkeeping the induction needs; they are the only private declarations, and they
mirror `HashSig.SLHDSA.GeneralHypertree`'s own private `insertIdx` pair.

`LayerPosition.advance` and its equations are declared in the `SLHDSA.LayerPosition` namespace
rather than this module's own, because they are position arithmetic and dot notation on a
`LayerPosition` resolves there.  `HashSig.SLHDSA.Position` has no `advance` today and this is its
only consumer, so it lives here; promoting it to that module later would move the declarations
without renaming them.

## The walk

Fix a reachable position `pos`, a count `layers` of positions from `pos` through the final layer,
a forged message `msg`, an honest message `msg' ≠ msg`, and a vector of `layers` XMSS signatures.
Recovery threads each layer's recovered root into the next position, as the message signed there.
The honest walk from the same position threads the honest XMSS roots instead, and its layer-`j`
message is `honestLayerMsg`: the given honest message at `j = 0`, and the honest XMSS root of the
layer-`(j-1)` tree afterwards.  Above layer zero it is therefore a function of the honest key
material and the position alone, with no honest signature in it, because an honest XMSS signature
recovers its own tree's root whatever it signs.

If the forged walk ends at the honest top root then at some layer `j` the two walks meet: the
forged walk's layer-`j` recovery already equals the honest layer-`j` root, while its layer-`j`
message still differs from the honest one.  The induction is on `layers`, generalising the
position and both messages.  At one remaining layer the position is final, its address is the top
tree's, and `j = 0`.  At two or more, either the head recovery is already the honest root — then
`j = 0` and the messages differ by hypothesis — or it is not, and the induction hypothesis applies
at the next position with the two recovered roots as the two new messages, giving `j + 1`.

`LayerPosition.advance` is what lets the conclusion name layer `j`'s position.  It iterates `next`
and carries the same dependent bound `next` does, so `pos.advance j` is a `LayerPosition` exactly
when `pos.layer.val + j < d`.  It recurses on the left, `pos.advance (j+1) = (pos.next).advance j`,
which is the step the induction takes; `advance_succ` is the other associativity, needed to reach
`LayerPosition.atLayer`, and `advance_initial_eq_atLayer` is that bridge.  `next` takes its bound
as a proof argument, so rewriting under it needs `next_congr` rather than `rw`.

## The layer bound

The bound every statement here carries is `j < layers` against `pos.layer.val + layers = d` —
equivalently `pos.layer.val + j < d`.  It is the bound the source's recorded targets are guarded
by: each of the three case flags is an existential over `0 ≤ i < d`, and each reduction picks its
`i` with a list `find` over that range.  What the layer then indexes differs between the three.
The `H` reduction builds the address it extracts at with `set_ltidx`, from that `i` and the tree
index at that layer.  The other two build no address of their own; they turn the same triple into
an index into the challenge oracle's query list, `bigi predT (fun i => nr_trees i) 0 cidx * l' +
tidx * l' + kpidx`.  Either way the layer is one of the coordinates separating one recorded target
from another, and `0 ≤ i < d` is its range.

Two things turn on it, and a third does not.

* It is what *forms* the position: `LayerPosition.layer` is a `Fin d`.  Slice 1's ledgers are
  enumerations of exactly those typed positions, so without the bound there is no position, no
  address, and nothing listed.  The tree word needs no bound of its own — `LayerPosition.tree` is
  a `Fin (2 ^ layerTreeHeight vp layer.val)` and `next` carries that forward — and neither does
  the leaf, which is a `Fin (2 ^ h')`.
* It is what separates one layer's targets from another's.  Every layer's XMSS internal nodes are
  members of the one ledger `xmssNodeAddresses vp`; the `TREE` type code separates that ledger
  from the other five and does nothing across layers.  Cross-layer separation is the
  `coord = coord'` conclusion of `xmssNodeAdrsKey_injective`, and since
  `(pos.advance j).layer.val = pos.layer.val + j`, distinct layers below `d` give distinct
  coordinates.  That is `layerTreeCoord_advance_ne` and `advance_xmssNodeAdrsKey_injective`.
* It is *not* what keeps a witness inside its own role's ledger, and it is not a height bound.
  The heights an XMSS witness carries are `XmssWitness.Valid`'s, unchanged here.

## Address roles

Every address a hypertree witness names is the address the underlying XMSS witness names at the
position `pos.advance w.layer`, so slice 1's membership lemmas apply through
`HashSig.SLHDSA.Security.XmssWitnesses` — `mem_xmssNodeAddresses_of_leaf` for the `H` branch and,
through `wotsLeafAdrs_eq_wotsInstanceAdrs`, `mem_wotsPkAddresses`, `mem_wotsStepAddresses_of_lt`
and `wotsPreimageAdrs_mem_optionalWotsAddresses` for the three WOTS+ branches.  None of them is
restated here, and neither is any game-shape bridge: `HypertreeWitness.Valid` reduces to
`XmssWitness.Valid` at a named position, so `xmssWitness_valid_hCollision_eval` and the three
WOTS+ bridges apply unchanged.

`advance_xmssNodeAdrsKey_injective` consumes `EncodedTargetLedgerConditions` rather than assuming
a fresh injectivity hypothesis, so a concrete profile discharges it through
`approvedEncodedTargetLedgerConditions`; the SHA-2 zero fallback is never treated as unreachable.

## References

- NIST FIPS 205, §7 (Algorithms 12–13)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`FL_SL_XMSS_MT_ES.ec`)
-/

public section

namespace SLHDSA

namespace LayerPosition

variable {vp : ValidatedParams}

/-- Transport an equality of positions under `next`.  `next` takes its layer bound as a proof
argument, so a rewrite under it has an ill-typed motive; this lemma closes such goals by
substitution, the two proof arguments being equal by proof irrelevance. -/
theorem next_congr {a b : LayerPosition vp} (hab : a = b)
    (ha : a.layer.val + 1 < vp.params.d) (hb : b.layer.val + 1 < vp.params.d) :
    a.next ha = b.next hb := by subst hab; rfl

/-- Advance `j` hypertree layers from a reachable position, iterating the FIPS low-bits/high-bits
transition `next`.  The bound is `next`'s, accumulated: the result is a position at layer
`pos.layer.val + j`, and that has to be below `d` for the position to exist.

The recursion is on the left — advancing `j + 1` layers is advancing one and then `j` — which is
the step the layer walk's induction takes.  `advance_succ` gives the other association. -/
def advance : (pos : LayerPosition vp) → (j : ℕ) →
    pos.layer.val + j < vp.params.d → LayerPosition vp
  | pos, 0, _ => pos
  | pos, j + 1, h => (pos.next (by omega)).advance j (by
      simp only [LayerPosition.next_layer_val]; omega)

/-- Advancing no layers is the identity. -/
@[simp]
theorem advance_zero (pos : LayerPosition vp) (h : pos.layer.val + 0 < vp.params.d) :
    pos.advance 0 h = pos := by simp [advance]

/-- The left association: advancing `j + 1` layers is one `next` followed by `j` more. -/
theorem advance_next (pos : LayerPosition vp) (j : ℕ)
    (h : pos.layer.val + (j + 1) < vp.params.d) :
    pos.advance (j + 1) h =
      (pos.next (by omega)).advance j (by simp only [next_layer_val]; omega) := by
  simp [advance]

/-- Advancing `j` layers lands on layer `pos.layer.val + j`. -/
@[simp]
theorem advance_layer_val (pos : LayerPosition vp) (j : ℕ)
    (h : pos.layer.val + j < vp.params.d) :
    (pos.advance j h).layer.val = pos.layer.val + j := by
  induction j generalizing pos with
  | zero => rw [advance_zero]; omega
  | succ j ih => rw [advance_next, ih]; simp only [next_layer_val]; omega

/-- The right association: advancing `j + 1` layers is `j` layers followed by one `next`. -/
theorem advance_succ (pos : LayerPosition vp) (j : ℕ)
    (h : pos.layer.val + (j + 1) < vp.params.d) :
    pos.advance (j + 1) h =
      (pos.advance j (by omega)).next (by rw [advance_layer_val]; omega) := by
  induction j generalizing pos with
  | zero =>
      rw [advance_next pos 0 h, advance_zero]
      exact (next_congr (advance_zero pos (by omega)) _ _).symm
  | succ j ih =>
      rw [advance_next pos (j + 1) h, ih (pos.next (by omega))]
      exact next_congr (advance_next pos j (by omega)).symm _ _

/-- Advancing from the digest-derived layer-zero position is the total random-access trajectory
`atLayer`.  This is what lets a statement proved by the layer-by-layer induction be read at a
`Fin d` layer. -/
theorem advance_initial_eq_atLayer (vp : ValidatedParams) (parts : DigestParts vp.params)
    (j : ℕ) (h : (LayerPosition.initial vp parts).layer.val + j < vp.params.d) :
    (LayerPosition.initial vp parts).advance j h = atLayer vp parts ⟨j, by simpa using h⟩ := by
  induction j with
  | zero => rw [advance_zero]; exact (atLayer_zero_eq_initial vp parts).symm
  | succ j ih =>
      rw [advance_succ]
      refine Eq.trans (next_congr (ih (by omega)) _
        (by simp only [atLayer_layer_val]; simpa using h)) ?_
      exact (atLayer_succ_eq_next vp parts ⟨j, by omega⟩ (by simpa using h)).symm

end LayerPosition

namespace Security

open GeneralHypertree

private theorem getElem_zero_eq_head {X : Type*} {n : ℕ} (v : Vector X (n + 1)) :
    v[0] = v.head := by simp [Vector.head]

private theorem getElem_succ_eq_tail {X : Type*} {n : ℕ} (v : Vector X (n + 1)) (j : ℕ)
    (hj : j < n) : v[j + 1] = v.tail[j] := by simp [Nat.add_comm]

/-! ## The honest running message

The message the honest signer signs at each layer of a walk that starts at `pos`. -/

/-- The honest message signed at layer `j` of the walk that starts at `pos` with the honest
message `msg`: `msg` itself at layer zero, and the honest XMSS root of the layer-`(j-1)` tree
afterwards.

It is a function of the honest key material and the position alone.  No honest signature appears
in it, because root recovery from an honest XMSS signature reaches that tree's root whatever
message the signature signs, so the honest walk's layer-`(j+1)` message does not depend on its
layer-`j` message. -/
def honestLayerMsg (vp : ValidatedParams) (prims : Primitives vp.params) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (pos : LayerPosition vp) (msg : prims.Y) :
    (j : ℕ) → pos.layer.val + j < vp.params.d → prims.Y
  | 0, _ => msg
  | j + 1, h => xmssRoot prims sk pk (pos.advance j (by omega)).toAdrs

/-- At layer zero the honest running message is the honest message the walk starts with. -/
theorem honestLayerMsg_zero (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (pos : LayerPosition vp) (msg : prims.Y)
    (h : pos.layer.val + 0 < vp.params.d) :
    honestLayerMsg vp prims sk pk pos msg 0 h = msg := by simp [honestLayerMsg]

/-- Above layer zero the honest running message is the honest XMSS root of the tree one layer
down. -/
theorem honestLayerMsg_succ (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (pos : LayerPosition vp) (msg : prims.Y) (j : ℕ)
    (h : pos.layer.val + (j + 1) < vp.params.d) :
    honestLayerMsg vp prims sk pk pos msg (j + 1) h =
      xmssRoot prims sk pk (pos.advance j (by omega)).toAdrs := by simp [honestLayerMsg]

/-- Shifting the walk's start by one layer.  The honest running message at layer `j + 1` of the
walk from `pos` is the one at layer `j` of the walk from `pos.next`, whose own honest message is
the honest XMSS root at `pos`.  This is the step the layer walk's induction takes. -/
theorem honestLayerMsg_next (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (pos : LayerPosition vp) (msg : prims.Y) (j : ℕ)
    (hnext : pos.layer.val + 1 < vp.params.d)
    (h : pos.layer.val + (j + 1) < vp.params.d) :
    honestLayerMsg vp prims sk pk pos msg (j + 1) h =
      honestLayerMsg vp prims sk pk (pos.next hnext) (xmssRoot prims sk pk pos.toAdrs) j
        (by simp only [LayerPosition.next_layer_val]; omega) := by
  cases j with
  | zero => rw [honestLayerMsg_succ, honestLayerMsg_zero, LayerPosition.advance_zero]
  | succ i => rw [honestLayerMsg_succ, honestLayerMsg_succ, LayerPosition.advance_next]

/-! ## The layer walk -/

/-- **The layer walk.**  A vector of `layers` XMSS signatures whose recovery from `pos` on the
forged message `msg` reaches the honest top-layer root exhibits a layer `j < layers` at which its
own recovered root is already the honest XMSS root of that layer's tree, while the message it
recovers from differs from the honest running message there.

That layer's signature is therefore an XMSS forgery at `(pos.advance j).toAdrs` on the leaf
`(pos.advance j).leaf.val`, which is the pair of hypotheses `xmssPkFromSig_forgeryCases` and
`findXmssWitness_isSome` take.

The proof is a two-step induction on `layers`, generalising the position and both messages, the
shape `recoverFromPosition_signFromPosition` already uses.  At no remaining layers the position's
own layer bound contradicts the hypothesis, so nothing is claimed there.  At one, the position is
final and `j = 0`.  At two or more the head recovery either is the honest root at `pos`, giving
`j = 0` with the messages distinct by hypothesis, or is not, and the induction hypothesis at
`pos.next` — taking the two recovered roots as its two messages — gives `j + 1`.

This is the Lean counterpart of the exhaustiveness of the source's three case flags, which
`FL_SL_XMSS_MT_ES.ec` discharges inline rather than as a named lemma: a `conseq` to a false
post-condition followed by an induction on `d` closed by SMT.  The flags themselves are
existentials over the same layer range, and each reduction selects its layer with a list `find`
over it.

*Deterministic inclusion.* -/
theorem recoverFromPosition_binding (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (pos : LayerPosition vp) (layers : ℕ)
    (hlayers : pos.layer.val + layers = vp.params.d) (msg msg' : prims.Y) (hne : msg ≠ msg')
    (sigs : Vector (XmssSig vp.params prims.core) layers)
    (hroot : recoverFromPosition vp prims pk pos layers hlayers msg sigs =
      xmssRoot prims sk pk (layerAdrs (vp.params.d - 1) 0)) :
    ∃ (j : ℕ) (hj : j < layers) (m : prims.Y),
      m ≠ honestLayerMsg vp prims sk pk pos msg' j (by omega) ∧
        xmssPkFromSig prims (pos.advance j (by omega)).leaf.val sigs[j] m pk
            (pos.advance j (by omega)).toAdrs =
          xmssRoot prims sk pk (pos.advance j (by omega)).toAdrs := by
  induction layers using Nat.twoStepInduction generalizing pos msg msg' with
  | zero => have := pos.layer.isLt; omega
  | one =>
      simp only [recoverFromPosition] at hroot
      rw [← LayerPosition.toAdrs_eq_layerAdrs_of_isFinal pos (by omega)] at hroot
      refine ⟨0, by omega, msg, ?_, ?_⟩
      · rw [honestLayerMsg_zero]; exact hne
      · rw [LayerPosition.advance_zero, getElem_zero_eq_head]; exact hroot
  | more layers _ ih =>
      simp only [recoverFromPosition] at hroot
      by_cases hcase : xmssPkFromSig prims pos.leaf.val sigs.head msg pk pos.toAdrs =
          xmssRoot prims sk pk pos.toAdrs
      · refine ⟨0, by omega, msg, ?_, ?_⟩
        · rw [honestLayerMsg_zero]; exact hne
        · rw [LayerPosition.advance_zero, getElem_zero_eq_head]; exact hcase
      · obtain ⟨j, hj, m, hmne, hmeq⟩ :=
          ih (pos.next (by omega)) (by simp only [LayerPosition.next_layer_val]; omega)
            _ (xmssRoot prims sk pk pos.toAdrs) hcase sigs.tail hroot
        refine ⟨j + 1, by omega, m, ?_, ?_⟩
        · rw [honestLayerMsg_next vp prims sk pk pos msg' j (by omega)]; exact hmne
        · rw [LayerPosition.advance_next, getElem_succ_eq_tail sigs j (by omega)]; exact hmeq

/-- The top-level root match, read as the layer walk's hypothesis: recovery of the published root
from a hypertree signature is the typed recovery loop run from the digest-derived layer-zero
position for all `d` layers, and the published root is the top tree's XMSS root. -/
theorem recoverFromPosition_of_pkFromSig (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (parts : DigestParts vp.params) (msg : prims.Y)
    (sig : Signature vp prims.core)
    (hroot : pkFromSig vp prims msg sig pk parts = root vp prims sk pk) :
    recoverFromPosition vp prims pk (LayerPosition.initial vp parts) vp.params.d (by simp) msg
      sig = xmssRoot prims sk pk (layerAdrs (vp.params.d - 1) 0) := by
  rw [pkFromSig_eq_recoverFromPosition, root_eq_xmssRoot] at hroot
  exact hroot

/-- **The layer walk at the top level.**  A hypertree signature that recovers the published root
from a forged message exhibits a layer below `d` at which its own recovered root is already the
honest XMSS root of that layer's tree, from a message differing from the honest running one.

The position is `LayerPosition.initial` advanced `j` layers, which
`LayerPosition.advance_initial_eq_atLayer` identifies with `LayerPosition.atLayer` at the `Fin d`
layer `j`.

*Deterministic inclusion.* -/
theorem pkFromSig_binding (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (parts : DigestParts vp.params)
    (msg msg' : prims.Y) (hne : msg ≠ msg') (sig : Signature vp prims.core)
    (hroot : pkFromSig vp prims msg sig pk parts = root vp prims sk pk) :
    ∃ (j : ℕ) (hj : j < vp.params.d) (m : prims.Y),
      m ≠ honestLayerMsg vp prims sk pk (LayerPosition.initial vp parts) msg' j (by simpa) ∧
        xmssPkFromSig prims
              ((LayerPosition.initial vp parts).advance j (by simpa)).leaf.val sig[j] m pk
            ((LayerPosition.initial vp parts).advance j (by simpa)).toAdrs =
          xmssRoot prims sk pk ((LayerPosition.initial vp parts).advance j (by simpa)).toAdrs :=
  recoverFromPosition_binding vp prims sk pk (LayerPosition.initial vp parts) vp.params.d
    (by simp) msg msg' hne sig
    (recoverFromPosition_of_pkFromSig vp prims sk pk parts msg sig hroot)

/-! ## The extracted witness

A hypertree witness is a layer together with an XMSS witness at that layer's position.  Every
honest object it attacks is computed by `HypertreeWitness.Valid` from the honest secret seed and
the position the layer names — the honest tree at `(pos.advance layer).toAdrs`, the honest WOTS+
key material at the leaf `(pos.advance layer).leaf.val` that layer's signature opens, and the
honest message `honestLayerMsg` signed there.  None of the three is a field. -/

/-- A witness against one component hash at one hypertree layer: the layer, and an `XmssWitness`
at the position that layer names.  The position itself is not carried, because the walk's starting
position and the layer already fix it; `HypertreeWitness.Valid` recomputes it. -/
structure HypertreeWitness (vp : ValidatedParams) (prims : Primitives vp.params) where
  /-- The layer, counted from the walk's starting position. -/
  layer : ℕ
  /-- The XMSS witness at that layer's tree and leaf. -/
  witness : XmssWitness vp.params prims

/-- The winning condition a hypertree witness asserts, against the honest hypertree that `sk`
generates under the public seed `pk`, along the walk of `layers` layers that starts at `pos` with
the honest message `honestMsg`.

The layer bound `w.layer < layers` is the first conjunct.  It is what makes
`pos.advance w.layer` a position at all, hence what places every address the witness names in a
slice-1 ledger; it is also what separates this layer's targets from another layer's inside the one
`xmssNodeAddresses` ledger.  The remaining content is `XmssWitness.Valid` at that position's tree
address, that position's leaf, and the honest running message there — all three computed, none
supplied.

This is a statement about hash values and ledger placement only.  It does not say that any honest
object it names was committed as a game target, nor that any execution queried one. -/
def HypertreeWitness.Valid {vp : ValidatedParams} {prims : Primitives vp.params}
    (sk : prims.SkSeed) (pk : prims.PkSeed) (pos : LayerPosition vp) (honestMsg : prims.Y)
    (layers : ℕ) (hlayers : pos.layer.val + layers = vp.params.d)
    (w : HypertreeWitness vp prims) : Prop :=
  ∃ _ : w.layer < layers,
    w.witness.Valid sk pk (pos.advance w.layer (by omega)).toAdrs
      (pos.advance w.layer (by omega)).leaf.val
      (honestLayerMsg vp prims sk pk pos honestMsg w.layer (by omega))

/-- Unfolding equation for `HypertreeWitness.Valid`.  The body is not exposed, so this is what a
consumer destructures. -/
@[simp] theorem HypertreeWitness.valid_iff {vp : ValidatedParams} {prims : Primitives vp.params}
    (sk : prims.SkSeed) (pk : prims.PkSeed) (pos : LayerPosition vp) (honestMsg : prims.Y)
    (layers : ℕ) (hlayers : pos.layer.val + layers = vp.params.d)
    (w : HypertreeWitness vp prims) :
    w.Valid sk pk pos honestMsg layers hlayers ↔
      ∃ _ : w.layer < layers,
        w.witness.Valid sk pk (pos.advance w.layer (by omega)).toAdrs
          (pos.advance w.layer (by omega)).leaf.val
          (honestLayerMsg vp prims sk pk pos honestMsg w.layer (by omega)) := Iff.rfl

/-- Compute a hypertree witness from a vector of `layers` XMSS signatures, the forged message
`msg` the walk from `pos` starts with, the honest message `msg'`, and the honest key material.

The search walks the layers in order, comparing each layer's recovered root with the honest XMSS
root of that layer's tree.  At the first layer where they agree it hands that layer's signature to
`findXmssWitness` and labels the result with the layer; where they disagree it recomputes the next
position and recurses, carrying the recovered root as the next forged message and the honest root
as the next honest message.  Past the last layer it returns `none`.

Each layer's guard is recomputed here from `sk`, and so is the honest message handed to
`findXmssWitness` at every layer above the first; the first layer's honest message is the caller's
`msg'`, which at the top level is the message the honest signer signed.

The guard is the root match at the layer, not at the top, so the search does not need the walk to
reach the honest top root.  It stops at the first layer whose own recovered root is that layer's
honest root, wherever that falls, and whatever it returns there is valid all the same —
`findHypertreeWitness_sound` takes no top-root hypothesis.  There are exactly two ways it returns
nothing: no layer's recovered root was that layer's honest root, so the walk ran past the last
layer; or one was, and `findXmssWitness` returned nothing there. -/
def findHypertreeWitness (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (sk : prims.SkSeed) (pk : prims.PkSeed) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → prims.Y → prims.Y →
      Vector (XmssSig vp.params prims.core) layers → Option (HypertreeWitness vp prims)
  | 0, _, _, _, _ => none
  | 1, _, msg, msg', sigs =>
      if xmssPkFromSig prims pos.leaf.val sigs.head msg pk pos.toAdrs =
          xmssRoot prims sk pk pos.toAdrs then
        (findXmssWitness prims pos.leaf.val sigs.head msg msg' sk pk pos.toAdrs).map (⟨0, ·⟩)
      else none
  | layers + 2, h, msg, msg', sigs =>
      if xmssPkFromSig prims pos.leaf.val sigs.head msg pk pos.toAdrs =
          xmssRoot prims sk pk pos.toAdrs then
        (findXmssWitness prims pos.leaf.val sigs.head msg msg' sk pk pos.toAdrs).map (⟨0, ·⟩)
      else
        (findHypertreeWitness vp prims sk pk (pos.next (by omega)) (layers + 1)
            (by simp only [LayerPosition.next_layer_val]; omega)
            (xmssPkFromSig prims pos.leaf.val sigs.head msg pk pos.toAdrs)
            (xmssRoot prims sk pk pos.toAdrs) sigs.tail).map
          fun w => ⟨w.layer + 1, w.witness⟩

/-- The search stops at the starting layer exactly when that layer's recovered root is the honest
XMSS root there.  The bodies are not exposed, so this equation is what a consumer rewrites with.

The walk length is written `layers + 1` because the equation names `sigs.head`, which needs a
nonzero length; at length zero the search returns `none`, and the position's own layer bound
refutes the walk-length hypothesis there in any case. -/
theorem findHypertreeWitness_eq_of_root (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (sk : prims.SkSeed) (pk : prims.PkSeed) (pos : LayerPosition vp)
    (layers : ℕ) (hlayers : pos.layer.val + (layers + 1) = vp.params.d) (msg msg' : prims.Y)
    (sigs : Vector (XmssSig vp.params prims.core) (layers + 1))
    (hmatch : xmssPkFromSig prims pos.leaf.val sigs.head msg pk pos.toAdrs =
      xmssRoot prims sk pk pos.toAdrs) :
    findHypertreeWitness vp prims sk pk pos (layers + 1) hlayers msg msg' sigs =
      (findXmssWitness prims pos.leaf.val sigs.head msg msg' sk pk pos.toAdrs).map (⟨0, ·⟩) := by
  match layers, hlayers, sigs, hmatch with
  | 0, _, _, hmatch => rw [findHypertreeWitness, if_pos hmatch]
  | _ + 1, _, _, hmatch => rw [findHypertreeWitness, if_pos hmatch]

/-- Where the starting layer's recovered root is not the honest one and a layer remains above it,
the search moves to the next position and its answer is that layer's, shifted up by one. -/
theorem findHypertreeWitness_eq_next_of_ne (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (sk : prims.SkSeed) (pk : prims.PkSeed) (pos : LayerPosition vp)
    (layers : ℕ) (hlayers : pos.layer.val + (layers + 2) = vp.params.d) (msg msg' : prims.Y)
    (sigs : Vector (XmssSig vp.params prims.core) (layers + 2))
    (hmatch : xmssPkFromSig prims pos.leaf.val sigs.head msg pk pos.toAdrs ≠
      xmssRoot prims sk pk pos.toAdrs) :
    findHypertreeWitness vp prims sk pk pos (layers + 2) hlayers msg msg' sigs =
      (findHypertreeWitness vp prims sk pk (pos.next (by omega)) (layers + 1)
          (by simp only [LayerPosition.next_layer_val]; omega)
          (xmssPkFromSig prims pos.leaf.val sigs.head msg pk pos.toAdrs)
          (xmssRoot prims sk pk pos.toAdrs) sigs.tail).map
        fun w => ⟨w.layer + 1, w.witness⟩ := by
  rw [findHypertreeWitness, if_neg hmatch]

/-- **Extractor soundness.**  Whatever `findHypertreeWitness` returns satisfies
`HypertreeWitness.Valid` against the honest hypertree, at the layer it reports and against the
honest running message there.

There is no top-root hypothesis.  Each layer's guard is the root match at that layer, which is
`findXmssWitness_sound`'s own hypothesis, so the conclusion holds whether or not the walk reaches
the honest top root.  The leaf bound the XMSS lemma needs is free: it is `pos.leaf.isLt` at every
position the walk visits.  Nothing here says anything is returned; existence is
`findHypertreeWitness_isSome`'s, and that one does take the top root.

*Deterministic inclusion.* -/
theorem findHypertreeWitness_sound (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (sk : prims.SkSeed) (pk : prims.PkSeed) (pos : LayerPosition vp)
    (layers : ℕ) (hlayers : pos.layer.val + layers = vp.params.d) (msg msg' : prims.Y)
    (sigs : Vector (XmssSig vp.params prims.core) layers)
    {w : HypertreeWitness vp prims}
    (hw : findHypertreeWitness vp prims sk pk pos layers hlayers msg msg' sigs = some w) :
    w.Valid sk pk pos msg' layers hlayers := by
  induction layers using Nat.twoStepInduction generalizing pos msg msg' w with
  | zero => simp [findHypertreeWitness] at hw
  | one =>
      rw [findHypertreeWitness] at hw
      split at hw
      · rw [Option.map_eq_some_iff] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        refine ⟨Nat.zero_lt_succ _, ?_⟩
        rw [LayerPosition.advance_zero, honestLayerMsg_zero]
        exact findXmssWitness_sound prims pos.leaf.val pos.leaf.isLt sigs.head msg msg' sk pk
          pos.toAdrs (by assumption) hu
      · exact absurd hw (by simp)
  | more layers _ ih =>
      rw [findHypertreeWitness] at hw
      split at hw
      · rw [Option.map_eq_some_iff] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        refine ⟨Nat.zero_lt_succ _, ?_⟩
        rw [LayerPosition.advance_zero, honestLayerMsg_zero]
        exact findXmssWitness_sound prims pos.leaf.val pos.leaf.isLt sigs.head msg msg' sk pk
          pos.toAdrs (by assumption) hu
      · rw [Option.map_eq_some_iff] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        obtain ⟨huj, huv⟩ :=
          ih (pos.next (by omega)) (by simp only [LayerPosition.next_layer_val]; omega)
            _ (xmssRoot prims sk pk pos.toAdrs) sigs.tail hu
        refine ⟨Nat.succ_lt_succ huj, ?_⟩
        rw [LayerPosition.advance_next,
          honestLayerMsg_next vp prims sk pk pos msg' u.layer (by omega)]
        exact huv

/-- **Extractor completeness.**  On two distinct messages, against a vector of signatures whose
recovery from `pos` reaches the honest top-layer root, the search always returns a witness.

The layer walk supplies the layer, and at that layer `findXmssWitness_isSome` supplies the
witness.  The validated parameters come from `vp` itself and the byte laws are the argument
`findWotsWitness_isSome` needs; the leaf bound is `pos.leaf.isLt` at every position visited.

*Deterministic inclusion.* -/
theorem findHypertreeWitness_isSome (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] (laws : prims.core.ByteLaws) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (pos : LayerPosition vp) (layers : ℕ) (hlayers : pos.layer.val + layers = vp.params.d)
    (msg msg' : prims.Y) (hne : msg ≠ msg')
    (sigs : Vector (XmssSig vp.params prims.core) layers)
    (hroot : recoverFromPosition vp prims pk pos layers hlayers msg sigs =
      xmssRoot prims sk pk (layerAdrs (vp.params.d - 1) 0)) :
    (findHypertreeWitness vp prims sk pk pos layers hlayers msg msg' sigs).isSome := by
  induction layers using Nat.twoStepInduction generalizing pos msg msg' with
  | zero => have := pos.layer.isLt; omega
  | one =>
      simp only [recoverFromPosition] at hroot
      rw [← LayerPosition.toAdrs_eq_layerAdrs_of_isFinal pos (by omega)] at hroot
      rw [findHypertreeWitness, if_pos hroot, Option.isSome_map]
      exact findXmssWitness_isSome vp.valid prims laws pos.leaf.val pos.leaf.isLt sigs.head msg
        msg' sk pk pos.toAdrs hne hroot
  | more layers _ ih =>
      simp only [recoverFromPosition] at hroot
      rw [findHypertreeWitness]
      split
      · rw [Option.isSome_map]
        exact findXmssWitness_isSome vp.valid prims laws pos.leaf.val pos.leaf.isLt sigs.head msg
          msg' sk pk pos.toAdrs hne (by assumption)
      · rw [Option.isSome_map]
        exact ih (pos.next (by omega)) (by simp only [LayerPosition.next_layer_val]; omega)
          _ (xmssRoot prims sk pk pos.toAdrs) (by assumption) sigs.tail hroot

/-! ## Cross-layer ledger separation

*Transcript transport.*  Every layer's XMSS internal nodes belong to the one ledger
`xmssNodeAddresses vp`, so nothing separates two layers' `TREE` targets by type code.  What
separates them is the tree coordinate, and the layer bound is what makes it distinct. -/

variable {vp : ValidatedParams}

/-- Two different layers of one walk name two different XMSS tree coordinates.  The layer word of
`pos.advance j` is `pos.layer.val + j`, and both are below `d`, so the coordinates differ as soon
as the layers do. -/
theorem layerTreeCoord_advance_ne (pos : LayerPosition vp) {j j' : ℕ}
    (hj : pos.layer.val + j < vp.params.d) (hj' : pos.layer.val + j' < vp.params.d)
    (hne : j ≠ j') :
    LayerTreeCoord.ofPosition (pos.advance j hj) ≠
      LayerTreeCoord.ofPosition (pos.advance j' hj') := by
  intro hcoord
  have hadrs : (pos.advance j hj).toAdrs = (pos.advance j' hj').toAdrs := by
    rw [← LayerTreeCoord.ofPosition_toAdrs, ← LayerTreeCoord.ofPosition_toAdrs, hcoord]
  have hlayer := congrArg (fun a : Adrs => a.layer) hadrs
  simp only [LayerPosition.toAdrs_layer, LayerPosition.advance_layer_val] at hlayer
  omega

/-- Under the encoded-ledger conditions, XMSS internal-node targets at two different layers of one
walk carry different encoded tweaks.  Together with `xmssNodeAdrsKey_injective`, which separates
coordinates, heights and node indices, this is what stops two hypertree witnesses at different
layers from attacking the same tweak of `xmssHTcrCProblem`.

The conditions are consumed, not assumed afresh, so the SHA-2 zero fallback is never treated as
unreachable. -/
theorem advance_xmssNodeAdrsKey_injective {prims : Primitives vp.params}
    (conditions : EncodedTargetLedgerConditions vp prims) (pos : LayerPosition vp) {j j' : ℕ}
    (hj : pos.layer.val + j < vp.params.d) (hj' : pos.layer.val + j' < vp.params.d)
    {z z' i i' : ℕ} (hz : 0 < z) (hzh : z ≤ vp.params.hp) (hi : i < 2 ^ (vp.params.hp - z))
    (hz' : 0 < z') (hzh' : z' ≤ vp.params.hp) (hi' : i' < 2 ^ (vp.params.hp - z'))
    (hkey : prims.adrsToKey (xmssNodeAdrs (pos.advance j hj).toAdrs z i) =
      prims.adrsToKey (xmssNodeAdrs (pos.advance j' hj').toAdrs z' i')) :
    j = j' ∧ z = z' ∧ i = i' := by
  have hcoord := xmssNodeAdrsKey_injective (vp := vp) conditions
    (coord := LayerTreeCoord.ofPosition (pos.advance j hj))
    (coord' := LayerTreeCoord.ofPosition (pos.advance j' hj')) hz hzh hi hz' hzh' hi'
    (by simpa using hkey)
  refine ⟨?_, hcoord.2.1, hcoord.2.2⟩
  by_contra hne
  exact layerTreeCoord_advance_ne pos hj hj' hne hcoord.1

end Security

end SLHDSA
