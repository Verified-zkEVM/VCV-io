/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Gadget
import VCVio.CryptoFoundations.CommitmentScheme

/-!
# Inner-Outer Ajtai Commitment

The Greyhound/Hachi inner-outer commitment composition over the generic lattice ring
interface.

For each message block `m_i`, the committer computes a gadget decomposition
`s_i`, an inner Ajtai commitment `t_i = A * s_i`, a gadget decomposition
`tHat_i`, and finally the outer commitment
`u = B * flatten(tHat_i)_i`.

Digit decomposition is intentionally supplied as data: the generic
`NegacyclicRing` abstraction knows how to multiply ring elements but does not
choose centered representatives or base-`b` digits for arbitrary coefficient
domains. TODO add to VCV-io.

TODO citations
-/

open OracleComp

universe u

namespace LatticeCrypto
namespace Ajtai
namespace InnerOuter

variable {Coeff : Type u} [CommRing Coeff]

/-- Public parameters for the inner-outer Ajtai commitment. -/
structure PublicParams (ring : NegacyclicRing Coeff)
    (innerRows messageRows messageDigits outerRows blocks innerDigits : Nat) where
  /-- Inner Ajtai matrix `A`. -/
  innerMatrix : RqMatrix ring innerRows (messageRows * messageDigits)
  /-- Outer Ajtai matrix `B`. -/
  outerMatrix : RqMatrix ring outerRows (blocks * (innerRows * innerDigits))

/-- Opening for the inner-outer commitment. -/
structure Opening (ring : NegacyclicRing Coeff)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) where
  /-- Gadget decompositions of the message blocks. -/
  messageDecomp : PolyVec (RqVec ring (messageRows * messageDigits)) blocks
  /-- Gadget decompositions of the inner commitments. -/
  innerDecomp : PolyVec (RqVec ring (innerRows * innerDigits)) blocks

/-- Decomposition operations used by the honest committer. -/
structure Decomposition (ring : NegacyclicRing Coeff)
    (messageRows messageDigits innerRows innerDigits : Nat) where
  /-- Decompose one message block with respect to the message gadget. -/
  message : RqVec ring messageRows → RqVec ring (messageRows * messageDigits)
  /-- Decompose one inner commitment with respect to the inner gadget. -/
  inner : RqVec ring innerRows → RqVec ring (innerRows * innerDigits)

/-- Messages are block vectors over the row space of the message gadget. -/
abbrev Message (ring : NegacyclicRing Coeff) (messageRows blocks : Nat) :=
  PolyVec (RqVec ring messageRows) blocks

/-- Inner-outer commitments live in the row space of the outer matrix. -/
abbrev Commitment (ring : NegacyclicRing Coeff) (outerRows : Nat) :=
  RqVec ring outerRows

/-- Compute all message decompositions for the honest committer. -/
def messageDecomps (ring : NegacyclicRing Coeff)
    {messageRows messageDigits innerRows innerDigits blocks : Nat}
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    (m : Message ring messageRows blocks) :
    PolyVec (RqVec ring (messageRows * messageDigits)) blocks :=
  m.map decomp.message

/-- Compute one inner commitment `A * s_i`. -/
def innerCommit (ring : NegacyclicRing Coeff)
    {innerRows messageRows messageDigits : Nat}
    (A : RqMatrix ring innerRows (messageRows * messageDigits))
    (s : RqVec ring (messageRows * messageDigits)) : RqVec ring innerRows :=
  matVecMul ring A s

/-- Compute all inner gadget decompositions for the honest committer. -/
def innerDecomps (ring : NegacyclicRing Coeff)
    {messageRows messageDigits innerRows innerDigits blocks : Nat}
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    (A : RqMatrix ring innerRows (messageRows * messageDigits))
    (ss : PolyVec (RqVec ring (messageRows * messageDigits)) blocks) :
    PolyVec (RqVec ring (innerRows * innerDigits)) blocks :=
  ss.map fun s => decomp.inner (innerCommit ring A s)

/-- Compute the outer commitment from an opening. -/
def commitWithOpening (ring : NegacyclicRing Coeff)
    {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) :
    Commitment ring outerRows :=
  matVecMul ring pp.outerMatrix (flattenBlocks opening.innerDecomp)

/-- Honest opening generation from the supplied decomposition operations. -/
def openMessage (ring : NegacyclicRing Coeff)
    {messageRows messageDigits innerRows innerDigits outerRows blocks : Nat}
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message ring messageRows blocks) :
    Opening ring innerRows messageRows messageDigits blocks innerDigits :=
  let ss := messageDecomps ring decomp m
  { messageDecomp := ss
    innerDecomp := innerDecomps ring decomp pp.innerMatrix ss }

/-- Check that the opening's message decompositions map back to the claimed message. -/
def messageChecks (ring : NegacyclicRing Coeff) (base : Coeff)
    {innerRows messageRows messageDigits blocks innerDigits : Nat}
    (m : Message ring messageRows blocks)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) : Prop :=
  ∀ i : Fin blocks, gadgetMul ring base (opening.messageDecomp.get i) = m.get i

/-- Boolean version of `messageChecks` used by executable verification. -/
def messageChecksBool (ring : NegacyclicRing Coeff) (base : Coeff)
    {innerRows messageRows messageDigits blocks innerDigits : Nat}
    [DecidableEq (RqVec ring messageRows)]
    (m : Message ring messageRows blocks)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  (List.finRange blocks).all fun i =>
    decide (gadgetMul ring base (opening.messageDecomp.get i) = m.get i)

/-- Check that each inner decomposition opens the corresponding inner Ajtai commitment. -/
def innerChecks (ring : NegacyclicRing Coeff) (base : Coeff)
    {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) : Prop :=
  ∀ i : Fin blocks,
    innerCommit ring pp.innerMatrix (opening.messageDecomp.get i) =
      gadgetMul ring base (opening.innerDecomp.get i)

/-- Boolean version of `innerChecks` used by executable verification. -/
def innerChecksBool (ring : NegacyclicRing Coeff) (base : Coeff)
    {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
    [DecidableEq (RqVec ring innerRows)]
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  (List.finRange blocks).all fun i =>
    decide
      (innerCommit ring pp.innerMatrix (opening.messageDecomp.get i) =
        gadgetMul ring base (opening.innerDecomp.get i))

/-- Verify a Hachi-style inner-outer opening. -/
def verify (ring : NegacyclicRing Coeff) (base : Coeff)
    {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
    [DecidableEq (RqVec ring messageRows)]
    [DecidableEq (RqVec ring innerRows)]
    [DecidableEq (Commitment ring outerRows)]
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message ring messageRows blocks)
    (c : Commitment ring outerRows)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  messageChecksBool ring base m opening &&
    innerChecksBool ring base pp opening &&
    decide (commitWithOpening ring pp opening = c)

/-- The inner-outer Ajtai commitment instantiated as `CommitmentScheme`. -/
def commitmentScheme (ring : NegacyclicRing Coeff) (base : Coeff)
    (innerRows messageRows messageDigits outerRows blocks innerDigits : Nat)
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    [SampleableType (RqMatrix ring innerRows (messageRows * messageDigits))]
    [SampleableType (RqMatrix ring outerRows (blocks * (innerRows * innerDigits)))]
    [DecidableEq (RqVec ring messageRows)]
    [DecidableEq (RqVec ring innerRows)]
    [DecidableEq (Commitment ring outerRows)] :
    CommitmentScheme
      (PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
      (Message ring messageRows blocks)
      (Commitment ring outerRows)
      (Opening ring innerRows messageRows messageDigits blocks innerDigits) where
  setup := do
    let A ← $ᵗ RqMatrix ring innerRows (messageRows * messageDigits)
    let B ← $ᵗ RqMatrix ring outerRows (blocks * (innerRows * innerDigits))
    pure { innerMatrix := A, outerMatrix := B }
  commit pp m := do
    let opening := openMessage ring decomp pp m
    pure (commitWithOpening ring pp opening, opening)
  verify pp m c opening := verify ring base pp m c opening

end InnerOuter
end Ajtai
end LatticeCrypto
