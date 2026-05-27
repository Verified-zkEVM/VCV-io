/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Simple.Scheme
import LatticeCrypto.Ajtai.Arithmetic
import VCVio.CryptoFoundations.CommitmentScheme

/-!
# Inner-Outer Ajtai Commitment Scheme

Definitions for the Greyhound/Hachi inner-outer commitment composition.
-/

open OracleComp ENNReal
open CommitmentScheme

universe u

namespace LatticeCrypto
namespace Ajtai
namespace InnerOuter

variable {Coeff : Type u} [CommRing Coeff]

/-- Public parameters for the inner-outer Ajtai commitment. -/
structure PublicParams (ring : NegacyclicRing Coeff)
    (innerRows messageRows messageDigits outerRows blocks innerDigits : Nat) where
  /-- Inner Ajtai matrix `A`. -/
  innerMatrix : Simple.PublicParams ring innerRows (messageRows * messageDigits)
  /-- Outer Ajtai matrix `B`. -/
  outerMatrix : Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits))

/-- Opening for the inner-outer commitment. -/
structure Opening (ring : NegacyclicRing Coeff)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) where
  /-- Gadget decompositions of the message blocks. -/
  messageDecomp : PolyVec (PolyVec ring.Poly (messageRows * messageDigits)) blocks
  /-- Gadget decompositions of the inner commitments. -/
  innerDecomp : PolyVec (PolyVec ring.Poly (innerRows * innerDigits)) blocks

/-- Decomposition operations used by the honest committer. -/
structure Decomposition (ring : NegacyclicRing Coeff)
    (messageRows messageDigits innerRows innerDigits : Nat) where
  /-- Decompose one message block with respect to the message gadget. -/
  message : PolyVec ring.Poly messageRows → PolyVec ring.Poly (messageRows * messageDigits)
  /-- Decompose one inner commitment with respect to the inner gadget. -/
  inner : PolyVec ring.Poly innerRows → PolyVec ring.Poly (innerRows * innerDigits)

/-- Messages are block vectors over the row space of the message gadget. -/
abbrev Message (ring : NegacyclicRing Coeff) (messageRows blocks : Nat) :=
  PolyVec (PolyVec ring.Poly messageRows) blocks

/-- Inner-outer commitments live in the row space of the outer matrix. -/
abbrev Commitment (ring : NegacyclicRing Coeff) (outerRows : Nat) :=
  Simple.Commitment ring outerRows

section Scheme

variable {ring : NegacyclicRing Coeff}
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}

/-- Honest opening generation from the supplied decomposition operations. -/
def openMessage
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message ring messageRows blocks) :
    Opening ring innerRows messageRows messageDigits blocks innerDigits :=
  let ss := m.map decomp.message
  { messageDecomp := ss
    innerDecomp := ss.map fun s => decomp.inner (Simple.commit ring pp.innerMatrix s) }

/-- Compute the outer commitment from an opening. -/
def commitWithOpening
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) :
    Commitment ring outerRows :=
  Simple.commit ring pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp)

variable [DecidableEq (PolyVec ring.Poly messageRows)]
variable [DecidableEq (PolyVec ring.Poly innerRows)]
variable [DecidableEq (Commitment ring outerRows)]

/-- Verify a inner-outer opening. -/
def verify (base : Coeff)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message ring messageRows blocks)
    (c : Commitment ring outerRows)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  (List.finRange blocks).all (fun i =>
    Simple.verify ring (gadgetMatrix ring base messageRows messageDigits)
      (opening.messageDecomp.get i) (m.get i) ()) &&
    (List.finRange blocks).all (fun i =>
      Simple.verify ring (gadgetMatrix ring base innerRows innerDigits)
        (opening.innerDecomp.get i)
        (Simple.commit ring pp.innerMatrix (opening.messageDecomp.get i)) ()) &&
    Simple.verify ring pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp) c ()

section CommitmentScheme

variable [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
variable [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))]
variable [DecidableEq (PolyVec ring.Poly messageRows)]
variable [DecidableEq (PolyVec ring.Poly innerRows)]
variable [DecidableEq (Commitment ring outerRows)]

/-- The inner-outer Ajtai commitment instantiated as `CommitmentScheme`. -/
def commitmentScheme (base : Coeff)
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits) :
    CommitmentScheme
      (PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
      (Message ring messageRows blocks)
      (Commitment ring outerRows)
      (Opening ring innerRows messageRows messageDigits blocks innerDigits) where
  setup := do
    let A ← $ᵗ Simple.PublicParams ring innerRows (messageRows * messageDigits)
    let B ← $ᵗ Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits))
    pure { innerMatrix := A, outerMatrix := B }
  commit pp m := do
    let opening := openMessage decomp pp m
    pure (commitWithOpening pp opening, opening)
  verify pp m c opening := verify base pp m c opening

end CommitmentScheme

end Scheme

end InnerOuter
end Ajtai
end LatticeCrypto
