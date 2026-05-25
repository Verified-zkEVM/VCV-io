/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Simple
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
domains.
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

namespace Decomposition

/-- A decomposition is lawful when the corresponding gadget matrix reconstructs every input. -/
def IsLawful (ring : NegacyclicRing Coeff) (base : Coeff)
    {messageRows messageDigits innerRows innerDigits : Nat}
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits) : Prop :=
  (∀ m : PolyVec ring.Poly messageRows, gadgetMul ring base (decomp.message m) = m) ∧
    (∀ t : PolyVec ring.Poly innerRows, gadgetMul ring base (decomp.inner t) = t)

end Decomposition

/-- Messages are block vectors over the row space of the message gadget. -/
abbrev Message (ring : NegacyclicRing Coeff) (messageRows blocks : Nat) :=
  PolyVec (PolyVec ring.Poly messageRows) blocks

/-- Inner-outer commitments live in the row space of the outer matrix. -/
abbrev Commitment (ring : NegacyclicRing Coeff) (outerRows : Nat) :=
  Simple.Commitment ring outerRows

/-- Compute the outer commitment from an opening. -/
def commitWithOpening (ring : NegacyclicRing Coeff)
    {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) :
    Commitment ring outerRows :=
  Simple.commit ring pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp)

/-- Honest opening generation from the supplied decomposition operations. -/
def openMessage (ring : NegacyclicRing Coeff)
    {messageRows messageDigits innerRows innerDigits outerRows blocks : Nat}
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message ring messageRows blocks) :
    Opening ring innerRows messageRows messageDigits blocks innerDigits :=
  let ss := m.map decomp.message
  { messageDecomp := ss
    innerDecomp := ss.map fun s => decomp.inner (Simple.commit ring pp.innerMatrix s) }

/-- Verify a Hachi-style inner-outer opening. -/
def verify (ring : NegacyclicRing Coeff) (base : Coeff)
    {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
    [DecidableEq (PolyVec ring.Poly messageRows)]
    [DecidableEq (PolyVec ring.Poly innerRows)]
    [DecidableEq (Commitment ring outerRows)]
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

/-- The inner-outer Ajtai commitment instantiated as `CommitmentScheme`. -/
def commitmentScheme (ring : NegacyclicRing Coeff) (base : Coeff)
    (innerRows messageRows messageDigits outerRows blocks innerDigits : Nat)
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
    [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))]
    [DecidableEq (PolyVec ring.Poly messageRows)]
    [DecidableEq (PolyVec ring.Poly innerRows)]
    [DecidableEq (Commitment ring outerRows)] :
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
    let opening := openMessage ring decomp pp m
    pure (commitWithOpening ring pp opening, opening)
  verify pp m c opening := verify ring base pp m c opening

/-- Inner-outer Ajtai commitments are perfectly correct for lawful decompositions. -/
theorem perfectlyCorrect (ring : NegacyclicRing Coeff) (base : Coeff)
    (innerRows messageRows messageDigits outerRows blocks innerDigits : Nat)
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    (hdecomp : decomp.IsLawful ring base)
    [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
    [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))]
    [DecidableEq (PolyVec ring.Poly messageRows)]
    [DecidableEq (PolyVec ring.Poly innerRows)]
    [DecidableEq (Commitment ring outerRows)] :
    (commitmentScheme ring base innerRows messageRows messageDigits outerRows blocks innerDigits
      decomp).PerfectlyCorrect := by
  intro pp _ m cd hmem
  simp only [commitmentScheme, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl
  let opening := openMessage ring decomp pp m
  have hMessage :
      (List.finRange blocks).all (fun i =>
        Simple.verify ring (gadgetMatrix ring base messageRows messageDigits)
          (opening.messageDecomp.get i) (m.get i) ()) = true := by
    simp only [List.all_eq_true]
    intro i _hi
    have hmap : opening.messageDecomp.get i = decomp.message (m.get i) := by
      simp only [opening, openMessage]
      change (Vector.map decomp.message m)[i.val] = decomp.message (m[i.val])
      simp
    have hprod :
        Simple.commit ring (gadgetMatrix ring base messageRows messageDigits)
          (opening.messageDecomp.get i) = m.get i := by
      rw [hmap]
      simpa [Simple.commit, gadgetMul] using hdecomp.1 (m.get i)
    simp [Simple.verify, hprod]
  have hInner :
      (List.finRange blocks).all (fun i =>
        Simple.verify ring (gadgetMatrix ring base innerRows innerDigits)
          (opening.innerDecomp.get i)
          (Simple.commit ring pp.innerMatrix (opening.messageDecomp.get i)) ()) = true := by
    simp only [List.all_eq_true]
    intro i _hi
    have hmap :
        opening.innerDecomp.get i =
          decomp.inner (Simple.commit ring pp.innerMatrix (opening.messageDecomp.get i)) := by
      simp only [opening, openMessage]
      change
        (Vector.map (fun s => decomp.inner (Simple.commit ring pp.innerMatrix s))
          (Vector.map decomp.message m)).get i =
          decomp.inner
            (Simple.commit ring pp.innerMatrix ((Vector.map decomp.message m).get i))
      change
        (Vector.map (fun s => decomp.inner (Simple.commit ring pp.innerMatrix s))
          (Vector.map decomp.message m))[i.val] =
          decomp.inner
            (Simple.commit ring pp.innerMatrix ((Vector.map decomp.message m)[i.val]))
      simp
    have hprod :
        Simple.commit ring (gadgetMatrix ring base innerRows innerDigits)
          (opening.innerDecomp.get i) =
          Simple.commit ring pp.innerMatrix (opening.messageDecomp.get i) := by
      rw [hmap]
      simpa [Simple.commit, gadgetMul] using
        hdecomp.2 (Simple.commit ring pp.innerMatrix (opening.messageDecomp.get i))
    simp [Simple.verify, hprod]
  change
    verify ring base pp m
      (commitWithOpening ring pp opening)
      opening = true
  simp [verify, commitWithOpening, hMessage, hInner]

end InnerOuter
end Ajtai
end LatticeCrypto
