/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.InnerOuter.Scheme
import LatticeCrypto.Ajtai.Simple.Correctness

/-!
# Correctness of the Inner-Outer Ajtai Commitment
-/

open OracleComp ENNReal
open CommitmentScheme

universe u

namespace LatticeCrypto
namespace Ajtai
namespace InnerOuter

variable {Coeff : Type u} [CommRing Coeff]

variable {ring : NegacyclicRing Coeff}
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
variable [DecidableEq (PolyVec ring.Poly messageRows)]
variable [DecidableEq (PolyVec ring.Poly innerRows)]
variable [DecidableEq (Commitment ring outerRows)]

section Correctness

omit [DecidableEq (PolyVec ring.Poly innerRows)] [DecidableEq (Commitment ring outerRows)] in
/-- Honest message decompositions pass the message gadget checks. -/
theorem openMessage_message_checks (base : Coeff)
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    (hMessageDecomp : IsLawfulGadgetDecomposition ring base decomp.message)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message ring messageRows blocks) :
    (List.finRange blocks).all (fun i =>
      Simple.verify ring (gadgetMatrix ring base messageRows messageDigits)
        ((openMessage decomp pp m).messageDecomp.get i) (m.get i) ()) = true := by
  simp only [List.all_eq_true]
  intro i _hi
  have hmap :
      (openMessage decomp pp m).messageDecomp.get i = decomp.message (m.get i) := by
    simp only [openMessage]
    change (Vector.map decomp.message m)[i.val] = decomp.message (m[i.val])
    simp
  have hprod :
      Simple.commit ring (gadgetMatrix ring base messageRows messageDigits)
        ((openMessage decomp pp m).messageDecomp.get i) = m.get i := by
    rw [hmap]
    simpa [Simple.commit, gadgetMul] using hMessageDecomp (m.get i)
  simp [Simple.verify, hprod]

omit [DecidableEq (PolyVec ring.Poly messageRows)] [DecidableEq (Commitment ring outerRows)] in
/-- Honest inner decompositions pass the inner gadget checks. -/
theorem openMessage_inner_checks (base : Coeff)
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    (hInnerDecomp : IsLawfulGadgetDecomposition ring base decomp.inner)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message ring messageRows blocks) :
    (List.finRange blocks).all (fun i =>
      Simple.verify ring (gadgetMatrix ring base innerRows innerDigits)
        ((openMessage decomp pp m).innerDecomp.get i)
        (Simple.commit ring pp.innerMatrix ((openMessage decomp pp m).messageDecomp.get i))
        ()) = true := by
  simp only [List.all_eq_true]
  intro i _hi
  have hmap :
      (openMessage decomp pp m).innerDecomp.get i =
        decomp.inner (Simple.commit ring pp.innerMatrix
          ((openMessage decomp pp m).messageDecomp.get i)) := by
    simp only [openMessage]
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
        ((openMessage decomp pp m).innerDecomp.get i) =
        Simple.commit ring pp.innerMatrix ((openMessage decomp pp m).messageDecomp.get i) := by
    rw [hmap]
    simpa [Simple.commit, gadgetMul] using
      hInnerDecomp
        (Simple.commit ring pp.innerMatrix ((openMessage decomp pp m).messageDecomp.get i))
  simp [Simple.verify, hprod]

variable [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
variable [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))]

/-- Inner-outer Ajtai commitments are perfectly correct for lawful decompositions. -/
theorem perfectlyCorrect (base : Coeff)
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    (hMessageDecomp : IsLawfulGadgetDecomposition ring base decomp.message)
    (hInnerDecomp : IsLawfulGadgetDecomposition ring base decomp.inner) :
    (commitmentScheme
      (outerRows := outerRows) (blocks := blocks) base decomp).PerfectlyCorrect := by
  classical
  intro pp _ m cd hmem
  simp only [commitmentScheme, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl
  let opening := openMessage decomp pp m
  have hMessage :
      (List.finRange blocks).all (fun i =>
        Simple.verify ring (gadgetMatrix ring base messageRows messageDigits)
          (opening.messageDecomp.get i) (m.get i) ()) = true := by
    simpa [opening] using openMessage_message_checks base decomp hMessageDecomp pp m
  have hInner :
      (List.finRange blocks).all (fun i =>
        Simple.verify ring (gadgetMatrix ring base innerRows innerDigits)
          (opening.innerDecomp.get i)
          (Simple.commit ring pp.innerMatrix (opening.messageDecomp.get i)) ()) = true := by
    simpa [opening] using openMessage_inner_checks base decomp hInnerDecomp pp m
  change
    verify base pp m
      (commitWithOpening pp opening)
      opening = true
  simp [verify, commitWithOpening, hMessage, hInner]

end Correctness

end InnerOuter
end Ajtai
end LatticeCrypto
