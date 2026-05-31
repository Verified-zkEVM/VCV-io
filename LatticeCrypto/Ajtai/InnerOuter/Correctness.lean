/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.InnerOuter.Scheme
import LatticeCrypto.Ajtai.Simple.Correctness

/-!
# Correctness of the Inner-Outer Ajtai Commitment

Perfect correctness of the inner-outer Ajtai commitment over the canonical
vector-backed negacyclic ring `vectorNegacyclicRing (ZMod q) d`.
-/

open OracleComp ENNReal
open CommitmentScheme

namespace LatticeCrypto
namespace Ajtai
namespace InnerOuter

variable {q : ℕ} [NeZero q] [Fact (1 < q)] {d : ℕ} [NeZero d]

variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
variable [DecidableEq (PolyVec (vectorNegacyclicRing (ZMod q) d).Poly messageRows)]
variable [DecidableEq (PolyVec (vectorNegacyclicRing (ZMod q) d).Poly innerRows)]
variable [DecidableEq (Commitment (vectorNegacyclicRing (ZMod q) d) outerRows)]

section Correctness

omit [NeZero q] [Fact (1 < q)] [NeZero d]
  [DecidableEq (PolyVec (R).Poly innerRows)] [DecidableEq (Commitment R outerRows)] in
/-- Honest message decompositions pass the message gadget checks. -/
theorem openMessage_message_checks (base : ZMod q)
    (decomp : Decomposition R messageRows messageDigits innerRows innerDigits)
    (hMessageDecomp : IsLawfulGadgetDecomposition R base decomp.message)
    (pp : PublicParams R innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message R messageRows blocks) :
    (List.finRange blocks).all (fun i =>
      Simple.verify R (gadgetMatrix R base messageRows messageDigits)
        ((openMessage decomp pp m).messageDecomp.get i) (m.get i) ()) = true := by
  simp only [List.all_eq_true]
  intro i _hi
  have hmap :
      (openMessage decomp pp m).messageDecomp.get i = decomp.message (m.get i) := by
    simp only [openMessage]
    change (Vector.map decomp.message m)[i.val] = decomp.message (m[i.val])
    simp
  have hprod :
      Simple.commit R (gadgetMatrix R base messageRows messageDigits)
        ((openMessage decomp pp m).messageDecomp.get i) = m.get i := by
    rw [hmap]
    simpa [Simple.commit, gadgetMul] using hMessageDecomp (m.get i)
  simp [Simple.verify, hprod]

omit [NeZero q] [Fact (1 < q)] [NeZero d]
  [DecidableEq (PolyVec (R).Poly messageRows)] [DecidableEq (Commitment R outerRows)] in
/-- Honest inner decompositions pass the inner gadget checks. -/
theorem openMessage_inner_checks (base : ZMod q)
    (decomp : Decomposition R messageRows messageDigits innerRows innerDigits)
    (hInnerDecomp : IsLawfulGadgetDecomposition R base decomp.inner)
    (pp : PublicParams R innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message R messageRows blocks) :
    (List.finRange blocks).all (fun i =>
      Simple.verify R (gadgetMatrix R base innerRows innerDigits)
        ((openMessage decomp pp m).innerDecomp.get i)
        (Simple.commit R pp.innerMatrix ((openMessage decomp pp m).messageDecomp.get i))
        ()) = true := by
  simp only [List.all_eq_true]
  intro i _hi
  have hmap :
      (openMessage decomp pp m).innerDecomp.get i =
        decomp.inner (Simple.commit R pp.innerMatrix
          ((openMessage decomp pp m).messageDecomp.get i)) := by
    simp only [openMessage]
    change
      (Vector.map (fun s => decomp.inner (Simple.commit R pp.innerMatrix s))
        (Vector.map decomp.message m)).get i =
        decomp.inner
          (Simple.commit R pp.innerMatrix ((Vector.map decomp.message m).get i))
    change
      (Vector.map (fun s => decomp.inner (Simple.commit R pp.innerMatrix s))
        (Vector.map decomp.message m))[i.val] =
        decomp.inner
          (Simple.commit R pp.innerMatrix ((Vector.map decomp.message m)[i.val]))
    simp
  have hprod :
      Simple.commit R (gadgetMatrix R base innerRows innerDigits)
        ((openMessage decomp pp m).innerDecomp.get i) =
        Simple.commit R pp.innerMatrix ((openMessage decomp pp m).messageDecomp.get i) := by
    rw [hmap]
    simpa [Simple.commit, gadgetMul] using
      hInnerDecomp
        (Simple.commit R pp.innerMatrix ((openMessage decomp pp m).messageDecomp.get i))
  simp [Simple.verify, hprod]

variable [SampleableType
  (Simple.PublicParams (vectorNegacyclicRing (ZMod q) d) innerRows (messageRows * messageDigits))]
variable [SampleableType
  (Simple.PublicParams (vectorNegacyclicRing (ZMod q) d) outerRows
    (blocks * (innerRows * innerDigits)))]

omit [NeZero q] [Fact (1 < q)] [NeZero d] in
/-- Inner-outer Ajtai commitments are perfectly correct for lawful decompositions. -/
theorem perfectlyCorrect (base : ZMod q)
    (decomp : Decomposition R messageRows messageDigits innerRows innerDigits)
    (hMessageDecomp : IsLawfulGadgetDecomposition R base decomp.message)
    (hInnerDecomp : IsLawfulGadgetDecomposition R base decomp.inner) :
    (commitmentScheme
      (outerRows := outerRows) (blocks := blocks) base decomp).PerfectlyCorrect := by
  intro pp _ m cd hmem
  simp only [commitmentScheme, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl
  let opening := openMessage decomp pp m
  have hMessage :
      (List.finRange blocks).all (fun i =>
        Simple.verify R (gadgetMatrix R base messageRows messageDigits)
          (opening.messageDecomp.get i) (m.get i) ()) = true := by
    simpa [opening] using openMessage_message_checks base decomp hMessageDecomp pp m
  have hInner :
      (List.finRange blocks).all (fun i =>
        Simple.verify R (gadgetMatrix R base innerRows innerDigits)
          (opening.innerDecomp.get i)
          (Simple.commit R pp.innerMatrix (opening.messageDecomp.get i)) ()) = true := by
    simpa [opening] using openMessage_inner_checks base decomp hInnerDecomp pp m
  change
    verify base pp m
      (commitWithOpening pp opening)
      opening = true
  simp [verify, commitWithOpening, hMessage, hInner]

/-- Correctness for the canonical base-two gadget decomposition.

This discharges the `IsLawfulGadgetDecomposition` hypotheses of `perfectlyCorrect`
via `binaryDecompose_lawful`: instantiating both the message and inner
decompositions with the base-two binary digit expansion `binaryDecompose` makes the
inner-outer commitment with base-two gadget `gadgetMatrix R 2` perfectly correct,
provided each digit count covers the modulus (`q ≤ 2 ^ messageDigits`, resp.
`q ≤ 2 ^ innerDigits`). No lawfulness is assumed; it is proven. -/
theorem perfectlyCorrect_base2
    (hmsgDigits : 0 < messageDigits) (hmsgCover : q ≤ 2 ^ messageDigits)
    (hinnerDigits : 0 < innerDigits) (hinnerCover : q ≤ 2 ^ innerDigits) :
    (commitmentScheme (outerRows := outerRows) (blocks := blocks) (2 : ZMod q)
        (({ message := binaryDecompose messageRows messageDigits
            inner := binaryDecompose innerRows innerDigits } :
          Decomposition R messageRows messageDigits innerRows innerDigits))).PerfectlyCorrect :=
  perfectlyCorrect (2 : ZMod q)
    (({ message := binaryDecompose messageRows messageDigits
        inner := binaryDecompose innerRows innerDigits } :
      Decomposition R messageRows messageDigits innerRows innerDigits))
    (binaryDecompose_lawful (n := d) messageRows messageDigits hmsgDigits hmsgCover)
    (binaryDecompose_lawful (n := d) innerRows innerDigits hinnerDigits hinnerCover)

end Correctness

end InnerOuter
end Ajtai
end LatticeCrypto
