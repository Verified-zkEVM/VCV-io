/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.InnerOuter.Correctness
import LatticeCrypto.HardnessAssumptions.ModuleShortIntegerSolution
import LatticeCrypto.Ring.Laws
import LatticeCrypto.Ring.Norms
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Security of the Inner-Outer Ajtai Commitment (Weak Binding)
-/

open OracleComp ENNReal
open CommitmentScheme

universe u

namespace LatticeCrypto
namespace Ajtai
namespace InnerOuter

/-! ## Hachi/Greyhound Weak Binding -/

namespace WeakBinding

variable {Coeff : Type u} [CommRing Coeff]

/-! helper lemmas -/

lemma moduleSIS_relation_eq_true {ring : NegacyclicRing Coeff} {rows cols : Nat}
    [DecidableEq (PolyVec ring.Poly cols)] [DecidableEq (PolyVec ring.Poly rows)]
    (isShort : ModuleSIS.Solution ring cols → Bool)
    (A : PolyMatrix ring.Poly rows cols) (z : ModuleSIS.Solution ring cols)
    (hne : z ≠ 0) (hshort : isShort z = true)
    (hker : ring.matVecMul A z = 0) :
    ModuleSIS.relation ring isShort A z = true := by
  simp [ModuleSIS.relation, hne, hshort, hker]

lemma probOutput_pure_bool_le_or (win inner outer : Bool)
    (h : win = true → inner = true ∨ outer = true) :
    Pr[= true | ((pure win) : ProbComp Bool)] ≤
      Pr[= true | ((pure inner) : ProbComp Bool)] +
        Pr[= true | ((pure outer) : ProbComp Bool)] := by
  cases win <;> cases inner <;> cases outer <;> simp at h ⊢

lemma polyVec_sub_eq_zero_of_eq {ring : NegacyclicRing Coeff} {n : Nat}
    {x y : PolyVec ring.Poly n} (h : x = y) : x - y = 0 := by
  subst y
  apply Vector.ext
  intro i hi
  rw [show (0 : PolyVec ring.Poly n) =
    Vector.ofFn (fun _ : Fin n => (0 : ring.Poly)) by rfl]
  simp [Vector.getElem_sub]

lemma polyVec_sub_ne_zero_of_ne {ring : NegacyclicRing Coeff} {n : Nat}
    {x y : PolyVec ring.Poly n} (h : x ≠ y) : x - y ≠ 0 := by
  intro hzero
  apply h
  apply Vector.ext
  intro i hi
  have hget := congrArg (fun v : PolyVec ring.Poly n => v[i]) hzero
  have hcoordVec : x[i] - y[i] = (0 : PolyVec ring.Poly n)[i] := by
    simpa [Vector.getElem_sub] using hget
  have hzeroGet : (0 : PolyVec ring.Poly n)[i] = 0 := by
    rw [show (0 : PolyVec ring.Poly n) =
      Vector.ofFn (fun _ : Fin n => (0 : ring.Poly)) by rfl]
    simp
  exact sub_eq_zero.mp (hcoordVec.trans hzeroGet)

variable {ring : NegacyclicRing Coeff}

lemma block_eq_of_flattenBlocks_eq
    {blocks width : Nat} {xs ys : PolyVec (PolyVec ring.Poly width) blocks}
    (h : PolyVec.flattenBlocks xs = PolyVec.flattenBlocks ys) (i : Fin blocks) :
    xs.get i = ys.get i := by
  apply Vector.ext
  intro j hj
  exact PolyVec.get_get_eq_of_flattenBlocks_eq h i ⟨j, hj⟩

/-- The first block where two vectors differ, if one exists. -/
def firstDiff? {α : Type*} [DecidableEq α] {n : Nat}
    (x y : Vector α n) : Option (Fin n) :=
  Fin.find? fun i => x.get i != y.get i

/-- Boolean wrapper for the existence of a differing vector component. -/
def differs {α : Type*} [DecidableEq α] {n : Nat} (x y : Vector α n) : Bool :=
  (firstDiff? x y).isSome

lemma firstDiff?_some_of_differs {α : Type*} [DecidableEq α] {n : Nat}
    {x y : Vector α n} (h : differs x y = true) :
    ∃ i : Fin n, firstDiff? x y = some i := by
  unfold differs at h
  cases hfind : firstDiff? x y with
  | none => simp [hfind] at h
  | some i =>
      refine ⟨i, ?_⟩
      simp

lemma firstDiff?_eq_some_ne {α : Type*} [DecidableEq α] {n : Nat}
    {x y : Vector α n} {i : Fin n} (h : firstDiff? x y = some i) :
    x.get i ≠ y.get i := by
  have hmem : i ∈ firstDiff? x y := by
    simp [h]
  by_contra hxy
  simp [firstDiff?, hxy] at hmem

/-- inner/outer witness selection.

If the two outer witnesses are equal, use the first differing inner block;
otherwise use the outer difference witness. -/
def outputFromFirstDiff
    {α : Type*} [DecidableEq α]
    {innerCols outerCols blocks : Nat}
    [DecidableEq (PolyVec ring.Poly outerCols)]
    (x y : Vector α blocks)
    (flat₁ flat₂ : PolyVec ring.Poly outerCols)
    (innerSolution : Fin blocks → ModuleSIS.Solution ring innerCols) :
    Sum (ModuleSIS.Solution ring innerCols) (ModuleSIS.Solution ring outerCols) :=
  if flat₁ == flat₂ then
    match firstDiff? x y with
    | some i => Sum.inl (innerSolution i)
    | none => Sum.inr (flat₁ - flat₂)
  else
    Sum.inr (flat₁ - flat₂)


/-- Trivial fallback witness used on the branch where the other matrix yields the SIS witness. -/
def dummySolution (ring : NegacyclicRing Coeff) (cols : Nat) :
    ModuleSIS.Solution ring cols :=
  Vector.ofFn fun _ => 0

variable {ring : NegacyclicRing Coeff}

/-- A Hachi/Greyhound weak opening for the non-hiding inner-outer commitment.

Here `message` is the tuple `(sᵢ)ᵢ`, `innerDecomp` is `(t̂ᵢ)ᵢ`, and `challenge`
is `(cᵢ)ᵢ`. -/
structure Opening (ring : NegacyclicRing Coeff)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) where
  message : PolyVec (PolyVec ring.Poly (messageRows * messageDigits)) blocks
  innerDecomp : PolyVec (PolyVec ring.Poly (innerRows * innerDigits)) blocks
  challenge : PolyVec ring.Poly blocks

section Scheme

variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
variable [DecidableEq (PolyVec ring.Poly (messageRows * messageDigits))]
variable [DecidableEq (PolyVec ring.Poly (blocks * (innerRows * innerDigits)))]
variable [DecidableEq (PolyVec ring.Poly innerRows)]
variable [DecidableEq (Commitment ring outerRows)]

/-- Verify a Hachi/Greyhound weak opening. -/
def verify_weak (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    (betaSq gammaSq kappa : Nat)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (u : Commitment ring outerRows)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  (List.finRange blocks).all (fun i =>
    scalarLaws.isUnitLike (opening.challenge.get i) &&
      decide (normOps.l1Norm (opening.challenge.get i) ≤ kappa) &&
      decide (PolyVec.l2NormSq normOps
          (NegacyclicRing.scalarVecMul ring (opening.challenge.get i) (opening.message.get i)) ≤
        betaSq) &&
      Simple.verify ring (gadgetMatrix ring base innerRows innerDigits)
        (opening.innerDecomp.get i)
        (Simple.commit ring pp.innerMatrix (opening.message.get i)) ()) &&
    decide (PolyVec.l2NormSq normOps (PolyVec.flattenBlocks opening.innerDecomp) ≤ gammaSq) &&
    Simple.verify ring pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp) u ()

/-- A weak-binding adversary outputs two weak openings for the same commitment. -/
abbrev Adversary :=
  PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits →
    ProbComp
      (Commitment ring outerRows ×
        Opening ring innerRows messageRows messageDigits blocks innerDigits ×
        Opening ring innerRows messageRows messageDigits blocks innerDigits)

/-- Weak openings differ when they contain different message tuples `(sᵢ)ᵢ`. -/
def openingsDiffer
    (opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  differs opening₁.message opening₂.message

section Experiment

variable [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
variable [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))]

/-- The Hachi/Greyhound weak-binding experiment for the non-hiding commitment. -/
def experiment (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    (betaSq gammaSq kappa : Nat)
    (adv : Adversary (ring := ring) (innerRows := innerRows) (messageRows := messageRows)
      (messageDigits := messageDigits) (outerRows := outerRows) (blocks := blocks)
      (innerDigits := innerDigits)) :
    ProbComp Bool := do
  let A ← $ᵗ Simple.PublicParams ring innerRows (messageRows * messageDigits)
  let B ← $ᵗ Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits))
  let pp := { innerMatrix := A, outerMatrix := B }
  let (u, opening₁, opening₂) ← adv pp
  pure
    (openingsDiffer opening₁ opening₂ &&
      verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening₁ &&
      verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening₂)

/-- Weak-binding advantage for Hachi/Greyhound weak openings. -/
noncomputable def advantage (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    (betaSq gammaSq kappa : Nat)
    (adv : Adversary (ring := ring) (innerRows := innerRows) (messageRows := messageRows)
      (messageDigits := messageDigits) (outerRows := outerRows) (blocks := blocks)
      (innerDigits := innerDigits)) :
    ℝ≥0∞ :=
  Pr[= true | experiment base normOps scalarLaws betaSq gammaSq kappa adv]

end Experiment

/-- The scaled inner Module-SIS vector extracted from two weak openings. -/
def scaledMessage
    (opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits)
    (i : Fin blocks) : PolyVec ring.Poly (messageRows * messageDigits) :=
  NegacyclicRing.scalarVecMul ring
    (ring.mul (opening₁.challenge.get i) (opening₂.challenge.get i)) (opening₁.message.get i)

/-- Turn two weak openings into either an inner or outer Module-SIS witness. -/
def outputToModuleSIS
    (opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits) :
    Sum
      (ModuleSIS.Solution ring (messageRows * messageDigits))
      (ModuleSIS.Solution ring (blocks * (innerRows * innerDigits))) :=
  let flat₁ := PolyVec.flattenBlocks opening₁.innerDecomp
  let flat₂ := PolyVec.flattenBlocks opening₂.innerDecomp
  outputFromFirstDiff (ring := ring) (innerCols := messageRows * messageDigits)
    (outerCols := blocks * (innerRows * innerDigits)) (blocks := blocks)
    opening₁.message opening₂.message flat₁ flat₂ fun i =>
    scaledMessage opening₁ opening₂ i - scaledMessage opening₂ opening₁ i

/-- Per-block facts obtained from a successful weak-opening verification. -/
structure VerifiedBlock (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    (betaSq kappa : Nat)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits)
    (i : Fin blocks) : Prop where
  unit : scalarLaws.isUnitLike (opening.challenge.get i) = true
  challenge_short : normOps.l1Norm (opening.challenge.get i) ≤ kappa
  scaled_short :
    PolyVec.l2NormSq normOps
        (NegacyclicRing.scalarVecMul ring (opening.challenge.get i) (opening.message.get i)) ≤
      betaSq
  inner_eq :
    Simple.commit ring (gadgetMatrix ring base innerRows innerDigits)
      (opening.innerDecomp.get i) =
      Simple.commit ring pp.innerMatrix (opening.message.get i)

/-- Facts obtained from a successful weak-opening verification. -/
structure VerifiedOpening (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    (betaSq gammaSq kappa : Nat)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (u : Commitment ring outerRows)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) : Prop where
  outer_eq :
    Simple.commit ring pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp) = u
  outer_short : PolyVec.l2NormSq normOps (PolyVec.flattenBlocks opening.innerDecomp) ≤ gammaSq
  block : ∀ i : Fin blocks, VerifiedBlock base normOps scalarLaws betaSq kappa pp opening i

omit [DecidableEq (PolyVec ring.Poly (messageRows * messageDigits))]
  [DecidableEq (PolyVec ring.Poly (blocks * (innerRows * innerDigits)))] in
/-- Extract reusable weak-opening facts from the verifier. -/
theorem verifiedOpening_of_verify_eq_true
    {base : Coeff}
    {normOps : NormOps ring.backend} {scalarLaws : NegacyclicRing.ScalarMulLaws ring}
    {betaSq gammaSq kappa : Nat}
    {pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits}
    {u : Commitment ring outerRows}
    {opening : Opening ring innerRows messageRows messageDigits blocks innerDigits}
    (hverify : verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening = true) :
    VerifiedOpening base normOps scalarLaws betaSq gammaSq kappa pp u opening := by
  have hv := hverify
  simp only [verify_weak, Bool.and_eq_true] at hv
  refine ⟨?_, ?_, ?_⟩
  · simpa using
      (Simple.verify_eq_true_iff ring pp.outerMatrix
        (PolyVec.flattenBlocks opening.innerDecomp) u ()).1 hv.2
  · simpa [decide_eq_true_eq] using hv.1.2
  · intro i
    have hAll :
        ∀ i ∈ List.finRange blocks,
          scalarLaws.isUnitLike (opening.challenge.get i) &&
            decide (normOps.l1Norm (opening.challenge.get i) ≤ kappa) &&
            decide (PolyVec.l2NormSq normOps
                (NegacyclicRing.scalarVecMul ring (opening.challenge.get i)
                  (opening.message.get i)) ≤ betaSq) &&
            Simple.verify ring (gadgetMatrix ring base innerRows innerDigits)
              (opening.innerDecomp.get i)
              (Simple.commit ring pp.innerMatrix (opening.message.get i)) () = true := by
      simpa [List.all_eq_true] using hv.1.1
    have hBlock :
        ((scalarLaws.isUnitLike (opening.challenge.get i) = true ∧
            decide (normOps.l1Norm (opening.challenge.get i) ≤ kappa) = true) ∧
          decide (PolyVec.l2NormSq normOps
              (NegacyclicRing.scalarVecMul ring (opening.challenge.get i)
                (opening.message.get i)) ≤ betaSq) = true) ∧
          Simple.verify ring (gadgetMatrix ring base innerRows innerDigits)
            (opening.innerDecomp.get i)
            (Simple.commit ring pp.innerMatrix (opening.message.get i)) () = true := by
      simpa [Bool.and_eq_true] using hAll i (List.mem_finRange i)
    refine ⟨hBlock.1.1.1, ?_, ?_, ?_⟩
    · simpa [decide_eq_true_eq] using hBlock.1.1.2
    · simpa [decide_eq_true_eq] using hBlock.1.2
    · exact
        (Simple.verify_eq_true_iff ring
          (gadgetMatrix ring base innerRows innerDigits)
          (opening.innerDecomp.get i)
        (Simple.commit ring pp.innerMatrix (opening.message.get i)) ()).1 hBlock.2

omit [DecidableEq (PolyVec ring.Poly (messageRows * messageDigits))]
  [DecidableEq (PolyVec ring.Poly (blocks * (innerRows * innerDigits)))]
  [DecidableEq (PolyVec ring.Poly innerRows)] [DecidableEq (Commitment ring outerRows)] in
/-- Verified blocks preserve message inequality after challenge scaling. -/
theorem scaledMessage_ne_of_message_ne
    (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    {base : Coeff} {normOps : NormOps ring.backend} {betaSq kappa : Nat}
    {pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits}
    {opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits}
    {i : Fin blocks}
    (hBlock₁ : VerifiedBlock base normOps scalarLaws betaSq kappa pp opening₁ i)
    (hBlock₂ : VerifiedBlock base normOps scalarLaws betaSq kappa pp opening₂ i)
    (hmsgNe : opening₁.message.get i ≠ opening₂.message.get i) :
    scaledMessage opening₁ opening₂ i ≠ scaledMessage opening₂ opening₁ i :=
  NegacyclicRing.ScalarMulLaws.scalarVecMul_mul_ne_of_ne
    scalarLaws hBlock₁.unit hBlock₂.unit hmsgNe

omit [DecidableEq (PolyVec ring.Poly (messageRows * messageDigits))]
  [DecidableEq (PolyVec ring.Poly (blocks * (innerRows * innerDigits)))]
  [DecidableEq (PolyVec ring.Poly innerRows)] [DecidableEq (Commitment ring outerRows)] in
/-- A verified block pair yields the required bound for a scaled message. -/
theorem scaledMessage_l2NormSq_le
    {normOps : NormOps ring.backend}
    (normLaws : NegacyclicRing.ScalarNormLaws ring normOps)
    {base : Coeff} {scalarLaws : NegacyclicRing.ScalarMulLaws ring}
    {betaSq kappa : Nat}
    {pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits}
    {opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits}
    {i : Fin blocks}
    (hBlock₁ : VerifiedBlock base normOps scalarLaws betaSq kappa pp opening₁ i)
    (hBlock₂ : VerifiedBlock base normOps scalarLaws betaSq kappa pp opening₂ i) :
    PolyVec.l2NormSq normOps (scaledMessage opening₁ opening₂ i) ≤
      normLaws.scalarVecMulMulL2NormSqBound kappa betaSq := by
  simpa [scaledMessage] using
    normLaws.scalarVecMul_mul_l2NormSq_le (opening₁.challenge.get i)
      (opening₂.challenge.get i) (opening₁.message.get i)
      hBlock₂.challenge_short hBlock₁.scaled_short

omit [DecidableEq (PolyVec ring.Poly (messageRows * messageDigits))]
  [DecidableEq (PolyVec ring.Poly (blocks * (innerRows * innerDigits)))]
  [DecidableEq (PolyVec ring.Poly innerRows)] [DecidableEq (Commitment ring outerRows)] in
/-- Equal flattened inner decompositions make verified inner messages collide. -/
theorem inner_commit_eq_of_flatten_eq
    {base : Coeff} {normOps : NormOps ring.backend}
    {scalarLaws : NegacyclicRing.ScalarMulLaws ring} {betaSq gammaSq kappa : Nat}
    {pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits}
    {u : Commitment ring outerRows}
    {opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits}
    (hv₁ : VerifiedOpening base normOps scalarLaws betaSq gammaSq kappa pp u opening₁)
    (hv₂ : VerifiedOpening base normOps scalarLaws betaSq gammaSq kappa pp u opening₂)
    (hflat :
      PolyVec.flattenBlocks opening₁.innerDecomp = PolyVec.flattenBlocks opening₂.innerDecomp)
    (i : Fin blocks) :
    Simple.commit ring pp.innerMatrix (opening₁.message.get i) =
      Simple.commit ring pp.innerMatrix (opening₂.message.get i) := by
  have hblock : opening₁.innerDecomp.get i = opening₂.innerDecomp.get i :=
    block_eq_of_flattenBlocks_eq hflat i
  calc
    Simple.commit ring pp.innerMatrix (opening₁.message.get i) =
        Simple.commit ring (gadgetMatrix ring base innerRows innerDigits)
          (opening₁.innerDecomp.get i) := (hv₁.block i).inner_eq.symm
    _ = Simple.commit ring (gadgetMatrix ring base innerRows innerDigits)
          (opening₂.innerDecomp.get i) := by rw [hblock]
    _ = Simple.commit ring pp.innerMatrix (opening₂.message.get i) := (hv₂.block i).inner_eq

omit [DecidableEq (PolyVec ring.Poly (blocks * (innerRows * innerDigits)))]
  [DecidableEq (Commitment ring outerRows)] in
/-- Verified weak blocks give a valid inner Module-SIS relation. -/
theorem inner_relation_of_verified
    (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    (linearLaws : NegacyclicRing.LinearLaws ring)
    {normOps : NormOps ring.backend}
    (normLaws : NegacyclicRing.ScalarNormLaws ring normOps)
    {base : Coeff} {betaSq gammaSq kappa : Nat}
    {pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits}
    {u : Commitment ring outerRows}
    {opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits}
    (hv₁ : VerifiedOpening base normOps scalarLaws betaSq gammaSq kappa pp u opening₁)
    (hv₂ : VerifiedOpening base normOps scalarLaws betaSq gammaSq kappa pp u opening₂)
    (hflat :
      PolyVec.flattenBlocks opening₁.innerDecomp = PolyVec.flattenBlocks opening₂.innerDecomp)
    {i : Fin blocks} (hmsgNe : opening₁.message.get i ≠ opening₂.message.get i) :
    ModuleSIS.relation ring
      (fun z : ModuleSIS.Solution ring (messageRows * messageDigits) =>
        decide (PolyVec.l2NormSq normOps z ≤
          normLaws.subL2NormSqBound
            (normLaws.scalarVecMulMulL2NormSqBound kappa betaSq)))
      pp.innerMatrix
      (scaledMessage opening₁ opening₂ i - scaledMessage opening₂ opening₁ i) = true := by
  have hBlock₁ := hv₁.block i
  have hBlock₂ := hv₂.block i
  have hscaledNe : scaledMessage opening₁ opening₂ i ≠ scaledMessage opening₂ opening₁ i :=
    scaledMessage_ne_of_message_ne scalarLaws hBlock₁ hBlock₂ hmsgNe
  have hne :
      scaledMessage opening₁ opening₂ i - scaledMessage opening₂ opening₁ i ≠ 0 :=
    polyVec_sub_ne_zero_of_ne hscaledNe
  have hshort :
      (fun z : ModuleSIS.Solution ring (messageRows * messageDigits) =>
        decide (PolyVec.l2NormSq normOps z ≤
          normLaws.subL2NormSqBound
            (normLaws.scalarVecMulMulL2NormSqBound kappa betaSq)))
        (scaledMessage opening₁ opening₂ i - scaledMessage opening₂ opening₁ i) = true := by
    have hleft := scaledMessage_l2NormSq_le normLaws hBlock₁ hBlock₂
    have hright := scaledMessage_l2NormSq_le normLaws hBlock₂ hBlock₁
    have hdiff := normLaws.sub_l2NormSq_le
      (scaledMessage opening₁ opening₂ i) (scaledMessage opening₂ opening₁ i)
      hleft hright
    simp [hdiff]
  have hinnerEq := inner_commit_eq_of_flatten_eq hv₁ hv₂ hflat i
  have heq :
      ring.matVecMul pp.innerMatrix (scaledMessage opening₁ opening₂ i) =
        ring.matVecMul pp.innerMatrix (scaledMessage opening₂ opening₁ i) := by
    simpa [Simple.commit, scaledMessage] using
      NegacyclicRing.ScalarMulLaws.matVecMul_scalarVecMul_mul_eq_of_eq
        scalarLaws pp.innerMatrix (opening₁.challenge.get i) (opening₂.challenge.get i)
        (by simpa [Simple.commit] using hinnerEq)
  have hker :
      ring.matVecMul pp.innerMatrix
          (scaledMessage opening₁ opening₂ i - scaledMessage opening₂ opening₁ i) = 0 := by
    rw [linearLaws.matVecMul_sub pp.innerMatrix
      (scaledMessage opening₁ opening₂ i) (scaledMessage opening₂ opening₁ i)]
    exact polyVec_sub_eq_zero_of_eq heq
  exact moduleSIS_relation_eq_true _ pp.innerMatrix _ hne hshort hker

omit [DecidableEq (PolyVec ring.Poly (messageRows * messageDigits))]
  [DecidableEq (PolyVec ring.Poly innerRows)] in
/-- Verified weak openings with different flattened witnesses give a valid outer relation. -/
theorem outer_relation_of_verified
    (linearLaws : NegacyclicRing.LinearLaws ring)
    {base : Coeff} {normOps : NormOps ring.backend}
    (normLaws : NegacyclicRing.ScalarNormLaws ring normOps)
    {scalarLaws : NegacyclicRing.ScalarMulLaws ring} {betaSq gammaSq kappa : Nat}
    {pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits}
    {u : Commitment ring outerRows}
    {opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits}
    (hv₁ : VerifiedOpening base normOps scalarLaws betaSq gammaSq kappa pp u opening₁)
    (hv₂ : VerifiedOpening base normOps scalarLaws betaSq gammaSq kappa pp u opening₂)
    (hflat :
      PolyVec.flattenBlocks opening₁.innerDecomp ≠ PolyVec.flattenBlocks opening₂.innerDecomp) :
    ModuleSIS.relation ring
      (fun z : ModuleSIS.Solution ring (blocks * (innerRows * innerDigits)) =>
        decide (PolyVec.l2NormSq normOps z ≤ normLaws.subL2NormSqBound gammaSq))
      pp.outerMatrix
      (PolyVec.flattenBlocks opening₁.innerDecomp -
        PolyVec.flattenBlocks opening₂.innerDecomp) = true := by
  have hne :
      PolyVec.flattenBlocks opening₁.innerDecomp -
          PolyVec.flattenBlocks opening₂.innerDecomp ≠ 0 :=
    polyVec_sub_ne_zero_of_ne hflat
  have hshort :
      (fun z : ModuleSIS.Solution ring (blocks * (innerRows * innerDigits)) =>
        decide (PolyVec.l2NormSq normOps z ≤ normLaws.subL2NormSqBound gammaSq))
        (PolyVec.flattenBlocks opening₁.innerDecomp -
          PolyVec.flattenBlocks opening₂.innerDecomp) = true := by
    have hdiff := normLaws.sub_l2NormSq_le
      (PolyVec.flattenBlocks opening₁.innerDecomp)
      (PolyVec.flattenBlocks opening₂.innerDecomp)
      hv₁.outer_short hv₂.outer_short
    simp [hdiff]
  have heq :
      ring.matVecMul pp.outerMatrix (PolyVec.flattenBlocks opening₁.innerDecomp) =
        ring.matVecMul pp.outerMatrix (PolyVec.flattenBlocks opening₂.innerDecomp) := by
    simpa [Simple.commit] using hv₁.outer_eq.trans hv₂.outer_eq.symm
  have hker :
      ring.matVecMul pp.outerMatrix
          (PolyVec.flattenBlocks opening₁.innerDecomp -
            PolyVec.flattenBlocks opening₂.innerDecomp) = 0 := by
    rw [linearLaws.matVecMul_sub pp.outerMatrix
      (PolyVec.flattenBlocks opening₁.innerDecomp)
      (PolyVec.flattenBlocks opening₂.innerDecomp)]
    exact polyVec_sub_eq_zero_of_eq heq
  exact moduleSIS_relation_eq_true _ pp.outerMatrix _ hne hshort hker

/-- A successful pair of weak openings yields either an inner or outer Module-SIS witness. -/
theorem outputToModuleSIS_valid
    (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    (linearLaws : NegacyclicRing.LinearLaws ring)
    (normLaws : NegacyclicRing.ScalarNormLaws ring normOps)
    (betaSq gammaSq kappa : Nat)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (u : Commitment ring outerRows)
    (opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits)
    (hwin :
      (openingsDiffer opening₁ opening₂ &&
        verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening₁ &&
        verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening₂) = true) :
    match outputToModuleSIS opening₁ opening₂ with
    | Sum.inl z =>
        ModuleSIS.relation ring
          (fun z =>
            decide (PolyVec.l2NormSq normOps z ≤
              normLaws.subL2NormSqBound
                (normLaws.scalarVecMulMulL2NormSqBound kappa betaSq)))
          pp.innerMatrix z = true
    | Sum.inr z =>
        ModuleSIS.relation ring
          (fun z =>
            decide (PolyVec.l2NormSq normOps z ≤ normLaws.subL2NormSqBound gammaSq))
          pp.outerMatrix z = true := by
  simp only [Bool.and_eq_true] at hwin
  rcases hwin with ⟨⟨hdiff, hverify₁⟩, hverify₂⟩
  have hv₁ := verifiedOpening_of_verify_eq_true hverify₁
  have hv₂ := verifiedOpening_of_verify_eq_true hverify₂
  let flat₁ := PolyVec.flattenBlocks opening₁.innerDecomp
  let flat₂ := PolyVec.flattenBlocks opening₂.innerDecomp
  by_cases hflat : flat₁ = flat₂
  · obtain ⟨i, hfind⟩ := firstDiff?_some_of_differs hdiff
    have hmsgNe : opening₁.message.get i ≠ opening₂.message.get i :=
      firstDiff?_eq_some_ne hfind
    have hrel := inner_relation_of_verified scalarLaws linearLaws normLaws hv₁ hv₂
      (by simpa [flat₁, flat₂] using hflat) hmsgNe
    simpa [outputToModuleSIS, outputFromFirstDiff, flat₁, flat₂, hflat, hfind]
      using hrel
  · have hrel := outer_relation_of_verified linearLaws normLaws hv₁ hv₂
      (by simpa [flat₁, flat₂] using hflat)
    simpa [outputToModuleSIS, outputFromFirstDiff, flat₁, flat₂, hflat] using hrel

section Advantages

variable [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
variable [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))]

/-- Reduction that uses a weak-binding adversary to attack the inner Module-SIS matrix. -/
def innerAdvToModuleSIS
    (isShort : ModuleSIS.Solution ring (messageRows * messageDigits) → Bool)
    (adv : Adversary (ring := ring) (innerRows := innerRows) (messageRows := messageRows)
      (messageDigits := messageDigits) (outerRows := outerRows) (blocks := blocks)
      (innerDigits := innerDigits)) :
    ModuleSIS.Adversary ring innerRows (messageRows * messageDigits) isShort :=
  fun A => do
    let B ← $ᵗ Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits))
    let pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits :=
      { innerMatrix := A, outerMatrix := B }
    let (_u, opening₁, opening₂) ← adv pp
    match outputToModuleSIS opening₁ opening₂ with
    | Sum.inl z => pure z
    | Sum.inr _ => pure (dummySolution ring (messageRows * messageDigits))

/-- Reduction that uses a weak-binding adversary to attack the outer Module-SIS matrix. -/
def outerAdvToModuleSIS
    (isShort : ModuleSIS.Solution ring (blocks * (innerRows * innerDigits)) → Bool)
    (adv : Adversary (ring := ring) (innerRows := innerRows) (messageRows := messageRows)
      (messageDigits := messageDigits) (outerRows := outerRows) (blocks := blocks)
      (innerDigits := innerDigits)) :
    ModuleSIS.Adversary ring outerRows (blocks * (innerRows * innerDigits)) isShort :=
  fun B => do
    let A ← $ᵗ Simple.PublicParams ring innerRows (messageRows * messageDigits)
    let pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits :=
      { innerMatrix := A, outerMatrix := B }
    let (_u, opening₁, opening₂) ← adv pp
    match outputToModuleSIS opening₁ opening₂ with
    | Sum.inl _ => pure (dummySolution ring (blocks * (innerRows * innerDigits)))
    | Sum.inr z => pure z

omit [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))] in
/-- Pointwise form of the weak-binding to Module-SIS advantage bound. -/
theorem sample_advantage_le_moduleSIS (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    (linearLaws : NegacyclicRing.LinearLaws ring)
    (normLaws : NegacyclicRing.ScalarNormLaws ring normOps)
    (betaSq gammaSq kappa : Nat)
    (A : Simple.PublicParams ring innerRows (messageRows * messageDigits))
    (B : Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))
    (u : Commitment ring outerRows)
    (opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits) :
    probOutput
        ((pure
          (openingsDiffer opening₁ opening₂ &&
            verify_weak base normOps scalarLaws betaSq gammaSq kappa
              { innerMatrix := A, outerMatrix := B } u opening₁ &&
            verify_weak base normOps scalarLaws betaSq gammaSq kappa
              { innerMatrix := A, outerMatrix := B } u opening₂)) : ProbComp Bool)
        true ≤
      probOutput
          ((ModuleSIS.relation ring
            (fun z =>
              decide (PolyVec.l2NormSq normOps z ≤
                normLaws.subL2NormSqBound
                  (normLaws.scalarVecMulMulL2NormSqBound kappa betaSq)))
            A <$> match outputToModuleSIS opening₁ opening₂ with
              | Sum.inl z => pure z
              | Sum.inr _ => pure (dummySolution ring (messageRows * messageDigits))) :
            ProbComp Bool)
          true +
        probOutput
          ((ModuleSIS.relation ring
            (fun z =>
              decide (PolyVec.l2NormSq normOps z ≤ normLaws.subL2NormSqBound gammaSq))
            B <$> match outputToModuleSIS opening₁ opening₂ with
              | Sum.inl _ => pure (dummySolution ring (blocks * (innerRows * innerDigits)))
              | Sum.inr z => pure z) : ProbComp Bool)
          true := by
  let pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits :=
    { innerMatrix := A, outerMatrix := B }
  cases hsol : outputToModuleSIS opening₁ opening₂ with
  | inl z =>
      simpa [hsol, pp] using
        probOutput_pure_bool_le_or
          (openingsDiffer opening₁ opening₂ &&
            verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening₁ &&
            verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening₂)
            (ModuleSIS.relation ring
            (fun z =>
              decide (PolyVec.l2NormSq normOps z ≤
                normLaws.subL2NormSqBound
                  (normLaws.scalarVecMulMulL2NormSqBound kappa betaSq)))
            A z)
          (ModuleSIS.relation ring
            (fun z =>
              decide (PolyVec.l2NormSq normOps z ≤
                normLaws.subL2NormSqBound gammaSq))
            B (dummySolution ring (blocks * (innerRows * innerDigits))))
          (by
            intro hwin
            left
            have hvalid := outputToModuleSIS_valid (base := base)
              (normOps := normOps) (scalarLaws := scalarLaws)
              (linearLaws := linearLaws) (normLaws := normLaws)
              (betaSq := betaSq) (gammaSq := gammaSq) (kappa := kappa)
              pp u opening₁ opening₂ hwin
            have hvalidInner :
                ModuleSIS.relation ring
                  (fun z =>
                    decide (PolyVec.l2NormSq normOps z ≤
                      normLaws.subL2NormSqBound
                        (normLaws.scalarVecMulMulL2NormSqBound kappa betaSq)))
                  pp.innerMatrix z = true := by
              simpa [hsol] using hvalid
            simpa [pp] using hvalidInner)
  | inr z =>
      simpa [hsol, pp] using
        probOutput_pure_bool_le_or
          (openingsDiffer opening₁ opening₂ &&
            verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening₁ &&
            verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening₂)
          (ModuleSIS.relation ring
            (fun z =>
              decide (PolyVec.l2NormSq normOps z ≤
                normLaws.subL2NormSqBound
                  (normLaws.scalarVecMulMulL2NormSqBound kappa betaSq)))
            A (dummySolution ring (messageRows * messageDigits)))
          (ModuleSIS.relation ring
            (fun z =>
              decide (PolyVec.l2NormSq normOps z ≤
                normLaws.subL2NormSqBound gammaSq))
            B z)
          (by
            intro hwin
            right
            have hvalid := outputToModuleSIS_valid (base := base)
              (normOps := normOps) (scalarLaws := scalarLaws)
              (linearLaws := linearLaws) (normLaws := normLaws)
              (betaSq := betaSq) (gammaSq := gammaSq) (kappa := kappa)
              pp u opening₁ opening₂ hwin
            have hvalidOuter :
                ModuleSIS.relation ring
                  (fun z =>
                    decide (PolyVec.l2NormSq normOps z ≤
                      normLaws.subL2NormSqBound gammaSq))
                  pp.outerMatrix z = true := by
              simpa [hsol] using hvalid
            simpa [pp] using hvalidOuter)

-- The direct Module-SIS RHS unfolds to reductions with swapped independent samples.
/-- Hachi/Greyhound weak binding is bounded by the extracted Module-SIS advantages. -/
theorem advantage_le_moduleSIS (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    (linearLaws : NegacyclicRing.LinearLaws ring)
    (normLaws : NegacyclicRing.ScalarNormLaws ring normOps)
    (betaSq gammaSq kappa : Nat)
    (adv : Adversary (ring := ring) (innerRows := innerRows) (messageRows := messageRows)
      (messageDigits := messageDigits) (outerRows := outerRows) (blocks := blocks)
      (innerDigits := innerDigits))
    :
    advantage base normOps scalarLaws betaSq gammaSq kappa adv ≤
      ModuleSIS.advantage ring innerRows (messageRows * messageDigits)
          (fun z =>
            decide (PolyVec.l2NormSq normOps z ≤
              normLaws.subL2NormSqBound
                (normLaws.scalarVecMulMulL2NormSqBound kappa betaSq)))
          (innerAdvToModuleSIS
            (fun z =>
              decide (PolyVec.l2NormSq normOps z ≤
                normLaws.subL2NormSqBound
                  (normLaws.scalarVecMulMulL2NormSqBound kappa betaSq)))
            adv) +
        ModuleSIS.advantage ring outerRows (blocks * (innerRows * innerDigits))
          (fun z =>
            decide (PolyVec.l2NormSq normOps z ≤ normLaws.subL2NormSqBound gammaSq))
          (outerAdvToModuleSIS
            (fun z =>
              decide (PolyVec.l2NormSq normOps z ≤ normLaws.subL2NormSqBound gammaSq))
            adv) := by
  unfold advantage experiment
    ModuleSIS.advantage SIS.advantage SIS.experiment ModuleSIS.problem
    innerAdvToModuleSIS outerAdvToModuleSIS
  simp only [monad_norm]
  rw [← probOutput_bind_bind_swap
    (mx := (($ᵗ PolyMatrix ring.Poly innerRows (messageRows * messageDigits)) :
      ProbComp (PolyMatrix ring.Poly innerRows (messageRows * messageDigits))))
    (my := (($ᵗ PolyMatrix ring.Poly outerRows (blocks * (innerRows * innerDigits))) :
      ProbComp (PolyMatrix ring.Poly outerRows (blocks * (innerRows * innerDigits)))))
    (z := true)]
  refine (probOutput_bind_congr_le_add
    (mx := (($ᵗ PolyMatrix ring.Poly innerRows (messageRows * messageDigits)) :
      ProbComp (PolyMatrix ring.Poly innerRows (messageRows * messageDigits))))
    (y := true) (z₁ := true) (z₂ := true)) ?_
  intro A _
  refine (probOutput_bind_congr_le_add
    (mx := (($ᵗ PolyMatrix ring.Poly outerRows (blocks * (innerRows * innerDigits))) :
      ProbComp (PolyMatrix ring.Poly outerRows (blocks * (innerRows * innerDigits)))))
    (y := true) (z₁ := true) (z₂ := true)) ?_
  intro B _
  refine (probOutput_bind_congr_le_add
    (mx := (adv { innerMatrix := A, outerMatrix := B } :
      ProbComp (Commitment ring outerRows ×
        Opening ring innerRows messageRows messageDigits blocks innerDigits ×
        Opening ring innerRows messageRows messageDigits blocks innerDigits)))
    (y := true) (z₁ := true) (z₂ := true)) ?_
  intro ⟨u, opening₁, opening₂⟩ _
  simpa using sample_advantage_le_moduleSIS base normOps scalarLaws linearLaws normLaws
    betaSq gammaSq kappa A B u opening₁ opening₂

end Advantages

end Scheme

end WeakBinding


end InnerOuter
end Ajtai
end LatticeCrypto
