/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Simple
import LatticeCrypto.HardnessAssumptions.ModuleShortIntegerSolution
import LatticeCrypto.Ring.Laws
import LatticeCrypto.Ring.Norms
import Mathlib.Data.Fin.Tuple.Basic
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

-- TODO drag the weak opening/verify defs up here.

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

section Correctness

lemma moduleSIS_relation_eq_true {ring : NegacyclicRing Coeff} {rows cols : Nat}
    [DecidableEq (PolyVec ring.Poly cols)] [DecidableEq (PolyVec ring.Poly rows)]
    (isShort : ModuleSIS.Solution ring cols → Bool)
    (A : PolyMatrix ring.Poly rows cols) (z : ModuleSIS.Solution ring cols)
    (hne : z.left ≠ z.right) (hshort : isShort z = true)
    (heq : ring.matVecMul A z.left = ring.matVecMul A z.right) :
    ModuleSIS.relation ring isShort A z = true := by
  simp [ModuleSIS.relation, hne, hshort, heq]

lemma probOutput_pure_bool_le_or (win inner outer : Bool)
    (h : win = true → inner = true ∨ outer = true) :
    Pr[= true | ((pure win) : ProbComp Bool)] ≤
      Pr[= true | ((pure inner) : ProbComp Bool)] +
        Pr[= true | ((pure outer) : ProbComp Bool)] := by
  cases win <;> cases inner <;> cases outer <;> simp at h ⊢

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

end Scheme

/-! ## Binding -/

namespace Binding

variable {ring : NegacyclicRing Coeff}

lemma exists_get_ne_of_ne {α : Type*} {n : Nat} {x y : Vector α n}
    (h : x ≠ y) : ∃ i : Fin n, x.get i ≠ y.get i := by
  by_contra hnone
  apply h
  apply Vector.ext
  intro i hi
  by_contra hxy
  exact hnone ⟨⟨i, hi⟩, hxy⟩

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

lemma firstDiff?_some_of_ne {α : Type*} [DecidableEq α] {n : Nat}
    {x y : Vector α n} (h : x ≠ y) :
    ∃ i : Fin n, firstDiff? x y = some i ∧ x.get i ≠ y.get i := by
  obtain ⟨i, hi⟩ := exists_get_ne_of_ne h
  let hdiff : ∃ i : Fin n, x.get i != y.get i := ⟨i, by simpa using hi⟩
  refine ⟨Fin.find (fun i => x.get i != y.get i) hdiff, ?_, ?_⟩
  · exact Fin.find?_eq_some_find_of_exists hdiff
  · simpa using Fin.find_spec hdiff

lemma firstDiff?_eq_some_ne {α : Type*} [DecidableEq α] {n : Nat}
    {x y : Vector α n} {i : Fin n} (h : firstDiff? x y = some i) :
    x.get i ≠ y.get i := by
  have hmem : i ∈ firstDiff? x y := by
    simp [h]
  by_contra hxy
  simp [firstDiff?, hxy] at hmem

/-- Common inner/outer witness selection used by ordinary and weak binding.

If the two outer witnesses are equal, use the first differing inner block;
otherwise use the outer collision. -/
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
    | none => Sum.inr { left := flat₁, right := flat₂ }
  else
    Sum.inr { left := flat₁, right := flat₂ }

section Scheme

variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
variable [DecidableEq (Message ring messageRows blocks)]
variable [DecidableEq (PolyVec ring.Poly messageRows)]
variable [DecidableEq (PolyVec ring.Poly innerRows)]
variable [DecidableEq (PolyVec ring.Poly outerRows)]
variable [DecidableEq (PolyVec ring.Poly (messageRows * messageDigits))]
variable [DecidableEq (PolyVec ring.Poly (blocks * (innerRows * innerDigits)))]

/-- Turn one successful binding output into either an inner or outer Module-SIS witness. -/
def outputToModuleSIS
    (m₁ m₂ : Message ring messageRows blocks)
    (opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits) :
    Sum
      (ModuleSIS.Solution ring (messageRows * messageDigits))
      (ModuleSIS.Solution ring (blocks * (innerRows * innerDigits))) :=
  let flat₁ := PolyVec.flattenBlocks opening₁.innerDecomp
  let flat₂ := PolyVec.flattenBlocks opening₂.innerDecomp
  outputFromFirstDiff (ring := ring) (innerCols := messageRows * messageDigits)
    (outerCols := blocks * (innerRows * innerDigits)) (blocks := blocks)
    m₁ m₂ flat₁ flat₂ fun i =>
    { left := opening₁.messageDecomp.get i
      right := opening₂.messageDecomp.get i }

/-- Trivial fallback witness used on the branch where the other matrix yields the collision. -/
def dummySolution (ring : NegacyclicRing Coeff) (cols : Nat) :
    ModuleSIS.Solution ring cols where
  left := Vector.ofFn fun _ => 0
  right := Vector.ofFn fun _ => 0

section Reductions

variable [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
variable [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))]

/-- Reduction that uses a binding adversary to attack the inner Module-SIS matrix. -/
def innerAdvToModuleSIS
    (adv : BindingAdv
      (PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
      (Message ring messageRows blocks)
      (Commitment ring outerRows)
      (Opening ring innerRows messageRows messageDigits blocks innerDigits)) :
    ModuleSIS.Adversary ring innerRows (messageRows * messageDigits) (fun _ => true) :=
  fun A => do
    let B ← $ᵗ Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits))
    let (_c, m₁, opening₁, m₂, opening₂) ← adv { innerMatrix := A, outerMatrix := B }
    match outputToModuleSIS m₁ m₂ opening₁ opening₂ with
    | Sum.inl z => pure z
    | Sum.inr _ => pure (dummySolution ring (messageRows * messageDigits))

/-- Reduction that uses a binding adversary to attack the outer Module-SIS matrix. -/
def outerAdvToModuleSIS
    (adv : BindingAdv
      (PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
      (Message ring messageRows blocks)
      (Commitment ring outerRows)
      (Opening ring innerRows messageRows messageDigits blocks innerDigits)) :
    ModuleSIS.Adversary ring outerRows (blocks * (innerRows * innerDigits)) (fun _ => true) :=
  fun B => do
    let A ← $ᵗ Simple.PublicParams ring innerRows (messageRows * messageDigits)
    let (_c, m₁, opening₁, m₂, opening₂) ← adv { innerMatrix := A, outerMatrix := B }
    match outputToModuleSIS m₁ m₂ opening₁ opening₂ with
    | Sum.inl _ => pure (dummySolution ring (blocks * (innerRows * innerDigits)))
    | Sum.inr z => pure z

end Reductions

/-- Facts obtained from a successful ordinary inner-outer opening verification. -/
structure VerifiedOpening (base : Coeff)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (c : Commitment ring outerRows) (m : Message ring messageRows blocks)
    (opening : Opening ring innerRows messageRows messageDigits blocks innerDigits) : Prop where
  outer_eq :
    Simple.commit ring pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp) = c
  message_eq :
    ∀ i : Fin blocks,
      Simple.commit ring (gadgetMatrix ring base messageRows messageDigits)
        (opening.messageDecomp.get i) = m.get i
  inner_eq :
    ∀ i : Fin blocks,
      Simple.commit ring (gadgetMatrix ring base innerRows innerDigits)
        (opening.innerDecomp.get i) =
        Simple.commit ring pp.innerMatrix (opening.messageDecomp.get i)

omit [DecidableEq (Message ring messageRows blocks)]
  [DecidableEq (PolyVec ring.Poly (messageRows * messageDigits))]
  [DecidableEq (PolyVec ring.Poly (blocks * (innerRows * innerDigits)))] in
/-- Extract component equations from a successful ordinary opening verification. -/
theorem verifiedOpening_of_verify_eq_true
    {base : Coeff}
    {pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits}
    {c : Commitment ring outerRows} {m : Message ring messageRows blocks}
    {opening : Opening ring innerRows messageRows messageDigits blocks innerDigits}
    (hverify : verify base pp m c opening = true) :
    VerifiedOpening base pp c m opening := by
  have hv := hverify
  simp only [verify, Bool.and_eq_true] at hv
  refine ⟨?_, ?_, ?_⟩
  · simpa using
      (Simple.verify_eq_true_iff ring pp.outerMatrix
        (PolyVec.flattenBlocks opening.innerDecomp) c ()).1 hv.2
  · intro i
    have hMessageAll :
        ∀ i ∈ List.finRange blocks,
          Simple.verify ring (gadgetMatrix ring base messageRows messageDigits)
            (opening.messageDecomp.get i) (m.get i) () = true := by
      simpa [List.all_eq_true] using hv.1.1
    exact
      (Simple.verify_eq_true_iff ring
        (gadgetMatrix ring base messageRows messageDigits)
        (opening.messageDecomp.get i) (m.get i) ()).1
        (hMessageAll i (List.mem_finRange i))
  · intro i
    have hInnerAll :
        ∀ i ∈ List.finRange blocks,
          Simple.verify ring (gadgetMatrix ring base innerRows innerDigits)
            (opening.innerDecomp.get i)
            (Simple.commit ring pp.innerMatrix (opening.messageDecomp.get i)) () = true := by
      simpa [List.all_eq_true] using hv.1.2
    exact
      (Simple.verify_eq_true_iff ring
        (gadgetMatrix ring base innerRows innerDigits)
        (opening.innerDecomp.get i)
        (Simple.commit ring pp.innerMatrix (opening.messageDecomp.get i)) ()).1
        (hInnerAll i (List.mem_finRange i))

/-- A successful double opening yields either an inner or an outer Module-SIS collision. -/
theorem outputToModuleSIS_valid
    (base : Coeff)
    (pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
    (c : Commitment ring outerRows)
    (m₁ m₂ : Message ring messageRows blocks)
    (opening₁ opening₂ :
      Opening ring innerRows messageRows messageDigits blocks innerDigits)
    (hwin :
      (decide (m₁ ≠ m₂) &&
        verify base pp m₁ c opening₁ &&
        verify base pp m₂ c opening₂) = true) :
    match outputToModuleSIS m₁ m₂ opening₁ opening₂ with
    | Sum.inl z => ModuleSIS.relation ring (fun _ => true) pp.innerMatrix z = true
    | Sum.inr z => ModuleSIS.relation ring (fun _ => true) pp.outerMatrix z = true := by
  classical
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
  rcases hwin with ⟨⟨hmNe, hverify₁⟩, hverify₂⟩
  have hv₁ := verifiedOpening_of_verify_eq_true hverify₁
  have hv₂ := verifiedOpening_of_verify_eq_true hverify₂
  let flat₁ := PolyVec.flattenBlocks opening₁.innerDecomp
  let flat₂ := PolyVec.flattenBlocks opening₂.innerDecomp
  by_cases hflat : flat₁ = flat₂
  · obtain ⟨i, hfind, hiNe⟩ := firstDiff?_some_of_ne hmNe
    have hsNe : opening₁.messageDecomp.get i ≠ opening₂.messageDecomp.get i := by
      intro hs
      apply hiNe
      calc
        m₁.get i = Simple.commit ring (gadgetMatrix ring base messageRows messageDigits)
            (opening₁.messageDecomp.get i) := (hv₁.message_eq i).symm
        _ = Simple.commit ring (gadgetMatrix ring base messageRows messageDigits)
            (opening₂.messageDecomp.get i) := by rw [hs]
        _ = m₂.get i := hv₂.message_eq i
    have hinnerEq :
        Simple.commit ring pp.innerMatrix (opening₁.messageDecomp.get i) =
          Simple.commit ring pp.innerMatrix (opening₂.messageDecomp.get i) := by
      have hblock : opening₁.innerDecomp.get i = opening₂.innerDecomp.get i :=
        block_eq_of_flattenBlocks_eq (by simpa [flat₁, flat₂] using hflat) i
      calc
        Simple.commit ring pp.innerMatrix (opening₁.messageDecomp.get i) =
            Simple.commit ring (gadgetMatrix ring base innerRows innerDigits)
              (opening₁.innerDecomp.get i) := (hv₁.inner_eq i).symm
        _ = Simple.commit ring (gadgetMatrix ring base innerRows innerDigits)
              (opening₂.innerDecomp.get i) := by rw [hblock]
        _ = Simple.commit ring pp.innerMatrix (opening₂.messageDecomp.get i) := hv₂.inner_eq i
    simp [outputToModuleSIS, outputFromFirstDiff, flat₁, flat₂, hflat, hfind,
      ModuleSIS.relation, hsNe]
    simpa [Simple.commit] using hinnerEq
  · have houterEq : Simple.commit ring pp.outerMatrix flat₁ =
        Simple.commit ring pp.outerMatrix flat₂ := by
      simpa [flat₁, flat₂] using hv₁.outer_eq.trans hv₂.outer_eq.symm
    simp [outputToModuleSIS, outputFromFirstDiff, flat₁, flat₂, hflat, ModuleSIS.relation]
    simpa [Simple.commit] using houterEq


section Advantages

variable [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
variable [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))]

-- TODO is there not a better solution to the M-SIS advantages than having these two definitions?
-- It should be possible to use the standard Module-SIS advantage definition.

/-- Inner contextual Module-SIS advantage extracted from a binding adversary. -/
noncomputable def innerModuleSISAdvantage
    (adv : BindingAdv
      (PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
      (Message ring messageRows blocks)
      (Commitment ring outerRows)
      (Opening ring innerRows messageRows messageDigits blocks innerDigits)) : ℝ≥0∞ :=
  Pr[= true | do
    let A ← $ᵗ Simple.PublicParams ring innerRows (messageRows * messageDigits)
    let B ← $ᵗ Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits))
    let (_c, m₁, opening₁, m₂, opening₂) ← adv { innerMatrix := A, outerMatrix := B }
    match outputToModuleSIS m₁ m₂ opening₁ opening₂ with
    | Sum.inl z => pure (ModuleSIS.relation ring (fun _ => true) A z)
    | Sum.inr _ => pure false]

/-- Outer contextual Module-SIS advantage extracted from a binding adversary. -/
noncomputable def outerModuleSISAdvantage
    (adv : BindingAdv
      (PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
      (Message ring messageRows blocks)
      (Commitment ring outerRows)
      (Opening ring innerRows messageRows messageDigits blocks innerDigits)) : ℝ≥0∞ :=
  Pr[= true | do
    let A ← $ᵗ Simple.PublicParams ring innerRows (messageRows * messageDigits)
    let B ← $ᵗ Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits))
    let (_c, m₁, opening₁, m₂, opening₂) ← adv { innerMatrix := A, outerMatrix := B }
    match outputToModuleSIS m₁ m₂ opening₁ opening₂ with
    | Sum.inl _ => pure false
    | Sum.inr z => pure (ModuleSIS.relation ring (fun _ => true) B z)]

/-- Binding is bounded by the sum of the extracted inner and outer Module-SIS advantages. -/
theorem bindingAdvantage_le_moduleSIS (base : Coeff)
    (decomp : Decomposition ring messageRows messageDigits innerRows innerDigits)
    (adv : BindingAdv
      (PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits)
      (Message ring messageRows blocks)
      (Commitment ring outerRows)
      (Opening ring innerRows messageRows messageDigits blocks innerDigits)) :
    bindingAdvantage
        (commitmentScheme (outerRows := outerRows) (blocks := blocks) base decomp) adv ≤
      innerModuleSISAdvantage adv + outerModuleSISAdvantage adv := by
  unfold bindingAdvantage CommitmentScheme.bindingExp
    innerModuleSISAdvantage outerModuleSISAdvantage commitmentScheme
  simp only [monad_norm]
  refine probOutput_bind_congr_le_add fun A _ => ?_
  refine probOutput_bind_congr_le_add fun B _ => ?_
  refine probOutput_bind_congr_le_add fun ⟨c, m₁, opening₁, m₂, opening₂⟩ _ => ?_
  by_cases hwin :
      (decide (m₁ ≠ m₂) &&
        verify base { innerMatrix := A, outerMatrix := B } m₁ c opening₁ &&
        verify base { innerMatrix := A, outerMatrix := B } m₂ c opening₂) = true
  · have hvalid := outputToModuleSIS_valid (ring := ring) (base := base)
      { innerMatrix := A, outerMatrix := B } c m₁ m₂ opening₁ opening₂ hwin
    have hleftTrue :
        (m₁ ≠ m₂ ∧
            verify base { innerMatrix := A, outerMatrix := B } m₁ c opening₁ = true) ∧
          verify base { innerMatrix := A, outerMatrix := B } m₂ c opening₂ = true := by
      simpa [Bool.and_eq_true, decide_eq_true_eq] using hwin
    cases hsol : outputToModuleSIS m₁ m₂ opening₁ opening₂ with
    | inl z =>
        simp [hsol] at hvalid
        simp [hleftTrue, hvalid]
    | inr z =>
        simp [hsol] at hvalid
        simp [hleftTrue, hvalid]
  · have hleftFalse :
        ¬((m₁ ≠ m₂ ∧
              verify base { innerMatrix := A, outerMatrix := B } m₁ c opening₁ = true) ∧
            verify base { innerMatrix := A, outerMatrix := B } m₂ c opening₂ = true) := by
      intro hleft
      apply hwin
      simpa [Bool.and_eq_true, decide_eq_true_eq] using hleft
    simp [hleftFalse]

end Advantages

end Scheme

end Binding

/-! ## Hachi/Greyhound Weak Binding -/

namespace WeakBinding

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
  Binding.differs opening₁.message opening₂.message

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
  Binding.outputFromFirstDiff (ring := ring) (innerCols := messageRows * messageDigits)
    (outerCols := blocks * (innerRows * innerDigits)) (blocks := blocks)
    opening₁.message opening₂.message flat₁ flat₂ fun i =>
    { left := scaledMessage opening₁ opening₂ i
      right := scaledMessage opening₂ opening₁ i }

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
    Binding.block_eq_of_flattenBlocks_eq hflat i
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
        decide (PolyVec.l2NormSq normOps z.left ≤
            normLaws.scalarVecMulMulL2NormSqBound kappa betaSq) &&
          decide (PolyVec.l2NormSq normOps z.right ≤
            normLaws.scalarVecMulMulL2NormSqBound kappa betaSq))
      pp.innerMatrix
      { left := scaledMessage opening₁ opening₂ i
        right := scaledMessage opening₂ opening₁ i } = true := by
  have hBlock₁ := hv₁.block i
  have hBlock₂ := hv₂.block i
  have hne : scaledMessage opening₁ opening₂ i ≠ scaledMessage opening₂ opening₁ i :=
    scaledMessage_ne_of_message_ne scalarLaws hBlock₁ hBlock₂ hmsgNe
  have hshort :
      (fun z : ModuleSIS.Solution ring (messageRows * messageDigits) =>
        decide (PolyVec.l2NormSq normOps z.left ≤
            normLaws.scalarVecMulMulL2NormSqBound kappa betaSq) &&
          decide (PolyVec.l2NormSq normOps z.right ≤
            normLaws.scalarVecMulMulL2NormSqBound kappa betaSq))
        { left := scaledMessage opening₁ opening₂ i
          right := scaledMessage opening₂ opening₁ i } = true := by
    simp [scaledMessage_l2NormSq_le normLaws hBlock₁ hBlock₂,
      scaledMessage_l2NormSq_le normLaws hBlock₂ hBlock₁]
  have hinnerEq := inner_commit_eq_of_flatten_eq hv₁ hv₂ hflat i
  have heq :
      ring.matVecMul pp.innerMatrix (scaledMessage opening₁ opening₂ i) =
        ring.matVecMul pp.innerMatrix (scaledMessage opening₂ opening₁ i) := by
    simpa [Simple.commit, scaledMessage] using
      NegacyclicRing.ScalarMulLaws.matVecMul_scalarVecMul_mul_eq_of_eq
        scalarLaws pp.innerMatrix (opening₁.challenge.get i) (opening₂.challenge.get i)
        (by simpa [Simple.commit] using hinnerEq)
  exact moduleSIS_relation_eq_true _ pp.innerMatrix _ hne hshort heq

omit [DecidableEq (PolyVec ring.Poly (messageRows * messageDigits))]
  [DecidableEq (PolyVec ring.Poly innerRows)] in
/-- Verified weak openings with different flattened witnesses give a valid outer relation. -/
theorem outer_relation_of_verified
    {base : Coeff} {normOps : NormOps ring.backend}
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
        decide (PolyVec.l2NormSq normOps z.left ≤ gammaSq) &&
          decide (PolyVec.l2NormSq normOps z.right ≤ gammaSq))
      pp.outerMatrix
      { left := PolyVec.flattenBlocks opening₁.innerDecomp
        right := PolyVec.flattenBlocks opening₂.innerDecomp } = true := by
  have hshort :
      (fun z : ModuleSIS.Solution ring (blocks * (innerRows * innerDigits)) =>
        decide (PolyVec.l2NormSq normOps z.left ≤ gammaSq) &&
          decide (PolyVec.l2NormSq normOps z.right ≤ gammaSq))
        { left := PolyVec.flattenBlocks opening₁.innerDecomp
          right := PolyVec.flattenBlocks opening₂.innerDecomp } = true := by
    simp [hv₁.outer_short, hv₂.outer_short]
  have heq :
      ring.matVecMul pp.outerMatrix (PolyVec.flattenBlocks opening₁.innerDecomp) =
        ring.matVecMul pp.outerMatrix (PolyVec.flattenBlocks opening₂.innerDecomp) := by
    simpa [Simple.commit] using hv₁.outer_eq.trans hv₂.outer_eq.symm
  exact moduleSIS_relation_eq_true _ pp.outerMatrix _ hflat hshort heq

/-- A successful pair of weak openings yields either an inner or outer Module-SIS collision. -/
theorem outputToModuleSIS_valid
    (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
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
            decide (PolyVec.l2NormSq normOps z.left ≤
                normLaws.scalarVecMulMulL2NormSqBound kappa betaSq) &&
              decide (PolyVec.l2NormSq normOps z.right ≤
                normLaws.scalarVecMulMulL2NormSqBound kappa betaSq))
          pp.innerMatrix z = true
    | Sum.inr z =>
        ModuleSIS.relation ring
          (fun z =>
            decide (PolyVec.l2NormSq normOps z.left ≤ gammaSq) &&
              decide (PolyVec.l2NormSq normOps z.right ≤ gammaSq))
          pp.outerMatrix z = true := by
  simp only [Bool.and_eq_true] at hwin
  rcases hwin with ⟨⟨hdiff, hverify₁⟩, hverify₂⟩
  have hv₁ := verifiedOpening_of_verify_eq_true hverify₁
  have hv₂ := verifiedOpening_of_verify_eq_true hverify₂
  let flat₁ := PolyVec.flattenBlocks opening₁.innerDecomp
  let flat₂ := PolyVec.flattenBlocks opening₂.innerDecomp
  by_cases hflat : flat₁ = flat₂
  · obtain ⟨i, hfind⟩ := Binding.firstDiff?_some_of_differs hdiff
    have hmsgNe : opening₁.message.get i ≠ opening₂.message.get i :=
      Binding.firstDiff?_eq_some_ne hfind
    have hrel := inner_relation_of_verified scalarLaws normLaws hv₁ hv₂
      (by simpa [flat₁, flat₂] using hflat) hmsgNe
    simpa [outputToModuleSIS, Binding.outputFromFirstDiff, flat₁, flat₂, hflat, hfind]
      using hrel
  · have hrel := outer_relation_of_verified hv₁ hv₂ (by simpa [flat₁, flat₂] using hflat)
    simpa [outputToModuleSIS, Binding.outputFromFirstDiff, flat₁, flat₂, hflat] using hrel

section Advantages

variable [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
variable [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))]

-- TODO there must be a better way to formulate the MSIS advantages using the standard MSIS adv def.
-- TODO remove the two MSIS advantage defs below.

/-- Inner contextual Module-SIS advantage extracted from a weak-binding adversary. -/
noncomputable def innerModuleSISAdvantage
    (_base : Coeff) (normOps : NormOps ring.backend) (innerSq : Nat)
    (adv : Adversary (ring := ring) (innerRows := innerRows) (messageRows := messageRows)
      (messageDigits := messageDigits) (outerRows := outerRows) (blocks := blocks)
      (innerDigits := innerDigits)) :
    ℝ≥0∞ :=
  Pr[= true | do
    let A ← $ᵗ Simple.PublicParams ring innerRows (messageRows * messageDigits)
    let B ← $ᵗ Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits))
    let pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits :=
      { innerMatrix := A, outerMatrix := B }
    let (_u, opening₁, opening₂) ← adv pp
    match outputToModuleSIS opening₁ opening₂ with
    | Sum.inl z =>
        pure (ModuleSIS.relation ring
          (fun z =>
            decide (PolyVec.l2NormSq normOps z.left ≤ innerSq) &&
              decide (PolyVec.l2NormSq normOps z.right ≤ innerSq))
          A z)
    | Sum.inr _ => pure false]

/-- Outer contextual Module-SIS advantage extracted from a weak-binding adversary. -/
noncomputable def outerModuleSISAdvantage
    (_base : Coeff) (normOps : NormOps ring.backend) (gammaSq : Nat)
    (adv : Adversary (ring := ring) (innerRows := innerRows) (messageRows := messageRows)
      (messageDigits := messageDigits) (outerRows := outerRows) (blocks := blocks)
      (innerDigits := innerDigits)) :
    ℝ≥0∞ :=
  Pr[= true | do
    let A ← $ᵗ Simple.PublicParams ring innerRows (messageRows * messageDigits)
    let B ← $ᵗ Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits))
    let pp : PublicParams ring innerRows messageRows messageDigits outerRows blocks innerDigits :=
      { innerMatrix := A, outerMatrix := B }
    let (_u, opening₁, opening₂) ← adv pp
    match outputToModuleSIS opening₁ opening₂ with
    | Sum.inl _ => pure false
    | Sum.inr z =>
        pure (ModuleSIS.relation ring
          (fun z =>
            decide (PolyVec.l2NormSq normOps z.left ≤ gammaSq) &&
              decide (PolyVec.l2NormSq normOps z.right ≤ gammaSq))
          B z)]

omit [SampleableType (Simple.PublicParams ring innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams ring outerRows (blocks * (innerRows * innerDigits)))] in
/-- Pointwise form of the weak-binding to Module-SIS advantage bound. -/
theorem sample_advantage_le_moduleSIS (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
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
          ((match outputToModuleSIS opening₁ opening₂ with
            | Sum.inl z =>
                pure (ModuleSIS.relation ring
                  (fun z =>
                    decide (PolyVec.l2NormSq normOps z.left ≤
                        normLaws.scalarVecMulMulL2NormSqBound kappa betaSq) &&
                      decide (PolyVec.l2NormSq normOps z.right ≤
                        normLaws.scalarVecMulMulL2NormSqBound kappa betaSq))
                  A z)
            | Sum.inr _ => pure false) : ProbComp Bool)
          true +
        probOutput
          ((match outputToModuleSIS opening₁ opening₂ with
            | Sum.inl _ => pure false
            | Sum.inr z =>
                pure (ModuleSIS.relation ring
                  (fun z =>
                    decide (PolyVec.l2NormSq normOps z.left ≤ gammaSq) &&
                      decide (PolyVec.l2NormSq normOps z.right ≤ gammaSq))
                  B z)) : ProbComp Bool)
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
              decide (PolyVec.l2NormSq normOps z.left ≤
                  normLaws.scalarVecMulMulL2NormSqBound kappa betaSq) &&
                decide (PolyVec.l2NormSq normOps z.right ≤
                  normLaws.scalarVecMulMulL2NormSqBound kappa betaSq))
            A z)
          false
          (by
            intro hwin
            left
            have hvalid := outputToModuleSIS_valid (base := base)
              (normOps := normOps) (scalarLaws := scalarLaws) (normLaws := normLaws)
              (betaSq := betaSq) (gammaSq := gammaSq) (kappa := kappa)
              pp u opening₁ opening₂ hwin
            have hvalidInner :
                ModuleSIS.relation ring
                  (fun z =>
                    decide (PolyVec.l2NormSq normOps z.left ≤
                        normLaws.scalarVecMulMulL2NormSqBound kappa betaSq) &&
                      decide (PolyVec.l2NormSq normOps z.right ≤
                        normLaws.scalarVecMulMulL2NormSqBound kappa betaSq))
                  pp.innerMatrix z = true := by
              simpa [hsol] using hvalid
            simpa [pp] using hvalidInner)
  | inr z =>
      simpa [hsol, pp] using
        probOutput_pure_bool_le_or
          (openingsDiffer opening₁ opening₂ &&
            verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening₁ &&
            verify_weak base normOps scalarLaws betaSq gammaSq kappa pp u opening₂)
          false
          (ModuleSIS.relation ring
            (fun z =>
              decide (PolyVec.l2NormSq normOps z.left ≤ gammaSq) &&
                decide (PolyVec.l2NormSq normOps z.right ≤ gammaSq))
            B z)
          (by
            intro hwin
            right
            have hvalid := outputToModuleSIS_valid (base := base)
              (normOps := normOps) (scalarLaws := scalarLaws) (normLaws := normLaws)
              (betaSq := betaSq) (gammaSq := gammaSq) (kappa := kappa)
              pp u opening₁ opening₂ hwin
            have hvalidOuter :
                ModuleSIS.relation ring
                  (fun z =>
                    decide (PolyVec.l2NormSq normOps z.left ≤ gammaSq) &&
                      decide (PolyVec.l2NormSq normOps z.right ≤ gammaSq))
                  pp.outerMatrix z = true := by
              simpa [hsol] using hvalid
            simpa [pp] using hvalidOuter)

/-- Hachi/Greyhound weak binding is bounded by the extracted Module-SIS advantages. -/
theorem advantage_le_moduleSIS (base : Coeff)
    (normOps : NormOps ring.backend) (scalarLaws : NegacyclicRing.ScalarMulLaws ring)
    (normLaws : NegacyclicRing.ScalarNormLaws ring normOps)
    (betaSq gammaSq kappa : Nat)
    (adv : Adversary (ring := ring) (innerRows := innerRows) (messageRows := messageRows)
      (messageDigits := messageDigits) (outerRows := outerRows) (blocks := blocks)
      (innerDigits := innerDigits))
    :
    advantage base normOps scalarLaws betaSq gammaSq kappa adv ≤
      innerModuleSISAdvantage base normOps
          (normLaws.scalarVecMulMulL2NormSqBound kappa betaSq) adv +
        outerModuleSISAdvantage base normOps gammaSq adv := by
  unfold advantage experiment innerModuleSISAdvantage outerModuleSISAdvantage
  simp only [monad_norm]
  refine probOutput_bind_congr_le_add fun A _ => ?_
  refine probOutput_bind_congr_le_add fun B _ => ?_
  refine probOutput_bind_congr_le_add fun ⟨u, opening₁, opening₂⟩ _ => ?_
  simpa using sample_advantage_le_moduleSIS base normOps scalarLaws normLaws betaSq gammaSq kappa
    A B u opening₁ opening₂

end Advantages

end Scheme

end WeakBinding

end InnerOuter
end Ajtai
end LatticeCrypto
