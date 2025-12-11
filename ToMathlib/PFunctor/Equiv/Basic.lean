/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.PFunctor.Basic

/-!
# Equivalences of Polynomial Functors

This file defines equivalences between polynomial functors and proves basic properties about them.

An equivalence between two polynomial functors `P` and `Q`, written `P ≃ₚ Q`, is given by an
equivalence of the `A` types and an equivalence between the `B` types for each `a : A`.

We provide various canonical equivalences for operations on polynomial functors, such as:
- Sum operations: `P + 0 ≃ₚ P`, `0 + P ≃ₚ P`
- Product operations and their properties
- Equivalences for sigma and pi constructions
- Universe lifting equivalences
- Tensor product equivalences
- Composition equivalences

## Main definitions

- `PFunctor.Equiv`: An equivalence between two polynomial functors
- `≃ₚ`: Notation for polynomial functor equivalences

## Main results

- Basic equivalence properties: reflexivity, symmetry, transitivity
- Canonical equivalences for sum, product, and other constructions on polynomial functors
-/

universe u v uA uB uA' uB' uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

section find_home

instance instIsEmptySigma {α : Sort u} {β : α → Sort v} [inst : IsEmpty α] :
    IsEmpty ((a : α) ×' β a) where
  false := fun a => inst.elim a.1

end find_home

namespace PFunctor

namespace Equiv

section Sum

variable (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB})
  (R : PFunctor.{uA₃, uB}) (S : PFunctor.{uA₄, uB})

/-- Addition with the zero functor on the left is equivalent to the original functor -/
@[simps]
def sumZero : P + 0 ≃ₚ P where
  equivA := Equiv.sumEmpty P.A PEmpty
  equivB := (Sum.casesOn · (fun _ => _root_.Equiv.refl _) (fun a => a.elim))

/-- Addition with the zero functor on the right is equivalent to the original functor -/
@[simps]
def zeroSum : 0 + P ≃ₚ P where
  equivA := Equiv.emptySum PEmpty P.A
  equivB := (Sum.casesOn · (fun a => a.elim) (fun _ => _root_.Equiv.refl _))

/-- Sum of polynomial functors is commutative up to equivalence -/
@[simps]
def sumComm : (P + Q : PFunctor.{max uA₁ uA₂, uB}) ≃ₚ (Q + P : PFunctor.{max uA₁ uA₂, uB}) where
  equivA := _root_.Equiv.sumComm P.A Q.A
  equivB := (Sum.casesOn · (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _))

/-- Sum of polynomial functors is associative up to equivalence -/
@[simps]
def sumAssoc :
    ((P + Q) + R : PFunctor.{max uA₁ uA₂ uA₃, uB}) ≃ₚ
    (P + (Q + R) : PFunctor.{max uA₁ uA₂ uA₃, uB}) where
  equivA := _root_.Equiv.sumAssoc P.A Q.A R.A
  equivB := (Sum.casesOn ·
    (Sum.casesOn · (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _))
    (fun _ => _root_.Equiv.refl _))

/-- If `P ≃ₚ R` and `Q ≃ₚ S`, then `P + Q ≃ₚ R + S` -/
@[simps]
def sumCongr {P Q} {R : PFunctor.{uA₃, uB₁}} {S : PFunctor.{uA₄, uB₁}} (e₁ : P ≃ₚ R) (e₂ : Q ≃ₚ S) :
    P + Q ≃ₚ (R + S : PFunctor.{max uA₃ uA₄, uB₁}) where
  equivA := _root_.Equiv.sumCongr e₁.equivA e₂.equivA
  equivB := (Sum.casesOn · (e₁.equivB ·) (e₂.equivB ·))

/-- Rearrangement of nested sums: `(P + Q) + (R + S) ≃ₚ (P + R) + (Q + S)` -/
def sumSumSumComm :
    ((P + Q) + (R + S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, uB}) ≃ₚ
    ((P + R) + (Q + S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, uB}) where
  equivA := _root_.Equiv.sumSumSumComm P.A Q.A R.A S.A
  equivB := (Sum.casesOn ·
    (Sum.casesOn · (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _))
    (Sum.casesOn · (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _)))

end Sum

section Prod

variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})
  (S : PFunctor.{uA₄, uB₄})

/-- Product with `0` on the right is `0` -/
def prodZero : P * 0 ≃ₚ 0 where
  equivA := Equiv.prodPEmpty P.A
  equivB := fun a => a.2.elim

/-- Product with `0` on the left is `0` -/
def zeroProd : 0 * P ≃ₚ 0 where
  equivA := Equiv.pemptyProd P.A
  equivB := fun a => a.1.elim

/-- Product with the unit functor on the right is equivalent to the original functor -/
@[simps]
def prodOne : P * 1 ≃ₚ P where
  equivA := _root_.Equiv.prodPUnit P.A
  equivB := fun a => _root_.Equiv.sumEmpty (P.B a.1) PEmpty

/-- Product with the unit functor on the left is equivalent to the original functor -/
@[simps]
def oneProd : 1 * P ≃ₚ P where
  equivA := _root_.Equiv.punitProd P.A
  equivB := fun a => _root_.Equiv.emptySum PEmpty (P.B a.2)

/-- Product of polynomial functors is commutative up to equivalence -/
@[simps]
def prodComm :
    (P * Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ≃ₚ
    (Q * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) where
  equivA := _root_.Equiv.prodComm P.A Q.A
  equivB := fun a => _root_.Equiv.sumComm (P.B a.1) (Q.B a.2)

/-- Product of polynomial functors is associative up to equivalence -/
@[simps]
def prodAssoc :
    ((P * Q) * R : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) ≃ₚ
    (P * (Q * R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) where
  equivA := _root_.Equiv.prodAssoc P.A Q.A R.A
  equivB := fun a => _root_.Equiv.sumAssoc (P.B a.1.1) (Q.B a.1.2) (R.B a.2)

/-- Equivalence is preserved under product: if `P ≃ₚ R` and `Q ≃ₚ S`, then `P * Q ≃ₚ R * S` -/
@[simps]
def prodCongr {P Q} {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (e₁ : P ≃ₚ R) (e₂ : Q ≃ₚ S) : P * Q ≃ₚ (R * S : PFunctor.{max uA₃ uA₄, max uB₃ uB₄}) where
  equivA := _root_.Equiv.prodCongr e₁.equivA e₂.equivA
  equivB := fun a => _root_.Equiv.sumCongr (e₁.equivB a.1) (e₂.equivB a.2)

/-- Rearrangement of nested products: `(P * Q) * (R * S) ≃ₚ (P * R) * (Q * S)` -/
@[simps]
def prodProdProdComm :
    ((P * Q) * (R * S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) ≃ₚ
    ((P * R) * (Q * S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) where
  equivA := _root_.Equiv.prodProdProdComm P.A Q.A R.A S.A
  equivB := fun a => _root_.Equiv.sumSumSumComm (P.B a.1.1) (Q.B a.1.2) (R.B a.2.1) (S.B a.2.2)

/-- Sum distributes over product: `(P + Q) * R ≃ₚ (P * R) + (Q * R)` -/
def sumProdDistrib (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₁}) (R : PFunctor.{uA₃, uB₂}) :
    ((P + Q) * R : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) ≃ₚ
    ((P * R) + (Q * R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
  equivA := _root_.Equiv.sumProdDistrib P.A Q.A R.A
  equivB := fun ⟨a, _⟩ =>
    Sum.casesOn a (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _)

/-- Product distributes over sum: `P * (Q + R) ≃ₚ (P * Q) + (P * R)`

TODO: define in terms of `sumProdDistrib` -/
@[simps]
def prodSumDistrib (R : PFunctor.{uA₃, uB₂}):
    (P * (Q + R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) ≃ₚ
    ((P * Q) + (P * R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
  equivA := _root_.Equiv.prodSumDistrib P.A Q.A R.A
  equivB := fun ⟨_, a⟩ =>
    Sum.casesOn a (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _)

end Prod

section Sigma

variable (P : PFunctor.{uA₁, uB₁}) {I : Type v} (F : I → PFunctor.{uA₂, uB₂})

instance [inst : IsEmpty I] : IsEmpty (sigma F).A where
  false := fun a => inst.elim a.1

/-- Sigma of an empty family is the zero functor. -/
def emptySigma [inst : IsEmpty I] : sigma F ≃ₚ 0 where
  equivA := Equiv.equivPEmpty _
  equivB := fun a => inst.elim a.1

def uniqueSigma [Unique I] : sigma F ≃ₚ F default where
  equivA := _root_.Equiv.uniqueSigma _
  equivB := fun a => by simp [sigma] at a ⊢; sorry

/-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself. -/
def punitSigma {F : PUnit → PFunctor.{uA, uB}} : sigma F ≃ₚ F PUnit.unit where
  equivA := _root_.Equiv.uniqueSigma _
  equivB := sorry

#check Equiv.sigmaSumDistrib

#check Equiv.sumSigmaDistrib

#check Equiv.prodSumDistrib

/-- Left distributivity of sum over sigma. -/
def sumSigmaDistrib (F : I → PFunctor.{uA₂, uB₁}) :
    (P + sigma F : PFunctor.{max uA₁ uA₂ v, uB₁}) ≃ₚ
    sigma (fun i => (P + F i : PFunctor.{max uA₁ uA₂, uB₁})) where
  equivA := by simp [sigma, HAdd.hAdd, sum]; sorry
  equivB := fun a => sorry

/-- Right distributivity of sum over sigma. -/
def sigmaSumDistrib (F : I → PFunctor.{uA₂, uB₁}) :
    (sigma F + P : PFunctor.{max uA₁ uA₂ v, uB₁}) ≃ₚ
    sigma (fun i => (F i + P : PFunctor.{max uA₁ uA₂, uB₁})) where
  equivA := by simp [sigma, HAdd.hAdd, sum]; sorry
  -- exact (_root_.Equiv.sumSigmaDistrib _).symm
  equivB := fun a => sorry

/-- Left distributivity of product over sigma. -/
def prodSigmaDistrib : (P * sigma F : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) ≃ₚ
    sigma (fun i => (P * F i : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) where
  equivA := sorry
  equivB := sorry

/-- Right distributivity of product over sigma. -/
def sigmaProdDistrib : (sigma F * P : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) ≃ₚ
    sigma (fun i => (F i * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) where
  equivA := sorry
  equivB := sorry

/-- Left distributivity of tensor product over sigma. -/
def tensorSigmaDistrib :
    P ⊗ sigma F ≃ₚ sigma (fun i => P ⊗ F i) where
  equivA := sorry
  equivB := sorry

/-- Right distributivity of tensor product over sigma. -/
def sigmaTensorDistrib {I : Type v} (F : I → PFunctor.{uA₁, uB₁}) (P : PFunctor.{uA₂, uB₂}) :
    sigma F ⊗ P ≃ₚ sigma (fun i => F i ⊗ P) where
  equivA := sorry
  equivB := sorry

/-- Right distributivity of composition over sigma. -/
def sigmaCompDistrib {I : Type v} (F : I → PFunctor.{uA₁, uB₁}) (P : PFunctor.{uA₂, uB₂}) :
    sigma F ◃ P ≃ₚ sigma (fun i => F i ◃ P) where
  equivA := sorry
  equivB := sorry

end Sigma

section Pi

/-- Pi over a `PUnit`-indexed family is equivalent to the functor itself. -/
def piPUnit (P : PFunctor.{uA, uB}) :
    pi (fun (_ : PUnit) => P) ≃ₚ P where
  equivA := sorry
  equivB := sorry

end Pi

section ULift

variable (P : PFunctor.{uA₁, uB₁})

/-- Equivalence between a polynomial functor and its universe-lifted version -/
def uliftEquiv : P ≃ₚ (P.ulift : PFunctor.{max uA₁ u, max uB₁ v}) :=
  sorry

/-- Universe lifting is idempotent up to equivalence -/
def uliftUliftEquiv : P.ulift.ulift ≃ₚ P.ulift :=
  sorry

-- TODO: find better ways to annotate universe levels

/-- Universe lifting commutes with sum -/
def uliftSumEquiv (Q : PFunctor.{uA₂, uB₁}) :
    (PFunctor.ulift.{_, _, u, v} (P + Q : PFunctor.{max uA₁ uA₂, uB₁})) ≃ₚ
    ((PFunctor.ulift.{_, _, uA, uB} P : PFunctor.{max uA₁ uA, max uB₁ uB}) +
      (Q.ulift : PFunctor.{max uA₂ uA', max uB₁ uB}) : PFunctor.{max uA₁ uA uA₂ uA', max uB₁ uB}) :=
  sorry

-- /-- Universe lifting commutes with product -/
-- def uliftProdEquiv (Q : PFunctor.{uA₂, uB₂}) :
--     Equiv.{max uA₁ uA₂ u, max uB₁ v, max uA₁ uA uA₂ uA', max uB₁ uB}
--     (PFunctor.ulift.{_, _, u, v} (sum.{uB₁, uA₁, uA₂} P Q))
--     (sum.{max uB₁ uB, max uA₁ uA, max uA₂ uA'} (P.ulift : PFunctor.{max uA₁ uA, max uB₁ uB})
--       (Q.ulift : PFunctor.{max uA₂ uA', max uB₁ uB}) : PFunctor.{max uA₁ uA uA₂ uA', max uB₁ uB})
--     (P * Q).ulift ≃ₚ (P.ulift * Q.ulift) :=
--   sorry

-- same for tensor product & composition

end ULift

section Tensor

variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})
  (S : PFunctor.{uA₄, uB₄})

/-- Tensor product with `0` on the right is `0` -/
def tensorZero : P ⊗ 0 ≃ₚ 0 where
  equivA := Equiv.prodPEmpty P.A
  equivB := fun a => Equiv.prodPEmpty (P.B a.1)

/-- Tensor product with `0` on the left is `0` -/
def zeroTensor : 0 ⊗ P ≃ₚ 0 where
  equivA := Equiv.pemptyProd P.A
  equivB := fun a => Equiv.pemptyProd (P.B a.2)

instance {P} {a : (P ⊗ 1).A} : IsEmpty ((P ⊗ 1).B a) := by
  simp [tensor, OfNat.ofNat, One.one]
  exact Or.inr (PEmpty.instIsEmpty)

/-- Tensor product with `1` on the right is equivalent to the constant functor -/
def tensorOne : P ⊗ 1 ≃ₚ C P.A where
  equivA := Equiv.prodPUnit P.A
  equivB := fun _ => Equiv.equivPEmpty _

instance {P} {a : (1 ⊗ P).A} : IsEmpty ((1 ⊗ P).B a) := by
  simp [tensor, OfNat.ofNat, One.one]
  exact Or.inl (PEmpty.instIsEmpty)

/-- Tensor product with `1` on the left is equivalent to the constant functor -/
def oneTensor : 1 ⊗ P ≃ₚ C P.A where
  equivA := Equiv.punitProd P.A
  equivB := fun _ => Equiv.equivPEmpty _

/-- Tensor product with the functor Y on the right -/
@[simps]
def tensorX : P ⊗ X ≃ₚ P where
  equivA := _root_.Equiv.prodPUnit P.A
  equivB := fun a => _root_.Equiv.prodPUnit (P.B a.1)

/-- Tensor product with the functor Y on the left -/
@[simps]
def xTensor : X ⊗ P ≃ₚ P where
  equivA := _root_.Equiv.punitProd P.A
  equivB := fun a => _root_.Equiv.punitProd (P.B a.2)

/-- Tensor product of polynomial functors is commutative up to equivalence -/
@[simps]
def tensorComm :
    (P ⊗ Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ≃ₚ
    (Q ⊗ P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) where
  equivA := _root_.Equiv.prodComm P.A Q.A
  equivB := fun a => _root_.Equiv.prodComm (P.B a.1) (Q.B a.2)

/-- Tensor product of polynomial functors is associative up to equivalence -/
@[simps]
def tensorAssoc :
    ((P ⊗ Q) ⊗ R : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) ≃ₚ
    (P ⊗ (Q ⊗ R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) where
  equivA := _root_.Equiv.prodAssoc P.A Q.A R.A
  equivB := fun a => _root_.Equiv.prodAssoc (P.B a.1.1) (Q.B a.1.2) (R.B a.2)

/-- Tensor product preserves equivalences: if `P ≃ₚ R` and `Q ≃ₚ S`, then `P ⊗ Q ≃ₚ R ⊗ S` -/
@[simps]
def tensorCongr {P : PFunctor.{uA₁, uB₁}} {Q} {R : PFunctor.{uA₃, uB₃}} {S}
    (e₁ : P ≃ₚ R) (e₂ : Q ≃ₚ S) :
      (P ⊗ Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ≃ₚ
      (R ⊗ S : PFunctor.{max uA₃ uA₄, max uB₃ uB₄}) where
  equivA := _root_.Equiv.prodCongr e₁.equivA e₂.equivA
  equivB := fun a => _root_.Equiv.prodCongr (e₁.equivB a.1) (e₂.equivB a.2)

/-- Rearrangement of nested tensor products: `(P ⊗ Q) ⊗ (R ⊗ S) ≃ₚ (P ⊗ R) ⊗ (Q ⊗ S)` -/
def tensorTensorTensorComm :
    ((P ⊗ Q) ⊗ (R ⊗ S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) ≃ₚ
    ((P ⊗ R) ⊗ (Q ⊗ S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) where
  equivA := _root_.Equiv.prodProdProdComm P.A Q.A R.A S.A
  equivB := fun a => _root_.Equiv.prodProdProdComm (P.B a.1.1) (Q.B a.1.2) (R.B a.2.1) (S.B a.2.2)

/-- Sum distributes over tensor product: `(P + Q) ⊗ R ≃ₚ (P ⊗ R) + (Q ⊗ R)` -/
def sumTensorDistrib (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₁}) (R : PFunctor.{uA₃, uB₂}) :
    ((P + Q : PFunctor.{max uA₁ uA₂, uB₁}) ⊗ R) ≃ₚ
    ((P ⊗ R) + (Q ⊗ R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
  equivA := _root_.Equiv.sumProdDistrib P.A Q.A R.A
  equivB := fun ⟨a, _⟩ =>
    Sum.casesOn a (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _)

/-- Tensor product distributes over sum: `P ⊗ (Q + R) ≃ₚ (P ⊗ Q) + (P ⊗ R)` -/
def tensorSumDistrib (R : PFunctor.{uA₃, uB₂}):
    (P ⊗ (Q + R : PFunctor.{max uA₂ uA₃, uB₂})) ≃ₚ
    ((P ⊗ Q) + (P ⊗ R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
  equivA := _root_.Equiv.prodSumDistrib P.A Q.A R.A
  equivB := fun ⟨_, a⟩ =>
    Sum.casesOn a (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _)

end Tensor

section Comp

variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})

instance : IsEmpty (0 ◃ P).A where
  false := fun a => a.1.elim

def zeroComp : 0 ◃ P ≃ₚ 0 where
  equivA := Equiv.equivPEmpty _
  equivB := fun a => a.1.elim

instance {a : (1 ◃ P).A} : IsEmpty ((1 ◃ P).B a) where
  false := fun a => a.1.elim

def oneComp : (1 : PFunctor.{uA, uB}) ◃ P ≃ₚ 1 where
  equivA := (@_root_.Equiv.uniqueSigma _ (fun i => B 1 i → P.A)
    (instUniqueAOfNat_toMathlib.{uA, uB})).trans (Equiv.pemptyArrowEquivPUnit _)
  equivB := fun _ => Equiv.equivPEmpty _

#check Equiv.sigmaAssocProd

/-- Associativity of composition -/
def compAssoc : (P ◃ Q) ◃ R ≃ₚ P ◃ (Q ◃ R) where
  equivA := {
    toFun := fun ⟨⟨pa, qf⟩, rf⟩ => ⟨pa, fun pb => ⟨qf pb, fun qb => rf ⟨pb, qb⟩⟩⟩
    invFun := fun ⟨pa, g⟩ => ⟨⟨pa, fun pb => (g pb).1⟩, fun ⟨pb, qb⟩ => (g pb).2 qb⟩
    left_inv := by
      rintro ⟨⟨pa, qf⟩, rf⟩
      simp [comp]
    right_inv := by
      rintro ⟨pa, g⟩; simp [comp]
  }
  equivB := fun ⟨⟨pa, qf⟩, rf⟩ => sorry
  -- Equiv.sigmaProdDistrib _ _

/-- Composition with `X` is identity (right) -/
def compX : P ◃ X ≃ₚ P where
  equivA := Equiv.sigmaUnique P.A (fun a => P.B a → PUnit.{_ + 1})
  equivB := fun _ => _root_.Equiv.sigmaPUnit _

/-- Composition with `X` is identity (left) -/
def XComp : X ◃ P ≃ₚ P where
  equivA := (_root_.Equiv.uniqueSigma _).trans (Equiv.punitArrowEquiv P.A)
  equivB := fun _ => by exact _root_.Equiv.uniqueSigma _

/-- Distributivity of composition over sum on the right -/
def sumCompDistrib (Q : PFunctor.{uA₂, uB₁}) :
    (P + Q : PFunctor.{max uA₁ uA₂, uB₁}) ◃ R ≃ₚ
    ((P ◃ R) + (Q ◃ R) : PFunctor.{max uA₁ uA₂ uA₃ uB₁, max uB₁ uB₃}) where
  equivA := sorry
  equivB := sorry

-- def prodCompDistrib (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃}) :
--     (P * Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ◃ R ≃ₚ
--     ((P ◃ R) * (Q ◃ R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) where
--   equivA := sorry
--   equivB := sorry

-- sigmaCompDistrib
-- piCompDistrib

-- sigma / pi / tensor and comp?

end Comp

end Equiv

end PFunctor
