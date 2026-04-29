/-
Copyright (c) 2025 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
module

public import ToMathlib.PFunctor.Basic

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

@[expose] public section

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
def prodSumDistrib (R : PFunctor.{uA₃, uB₂}) :
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
  equivB := fun ⟨i, a⟩ => by
    have hi := Unique.eq_default i
    subst hi
    exact _root_.Equiv.refl _

/-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself. -/
def punitSigma {F : PUnit → PFunctor.{uA, uB}} : sigma F ≃ₚ F PUnit.unit where
  equivA := _root_.Equiv.uniqueSigma _
  equivB := fun ⟨i, a⟩ => by cases i; exact _root_.Equiv.refl _

/-- Left distributivity of sum over sigma. -/
def sumSigmaDistrib (F : I → PFunctor.{uA₂, uB₁}) [Unique I] :
    (P + sigma F : PFunctor.{max uA₁ uA₂ v, uB₁}) ≃ₚ
    sigma (fun i => (P + F i : PFunctor.{max uA₁ uA₂, uB₁})) where
  equivA := {
    toFun := fun
      | Sum.inl pa => ⟨default, Sum.inl pa⟩
      | Sum.inr ⟨i, fa⟩ => ⟨i, Sum.inr fa⟩
    invFun := fun
      | ⟨_, Sum.inl pa⟩ => Sum.inl pa
      | ⟨i, Sum.inr fa⟩ => Sum.inr ⟨i, fa⟩
    left_inv := by
      intro a
      rcases a with pa | ⟨i, fa⟩
      · rfl
      · rfl
    right_inv := by
      intro a
      rcases a with ⟨i, pa | fa⟩
      · cases (Unique.eq_default i)
        rfl
      · rfl
  }
  equivB := fun a => by
    rcases a with pa | ⟨i, fa⟩
    · exact _root_.Equiv.refl _
    · exact _root_.Equiv.refl _

/-- Right distributivity of sum over sigma. -/
def sigmaSumDistrib (F : I → PFunctor.{uA₂, uB₁}) [Unique I] :
    (sigma F + P : PFunctor.{max uA₁ uA₂ v, uB₁}) ≃ₚ
    sigma (fun i => (F i + P : PFunctor.{max uA₁ uA₂, uB₁})) where
  equivA := {
    toFun := fun
      | Sum.inl ⟨i, fa⟩ => ⟨i, Sum.inl fa⟩
      | Sum.inr pa => ⟨default, Sum.inr pa⟩
    invFun := fun
      | ⟨i, Sum.inl fa⟩ => Sum.inl ⟨i, fa⟩
      | ⟨_, Sum.inr pa⟩ => Sum.inr pa
    left_inv := by
      intro a
      rcases a with ⟨i, fa⟩ | pa
      · rfl
      · rfl
    right_inv := by
      intro a
      rcases a with ⟨i, fa | pa⟩
      · rfl
      · cases (Unique.eq_default i)
        rfl
  }
  -- exact (_root_.Equiv.sumSigmaDistrib _).symm
  equivB := fun a => by
    rcases a with ⟨i, fa⟩ | pa
    · exact _root_.Equiv.refl _
    · exact _root_.Equiv.refl _

/-- Left distributivity of product over sigma. -/
def prodSigmaDistrib : (P * sigma F : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) ≃ₚ
    sigma (fun i => (P * F i : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) where
  equivA := {
    toFun := fun ⟨pa, ⟨i, fa⟩⟩ => ⟨i, ⟨pa, fa⟩⟩
    invFun := fun ⟨i, ⟨pa, fa⟩⟩ => ⟨pa, ⟨i, fa⟩⟩
    left_inv := by
      rintro ⟨pa, ⟨i, fa⟩⟩
      rfl
    right_inv := by
      rintro ⟨i, ⟨pa, fa⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨pa, ⟨i, fa⟩⟩
    exact _root_.Equiv.refl _

/-- Right distributivity of product over sigma. -/
def sigmaProdDistrib : (sigma F * P : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) ≃ₚ
    sigma (fun i => (F i * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) where
  equivA := {
    toFun := fun ⟨⟨i, fa⟩, pa⟩ => ⟨i, ⟨fa, pa⟩⟩
    invFun := fun ⟨i, ⟨fa, pa⟩⟩ => ⟨⟨i, fa⟩, pa⟩
    left_inv := by
      rintro ⟨⟨i, fa⟩, pa⟩
      rfl
    right_inv := by
      rintro ⟨i, ⟨fa, pa⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨⟨i, fa⟩, pa⟩
    exact _root_.Equiv.refl _

/-- Left distributivity of tensor product over sigma. -/
def tensorSigmaDistrib :
    P ⊗ sigma F ≃ₚ sigma (fun i => P ⊗ F i) where
  equivA := {
    toFun := fun ⟨pa, ⟨i, fa⟩⟩ => ⟨i, ⟨pa, fa⟩⟩
    invFun := fun ⟨i, ⟨pa, fa⟩⟩ => ⟨pa, ⟨i, fa⟩⟩
    left_inv := by
      rintro ⟨pa, ⟨i, fa⟩⟩
      rfl
    right_inv := by
      rintro ⟨i, ⟨pa, fa⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨pa, ⟨i, fa⟩⟩
    exact _root_.Equiv.refl _

/-- Right distributivity of tensor product over sigma. -/
def sigmaTensorDistrib {I : Type v} (F : I → PFunctor.{uA₁, uB₁}) (P : PFunctor.{uA₂, uB₂}) :
    sigma F ⊗ P ≃ₚ sigma (fun i => F i ⊗ P) where
  equivA := {
    toFun := fun ⟨⟨i, fa⟩, pa⟩ => ⟨i, ⟨fa, pa⟩⟩
    invFun := fun ⟨i, ⟨fa, pa⟩⟩ => ⟨⟨i, fa⟩, pa⟩
    left_inv := by
      rintro ⟨⟨i, fa⟩, pa⟩
      rfl
    right_inv := by
      rintro ⟨i, ⟨fa, pa⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨⟨i, fa⟩, pa⟩
    exact _root_.Equiv.refl _

/-- Right distributivity of composition over sigma. -/
def sigmaCompDistrib {I : Type v} (F : I → PFunctor.{uA₁, uB₁}) (P : PFunctor.{uA₂, uB₂}) :
    sigma F ◃ P ≃ₚ sigma (fun i => F i ◃ P) where
  equivA := {
    toFun := fun ⟨⟨i, fa⟩, pf⟩ => ⟨i, ⟨fa, pf⟩⟩
    invFun := fun ⟨i, ⟨fa, pf⟩⟩ => ⟨⟨i, fa⟩, pf⟩
    left_inv := by
      rintro ⟨⟨i, fa⟩, pf⟩
      rfl
    right_inv := by
      rintro ⟨i, ⟨fa, pf⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨⟨i, fa⟩, pf⟩
    exact _root_.Equiv.refl _

end Sigma

section Pi

/-- Pi over a `PUnit`-indexed family is equivalent to the functor itself. -/
def piPUnit (P : PFunctor.{uA, uB}) :
    pi (fun (_ : PUnit) => P) ≃ₚ P where
  equivA := _root_.Equiv.punitArrowEquiv P.A
  equivB := fun f => by
    simpa using (_root_.Equiv.uniqueSigma (fun i : PUnit => P.B (f i)))

end Pi

section ULift

variable (P : PFunctor.{uA₁, uB₁})

/-- Equivalence between a polynomial functor and its universe-lifted version -/
def uliftEquiv : P ≃ₚ (P.ulift : PFunctor.{max uA₁ u, max uB₁ v}) :=
  {
    equivA := {
      toFun := ULift.up
      invFun := ULift.down
      left_inv := by intro a; rfl
      right_inv := by intro a; cases a; rfl
    }
    equivB := fun _ => {
      toFun := ULift.up
      invFun := ULift.down
      left_inv := by intro b; rfl
      right_inv := by intro b; cases b; rfl
    }
  }

/-- Universe lifting is idempotent up to equivalence -/
def uliftUliftEquiv : P.ulift.ulift ≃ₚ P.ulift :=
  {
    equivA := {
      toFun := ULift.down
      invFun := ULift.up
      left_inv := by intro a; cases a; rfl
      right_inv := by intro a; rfl
    }
    equivB := fun _ => {
      toFun := ULift.down
      invFun := ULift.up
      left_inv := by intro b; cases b; rfl
      right_inv := by intro b; rfl
    }
  }

-- TODO: find better ways to annotate universe levels

/-- Universe lifting commutes with sum -/
def uliftSumEquiv (Q : PFunctor.{uA₂, uB₁}) :
    (PFunctor.ulift.{_, _, u, v} (P + Q : PFunctor.{max uA₁ uA₂, uB₁})) ≃ₚ
    ((PFunctor.ulift.{_, _, uA, uB} P : PFunctor.{max uA₁ uA, max uB₁ uB}) +
      (Q.ulift : PFunctor.{max uA₂ uA', max uB₁ uB}) : PFunctor.{max uA₁ uA uA₂ uA', max uB₁ uB}) :=
  {
    equivA := {
      toFun := fun a =>
        match ULift.down a with
        | Sum.inl pa => Sum.inl (ULift.up pa)
        | Sum.inr qa => Sum.inr (ULift.up qa)
      invFun := fun a =>
        ULift.up <| match a with
          | Sum.inl pa => Sum.inl (ULift.down pa)
          | Sum.inr qa => Sum.inr (ULift.down qa)
      left_inv := by
        intro a
        cases a with
        | up s =>
          cases s <;> rfl
      right_inv := by
        intro a
        cases a <;> rfl
    }
    equivB := fun a => by
      cases a with
      | up s =>
        cases s
        · exact {
            toFun := fun b => ULift.up (ULift.down b)
            invFun := fun b => ULift.up (ULift.down b)
            left_inv := by intro b; cases b; rfl
            right_inv := by intro b; cases b; rfl
          }
        · exact {
            toFun := fun b => ULift.up (ULift.down b)
            invFun := fun b => ULift.up (ULift.down b)
            left_inv := by intro b; cases b; rfl
            right_inv := by intro b; cases b; rfl
          }
  }

/-- Universe lifting commutes with product. -/
def uliftProdEquiv (Q : PFunctor.{uA₂, uB₂}) :
    (PFunctor.ulift.{_, _, u, v} (P * Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) ≃ₚ
      ((PFunctor.ulift.{_, _, uA, uB} P : PFunctor.{max uA₁ uA, max uB₁ uB}) *
        (PFunctor.ulift.{_, _, uA', uB'} Q : PFunctor.{max uA₂ uA', max uB₂ uB'}) :
          PFunctor.{max uA₁ uA₂ uA uA', max uB₁ uB₂ uB uB'}) :=
  {
    equivA := {
      toFun := fun a => (ULift.up (ULift.down a).1, ULift.up (ULift.down a).2)
      invFun := fun a => ULift.up (ULift.down a.1, ULift.down a.2)
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro a
        rcases a with ⟨pa, qa⟩
        cases pa
        cases qa
        rfl
    }
    equivB := fun a => by
      cases a with
      | up s =>
        rcases s with ⟨pa, qa⟩
        exact {
          toFun := fun b => match ULift.down b with
            | Sum.inl pb => Sum.inl (ULift.up pb)
            | Sum.inr qb => Sum.inr (ULift.up qb)
          invFun := fun b => ULift.up <| match b with
            | Sum.inl pb => Sum.inl (ULift.down pb)
            | Sum.inr qb => Sum.inr (ULift.down qb)
          left_inv := by
            intro b
            cases b with
            | up s =>
              cases s <;> rfl
          right_inv := by
            intro b
            cases b <;> rfl
        }
  }

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
  simpa [tensor, OfNat.ofNat, One.one] using
    (inferInstance : IsEmpty (P.B a.1 × PEmpty))

/-- Tensor product with `1` on the right is equivalent to the constant functor -/
def tensorOne : P ⊗ 1 ≃ₚ C P.A where
  equivA := Equiv.prodPUnit P.A
  equivB := fun _ => Equiv.equivPEmpty _

instance {P} {a : (1 ⊗ P).A} : IsEmpty ((1 ⊗ P).B a) := by
  simpa [tensor, OfNat.ofNat, One.one] using
    (inferInstance : IsEmpty (PEmpty × P.B a.2))

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
def tensorSumDistrib (R : PFunctor.{uA₃, uB₂}) :
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
  equivB := fun ⟨⟨pa, qf⟩, rf⟩ =>
    _root_.Equiv.sigmaAssoc (fun pb qb => R.B (rf ⟨pb, qb⟩))
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
  equivA := {
    toFun := fun
      | ⟨Sum.inl pa, pf⟩ => Sum.inl ⟨pa, pf⟩
      | ⟨Sum.inr qa, pf⟩ => Sum.inr ⟨qa, pf⟩
    invFun := fun
      | Sum.inl ⟨pa, pf⟩ => ⟨Sum.inl pa, pf⟩
      | Sum.inr ⟨qa, pf⟩ => ⟨Sum.inr qa, pf⟩
    left_inv := by
      rintro ⟨a, pf⟩
      cases a <;> rfl
    right_inv := by
      intro a
      cases a <;> rfl
  }
  equivB := fun a => by
    rcases a with ⟨a, pf⟩
    cases a <;> exact _root_.Equiv.refl _

/-- Composition distributes over product on the left. -/
def prodCompDistrib :
    (P * Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ◃ R ≃ₚ
      ((P ◃ R) * (Q ◃ R) : PFunctor.{max uA₁ uA₂ uA₃ uB₁ uB₂, max uB₁ uB₂ uB₃}) where
  equivA := {
    toFun := fun ⟨⟨pa, qa⟩, f⟩ =>
      (⟨pa, fun pb => f (Sum.inl pb)⟩, ⟨qa, fun qb => f (Sum.inr qb)⟩)
    invFun := fun ⟨⟨pa, fp⟩, ⟨qa, fq⟩⟩ =>
      ⟨⟨pa, qa⟩, Sum.elim fp fq⟩
    left_inv := by
      rintro ⟨⟨pa, qa⟩, f⟩
      apply Sigma.ext
      · rfl
      exact heq_of_eq <| by
        funext b
        cases b <;> rfl
    right_inv := by
      rintro ⟨⟨pa, fp⟩, ⟨qa, fq⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨⟨pa, qa⟩, f⟩
    exact {
      toFun := fun s => match s with
        | ⟨Sum.inl pb, rb⟩ => Sum.inl ⟨pb, rb⟩
        | ⟨Sum.inr qb, rb⟩ => Sum.inr ⟨qb, rb⟩
      invFun := fun s => match s with
        | Sum.inl ⟨pb, rb⟩ => ⟨Sum.inl pb, rb⟩
        | Sum.inr ⟨qb, rb⟩ => ⟨Sum.inr qb, rb⟩
      left_inv := by
        intro s
        rcases s with ⟨b, rb⟩
        cases b <;> rfl
      right_inv := by
        intro s
        cases s <;> rfl
    }

end Comp

end Equiv

end PFunctor
