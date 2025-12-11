/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.PFunctor.Multivariate.Basic

/-!
  # Polynomial Functors, Lens, and Charts

  This file defines polynomial functors, lenses, and charts. The goal is to provide basic
  definitions, with their properties and categories defined in later files.
-/

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆ vA vB

namespace PFunctor

section Basic

/-- The zero polynomial functor, defined as `A = PEmpty` and `B _ = PEmpty`, is the identity with
  respect to sum (up to equivalence) -/
instance : Zero PFunctor.{uA, uB} where
  zero := ⟨PEmpty, fun _ => PEmpty⟩

/-- The unit polynomial functor, defined as `A = PUnit` and `B _ = PEmpty`, is the identity with
  respect to product (up to equivalence) -/
instance : One PFunctor.{uA, uB} where
  one := ⟨PUnit, fun _ => PEmpty⟩

/-- The monomial functor, also written `P(X) = A X^ B`, has `A` as its head type and the constant
  family `B_a = B` as the child type for each each shape `a : A` . -/
def monomial (A : Type uA) (B : Type uB) : PFunctor.{uA, uB} :=
  ⟨A, fun _ => B⟩

@[inherit_doc] scoped[PFunctor] infixr:80 " X^ " => monomial

/-- The constant polynomial functor `P(X) = A X^ PEmpty` -/
def C (A : Type uA) : PFunctor.{uA, uB} :=
  A X^ PEmpty

/-- The variable (or indeterminate) polynomial functor `X`, defined as `P(X) = PUnit X^ PUnit`.

This is the identity with respect to tensor product and composition (up to equivalence). -/
def X : PFunctor.{uA, uB} :=
  PUnit X^ PUnit

/-- The linear polynomial functor `P(X) = A X` -/
def linear (A : Type uA) : PFunctor.{uA, uB} :=
  A X^ PUnit

/-- The self monomial polynomial functor `P(X) = S X^ S` -/
def selfMonomial (S : Type uA) : PFunctor.{uA, uA} :=
  S X^ S

/-- The pure power polynomial functor `P(X) = X^ B` -/
def purePower (B : Type uB) : PFunctor.{uA, uB} :=
  PUnit X^ B

/-- A polynomial functor is representable if it is equivalent to `X^A` for some type `A`. -/
alias representable := purePower

instance : IsEmpty (A 0) := inferInstanceAs (IsEmpty PEmpty)
instance : Unique (A 1) := inferInstanceAs (Unique PUnit)
instance {a} : IsEmpty (B 1 a) := inferInstanceAs (IsEmpty PEmpty)
instance {α} (a : α) : IsEmpty (B (C α) a) := inferInstanceAs (IsEmpty PEmpty)
instance : Unique (A X) := inferInstanceAs (Unique PUnit)
instance {a} : Unique (B X a) := inferInstanceAs (Unique PUnit)
instance {α} (a : α) : Unique (B (linear α) a) := inferInstanceAs (Unique PUnit)
instance {β} : Unique (A (purePower β)) := inferInstanceAs (Unique PUnit)

@[simp] lemma C_empty : C PEmpty = 0 := rfl
@[simp] lemma C_unit : C PUnit = 1 := rfl

@[simp] lemma C_A (A : Type u) : (C A).A = A := rfl
@[simp] lemma C_B (A : Type u) (a : (C A).A) : (C A).B a = PEmpty := rfl

@[simp] lemma X_A : X.A = PUnit := rfl
@[simp] lemma X_B (a : X.A) : X.B a = PUnit := rfl

@[simp] lemma linear_A (A : Type u) : (linear A).A = A := rfl
@[simp] lemma linear_B (A : Type u) (a : (linear A).A) : (linear A).B a = PUnit := rfl

@[simp] lemma selfMonomial_A (S : Type u) : (selfMonomial S).A = S := rfl
@[simp] lemma selfMonomial_B (S : Type u) (a : (selfMonomial S).A) : (selfMonomial S).B a = S := rfl
@[simp] lemma selfMonomial_unit : selfMonomial PUnit = X := rfl

@[simp] lemma purePower_A (B : Type u) : (purePower B).A = PUnit := rfl
@[simp] lemma purePower_B (B : Type u) (a : (purePower B).A) : (purePower B).B a = B := rfl
@[simp] lemma purePower_unit : purePower PUnit = X := rfl

end Basic

section Sum

/-- The sum (coproduct) of two polynomial functors `P` and `Q`, written as `P + Q`.

Defined as the sum of the head types and the sum case analysis for the child types.

Note: requires the `B` universe levels to be the same. -/
def sum (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} :=
  ⟨P.A ⊕ Q.A, Sum.elim P.B Q.B⟩

/-- Addition of polynomial functors, defined as the sum construction. -/
instance : HAdd PFunctor.{uA₁, uB} PFunctor.{uA₂, uB} PFunctor.{max uA₁ uA₂, uB} where
  hAdd := sum

instance : Add PFunctor.{uA, uB} where
  add := sum

alias coprod := sum

/-- The generalized sum (sigma type) of an indexed family of polynomial functors. -/
def sigma {I : Type v} (F : I → PFunctor.{uA, uB}) : PFunctor.{max uA v, uB} :=
  ⟨Σ i, (F i).A, fun ⟨i, a⟩ => (F i).B a⟩

-- macro "Σₚ" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``sigma xs b

end Sum

section Prod

/-- The product of two polynomial functors `P` and `Q`, written as `P * Q`.

Defined as the product of the head types and the sum of the child types. -/
def prod (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 ⊕ Q.B ab.2⟩

/-- Multiplication of polynomial functors, defined as the product construction. -/
instance : HMul PFunctor.{uA₁, uB₁} PFunctor.{uA₂, uB₂} PFunctor.{max uA₁ uA₂, max uB₁ uB₂} where
  hMul := prod

instance : Mul PFunctor.{uA, uB} where
  mul := prod

/-- The generalized product (pi type) of an indexed family of polynomial functors. -/
def pi {I : Type v} (F : I → PFunctor.{uA, uB}) : PFunctor.{max uA v, max uB v} :=
  ⟨(i : I) → (F i).A, fun f => Σ i, (F i).B (f i)⟩

end Prod

section Tensor

/-- The tensor (also called parallel or Dirichlet) product of two polynomial functors `P` and `Q`.

Defined as the product of the head types and the product of the child types. -/
def tensor (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 × Q.B ab.2⟩

/-- Infix notation for tensor product `P ⊗ Q` -/
scoped[PFunctor] infixl:70 " ⊗ " => tensor

/-- The unit for the tensor product `Y` -/
alias tensorUnit := X

end Tensor

section Comp

/-- Infix notation for `PFunctor.comp P Q` -/
scoped[PFunctor] infixl:80 " ◃ " => PFunctor.comp

/-- The unit for composition `Y` -/
alias compUnit := X

/-- Repeated composition `P ◃ P ◃ ... ◃ P` (n times). -/
@[simp]
def compNth (P : PFunctor.{uA, uB}) : Nat → PFunctor.{max uA uB, uB}
  | 0 => X
  | Nat.succ n => P ◃ compNth P n

instance : NatPow PFunctor.{max uA uB, uB} where
  pow := compNth

end Comp

section ULift

/-- Lift a polynomial functor `P` to a pair of larger universes. -/
protected def ulift (P : PFunctor.{uA, uB}) : PFunctor.{max uA vA, max uB vB} :=
  ⟨ULift P.A, fun a => ULift (P.B (ULift.down a))⟩

end ULift

/-- Exponential of polynomial functors `P ^ Q` -/
def exp (P Q : PFunctor.{uA, uB}) : PFunctor.{max uA uB, max uA uB} :=
  pi (fun a => P ◃ (X + C (Q.B a)))

instance : HPow PFunctor.{uA, uB} PFunctor.{uA, uB} PFunctor.{max uA uB, max uA uB} where
  hPow := exp

section Fintype

/-- A polynomial functor is finitely branching if each of its branches is a finite type. -/
protected class Fintype (P : PFunctor.{uA, uB}) where
  fintype_B : ∀ a, Fintype (P.B a)

instance {P : PFunctor.{uA, uB}} [inst : P.Fintype] : PFunctor.Fintype (PFunctor.ulift P) where
  fintype_B := fun a => by
    unfold PFunctor.ulift
    haveI : Fintype (P.B (ULift.down a)) := inst.fintype_B (ULift.down a)
    infer_instance

@[simp]
instance {P : PFunctor.{uA, uB}} [inst : P.Fintype] : ∀ a, Fintype (P.B a) :=
  fun a => inst.fintype_B a

end Fintype

/-- An equivalence between two polynomial functors `P` and `Q`, written `P ≃ₚ Q`, is given by an
equivalence of the `A` types and an equivalence between the `B` types for each `a : A`. -/
@[ext]
protected structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- An equivalence between the `A` types -/
  equivA : P.A ≃ Q.A
  /-- An equivalence between the `B` types for each `a : A` -/
  equivB : ∀ a, P.B a ≃ Q.B (equivA a)

@[inherit_doc] scoped[PFunctor] infixl:25 " ≃ₚ " => PFunctor.Equiv

#check Equiv.symm_apply_apply

namespace Equiv

/-- The identity equivalence between a polynomial functor `P` and itself. -/
def refl (P : PFunctor.{uA, uB}) : P ≃ₚ P where
  equivA := _root_.Equiv.refl P.A
  equivB := fun a => _root_.Equiv.refl (P.B a)

/-- The inverse of an equivalence between polynomial functors. -/
def symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (E : P ≃ₚ Q) : Q ≃ₚ P where
  equivA := E.equivA.symm
  equivB := fun a =>
    (Equiv.cast (congrArg Q.B ((Equiv.symm_apply_eq E.equivA).mp rfl))).trans
      (E.equivB (E.equivA.symm a)).symm

/-- The composition of two equivalences between polynomial functors. -/
def trans {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (E : P ≃ₚ Q) (F : Q ≃ₚ R) : P ≃ₚ R where
  equivA := E.equivA.trans F.equivA
  equivB := fun a => (E.equivB a).trans (F.equivB (E.equivA a))

/-- Equivalence between two polynomial functors `P` and `Q` that are equal. -/
def cast {P Q : PFunctor.{uA, uB}} (hA : P.A = Q.A) (hB : ∀ a, P.B a = Q.B (cast hA a)) :
    P ≃ₚ Q where
  equivA := _root_.Equiv.cast hA
  equivB := fun a => _root_.Equiv.cast (hB a)

@[simp]
theorem symm_symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (e : P ≃ₚ Q) :
    e.symm.symm = e := by
  ext a
  · simp [Equiv.symm]
  · simp [Equiv.symm]; ext a b; simp; sorry

@[simp]
theorem symm_comp_self {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (e : P ≃ₚ Q) :
    e.symm.equivA ∘ e.equivA = id := by
  simp [Equiv.symm]

end Equiv

/-- A **lens** between two polynomial functors `P` and `Q` is a pair of a function:
- `toFunA : P.A → Q.A`
- `toFunB : ∀ a, Q.B (toFunA a) → P.B a` -/
structure Lens (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  toFunA : P.A → Q.A
  toFunB : ∀ a, Q.B (toFunA a) → P.B a

/-- Infix notation for constructing a lens `toFunA ⇆ toFunB` -/
infixr:25 " ⇆ " => Lens.mk

/-- A chart between two polynomial functors `P` and `Q` is a pair of a function:
- `toFunA : P.A → Q.A`
- `toFunB : ∀ a, P.B a → Q.B (toFunA a)` -/
structure Chart (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  toFunA : P.A → Q.A
  toFunB : ∀ a, P.B a → Q.B (toFunA a)

/-- Infix notation for constructing a chart `toFunA ⇉ toFunB` -/
infixr:25 " ⇉ " => Chart.mk

section Lemmas

@[ext (iff := false)]
theorem ext {P Q : PFunctor.{uA, uB}} (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) : P = Q := by
  cases P; cases Q; simp at h h' ⊢; subst h; simp_all; funext; exact h' _

lemma X_eq_linear_pUnit : X = linear PUnit := rfl
lemma X_eq_purePower_pUnit : X = purePower PUnit := rfl

section ULift

variable {P : PFunctor.{uA, uB}}

@[simp]
theorem ulift_A : (P.ulift).A = ULift P.A := rfl

@[simp]
theorem ulift_B {a : P.A} : (P.ulift).B (ULift.up a) = ULift (P.B a) := rfl

end ULift

end Lemmas

end PFunctor
