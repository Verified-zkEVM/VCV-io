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

/-- The variable `y` polynomial functor, defined as `A = PUnit` and `B _ = PUnit`, is the identity
  with respect to tensor product and composition (up to equivalence) -/
def y : PFunctor.{uA, uB} :=
  ⟨PUnit, fun _ => PUnit⟩

instance : IsEmpty (A 0) := inferInstanceAs (IsEmpty PEmpty)
instance : Unique (A 1) := inferInstanceAs (Unique PUnit)
instance : IsEmpty (B 1 PUnit.unit) := inferInstanceAs (IsEmpty PEmpty)
instance : Unique (A y) := inferInstanceAs (Unique PUnit)
instance : Unique (B y PUnit.unit) := inferInstanceAs (Unique PUnit)

@[simp] lemma y_A : y.A = PUnit := rfl
@[simp] lemma y_B (a : y.A) : y.B a = PUnit := rfl

end Basic

section Monomial

/-- The monomial functor, also written `P(y) = A y^ B`, has `A` as its head type and the constant
  family `B_a = B` as the child type for each each shape `a : A` . -/
def monomial (A : Type uA) (B : Type uB) : PFunctor.{uA, uB} :=
  ⟨A, fun _ => B⟩

@[inherit_doc] scoped[PFunctor] infixr:80 " y^ " => monomial

/-- The constant polynomial functor `P(y) = A` -/
def C (A : Type uA) : PFunctor.{uA, uB} :=
  A y^ PEmpty

/-- The linear polynomial functor `P(y) = A y` -/
def linear (A : Type uA) : PFunctor.{uA, uB} :=
  A y^ PUnit

/-- The self monomial polynomial functor `P(y) = S y^ S` -/
def selfMonomial (S : Type uA) : PFunctor.{uA, uA} :=
  S y^ S

/-- The pure power polynomial functor `P(y) = y^ B` -/
def purePower (B : Type uB) : PFunctor.{uA, uB} :=
  PUnit y^ B

/-- A polynomial functor is representable if it is equivalent to `y^A` for some type `A`. -/
alias representable := purePower

@[simp] lemma C_zero : C PEmpty = 0 := rfl
@[simp] lemma C_one : C PUnit = 1 := rfl

@[simp] lemma C_A (A : Type u) : (C A).A = A := rfl
@[simp] lemma C_B (A : Type u) (a : (C A).A) : (C A).B a = PEmpty := rfl

@[simp] lemma linear_A (A : Type u) : (linear A).A = A := rfl
@[simp] lemma linear_B (A : Type u) (a : (linear A).A) : (linear A).B a = PUnit := rfl

@[simp] lemma purePower_A (B : Type u) : (purePower B).A = PUnit := rfl
@[simp] lemma purePower_B (B : Type u) (a : (purePower B).A) : (purePower B).B a = B := rfl

end Monomial

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

/-- Infix notation for tensor product `P ⊗ₚ Q` -/
scoped[PFunctor] infixl:70 " ⊗ₚ " => tensor

/-- The unit for the tensor product `Y` -/
alias tensorUnit := y

end Tensor

section Comp

/-- Infix notation for `PFunctor.comp P Q` -/
scoped[PFunctor] infixl:80 " ◃ " => PFunctor.comp

/-- The unit for composition `Y` -/
alias compUnit := y

/-- Repeated composition `P ◃ P ◃ ... ◃ P` (n times). -/
@[simp]
def compNth (P : PFunctor.{uA, uB}) : Nat → PFunctor.{max uA uB, uB}
  | 0 => y
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
  pi (fun a => P ◃ (y + C (Q.B a)))

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
structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- An equivalence between the `A` types -/
  equivA : P.A ≃ Q.A
  /-- An equivalence between the `B` types for each `a : A` -/
  equivB : ∀ a, P.B a ≃ Q.B (equivA a)

@[inherit_doc] scoped[PFunctor] infixl:25 " ≃ₚ " => Equiv

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

end Equiv

/-- A **lens** between two polynomial functors `P` and `Q` is a pair of a function:
- `toFunA : P.A → Q.A`
- `toFunB : ∀ a, Q.B (toFunA a) → P.B a` -/
structure Lens (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  toFunA : P.A → Q.A
  toFunB : ∀ a, Q.B (toFunA a) → P.B a

/-- Infix notation for constructing a lens `toFunA ⇆ toFunB` -/
infixr:25 " ⇆ " => Lens.mk

namespace Lens

/-- The identity lens -/
protected def id (P : PFunctor.{uA, uB}) : Lens P P where
  toFunA := id
  toFunB := fun _ => id

/-- Composition of lenses -/
def comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (l : Lens Q R) (l' : Lens P Q) : Lens P R where
  toFunA := l.toFunA ∘ l'.toFunA
  toFunB := fun i => (l'.toFunB i) ∘ l.toFunB (l'.toFunA i)

@[inherit_doc] infixl:75 " ∘ₗ " => comp

@[simp]
theorem id_comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Lens P Q) :
    (Lens.id Q) ∘ₗ f = f := rfl

@[simp]
theorem comp_id {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Lens P Q) :
    f ∘ₗ (Lens.id P) = f := rfl

theorem comp_assoc {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {S : PFunctor.{uA₄, uB₄}} (l : Lens R S) (l' : Lens Q R) (l'' : Lens P Q) :
    (l ∘ₗ l') ∘ₗ l'' = l ∘ₗ (l' ∘ₗ l'') := rfl

/-- An equivalence between two polynomial functors `P` and `Q`, using lenses.
    This corresponds to an isomorphism in the category `PFunctor` with `Lens` morphisms. -/
@[ext]
structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  toLens : Lens P Q
  invLens : Lens Q P
  left_inv : comp invLens toLens = Lens.id P
  right_inv : comp toLens invLens = Lens.id Q

@[inherit_doc] infix:50 " ≃ₗ " => Equiv

namespace Equiv

@[refl]
def refl (P : PFunctor.{uA, uB}) : P ≃ₗ P :=
  ⟨Lens.id P, Lens.id P, rfl, rfl⟩

@[symm]
def symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (e : P ≃ₗ Q) : Q ≃ₗ P :=
  ⟨e.invLens, e.toLens, e.right_inv, e.left_inv⟩

@[trans]
def trans {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (e₁ : P ≃ₗ Q) (e₂ : Q ≃ₗ R) : P ≃ₗ R :=
  ⟨e₂.toLens ∘ₗ e₁.toLens, e₁.invLens ∘ₗ e₂.invLens,
    by
      rw [comp_assoc]
      rw (occs := [2]) [← comp_assoc]
      simp [e₁.left_inv, e₂.left_inv],
    by
      rw [comp_assoc]
      rw (occs := [2]) [← comp_assoc]
      simp [e₁.right_inv, e₂.right_inv]⟩

end Equiv

/-- The (unique) initial lens from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{uA, uB}} : Lens 0 P :=
  PEmpty.elim ⇆ fun a => PEmpty.elim a

/-- The (unique) terminal lens from any functor `P` to the unit functor `1`. -/
def terminal {P : PFunctor.{uA, uB}} : Lens P 1 :=
  (fun _ => PUnit.unit) ⇆ (fun _ => PEmpty.elim)

alias fromZero := initial
alias toOne := terminal

/-- Left injection lens `inl : P → P + Q` -/
def inl {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Lens.{uA₁, uB, max uA₁ uA₂, uB} P (P + Q) :=
  Sum.inl ⇆ (fun _ d => d)

/-- Right injection lens `inr : Q → P + Q` -/
def inr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Lens.{uA₂, uB, max uA₁ uA₂, uB} Q (P + Q) :=
  Sum.inr ⇆ (fun _ d => d)

/-- Copairing of lenses `[l₁, l₂]ₗ : P + Q → R` -/
def coprodPair {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB₃}}
    (l₁ : Lens P R) (l₂ : Lens Q R) :
    Lens.{max uA₁ uA₂, uB, uA₃, uB₃} (P + Q) R :=
  (Sum.elim l₁.toFunA l₂.toFunA) ⇆
    (fun a d => match a with
      | Sum.inl pa => l₁.toFunB pa d
      | Sum.inr qa => l₂.toFunB qa d)

/-- Parallel application of lenses for coproduct `l₁ ⊎ l₂ : P + Q → R + W` -/
def coprodMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₃}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂, uB₁, max uA₃ uA₄, uB₃} (P + Q) (R + W) :=
  (Sum.map l₁.toFunA l₂.toFunA) ⇆
    (fun psum => match psum with
      | Sum.inl pa => l₁.toFunB pa
      | Sum.inr qa => l₂.toFunB qa)

-- def sigmaExists
-- def sigmaMap

/-- Projection lens `fst : P * Q → P` -/
def fst {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} (P * Q) P :=
  Prod.fst ⇆ (fun _ => Sum.inl)

/-- Projection lens `snd : P * Q → Q` -/
def snd {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, uA₂, uB₂} (P * Q) Q :=
  Prod.snd ⇆ (fun _ => Sum.inr)

/-- Pairing of lenses `⟨l₁, l₂⟩ₗ : P → Q * R` -/
def prodPair {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (l₁ : Lens P Q) (l₂ : Lens P R) :
    Lens.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q * R) :=
  (fun p => (l₁.toFunA p, l₂.toFunA p)) ⇆
    (fun p => Sum.elim (l₁.toFunB p) (l₂.toFunB p))

/-- Parallel application of lenses for product `l₁ ×ₗ l₂ : P * Q → R * W` -/
def prodMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P * Q) (R * W) :=
  (fun pq => (l₁.toFunA pq.1, l₂.toFunA pq.2)) ⇆
    (fun pq => Sum.elim (Sum.inl ∘ l₁.toFunB pq.1) (Sum.inr ∘ l₂.toFunB pq.2))

-- def piForall
-- def piMap

/-- Apply lenses to both sides of a composition: `l₁ ◃ₗ l₂ : (P ◃ Q ⇆ R ◃ W)` -/
def compMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂ uB₁, max uB₁ uB₂, max uA₃ uA₄ uB₃, max uB₃ uB₄} (P ◃ Q) (R ◃ W) :=
  (fun ⟨pa, pq⟩ => ⟨l₁.toFunA pa, fun rb' => l₂.toFunA (pq (l₁.toFunB pa rb'))⟩) ⇆
    (fun ⟨pa, pq⟩ ⟨rb, wc⟩ =>
      let pb := l₁.toFunB pa rb
      let qc := l₂.toFunB (pq pb) wc
      ⟨pb, qc⟩)

/-- Apply lenses to both sides of a tensor / parallel product: `l₁ ⊗ₗ l₂ : (P ⊗ₚ Q ⇆ R ⊗ₚ W)` -/
def tensorMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P ⊗ₚ Q) (R ⊗ₚ W) :=
  (fun ⟨pa, qa⟩ => (l₁.toFunA pa, l₂.toFunA qa)) ⇆
    (fun ⟨_pa, qa⟩ ⟨rb, wb⟩ => (l₁.toFunB _pa rb, l₂.toFunB qa wb))

/-- Lens to introduce `y` on the right: `P → P ◃ y` -/
def tildeR {P : PFunctor.{uA, uB}} : Lens P (P ◃ y) :=
  (fun a => ⟨a, fun _ => PUnit.unit⟩) ⇆ (fun _a => fun ⟨b, _⟩ => b)

/-- Lens to introduce `y` on the left: `P → y ◃ P` -/
def tildeL {P : PFunctor.{uA, uB}} : Lens P (y ◃ P) :=
  (fun a => ⟨PUnit.unit, fun _ => a⟩) ⇆ (fun _a => fun ⟨_, b⟩ => b)

/-- Lens from `P ◃ y` to `P` -/
def invTildeR {P : PFunctor.{uA, uB}} : Lens (P ◃ y) P :=
  (fun a => a.1) ⇆ (fun _ b => ⟨b, PUnit.unit⟩)

/-- Lens from `y ◃ P` to `P` -/
def invTildeL {P : PFunctor.{uA, uB}} : Lens (y ◃ P) P :=
  (fun ⟨_, f⟩ => f PUnit.unit) ⇆ (fun _ b => ⟨PUnit.unit, b⟩)

@[inherit_doc] infixl:75 " ◃ₗ " => compMap
@[inherit_doc] infixl:75 " ×ₗ " => prodMap
@[inherit_doc] infixl:75 " ⊎ₗ " => coprodMap
@[inherit_doc] infixl:75 " ⊗ₗ " => tensorMap
notation "[" l₁ "," l₂ "]ₗ" => coprodPair l₁ l₂
notation "⟨" l₁ "," l₂ "⟩ₗ" => prodPair l₁ l₂

/-- The type of lenses from a polynomial functor `P` to `y` -/
def enclose (P : PFunctor.{uA, uB}) : Type max uA uA₁ uB uB₁ :=
  Lens P y.{uA₁, uB₁}

/-- Helper lens for `speedup` -/
def fixState {S : Type u} : Lens (selfMonomial S) (selfMonomial S ◃ selfMonomial S) :=
  (fun s₀ => ⟨s₀, fun s₁ => s₁⟩) ⇆ (fun _s₀ => fun ⟨_s₁, s₂⟩ => s₂)

/-- The `speedup` lens operation: `Lens (S y^S) P → Lens (S y^S) (P ◃ P)` -/
def speedup {S : Type u} {P : PFunctor.{uA, uB}} (l : Lens (selfMonomial S) P) :
    Lens (selfMonomial S) (P ◃ P) :=
  (l ◃ₗ l) ∘ₗ fixState

end Lens

/-- A chart between two polynomial functors `P` and `Q` is a pair of a function:
- `toFunA : P.A → Q.A`
- `toFunB : ∀ a, P.B a → Q.B (toFunA a)` -/
structure Chart (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  toFunA : P.A → Q.A
  toFunB : ∀ a, P.B a → Q.B (toFunA a)

/-- Infix notation for constructing a chart `toFunA ⇉ toFunB` -/
infixr:25 " ⇉ " => Chart.mk

namespace Chart

/-- The identity chart -/
protected def id (P : PFunctor.{uA, uB}) : Chart P P := id ⇉ fun _ => id

/-- Composition of charts -/
def comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (c' : Chart Q R) (c : Chart P Q) : Chart P R where
  toFunA := c'.toFunA ∘ c.toFunA
  toFunB := fun i => c'.toFunB (c.toFunA i) ∘ c.toFunB i

/-- Infix notation for chart composition `c' ∘c c` -/
infixl:75 " ∘c " => comp

@[simp]
theorem id_comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Chart P Q) :
    (Chart.id Q) ∘c f = f := rfl

@[simp]
theorem comp_id {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Chart P Q) :
    f ∘c (Chart.id P) = f := rfl

theorem comp_assoc {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {S : PFunctor.{uA₄, uB₄}} (c : Chart R S) (c' : Chart Q R) (c'' : Chart P Q) :
    (c ∘c c') ∘c c'' = c ∘c (c' ∘c c'') := rfl

/-- An equivalence between two polynomial functors `P` and `Q`, using charts.
    This corresponds to an isomorphism in the category `PFunctor` with `Chart` morphisms. -/
@[ext]
structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  toChart : Chart P Q
  invChart : Chart Q P
  left_inv : comp invChart toChart = Chart.id P
  right_inv : comp toChart invChart = Chart.id Q

/-- Infix notation for chart equivalence `P ≃c Q` -/
infix:50 " ≃c " => Equiv

namespace Equiv

@[refl]
def refl (P : PFunctor.{uA, uB}) : P ≃c P :=
  ⟨Chart.id P, Chart.id P, rfl, rfl⟩

@[symm]
def symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (e : P ≃c Q) : Q ≃c P :=
  ⟨e.invChart, e.toChart, e.right_inv, e.left_inv⟩

def trans {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (e₁ : P ≃c Q) (e₂ : Q ≃c R) : P ≃c R :=
  ⟨e₂.toChart ∘c e₁.toChart, e₁.invChart ∘c e₂.invChart,
    by
      rw [comp_assoc]
      rw (occs := [2]) [← comp_assoc]
      simp [e₁.left_inv, e₂.left_inv],
    by
      rw [comp_assoc]
      rw (occs := [2]) [← comp_assoc]
      simp [e₁.right_inv, e₂.right_inv]⟩

end Equiv

/-- The (unique) initial chart from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{uA, uB}} : Chart 0 P :=
  PEmpty.elim ⇉ fun _ => PEmpty.elim

/-- The (unique) terminal chart from any functor `P` to the functor `Y`. -/
def terminal {P : PFunctor.{uA, uB}} : Chart P y :=
  (fun _ => PUnit.unit) ⇉ (fun _ _ => PUnit.unit)

alias fromZero := initial
alias toOne := terminal

end Chart

section Lemmas

@[ext (iff := false)]
theorem ext {P Q : PFunctor.{uA, uB}} (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) : P = Q := by
  cases P; cases Q; simp at h h' ⊢; subst h; simp_all; funext; exact h' _

@[ext (iff := false)]
theorem Lens.ext {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (l₁ l₂ : Lens P Q)
    (h₁ : ∀ a, l₁.toFunA a = l₂.toFunA a) (h₂ : ∀ a, l₁.toFunB a = (h₁ a) ▸ l₂.toFunB a) :
    l₁ = l₂ := by
  rcases l₁ with ⟨toFunA₁, _⟩
  rcases l₂ with ⟨toFunA₂, _⟩
  have h : toFunA₁ = toFunA₂ := funext h₁
  subst h
  simp_all
  exact funext h₂

@[ext (iff := false)]
theorem Chart.ext {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (c₁ c₂ : Chart P Q)
    (h₁ : ∀ a, c₁.toFunA a = c₂.toFunA a) (h₂ : ∀ a, c₁.toFunB a = (h₁ a) ▸ c₂.toFunB a) :
    c₁ = c₂ := by
  rcases c₁ with ⟨toFunA₁, _⟩
  rcases c₂ with ⟨toFunA₂, _⟩
  have h : toFunA₁ = toFunA₂ := funext h₁
  subst h
  simp_all
  exact funext h₂

lemma y_eq_linear_pUnit : y = linear PUnit := rfl
lemma y_eq_purePower_pUnit : y = purePower PUnit := rfl

section ULift

variable {P : PFunctor.{uA, uB}}

@[simp]
theorem ulift_A : (P.ulift).A = ULift P.A := rfl

@[simp]
theorem ulift_B {a : P.A} : (P.ulift).B (ULift.up a) = ULift (P.B a) := rfl

namespace Lens.Equiv

def ulift : P.ulift ≃ₗ P where
  toLens := (fun a => ULift.down a) ⇆ (fun _ b => ULift.up b)
  invLens := (fun a => ULift.up a) ⇆ (fun _ b => ULift.down b)
  left_inv := rfl
  right_inv := rfl

end Lens.Equiv

end ULift

namespace Lens

section Coprod

-- Note the universe levels for `uB` in order to apply coproduct / sum
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
  {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}} {X : PFunctor.{uA₅, uB₅}}

@[simp]
theorem coprodMap_comp_inl (l₁ : Lens P R) (l₂ : Lens Q W) :
    ((l₁ ⊎ₗ l₂) ∘ₗ Lens.inl) = (Lens.inl ∘ₗ l₁) := rfl

@[simp]
theorem coprodMap_comp_inr (l₁ : Lens P R) (l₂ : Lens Q W) :
    ((l₁ ⊎ₗ l₂) ∘ₗ Lens.inr) = (Lens.inr ∘ₗ l₂) := rfl

theorem coprodPair_comp_coprodMap (l₁ : Lens P R) (l₂ : Lens Q W)
    (f : Lens R X) (g : Lens W X) :
  Lens.coprodPair f g ∘ₗ (l₁ ⊎ₗ l₂) = Lens.coprodPair (f ∘ₗ l₁) (g ∘ₗ l₂) := by
  ext a <;> rcases a with a | a <;> rfl

@[simp]
theorem coprodPair_comp_inl (f : Lens P R) (g : Lens Q R) :
    Lens.coprodPair f g ∘ₗ Lens.inl = f := rfl

@[simp]
theorem coprodPair_comp_inr (f : Lens P R) (g : Lens Q R) :
    Lens.coprodPair f g ∘ₗ Lens.inr = g := rfl

theorem comp_inl_inr (h : Lens.{max uA₁ uA₂, uB₁, uA₃, uB₃} (P + Q) R) :
    Lens.coprodPair (h ∘ₗ Lens.inl) (h ∘ₗ Lens.inr) = h := by
  ext a <;> rcases a <;> rfl

@[simp]
theorem coprodMap_id :
    Lens.coprodMap (Lens.id P) (Lens.id Q) = Lens.id.{max uA₁ uA₂, uB₁} (P + Q) := by
  ext a <;> rcases a <;> rfl

@[simp]
theorem coprodPair_inl_inr :
    Lens.coprodPair Lens.inl Lens.inr = Lens.id.{max uA₁ uA₂, uB₁} (P + Q) := by
  ext a <;> rcases a <;> rfl

namespace Equiv

/-- Commutativity of coproduct -/
def coprodComm (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    Lens.Equiv.{max uA₁ uA₂, uB, max uA₁ uA₂, uB} (P + Q) (Q + P) where
  toLens := Lens.coprodPair Lens.inr Lens.inl
  invLens := Lens.coprodPair Lens.inr Lens.inl
  left_inv := by
    ext a <;> rcases a with a | a <;> rfl
  right_inv := by
    ext a <;> rcases a with a | a <;> rfl

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}

@[simp]
theorem coprodComm_symm :
    (coprodComm P Q).symm = coprodComm Q P := rfl

/-- Associativity of coproduct -/
def coprodAssoc :
    Lens.Equiv.{max uA₁ uA₂ uA₃, uB, max uA₁ uA₂ uA₃, uB} ((P + Q) + R) (P + (Q + R)) where
  toLens := -- Maps (P + Q) + R to P + (Q + R)
    Lens.coprodPair
      (Lens.coprodPair -- Maps P + Q to P + (Q + R)
        (Lens.inl) -- Maps P to P + (Q + R) via Sum.inl
        (Lens.inr ∘ₗ Lens.inl) -- Maps Q to P + (Q + R) via Sum.inr ∘ Sum.inl
      )
      (Lens.inr ∘ₗ Lens.inr) -- Maps R to P + (Q + R) via Sum.inr ∘ Sum.inr
  invLens := -- Maps P + (Q + R) to (P + Q) + R
    Lens.coprodPair
      (Lens.inl ∘ₗ Lens.inl) -- Maps P to (P + Q) + R via Sum.inl ∘ Sum.inl
      (Lens.coprodPair -- Maps Q + R to (P + Q) + R
        (Lens.inl ∘ₗ Lens.inr) -- Maps Q to (P + Q) + R via Sum.inl ∘ Sum.inr
        (Lens.inr) -- Maps R to (P + Q) + R via Sum.inr
      )
  left_inv := by
    ext a <;> rcases a with (a | a) |a <;> rfl
  right_inv := by
    ext a <;> rcases a with a | a |a <;> rfl

/-- Coproduct with `0` is identity (right) -/
def coprodZero :
    Lens.Equiv.{max uA uA₁, uB, uA₁, uB} (P + (0 : PFunctor.{uA, uB})) P where
  toLens := Lens.coprodPair (Lens.id P) Lens.initial
  invLens := Lens.inl
  left_inv := by
    ext a <;> rcases a with a | a
    · rfl
    · exact PEmpty.elim a
    · rfl
    · exact PEmpty.elim a
  right_inv := by
    ext <;> rfl

/-- Coproduct with `0` is identity (left) -/
def zeroCoprod :
    Lens.Equiv.{max uA uA₁, uB, uA₁, uB} ((0 : PFunctor.{uA, uB}) + P) P where
  toLens := Lens.coprodPair Lens.initial (Lens.id P)
  invLens := Lens.inr
  left_inv := by
    ext a <;> rcases a with a | a
    · exact PEmpty.elim a
    · rfl
    · exact PEmpty.elim a
    · rfl
  right_inv := by
    ext <;> rfl

end Equiv

end Coprod

section Prod

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {W : PFunctor.{uA₄, uB₄}} {X : PFunctor.{uA₅, uB₅}}

@[simp]
theorem fst_comp_prodMap (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.fst ∘ₗ (l₁ ×ₗ l₂) = l₁ ∘ₗ Lens.fst := rfl

@[simp]
theorem snd_comp_prodMap (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.snd ∘ₗ (l₁ ×ₗ l₂) = l₂ ∘ₗ Lens.snd := rfl

theorem prodMap_comp_prodPair (l₁ : Lens Q W) (l₂ : Lens R X) (f : Lens P Q) (g : Lens P R) :
    (l₁ ×ₗ l₂) ∘ₗ Lens.prodPair f g = Lens.prodPair (l₁ ∘ₗ f) (l₂ ∘ₗ g) := by
  ext a x
  · rfl
  · cases x <;> rfl

@[simp]
theorem fst_comp_prodPair (f : Lens P Q) (g : Lens P R) :
    Lens.fst ∘ₗ Lens.prodPair f g = f := rfl

@[simp]
theorem snd_comp_prodPair (f : Lens P Q) (g : Lens P R) :
    Lens.snd ∘ₗ Lens.prodPair f g = g := rfl

theorem comp_fst_snd (h : Lens.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q * R)) :
    Lens.prodPair (Lens.fst ∘ₗ h) (Lens.snd ∘ₗ h) = h := by
  ext a x
  · rfl
  · cases x <;> rfl

@[simp]
theorem prodMap_id :
    Lens.prodMap (Lens.id P) (Lens.id Q) = Lens.id.{max uA₁ uA₂, max uB₁ uB₂} (P * Q) := by
  ext a x
  · rfl
  · cases x <;> rfl

@[simp]
theorem prodPair_fst_snd :
    Lens.prodPair Lens.fst Lens.snd = Lens.id.{max uA₁ uA₂, max uB₁ uB₂} (P * Q) := by
  ext a x
  · rfl
  · cases x <;> rfl

namespace Equiv

/-- Commutativity of product -/
def prodComm (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}):
    Lens.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂} (P * Q) (Q * P) where
  toLens := Prod.swap ⇆ (fun _ => Sum.elim Sum.inr Sum.inl)
  invLens := Prod.swap ⇆ (fun _ => Sum.elim Sum.inr Sum.inl)
  left_inv := by
    ext _ b
    · rfl
    · cases b <;> rfl
  right_inv := by
    ext _ b
    · rfl
    · cases b <;> rfl

@[simp]
theorem prodComm_symm : (prodComm P Q).symm = prodComm Q P := rfl

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- Associativity of product -/
def prodAssoc : Lens.Equiv.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃, max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}
    ((P * Q) * R) (P * (Q * R)) where
  toLens := (_root_.Equiv.prodAssoc P.A Q.A R.A).toFun ⇆
              (fun _ d => (Equiv.sumAssoc _ _ _).invFun d)
  invLens := (_root_.Equiv.prodAssoc P.A Q.A R.A).invFun ⇆
               (fun _ d => Equiv.sumAssoc _ _ _ d)
  left_inv := by
    ext _ b
    · rfl
    · rcases b with b | _
      · cases b <;> rfl
      · rfl
  right_inv := by
    ext _ b
    · rfl
    · rcases b with _ | b
      · rfl
      · cases b <;> rfl

/-- Product with `1` is identity (right) -/
def prodOne :
    Lens.Equiv.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} (P * (1 : PFunctor.{uA₂, uB₂})) P where
  toLens := Prod.fst ⇆ (fun _ => Sum.inl)
  invLens := (fun p => (p, PUnit.unit)) ⇆ (fun _ => Sum.elim id PEmpty.elim)
  left_inv := by
    ext _ b
    · rfl
    · rcases b with _ | b
      · rfl
      · cases b
  right_inv := by
    ext <;> rfl

/-- Product with `1` is identity (left) -/
def oneProd :
    Lens.Equiv.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} ((1 : PFunctor.{uA₂, uB₂}) * P) P where
  toLens := Prod.snd ⇆ (fun _ => Sum.inr)
  invLens := (fun p => (PUnit.unit, p)) ⇆ (fun _ => Sum.elim PEmpty.elim id)
  left_inv := by
    ext _ b
    · rfl
    · rcases b with b | _
      · cases b
      · rfl
  right_inv := by
    ext <;> rfl

/-- Product with `0` is zero (right) -/
def prodZero :
    Lens.Equiv.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} (P * (0 : PFunctor.{uA₂, uB₂})) 0 where
  toLens := (fun a => PEmpty.elim a.2) ⇆ (fun _ x => PEmpty.elim x)
  invLens := PEmpty.elim ⇆ (fun pe _ => PEmpty.elim pe)
  left_inv := by
    ext ⟨_, a⟩ _ <;> exact PEmpty.elim a
  right_inv := by
    ext ⟨_, _⟩

/-- Product with `0` is zero (left) -/
def zeroProd :
    Lens.Equiv.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} ((0 : PFunctor.{uA₂, uB₂}) * P) 0 where
  toLens := (fun ⟨pa, _⟩ => PEmpty.elim pa) ⇆ (fun _ x => PEmpty.elim x)
  invLens := PEmpty.elim ⇆ (fun pe _ => PEmpty.elim pe)
  left_inv := by
    ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by
    ext ⟨_, _⟩

variable {R : PFunctor.{uA₃, uB₂}}

/-- Left distributive law for product over coproduct -/
def prodCoprodDistrib :
    Lens.Equiv.{max uA₁ uA₂ uA₃, max uB₁ uB₂, max uA₁ uA₂ uA₃, max uB₁ uB₂}
      (P * (Q + R)) ((P * Q) + (P * R)) where
  toLens := (fun ⟨p, qr⟩ => match qr with
              | Sum.inl q => Sum.inl (p, q)
              | Sum.inr r => Sum.inr (p, r)) ⇆
            (fun ⟨_, qr⟩ => match qr with
              | Sum.inl _ => id -- P.B p ⊕ Q.B q
              | Sum.inr _ => id) -- P.B p ⊕ R.B r
  invLens := (Sum.elim
              (fun ⟨p, q⟩ => (p, Sum.inl q))
              (fun ⟨p, r⟩ => (p, Sum.inr r))) ⇆
             (fun pq_pr => match pq_pr with
              | Sum.inl _ => id -- P.B p ⊕ Q.B q
              | Sum.inr _ => id) -- P.B p ⊕ R.B r
  left_inv := by
    ext a <;> rcases a with ⟨p, q | r⟩ <;> rfl
  right_inv := by
    ext a <;> rcases a with ⟨p, q⟩ | ⟨p, r⟩ <;> rfl

/-- Right distributive law for coproduct over product -/
def coprodProdDistrib :
    Lens.Equiv.{max uA₁ uA₂ uA₃, max uB₁ uB₂, max uA₁ uA₂ uA₃, max uB₁ uB₂}
      ((Q + R) * P) ((Q * P) + (R * P)) where
  toLens := (fun ⟨qr, p⟩ => Sum.elim (fun q => Sum.inl (q, p)) (fun r => Sum.inr (r, p)) qr) ⇆
            (fun ⟨qr, p⟩ => match qr with
              | Sum.inl _ => id
              | Sum.inr _ => id)
  invLens := (fun qp_rp => match qp_rp with
              | Sum.inl (q, p) => (Sum.inl q, p)
              | Sum.inr (r, p) => (Sum.inr r, p)) ⇆
             (fun qp_rp => match qp_rp with
              | Sum.inl _ => id
              | Sum.inr _ => id)
  left_inv := by
    ext a <;> rcases a with ⟨q | r, p⟩ <;> rfl
  right_inv := by
    ext a <;> rcases a with ⟨q, p⟩ | ⟨r, p⟩ <;> rfl

end Equiv

end Prod

section Comp

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

@[simp]
theorem compMap_id :
    (Lens.id P) ◃ₗ (Lens.id Q) = Lens.id (P ◃ Q) := by
  ext ⟨_, _⟩ ⟨_, _⟩ <;> rfl

theorem compMap_comp
    {P' : PFunctor.{uA₄, uB₄}} {Q' : PFunctor.{uA₅, uB₅}} {R' : PFunctor.{uA₆, uB₆}}
    (l₁ : Lens P P') (l₂ : Lens Q Q') (l₁' : Lens P' R) (l₂' : Lens Q' R') :
    (l₁' ∘ₗ l₁) ◃ₗ (l₂' ∘ₗ l₂) = (l₁' ◃ₗ l₂') ∘ₗ (l₁ ◃ₗ l₂) := rfl

namespace Equiv

/-- Associativity of composition -/
def compAssoc : (P ◃ Q) ◃ R ≃ₗ P ◃ (Q ◃ R) where
  toLens := (fun ⟨⟨pa, qf⟩, rf⟩ => ⟨pa, fun pb => ⟨qf pb, fun qb => rf ⟨pb, qb⟩⟩⟩) ⇆
            (fun _ ⟨pb, ⟨qb, rb⟩⟩ => ⟨⟨pb, qb⟩, rb⟩)
  invLens := (fun ⟨pa, g⟩ => ⟨⟨pa, fun pb => (g pb).1⟩, fun ⟨pb, qb⟩ => (g pb).2 qb⟩) ⇆
             (fun _ ⟨⟨pb, qb⟩, rb⟩ => ⟨pb, ⟨qb, rb⟩⟩)
  left_inv := rfl
  right_inv := rfl

/-- Composition with `y` is identity (right) -/
def compY : P ◃ y ≃ₗ P where
  toLens := invTildeR
  invLens := tildeR
  left_inv := rfl
  right_inv := rfl

/-- Composition with `y` is identity (left) -/
def yComp : y ◃ P ≃ₗ P where
  toLens := invTildeL
  invLens := tildeL
  left_inv := rfl
  right_inv := rfl

/-- Distributivity of composition over coproduct on the right -/
def coprodCompDistrib {R : PFunctor.{uA₃, uB₂}} :
    Lens.Equiv.{max uA₁ uA₂ uA₃ uB₂, max uB₁ uB₂, max uA₁ uA₂ uA₃ uB₂, max uB₁ uB₂}
      ((Q + R : PFunctor.{max uA₂ uA₃, uB₂}) ◃ P) ((Q ◃ P) + (R ◃ P)) where
  toLens := (fun a => match a with
              | ⟨Sum.inl qa, pf⟩ => Sum.inl ⟨qa, pf⟩
              | ⟨Sum.inr ra, pf⟩ => Sum.inr ⟨ra, pf⟩) ⇆
            (fun ⟨qr, pf⟩ b => match qr with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  invLens := (fun a => match a with
              | Sum.inl ⟨qa, pf⟩ => ⟨Sum.inl qa, pf⟩
              | Sum.inr ⟨ra, pf⟩ => ⟨Sum.inr ra, pf⟩) ⇆
            (fun qprp b => match qprp with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  left_inv := by
    ext a <;> rcases a with ⟨_ | _, _⟩ <;> rfl
  right_inv := by
    ext a <;> cases a <;> rfl

end Equiv

end Comp

section Tensor

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

@[simp]
theorem tensorMap_id : (Lens.id P) ⊗ₗ (Lens.id Q) = Lens.id (P ⊗ₚ Q) :=
  rfl

theorem tensorMap_comp
    {P' : PFunctor.{uA₄, uB₄}} {Q' : PFunctor.{uA₅, uB₅}} {R' : PFunctor.{uA₆, uB₆}}
    (l₁ : Lens P P') (l₂ : Lens Q Q') (l₁' : Lens P' R) (l₂' : Lens Q' R') :
    (l₁' ∘ₗ l₁) ⊗ₗ (l₂' ∘ₗ l₂) = (l₁' ⊗ₗ l₂') ∘ₗ (l₁ ⊗ₗ l₂) := rfl

namespace Equiv

/-- Commutativity of tensor product -/
def tensorComm (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) : P ⊗ₚ Q ≃ₗ Q ⊗ₚ P where
  toLens := Prod.swap ⇆ (fun _ => Prod.swap)
  invLens := Prod.swap ⇆ (fun _ => Prod.swap)
  left_inv := rfl
  right_inv := rfl

/-- Associativity of tensor product -/
def tensorAssoc : (P ⊗ₚ Q) ⊗ₚ R ≃ₗ P ⊗ₚ (Q ⊗ₚ R) where
  toLens := (_root_.Equiv.prodAssoc _ _ _).toFun ⇆
            (fun _ => (_root_.Equiv.prodAssoc _ _ _).invFun)
  invLens := (_root_.Equiv.prodAssoc _ _ _).invFun ⇆
            (fun _ => (_root_.Equiv.prodAssoc _ _ _).toFun)
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `y` is identity (right) -/
def tensorY : P ⊗ₚ y ≃ₗ P where
  toLens := Prod.fst ⇆ (fun _ b => (b, PUnit.unit))
  invLens := (fun p => (p, PUnit.unit)) ⇆ (fun _ bp => bp.1)
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `y` is identity (left) -/
def yTensor : y ⊗ₚ P ≃ₗ P where
  toLens := Prod.snd ⇆ (fun _ b => (PUnit.unit, b))
  invLens := (fun p => (PUnit.unit, p)) ⇆ (fun _ bp => bp.2)
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `0` is zero (left) -/
def zeroTensor : 0 ⊗ₚ P ≃ₗ 0 where
  toLens := (fun a => PEmpty.elim a.1) ⇆ (fun _ b => PEmpty.elim b)
  invLens := PEmpty.elim ⇆ (fun a _ => PEmpty.elim a)
  left_inv := by
    ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by
    ext a <;> exact PEmpty.elim a

/-- Tensor product with `0` is zero (right) -/
def tensorZero : P ⊗ₚ 0 ≃ₗ 0 where
  toLens := (fun a => PEmpty.elim a.2) ⇆ (fun _ b => PEmpty.elim b)
  invLens := PEmpty.elim ⇆ (fun a _ => PEmpty.elim a)
  left_inv := by
    ext ⟨_, b⟩ <;> exact PEmpty.elim b
  right_inv := by
    ext a <;> exact PEmpty.elim a

variable {R : PFunctor.{uA₃, uB₂}}

/-- Left distributivity of tensor product over coproduct -/
def tensorCoprodDistrib :
    Lens.Equiv.{max uA₁ uA₂ uA₃, max uB₁ uB₂, max uA₁ uA₂ uA₃, max uB₁ uB₂}
      (P ⊗ₚ (Q + R : PFunctor.{max uA₂ uA₃, uB₂})) ((P ⊗ₚ Q) + (P ⊗ₚ R)) where
  toLens := (fun ⟨p, qr⟩ => match qr with
              | Sum.inl q => Sum.inl (p, q)
              | Sum.inr r => Sum.inr (p, r)) ⇆
            (fun ⟨p, qr⟩ b => match qr with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  invLens := (fun pqpr => match pqpr with
              | Sum.inl (p, q) => (p, Sum.inl q)
              | Sum.inr (p, r) => (p, Sum.inr r)) ⇆
             (fun pqpr b => match pqpr with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  left_inv := by
    ext ⟨_, qr⟩ <;> cases qr <;> rfl
  right_inv := by
    ext pqpr <;> cases pqpr <;> rfl

/-- Right distributivity of tensor product over coproduct -/
def coprodTensorDistrib :
    (Q + R : PFunctor.{max uA₂ uA₃, uB₂}) ⊗ₚ P
      ≃ₗ ((Q ⊗ₚ P) + (R ⊗ₚ P) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
  toLens := (fun ⟨qr, p⟩ => match qr with
              | Sum.inl q => Sum.inl (q, p)
              | Sum.inr r => Sum.inr (r, p)) ⇆
            (fun ⟨qr, _⟩ b => match qr with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  invLens := (fun qprp => match qprp with
              | Sum.inl (q, p) => (Sum.inl q, p)
              | Sum.inr (r, p) => (Sum.inr r, p)) ⇆
             (fun qprp b => match qprp with
              | Sum.inl _ => b
              | Sum.inr _ => b)
  left_inv := by
    ext ⟨qr, _⟩ <;> cases qr <;> rfl
  right_inv := by
    ext qprp <;> cases qprp <;> rfl

end Equiv

end Tensor

section Sigma

variable {I : Type v}

instance [IsEmpty I] {F : I → PFunctor.{u}} : IsEmpty (sigma F).A := by
  simp [sigma]
instance [IsEmpty I] {F : I → PFunctor.{u}} {a : (sigma F).A} : IsEmpty ((sigma F).B a) :=
  isEmptyElim a

-- /-- Sigma of an empty family is the zero functor. -/
-- def sigmaEmpty [IsEmpty I] {F : I → PFunctor.{u}} : sigma F ≃ₗ 0 where
--   toLens := isEmptyElim ⇆ (fun a _ => isEmptyElim a)
--   invLens := isEmptyElim ⇆ (fun a _ => isEmptyElim a)
--   left_inv := by ext a <;> exact isEmptyElim a
--   right_inv := by ext a <;> exact isEmptyElim a

-- /-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself. -/
-- def sigmaUnit {F : PUnit → PFunctor.{u}} : sigma F ≃ₗ (F PUnit.unit).ulift where
--   toLens := (fun ⟨_, a⟩ => ULift.up a) ⇆ (fun _ b => b)
--   invLens := (fun a => ⟨PUnit.unit, ULift.down a⟩) ⇆ (fun _ b => b)
--   left_inv := rfl
--   right_inv := rfl

-- /-- Sigma of an `I`-indexed family, where `I` is unique, is equivalent to the functor itself. -/
-- def sigmaOfUnique [Unique I] {F : I → PFunctor.{u}} : sigma F ≃ₗ (F default).ulift where
--   toLens := (fun ⟨_, a⟩ => (Unique.uniq _ _) ▸ ULift.up a) ⇆
--             (fun ⟨i, a⟩ b => (Unique.uniq _ i) ▸ b)
--   invLens := (fun a => ⟨default, ULift.down a⟩) ⇆ (fun _ b => b)
--   left_inv := by
--     ext ⟨i, a⟩ b <;> simp [sigma, Lens.id, comp]
--     · generalize_proofs h; subst h; simp
--     · generalize_proofs _ h; subst h; simp
--   right_inv := rfl

-- /-- Left distributivity of product over sigma. -/
-- def prodSigmaDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
--     P * sigma F ≃ₗ sigma (fun i => P * F i) where
--   toLens := (fun ⟨pa, ⟨i, fia⟩⟩ => ⟨i, ⟨pa, fia⟩⟩) ⇆
--             (fun _ b => match ULift.down b with
--               | Sum.inl p => Sum.inl p
--               | Sum.inr q => Sum.inr (ULift.up q))
--   invLens := (fun ⟨i, ⟨pa, fia⟩⟩ => ⟨pa, ⟨i, fia⟩⟩) ⇆
--              (fun _ b => match b with
--               | Sum.inl p => ULift.up (Sum.inl p)
--               | Sum.inr q => ULift.up (Sum.inr (ULift.down q)))
--   left_inv := by
--     ext ⟨pa, ⟨i, fia⟩⟩ b
--     · rfl
--     · rcases b with _ | _ <;> rfl
--   right_inv := by
--     ext ⟨i, ⟨pa, fia⟩⟩ b
--     · rfl
--     · rcases b with _ | _ <;> rfl

-- /-- Right distributivity of product over sigma. -/
-- def sigmaProdDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
--     sigma F * P ≃ₗ sigma (fun i => F i * P) where
--   toLens := (fun ⟨⟨i, fia⟩, pa⟩ => ⟨i, ⟨fia, pa⟩⟩) ⇆
--             (fun _ b => match ULift.down b with
--               | Sum.inl p => Sum.inl (ULift.up p)
--               | Sum.inr q => Sum.inr q)
--   invLens := (fun ⟨i, ⟨fia, pa⟩⟩ => ⟨⟨i, fia⟩, pa⟩) ⇆
--              (fun _ b => match b with
--               | Sum.inl p => ULift.up (Sum.inl (ULift.down p))
--               | Sum.inr q => ULift.up (Sum.inr q))
--   left_inv := by
--     ext ⟨⟨i, fia⟩, pa⟩ b
--     · rfl
--     · rcases b with _ | _ <;> rfl
--   right_inv := by
--     ext ⟨i, ⟨fia, pa⟩⟩ b
--     · rfl
--     · rcases b with _ | _ <;> rfl

-- /-- Left distributivity of tensor product over sigma. -/
-- def tensorSigmaDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
--     P ⊗ₚ sigma F ≃ₗ sigma (fun i => P ⊗ₚ F i) where
--   toLens := (fun ⟨pa, ⟨i, fia⟩⟩ => ⟨i, ⟨pa, fia⟩⟩) ⇆
--             (fun _ ⟨pb, fib⟩ => ⟨pb, ULift.up fib⟩)
--   invLens := (fun ⟨i, ⟨pa, fia⟩⟩ => ⟨pa, ⟨i, fia⟩⟩) ⇆
--              (fun _ ⟨pb, fib⟩ => ⟨pb, ULift.down fib⟩)
--   left_inv := rfl
--   right_inv := rfl

-- /-- Right distributivity of tensor product over sigma. -/
-- def sigmaTensorDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
--     sigma F ⊗ₚ P ≃ₗ sigma (fun i => F i ⊗ₚ P) where
--   toLens := (fun ⟨⟨i, fia⟩, pa⟩ => ⟨i, ⟨fia, pa⟩⟩) ⇆
--             (fun _ ⟨fib, pb⟩ => ⟨ULift.up fib, pb⟩)
--   invLens := (fun ⟨i, ⟨fia, pa⟩⟩ => ⟨⟨i, fia⟩, pa⟩) ⇆
--              (fun _ ⟨fib, pb⟩ => ⟨ULift.down fib, pb⟩)
--   left_inv := rfl
--   right_inv := rfl

-- /-- Right distributivity of composition over sigma. -/
-- def sigmaCompDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
--     (sigma F) ◃ P ≃ₗ sigma (fun i => F i ◃ P) where
--   toLens := (fun ⟨⟨i, fia⟩, pf⟩ => ⟨i, ⟨fia, pf⟩⟩) ⇆
--             (fun _ b => match ULift.down b with
--               | Sum.inl p => Sum.inl (ULift.up p)
--               | Sum.inr q => Sum.inr q)
--   invLens := (fun ⟨i, ⟨fia, pf⟩⟩ => ⟨⟨i, fia⟩, pf⟩) ⇆
--              (fun _ b => match b with
--               | Sum.inl p => ULift.up (Sum.inl (ULift.down p))
--               | Sum.inr q => ULift.up (Sum.inr q))
--   left_inv := rfl
--   right_inv := rfl

end Sigma

section Pi

variable {I : Type v}

/-- Pi over a `PUnit`-indexed family is equivalent to the functor itself. -/
def piUnit {P : PFunctor.{u}} : pi (fun (_ : PUnit) => P) ≃ₗ P where
  toLens := (fun f => f PUnit.unit) ⇆ (fun _ pb => ⟨PUnit.unit, pb⟩)
  invLens := (fun pa _ => pa) ⇆ (fun _ spb => spb.2)
  left_inv := rfl
  right_inv := rfl

-- /-- Pi of a family of zero functors over an inhabited type is the zero functor. -/
-- def piZero (F_zero : ∀ i, F i = 0) :
--     pi (F : I → PFunctor.{u}) ≃ₗ 0 where
--   toLens := (fun a => PEmpty.elim
-- (Classical.choice (Function.funext_iff.mp F_zero (Classical.choice Classical.propDecidable))))
-- ⇆ -- Requires some work to construct the PEmpty element
--             (fun _ => PEmpty.elim)
--   invLens := PEmpty.elim ⇆ (fun a => PEmpty.elim a)
--   left_inv := sorry -- Proof depends on constructing the PEmpty term above
--   right_inv := by ext a <;> exact PEmpty.elim a

end Pi

end Lens

-- Do the same for charts?

end Lemmas

namespace Equiv

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}

/-- Convert an equivalence between two polynomial functors `P` and `Q` to a lens. -/
def toLens (e : Equiv P Q) : Lens P Q where
  toFunA := e.equivA
  toFunB := fun a => (e.equivB a).symm

/-- Convert an equivalence between two polynomial functors `P` and `Q` to a chart. -/
def toChart (e : Equiv P Q) : Chart P Q where
  toFunA := e.equivA
  toFunB := fun a => e.equivB a

end Equiv

end PFunctor
