/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.PFunctor.Basic

/-!
# More properties about lenses between polynomial functors
-/

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆

section find_home

variable {α : Sort u} {β : α → Sort v} {γ : α → Sort v}

lemma heq_forall_iff (h : ∀ a, β a = γ a) {f : (a : α) → β a} {g : (a : α) → γ a} :
    f ≍ g ↔ ∀ a, (f a) ≍ (g a) := by
  have := funext h
  subst this
  aesop

end find_home

namespace PFunctor

namespace Lens

@[ext (iff := false)]
theorem ext {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (l₁ l₂ : Lens P Q)
    (h₁ : ∀ a, l₁.toFunA a = l₂.toFunA a) (h₂ : ∀ a, l₁.toFunB a = (h₁ a) ▸ l₂.toFunB a) :
    l₁ = l₂ := by
  rcases l₁ with ⟨toFunA₁, _⟩
  rcases l₂ with ⟨toFunA₂, _⟩
  have h : toFunA₁ = toFunA₂ := funext h₁
  subst h
  simp_all
  exact funext h₂

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
  left_inv : comp invLens toLens = Lens.id P := by simp
  right_inv : comp toLens invLens = Lens.id Q := by simp

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
def sumPair {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB₃}}
    (l₁ : Lens P R) (l₂ : Lens Q R) :
    Lens.{max uA₁ uA₂, uB, uA₃, uB₃} (P + Q) R :=
  (Sum.elim l₁.toFunA l₂.toFunA) ⇆
    (fun a d => match a with
      | Sum.inl pa => l₁.toFunB pa d
      | Sum.inr qa => l₂.toFunB qa d)

/-- Parallel application of lenses for coproduct `l₁ ⊎ l₂ : P + Q → R + W` -/
def sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}} {R : PFunctor.{uA₃, uB₃}}
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

/-- Apply lenses to both sides of a tensor / parallel product: `l₁ ⊗ₗ l₂ : (P ⊗ Q ⇆ R ⊗ W)` -/
def tensorMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (l₁ : Lens P R) (l₂ : Lens Q W) :
    Lens.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P ⊗ Q) (R ⊗ W) :=
  (fun ⟨pa, qa⟩ => (l₁.toFunA pa, l₂.toFunA qa)) ⇆
    (fun ⟨_pa, qa⟩ ⟨rb, wb⟩ => (l₁.toFunB _pa rb, l₂.toFunB qa wb))

/-- Lens to introduce `X` on the right: `P → P ◃ X` -/
def tildeR {P : PFunctor.{uA, uB}} : Lens P (P ◃ X) :=
  (fun a => ⟨a, fun _ => PUnit.unit⟩) ⇆ (fun _a => fun ⟨b, _⟩ => b)

/-- Lens to introduce `X` on the left: `P → X ◃ P` -/
def tildeL {P : PFunctor.{uA, uB}} : Lens P (X ◃ P) :=
  (fun a => ⟨PUnit.unit, fun _ => a⟩) ⇆ (fun _a => fun ⟨_, b⟩ => b)

/-- Lens from `P ◃ X` to `P` -/
def invTildeR {P : PFunctor.{uA, uB}} : Lens (P ◃ X) P :=
  (fun a => a.1) ⇆ (fun _ b => ⟨b, PUnit.unit⟩)

/-- Lens from `X ◃ P` to `P` -/
def invTildeL {P : PFunctor.{uA, uB}} : Lens (X ◃ P) P :=
  (fun ⟨_, f⟩ => f PUnit.unit) ⇆ (fun _ b => ⟨PUnit.unit, b⟩)

@[inherit_doc] infixl:75 " ◃ₗ " => compMap
@[inherit_doc] infixl:75 " ×ₗ " => prodMap
@[inherit_doc] infixl:75 " ⊎ₗ " => sumMap
@[inherit_doc] infixl:75 " ⊗ₗ " => tensorMap
notation "[" l₁ "," l₂ "]ₗ" => sumPair l₁ l₂
notation "⟨" l₁ "," l₂ "⟩ₗ" => prodPair l₁ l₂

/-- The type of lenses from a polynomial functor `P` to `X` -/
def enclose (P : PFunctor.{uA, uB}) : Type max uA uA₁ uB uB₁ :=
  Lens P X.{uA₁, uB₁}

/-- Helper lens for `speedup` -/
def fixState {S : Type u} : Lens (selfMonomial S) (selfMonomial S ◃ selfMonomial S) :=
  (fun s₀ => ⟨s₀, fun s₁ => s₁⟩) ⇆ (fun _s₀ => fun ⟨_s₁, s₂⟩ => s₂)

/-- The `speedup` lens operation: `Lens (S y^S) P → Lens (S y^S) (P ◃ P)` -/
def speedup {S : Type u} {P : PFunctor.{uA, uB}} (l : Lens (selfMonomial S) P) :
    Lens (selfMonomial S) (P ◃ P) :=
  (l ◃ₗ l) ∘ₗ fixState

section Coprod

-- Note the universe levels for `uB` in order to apply coproduct / sum
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
  {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}} {X : PFunctor.{uA₅, uB₅}}

@[simp]
theorem sumMap_comp_inl (l₁ : Lens P R) (l₂ : Lens Q W) :
    ((l₁ ⊎ₗ l₂) ∘ₗ Lens.inl) = (Lens.inl ∘ₗ l₁) := rfl

@[simp]
theorem sumMap_comp_inr (l₁ : Lens P R) (l₂ : Lens Q W) :
    ((l₁ ⊎ₗ l₂) ∘ₗ Lens.inr) = (Lens.inr ∘ₗ l₂) := rfl

theorem sumPair_comp_sumMap (l₁ : Lens P R) (l₂ : Lens Q W)
    (f : Lens R X) (g : Lens W X) :
  Lens.sumPair f g ∘ₗ (l₁ ⊎ₗ l₂) = Lens.sumPair (f ∘ₗ l₁) (g ∘ₗ l₂) := by
  ext a <;> rcases a with a | a <;> rfl

@[simp]
theorem sumPair_comp_inl (f : Lens P R) (g : Lens Q R) :
    Lens.sumPair f g ∘ₗ Lens.inl = f := rfl

@[simp]
theorem sumPair_comp_inr (f : Lens P R) (g : Lens Q R) :
    Lens.sumPair f g ∘ₗ Lens.inr = g := rfl

theorem comp_inl_inr (h : Lens.{max uA₁ uA₂, uB₁, uA₃, uB₃} (P + Q) R) :
    Lens.sumPair (h ∘ₗ Lens.inl) (h ∘ₗ Lens.inr) = h := by
  ext a <;> rcases a <;> rfl

@[simp]
theorem sumMap_id :
    Lens.sumMap (Lens.id P) (Lens.id Q) = Lens.id.{max uA₁ uA₂, uB₁} (P + Q) := by
  ext a <;> rcases a <;> rfl

@[simp]
theorem sumPair_inl_inr :
    Lens.sumPair Lens.inl Lens.inr = Lens.id.{max uA₁ uA₂, uB₁} (P + Q) := by
  ext a <;> rcases a <;> rfl

namespace Equiv

/-- Commutativity of coproduct -/
def sumComm (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    Lens.Equiv.{max uA₁ uA₂, uB, max uA₁ uA₂, uB} (P + Q) (Q + P) where
  toLens := Lens.sumPair Lens.inr Lens.inl
  invLens := Lens.sumPair Lens.inr Lens.inl
  left_inv := by
    ext a <;> rcases a with a | a <;> rfl
  right_inv := by
    ext a <;> rcases a with a | a <;> rfl

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}

@[simp]
theorem sumComm_symm :
    (sumComm P Q).symm = sumComm Q P := rfl

/-- Associativity of coproduct -/
def sumAssoc :
    Lens.Equiv.{max uA₁ uA₂ uA₃, uB, max uA₁ uA₂ uA₃, uB} ((P + Q) + R) (P + (Q + R)) where
  toLens := -- Maps (P + Q) + R to P + (Q + R)
    Lens.sumPair
      (Lens.sumPair -- Maps P + Q to P + (Q + R)
        (Lens.inl) -- Maps P to P + (Q + R) via Sum.inl
        (Lens.inr ∘ₗ Lens.inl) -- Maps Q to P + (Q + R) via Sum.inr ∘ Sum.inl
      )
      (Lens.inr ∘ₗ Lens.inr) -- Maps R to P + (Q + R) via Sum.inr ∘ Sum.inr
  invLens := -- Maps P + (Q + R) to (P + Q) + R
    Lens.sumPair
      (Lens.inl ∘ₗ Lens.inl) -- Maps P to (P + Q) + R via Sum.inl ∘ Sum.inl
      (Lens.sumPair -- Maps Q + R to (P + Q) + R
        (Lens.inl ∘ₗ Lens.inr) -- Maps Q to (P + Q) + R via Sum.inl ∘ Sum.inr
        (Lens.inr) -- Maps R to (P + Q) + R via Sum.inr
      )
  left_inv := by
    ext a <;> rcases a with (a | a) |a <;> rfl
  right_inv := by
    ext a <;> rcases a with a | a |a <;> rfl

/-- Coproduct with `0` is identity (right) -/
def sumZero :
    Lens.Equiv.{max uA uA₁, uB, uA₁, uB} (P + (0 : PFunctor.{uA, uB})) P where
  toLens := Lens.sumPair (Lens.id P) Lens.initial
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
  toLens := Lens.sumPair Lens.initial (Lens.id P)
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
              (fun _ d => (_root_.Equiv.sumAssoc _ _ _).invFun d)
  invLens := (_root_.Equiv.prodAssoc P.A Q.A R.A).invFun ⇆
               (fun _ d => _root_.Equiv.sumAssoc _ _ _ d)
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
def sumProdDistrib :
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

/-- Composition with `X` is identity (right) -/
def compX : P ◃ X ≃ₗ P where
  toLens := invTildeR
  invLens := tildeR
  left_inv := rfl
  right_inv := rfl

/-- Composition with `X` is identity (left) -/
def XComp : X ◃ P ≃ₗ P where
  toLens := invTildeL
  invLens := tildeL
  left_inv := rfl
  right_inv := rfl

/-- Distributivity of composition over coproduct on the right -/
def sumCompDistrib {R : PFunctor.{uA₃, uB₂}} :
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
theorem tensorMap_id : (Lens.id P) ⊗ₗ (Lens.id Q) = Lens.id (P ⊗ Q) :=
  rfl

theorem tensorMap_comp
    {P' : PFunctor.{uA₄, uB₄}} {Q' : PFunctor.{uA₅, uB₅}} {R' : PFunctor.{uA₆, uB₆}}
    (l₁ : Lens P P') (l₂ : Lens Q Q') (l₁' : Lens P' R) (l₂' : Lens Q' R') :
    (l₁' ∘ₗ l₁) ⊗ₗ (l₂' ∘ₗ l₂) = (l₁' ⊗ₗ l₂') ∘ₗ (l₁ ⊗ₗ l₂) := rfl

namespace Equiv

/-- Commutativity of tensor product -/
def tensorComm (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) : P ⊗ Q ≃ₗ Q ⊗ P where
  toLens := Prod.swap ⇆ (fun _ => Prod.swap)
  invLens := Prod.swap ⇆ (fun _ => Prod.swap)
  left_inv := rfl
  right_inv := rfl

/-- Associativity of tensor product -/
def tensorAssoc : (P ⊗ Q) ⊗ R ≃ₗ P ⊗ (Q ⊗ R) where
  toLens := (_root_.Equiv.prodAssoc _ _ _).toFun ⇆
            (fun _ => (_root_.Equiv.prodAssoc _ _ _).invFun)
  invLens := (_root_.Equiv.prodAssoc _ _ _).invFun ⇆
            (fun _ => (_root_.Equiv.prodAssoc _ _ _).toFun)
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `X` is identity (right) -/
def tensorX : P ⊗ X ≃ₗ P where
  toLens := Prod.fst ⇆ (fun _ b => (b, PUnit.unit))
  invLens := (fun p => (p, PUnit.unit)) ⇆ (fun _ bp => bp.1)
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `X` is identity (left) -/
def xTensor : X ⊗ P ≃ₗ P where
  toLens := Prod.snd ⇆ (fun _ b => (PUnit.unit, b))
  invLens := (fun p => (PUnit.unit, p)) ⇆ (fun _ bp => bp.2)
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `0` is zero (left) -/
def zeroTensor : 0 ⊗ P ≃ₗ 0 where
  toLens := (fun a => PEmpty.elim a.1) ⇆ (fun _ b => PEmpty.elim b)
  invLens := PEmpty.elim ⇆ (fun a _ => PEmpty.elim a)
  left_inv := by
    ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by
    ext a <;> exact PEmpty.elim a

/-- Tensor product with `0` is zero (right) -/
def tensorZero : P ⊗ 0 ≃ₗ 0 where
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
      (P ⊗ (Q + R : PFunctor.{max uA₂ uA₃, uB₂})) ((P ⊗ Q) + (P ⊗ R)) where
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
def sumTensorDistrib :
    (Q + R : PFunctor.{max uA₂ uA₃, uB₂}) ⊗ P
      ≃ₗ ((Q ⊗ P) + (R ⊗ P) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
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
--     P ⊗ sigma F ≃ₗ sigma (fun i => P ⊗ F i) where
--   toLens := (fun ⟨pa, ⟨i, fia⟩⟩ => ⟨i, ⟨pa, fia⟩⟩) ⇆
--             (fun _ ⟨pb, fib⟩ => ⟨pb, ULift.up fib⟩)
--   invLens := (fun ⟨i, ⟨pa, fia⟩⟩ => ⟨pa, ⟨i, fia⟩⟩) ⇆
--              (fun _ ⟨pb, fib⟩ => ⟨pb, ULift.down fib⟩)
--   left_inv := rfl
--   right_inv := rfl

-- /-- Right distributivity of tensor product over sigma. -/
-- def sigmaTensorDistrib {P : PFunctor.{u}} {I : Type u} {F : I → PFunctor.{u}} :
--     sigma F ⊗ P ≃ₗ sigma (fun i => F i ⊗ P) where
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

namespace Equiv

/-- ULift equivalence for lenses -/
def ulift {P : PFunctor.{uA, uB}} : P.ulift ≃ₗ P where
  toLens := (fun a => ULift.down a) ⇆ (fun _ b => ULift.up b)
  invLens := (fun a => ULift.up a) ⇆ (fun _ b => ULift.down b)
  left_inv := rfl
  right_inv := rfl

end Equiv

end Lens

namespace Equiv

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}

/-- Convert an equivalence between two polynomial functors `P` and `Q` to a lens. -/
def toLensEquiv (e : P ≃ₚ Q) : P ≃ₗ Q where
  toLens := e.equivA ⇆ (fun a => (e.equivB a).symm)
  invLens := e.symm.equivA ⇆ (fun a => (e.symm.equivB a).symm)
  left_inv := by
    simp only [Lens.comp, Lens.id]
    ext a b <;> simp [Equiv.symm]; sorry
  right_inv := by sorry

end Equiv

end PFunctor
