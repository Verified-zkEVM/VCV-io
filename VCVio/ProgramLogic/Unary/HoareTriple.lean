/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.EvalDist
import Mathlib.Control.Lawful
import ToMathlib.Control.Monad.Relative
import VCVio.OracleComp.EvalDist

/-!
# Hoare triples for `OracleComp` and extensions

-/

universe u v

namespace OracleComp

open OracleComp

open scoped ENNReal

-- Notation: we want to write pre and post-conditions as `{P} e {Q}_⦃ ε ⦄` for a probabilistic
-- program `e`, which means that assuming pre-condition `P`, the program `e` after execution
-- satisfies post-condition `Q` except with probability `ε`.

namespace StateM

-- Below is an experimental implementation of Hoare triples for the state monad
-- We will eventually integrate this with the Hoare triples for `OracleComp`

def PreCondition (σ : Type*) := σ → Prop

abbrev PreCondition.top (σ : Type*) : PreCondition σ := fun _ => True

@[simp]
theorem PreCondition.top_def {σ : Type _} : PreCondition.top σ = fun _ => True := rfl

/-- Pre-conditions are partially ordered by reverse inclusion -/
instance {σ : Type*} : PartialOrder (PreCondition σ) where
  le P₁ P₂ := ∀ s, P₂ s → P₁ s
  le_refl P := by simp
  le_trans P₁ P₂ P₃ hP₁₂ hP₂₃ := by
    intro s hP₂
    exact hP₁₂ s (hP₂₃ s hP₂)
  le_antisymm P₁ P₂ hP₁₂ hP₂₁ := by
    funext s
    aesop

def PostCondition (σ α : Type*) := σ → α → σ → Prop

/-- Post-conditions are partially ordered by reverse inclusion -/
instance {σ α : Type*} : PartialOrder (PostCondition σ α) where
  le Q₁ Q₂ := ∀ s a s', Q₂ s a s' → Q₁ s a s'
  le_refl Q := by simp
  le_trans Q₁ Q₂ Q₃ hQ₁₂ hQ₂₃ := by
    intro s a s' hQ₂
    exact hQ₁₂ s a s' (hQ₂₃ s a s' hQ₂)
  le_antisymm Q₁ Q₂ hQ₁₂ hQ₂₁ := by
    funext s a s'
    aesop

variable {σ α β : Type*}

def HoareState (P : PreCondition σ) (α : Type*) (Q : PostCondition σ α) :=
  ∀ s : {s : σ // P s}, {result : α × σ // Q s result.1 result.2}

namespace HoareState

def pure (x : α) : HoareState (PreCondition.top σ) α (fun s a s' => s = s' ∧ a = x)
  | ⟨s, h⟩ => ⟨(x, s), by simp⟩

def bind {P₁ : PreCondition σ} {Q₁ : PostCondition σ α}
    {P₂ : α → PreCondition σ} {Q₂ : α → PostCondition σ β}
    (m : HoareState P₁ α Q₁) (f : ∀ x, HoareState (P₂ x) β (Q₂ x)) :
      HoareState (fun s₁ => P₁ s₁ ∧ ∀ x s₂, Q₁ s₁ x s₂ → P₂ x s₂) β
        (fun s₁ y s₃ => ∃ x s₂, Q₁ s₁ x s₂ ∧ Q₂ x s₂ y s₃)
  | ⟨s₁, h₁⟩ => match m ⟨s₁, h₁.left⟩ with
    | ⟨(x, s₂), h₂⟩ =>
      let ⟨⟨y, s₃⟩, h₃⟩ := f x ⟨s₂, h₁.right x s₂ h₂⟩
      ⟨⟨y, s₃⟩, ⟨x, s₂, h₂, h₃⟩⟩

notation:50 m₁ " >>=ₕ " m₂ => bind m₁ m₂

def get : HoareState (PreCondition.top σ) σ (fun s x s' => s = s' ∧ x = s)
  | ⟨s, h⟩ => ⟨(s, s), by simp⟩

def set (s : σ) : HoareState (PreCondition.top σ) PUnit (fun _ _ s' => s = s')
  | ⟨_, _⟩ => ⟨(PUnit.unit, s), rfl⟩

-- What kind of monadic structure does `HoareState` have?

end HoareState

def HoareTriple {σ α : Type _} (P : PreCondition σ) (comp : StateM σ α) (Q : PostCondition σ α) :
    Prop :=
  ∀ s : σ, P s → Q s (comp s).1 (comp s).2

scoped notation "⦃" P "⦄" comp " ⦃" Q "⦄" => HoareTriple P comp Q

variable {σ α β : Type _}

namespace HoareTriple

@[simp]
theorem pure_rule (x : α) :
    HoareTriple (PreCondition.top σ) (pure x) (fun s a s' => s = s' ∧ a = x) := by
  intro s h; exact ⟨rfl, rfl⟩

theorem pure_rule_forward {P : PreCondition σ} (x : α) :
    HoareTriple P (pure x) (fun s a s' => s = s' ∧ a = x ∧ P s) := by
  intro s h
  exact ⟨rfl, rfl, h⟩

theorem pure_rule_backward {Q : PostCondition σ α} (x : α) :
    HoareTriple (fun s => Q s x s) (pure x) Q := by
  intro s h
  exact h

theorem bind_rule {P₁ : PreCondition σ} {Q₁ : PostCondition σ α}
    {P₂ : α → PreCondition σ} {Q₂ : α → PostCondition σ β}
    {comp₁ : StateM σ α} {comp₂ : α → StateM σ β}
    (h₁ : HoareTriple P₁ comp₁ Q₁) (h₂ : ∀ x, HoareTriple (P₂ x) (comp₂ x) (Q₂ x)) :
    HoareTriple (fun s => P₁ s ∧ ∀ x s', Q₁ s x s' → P₂ x s')
                (comp₁ >>= comp₂)
                (fun s y s'' => ∃ x s', Q₁ s x s' ∧ Q₂ x s' y s'') := by
  intro s ⟨h_p, h_imp⟩
  rcases h : comp₁ s with ⟨x, s'⟩
  have hQ₁ := h₁ s h_p
  rw [h] at hQ₁
  refine ⟨x, s', ⟨?_, ?_⟩⟩
  · exact hQ₁
  · simp [bind, StateT.bind, h]
    have hQ₂ := h₂ x s' (h_imp x s' hQ₁)
    exact hQ₂

-- theorem seq_rule {P P' : PreCondition σ}
--     {Q : PostCondition σ α} {R : PostCondition σ β}
--     {comp₁ : StateM σ α} {comp₂ : StateM σ β}
--     (h₁ : HoareTriple P comp₁ Q) (h₂ : HoareTriple P' comp₂ R) :
--     HoareTriple (fun s => P s ∧ ∀ x s', Q s x s' → P' s')
--               (comp₁ >>= fun _ => comp₂) R := by
--   sorry

theorem weaken_rule {P : PreCondition σ} {Q : PostCondition σ α}
    {comp : StateM σ α} (h : HoareTriple P comp Q) (P' : PreCondition σ)
    (h_imp : ∀ s, P' s → P s) :
      HoareTriple P' comp Q := by
  intro s h_p'
  exact h s (h_imp s h_p')

theorem strengthen_rule {P : PreCondition σ} {Q : PostCondition σ α}
    {comp : StateM σ α} (h : HoareTriple P comp Q) (Q' : PostCondition σ α)
    (h_imp : ∀ s x s', Q s x s' → Q' s x s') :
      HoareTriple P comp Q' := by
  intro s h_p
  exact h_imp s (comp s).1 (comp s).2 (h s h_p)

/-- Consequence rule: combination of weaken and strengthen

In this form, it's meant to be applied forward, not backward -/
theorem conseq_rule {P : PreCondition σ} {Q : PostCondition σ α}
    {comp : StateM σ α} (h : HoareTriple P comp Q) (P' : PreCondition σ) (Q' : PostCondition σ α)
    (hP : ∀ s, P' s → P s) (hQ : ∀ s x s', Q s x s' → Q' s x s') :
      HoareTriple P' comp Q' := by
  intro s h_p'
  exact hQ s (comp s).1 (comp s).2 (h s (hP s h_p'))

theorem frame_rule {P : PreCondition σ} {Q : PostCondition σ α}
    {comp : StateM σ α} (h : HoareTriple P comp Q) (R : PreCondition σ) :
    HoareTriple (fun s => P s ∧ R s) comp (fun s x s' => Q s x s' ∧ R s) := by
  intro s ⟨h_p, h_r⟩
  exact ⟨h s h_p, h_r⟩

@[simp]
theorem frame_true_pre {P : PreCondition σ} {Q : PostCondition σ α}
    {comp : StateM σ α} (h : HoareTriple P comp Q) :
      HoareTriple (fun s => P s ∧ True) comp Q := by
  intro s ⟨h_p, _⟩
  exact h s h_p

@[simp]
theorem get_rule_basic :
    HoareTriple (fun _ => True) (get : StateM σ σ) (fun s x s' => s = x ∧ s = s') := by
  intro s _
  exact ⟨rfl, rfl⟩

@[simp]
theorem set_rule_basic (s' : σ) :
    HoareTriple (fun _ => True) (set s' : StateM σ Unit) (fun _ _ s'' => s'' = s') := by
  intro s _
  rfl

/-- Strongest postcondition for get: After get executes, we know the value read equals the state,
    and the state hasn't changed -/
theorem get_rule_forward (P : PreCondition σ) :
    HoareTriple P (get : StateM σ σ) (fun s x s' => P s ∧ s = x ∧ s = s') := by
  have h := get_rule_basic (σ := σ)
  have h' := frame_rule h P
  simp_all
  refine strengthen_rule h' _ ?_
  aesop

theorem set_rule_forward (P : PreCondition σ) (s' : σ) :
    HoareTriple P (set s' : StateM σ Unit) (fun s _ s'' => P s ∧ s'' = s') := by
  have h := set_rule_basic s'
  have h' := frame_rule h P
  simp_all
  refine strengthen_rule h' _ ?_
  aesop

/-- Weakest precondition for get: To ensure Q holds after get,
Q must hold for the state value we read -/
theorem get_rule_backward (Q : σ → σ → σ → Prop) :
    HoareTriple (fun s => Q s s s) get Q := by
  intro s h
  apply h

/-- Weakest precondition for set: To ensure Q holds after setting state to s',
    Q must hold for that new state -/
theorem set_rule_backward (s' : σ) (Q : σ → Unit → σ → Prop) :
    HoareTriple (fun s => Q s () s') (set s') Q := by
  intro s h
  exact h

theorem conj_rule {P₁ P₂ : PreCondition σ} {Q₁ Q₂ : PostCondition σ α}
    {comp : StateM σ α}
    (h₁ : HoareTriple P₁ comp Q₁) (h₂ : HoareTriple P₂ comp Q₂) :
    HoareTriple (fun s => P₁ s ∧ P₂ s) comp (fun s x s' => Q₁ s x s' ∧ Q₂ s x s') := by
  intro s ⟨h_p₁, h_p₂⟩
  exact ⟨h₁ s h_p₁, h₂ s h_p₂⟩

end HoareTriple

class WeakestPrecondition (comp : StateM σ α) (Q : PostCondition σ α) where
  P : PreCondition σ
  hP : HoareTriple P comp Q
  hWeak : ∀ P', HoareTriple P' comp Q → P ≤ P'

class StrongestPostcondition (P : PreCondition σ) (comp : StateM σ α) where
  Q : PostCondition σ α
  hQ : HoareTriple P comp Q
  hStrong : ∀ Q', HoareTriple P comp Q' → Q' ≤ Q

instance {comp : StateM σ α} {Q : PostCondition σ α} :
    Subsingleton (WeakestPrecondition comp Q) := by
  constructor
  intro ⟨P₁, hP₁, hP₁_imp⟩ ⟨P₂, hP₂, hP₂_imp⟩
  congr
  exact le_antisymm (hP₁_imp P₂ hP₂) (hP₂_imp P₁ hP₁)

instance {P : PreCondition σ} {comp : StateM σ α} :
    Subsingleton (StrongestPostcondition P comp) := by
  constructor
  intro ⟨Q₁, hQ₁, hQ₁_imp⟩ ⟨Q₂, hQ₂, hQ₂_imp⟩
  congr
  exact le_antisymm (hQ₂_imp Q₁ hQ₁) (hQ₁_imp Q₂ hQ₂)

section pure

instance {Q : PostCondition σ α} {x : α} :
    Inhabited (WeakestPrecondition (pure x : StateM σ α) Q) where
  default := ⟨fun s => Q s x s, HoareTriple.pure_rule_backward x, fun _ hP' => hP'⟩

instance {Q : PostCondition σ σ} {x : σ} : WeakestPrecondition (pure x : StateM σ σ) Q := default

instance {P : PreCondition σ} {x : α} :
    Inhabited (StrongestPostcondition P (pure x : StateM σ α)) where
  default := ⟨fun s a s' => s = s' ∧ a = x ∧ P s, HoareTriple.pure_rule_forward x,
    fun y hP hy => by aesop⟩

instance {P : PreCondition σ} {x : α} : StrongestPostcondition P (pure x : StateM σ α) := default

end pure

section bind

-- instance {Q : PostCondition σ β} {comp₁ : StateM σ α} {comp₂ : α → StateM σ β}
--     [∀ x, Inhabited (WeakestPrecondition (comp₂ x) Q)]
--     [Inhabited (WeakestPrecondition comp₁ Q₁)]
--       Inhabited (WeakestPrecondition (comp₁ >>= comp₂) Q) where
--   default := ⟨fun s => ∃ x s', Q₁ s x s' ∧ P₂ x s', HoareTriple.bind_rule
-- (default : WeakestPrecondition comp₁ Q₁) (fun x => default :
-- StrongestPostcondition (fun s => Q₁ s ∧ P₂ s) (comp₂ x)),
--     fun P' hP' s h_p => by aesop⟩

end bind

section get

instance {Q : PostCondition σ σ} : Inhabited (WeakestPrecondition (get : StateM σ σ) Q) where
  default := ⟨fun s => Q s s s, HoareTriple.get_rule_backward Q, fun _ hP' => hP'⟩

instance {Q : PostCondition σ σ} : WeakestPrecondition (get : StateM σ σ) Q := default

end get

section set

instance {P : PreCondition σ} {s' : σ} :
    Inhabited (StrongestPostcondition P (set s' : StateM σ Unit)) where
  default := ⟨fun s _ s'' => P s ∧ s'' = s', HoareTriple.set_rule_forward P s',
    fun Q' hQ' _ => by aesop⟩

instance {P : PreCondition σ} {s' : σ} :
  StrongestPostcondition P (set s' : StateM σ Unit) := default

end set

end StateM

section Example

open StateM

-- Following the exposition "The Hoare State Monad" by Wouter Swierstra

inductive Tree' (a : Type*) where
  | leaf : a → Tree' a
  | node : Tree' a → Tree' a → Tree' a

variable {α : Type*}

def relabel (t : Tree' α) (n : ℕ) : Tree' ℕ × ℕ := match t with
  | .leaf _ => (.leaf n, n + 1)
  | .node l r =>
    let (l', n') := relabel l n
    let (r', n'') := relabel r n'
    (.node l' r', n'')

def relabelM : (t : Tree' α) → StateM ℕ (Tree' ℕ)
  | .leaf _ => do
    let n ← get
    set (n + 1)
    return .leaf n
  | .node l r => do
    let l' ← relabelM l
    let r' ← relabelM r
    return .node l' r'

def flatten : (t : Tree' α) → List α
  | .leaf a => [a]
  | .node l r => flatten l ++ flatten r

-- theorem flatten_relabel {t : Tree' α} {n : ℕ} : List.Nodup (flatten ((relabelM t).run n).1) := by
--   sorry

def size : Tree' α → ℕ
  | .leaf _ => 1
  | .node l r => size l + size r

def Nat.seq : ℕ → ℕ → List ℕ
  | _, 0 => []
  | n, m + 1 => n :: Nat.seq (n + 1) m

end Example

end OracleComp
