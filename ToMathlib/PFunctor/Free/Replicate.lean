/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.PFunctor.Free.Displayed.Append
public import ToMathlib.PFunctor.Free.Path

/-!
# `n`-fold append of free polynomial trees

`FreeM.replicate a s n` is the non-dependent `n`-fold append of `s` with a
constant continuation, terminating with the leaf value `a`. Together with
the displayed-layer `Decoration.replicate` and `Decoration.Over.replicate`,
this captures uniform iteration of a `FreeM` tree without referring to the
protocol layer.
-/

@[expose] public section

universe u v w w₂ w₃ w₄

namespace PFunctor
namespace FreeM

variable {P : PFunctor.{u, v}} {α : Type w}

/-- Non-dependent `n`-fold append of a free tree with a constant continuation. -/
def replicate (a : α) (s : FreeM P α) : (n : Nat) → FreeM P α
  | 0 => FreeM.pure a
  | n + 1 => s.append (fun _ => replicate a s n)

@[simp, grind =]
theorem replicate_zero (a : α) (s : FreeM P α) :
    replicate a s 0 = FreeM.pure a := rfl

@[simp]
theorem replicate_succ (a : α) (s : FreeM P α) (n : Nat) :
    replicate a s (n + 1) = s.append (fun _ => replicate a s n) := rfl

namespace Displayed
namespace Decoration

/-- Replicate a decoration along `FreeM.replicate`. -/
def replicate {Γ : P.A → Type w₂} (a : α) {s : FreeM P α}
    (d : Decoration Γ s) : (n : Nat) → Decoration Γ (FreeM.replicate a s n)
  | 0 => ⟨⟩
  | n + 1 => Decoration.append d (fun _ => Decoration.replicate a d n)

@[simp]
theorem replicate_zero {Γ : P.A → Type w₂} (a : α) {s : FreeM P α}
    (d : Decoration Γ s) :
    Decoration.replicate a d 0 =
      (⟨⟩ : Decoration Γ (FreeM.replicate a s 0)) :=
  rfl

@[simp]
theorem replicate_succ {Γ : P.A → Type w₂} (a : α) {s : FreeM P α}
    (d : Decoration Γ s) (n : Nat) :
    Decoration.replicate a d (n + 1) =
      Decoration.append d (fun _ => Decoration.replicate a d n) :=
  rfl

namespace Over

/-- Replicate a dependent decoration along replicated base decorations. -/
def replicate {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    (a : α) {s : FreeM P α} {d : Decoration Γ s}
    (r : Decoration.Over Γ F s d) :
    (n : Nat) → Decoration.Over Γ F (FreeM.replicate a s n) (d.replicate a n)
  | 0 => ⟨⟩
  | n + 1 => Decoration.Over.append r (fun _ => Over.replicate a r n)

@[simp]
theorem replicate_zero {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    (a : α) {s : FreeM P α} {d : Decoration Γ s}
    (r : Decoration.Over Γ F s d) :
    Decoration.Over.replicate a r 0 =
      (⟨⟩ : Decoration.Over Γ F (FreeM.replicate a s 0) (d.replicate a 0)) :=
  rfl

@[simp]
theorem replicate_succ {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    (a : α) {s : FreeM P α} {d : Decoration Γ s}
    (r : Decoration.Over Γ F s d) (n : Nat) :
    Decoration.Over.replicate a r (n + 1) =
      Decoration.Over.append r (fun _ => Over.replicate a r n) :=
  rfl

/-- `Decoration.Over.map` commutes with `Over.replicate`. -/
theorem map_replicate {Γ : P.A → Type w₂}
    {F : (a : P.A) → Γ a → Type w₃} {G : (a : P.A) → Γ a → Type w₄}
    (η : ∀ a γ, F a γ → G a γ) (a : α) {s : FreeM P α} {d : Decoration Γ s}
    (r : Decoration.Over Γ F s d) (n : Nat) :
    Decoration.Over.map η (FreeM.replicate a s n) (d.replicate a n)
        (Decoration.Over.replicate a r n) =
      Decoration.Over.replicate a (Decoration.Over.map η s d r) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Decoration.Over.map η (s.append _) _
        (Decoration.Over.append r (fun _ => Over.replicate a r n)) = _
    rw [Decoration.Over.map_append η s _ d _ r]
    refine congrArg (Decoration.Over.append (Decoration.Over.map η s d r)) ?_
    funext _
    exact ih

end Over

/-- `Decoration.map` commutes with `Decoration.replicate`. -/
theorem map_replicate {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a) (a : α) {s : FreeM P α} (d : Decoration Γ s) :
    (n : Nat) →
    Decoration.map f (FreeM.replicate a s n) (d.replicate a n) =
      (Decoration.map f s d).replicate a n
  | 0 => rfl
  | n + 1 => by
      change Decoration.map f (s.append _) (d.append fun _ => d.replicate a n) = _
      rw [Decoration.map_append f s _ d]
      congr 1; funext _
      exact map_replicate f a d n

end Decoration
end Displayed
end FreeM
end PFunctor
