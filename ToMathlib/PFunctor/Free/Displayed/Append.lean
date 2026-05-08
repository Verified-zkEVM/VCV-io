/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.PFunctor.Free.Displayed.Decoration
public import ToMathlib.PFunctor.Free.Path

/-!
# Decoration along `FreeM.append`

Concatenation of node-local metadata along the dependent sequential composition
`FreeM.append`. The decoration of an appended tree is the `Decoration` of the
prefix paired (per canonical prefix path) with the `Decoration` of the suffix.

This file lives below the protocol layer: nothing here mentions `Spec`,
`Transcript`, or any interaction-specific notion. Protocol-flavored append
combinators are thin specializations of these definitions.
-/

@[expose] public section

universe u v w w₂ w₃ w₄

namespace PFunctor
namespace FreeM
namespace Displayed
namespace Decoration

variable {P : PFunctor.{u, v}} {α β : Type w}

/-- Concatenate per-node metadata along `FreeM.append`. -/
def append {Γ : P.A → Type w₂}
    {s₁ : FreeM P α} {s₂ : Path s₁ → FreeM P β}
    (d₁ : Decoration Γ s₁)
    (d₂ : (path₁ : Path s₁) → Decoration Γ (s₂ path₁)) :
    Decoration Γ (FreeM.append s₁ s₂) :=
  match s₁, d₁ with
  | .pure _, _ => d₂ ⟨⟩
  | .roll _ _, ⟨γ, dRest⟩ =>
      ⟨γ, fun b => append (dRest b) (fun path => d₂ ⟨b, path⟩)⟩

@[simp]
theorem append_pure {Γ : P.A → Type w₂} (x : α)
    (d₁ : Decoration Γ (FreeM.pure (P := P) x))
    (s₂ : Path (FreeM.pure (P := P) x) → FreeM P β)
    (d₂ : (path₁ : Path (FreeM.pure (P := P) x)) → Decoration Γ (s₂ path₁)) :
    append d₁ d₂ = d₂ ⟨⟩ :=
  rfl

@[simp]
theorem append_roll {Γ : P.A → Type w₂}
    (a : P.A) (rest : P.B a → FreeM P α)
    (d₁ : Decoration Γ (FreeM.roll a rest))
    (s₂ : Path (FreeM.roll a rest) → FreeM P β)
    (d₂ : (path₁ : Path (FreeM.roll a rest)) → Decoration Γ (s₂ path₁)) :
    append d₁ d₂ =
      ⟨d₁.1, fun b => append (d₁.2 b) (fun path => d₂ ⟨b, path⟩)⟩ :=
  rfl

namespace Over

/-- Concatenate dependent over-decorations along `FreeM.append`, over an
appended base decoration. -/
def append {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    {s₁ : FreeM P α} {s₂ : Path s₁ → FreeM P β}
    {d₁ : Decoration Γ s₁}
    {d₂ : (path₁ : Path s₁) → Decoration Γ (s₂ path₁)}
    (r₁ : Decoration.Over Γ F s₁ d₁)
    (r₂ : (path₁ : Path s₁) → Decoration.Over Γ F (s₂ path₁) (d₂ path₁)) :
    Decoration.Over Γ F (FreeM.append s₁ s₂) (Decoration.append d₁ d₂) :=
  match s₁, d₁, r₁ with
  | .pure _, _, _ => r₂ ⟨⟩
  | .roll _ _, ⟨_, _⟩, ⟨fData, rRest⟩ =>
      ⟨fData, fun b => append (rRest b) (fun path => r₂ ⟨b, path⟩)⟩

@[simp]
theorem append_pure {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    (x : α)
    (d₁ : Decoration Γ (FreeM.pure (P := P) x))
    (s₂ : Path (FreeM.pure (P := P) x) → FreeM P β)
    (d₂ : (path₁ : Path (FreeM.pure (P := P) x)) → Decoration Γ (s₂ path₁))
    (r₁ : Decoration.Over Γ F (FreeM.pure (P := P) x) d₁)
    (r₂ : (path₁ : Path (FreeM.pure (P := P) x)) →
      Decoration.Over Γ F (s₂ path₁) (d₂ path₁)) :
    Over.append (s₁ := FreeM.pure (P := P) x) (s₂ := s₂) (d₁ := d₁) (d₂ := d₂)
      r₁ r₂ = r₂ ⟨⟩ :=
  rfl

@[simp]
theorem append_roll {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    (a : P.A) (rest : P.B a → FreeM P α)
    (d₁ : Decoration Γ (FreeM.roll a rest))
    (s₂ : Path (FreeM.roll a rest) → FreeM P β)
    (d₂ : (path₁ : Path (FreeM.roll a rest)) → Decoration Γ (s₂ path₁))
    (r₁ : Decoration.Over Γ F (FreeM.roll a rest) d₁)
    (r₂ : (path₁ : Path (FreeM.roll a rest)) →
      Decoration.Over Γ F (s₂ path₁) (d₂ path₁)) :
    Over.append (s₁ := FreeM.roll a rest) (s₂ := s₂) (d₁ := d₁) (d₂ := d₂)
      r₁ r₂ =
      ⟨r₁.1, fun b => Over.append (r₁.2 b) (fun path => r₂ ⟨b, path⟩)⟩ :=
  rfl

/-- `Decoration.Over.map` commutes with `Decoration.Over.append`. -/
theorem map_append {Γ : P.A → Type w₂}
    {F : (a : P.A) → Γ a → Type w₃} {G : (a : P.A) → Γ a → Type w₄}
    (η : ∀ a γ, F a γ → G a γ) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (d₁ : Decoration Γ s₁) →
    (d₂ : (path₁ : Path s₁) → Decoration Γ (s₂ path₁)) →
    (r₁ : Decoration.Over Γ F s₁ d₁) →
    (r₂ : (path₁ : Path s₁) → Decoration.Over Γ F (s₂ path₁) (d₂ path₁)) →
    Decoration.Over.map η (FreeM.append s₁ s₂) (Decoration.append d₁ d₂)
        (Decoration.Over.append r₁ r₂) =
      Decoration.Over.append (Decoration.Over.map η s₁ d₁ r₁)
        (fun path₁ => Decoration.Over.map η (s₂ path₁) (d₂ path₁) (r₂ path₁))
  | .pure _, _, _, _, _, _ => rfl
  | .roll a rest, s₂, ⟨γ, dRest⟩, d₂, ⟨fd, rRest⟩, r₂ => by
      simp only [FreeM.append, Decoration.append, Decoration.Over.append,
        Decoration.Over.map, Decoration.Over.mapLocalHom,
        Displayed.Over.FiberLocalHom.toHom_roll]
      congr 1; funext b
      exact map_append η (rest b) (fun path => s₂ ⟨b, path⟩)
        (dRest b) (fun path => d₂ ⟨b, path⟩) (rRest b)
        (fun path => r₂ ⟨b, path⟩)

end Over

/-- `Decoration.map` commutes with `Decoration.append`. -/
theorem map_append {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (d₁ : Decoration Γ s₁) →
    (d₂ : (path₁ : Path s₁) → Decoration Γ (s₂ path₁)) →
    Decoration.map f (FreeM.append s₁ s₂) (Decoration.append d₁ d₂) =
      Decoration.append (Decoration.map f s₁ d₁)
        (fun path₁ => Decoration.map f (s₂ path₁) (d₂ path₁))
  | .pure _, _, _, _ => rfl
  | .roll a rest, s₂, ⟨γ, dRest⟩, d₂ => by
      simp only [FreeM.append, Decoration.append, Decoration.map,
        Decoration.mapLocalHom, Displayed.LocalHom.toHom_roll]
      congr 1; funext b
      exact map_append f (rest b) (fun path => s₂ ⟨b, path⟩)
        (dRest b) (fun path => d₂ ⟨b, path⟩)

end Decoration
end Displayed
end FreeM
end PFunctor
