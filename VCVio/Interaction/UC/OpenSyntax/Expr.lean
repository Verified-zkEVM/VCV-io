/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.OpenSyntax.Raw
import VCVio.Interaction.UC.OpenSyntax.Interp

/-!
# Quotiented free model of open composition

This module defines `Expr`, the initial (quotiented) free model of
`OpenTheory`.

`Expr Atom Δ` is the quotient of the raw syntax tree `Raw Atom Δ` by the
equivalence relation `Raw.Equiv`, which identifies raw expressions that
should be equal according to the `OpenTheory` equations (functoriality of
`map`, naturality of `par`, `wire`, and `plug`).

The quotient construction yields a lawful `OpenTheory` instance by
construction: each law holds because it is a constructor of `Raw.Equiv`.

## Main definitions

* `Expr`: quotient of `Raw` by `Raw.Equiv`.
* `Expr.mk`: canonical projection from `Raw` to `Expr`.
* `Expr.map`, `Expr.par`, `Expr.wire`, `Expr.plug`: lifted operations.
* `Expr.interpret`: interpretation into any lawful `OpenTheory`, lifted from
  `Raw.interpret`.
* `Expr.theory`: the free lawful `OpenTheory` over `Atom`.
* `Expr.toInterp`: embedding into the tagless-final `Interp` model.
-/

universe u

namespace Interaction
namespace UC
namespace OpenSyntax

/--
`Expr Atom Δ` is the free open-system expression of boundary `Δ`, generated
by primitive atoms `Atom`.

This is the quotient of `Raw Atom Δ` by the `OpenTheory` equations. Unlike the
raw syntax tree, `Expr` satisfies `map_id`, `map_comp`, and the naturality
laws, so it forms a lawful `OpenTheory`.

For pattern matching on the underlying syntax, project to `Raw` via
`Expr.liftOn` or work with `Raw` directly.
-/
def Expr (Atom : PortBoundary → Type u) (Δ : PortBoundary) : Type (u + 1) :=
  Quotient (Raw.setoid Atom Δ)

namespace Expr

/--
Project a raw expression into the quotiented `Expr`.
-/
def mk {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (e : Raw Atom Δ) : Expr Atom Δ :=
  Quotient.mk _ e

/--
Inject a primitive open component.
-/
def atom {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (a : Atom Δ) : Expr Atom Δ :=
  mk (.atom a)

/--
Adapt the exposed boundary along a structural morphism.
-/
def map {Atom : PortBoundary → Type u} {Δ₁ Δ₂ : PortBoundary}
    (f : PortBoundary.Hom Δ₁ Δ₂)
    (e : Expr Atom Δ₁) : Expr Atom Δ₂ :=
  Quotient.liftOn e (fun r => mk (.map f r))
    (fun _ _ h => Quotient.sound (Raw.Equiv.congr_map h))

/--
Place two open systems side by side.
-/
def par {Atom : PortBoundary → Type u} {Δ₁ Δ₂ : PortBoundary}
    (e₁ : Expr Atom Δ₁) (e₂ : Expr Atom Δ₂) :
    Expr Atom (PortBoundary.tensor Δ₁ Δ₂) :=
  Quotient.liftOn₂ e₁ e₂ (fun r₁ r₂ => mk (.par r₁ r₂))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (Raw.Equiv.congr_par h₁ h₂))

/--
Connect one shared boundary between two open systems.
-/
def wire {Atom : PortBoundary → Type u} {Δ₁ Γ Δ₂ : PortBoundary}
    (e₁ : Expr Atom (PortBoundary.tensor Δ₁ Γ))
    (e₂ : Expr Atom (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    Expr Atom (PortBoundary.tensor Δ₁ Δ₂) :=
  Quotient.liftOn₂ e₁ e₂ (fun r₁ r₂ => mk (.wire r₁ r₂))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (Raw.Equiv.congr_wire h₁ h₂))

/--
The identity wire (coevaluation) on boundary `Γ`.
-/
def idWire {Atom : PortBoundary → Type u} (Γ : PortBoundary) :
    Expr Atom (PortBoundary.tensor (PortBoundary.swap Γ) Γ) :=
  mk (.idWire Γ)

/--
Close an open system against a matching context.
Derived from `wire` and `map`, mirroring `Raw.plug`.
-/
def plug {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (e : Expr Atom Δ) (k : Expr Atom (PortBoundary.swap Δ)) :
    Expr Atom PortBoundary.empty :=
  Expr.map (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
    (Expr.wire
      (Expr.map (PortBoundary.Equiv.tensorEmptyLeft Δ).symm.toHom e)
      (Expr.map (PortBoundary.Equiv.tensorEmptyRight
        (PortBoundary.swap Δ)).symm.toHom k))

/--
The monoidal unit (closed system with no boundary).
Derived from `idWire` and `map`, mirroring `Raw.unit`.
-/
def unit {Atom : PortBoundary → Type u} : Expr Atom PortBoundary.empty :=
  Expr.map (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
    (Expr.idWire PortBoundary.empty)

/--
Interpret a quotiented expression in a compact closed target theory.

Well-defined on the quotient because `Raw.Equiv.interpret_eq` shows that
equivalent raw expressions interpret the same way in any compact closed theory.
-/
def interpret {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (e : Expr Atom Δ)
    (T : OpenTheory)
    [hT : OpenTheory.CompactClosed T]
    (interp : ∀ {Δ : PortBoundary}, Atom Δ → T.Obj Δ) :
    T.Obj Δ :=
  Quotient.liftOn e
    (fun r => r.interpret T interp OpenTheory.CompactClosed.idWire)
    (fun _ _ h => Raw.Equiv.interpret_eq h T interp)

@[simp]
theorem interpret_mk {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (r : Raw Atom Δ)
    (T : OpenTheory)
    [OpenTheory.CompactClosed T]
    (interp : ∀ {Δ : PortBoundary}, Atom Δ → T.Obj Δ) :
    (mk r).interpret T interp =
      r.interpret T interp OpenTheory.CompactClosed.idWire :=
  rfl

@[simp]
theorem interpret_atom {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (a : Atom Δ)
    (T : OpenTheory)
    [OpenTheory.CompactClosed T]
    (interp : ∀ {Δ : PortBoundary}, Atom Δ → T.Obj Δ) :
    (Expr.atom a).interpret T interp = interp a :=
  rfl

@[simp]
theorem interpret_map {Atom : PortBoundary → Type u} {Δ₁ Δ₂ : PortBoundary}
    (f : PortBoundary.Hom Δ₁ Δ₂)
    (e : Expr Atom Δ₁)
    (T : OpenTheory)
    [OpenTheory.CompactClosed T]
    (interp : ∀ {Δ : PortBoundary}, Atom Δ → T.Obj Δ) :
    (Expr.map f e).interpret T interp = T.map f (e.interpret T interp) :=
  Quotient.inductionOn e fun _ => rfl

@[simp]
theorem interpret_par {Atom : PortBoundary → Type u} {Δ₁ Δ₂ : PortBoundary}
    (e₁ : Expr Atom Δ₁)
    (e₂ : Expr Atom Δ₂)
    (T : OpenTheory)
    [OpenTheory.CompactClosed T]
    (interp : ∀ {Δ : PortBoundary}, Atom Δ → T.Obj Δ) :
    (Expr.par e₁ e₂).interpret T interp =
      T.par (e₁.interpret T interp) (e₂.interpret T interp) :=
  Quotient.inductionOn₂ e₁ e₂ fun _ _ => rfl

@[simp]
theorem interpret_wire {Atom : PortBoundary → Type u}
    {Δ₁ Γ Δ₂ : PortBoundary}
    (e₁ : Expr Atom (PortBoundary.tensor Δ₁ Γ))
    (e₂ : Expr Atom (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (T : OpenTheory)
    [OpenTheory.CompactClosed T]
    (interp : ∀ {Δ : PortBoundary}, Atom Δ → T.Obj Δ) :
    (Expr.wire e₁ e₂).interpret T interp =
      T.wire (e₁.interpret T interp) (e₂.interpret T interp) :=
  Quotient.inductionOn₂ e₁ e₂ fun _ _ => rfl

@[simp]
theorem interpret_idWire {Atom : PortBoundary → Type u}
    (Γ : PortBoundary)
    (T : OpenTheory)
    [OpenTheory.CompactClosed T]
    (interp : ∀ {Δ : PortBoundary}, Atom Δ → T.Obj Δ) :
    (Expr.idWire Γ : Expr Atom _).interpret T interp =
      OpenTheory.CompactClosed.idWire (T := T) Γ :=
  rfl

@[simp]
theorem interpret_plug {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (e : Expr Atom Δ)
    (k : Expr Atom (PortBoundary.swap Δ))
    (T : OpenTheory)
    [OpenTheory.CompactClosed T]
    (interp : ∀ {Δ : PortBoundary}, Atom Δ → T.Obj Δ) :
    (Expr.plug e k).interpret T interp =
      T.plug (e.interpret T interp) (k.interpret T interp) := by
  simp only [Expr.plug, interpret_map, interpret_wire]
  exact (OpenTheory.plug_eq_wire _ _).symm

@[simp]
theorem interpret_unit {Atom : PortBoundary → Type u}
    (T : OpenTheory)
    [OpenTheory.CompactClosed T]
    (interp : ∀ {Δ : PortBoundary}, Atom Δ → T.Obj Δ) :
    (Expr.unit : Expr Atom _).interpret T interp =
      OpenTheory.Monoidal.unit (T := T) := by
  simp only [Expr.unit, interpret_map]
  exact OpenTheory.unit_eq.symm

-- ============================================================================
-- § Lawful OpenTheory instance
-- ============================================================================

/--
The free lawful `OpenTheory` whose objects are quotiented expressions over
`Atom`.
-/
abbrev theory (Atom : PortBoundary → Type u) :
    OpenTheory.{u + 1} where
  Obj := Expr Atom
  map := Expr.map
  par := Expr.par
  wire := Expr.wire
  plug := Expr.plug

instance lawfulMap (Atom : PortBoundary → Type u) :
    OpenTheory.IsLawfulMap (Expr.theory Atom) where
  map_id := fun W =>
    Quotient.inductionOn W fun _ => Quotient.sound Raw.Equiv.map_id
  map_comp := fun _ _ W =>
    Quotient.inductionOn W fun _ => Quotient.sound Raw.Equiv.map_comp

instance lawfulPar (Atom : PortBoundary → Type u) :
    OpenTheory.IsLawfulPar (Expr.theory Atom) where
  map_id := OpenTheory.IsLawfulMap.map_id (T := Expr.theory Atom)
  map_comp := OpenTheory.IsLawfulMap.map_comp (T := Expr.theory Atom)
  map_par := fun _ _ W₁ W₂ =>
    Quotient.inductionOn₂ W₁ W₂ fun _ _ => Quotient.sound Raw.Equiv.map_par

instance lawfulWire (Atom : PortBoundary → Type u) :
    OpenTheory.IsLawfulWire (Expr.theory Atom) where
  map_id := OpenTheory.IsLawfulMap.map_id (T := Expr.theory Atom)
  map_comp := OpenTheory.IsLawfulMap.map_comp (T := Expr.theory Atom)
  map_wire := fun _ _ W₁ W₂ =>
    Quotient.inductionOn₂ W₁ W₂ fun _ _ => Quotient.sound Raw.Equiv.map_wire

instance lawfulPlug (Atom : PortBoundary → Type u) :
    OpenTheory.IsLawfulPlug (Expr.theory Atom) where
  map_id := OpenTheory.IsLawfulMap.map_id (T := Expr.theory Atom)
  map_comp := OpenTheory.IsLawfulMap.map_comp (T := Expr.theory Atom)
  map_plug := fun _ W K =>
    Quotient.inductionOn₂ W K fun _ _ => Quotient.sound Raw.Equiv.map_plug

instance lawful (Atom : PortBoundary → Type u) :
    OpenTheory.IsLawful (Expr.theory Atom) where

instance monoidal (Atom : PortBoundary → Type u) :
    OpenTheory.Monoidal (Expr.theory Atom) where
  unit := Expr.unit
  par_assoc := fun W₁ W₂ W₃ =>
    Quotient.inductionOn₃ W₁ W₂ W₃ fun _ _ _ =>
      Quotient.sound Raw.Equiv.par_assoc
  par_comm := fun W₁ W₂ =>
    Quotient.inductionOn₂ W₁ W₂ fun _ _ =>
      Quotient.sound Raw.Equiv.par_comm
  par_leftUnit := fun W =>
    Quotient.inductionOn W fun _ =>
      Quotient.sound Raw.Equiv.par_leftUnit
  par_rightUnit := fun W =>
    Quotient.inductionOn W fun _ =>
      Quotient.sound Raw.Equiv.par_rightUnit

instance compactClosed (Atom : PortBoundary → Type u) :
    OpenTheory.CompactClosed (Expr.theory Atom) where
  idWire := Expr.idWire
  plug_eq_wire := fun W K =>
    Quotient.inductionOn₂ W K fun _ _ => rfl
  wire_idWire := fun _ _ W₂ =>
    Quotient.inductionOn W₂ fun _ =>
      Quotient.sound Raw.Equiv.wire_idWire
  wire_idWire_right := fun _ _ W₁ =>
    Quotient.inductionOn W₁ fun _ =>
      Quotient.sound Raw.Equiv.wire_idWire_right
  unit_eq := rfl
  wire_par_superpose := fun W₁ W₂ W₃ =>
    Quotient.inductionOn₃ W₁ W₂ W₃ fun _ _ _ =>
      Quotient.sound Raw.Equiv.wire_par_superpose
  wire_assoc := fun W₁ W₂ W₃ =>
    Quotient.inductionOn₃ W₁ W₂ W₃ fun _ _ _ =>
      Quotient.sound Raw.Equiv.wire_assoc
  wire_comm := fun W₁ W₂ =>
    Quotient.inductionOn₂ W₁ W₂ fun _ _ =>
      Quotient.sound Raw.Equiv.wire_comm
  plug_par_left := fun W₁ W₂ K =>
    Quotient.inductionOn₃ W₁ W₂ K fun _ _ _ =>
      Quotient.sound Raw.Equiv.plug_par_left
  plug_wire_left := fun W₁ W₂ K =>
    Quotient.inductionOn₃ W₁ W₂ K fun _ _ _ =>
      Quotient.sound Raw.Equiv.plug_wire_left

-- ============================================================================
-- § Bridge: Expr → Interp
-- ============================================================================

/--
Embed a quotiented expression into the tagless-final representation.

Well-defined on the quotient because equivalent raw expressions interpret the
same way in every compact closed theory (which is exactly what `Interp.ext`
requires).
-/
def toInterp {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (e : Expr Atom Δ) : Interp Atom Δ :=
  Quotient.liftOn e
    (fun r => ⟨fun T hCC interp => r.interpret T interp hCC.idWire⟩)
    (fun _ _ h => Interp.ext (fun T hCC interp =>
      @Raw.Equiv.interpret_eq _ _ _ _ h T hCC interp))

@[simp]
theorem toInterp_mk {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (r : Raw Atom Δ) :
    (mk r).toInterp = (⟨fun T hCC interp =>
      r.interpret T interp hCC.idWire⟩ : Interp Atom Δ) :=
  rfl

@[simp]
theorem toInterp_atom {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (a : Atom Δ) :
    (Expr.atom a).toInterp = Interp.atom (Atom := Atom) a := by
  ext T hT interp; rfl

@[simp]
theorem toInterp_map {Atom : PortBoundary → Type u} {Δ₁ Δ₂ : PortBoundary}
    (f : PortBoundary.Hom Δ₁ Δ₂) (e : Expr Atom Δ₁) :
    (Expr.map f e).toInterp = Interp.map f e.toInterp :=
  Quotient.inductionOn e fun _ => Interp.ext fun _ _ _ => rfl

@[simp]
theorem toInterp_par {Atom : PortBoundary → Type u} {Δ₁ Δ₂ : PortBoundary}
    (e₁ : Expr Atom Δ₁) (e₂ : Expr Atom Δ₂) :
    (Expr.par e₁ e₂).toInterp = Interp.par e₁.toInterp e₂.toInterp :=
  Quotient.inductionOn₂ e₁ e₂ fun _ _ => Interp.ext fun _ _ _ => rfl

@[simp]
theorem toInterp_wire {Atom : PortBoundary → Type u}
    {Δ₁ Γ Δ₂ : PortBoundary}
    (e₁ : Expr Atom (PortBoundary.tensor Δ₁ Γ))
    (e₂ : Expr Atom (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    (Expr.wire e₁ e₂).toInterp = Interp.wire e₁.toInterp e₂.toInterp :=
  Quotient.inductionOn₂ e₁ e₂ fun _ _ => Interp.ext fun _ _ _ => rfl

@[simp]
theorem toInterp_idWire {Atom : PortBoundary → Type u}
    (Γ : PortBoundary) :
    (Expr.idWire Γ : Expr Atom _).toInterp = Interp.idWire Γ := by
  ext T hT interp; rfl

@[simp]
theorem toInterp_plug {Atom : PortBoundary → Type u} {Δ : PortBoundary}
    (e : Expr Atom Δ) (k : Expr Atom (PortBoundary.swap Δ)) :
    (Expr.plug e k).toInterp = Interp.plug e.toInterp k.toInterp :=
  Quotient.inductionOn₂ e k fun r₁ r₂ =>
    Interp.ext fun T hT interp => by
      change (Raw.plug r₁ r₂).interpret T interp hT.idWire =
        T.plug (r₁.interpret T interp hT.idWire) (r₂.interpret T interp hT.idWire)
      simp only [Raw.interpret]
      exact (OpenTheory.plug_eq_wire (T := T)
        (r₁.interpret T interp hT.idWire) (r₂.interpret T interp hT.idWire)).symm

@[simp]
theorem toInterp_unit {Atom : PortBoundary → Type u} :
    (Expr.unit : Expr Atom _).toInterp = Interp.unit := by
  have h : (Expr.unit : Expr Atom _).toInterp =
      (⟨fun T hCC interp =>
        (Raw.unit (Atom := Atom)).interpret T interp hCC.idWire⟩ :
        Interp Atom _) := rfl
  rw [h]
  ext T hT interp
  simp [Raw.interpret, Interp.unit, OpenTheory.unit_eq]

end Expr

end OpenSyntax
end UC
end Interaction
