/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Append
import VCVio.Interaction.Basic.Replicate
import VCVio.Interaction.Basic.Chain
import VCVio.Interaction.TwoParty.Role
import VCVio.Interaction.TwoParty.Decoration
import Mathlib.Logic.Equiv.Defs

/-!
# Role-aware refinement and bridge to `Decoration.Over`

`Role.Refine S` carries sender data `S X` and skips receiver nodes (no `PUnit` padding). Conversion
to `Spec.Decoration.Over` with fiber `Role.SenderData` is an equivalence; `map` laws commute with
`append`, `replicate`, and `stateChain`.
-/

universe u v w w₂

namespace Interaction

/-- Role-aware displayed data: `S X` at sender nodes; `∀` recursion at receiver nodes. -/
@[reducible] def Role.Refine (S : Type u → Type v) :
    (spec : Spec.{u}) → RoleDecoration spec → Type (max u v)
  | .done, _ => PUnit
  | .node X rest, ⟨.sender, rRest⟩ =>
      S X × (∀ x, Role.Refine S (rest x) (rRest x))
  | .node _X rest, ⟨.receiver, rRest⟩ =>
      ∀ x, Role.Refine S (rest x) (rRest x)

namespace Role.Refine

/-- Natural transformation of sender fibers, applied recursively. -/
def map {S : Type u → Type v} {T : Type u → Type w}
    (f : ∀ X, S X → T X) :
    (spec : Spec) → (roles : RoleDecoration spec) →
    Role.Refine S spec roles → Role.Refine T spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ =>
      ⟨f _ s, fun x => map f (rest x) (rRest x) (rr x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, rr =>
      fun x => map f (rest x) (rRest x) (rr x)

/-- Append refinements over appended role decorations. -/
def append {S : Type u → Type v}
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)} :
    Role.Refine S s₁ r₁ →
    ((tr₁ : Spec.Transcript s₁) → Role.Refine S (s₂ tr₁) (r₂ tr₁)) →
    Role.Refine S (s₁.append s₂) (r₁.append r₂) :=
  match s₁, r₁ with
  | .done, _ => fun _ sd₂ => sd₂ ⟨⟩
  | .node _ _rest, ⟨.sender, _rRest⟩ => fun ⟨s, rr⟩ sd₂ =>
      ⟨s, fun x => append (rr x) (fun p => sd₂ ⟨x, p⟩)⟩
  | .node _ _rest, ⟨.receiver, _rRest⟩ => fun rr sd₂ =>
      fun x => append (rr x) (fun p => sd₂ ⟨x, p⟩)

/-- Replicate along `Spec.replicate` / `Spec.Decoration.replicate`. -/
def replicate {S : Type u → Type v}
    {spec : Spec} {roles : RoleDecoration spec}
    (sd : Role.Refine S spec roles) : (n : Nat) →
    Role.Refine S (spec.replicate n) (roles.replicate n)
  | 0 => ⟨⟩
  | n + 1 => append sd (fun _ => replicate sd n)

/-- Chain a family of refinements along `Spec.stateChain`. -/
def stateChain {S : Type u → Type v}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    (sdeco : (i : Nat) → (s : Stage i) → Role.Refine S (spec i s) (roles i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Role.Refine S (Spec.stateChain Stage spec advance n i s)
      (Spec.Decoration.stateChain roles n i s)
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      append (sdeco i s)
        (fun tr => stateChain sdeco n (i + 1) (advance i s tr))

end Role.Refine

namespace Role

/-- Fiber `S X` at sender and `PUnit` at receiver (for the `Decoration.Over` bridge). -/
def SenderData (S : Type u → Type v) (X : Type u) : Role → Type v
  | .sender => S X
  | .receiver => PUnit

/-- Functorial update of `SenderData` under `f : ∀ X, S X → T X`. -/
def SenderData.map {S T : Type u → Type v} (f : ∀ X, S X → T X) (X : Type u) :
    ∀ r : Role, SenderData S X r → SenderData T X r
  | .sender, s => f X s
  | .receiver, u => u

end Role

namespace Role.Refine

@[simp, grind =]
theorem map_id {S : Type u → Type v} :
    (spec : Spec) → (roles : RoleDecoration spec) → (rr : Role.Refine S spec roles) →
    map (fun X (s : S X) => s) spec roles rr = rr
  | .done, _, _ => rfl
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ => by
      simp only [map]; congr 1; funext x
      exact map_id (rest x) (rRest x) (rr x)
  | .node _ rest, ⟨.receiver, rRest⟩, rr => by
      funext x
      simp only [map]
      exact map_id (rest x) (rRest x) (rr x)

theorem map_comp {S : Type u → Type v} {T : Type u → Type w} {U : Type u → Type w₂}
    (g : ∀ X, T X → U X) (f : ∀ X, S X → T X) :
    (spec : Spec) → (roles : RoleDecoration spec) → (rr : Role.Refine S spec roles) →
    map g spec roles (map f spec roles rr) =
      map (fun X => g X ∘ f X) spec roles rr
  | .done, _, _ => rfl
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ => by
      simp only [map]; congr 1; funext x
      exact map_comp g f (rest x) (rRest x) (rr x)
  | .node _ rest, ⟨.receiver, rRest⟩, rr => by
      funext x
      simp only [map]
      exact map_comp g f (rest x) (rRest x) (rr x)

theorem map_append {S T : Type u → Type v} (f : ∀ X, S X → T X)
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {rd₁ : RoleDecoration s₁}
    {rd₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    (sd₁ : Role.Refine S s₁ rd₁)
    (sd₂ : (tr₁ : Spec.Transcript s₁) → Role.Refine S (s₂ tr₁) (rd₂ tr₁)) :
    map f (s₁.append s₂) (rd₁.append rd₂) (append sd₁ sd₂) =
      append (map f s₁ rd₁ sd₁)
        (fun tr₁ => map f (s₂ tr₁) (rd₂ tr₁) (sd₂ tr₁)) := by
  cases s₁ with
  | done => rfl
  | node X rest =>
    rcases rd₁ with ⟨role, rRest⟩
    cases role with
    | sender =>
      rcases sd₁ with ⟨_s, rr⟩
      simp only [append, map]
      refine Prod.ext rfl ?_
      funext x
      exact map_append f (rr x) (fun p => sd₂ ⟨x, p⟩)
    | receiver =>
      simp only [append, map]
      funext x
      exact map_append f (sd₁ x) (fun p => sd₂ ⟨x, p⟩)

theorem map_replicate {S T : Type u → Type v} (f : ∀ X, S X → T X)
    {spec : Spec} {roles : RoleDecoration spec}
    (sd : Role.Refine S spec roles) (n : Nat) :
    map f (spec.replicate n) (roles.replicate n) (replicate sd n) =
      replicate (map f spec roles sd) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [replicate, Spec.replicate_succ, Spec.Decoration.replicate]
    rw [map_append f sd (fun _ => replicate sd n)]
    refine congrArg (append (map f spec roles sd)) ?_
    funext _
    exact ih

theorem map_stateChain {S T : Type u → Type v} (f : ∀ X, S X → T X)
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    (sdeco : (i : Nat) → (s : Stage i) → Role.Refine S (spec i s) (roles i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    map f (Spec.stateChain Stage spec advance n i s)
        (Spec.Decoration.stateChain roles n i s) (stateChain sdeco n i s) =
      stateChain (fun j t => map f (spec j t) (roles j t) (sdeco j t)) n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
      simp only [Spec.stateChain_succ, stateChain, Spec.Decoration.stateChain]
      rw [map_append f (sdeco i s)
            (fun tr => stateChain sdeco n (i + 1) (advance i s tr))]
      refine congrArg (append (map f (spec i s) (roles i s) (sdeco i s))) ?_
      funext tr
      exact map_stateChain f sdeco n (i + 1) (advance i s tr)

def toDecorationOver {S : Type u → Type v} :
    (spec : Spec) → (roles : RoleDecoration spec) →
    Role.Refine S spec roles →
    Spec.Decoration.Over (fun X r => Role.SenderData S X r) spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ =>
      ⟨s, fun x => toDecorationOver (rest x) (rRest x) (rr x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, rr =>
      ⟨⟨⟩, fun x => toDecorationOver (rest x) (rRest x) (rr x)⟩

def ofDecorationOver {S : Type u → Type v} :
    (spec : Spec) → (roles : RoleDecoration spec) →
    Spec.Decoration.Over (fun X r => Role.SenderData S X r) spec roles →
    Role.Refine S spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ =>
      ⟨s, fun x => ofDecorationOver (rest x) (rRest x) (rr x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨_, rr⟩ =>
      fun x => ofDecorationOver (rest x) (rRest x) (rr x)

@[simp]
theorem toDecorationOver_ofDecorationOver {S : Type u → Type v} :
    ∀ (spec : Spec) (roles : RoleDecoration spec)
      (dr : Spec.Decoration.Over (fun X r => Role.SenderData S X r) spec roles),
      toDecorationOver spec roles (ofDecorationOver spec roles dr) = dr
  | .done, _, ⟨⟩ => rfl
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ => by
      simp only [toDecorationOver, ofDecorationOver]
      congr 1
      funext x
      exact toDecorationOver_ofDecorationOver (rest x) (rRest x) (rr x)
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨u, rr⟩ => by
      cases u
      simp only [toDecorationOver, ofDecorationOver]
      congr 1
      funext x
      exact toDecorationOver_ofDecorationOver (rest x) (rRest x) (rr x)

@[simp]
theorem ofDecorationOver_toDecorationOver {S : Type u → Type v} :
    ∀ (spec : Spec) (roles : RoleDecoration spec)
      (rr : Role.Refine S spec roles),
      ofDecorationOver spec roles (toDecorationOver spec roles rr) = rr
  | .done, _, ⟨⟩ => rfl
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ => by
      simp only [toDecorationOver, ofDecorationOver]
      congr 1
      funext x
      exact ofDecorationOver_toDecorationOver (rest x) (rRest x) (rr x)
  | .node _ rest, ⟨.receiver, rRest⟩, rr => by
      funext x
      simp only [toDecorationOver, ofDecorationOver]
      exact ofDecorationOver_toDecorationOver (rest x) (rRest x) (rr x)

/-- Canonical equivalence with `Decoration.Over` at fiber `SenderData`. -/
def equivDecorationOver {S : Type u → Type v}
    (spec : Spec) (roles : RoleDecoration spec) :
    Equiv (Role.Refine S spec roles)
      (Spec.Decoration.Over (fun X r => Role.SenderData S X r) spec roles) where
  toFun := toDecorationOver spec roles
  invFun := ofDecorationOver spec roles
  left_inv rr := ofDecorationOver_toDecorationOver spec roles rr
  right_inv dr := toDecorationOver_ofDecorationOver spec roles dr

theorem toDecorationOver_map {S T : Type u → Type v} (f : ∀ X, S X → T X) :
    (spec : Spec) → (roles : RoleDecoration spec) → (rr : Role.Refine S spec roles) →
    toDecorationOver spec roles (map f spec roles rr) =
      Spec.Decoration.Over.map (fun X r => Role.SenderData.map f X r) spec roles
        (toDecorationOver spec roles rr)
  | .done, _, _ => rfl
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ => by
      simp only [toDecorationOver, map, Spec.Decoration.Over.map]
      congr 1; funext x
      exact toDecorationOver_map f (rest x) (rRest x) (rr x)
  | .node _ rest, ⟨.receiver, rRest⟩, rr => by
      simp only [toDecorationOver, map, Spec.Decoration.Over.map,
        Role.SenderData.map]
      congr 1; funext x
      exact toDecorationOver_map f (rest x) (rRest x) (rr x)

theorem ofDecorationOver_map {S T : Type u → Type v} (f : ∀ X, S X → T X) :
    (spec : Spec) → (roles : RoleDecoration spec) →
    (dr : Spec.Decoration.Over (fun X r => Role.SenderData S X r) spec roles) →
    ofDecorationOver spec roles
        (Spec.Decoration.Over.map (fun X r => Role.SenderData.map f X r) spec roles dr) =
      map f spec roles (ofDecorationOver spec roles dr)
  | .done, _, _ => rfl
  | .node _ rest, ⟨.sender, rRest⟩, ⟨s, rr⟩ => by
      simp only [ofDecorationOver, Spec.Decoration.Over.map, map]
      congr 1; funext x
      exact ofDecorationOver_map f (rest x) (rRest x) (rr x)
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨u, rr⟩ => by
      cases u
      funext x
      simp only [ofDecorationOver, Spec.Decoration.Over.map, map,
        Role.SenderData.map]
      exact ofDecorationOver_map f (rest x) (rRest x) (rr x)

end Role.Refine
end Interaction
