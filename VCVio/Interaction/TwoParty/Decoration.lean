/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Append
import VCVio.Interaction.Basic.MonadDecoration
import VCVio.Interaction.TwoParty.Role

/-!
# Role decorations and common role-based node contexts

A `RoleDecoration spec` is a `Spec.Decoration` with fiber `fun _ => Role`: each internal node is
labeled sender or receiver. This replaces a separate two-party interaction inductive while reusing
all `Spec` infrastructure (`Transcript`, `append`, etc.).

This file also packages the most common role-based node contexts used by the two-party interaction
layer:
* `RoleContext` / `RoleSchema` for plain sender/receiver metadata;
* `RoleMonadContext` for one bundled monad over each role-labeled node;
* `RolePairedMonadContext` for paired prover/verifier monads;
* `RolePairedMonadContext.fst` / `RolePairedMonadContext.snd` for forgetting one side of the
  paired monadic context.

Only the plain role layer is exposed as a schema here. The monadic extensions are exported as
realized node contexts, because `BundledMonad` lives in a higher universe than `Role`, while
`Spec.Node.Schema` currently uses one fixed universe for all staged fields.

These are the outward-facing schema/context names used by `Strategy.withRolesAndMonads`,
`Counterpart.withMonads`, and the monadic execution layer.
-/

universe u

namespace Interaction

/-- The plain role-labeled node context. -/
abbrev RoleContext : Spec.Node.Context := fun _ => Role

/-- The singleton schema presenting `RoleContext`. -/
abbrev RoleSchema : Spec.Node.Schema RoleContext :=
  .singleton RoleContext

/-- Role context extended by one bundled monad field. -/
abbrev RoleMonadContext : Spec.Node.Context.{u, u + 1} :=
  Spec.Node.Context.extend RoleContext (fun _ _ => BundledMonad.{u, u})

/-- Role context extended by a pair of bundled monads. -/
abbrev RolePairedMonadContext : Spec.Node.Context.{u, u + 1} :=
  Spec.Node.Context.extend
    RoleContext (fun _ _ => BundledMonad.{u, u} × BundledMonad.{u, u})

namespace RolePairedMonadContext

/-- Forget the counterpart monad from a paired role/monad context. -/
abbrev fst : Spec.Node.ContextHom RolePairedMonadContext RoleMonadContext :=
  Spec.Node.Context.extendMap
    (Spec.Node.ContextHom.id RoleContext)
    (fun _ _ (bms : BundledMonad.{u, u} × BundledMonad.{u, u}) => bms.1)

/-- Forget the focal monad from a paired role/monad context. -/
abbrev snd : Spec.Node.ContextHom RolePairedMonadContext RoleMonadContext :=
  Spec.Node.Context.extendMap
    (Spec.Node.ContextHom.id RoleContext)
    (fun _ _ (bms : BundledMonad.{u, u} × BundledMonad.{u, u}) => bms.2)

end RolePairedMonadContext

/-- Per-node sender/receiver assignment on a `Spec`. -/
abbrev RoleDecoration := Spec.Decoration (fun _ => Role)

namespace Spec
namespace Decoration

/-- Swap sender ↔ receiver at each node.

Because `RoleDecoration` is an `abbrev` of `Decoration (fun _ => Role)`, dot notation on
`roles : RoleDecoration spec` resolves this `Spec.Decoration.swap`. -/
def swap {spec : Spec} (roles : Decoration (fun _ => Role) spec) :
    Decoration (fun _ => Role) spec :=
  map (fun _ => Role.swap) spec roles

end Decoration
end Spec

namespace RoleDecoration

/-- View a plain monad decoration as one displayed layer over an existing role decoration. -/
def monadsOver :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) → (md : Spec.MonadDecoration spec) →
    Spec.Decoration.Over (fun _ (_ : Role) => BundledMonad.{u, u}) spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨_, rRest⟩, ⟨bm, mRest⟩ =>
      ⟨bm, fun x => monadsOver (rest x) (rRest x) (mRest x)⟩

/-- Pack roles together with one bundled monad per node into `RoleMonadContext`. -/
def withMonads {spec : Spec.{u}}
    (roles : RoleDecoration spec) (md : Spec.MonadDecoration spec) :
    Spec.Decoration RoleMonadContext spec :=
  Spec.Decoration.ofOver (fun _ (_ : Role) => BundledMonad.{u, u}) spec roles
    (monadsOver spec roles md)

/-- View a pair of monad decorations as one displayed layer over an existing role decoration. -/
def pairedMonadsOver :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) →
    (stratDeco : Spec.MonadDecoration spec) → (cptDeco : Spec.MonadDecoration spec) →
    Spec.Decoration.Over
      (fun _ (_ : Role) => BundledMonad.{u, u} × BundledMonad.{u, u}) spec roles
  | .done, _, _, _ => ⟨⟩
  | .node _ rest, ⟨_, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩ =>
      ⟨(bmS, bmC), fun x => pairedMonadsOver (rest x) (rRest x) (mRestS x) (mRestC x)⟩

/-- Pack roles together with paired prover/counterpart monads into `RolePairedMonadContext`. -/
def withPairedMonads {spec : Spec.{u}}
    (roles : RoleDecoration spec) (stratDeco : Spec.MonadDecoration spec)
    (cptDeco : Spec.MonadDecoration spec) :
    Spec.Decoration RolePairedMonadContext spec :=
  Spec.Decoration.ofOver
    (fun _ (_ : Role) => BundledMonad.{u, u} × BundledMonad.{u, u})
    spec roles (pairedMonadsOver spec roles stratDeco cptDeco)

@[simp]
theorem withPairedMonads_map_fst :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {stratDeco cptDeco : Spec.MonadDecoration spec} →
    Spec.Decoration.map RolePairedMonadContext.fst spec
        (RoleDecoration.withPairedMonads roles stratDeco cptDeco) =
      RoleDecoration.withMonads roles stratDeco
  | .done, _, _, _ => rfl
  | .node _ rest, ⟨role, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩ => by
      simp only [RoleDecoration.withPairedMonads, RoleDecoration.withMonads,
        RoleDecoration.monadsOver, RoleDecoration.pairedMonadsOver,
        RolePairedMonadContext.fst]
      apply Prod.ext
      · rfl
      funext x
      exact withPairedMonads_map_fst
        (spec := rest x) (roles := rRest x)
        (stratDeco := mRestS x) (cptDeco := mRestC x)

@[simp]
theorem withPairedMonads_map_snd :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {stratDeco cptDeco : Spec.MonadDecoration spec} →
    Spec.Decoration.map RolePairedMonadContext.snd spec
        (RoleDecoration.withPairedMonads roles stratDeco cptDeco) =
      RoleDecoration.withMonads roles cptDeco
  | .done, _, _, _ => rfl
  | .node _ rest, ⟨role, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩ => by
      simp only [RoleDecoration.withPairedMonads, RoleDecoration.withMonads,
        RoleDecoration.monadsOver, RoleDecoration.pairedMonadsOver,
        RolePairedMonadContext.snd]
      apply Prod.ext
      · rfl
      funext x
      exact withPairedMonads_map_snd
        (spec := rest x) (roles := rRest x)
        (stratDeco := mRestS x) (cptDeco := mRestC x)

end RoleDecoration

end Interaction
