/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.MonadDecoration
import VCVio.Interaction.TwoParty.Role

/-!
# Role decorations and common role-based node contexts

A `RoleDecoration spec` is a `Decoration` with fiber `fun _ => Role`:
each internal node is labeled sender or receiver. It adds two-party control
information to an ordinary interaction tree while reusing the surrounding `Spec` infrastructure
(`Transcript`, `append`, etc.).

This file also packages the most common role-based node contexts used by the
two-party interaction layer:
* `RoleContext` / `RoleSchema` for plain sender/receiver metadata;
* `RoleMonadContext` for one bundled monad over each role-labeled node;
* `RolePairedMonadContext` for paired focal/counterpart monads;
* `RolePairedMonadContext.fst` / `RolePairedMonadContext.snd` for forgetting
  one side of the paired monadic context.

Only the plain role layer is exposed as a schema here. The monadic extensions are exported as
realized node contexts, because `BundledMonad` lives in a higher universe than `Role`, while
`Spec.Node.Schema` currently uses one fixed universe for all staged fields.

These contexts are ordinary inputs to `StrategyOver`: roles say who owns the
move, and monad decorations say which node effect is used by each participant.
-/

universe u uA uB t

namespace Interaction
open PFunctor.FreeM.Displayed (Decoration)
namespace TwoParty

open TwoParty
open PFunctor

variable {P : PFunctor.{uA, uB}} {α : Type t}

/-! ## Generic role contexts -/

/-- The generic role-labeled node context for a polynomial control tree. -/
abbrev RoleContextOver (P : PFunctor.{uA, uB}) : P.A → Type :=
  fun _ => Role

/-- Generic role context extended by one bundled monad field. -/
abbrev RoleMonadContextOver (P : PFunctor.{uA, uB}) : P.A → Type (u + 1) :=
  fun _ => Σ _ : Role, BundledMonad.{u, u}

/-- Generic role context extended by a pair of bundled monads. -/
abbrev RolePairedMonadContextOver (P : PFunctor.{uA, uB}) : P.A → Type (u + 1) :=
  fun _ => Σ _ : Role, BundledMonad.{u, u} × BundledMonad.{u, u}

namespace RoleMonadContextOver

/-- Duplicate one generic role/monad context into paired focal/counterpart monads. -/
abbrev diagonal :
    ∀ pos, RoleMonadContextOver P pos → RolePairedMonadContextOver P pos :=
  fun _ ⟨role, bm⟩ => ⟨role, (bm, bm)⟩

end RoleMonadContextOver

namespace RolePairedMonadContextOver

/-- Forget the counterpart monad from a generic paired role/monad context. -/
abbrev fst :
    ∀ pos, RolePairedMonadContextOver P pos → RoleMonadContextOver P pos :=
  fun _ ⟨role, bms⟩ => ⟨role, bms.1⟩

/-- Forget the focal monad from a generic paired role/monad context. -/
abbrev snd :
    ∀ pos, RolePairedMonadContextOver P pos → RoleMonadContextOver P pos :=
  fun _ ⟨role, bms⟩ => ⟨role, bms.2⟩

end RolePairedMonadContextOver

/-- Generic per-node sender/receiver assignment on a polynomial free tree. -/
abbrev RoleDecorationOver :=
  Decoration (P := P) (α := α) (RoleContextOver P)

/-- Swap sender and receiver at each node of a generic role decoration. -/
def RoleDecorationOver.swap {s : PFunctor.FreeM P α} (roles : RoleDecorationOver (P := P) s) :
    RoleDecorationOver (P := P) s :=
  Decoration.map (P := P) (α := α) (fun _ => Role.swap) s roles

namespace RoleDecorationOver

/-- View a generic monad decoration as one displayed layer over a role decoration. -/
def monadsOver :
    (s : PFunctor.FreeM P α) → (roles : RoleDecorationOver (P := P) s) →
    (md : MonadDecoration (P := P) (α := α) s) →
    Decoration.Over (P := P) (α := α) (RoleContextOver P)
      (fun _ (_ : Role) => BundledMonad.{u, u}) s roles
  | .pure _, _, _ => ⟨⟩
  | .roll _ rest, ⟨_, rRest⟩, ⟨bm, mRest⟩ =>
      ⟨bm, fun b => monadsOver (rest b) (rRest b) (mRest b)⟩

/-- Pack roles together with one bundled monad per node generically. -/
def withMonads {s : PFunctor.FreeM P α}
    (roles : RoleDecorationOver (P := P) s) (md : MonadDecoration (P := P) (α := α) s) :
    Decoration (P := P) (α := α) (RoleMonadContextOver P) s :=
  Decoration.ofOver (P := P) (α := α) s roles
    (monadsOver (P := P) (α := α) s roles md)

/-- View paired monad decorations as one displayed layer over a role decoration. -/
def pairedMonadsOver :
    (s : PFunctor.FreeM P α) → (roles : RoleDecorationOver (P := P) s) →
    (stratDeco : MonadDecoration (P := P) (α := α) s) →
    (cptDeco : MonadDecoration (P := P) (α := α) s) →
    Decoration.Over (P := P) (α := α) (RoleContextOver P)
      (fun _ (_ : Role) => BundledMonad.{u, u} × BundledMonad.{u, u}) s roles
  | .pure _, _, _, _ => ⟨⟩
  | .roll _ rest, ⟨_, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩ =>
      ⟨(bmS, bmC), fun b => pairedMonadsOver (rest b) (rRest b) (mRestS b) (mRestC b)⟩

/-- Pack roles together with paired focal/counterpart monads generically. -/
def withPairedMonads {s : PFunctor.FreeM P α}
    (roles : RoleDecorationOver (P := P) s)
    (stratDeco : MonadDecoration (P := P) (α := α) s)
    (cptDeco : MonadDecoration (P := P) (α := α) s) :
    Decoration (P := P) (α := α) (RolePairedMonadContextOver P) s :=
  Decoration.ofOver (P := P) (α := α) s roles
    (pairedMonadsOver (P := P) (α := α) s roles stratDeco cptDeco)

@[simp]
theorem withPairedMonads_map_fst :
    {s : PFunctor.FreeM P α} → {roles : RoleDecorationOver (P := P) s} →
    {stratDeco cptDeco : MonadDecoration (P := P) (α := α) s} →
    Decoration.map (P := P) (α := α) (RolePairedMonadContextOver.fst (P := P)) s
        (withPairedMonads (P := P) (α := α) roles stratDeco cptDeco) =
      withMonads (P := P) (α := α) roles stratDeco
  | .pure _, _, _, _ => rfl
  | .roll _ rest, ⟨role, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩ => by
      simp only [withPairedMonads, withMonads, monadsOver, pairedMonadsOver,
        RolePairedMonadContextOver.fst, Decoration.map_roll, Decoration.ofOver]
      apply Prod.ext
      · rfl
      funext b
      exact withPairedMonads_map_fst
        (s := rest b) (roles := rRest b)
        (stratDeco := mRestS b) (cptDeco := mRestC b)

@[simp]
theorem withPairedMonads_map_snd :
    {s : PFunctor.FreeM P α} → {roles : RoleDecorationOver (P := P) s} →
    {stratDeco cptDeco : MonadDecoration (P := P) (α := α) s} →
    Decoration.map (P := P) (α := α) (RolePairedMonadContextOver.snd (P := P)) s
        (withPairedMonads (P := P) (α := α) roles stratDeco cptDeco) =
      withMonads (P := P) (α := α) roles cptDeco
  | .pure _, _, _, _ => rfl
  | .roll _ rest, ⟨role, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩ => by
      simp only [withPairedMonads, withMonads, monadsOver, pairedMonadsOver,
        RolePairedMonadContextOver.snd, Decoration.map_roll, Decoration.ofOver]
      apply Prod.ext
      · rfl
      funext b
      exact withPairedMonads_map_snd
        (s := rest b) (roles := rRest b)
        (stratDeco := mRestS b) (cptDeco := mRestC b)

end RoleDecorationOver

/-! ## Plain-spec role contexts -/

/-- The plain role-labeled node context. -/
abbrev RoleContext : Spec.Node.Context := fun _ => Role

/-- The singleton schema presenting `RoleContext`. -/
abbrev RoleSchema : Spec.Node.Schema RoleContext :=
  .singleton RoleContext

/-- Role context extended by one bundled monad field. -/
abbrev RoleMonadContext : Spec.Node.Context.{u, u + 1} :=
  fun _ => Σ _ : Role, BundledMonad.{u, u}

/-- Role context extended by a pair of bundled monads. -/
abbrev RolePairedMonadContext : Spec.Node.Context.{u, u + 1} :=
  fun _ => Σ _ : Role, BundledMonad.{u, u} × BundledMonad.{u, u}

namespace RoleMonadContext

/-- Duplicate one role/monad context into paired focal/counterpart monads. -/
abbrev diagonal : Spec.Node.ContextHom RoleMonadContext RolePairedMonadContext :=
  Spec.Node.Context.extendMap
    (Spec.Node.ContextHom.id RoleContext)
    (fun _ _ (bm : BundledMonad.{u, u}) => (bm, bm))

end RoleMonadContext

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
abbrev RoleDecoration := Decoration (P := Spec.basePFunctor)
  (α := PUnit.{u+1}) (fun _ => Role)

/-- Swap sender and receiver at each node of a role decoration. -/
def RoleDecoration.swap {spec : Spec} (roles : RoleDecoration spec) :
    RoleDecoration spec :=
  Decoration.map (fun _ => Role.swap) spec roles

namespace RoleDecoration

/-- View a plain monad decoration as one displayed layer over an existing role decoration. -/
def monadsOver :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) → (md : Spec.MonadDecoration spec) →
    Decoration.Over (fun _ => Role) (fun _ (_ : Role) => BundledMonad.{u, u}) spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨_, rRest⟩, ⟨bm, mRest⟩ =>
      ⟨bm, fun x => monadsOver (rest x) (rRest x) (mRest x)⟩

/-- Pack roles together with one bundled monad per node into `RoleMonadContext`. -/
def withMonads {spec : Spec.{u}}
    (roles : RoleDecoration spec) (md : Spec.MonadDecoration spec) :
    Decoration RoleMonadContext spec :=
  Decoration.ofOver spec roles (monadsOver spec roles md)

/-- View a pair of monad decorations as one displayed layer over an existing role decoration. -/
def pairedMonadsOver :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) →
    (stratDeco : Spec.MonadDecoration spec) → (cptDeco : Spec.MonadDecoration spec) →
    Decoration.Over
      (fun _ => Role) (fun _ (_ : Role) => BundledMonad.{u, u} × BundledMonad.{u, u}) spec roles
  | .done, _, _, _ => ⟨⟩
  | .node _ rest, ⟨_, rRest⟩, ⟨bmS, mRestS⟩, ⟨bmC, mRestC⟩ =>
      ⟨(bmS, bmC), fun x => pairedMonadsOver (rest x) (rRest x) (mRestS x) (mRestC x)⟩

/-- Pack roles together with paired prover/counterpart monads into `RolePairedMonadContext`. -/
def withPairedMonads {spec : Spec.{u}}
    (roles : RoleDecoration spec) (stratDeco : Spec.MonadDecoration spec)
    (cptDeco : Spec.MonadDecoration spec) :
    Decoration RolePairedMonadContext spec :=
  Decoration.ofOver spec roles (pairedMonadsOver spec roles stratDeco cptDeco)

@[simp]
theorem withPairedMonads_map_fst :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {stratDeco cptDeco : Spec.MonadDecoration spec} →
    Decoration.map RolePairedMonadContext.fst spec
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
    Decoration.map RolePairedMonadContext.snd spec
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

end TwoParty
end Interaction
