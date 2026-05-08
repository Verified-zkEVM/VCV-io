/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.BundledMonad
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Interaction

/-!
# Per-node monad decorations

`MonadDecoration s` assigns a `BundledMonad` to each internal node of a
polynomial free tree.

The corresponding one-participant syntax, `Strategy.monadicSyntax`, chooses a
move at a node and places the continuation in the monad recorded by that node.
Use it directly with `StrategyOver` for whole-tree strategies and with
`InteractionOver.run` through `Strategy.monadicInteraction` for execution in an
ambient monad.
-/

universe u uA uB t

namespace Interaction

open PFunctor

variable {P : PFunctor.{uA, uB}} {α : Type t}

/-- Node-wise choice of monad, as a `Decoration` valued in `BundledMonad`. -/
abbrev MonadDecoration :=
  Decoration (P := P) (α := α) (fun (_ : P.A) => BundledMonad.{u, u})

namespace MonadDecoration

/--
Constant monad decoration: every node in the interaction tree uses the same
bundled monad.

This is the bridge between ordinary single-monad strategies and strategies
whose node effects are described by a `MonadDecoration`.
-/
def constant (bm : BundledMonad.{u, u}) :
    (s : PFunctor.FreeM P α) → MonadDecoration.{u} s
  | .pure _ => PUnit.unit
  | .roll _ rest => ⟨bm, fun b => constant bm (rest b)⟩

/--
Nodewise monad homomorphism between two monad decorations on the same
polynomial free tree.

At each internal node it gives a lift from the source bundled monad to the
target bundled monad, together with recursive lifts for every continuation
subtree.
-/
def Hom :
    (s : PFunctor.FreeM P α) → MonadDecoration.{u} s →
      MonadDecoration.{u} s → Type (max uB (u + 1))
  | .pure _, _, _ => PUnit
  | .roll pos rest, ⟨m₁, md₁⟩, ⟨m₂, md₂⟩ =>
      (∀ {α : Type u}, m₁.M α → m₂.M α) ×
        ((b : P.B pos) → Hom (rest b) (md₁ b) (md₂ b))

namespace Hom

/-- Identity homomorphism on a monad decoration. -/
def id :
    (s : PFunctor.FreeM P α) → (md : MonadDecoration.{u} s) →
      Hom s md md
  | .pure _, _ => PUnit.unit
  | .roll _ rest, ⟨_, mdRest⟩ =>
      ⟨fun x => x, fun b => id (rest b) (mdRest b)⟩

/-- Constant homomorphism induced by a single monad lift. -/
def constant {bm₁ bm₂ : BundledMonad.{u, u}}
    (lift : ∀ {α : Type u}, bm₁.M α → bm₂.M α) :
    (s : PFunctor.FreeM P α) →
      Hom s (MonadDecoration.constant bm₁ s) (MonadDecoration.constant bm₂ s)
  | .pure _ => PUnit.unit
  | .roll _ rest => ⟨lift, fun b => constant lift (rest b)⟩

end Hom

end MonadDecoration

namespace Spec

/-- Node-wise choice of monad on a plain interaction spec. -/
abbrev MonadDecoration :=
  _root_.Interaction.MonadDecoration.{u, u + 1, u, u}
    (P := Spec.basePFunctor) (α := PUnit.{u + 1})

namespace MonadDecoration

/-- Constant monad decoration on a plain interaction spec. -/
abbrev constant (bm : BundledMonad.{u, u}) :
    (spec : Spec.{u}) → MonadDecoration.{u} spec :=
  _root_.Interaction.MonadDecoration.constant.{u, u + 1, u, u}
    (P := Spec.basePFunctor) (α := PUnit.{u + 1}) bm

/-- Nodewise monad homomorphism between plain-spec monad decorations. -/
abbrev Hom (spec : Spec.{u})
    (md₁ md₂ : MonadDecoration.{u} spec) : Type (u + 1) :=
  _root_.Interaction.MonadDecoration.Hom.{u, u + 1, u, u}
    (P := Spec.basePFunctor) (α := PUnit.{u + 1}) spec md₁ md₂

namespace Hom

/-- Identity homomorphism on a plain-spec monad decoration. -/
abbrev id :
    (spec : Spec.{u}) → (md : MonadDecoration.{u} spec) →
      Hom spec md md :=
  _root_.Interaction.MonadDecoration.Hom.id.{u, u + 1, u, u}
    (P := Spec.basePFunctor) (α := PUnit.{u + 1})

/-- Constant homomorphism induced by a single monad lift. -/
abbrev constant {bm₁ bm₂ : BundledMonad.{u, u}}
    (lift : ∀ {α : Type u}, bm₁.M α → bm₂.M α) :
    (spec : Spec.{u}) →
      Hom spec (MonadDecoration.constant bm₁ spec) (MonadDecoration.constant bm₂ spec) :=
  _root_.Interaction.MonadDecoration.Hom.constant.{u, u + 1, u, u}
    (P := Spec.basePFunctor) (α := PUnit.{u + 1}) lift

end Hom

end MonadDecoration

/-- One-participant local syntax whose continuation lives in the node monad.

At each node the strategy chooses a move `x` immediately, then supplies the
continuation in the `BundledMonad` stored by the node decoration. -/
def Strategy.monadicSyntax :
    SyntaxOver.{u, u, u, u + 1} PUnit (fun (_ : Type u) => BundledMonad.{u, u}) where
  Node _ (X : Type u) bm (Cont : X → Type u) :=
    (x : X) × bm.M (Cont x)

/-- One-step execution law for `Strategy.monadicSyntax`.

The node selects the next move directly. Its continuation is lifted from the
decorated node monad into the ambient execution monad before the generic runner
continues with the selected subtree. -/
def Strategy.monadicInteraction {m : Type u → Type u} [Monad m]
    (liftM : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α) :
    InteractionOver PUnit (fun (_ : Type u) => BundledMonad.{u, u}) Strategy.monadicSyntax m where
  interact := fun {_X} {γ} {_Cont} {_Result} profile k => do
    let node := profile PUnit.unit
    let next ← liftM γ node.2
    k node.1 (fun _ => next)

end Spec
end Interaction
