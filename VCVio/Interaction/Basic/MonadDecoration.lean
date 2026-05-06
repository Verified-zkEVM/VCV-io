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

`MonadDecoration spec` assigns a `BundledMonad` to each internal node.

The corresponding one-participant syntax, `Strategy.monadicSyntax`, chooses a
move at a node and places the continuation in the monad recorded by that node.
Use it directly with `StrategyOver` for whole-tree strategies and with
`StrategyOver.run` through `Strategy.monadicInteraction` for execution in an
ambient monad.
-/

universe u

namespace Interaction
namespace Spec

/-- Node-wise choice of monad, as a `Decoration` valued in `BundledMonad`. -/
abbrev MonadDecoration :=
  Decoration (fun (_ : Type u) => BundledMonad)

namespace MonadDecoration

/--
Constant monad decoration: every node in the interaction tree uses the same
bundled monad.

This is the bridge between ordinary single-monad strategies and strategies
whose node effects are described by a `MonadDecoration`.
-/
def constant (bm : BundledMonad.{u, u}) :
    (spec : Spec.{u}) → MonadDecoration.{u, u, u} spec
  | .done => PUnit.unit
  | .node _ rest => ⟨bm, fun x => constant bm (rest x)⟩

/--
Nodewise monad homomorphism between two monad decorations on the same
interaction tree.

At each internal node it gives a lift from the source bundled monad to the
target bundled monad, together with recursive lifts for every continuation
subtree.
-/
def Hom :
    (spec : Spec.{u}) → MonadDecoration.{u, u, u} spec →
      MonadDecoration.{u, u, u} spec → Type (u + 1)
  | .done, _, _ => PUnit
  | .node X rest, ⟨m₁, md₁⟩, ⟨m₂, md₂⟩ =>
      (∀ {α : Type u}, m₁.M α → m₂.M α) ×
        ((x : X) → Hom (rest x) (md₁ x) (md₂ x))

namespace Hom

/-- Identity homomorphism on a monad decoration. -/
def id :
    (spec : Spec.{u}) → (md : MonadDecoration.{u, u, u} spec) →
      Hom spec md md
  | .done, _ => PUnit.unit
  | .node _ rest, ⟨_, mdRest⟩ =>
      ⟨fun x => x, fun x => id (rest x) (mdRest x)⟩

/-- Constant homomorphism induced by a single monad lift. -/
def constant {bm₁ bm₂ : BundledMonad.{u, u}}
    (lift : ∀ {α : Type u}, bm₁.M α → bm₂.M α) :
    (spec : Spec.{u}) →
      Hom spec (MonadDecoration.constant bm₁ spec) (MonadDecoration.constant bm₂ spec)
  | .done => PUnit.unit
  | .node _ rest => ⟨lift, fun x => constant lift (rest x)⟩

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
