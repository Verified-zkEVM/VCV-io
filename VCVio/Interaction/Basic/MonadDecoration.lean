/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.BundledMonad
import VCVio.Interaction.Basic.Decoration

/-!
# Per-node monad decorations

`MonadDecoration spec` assigns a `BundledMonad` to each internal node. `Strategy.withMonads`
generalizes `Strategy` so continuations live in the monad recorded at each node; `runWithMonads`
lifts everything into a single ambient monad.
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

/-- Strategy type where each node's continuation uses the monad from `MonadDecoration`. -/
def Strategy.withMonads :
    (spec : Spec.{u}) → MonadDecoration spec → (Transcript spec → Type u) → Type u
  | .done, _, Output => Output ⟨⟩
  | .node X rest, ⟨bm, dRest⟩, Output =>
      (x : X) × bm.M (withMonads (rest x) (dRest x) (fun p => Output ⟨x, p⟩))

/-- Execute a `withMonads` strategy, lifting each node's bundled monad into `m`. -/
def Strategy.runWithMonads {m : Type u → Type u} [Monad m]
    (liftM : ∀ (bm : BundledMonad) {α : Type u}, bm.M α → m α) :
    (spec : Spec) → (deco : MonadDecoration spec) →
    {Output : Transcript spec → Type u} →
    Strategy.withMonads spec deco Output → m ((tr : Transcript spec) × Output tr)
  | .done, _, _, output => pure ⟨⟨⟩, output⟩
  | .node _ rest, ⟨bm, dRest⟩, _, ⟨x, cont⟩ => do
      let next ← liftM bm cont
      let ⟨tail, out⟩ ← runWithMonads liftM (rest x) (dRest x) next
      return ⟨⟨x, tail⟩, out⟩

end Spec
end Interaction
