/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.BundledMonad
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Strategy

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
