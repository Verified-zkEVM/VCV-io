/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio

/-!
# `vcgen` name-collision canary

Core Lean ships a tactic spelled `vcgen` (`Std.Tactic.Do`), and VCVio's program logic ships its
own `vcgen` (`VCVio.ProgramLogic.Tactics.Unary`). Both are in scope in any file that imports the
root `VCVio` module, because the `Std.Do` bridges under `VCVio/ProgramLogic/Unary/` import
core's syntax. The parser then produces a `choice` node and the elaborator tries the
alternatives in turn; this file pins the behaviour that VCVio proofs rely on, namely that a
`wp`-triple goal is still closed by `vcgen` in that setting. If a toolchain bump makes the choice
node stop falling through (an error from core's `vcgen` no longer counts as "try the next
alternative"), this file fails first, and the fix is the planned rename of VCVio's tactic
rather than a reorder of imports.
-/

public section

open ENNReal OracleSpec OracleComp
open Lean.Order
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic

namespace VCVioTest.VCGenAmbiguity

universe u

variable {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}

example (oa : OracleComp spec α) (post : Nat × α → Nat → ℝ≥0∞) :
    ⦃fun s => wp⟦oa⟧ (fun a => post (s, a) (s + 1))⦄
      (do
        let s ← (MonadStateOf.get : StateT Nat (OracleComp spec) Nat)
        MonadStateOf.set (s + 1)
        let a ← (MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)
        pure (s, a))
    ⦃post⦄ := by
  vcgen

example (s' : Nat) (oa : OracleComp spec α) (post : α → Nat → ℝ≥0∞) :
    ⦃fun _ => wp⟦oa⟧ (fun a => post a s')⦄
      (do
        MonadStateOf.set s'
        MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)
    ⦃post⦄ := by
  vcgen

end VCVioTest.VCGenAmbiguity
