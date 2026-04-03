/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Unary

/-!
# Probability Rewrite Tactic Examples

This file validates probability-rewrite tactics from
`VCVio.ProgramLogic.Tactics`: `vcstep rw`, `vcstep rw under`,
`vcstep rw congr`, `vcstep rw congr'`, and the exhaustive `vcgen` driver
on `Pr[...] = Pr[...]` goals.
-/

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
variable {α β γ δ ε : Type}

/-! ## Congruence -/

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ support mx, Pr[= y | f x] = Pr[= y | g x]) :
    Pr[= y | mx >>= f] = Pr[= y | mx >>= g] := by
  vcstep
  exact h _ ‹_›

/-! ## Bind swap -/

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {y : γ} :
    Pr[= y | mx >>= fun a => my >>= fun b => f a b] =
    Pr[= y | my >>= fun b => mx >>= fun a => f a b] := by
  vcstep rw

/-! ## `rw under` -/

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {mz : OracleComp spec γ} {f : α → β → γ → OracleComp spec δ} {y : δ} :
    Pr[= y | mx >>= fun a => my >>= fun b => mz >>= fun c => f a b c] =
    Pr[= y | mx >>= fun a => mz >>= fun c => my >>= fun b => f a b c] := by
  vcstep rw under 1

example {mw : OracleComp spec α} {mx : OracleComp spec β}
    {my : OracleComp spec γ} {mz : OracleComp spec δ}
    {f : α → β → γ → δ → OracleComp spec ε} {out : ε} :
    Pr[= out | mw >>= fun w => mx >>= fun x => my >>= fun y => mz >>= fun z => f w x y z] =
    Pr[= out | mw >>= fun w => mx >>= fun x => mz >>= fun z => my >>= fun y => f w x y z] := by
  vcstep rw under 2

/-! ## Auto swap detection -/

example {mw : OracleComp spec α} {mx : OracleComp spec β}
    {my : OracleComp spec γ} {mz : OracleComp spec δ}
    {f : α → β → γ → δ → OracleComp spec ε} {out : ε} :
    Pr[= out | mw >>= fun w => mx >>= fun x => my >>= fun y => mz >>= fun z => f w x y z] =
    Pr[= out | mw >>= fun w => mx >>= fun x => mz >>= fun z => my >>= fun y => f w x y z] := by
  vcstep

example {mw : OracleComp spec α} {mx : OracleComp spec β}
    {my : OracleComp spec γ} {mz : OracleComp spec δ}
    {f : α → β → γ → δ → OracleComp spec (Bool × ε)} :
    Pr[= true | do
      let w ← mw
      let x ← mx
      let b ← Prod.fst <$> (do
        let y ← my
        let z ← mz
        f w x y z)
      pure b] =
    Pr[= true | do
      let w ← mw
      let x ← mx
      let b ← Prod.fst <$> (do
        let z ← mz
        let y ← my
        f w x y z)
      pure b] := by
  vcstep

example {mw : OracleComp spec α} {mx : OracleComp spec β} {my : OracleComp spec γ}
    {f : α → β → γ → δ} [DecidableEq δ] {out : δ} :
    Pr[= out | do
      let w ← mw
      let x ← mx
      let z ← f w x <$> my
      pure z] =
    Pr[= out | do
      let x ← mx
      let w ← mw
      let z ← f w x <$> my
      pure z] := by
  vcstep

/-! ## `rw congr` / `rw congr'` -/

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[q | f x] = Pr[q | g x]) :
    Pr[q | mx >>= f] = Pr[q | mx >>= g] := by
  vcstep rw congr'
  exact h _

/-! ## Exhaustive `vcgen` on probability equalities -/

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {q : γ → Prop} :
    Pr[q | mx >>= fun a => my >>= fun b => f a b] =
    Pr[q | my >>= fun b => mx >>= fun a => f a b] := by
  vcgen
