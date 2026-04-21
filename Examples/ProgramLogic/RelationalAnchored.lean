/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.Quantitative
import ToMathlib.Control.Monad.RelationalAlgebraAnchored

/-!
# Honest Exception Relational WP Examples

Demonstrates the derived combinators `rwpExc`, `rwpExcLeft`, `rwpExcRight`, `rwpOpt`,
`rwpOptLeft`, and `rwpOptRight` from `ToMathlib.Control.Monad.RelationalAlgebraAnchored`.
These honest variants distinguish exception/`none` outcomes per side, in contrast to the
default `instExceptTLeft` / `instOptionTLeft` couplings, which collapse all failure mass
to `⊥`.

The `MAlgRelOrdered.Anchored` instance for two `OracleComp` monads (proved in
`VCVio.ProgramLogic.Relational.Quantitative` for `ℝ≥0∞`) is what makes the cross-corner
reductions and the bind laws available.
-/

universe u

namespace OracleComp.ProgramLogic.AnchoredExamples

open ENNReal MAlgRelOrdered MAlgRelOrdered.Anchored

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]

/-! ## Pure-pure base cases -/

/-- Two `pure ok` programs hit the `(ok, ok)` corner exactly. -/
example {α β ε₁ ε₂ : Type} (a : α) (b : β)
    (postOO : α → β → ℝ≥0∞) (postEO : ε₁ → β → ℝ≥0∞)
    (postOE : α → ε₂ → ℝ≥0∞) (postEE : ε₁ → ε₂ → ℝ≥0∞) :
    rwpExc (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := ℝ≥0∞)
        (pure a : ExceptT ε₁ (OracleComp spec₁) α)
        (pure b : ExceptT ε₂ (OracleComp spec₂) β)
        postOO postEO postOE postEE = postOO a b := by
  simp

/-- A `throw` on the left lands in the `(error, ok)` corner. -/
example {α β ε₁ ε₂ : Type} (e : ε₁) (b : β)
    (postOO : α → β → ℝ≥0∞) (postEO : ε₁ → β → ℝ≥0∞)
    (postOE : α → ε₂ → ℝ≥0∞) (postEE : ε₁ → ε₂ → ℝ≥0∞) :
    rwpExc (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := ℝ≥0∞)
        (throw e : ExceptT ε₁ (OracleComp spec₁) α)
        (pure b : ExceptT ε₂ (OracleComp spec₂) β)
        postOO postEO postOE postEE = postEO e b := by
  simp

/-- Both sides throw: hits the `(error, error)` corner. -/
example {α β ε₁ ε₂ : Type} (e₁ : ε₁) (e₂ : ε₂)
    (postOO : α → β → ℝ≥0∞) (postEO : ε₁ → β → ℝ≥0∞)
    (postOE : α → ε₂ → ℝ≥0∞) (postEE : ε₁ → ε₂ → ℝ≥0∞) :
    rwpExc (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := ℝ≥0∞)
        (throw e₁ : ExceptT ε₁ (OracleComp spec₁) α)
        (throw e₂ : ExceptT ε₂ (OracleComp spec₂) β)
        postOO postEO postOE postEE = postEE e₁ e₂ := by
  simp

/-! ## Anchored pure-side reductions -/

/-- When the left side is a literal `pure ok`, the relational WP reduces to a unary
honest exception WP on the right side. -/
example {α β ε₁ ε₂ : Type} (a : α) (y : ExceptT ε₂ (OracleComp spec₂) β)
    (postOO : α → β → ℝ≥0∞) (postEO : ε₁ → β → ℝ≥0∞)
    (postOE : α → ε₂ → ℝ≥0∞) (postEE : ε₁ → ε₂ → ℝ≥0∞) :
    rwpExc (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := ℝ≥0∞)
        (pure a : ExceptT ε₁ (OracleComp spec₁) α) y postOO postEO postOE postEE =
      MAlgOrdered.wpExc y (postOO a) (postOE a) :=
  rwpExc_pure_left a y postOO postEO postOE postEE

/-- A `throw` on the left collapses the relational WP to a unary WP that ignores the
left's `α` outcome and only sees the (left error, right outcome) postconditions. -/
example {α β ε₁ ε₂ : Type} (e : ε₁) (y : ExceptT ε₂ (OracleComp spec₂) β)
    (postOO : α → β → ℝ≥0∞) (postEO : ε₁ → β → ℝ≥0∞)
    (postOE : α → ε₂ → ℝ≥0∞) (postEE : ε₁ → ε₂ → ℝ≥0∞) :
    rwpExc (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := ℝ≥0∞)
        (throw e : ExceptT ε₁ (OracleComp spec₁) α) y postOO postEO postOE postEE =
      MAlgOrdered.wpExc y (postEO e) (postEE e) :=
  rwpExc_throw_left e y postOO postEO postOE postEE

/-! ## One-sided combinators -/

/-- `rwpExcLeft` distinguishes left ok / left error per the right's value. -/
example {α β ε : Type} (a : α) (y : OracleComp spec₂ β)
    (postOk : α → β → ℝ≥0∞) (postErr : ε → β → ℝ≥0∞) :
    rwpExcLeft (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := ℝ≥0∞)
        (pure a : ExceptT ε (OracleComp spec₁) α) y postOk postErr =
      MAlgOrdered.wp y (postOk a) :=
  rwpExcLeft_pure_left a y postOk postErr

/-- A `throw` on the left in `rwpExcLeft` collapses to a unary WP using the error
postcondition. -/
example {α β ε : Type} (e : ε) (y : OracleComp spec₂ β)
    (postOk : α → β → ℝ≥0∞) (postErr : ε → β → ℝ≥0∞) :
    rwpExcLeft (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := ℝ≥0∞)
        (throw e : ExceptT ε (OracleComp spec₁) α) y postOk postErr =
      MAlgOrdered.wp y (postErr e) :=
  rwpExcLeft_throw_left e y postOk postErr

/-! ## OptionT combinators -/

/-- A `pure none` (i.e., `failure`) on the left of `rwpOpt` collapses to a unary `wpOpt`
on the right side using the `(none, ?)` corner postconditions. -/
example {α β : Type} (y : OptionT (OracleComp spec₂) β)
    (postSS : α → β → ℝ≥0∞) (postSN : α → ℝ≥0∞)
    (postNS : β → ℝ≥0∞) (postNN : ℝ≥0∞) :
    rwpOpt (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := ℝ≥0∞)
        (OptionT.mk (pure none) : OptionT (OracleComp spec₁) α) y postSS postSN postNS postNN =
      MAlgOrdered.wpOpt y postNS postNN :=
  rwpOpt_fail_left y postSS postSN postNS postNN

end OracleComp.ProgramLogic.AnchoredExamples
