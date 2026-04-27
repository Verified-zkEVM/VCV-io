/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.Algebra
import ToMathlib.Control.StateT
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist
import Loom.WP.Basic
import Loom.Triple.Basic

/-!
# Quantitative `WP` carrier for `OracleComp` (Loom2 default)

This file is the **home** of the quantitative algebra structure on
`OracleComp spec` valued in `ℝ≥0∞`, plus its registration as the
default `Std.Do'.WP (OracleComp spec) ℝ≥0∞ EPost.nil` instance.

It provides three layers:

1. **Expectation algebra** — `μ : OracleComp spec ℝ≥0∞ → ℝ≥0∞` and the
   legacy `MAlgOrdered (OracleComp spec) ℝ≥0∞` instance. These remain
   the structural root for `OracleComp.ProgramLogic.wp` / `.Triple` and
   the relational eRHL stack until the irreversible Commit 8 prunes
   `MAlgOrdered`.
2. **`Lean.Order` adapters for `ℝ≥0∞`** — bridges Mathlib's `≤` and
   `sSup` to Lean core's `Lean.Order.{PartialOrder, CompleteLattice}`,
   which Loom2 builds on. `Prop` ships with its own adapters in
   `Loom/LatticeExt.lean`.
3. **`Std.Do'.WP` instance** — the canonical entry point for new
   program-logic developments. Its `wpTrans` wraps the existing
   `MAlgOrdered.wp`, so the keystone alignment lemma
   `wp_eq_mAlgOrdered_wp` holds by `rfl`.

## Layout

This is one of three `WP` carriers we register on `OracleComp`. Because
`Std.Do'.WP`'s `Pred` and `EPred` are `outParam`s, only one carrier can
be *visible* to instance synthesis at a time. We register them
asymmetrically:

* This file (`Loom/Quantitative.lean`) — the `ℝ≥0∞` carrier as a normal
  `instance`, always live once the file is imported. This is the default.
* `Loom/Qualitative.lean` — the `Prop` carrier as a `scoped instance`
  under `namespace OracleComp.Qualitative`, opt-in via
  `open OracleComp.Qualitative`.
* `Loom/Probabilistic.lean` — the `Prob` carrier as a `scoped instance`
  under `namespace OracleComp.Probabilistic`, opt-in via
  `open OracleComp.Probabilistic`.

There is no umbrella `Unary/Loom.lean` re-export. Consumers import the
specific carrier they need. This makes the carrier choice explicit at
every import site.

## Loom2 vs. Mathlib lattice plumbing

Loom2 builds on `Lean.Order.{PartialOrder, CompleteLattice, CCPO}` from
`Init.Internal.Order`, a class hierarchy distinct from Mathlib's
`Order.{PartialOrder, CompleteLattice}`. We provide the narrow `ℝ≥0∞`
adapters here.

When Volo's PR #12965 lands upstream and the `Std.Do.{WP,…}` API
stabilizes, this bridge collapses to a re-export and the lattice
adapters can move to a shared `ToMathlib/Order/LeanOrderAdapter.lean`.
-/

open ENNReal
open Std.Do'

universe u

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β : Type}

/-! ## Expectation algebra and the `MAlgOrdered` instance -/

/-- Expectation-style algebra for oracle computations returning `ℝ≥0∞`. -/
noncomputable def μ (oa : OracleComp spec ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, Pr[= x | oa] * x

lemma μ_bind_eq_tsum {α : Type}
    (oa : OracleComp spec α) (ob : α → OracleComp spec ℝ≥0∞) :
    μ (oa >>= ob) = ∑' x, Pr[= x | oa] * μ (ob x) := by
  unfold μ
  calc
    (∑' y, Pr[= y | oa >>= ob] * y)
        = (∑' y, (∑' x, Pr[= x | oa] * Pr[= y | ob x]) * y) := by
            refine tsum_congr ?_
            intro y
            rw [probOutput_bind_eq_tsum]
    _ = (∑' y, ∑' x, (Pr[= x | oa] * Pr[= y | ob x]) * y) := by
          refine tsum_congr ?_
          intro y
          rw [ENNReal.tsum_mul_right]
    _ = ∑' x, ∑' y, (Pr[= x | oa] * Pr[= y | ob x]) * y := by
          rw [ENNReal.tsum_comm]
    _ = ∑' x, Pr[= x | oa] * ∑' y, Pr[= y | ob x] * y := by
          refine tsum_congr ?_
          intro x
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr ?_
          intro y
          rw [mul_assoc]
    _ = ∑' x, Pr[= x | oa] * μ (ob x) := rfl

noncomputable instance instMAlgOrdered :
    MAlgOrdered (OracleComp spec) ℝ≥0∞ where
  μ := μ (spec := spec)
  μ_pure x := by
    haveI : DecidableEq ℝ≥0∞ := Classical.decEq _
    simp [μ, probOutput_pure]
  μ_bind_mono f g hfg x := by
    rw [μ_bind_eq_tsum (oa := x) (ob := f), μ_bind_eq_tsum (oa := x) (ob := g)]
    refine ENNReal.tsum_le_tsum ?_
    intro a
    simpa [mul_comm] using (mul_le_mul_right (hfg a) (Pr[= a | x]))

end OracleComp.ProgramLogic

/-! ## `Lean.Order` adapters for `ℝ≥0∞`

Loom2's `Std.Do'.WP m Pred EPred` requires `Assertion Pred` (a class
abbrev for `Lean.Order.CompleteLattice`). We bridge Mathlib's order
structure on `ℝ≥0∞` to Lean core's lattice hierarchy here. -/

namespace OracleComp.ProgramLogic.Loom

/-- Bridge Mathlib's `≤` on `ℝ≥0∞` to `Lean.Order.PartialOrder`. -/
instance : Lean.Order.PartialOrder ℝ≥0∞ where
  rel a b := a ≤ b
  rel_refl := le_refl _
  rel_trans h₁ h₂ := le_trans h₁ h₂
  rel_antisymm := le_antisymm

/-- Bridge Mathlib's `sSup` on `ℝ≥0∞` to `Lean.Order.CompleteLattice`.

`Lean.Order.CompleteLattice.has_sup c` requires a least upper bound for
the predicate-encoded set `{x | c x}`. We discharge it with Mathlib's
`sSup` specialization. -/
instance : Lean.Order.CompleteLattice ℝ≥0∞ where
  has_sup c := by
    refine ⟨sSup {x | c x}, fun x => ?_⟩
    constructor
    · intro hsup y hcy
      have hle : y ≤ sSup {x | c x} := le_sSup (a := y) hcy
      exact le_trans hle hsup
    · intro h
      exact sSup_le (fun y hy => h y hy)

end OracleComp.ProgramLogic.Loom

/-! ## `Lean.Order.CCPO` instance for `Std.Do'.EPost.nil`

Loom2's Hoare-triple notation `⦃ pre ⦄ x ⦃ post ⦄` (defined in
`Loom.Triple.Basic`) expands to `Std.Do'.Triple pre x post ⊥` where
`⊥` is the `Lean.Order.CCPO`-bottom (`Lean.Order.bot`). For monads
with no exception layer, the `EPred` is `Std.Do'.EPost.nil`, which
Loom2 ships only with a `Lean.Order.CompleteLattice` instance, not a
`CCPO` one. (`CCPO` and `CompleteLattice` are independent sibling
classes in Lean core's `Init.Internal.Order`.)

We provide the missing `CCPO` instance here. `EPost.nil` is a
single-element type, so the chain-supremum is trivial: every chain has
the unique element `EPost.nil.mk` as its least upper bound. -/

namespace Std.Do'

instance : Lean.Order.CCPO EPost.nil where
  has_csup _ := ⟨EPost.nil.mk, fun _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩

end Std.Do'

namespace OracleComp.ProgramLogic.Loom

/-! ## `Std.Do'.WP` instance for `OracleComp` -/

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β : Type}

/-- Quantitative `Std.Do'.WP` interpretation of `OracleComp spec` valued in `ℝ≥0∞`.

The `wpTrans` is the existing `MAlgOrdered.wp` (i.e. expectation of
`post` under `evalDist`); the `EPost.nil` argument is ignored since
`OracleComp` has no first-class exception slot. The three `WP` axioms
reduce to the existing `MAlgOrdered.{wp_pure, wp_bind, wp_mono}`
equalities. -/
noncomputable instance instWP :
    Std.Do'.WP (OracleComp spec) ℝ≥0∞ Std.Do'.EPost.nil where
  wpTrans x := ⟨fun post _epost =>
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) x post⟩
  wp_trans_pure x := by
    intro post _epost
    change post x ≤ MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (pure x) post
    rw [MAlgOrdered.wp_pure]
  wp_trans_bind x f := by
    intro post _epost
    change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) x
            (fun a => MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (f a) post) ≤
          MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (x >>= f) post
    rw [MAlgOrdered.wp_bind]
  wp_trans_monotone x := by
    intro post post' _epost _epost' _hepost hpost
    exact MAlgOrdered.wp_mono (m := OracleComp spec) (l := ℝ≥0∞) x hpost

/-! ## Definitional alignment with `MAlgOrdered.wp`

The keystone lemma confirms `Std.Do'.wp` agrees with `MAlgOrdered.wp`
on the nose, so every existing quantitative `wp_*` theorem in
`HoareTriple.lean` transports for free when the user rewrites
`Std.Do'.wp _ _ _ ↦ MAlgOrdered.wp _ _`.

The epost argument is `⊥` to match Loom2's `⦃ _ ⦄ _ ⦃ _ ⦄` notation in
`Loom.Triple.Basic`. The `WP` instance for `OracleComp` ignores the
epost argument entirely, so any element of `EPost.nil` would yield the
same value. -/

theorem wp_eq_mAlgOrdered_wp
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Std.Do'.wp oa post Lean.Order.bot =
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa post := rfl

/-! ## `StateT (OracleComp spec)` WP normalization -/

@[simp]
theorem wp_StateT_bind {σ : Type} (x : StateT σ (OracleComp spec) α)
    (f : α → StateT σ (OracleComp spec) β) (post : β → σ → ℝ≥0∞) :
    Std.Do'.wp (StateT.bind x f) post Lean.Order.bot =
      fun s => Std.Do'.wp x (fun a s' => Std.Do'.wp (f a) post Lean.Order.bot s')
        Lean.Order.bot s := by
  funext s
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) ((x >>= f).run s)
      (fun p : β × σ => post p.1 p.2) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (x.run s)
      (fun p : α × σ =>
        MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) ((f p.1).run p.2)
          (fun q : β × σ => post q.1 q.2))
  rw [StateT.run_bind, MAlgOrdered.wp_bind]

@[simp]
theorem wp_StateT_bind' {σ : Type} (x : StateT σ (OracleComp spec) α)
    (f : α → StateT σ (OracleComp spec) β) (post : β → σ → ℝ≥0∞) :
    Std.Do'.wp (x >>= f) post Lean.Order.bot =
      fun s => Std.Do'.wp x (fun a s' => Std.Do'.wp (f a) post Lean.Order.bot s')
        Lean.Order.bot s := by
  exact wp_StateT_bind x f post

@[simp]
theorem wp_StateT_pure {σ : Type} (x : α) (post : α → σ → ℝ≥0∞) :
    Std.Do'.wp (pure x : StateT σ (OracleComp spec) α) post Lean.Order.bot =
      fun s => post x s := by
  funext s
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (pure (x, s) : OracleComp spec (α × σ))
      (fun p : α × σ => post p.1 p.2) = post x s
  rw [MAlgOrdered.wp_pure]

@[simp]
theorem wp_StateT_get {σ : Type} (post : σ → σ → ℝ≥0∞) :
    Std.Do'.wp (MonadStateOf.get : StateT σ (OracleComp spec) σ) post Lean.Order.bot =
      fun s => post s s := by
  funext s
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (pure (s, s) : OracleComp spec (σ × σ))
      (fun p : σ × σ => post p.1 p.2) = post s s
  rw [MAlgOrdered.wp_pure]

@[simp]
theorem wp_StateT_set {σ : Type} (s' : σ) (post : PUnit → σ → ℝ≥0∞) :
    Std.Do'.wp (MonadStateOf.set s' : StateT σ (OracleComp spec) PUnit) post
      Lean.Order.bot = fun _ => post ⟨⟩ s' := by
  funext s
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (pure (PUnit.unit, s') : OracleComp spec (PUnit × σ))
      (fun p : PUnit × σ => post p.1 p.2) = post ⟨⟩ s'
  rw [MAlgOrdered.wp_pure]

@[simp]
theorem wp_StateT_modifyGet {σ : Type} (f : σ → α × σ) (post : α → σ → ℝ≥0∞) :
    Std.Do'.wp (MonadStateOf.modifyGet f : StateT σ (OracleComp spec) α) post
      Lean.Order.bot = fun s => post (f s).1 (f s).2 := by
  funext s
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (pure (f s) : OracleComp spec (α × σ))
      (fun p : α × σ => post p.1 p.2) = post (f s).1 (f s).2
  rw [MAlgOrdered.wp_pure]

@[simp]
theorem wp_StateT_monadLift {σ : Type} (oa : OracleComp spec α)
    (post : α → σ → ℝ≥0∞) :
    Std.Do'.wp (MonadLift.monadLift oa : StateT σ (OracleComp spec) α) post
      Lean.Order.bot = fun s => Std.Do'.wp oa (fun a => post a s) Lean.Order.bot := by
  funext s
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (oa >>= fun a => pure (a, s))
      (fun p : α × σ => post p.1 p.2) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa (fun a => post a s)
  rw [MAlgOrdered.wp_bind]
  refine congrArg (MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa) ?_
  funext a
  rw [MAlgOrdered.wp_pure]

/-- `Std.Do'.Triple` agrees with `MAlgOrdered.Triple` propositionally.

Use as a forward iff: `triple_iff_mAlgOrdered_triple.mp` extracts
`pre ≤ MAlgOrdered.wp …` from a `Std.Do'.Triple`, and `.mpr` packages
it back. The two are *not* definitionally equal because `Std.Do'.Triple`
is an inductive wrapper rather than a `def` over `≤`. -/
theorem triple_iff_mAlgOrdered_triple
    (pre : ℝ≥0∞) (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Std.Do'.Triple pre oa post Lean.Order.bot ↔
      MAlgOrdered.Triple (m := OracleComp spec) (l := ℝ≥0∞) pre oa post :=
  Std.Do'.Triple.iff

end OracleComp.ProgramLogic.Loom
