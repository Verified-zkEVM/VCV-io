/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import ToMathlib.Control.Monad.RelWP
import VCVio.ProgramLogic.Unary.Loom.Probabilistic
import VCVio.ProgramLogic.Relational.Quantitative

/-!
# Probabilistic `RelWP` carrier for `OracleComp` (`Prob`, scoped)

Installs the probabilistic `Std.Do'.RelWP (OracleComp spec₁)
(OracleComp spec₂) Prob EPost.nil EPost.nil` instance, where `Prob =
{ x : ℝ≥0∞ // x ≤ 1 }` is the unit interval as a subtype of `ℝ≥0∞`
(see `VCVio/ProgramLogic/Unary/Loom/Probabilistic.lean` for the
`Prob` carrier and its `Lean.Order.{PartialOrder, CompleteLattice}`
instances).

Sitting between the qualitative `Prop` carrier and the quantitative
`ℝ≥0∞` carrier, this tier is the natural home for relational
probability-bounded reasoning: pRHL with quantitative slack, apRHL with
ε-budgets that always live in `[0, 1]`, advantage / negligibility on the
relational side.

The carrier is a `noncomputable scoped instance` under `namespace
OracleComp.Rel.Probabilistic`. Consumers `open` the namespace to enable
it. See `.ignore/wp-cutover-plan.md` §"Three-tier carrier design" for
the broader story (Galois connections, coherence lemmas).

## Layout and discipline

Because `Std.Do'.RelWP`'s `Pred`, `EPred₁`, `EPred₂` are `outParam`s,
only one carrier can be visible to instance synthesis at a time. The
default quantitative `ℝ≥0∞` carrier (in `Loom/Quantitative.lean`)
remains a normal `instance` and is always live; this scoped instance
is opt-in via `open OracleComp.Rel.Probabilistic`.

The keystone alignment lemma `rwp_val_eq_eRelWP` confirms the
underlying `ℝ≥0∞` value of `Std.Do'.rwp` agrees with `eRelWP` on the
nose, so quantitative theorems still apply after coercing through
`.val`.
-/

universe u

open ENNReal Std.Do' OracleComp.ProgramLogic.Loom

namespace OracleComp.Rel.Probabilistic

variable {ι₁ ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β γ δ : Type}

/-! ## Bound: `eRelWP` on a `Prob`-valued post is always `≤ 1`

The relational expectation of a `Prob`-valued postcondition is bounded
by `1`: any coupling has total mass `≤ 1`, and pointwise the
postcondition is `≤ 1`. -/

private lemma eRelWP_le_one_of_post_le_one
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → ℝ≥0∞) (hpost : ∀ a b, post a b ≤ 1) :
    OracleComp.ProgramLogic.Relational.eRelWP oa ob post ≤ 1 := by
  unfold OracleComp.ProgramLogic.Relational.eRelWP
  refine iSup_le fun c => ?_
  calc ∑' z : α × β, Pr[= z | c.1] * post z.1 z.2
      ≤ ∑' z : α × β, Pr[= z | c.1] * 1 :=
        ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl (hpost z.1 z.2)
    _ = ∑' z : α × β, Pr[= z | c.1] := by simp
    _ ≤ 1 := by
        rw [tsum_probOutput_eq_sub]
        exact tsub_le_self

/-- The underlying `ℝ≥0∞`-valued relational WP, packaged for use inside
the `Prob` constructor. -/
private noncomputable def rwpVal
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → Prob) : ℝ≥0∞ :=
  OracleComp.ProgramLogic.Relational.eRelWP oa ob (fun a b => (post a b).val)

private theorem rwpVal_le_one
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → Prob) :
    rwpVal oa ob post ≤ 1 :=
  eRelWP_le_one_of_post_le_one oa ob _ (fun a b => (post a b).val_le_one)

/-- Probabilistic `Std.Do'.RelWP` interpretation of pairs of
`OracleComp` programs valued in `Prob = [0, 1] ⊆ ℝ≥0∞`.

The `rwpTrans` is the existing quantitative `eRelWP` evaluated on
`Prob`-valued postconditions and packaged into `Prob` via the `≤ 1`
bound. The two `EPost.nil` arguments are ignored since neither side of
an `OracleComp` pair has a first-class exception slot.

This is a `scoped instance` rather than a normal `instance`: only one
`Std.Do'.RelWP (OracleComp spec₁) (OracleComp spec₂) _ _ _` instance
can be visible at a time (`Pred` is an `outParam`), and the default is
the quantitative `ℝ≥0∞` carrier. Open `OracleComp.Rel.Probabilistic`
to switch into the probabilistic carrier. -/
noncomputable scoped instance (priority := 1100) instRelWP_prob :
    Std.Do'.RelWP (OracleComp spec₁) (OracleComp spec₂) Prob
      Std.Do'.EPost.nil Std.Do'.EPost.nil where
  rwpTrans oa ob post _epost₁ _epost₂ :=
    ⟨rwpVal oa ob post, rwpVal_le_one oa ob post⟩
  rwp_trans_pure a b := by
    intro post _epost₁ _epost₂
    change (post a b).val ≤ rwpVal (pure a : OracleComp spec₁ _) (pure b : OracleComp spec₂ _) post
    unfold rwpVal
    rw [OracleComp.ProgramLogic.Relational.eRelWP_pure]
  rwp_trans_bind_le {α β γ δ} oa ob f g := by
    intro post _epost₁ _epost₂
    change rwpVal oa ob (fun a b => ⟨rwpVal (f a) (g b) post, rwpVal_le_one (f a) (g b) post⟩) ≤
            rwpVal (oa >>= f) (ob >>= g) post
    unfold rwpVal
    exact OracleComp.ProgramLogic.Relational.eRelWP_bind_le
      (spec₁ := spec₁) (spec₂ := spec₂) oa ob f g _
  rwp_trans_monotone {α β} oa ob post post' _epost₁ _epost₁' _epost₂ _epost₂' := by
    intro _h₁ _h₂ hpost
    change rwpVal oa ob post ≤ rwpVal oa ob post'
    unfold rwpVal
    exact OracleComp.ProgramLogic.Relational.eRelWP_mono
      (spec₁ := spec₁) (spec₂ := spec₂)
      (fun a b => (show (post a b).val ≤ (post' a b).val from hpost a b))

/-! ## Definitional alignment with `eRelWP` (Prob)

The keystone lemma confirms that the underlying `ℝ≥0∞` value of
`Std.Do'.rwp` agrees with the quantitative `eRelWP` on the nose, so
quantitative theorems still apply after coercing through `.val`. -/

theorem rwp_val_eq_eRelWP
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (post : α → β → Prob) :
    (Std.Do'.rwp oa ob post Lean.Order.bot Lean.Order.bot).val =
      OracleComp.ProgramLogic.Relational.eRelWP oa ob (fun a b => (post a b).val) := rfl

end OracleComp.Rel.Probabilistic
