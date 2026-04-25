/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Loom.WP.Basic
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Probabilistic `WP` carrier for `OracleComp` (`Prob`, scoped)

Installs the probabilistic `Std.Do'.WP (OracleComp spec) Prob EPost.nil`
instance, where `Prob = { x : ℝ≥0∞ // x ≤ 1 }` is the unit interval as a
subtype of `ℝ≥0∞`. Sitting between the qualitative `Prop` carrier and
the quantitative `ℝ≥0∞` carrier, this tier is the natural home for
probability-bounded reasoning: union bound, complement
(`1 - p` involution), Bayes, independence, advantage / negligibility.

The carrier is a `noncomputable scoped instance` under `namespace
OracleComp.Probabilistic`. Consumers `open` the namespace to enable it.

## Why a separate tier (rather than `ℝ≥0∞` with side conditions)?

In pure `ℝ≥0∞`:

* `1 - (1 - p) = p` only when `p ≤ 1`; the side condition is implicit
  at every step.
* Union bound `Pr[A ∪ B] ≤ Pr[A] + Pr[B]` requires threading
  `(· : Prop → ℝ≥0∞)` indicator coercions through every step.
* Game-hopping uses signed differences `|Pr[A] - Pr[B]|`; in `ℝ≥0∞` you
  build `|·|` out of `max - min`.
* Negligibility lives in `[0,1]` morally; our `Negligible` machinery in
  `Asymptotics/` already silently assumes `≤ 1`.

`Prob` makes all of these direct, and lets tactic registries
(`@[wpStep]`, `@[vcspec]`) be partitioned by tier so that `wp_prob`
goals never invoke `Markov` / `KL_div` lemmas.

See `.ignore/wp-cutover-plan.md` §"Three-tier carrier design" for the
broader story (Galois connections, coherence lemmas).
-/

universe u

open ENNReal Std.Do'

/-! ## The `Prob` carrier

`Prob` is the closed unit interval `[0, 1] ⊆ ℝ≥0∞`. It is a complete
bounded lattice under the inherited `≤` from `ℝ≥0∞`, with sup of any
predicate-encoded subset given by `sSup` (clamped at `1`, but the bound
follows for free since every element is already `≤ 1`).
-/

/-- The closed unit interval `[0, 1]` as a subtype of `ℝ≥0∞`.

Used as the carrier for the probabilistic `Std.Do'.WP` interpretation of
`OracleComp` (see `OracleComp.Probabilistic.instWP_prob`). The
`Subtype.val` coercion to `ℝ≥0∞` is free, so probabilistic statements
re-export to the quantitative carrier without duplication. -/
def Prob : Type := { x : ℝ≥0∞ // x ≤ 1 }

namespace Prob

/-- Underlying `ℝ≥0∞` value. -/
@[coe] def val (p : Prob) : ℝ≥0∞ := p.1

instance : Coe Prob ℝ≥0∞ := ⟨val⟩

@[ext] theorem ext {p q : Prob} (h : p.val = q.val) : p = q := Subtype.ext h

/-- The `≤ 1` witness for any `Prob`. -/
theorem val_le_one (p : Prob) : p.val ≤ 1 := p.2

instance : Zero Prob := ⟨⟨0, zero_le_one⟩⟩
instance : One Prob := ⟨⟨1, le_refl _⟩⟩

@[simp] theorem val_zero : (0 : Prob).val = 0 := rfl
@[simp] theorem val_one : (1 : Prob).val = 1 := rfl

/-- Indicator coercion from a decidable proposition to `Prob`: `1` if `p`
holds, `0` otherwise. Used to lift a qualitative post `α → Prop` into a
probabilistic post `α → Prob`, as in
`OracleComp.Loom.Coherence.wp_qual_iff_wp_prob_indicator_eq_one`. -/
def indicator (p : Prop) [Decidable p] : Prob :=
  ⟨if p then 1 else 0, by split_ifs <;> simp⟩

@[simp] theorem val_indicator (p : Prop) [Decidable p] :
    (indicator p).val = if p then 1 else 0 := rfl

/-! ### `Lean.Order` instances

Loom2 builds on `Lean.Order.{PartialOrder, CompleteLattice}` from Lean
core's `Init.Internal.Order`. We provide the bridges for `Prob` here;
the pattern mirrors `…/Loom/Quantitative.lean` for `ℝ≥0∞`. -/

/-- Bridge `Subtype` ordering on `Prob` to `Lean.Order.PartialOrder`.

Definitionally, `a ⊑ b ↔ a.val ≤ b.val`, so `change a.val ≤ b.val`
unfolds the `Lean.Order.PartialOrder.rel` projection at proof sites. -/
instance instPartialOrder : Lean.Order.PartialOrder Prob where
  rel a b := a.val ≤ b.val
  rel_refl := le_refl _
  rel_trans h₁ h₂ := le_trans h₁ h₂
  rel_antisymm h₁ h₂ := ext (le_antisymm h₁ h₂)

/-- Underlying `ℝ≥0∞` set for a `Prob`-valued predicate. -/
private def valImage (c : Prob → Prop) : Set ℝ≥0∞ :=
  {x : ℝ≥0∞ | ∃ p : Prob, c p ∧ p.val = x}

/-- Supremum on `Prob` of a predicate-encoded subset.

The supremum on `ℝ≥0∞` of any subset of `[0,1]` is itself in `[0,1]`,
since `sSup` is monotone and bounded above by `1`. -/
noncomputable def probSup (c : Prob → Prop) : Prob :=
  ⟨sSup (valImage c),
    sSup_le (by rintro x ⟨p, _, rfl⟩; exact p.val_le_one)⟩

theorem probSup_is_sup (c : Prob → Prop) : Lean.Order.is_sup c (probSup c) := by
  intro y
  refine ⟨?_, ?_⟩
  · -- (probSup c) ⊑ y → ∀ z, c z → z ⊑ y
    intro hsup z hcz
    -- hsup : (probSup c).val ≤ y.val (via the Prob PartialOrder.rel)
    -- goal : z.val ≤ y.val
    change z.val ≤ y.val
    have hle : z.val ≤ (probSup c).val := le_sSup ⟨z, hcz, rfl⟩
    exact le_trans hle (by change (probSup c).val ≤ y.val at hsup; exact hsup)
  · -- (∀ z, c z → z ⊑ y) → (probSup c) ⊑ y
    intro h
    change (probSup c).val ≤ y.val
    refine sSup_le ?_
    rintro x ⟨p, hcp, rfl⟩
    exact (show p.val ≤ y.val from h p hcp)

/-- Bridge `sSup` on `Prob` to `Lean.Order.CompleteLattice`.

The least upper bound of any predicate-encoded subset of `Prob` exists
(it is the `sSup` in `ℝ≥0∞` of the underlying values, which lands in
`[0,1]` because every member already does). -/
noncomputable instance instCompleteLattice : Lean.Order.CompleteLattice Prob where
  has_sup c := ⟨probSup c, probSup_is_sup c⟩

end Prob

/-! ## `WP` instance for `OracleComp`

The probabilistic WP wraps the existing quantitative `MAlgOrdered.wp`
post-composed with the `Prob` constructor. The `≤ 1` bound is witnessed
by monotonicity of `MAlgOrdered.wp` against the constant-`1` post,
which evaluates to `1` on `OracleComp` (since `OracleComp` has
`HasEvalPMF`, a true probability monad). -/

namespace OracleComp.Probabilistic

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β : Type}

/-- The underlying `ℝ≥0∞`-valued WP, packaged for use inside the `Prob`
constructor. -/
private noncomputable def wpVal (oa : OracleComp spec α) (post : α → Prob) : ℝ≥0∞ :=
  MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa (fun a => (post a).val)

private theorem wpVal_le_one (oa : OracleComp spec α) (post : α → Prob) :
    wpVal oa post ≤ 1 := by
  unfold wpVal
  calc MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa (fun a => (post a).val)
      ≤ MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa (fun _ => 1) :=
        MAlgOrdered.wp_mono (m := OracleComp spec) (l := ℝ≥0∞) oa
          (fun a => (post a).val_le_one)
    _ = 1 := OracleComp.ProgramLogic.wp_const oa 1

/-- Probabilistic `Std.Do'.WP` interpretation of `OracleComp spec` valued in
`Prob = [0, 1] ⊆ ℝ≥0∞`.

The `wpTrans` is the existing quantitative `MAlgOrdered.wp` evaluated on
`Prob`-valued postconditions and packaged into `Prob` via the `≤ 1`
bound. The `EPost.nil` argument is ignored since `OracleComp` has no
first-class exception slot.

This is a `scoped instance` rather than a normal `instance`: only one
`Std.Do'.WP (OracleComp spec) _ _` instance can be visible at a time
(`Pred` is an `outParam`), and the default is the quantitative `ℝ≥0∞`
carrier. Open `OracleComp.Probabilistic` to switch into the
probabilistic carrier. -/
noncomputable scoped instance (priority := 1100) instWP_prob :
    Std.Do'.WP (OracleComp spec) Prob Std.Do'.EPost.nil where
  wpTrans oa := ⟨fun post _epost =>
    ⟨wpVal oa post, wpVal_le_one oa post⟩⟩
  wp_trans_pure x := by
    intro post _epost
    change (post x).val ≤ wpVal (pure x) post
    unfold wpVal
    rw [MAlgOrdered.wp_pure]
  wp_trans_bind oa f := by
    intro post _epost
    change wpVal oa (fun a => ⟨wpVal (f a) post, wpVal_le_one (f a) post⟩) ≤
            wpVal (oa >>= f) post
    unfold wpVal
    rw [MAlgOrdered.wp_bind]
    rfl
  wp_trans_monotone oa := by
    intro post post' _epost _epost' _hepost hpost
    change wpVal oa post ≤ wpVal oa post'
    unfold wpVal
    exact MAlgOrdered.wp_mono (m := OracleComp spec) (l := ℝ≥0∞) oa
      (fun a => (show (post a).val ≤ (post' a).val from hpost a))

/-! ## Definitional alignment with `MAlgOrdered.wp` (Prob)

The keystone lemma confirms that the underlying `ℝ≥0∞` value of
`Std.Do'.wp` agrees with the quantitative `MAlgOrdered.wp` on the nose,
so quantitative theorems still apply after coercing through `.val`. -/

theorem wp_val_eq_mAlgOrdered_wp
    (oa : OracleComp spec α) (post : α → Prob) :
    (Std.Do'.wp oa post Lean.Order.bot).val =
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa (fun a => (post a).val) := rfl

end OracleComp.Probabilistic
