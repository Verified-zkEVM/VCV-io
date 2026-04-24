/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Unary.Loom.Quantitative
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Quantitative Hoare triples for `OracleComp`

The user-facing wrappers `wp`/`Triple` for the quantitative (`ℝ≥0∞`) program
logic on `OracleComp spec`. These are routed through the canonical
`Std.Do'.{wp, Triple}` interface (see `Loom/Quantitative.lean` for the
underlying `WP` instance), with `EPost.nil.mk` as the unused exception
postcondition.

* `wp` is a `noncomputable abbrev` over `Std.Do'.wp _ _ EPost.nil.mk`. It
  is *definitionally equal* to `MAlgOrdered.wp` via the keystone
  `wp_eq_mAlgOrdered_wp` (`rfl`), so existing `simp [wp, MAlgOrdered.wp_*]`
  proof patterns continue to fire.
* `Triple` is a `noncomputable abbrev` over `Std.Do'.Triple _ _ _ EPost.nil.mk`.
  Because `Std.Do'.Triple` is an `inductive` wrapper around `pre ⊑ wp …`,
  the alignment with `MAlgOrdered.Triple` is propositional, not
  definitional; we bridge via `triple_iff_mAlgOrdered_triple` and the
  constructor `Std.Do'.Triple.intro`.
-/

open ENNReal
open Std.Do'

universe u

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β σ : Type}

/-! ## API contract

- This unary quantitative interface is instantiated for `OracleComp spec`.
- Probability/evaluation assumptions are `[spec.Fintype]` and `[spec.Inhabited]`.
- The quantitative codomain is fixed to `ℝ≥0∞`.
-/

/-- Quantitative weakest precondition for `OracleComp`.

Definitionally equal to `MAlgOrdered.wp (l := ℝ≥0∞)` via
`OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp` (`rfl`).

The exception postcondition is `Lean.Order.bot`, which Loom2's
`⦃ _ ⦄ _ ⦃ _ ⦄` notation also uses (after `open Lean.Order` at the
top of `Loom.Triple.Basic`). On the empty `EPost.nil` carrier `⊥` and
`EPost.nil.mk` agree as the unique inhabitant; we use the qualified
name to disambiguate from Mathlib's `Bot.bot` notation that's also in
scope here. -/
noncomputable abbrev wp (oa : OracleComp spec α) (post : α → ℝ≥0∞) : ℝ≥0∞ :=
  Std.Do'.wp oa post Lean.Order.bot

/-- Quantitative Hoare-style triple for `OracleComp`.

This is the inductive `Std.Do'.Triple pre oa post Lean.Order.bot`, which
unwraps to `pre ⊑ wp oa post Lean.Order.bot` (i.e. `pre ≤ wp oa post`).
Use `triple_iff_le_wp` (or the bridge
`OracleComp.ProgramLogic.Loom.triple_iff_mAlgOrdered_triple`) to convert
between the inductive shape and the underlying `≤`. The `Lean.Order.bot`
epost matches Loom2's `⦃ _ ⦄ _ ⦃ _ ⦄` notation in `Loom.Triple.Basic`. -/
noncomputable abbrev Triple (pre : ℝ≥0∞) (oa : OracleComp spec α) (post : α → ℝ≥0∞) : Prop :=
  Std.Do'.Triple pre oa post Lean.Order.bot

/-! ## Internal bridges

Two convenience bridges keep the proofs short:

* `wp_def_eq` rewrites `wp` (now `Std.Do'.wp _ _ EPost.nil.mk`) to
  `MAlgOrdered.wp _ _`. They are `rfl`-equal via the `instWP` instance,
  so this is purely a syntactic re-tag for `rw`/`simp`.
* `triple_iff_le_wp` and `Triple.{ofLE, toLE}` bridge the inductive
  `Std.Do'.Triple` to its `≤`-form, since (unlike `wp`) `Triple` is
  *not* definitionally `≤`. -/

theorem wp_def_eq (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp oa post = MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa post := rfl

/-- The new inductive `Triple` unwraps to the `≤`-form against `wp`.

This is the public bridge from the inductive `Std.Do'.Triple` (the new
shape after the Loom2 cutover) to the legacy `pre ≤ wp …` form that
existing `MAlgOrdered`-based proofs are stated against. Use
`triple_iff_le_wp.mp h |>.toLE` (or `Triple.toLE` directly) to extract
the inequality, and `Triple.ofLE` (or `triple_iff_le_wp.mpr`) to package
one back. -/
theorem triple_iff_le_wp
    (pre : ℝ≥0∞) (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Triple pre oa post ↔ pre ≤ wp oa post :=
  Std.Do'.Triple.iff

/-- Construct a `Triple` from the `≤`-form precondition. Mirror of
`Std.Do'.Triple.intro`. -/
@[inline] def Triple.ofLE
    {pre : ℝ≥0∞} {oa : OracleComp spec α} {post : α → ℝ≥0∞}
    (h : pre ≤ wp oa post) : Triple pre oa post :=
  Std.Do'.Triple.intro h

/-- Extract the `≤`-form from a `Triple`. -/
@[inline] def Triple.toLE
    {pre : ℝ≥0∞} {oa : OracleComp spec α} {post : α → ℝ≥0∞}
    (h : Triple pre oa post) : pre ≤ wp oa post :=
  match h with | .intro h => h

/-! ## `wp` lemmas (re-routed through `Std.Do'.wp` definitionally)

`wp` is `noncomputable abbrev` over `Std.Do'.wp _ _ EPost.nil.mk`, which
is `rfl`-equal to `MAlgOrdered.wp _ _` for `OracleComp` (see
`Loom.instWP`). Existing `simp [wp, MAlgOrdered.wp_*]` proofs continue
to fire because `simp` unfolds the abbrev and matches under
definitional equality. -/

@[simp, game_rule] theorem wp_pure (x : α) (post : α → ℝ≥0∞) :
    wp (spec := spec) (pure x) post = post x := by
  rw [wp_def_eq, MAlgOrdered.wp_pure]

@[simp, game_rule] theorem wp_ite (c : Prop) [Decidable c]
    (oa ob : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (spec := spec) (if c then oa else ob) post =
      if c then wp oa post else wp ob post := by
  split_ifs <;> rfl

@[simp, game_rule] theorem wp_dite (c : Prop) [Decidable c]
    (oa : c → OracleComp spec α) (ob : ¬c → OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (spec := spec) (dite c oa ob) post =
      dite c (fun h => wp (oa h) post) (fun h => wp (ob h) post) := by
  split_ifs <;> rfl

@[game_rule] theorem wp_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (post : β → ℝ≥0∞) :
    wp (spec := spec) (oa >>= ob) post =
      wp oa (fun x => wp (ob x) post) := by
  simp only [wp_def_eq]
  exact MAlgOrdered.wp_bind (m := OracleComp spec) (l := ℝ≥0∞) oa ob post

@[game_rule] theorem wp_replicate_zero (oa : OracleComp spec α) (post : List α → ℝ≥0∞) :
    wp (spec := spec) (oa.replicate 0) post = post [] := by
  simp [OracleComp.replicate_zero]

@[game_rule] theorem wp_replicate_succ
    (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp (spec := spec) (oa.replicate (n + 1)) post =
      wp oa (fun x => wp (oa.replicate n) (fun xs => post (x :: xs))) := by
  rw [OracleComp.replicate_succ_bind, wp_bind]
  congr 1
  funext x
  rw [wp_bind]
  simp

@[game_rule] theorem wp_list_mapM_nil
    (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp (spec := spec) (([] : List α).mapM f) post = post [] := by
  simp

@[game_rule] theorem wp_list_mapM_cons
    (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp (spec := spec) ((x :: xs).mapM f) post =
      wp (f x) (fun y => wp (xs.mapM f) (fun ys => post (y :: ys))) := by
  rw [List.mapM_cons, wp_bind]
  congr 1
  funext y
  rw [wp_bind]
  simp

@[game_rule] theorem wp_list_foldlM_nil
    (f : σ → α → OracleComp spec σ) (init : σ) (post : σ → ℝ≥0∞) :
    wp (spec := spec) (([] : List α).foldlM f init) post = post init := by
  simp

@[game_rule] theorem wp_list_foldlM_cons
    (x : α) (xs : List α) (f : σ → α → OracleComp spec σ)
    (init : σ) (post : σ → ℝ≥0∞) :
    wp (spec := spec) ((x :: xs).foldlM f init) post =
      wp (f init x) (fun s => wp (xs.foldlM f s) post) := by
  rw [List.foldlM_cons, wp_bind]

theorem wp_mono (oa : OracleComp spec α) {post post' : α → ℝ≥0∞}
    (hpost : ∀ x, post x ≤ post' x) :
    wp (spec := spec) oa post ≤ wp oa post' := by
  simp only [wp_def_eq]
  exact MAlgOrdered.wp_mono (m := OracleComp spec) (l := ℝ≥0∞) oa hpost

@[game_rule] theorem wp_map
    (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp (f <$> oa) post = wp oa (post ∘ f) := by
  change wp (oa >>= fun a => pure (f a)) post = wp oa (post ∘ f)
  rw [wp_bind]
  congr 1
  funext a
  simp [Function.comp]

/-- General unfolding: `wp` as weighted sum over output probabilities. -/
theorem wp_eq_tsum (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp oa post = ∑' x, Pr[= x | oa] * post x := by
  rw [wp_def_eq, MAlgOrdered.wp]
  change μ (oa >>= fun a => pure (post a)) = _
  rw [μ_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  have : μ (pure (post x) : OracleComp spec ℝ≥0∞) = post x := by
    haveI : DecidableEq ℝ≥0∞ := Classical.decEq _
    simp [μ, probOutput_pure]
  rw [this]

@[simp] theorem wp_const (oa : OracleComp spec α) (c : ℝ≥0∞) :
    wp oa (fun _ => c) = c := by
  rw [wp_eq_tsum, ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

@[game_rule] theorem wp_add (oa : OracleComp spec α) (f g : α → ℝ≥0∞) :
    wp oa (fun x => f x + g x) = wp oa f + wp oa g := by
  simp only [wp_eq_tsum, mul_add, ENNReal.tsum_add]

@[game_rule] theorem wp_mul_const (oa : OracleComp spec α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    wp oa (fun x => c * f x) = c * wp oa f := by
  simp only [wp_eq_tsum]; simp_rw [mul_left_comm]; exact ENNReal.tsum_mul_left

theorem wp_const_mul (oa : OracleComp spec α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    wp oa (fun x => f x * c) = wp oa f * c := by
  simp_rw [mul_comm _ c]; rw [wp_mul_const, mul_comm]

/-! ## `Triple` lemmas (re-routed through `Std.Do'.Triple`)

`Triple` is the inductive `Std.Do'.Triple … EPost.nil.mk`. Each lemma
goes through the `Triple.{ofLE, toLE}` bridges to the `≤`-form, where
the original `MAlgOrdered`-based proofs apply directly. -/

theorem triple_conseq {pre pre' : ℝ≥0∞} {oa : OracleComp spec α}
    {post post' : α → ℝ≥0∞}
    (hpre : pre' ≤ pre) (hpost : ∀ x, post x ≤ post' x) :
    Triple (spec := spec) pre oa post → Triple pre' oa post' := fun h =>
  Triple.ofLE
    (le_trans hpre (le_trans h.toLE
      (MAlgOrdered.wp_mono (m := OracleComp spec) (l := ℝ≥0∞) oa hpost)))

theorem triple_bind {pre : ℝ≥0∞} {oa : OracleComp spec α}
    {cut : α → ℝ≥0∞} {ob : α → OracleComp spec β} {post : β → ℝ≥0∞}
    (hoa : Triple (spec := spec) pre oa cut)
    (hob : ∀ x, Triple (cut x) (ob x) post) :
    Triple pre (oa >>= ob) post := by
  refine Triple.ofLE ?_
  have h := MAlgOrdered.triple_bind (m := OracleComp spec) (l := ℝ≥0∞)
              hoa.toLE (fun x => (hob x).toLE)
  simpa [wp] using h

theorem triple_bind_wp {pre : ℝ≥0∞} {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {post : β → ℝ≥0∞}
    (h : Triple (spec := spec) pre oa (fun x => wp (ob x) post)) :
    Triple pre (oa >>= ob) post := by
  refine Triple.ofLE ?_
  have hle := h.toLE
  rw [wp_bind]; exact hle

theorem triple_pure (x : α) (post : α → ℝ≥0∞) :
    Triple (spec := spec) (post x) (pure x) post :=
  Triple.ofLE (by simp)

/-- A quantitative triple with precondition `0` is always true. -/
theorem triple_zero (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Triple (spec := spec) 0 oa post :=
  Triple.ofLE (by simp)

theorem triple_ite {c : Prop} [Decidable c] {pre : ℝ≥0∞}
    {oa ob : OracleComp spec α} {post : α → ℝ≥0∞}
    (ht : c → Triple (spec := spec) pre oa post)
    (hf : ¬c → Triple pre ob post) :
    Triple pre (if c then oa else ob) post := by
  split_ifs with h
  · exact ht h
  · exact hf h

theorem triple_dite {c : Prop} [Decidable c] {pre : ℝ≥0∞}
    {oa : c → OracleComp spec α} {ob : ¬c → OracleComp spec α} {post : α → ℝ≥0∞}
    (ht : ∀ h : c, Triple (spec := spec) pre (oa h) post)
    (hf : ∀ h : ¬c, Triple pre (ob h) post) :
    Triple pre (dite c oa ob) post := by
  split_ifs with h
  · exact ht h
  · exact hf h

/-- `probEvent` as a WP of an indicator postcondition. -/
lemma probEvent_eq_wp_indicator (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] :
    Pr[ p | oa] = wp oa (fun x => if p x then 1 else 0) := by
  rw [probEvent_eq_tsum_ite, wp_def_eq, MAlgOrdered.wp]
  change (∑' x : α, if p x then Pr[= x | oa] else 0) =
    μ ((oa >>= fun a => pure (if p a then 1 else 0)) : OracleComp spec ℝ≥0∞)
  rw [μ_bind_eq_tsum]
  refine tsum_congr ?_
  intro x
  have hμ :
      μ (pure (if p x then 1 else 0) : OracleComp spec ℝ≥0∞) = (if p x then 1 else 0) := by
    simpa using
      (MAlgOrdered.μ_pure (m := OracleComp spec) (l := ℝ≥0∞) (x := if p x then 1 else 0))
  rw [hμ]
  split_ifs <;> simp

/-- `probOutput` as a WP of a singleton-indicator postcondition. -/
lemma probOutput_eq_wp_indicator (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Pr[= x | oa] = wp oa (fun y => if y = x then 1 else 0) := by
  simpa [probEvent_eq_eq_probOutput] using
    (probEvent_eq_wp_indicator (oa := oa) (p := fun y => y = x))

/-- `liftM` query form of `wp_query`. -/
theorem wp_liftM_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp (spec := spec) (liftM (query t) : OracleComp spec (spec.Range t)) post =
      ∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u := by
  rw [wp_def_eq, MAlgOrdered.wp]
  calc
    μ (do let a ← liftM (query t); pure (post a))
        = ∑' u : spec.Range t,
            Pr[= u | (liftM (query t) : OracleComp spec (spec.Range t))] *
              μ (pure (post u) : OracleComp spec ℝ≥0∞) := by
            simpa using
              (μ_bind_eq_tsum
                (oa := (liftM (query t) : OracleComp spec (spec.Range t)))
                (ob := fun a => pure (post a)))
    _ = ∑' u : spec.Range t,
          (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u := by
            refine tsum_congr ?_
            intro u
            have hμ :
                μ (pure (post u) : OracleComp spec ℝ≥0∞) = post u := by
              let _ : DecidableEq ℝ≥0∞ := Classical.decEq ℝ≥0∞
              simp [μ, probOutput_pure]
            have hprob :
                Pr[= u | (liftM (query t) : OracleComp spec (spec.Range t))] =
                  (1 / Fintype.card (spec.Range t) : ℝ≥0∞) :=
              (probOutput_query_eq_div (spec := spec) t u)
            rw [hμ]
            simp [hprob]

/-- Quantitative WP rule for a uniform oracle query. -/
@[game_rule] theorem wp_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp (spec := spec) (query t : OracleComp spec (spec.Range t)) post =
      ∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u := by
  simpa using wp_liftM_query (spec := spec) t post

section Sampling

variable [SampleableType α]

@[game_rule] theorem wp_uniformSample (post : α → ℝ≥0∞) :
    wp ($ᵗ α) post = ∑' x, Pr[= x | ($ᵗ α : ProbComp α)] * post x := by
  rw [wp_def_eq, MAlgOrdered.wp]
  calc
    μ (do let a ← $ᵗ α; pure (post a))
        = ∑' x, Pr[= x | ($ᵗ α : ProbComp α)] * μ (pure (post x) : ProbComp ℝ≥0∞) := by
          simpa using
            (μ_bind_eq_tsum (oa := ($ᵗ α : ProbComp α)) (ob := fun a => pure (post a)))
    _ = ∑' x, Pr[= x | ($ᵗ α : ProbComp α)] * post x := by
          refine tsum_congr ?_
          intro x
          have hμ : μ (pure (post x) : ProbComp ℝ≥0∞) = post x := by
            let _ : DecidableEq ℝ≥0∞ := Classical.decEq ℝ≥0∞
            simp [μ, probOutput_pure]
          rw [hμ]

end Sampling

/-- Indicator-event probability as an exact quantitative triple. -/
theorem triple_probEvent_indicator (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Triple (spec := spec) (Pr[ p | oa]) oa (fun x => if p x then 1 else 0) :=
  Triple.ofLE (by rw [probEvent_eq_wp_indicator])

/-- Singleton-output probability as an exact quantitative triple. -/
theorem triple_probOutput_indicator (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Triple (spec := spec) (Pr[= x | oa]) oa (fun y => if y = x then 1 else 0) :=
  Triple.ofLE (by rw [probOutput_eq_wp_indicator])

/-- Lower bounds on `probEvent` are exactly indicator-postcondition triples. -/
theorem le_probEvent_iff_triple_indicator (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] (r : ℝ≥0∞) :
    r ≤ Pr[ p | oa] ↔ Triple (spec := spec) r oa (fun x => if p x then 1 else 0) := by
  rw [triple_iff_le_wp, ← probEvent_eq_wp_indicator]

/-- Lower bounds on `probOutput` are exactly singleton-indicator triples. -/
theorem le_probOutput_iff_triple_indicator (oa : OracleComp spec α) [DecidableEq α]
    (x : α) (r : ℝ≥0∞) :
    r ≤ Pr[= x | oa] ↔ Triple (spec := spec) r oa (fun y => if y = x then 1 else 0) := by
  rw [triple_iff_le_wp, ← probOutput_eq_wp_indicator]

/-- The support event of an `OracleComp` occurs almost surely. -/
@[simp] theorem probEvent_mem_support (oa : OracleComp spec α) :
    Pr[ fun x => x ∈ support oa | oa] = 1 := by
  rw [probEvent_eq_one_iff]
  refine ⟨by simp, fun x hx => hx⟩

/-- Exact probability-1 events are exact quantitative triples. -/
theorem triple_probEvent_eq_one (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] (h : Pr[ p | oa] = 1) :
    Triple (spec := spec) 1 oa (fun x => if p x then 1 else 0) := by
  have := triple_probEvent_indicator (oa := oa) p
  rwa [h] at this

/-- Exact probability-1 singleton outputs are exact quantitative triples. -/
theorem triple_probOutput_eq_one (oa : OracleComp spec α) [DecidableEq α]
    (x : α) (h : Pr[= x | oa] = 1) :
    Triple (spec := spec) 1 oa (fun y => if y = x then 1 else 0) := by
  have := triple_probOutput_indicator (oa := oa) x
  rwa [h] at this

/-- `Pr[= x | oa] = 1` ↔ `Triple 1 oa (indicator)`. Bridge for `vcgen` probability lowering. -/
theorem probOutput_eq_one_iff_triple (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Pr[= x | oa] = 1 ↔ Triple (spec := spec) 1 oa (fun y => if y = x then 1 else 0) := by
  constructor
  · exact triple_probOutput_eq_one oa x
  · intro h
    have hle : (1 : ℝ≥0∞) ≤ Pr[= x | oa] := by
      rw [probOutput_eq_wp_indicator]; exact h.toLE
    rwa [one_le_probOutput_iff] at hle

/-- Support membership is a useful default cut function for support-sensitive bind proofs. -/
theorem triple_support (oa : OracleComp spec α) [DecidablePred fun x => x ∈ support oa] :
    Triple (spec := spec) 1 oa (fun x => if x ∈ support oa then 1 else 0) := by
  simpa using
    triple_probEvent_eq_one (oa := oa) (p := fun x => x ∈ support oa)
      (h := probEvent_mem_support (oa := oa))

/-! ## Loop stepping rules (Triple-level) -/

theorem triple_replicate_succ {pre : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    {post : List α → ℝ≥0∞}
    (h : Triple pre oa (fun x => wp (oa.replicate n) (fun xs => post (x :: xs)))) :
    Triple pre (oa.replicate (n + 1)) post := by
  refine Triple.ofLE ?_
  rw [wp_replicate_succ]; exact h.toLE

theorem triple_list_mapM_cons {pre : ℝ≥0∞} {x : α} {xs : List α}
    {f : α → OracleComp spec β} {post : List β → ℝ≥0∞}
    (h : Triple pre (f x) (fun y => wp (xs.mapM f) (fun ys => post (y :: ys)))) :
    Triple pre ((x :: xs).mapM f) post := by
  refine Triple.ofLE ?_
  rw [wp_list_mapM_cons]; exact h.toLE

theorem triple_list_foldlM_cons {pre : ℝ≥0∞} {x : α} {xs : List α}
    {f : σ → α → OracleComp spec σ} {init : σ} {post : σ → ℝ≥0∞}
    (h : Triple pre (f init x) (fun s => wp (xs.foldlM f s) post)) :
    Triple pre ((x :: xs).foldlM f init) post := by
  refine Triple.ofLE ?_
  rw [wp_list_foldlM_cons]; exact h.toLE

/-! ## Loop invariant rules -/

/-- Constant invariant through bounded iteration via `replicate`. -/
theorem triple_replicate_inv {I : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    (hstep : Triple I oa (fun _ => I)) :
    Triple I (oa.replicate n) (fun _ => I) := by
  induction n with
  | zero => exact triple_pure [] (fun _ => I)
  | succ n ih =>
      rw [OracleComp.replicate_succ_bind]
      exact triple_bind hstep fun x => triple_bind ih fun xs =>
        triple_pure (x :: xs) (fun _ => I)

/-- Indexed invariant through `List.foldlM`. -/
theorem triple_list_foldlM_inv {I : σ → ℝ≥0∞}
    {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    (hstep : ∀ s x, x ∈ l → Triple (I s) (f s x) I) :
    Triple (I s₀) (l.foldlM f s₀) I := by
  induction l generalizing s₀ with
  | nil => exact triple_pure s₀ I
  | cons a as ih =>
      rw [List.foldlM_cons]
      exact triple_bind (hstep s₀ a (by simp)) fun s =>
        ih fun s x hx => hstep s x (by simp [hx])

/-- Constant invariant through `List.mapM`. -/
theorem triple_list_mapM_inv {I : ℝ≥0∞}
    {f : α → OracleComp spec β} {l : List α}
    (hstep : ∀ x, x ∈ l → Triple I (f x) (fun _ => I)) :
    Triple I (l.mapM f) (fun _ => I) := by
  induction l with
  | nil => exact triple_pure ([] : List β) (fun _ => I)
  | cons a as ih =>
      rw [List.mapM_cons]
      exact triple_bind (hstep a (by simp)) fun y =>
        triple_bind (ih fun x hx => hstep x (by simp [hx])) fun ys =>
          triple_pure (y :: ys) (fun _ => I)

/-- `replicate` invariant with consequence: bridges arbitrary pre/post to the invariant. -/
theorem triple_replicate {I pre : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : Triple I oa (fun _ => I)) :
    Triple pre (oa.replicate n) post :=
  triple_conseq hpre hpost (triple_replicate_inv hstep)

/-- `List.foldlM` invariant with consequence. -/
theorem triple_list_foldlM {I : σ → ℝ≥0∞}
    {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    {pre : ℝ≥0∞} {post : σ → ℝ≥0∞}
    (hpre : pre ≤ I s₀) (hpost : ∀ s, I s ≤ post s)
    (hstep : ∀ s x, x ∈ l → Triple (I s) (f s x) I) :
    Triple pre (l.foldlM f s₀) post :=
  triple_conseq hpre hpost (triple_list_foldlM_inv hstep)

/-- `List.mapM` invariant with consequence. -/
theorem triple_list_mapM {I : ℝ≥0∞}
    {f : α → OracleComp spec β} {l : List α}
    {pre : ℝ≥0∞} {post : List β → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ ys, I ≤ post ys)
    (hstep : ∀ x, x ∈ l → Triple I (f x) (fun _ => I)) :
    Triple pre (l.mapM f) post :=
  triple_conseq hpre hpost (triple_list_mapM_inv hstep)

/-! ## Congruence under evalDist equality -/

lemma probOutput_congr_evalDist {oa ob : OracleComp spec α}
    (h : evalDist oa = evalDist ob) (x : α) :
    Pr[= x | oa] = Pr[= x | ob] := by
  change evalDist oa x = evalDist ob x
  rw [h]

lemma μ_congr_evalDist {oa ob : OracleComp spec ℝ≥0∞}
    (h : evalDist oa = evalDist ob) :
    μ oa = μ ob := by
  unfold μ
  exact tsum_congr fun x => by rw [probOutput_congr_evalDist h]

lemma wp_congr_evalDist {oa ob : OracleComp spec α}
    (h : evalDist oa = evalDist ob) (post : α → ℝ≥0∞) :
    wp oa post = wp ob post := by
  change μ (oa >>= fun a => pure (post a)) = μ (ob >>= fun a => pure (post a))
  exact μ_congr_evalDist (by simp [h])

lemma μ_cross_congr_evalDist {ι' : Type*} {spec' : OracleSpec ι'}
    [spec'.Fintype] [spec'.Inhabited]
    {oa : OracleComp spec' ℝ≥0∞} {ob : OracleComp spec ℝ≥0∞}
    (h : evalDist oa = evalDist ob) :
    @μ _ spec' _ _ oa = μ ob := by
  simp only [μ]
  exact tsum_congr fun x => by
    change evalDist oa x * x = evalDist ob x * x
    rw [h]

end OracleComp.ProgramLogic
