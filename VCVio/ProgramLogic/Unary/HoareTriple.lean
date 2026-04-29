/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import VCVio.ProgramLogic.Unary.Loom.Quantitative
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Quantitative Hoare triples for `OracleComp`

The user-facing `wp_*` and `triple_*` lemma library for the quantitative
(`ℝ≥0∞`) program logic on `OracleComp spec`. After the Loom2 cutover the
canonical heads are `Std.Do'.wp` and `Std.Do'.Triple`, both with the
exception postcondition fixed to `Lean.Order.bot` on the empty
`Std.Do'.EPost.nil` carrier (which we equip with a `Lean.Order.CCPO`
instance in `Loom/Quantitative.lean`). All lemmas are stated against
those canonical heads, exactly the shape that:

* the user-facing notation `wp⟦c⟧ post` (in `NotationCore.lean`)
  elaborates to,
* Loom2's `⦃ pre ⦄ c ⦃ post ⦄` notation (in `Loom.Triple.Basic`)
  elaborates to,
* the `vcgen` / `vcstep` tactic infrastructure recognises after the
  cutover.

The keystone definitional alignment lives in `Loom/Quantitative.lean`:
`wp _ _ = MAlgOrdered.wp _ _` is `rfl` for
`OracleComp`, so existing `MAlgOrdered.wp_*` machinery transports
directly into the `Std.Do'` shape. The `Std.Do'.Triple` analogue is
inductive (not definitional) and bridged via `Std.Do'.Triple.iff`
(`pre ⊑ wp …`) and `triple_ofLE`.
-/

open ENNReal
open Std.Do'

universe u

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β σ : Type}

/-! ## API contract

- This unary quantitative interface is instantiated for `OracleComp spec`.
- Probability/evaluation assumptions are `[spec.Fintype]` and `[spec.Inhabited]`.
- The quantitative codomain is fixed to `ℝ≥0∞`.
- Every `wp_*` lemma is stated as
  `wp oa post = …`, every `triple_*` lemma as
  `Triple pre oa post`.
- For ergonomic call-site syntax, the abbreviations `wp` and `Triple`
  reduce to the canonical heads with `epost :=`. They
  are pure notation: every theorem is stated against the canonical
  forms, and tactics (`vcgen`, `vcstep`, `@[wpStep]`, …) match on the
  canonical heads after abbrev unfolding.
-/

/-- Quantitative weakest-precondition for `OracleComp spec`, fixing the
exception postcondition to `Lean.Order.bot`. Definitionally equal to
`Std.Do'.wp oa post Lean.Order.bot`; see the API contract for details. -/
noncomputable abbrev wp (oa : OracleComp spec α) (post : α → ℝ≥0∞) : ℝ≥0∞ :=
  Std.Do'.wp oa post Lean.Order.bot

/-- Quantitative Hoare triple for `OracleComp spec`, fixing the exception
postcondition to `Lean.Order.bot`. Definitionally equal to
`Std.Do'.Triple pre oa post Lean.Order.bot`; see the API contract for
details. -/
noncomputable abbrev Triple (pre : ℝ≥0∞) (oa : OracleComp spec α)
    (post : α → ℝ≥0∞) : Prop :=
  Std.Do'.Triple pre oa post Lean.Order.bot

/-! ## Internal alias

`MAlgOrdered.wp` is `rfl`-equal to `wp _ _` on
`OracleComp` via the `Loom.instWP` instance. The bridge `wp_eq_mAlgOrdered_wp`
re-exposes this so existing `MAlgOrdered.wp_*` lemmas can be applied with
a single rewrite. -/

theorem wp_eq_mAlgOrdered_wp (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp oa post =
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa post := rfl

/-- Bridge between Loom2's inductive `Std.Do'.Triple` and Mathlib's `≤` on
`ℝ≥0∞`. Loom2 defines `Std.Do'.Triple.iff` against
`Lean.Order.PartialOrder.rel`; on `ℝ≥0∞` our `Lean.Order.PartialOrder`
instance defines `rel` as Mathlib's `≤`, so the two coincide. The
explicit `Iff.rfl` re-exposes the equivalence in `≤`-form, which is what
all the downstream `triple_*` proofs are stated against. -/
theorem triple_iff_le_wp
    (pre : ℝ≥0∞) (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Triple pre oa post ↔
      pre ≤ wp oa post :=
  Std.Do'.Triple.iff (epost := Lean.Order.bot)

/-- Construct a `Triple …` from a `≤`-form proof
`pre ≤ wp oa post`. Companion to
`triple_iff_le_wp.mpr`; preferred as the constructor in concrete proofs
because it avoids Lean's typeclass-projection unification failures
that arise when calling `Std.Do'.Triple.intro` directly with a `≤`
proof. -/
theorem triple_ofLE
    {pre : ℝ≥0∞} {oa : OracleComp spec α} {post : α → ℝ≥0∞}
    (h : pre ≤ wp oa post) :
    Triple pre oa post :=
  (triple_iff_le_wp pre oa post).mpr h

/-- Extract the `≤`-form `pre ≤ wp oa post` from a
`Triple …`. Companion to `triple_iff_le_wp.mp`. -/
theorem triple_toLE
    {pre : ℝ≥0∞} {oa : OracleComp spec α} {post : α → ℝ≥0∞}
    (h : Triple pre oa post) :
    pre ≤ wp oa post :=
  (triple_iff_le_wp pre oa post).mp h

/-! ## `wp` lemmas (against `wp _ _`) -/

@[simp, game_rule] theorem wp_pure (x : α) (post : α → ℝ≥0∞) :
    wp (pure x : OracleComp spec α) post = post x := by
  rw [wp_eq_mAlgOrdered_wp, MAlgOrdered.wp_pure]

@[simp, game_rule] theorem wp_ite (c : Prop) [Decidable c]
    (oa ob : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (if c then oa else ob) post =
      if c then wp oa post
      else wp ob post := by
  split_ifs <;> rfl

@[simp, game_rule] theorem wp_dite (c : Prop) [Decidable c]
    (oa : c → OracleComp spec α) (ob : ¬c → OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (dite c oa ob) post =
      dite c (fun h => wp (oa h) post)
        (fun h => wp (ob h) post) := by
  split_ifs <;> rfl

@[game_rule] theorem wp_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (post : β → ℝ≥0∞) :
    wp (oa >>= ob) post =
      wp oa (fun x => wp (ob x) post) := by
  simp only [wp_eq_mAlgOrdered_wp]
  exact MAlgOrdered.wp_bind (m := OracleComp spec) (l := ℝ≥0∞) oa ob post

@[game_rule] theorem wp_replicate_zero (oa : OracleComp spec α) (post : List α → ℝ≥0∞) :
    wp (oa.replicate 0) post = post [] := by
  simp [OracleComp.replicate_zero]

@[game_rule] theorem wp_replicate_succ
    (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp (oa.replicate (n + 1)) post =
      wp oa
        (fun x => wp (oa.replicate n)
          (fun xs => post (x :: xs))) := by
  rw [OracleComp.replicate_succ_bind, wp_bind]
  congr 1
  funext x
  rw [wp_bind]
  simp

@[game_rule] theorem wp_list_mapM_nil
    (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp (([] : List α).mapM f) post = post [] := by
  simp

@[game_rule] theorem wp_list_mapM_cons
    (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp ((x :: xs).mapM f) post =
      wp (f x)
        (fun y => wp (xs.mapM f)
          (fun ys => post (y :: ys))) := by
  rw [List.mapM_cons, wp_bind]
  congr 1
  funext y
  rw [wp_bind]
  simp

@[game_rule] theorem wp_list_foldlM_nil
    (f : σ → α → OracleComp spec σ) (init : σ) (post : σ → ℝ≥0∞) :
    wp (([] : List α).foldlM f init) post = post init := by
  simp

@[game_rule] theorem wp_list_foldlM_cons
    (x : α) (xs : List α) (f : σ → α → OracleComp spec σ)
    (init : σ) (post : σ → ℝ≥0∞) :
    wp ((x :: xs).foldlM f init) post =
      wp (f init x)
        (fun s => wp (xs.foldlM f s) post) := by
  rw [List.foldlM_cons, wp_bind]

theorem wp_mono (oa : OracleComp spec α) {post post' : α → ℝ≥0∞}
    (hpost : ∀ x, post x ≤ post' x) :
    wp oa post ≤ wp oa post' := by
  simp only [wp_eq_mAlgOrdered_wp]
  exact MAlgOrdered.wp_mono (m := OracleComp spec) (l := ℝ≥0∞) oa hpost

@[game_rule] theorem wp_map
    (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp (f <$> oa) post =
      wp oa (post ∘ f) := by
  change wp (oa >>= fun a => pure (f a)) post = _
  rw [wp_bind]
  congr 1
  funext a
  simp [Function.comp]

/-- General unfolding: `wp` as weighted sum over output probabilities. -/
theorem wp_eq_tsum (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp oa post = ∑' x, Pr[= x | oa] * post x := by
  rw [wp_eq_mAlgOrdered_wp, MAlgOrdered.wp]
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
    wp oa (fun x => f x + g x) =
      wp oa f + wp oa g := by
  simp only [wp_eq_tsum, mul_add, ENNReal.tsum_add]

@[game_rule] theorem wp_mul_const (oa : OracleComp spec α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    wp oa (fun x => c * f x) =
      c * wp oa f := by
  simp only [wp_eq_tsum]; simp_rw [mul_left_comm]; exact ENNReal.tsum_mul_left

theorem wp_const_mul (oa : OracleComp spec α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    wp oa (fun x => f x * c) =
      wp oa f * c := by
  simp_rw [mul_comm _ c]; rw [wp_mul_const, mul_comm]

/-! ## `Triple` lemmas (against `Triple _ _ _`)

`Std.Do'.Triple` is an inductive wrapper around `pre ⊑ wp …`. The
accessor `Std.Do'.Triple.iff` exchanges between the inductive form and
the `≤`-form; `triple_ofLE` packages a `≤`-proof into the
constructor; pattern matching `match h with | .intro h => h` extracts
the underlying inequality. -/

theorem triple_conseq {pre pre' : ℝ≥0∞} {oa : OracleComp spec α}
    {post post' : α → ℝ≥0∞}
    (hpre : pre' ≤ pre) (hpost : ∀ x, post x ≤ post' x) :
    Triple pre oa post →
      Triple pre' oa post' := fun h =>
  triple_ofLE
    (le_trans hpre (le_trans (triple_toLE h)
      (MAlgOrdered.wp_mono (m := OracleComp spec) (l := ℝ≥0∞) oa hpost)))

theorem triple_bind {pre : ℝ≥0∞} {oa : OracleComp spec α}
    {cut : α → ℝ≥0∞} {ob : α → OracleComp spec β} {post : β → ℝ≥0∞}
    (hoa : Triple pre oa cut)
    (hob : ∀ x, Triple (cut x) (ob x) post) :
    Triple pre (oa >>= ob) post := by
  refine triple_ofLE ?_
  have h := MAlgOrdered.triple_bind (m := OracleComp spec) (l := ℝ≥0∞)
              (triple_toLE hoa) (fun x => triple_toLE (hob x))
  exact h

theorem triple_bind_wp {pre : ℝ≥0∞} {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {post : β → ℝ≥0∞}
    (h : Triple pre oa
          (fun x => wp (ob x) post)) :
    Triple pre (oa >>= ob) post := by
  refine triple_ofLE ?_
  have hle := triple_toLE h
  rw [wp_bind]; exact hle

theorem triple_pure (x : α) (post : α → ℝ≥0∞) :
    Triple (post x) (pure x : OracleComp spec α) post :=
  triple_ofLE (by simp)

/-- A quantitative triple with precondition `0` is always true. -/
theorem triple_zero (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Triple (0 : ℝ≥0∞) oa post :=
  triple_ofLE (by simp)

theorem triple_ite {c : Prop} [Decidable c] {pre : ℝ≥0∞}
    {oa ob : OracleComp spec α} {post : α → ℝ≥0∞}
    (ht : c → Triple pre oa post)
    (hf : ¬c → Triple pre ob post) :
    Triple pre (if c then oa else ob) post := by
  split_ifs with h
  · exact ht h
  · exact hf h

theorem triple_dite {c : Prop} [Decidable c] {pre : ℝ≥0∞}
    {oa : c → OracleComp spec α} {ob : ¬c → OracleComp spec α} {post : α → ℝ≥0∞}
    (ht : ∀ h : c, Triple pre (oa h) post)
    (hf : ∀ h : ¬c, Triple pre (ob h) post) :
    Triple pre (dite c oa ob) post := by
  split_ifs with h
  · exact ht h
  · exact hf h

/-- `probEvent` as a WP of an indicator postcondition. -/
lemma probEvent_eq_wp_indicator (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] :
    Pr[ p | oa] = wp oa (fun x => if p x then 1 else 0) := by
  rw [probEvent_eq_tsum_ite, wp_eq_mAlgOrdered_wp, MAlgOrdered.wp]
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
    wp (liftM (query t) : OracleComp spec (spec.Range t)) post =
      ∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u := by
  rw [wp_eq_mAlgOrdered_wp, MAlgOrdered.wp]
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
    wp (query t : OracleComp spec (spec.Range t)) post =
      ∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u := by
  simpa using wp_liftM_query (spec := spec) t post

/-- `HasQuery.query` form of `wp_query`: after the `HasQuery` ergonomic
cutover, the bare `query t : OracleComp spec _` in user code elaborates to
`HasQuery.query t`. This restates the rule with that head so the
`@[game_rule]` registry can dispatch on user-facing goals without unfolding. -/
@[game_rule] theorem wp_HasQuery_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp (spec := spec) (HasQuery.query t : OracleComp spec (spec.Range t)) post =
      ∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u :=
  wp_liftM_query (spec := spec) t post

section Sampling

variable [SampleableType α]

@[game_rule] theorem wp_uniformSample (post : α → ℝ≥0∞) :
    wp ($ᵗ α) post =
      ∑' x, Pr[= x | ($ᵗ α : ProbComp α)] * post x := by
  rw [wp_eq_mAlgOrdered_wp, MAlgOrdered.wp]
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
    Triple (Pr[ p | oa]) oa (fun x => if p x then 1 else 0) :=
  triple_ofLE (by rw [probEvent_eq_wp_indicator])

/-- Singleton-output probability as an exact quantitative triple. -/
theorem triple_probOutput_indicator (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Triple (Pr[= x | oa]) oa (fun y => if y = x then 1 else 0) :=
  triple_ofLE (by rw [probOutput_eq_wp_indicator])

/-- Lower bounds on `probEvent` are exactly indicator-postcondition triples. -/
theorem le_probEvent_iff_triple_indicator (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] (r : ℝ≥0∞) :
    r ≤ Pr[ p | oa] ↔
      Triple r oa (fun x => if p x then 1 else 0) := by
  rw [triple_iff_le_wp, ← probEvent_eq_wp_indicator]

/-- Lower bounds on `probOutput` are exactly singleton-indicator triples. -/
theorem le_probOutput_iff_triple_indicator (oa : OracleComp spec α) [DecidableEq α]
    (x : α) (r : ℝ≥0∞) :
    r ≤ Pr[= x | oa] ↔
      Triple r oa (fun y => if y = x then 1 else 0) := by
  rw [triple_iff_le_wp, ← probOutput_eq_wp_indicator]

/-- The support event of an `OracleComp` occurs almost surely. -/
@[simp] theorem probEvent_mem_support (oa : OracleComp spec α) :
    Pr[ fun x => x ∈ support oa | oa] = 1 := by
  rw [probEvent_eq_one_iff]
  refine ⟨by simp, fun x hx => hx⟩

/-- Exact probability-1 events are exact quantitative triples. -/
theorem triple_probEvent_eq_one (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] (h : Pr[ p | oa] = 1) :
    Triple (1 : ℝ≥0∞) oa (fun x => if p x then 1 else 0) := by
  have := triple_probEvent_indicator (oa := oa) p
  rwa [h] at this

/-- Exact probability-1 singleton outputs are exact quantitative triples. -/
theorem triple_probOutput_eq_one (oa : OracleComp spec α) [DecidableEq α]
    (x : α) (h : Pr[= x | oa] = 1) :
    Triple (1 : ℝ≥0∞) oa (fun y => if y = x then 1 else 0) := by
  have := triple_probOutput_indicator (oa := oa) x
  rwa [h] at this

/-- `Pr[= x | oa] = 1` ↔ `Triple 1 oa (indicator)`. Bridge for `vcgen` probability lowering. -/
theorem probOutput_eq_one_iff_triple (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Pr[= x | oa] = 1 ↔
      Triple (1 : ℝ≥0∞) oa (fun y => if y = x then 1 else 0) := by
  constructor
  · exact triple_probOutput_eq_one oa x
  · intro h
    have hle : (1 : ℝ≥0∞) ≤ Pr[= x | oa] := by
      rw [probOutput_eq_wp_indicator]; exact triple_toLE h
    rwa [one_le_probOutput_iff] at hle

/-- Support membership is a useful default cut function for support-sensitive bind proofs. -/
theorem triple_support (oa : OracleComp spec α) [DecidablePred fun x => x ∈ support oa] :
    Triple (1 : ℝ≥0∞) oa
      (fun x => if x ∈ support oa then 1 else 0) := by
  simpa using
    triple_probEvent_eq_one (oa := oa) (p := fun x => x ∈ support oa)
      (h := probEvent_mem_support (oa := oa))

/-! ## Loop stepping rules (Triple-level) -/

theorem triple_replicate_succ {pre : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    {post : List α → ℝ≥0∞}
    (h : Triple pre oa
          (fun x => wp (oa.replicate n)
            (fun xs => post (x :: xs)))) :
    Triple pre (oa.replicate (n + 1)) post := by
  refine triple_ofLE ?_
  rw [wp_replicate_succ]; exact triple_toLE h

theorem triple_list_mapM_cons {pre : ℝ≥0∞} {x : α} {xs : List α}
    {f : α → OracleComp spec β} {post : List β → ℝ≥0∞}
    (h : Triple pre (f x)
          (fun y => wp (xs.mapM f)
            (fun ys => post (y :: ys)))) :
    Triple pre ((x :: xs).mapM f) post := by
  refine triple_ofLE ?_
  rw [wp_list_mapM_cons]; exact triple_toLE h

theorem triple_list_foldlM_cons {pre : ℝ≥0∞} {x : α} {xs : List α}
    {f : σ → α → OracleComp spec σ} {init : σ} {post : σ → ℝ≥0∞}
    (h : Triple pre (f init x)
          (fun s => wp (xs.foldlM f s) post)) :
    Triple pre ((x :: xs).foldlM f init) post := by
  refine triple_ofLE ?_
  rw [wp_list_foldlM_cons]; exact triple_toLE h

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

/-! ## Congruence under `evalDist` equality -/

lemma probOutput_congr_evalDist {oa ob : OracleComp spec α}
    (h : 𝒟[oa] = 𝒟[ob]) (x : α) :
    Pr[= x | oa] = Pr[= x | ob] := by
  change 𝒟[oa] x = 𝒟[ob] x
  rw [h]

lemma μ_congr_evalDist {oa ob : OracleComp spec ℝ≥0∞}
    (h : 𝒟[oa] = 𝒟[ob]) :
    μ oa = μ ob := by
  unfold μ
  exact tsum_congr fun x => by rw [probOutput_congr_evalDist h]

lemma wp_congr_evalDist {oa ob : OracleComp spec α}
    (h : 𝒟[oa] = 𝒟[ob]) (post : α → ℝ≥0∞) :
    wp oa post = wp ob post := by
  change μ (oa >>= fun a => pure (post a)) = μ (ob >>= fun a => pure (post a))
  exact μ_congr_evalDist (by simp [h])

lemma μ_cross_congr_evalDist {ι' : Type*} {spec' : OracleSpec ι'}
    [spec'.Fintype] [spec'.Inhabited]
    {oa : OracleComp spec' ℝ≥0∞} {ob : OracleComp spec ℝ≥0∞}
    (h : 𝒟[oa] = 𝒟[ob]) :
    @μ _ spec' _ _ oa = μ ob := by
  simp only [μ]
  exact tsum_congr fun x => by
    change 𝒟[oa] x * x = 𝒟[ob] x * x
    rw [h]

end OracleComp.ProgramLogic
