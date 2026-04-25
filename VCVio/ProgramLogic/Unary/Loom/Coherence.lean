/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Unary.Loom.Probabilistic
import VCVio.ProgramLogic.Unary.Loom.Qualitative

/-!
# Cross-tier coherence for the unary `WP` carriers

The three unary tiers (Qualitative, Probabilistic, Quantitative) form a
chain of refinements:

```
                       indicator                    .val
  α → Prop  ───────────────────────▶  α → Prob  ────────────▶  α → ℝ≥0∞
  (almost-sure)                       ([0, 1])                 (expectation)
```

Both edges have *coherence* lemmas relating their `wp` values:

* **Probabilistic ↔ Quantitative** (definitional, `rfl`): the underlying
  `ℝ≥0∞` value of a probabilistic `wp` is the quantitative `wp` on the
  same post, viewed under `Subtype.val`. This is already proved as
  `OracleComp.Probabilistic.wp_val_eq_mAlgOrdered_wp` in
  `…/Loom/Probabilistic.lean`. We re-export it here under
  `OracleComp.Loom.Coherence` for discoverability and call it
  `wp_prob_val_eq_wp_quant`.
* **Qualitative ↔ Probabilistic** (this file, non-trivial): the
  `Prop`-valued `wp` is true iff the probabilistic `wp` on the
  indicator post equals `1`. This is the support-vs-expectation bridge,
  ultimately reducing to `probEvent_eq_wp_indicator` and
  `probEvent_eq_one_iff` from `VCVio/EvalDist/Defs/Basic.lean`.

## Why state these against `MAlgOrdered.wp` rather than `Std.Do'.wp`?

Both `OracleComp.Qualitative.instWP` and `OracleComp.Probabilistic.instWP_prob`
are `scoped instance`s. To use `Std.Do'.wp` for both at once we would have to
`open` two namespaces simultaneously, and `Std.Do'.WP`'s `Pred` is an
`outParam`, which would back out instance synthesis. Stating the lemmas
against `MAlgOrdered.wp` (specialised to `Prop` and `ℝ≥0∞`) sidesteps
the conflict; once a downstream user has chosen a single carrier, they
can rewrite from `wp _ _ EPost.nil.mk` to `MAlgOrdered.wp _ _`
via the keystone `rfl` lemmas in the per-carrier files.

See `.ignore/wp-cutover-plan.md` §"Three-tier carrier design" for the
broader story.
-/

universe u

open ENNReal OracleComp.ProgramLogic OracleComp.ProgramLogic.PropLogic

namespace OracleComp.Loom.Coherence

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α : Type}

/-! ## Probabilistic ↔ Quantitative

The probabilistic `Std.Do'.wp` agrees with the quantitative `MAlgOrdered.wp`
under `Subtype.val` by `rfl`; that statement lives in `…/Loom/Probabilistic.lean`
as `OracleComp.Probabilistic.wp_val_eq_mAlgOrdered_wp`. We do not restate
it here because pulling `OracleComp.Probabilistic.instWP_prob` into scope
to talk about `Std.Do'.wp` requires `open OracleComp.Probabilistic`,
which then occludes the qualitative tier discussed below. -/

/-! ## Qualitative ↔ Probabilistic (support-vs-expectation bridge)

For an `OracleComp` (which has `HasEvalPMF`, so total probability is
exactly `1`), the support-based `Prop`-valued `wp` agrees with "the
probabilistic `wp` on the indicator post equals `1`". -/

/-- Qualitative ↔ Probabilistic coherence: a `Prop`-valued post is
satisfied almost-surely iff its indicator post has probabilistic `wp`
equal to `1`.

The `[DecidablePred post]` requirement is intrinsic to the indicator
construction; consumers without classical-decidable predicates can
`Classical.dec`-coerce on call sites or reformulate via
`probEvent_eq_wp_indicator` directly. -/
theorem wp_qual_iff_wp_prob_indicator_eq_one
    (oa : OracleComp spec α) (post : α → Prop) [DecidablePred post] :
    MAlgOrdered.wp (m := OracleComp spec) (l := Prop) oa post ↔
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa
          (fun a => if post a then 1 else 0) = 1 := by
  rw [wp_iff_forall_support]
  change (∀ x ∈ support oa, post x) ↔
        wp oa (fun a => if post a then 1 else 0) = 1
  rw [← probEvent_eq_wp_indicator, probEvent_eq_one_iff]
  exact ⟨fun h => ⟨probFailure_eq_zero (mx := oa), h⟩, fun h => h.2⟩

/-- Convenience: the `Prob`-valued indicator-as-`wp` form of the
coherence lemma, for users who have already lifted their post to `Prob`
via `Prob.indicator`. -/
theorem wp_qual_iff_wp_prob_indicator_val_eq_one
    (oa : OracleComp spec α) (post : α → Prop) [DecidablePred post] :
    MAlgOrdered.wp (m := OracleComp spec) (l := Prop) oa post ↔
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa
          (fun a => (Prob.indicator (post a)).val) = 1 := by
  simp only [Prob.val_indicator]
  exact wp_qual_iff_wp_prob_indicator_eq_one oa post

end OracleComp.Loom.Coherence
