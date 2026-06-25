/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.ReplayFork
import VCVio.ProgramLogic.Unary.HandlerSpecs

/-!
# `Std.Do` handler specifications for the replay fork oracle

Lifts the per-query support-based invariants of `OracleComp.replayOracle`
(established in `VCVio.CryptoFoundations.ReplayFork`) into `Std.Do.Triple`
specifications consumable by `mvcgen`. Whole-program simulations are then
obtained for free via `simulateQ_triple_preserves_invariant` from
`VCVio.ProgramLogic.Unary.HandlerSpecs`.

## Main results

* `OracleComp.replayOracle_triple_prefix` - per-query `@[spec]` triple for
  preservation of `ReplayPrefixInvariant i`.
* `OracleComp.replayOracle_triple_replacement` - per-query `@[spec]` triple
  for preservation of `ReplayReplacementInvariant i`.
* `OracleComp.replayOracle_triple_immutable` - per-query `@[spec]` triple
  recording that `forkQuery`, `replacement`, and `trace` never change.
* `OracleComp.simulateQ_replayOracle_preserves_prefix` - whole-program
  prefix-invariant preservation for arbitrary `oa : OracleComp spec α`.
* `OracleComp.simulateQ_replayOracle_preserves_replacement` - whole-program
  replacement-invariant preservation.
* `OracleComp.simulateQ_replayOracle_preserves_immutable` - whole-program
  triple stating the immutable parameters of the replay state never change
  (relative to a fixed initial state).

The whole-program lemmas reproduce the three public theorems
`replayRunWithTraceValue_preservesPrefixInvariant`,
`replayRunWithTraceValue_preservesReplacementInvariant`, and the trio
`replayRunWithTraceValue_{forkQuery,replacement,trace}_eq` at the
`Std.Do.Triple` level: any property that is provable on a single
`replayOracle` step lifts uniformly through the simulator.
-/

open Std.Do OracleSpec OracleComp

/- File-scoped for the same reason as in
`VCVio.ProgramLogic.Unary.HandlerSpecs`: `mvcgen` currently warns on lifted
`OracleSpec.query` heads even though our `@[spec]` fall-throughs close the
goal. Once the upstream `DiscrTree` / `MonadLiftT.monadLift` key
normalisation lands (tracked in `StdDoBridge.lean`), this can be removed. -/
set_option mvcgen.warning false

namespace OracleComp.ProgramLogic.StdDo

variable {ι : Type}
variable {spec : OracleSpec.{0, 0} ι} [IsUniformSpec spec] [spec.DecidableEq]

section replayOracle

variable {i : ι}

/-! ### Per-query specs (consumable by `mvcgen`) -/

/-- Triple form of `OracleComp.replayOracle_preservesPrefixInvariant`:
each `replayOracle i t` step preserves the replay prefix invariant.

Not marked `@[spec]`. `replayOracle i t` admits three distinct useful
invariants (prefix / replacement / immutable parameters). `mvcgen`'s
`findSpec` is keyed by the syntactic head of the computation, not by the
shape of the assertion, so if more than one of these were registered as
`@[spec]` for the same head (`replayOracle i t`) the tactic would pick
an arbitrary one and silently drop the others. Instead, we leave all
three as plain theorems and ask the caller to pass the relevant one
explicitly, e.g. `mvcgen [replayOracle_triple_prefix]`. The same pattern
applies to `replayOracle_triple_replacement` and
`replayOracle_triple_immutable` below. -/
theorem replayOracle_triple_prefix (i t : ι) :
    Std.Do.Triple
      (replayOracle i t :
        StateT (ReplayForkState spec i) (OracleComp spec) (spec.Range t))
      (spred(fun st => ⌜ReplayPrefixInvariant i st⌝))
      (⇓ _ st' => ⌜ReplayPrefixInvariant i st'⌝) :=
  triple_stateT_iff_forall_support .. |>.mpr fun _ hst v st' hmem =>
    OracleComp.replayOracle_preservesPrefixInvariant (i := i) (t := t) hst (z := (v, st')) hmem

/-- Triple form of `OracleComp.replayOracle_preservesReplacementInvariant`:
each `replayOracle i t` step preserves the replay replacement invariant.

Not marked `@[spec]` to avoid colliding with `replayOracle_triple_prefix`
under `mvcgen`; pass it explicitly via `mvcgen [replayOracle_triple_replacement]`. -/
theorem replayOracle_triple_replacement (i t : ι) :
    Std.Do.Triple
      (replayOracle i t :
        StateT (ReplayForkState spec i) (OracleComp spec) (spec.Range t))
      (spred(fun st => ⌜ReplayReplacementInvariant i st⌝))
      (⇓ _ st' => ⌜ReplayReplacementInvariant i st'⌝) :=
  triple_stateT_iff_forall_support .. |>.mpr fun _ hst v st' hmem =>
    OracleComp.replayOracle_preservesReplacementInvariant (i := i) (t := t) hst (z := (v, st')) hmem

/-- Triple form of `OracleComp.replayOracle_immutable_params`: each
`replayOracle i t` step leaves `forkQuery`, `replacement`, and `trace`
untouched. The triple is parametric in the witness `st₀` of the initial
state.

Not marked `@[spec]` to avoid colliding with `replayOracle_triple_prefix`
under `mvcgen`; pass it explicitly via `mvcgen [replayOracle_triple_immutable]`. -/
theorem replayOracle_triple_immutable (i t : ι) (st₀ : ReplayForkState spec i) :
    Std.Do.Triple
      (replayOracle i t :
        StateT (ReplayForkState spec i) (OracleComp spec) (spec.Range t))
      (spred(fun st => ⌜st = st₀⌝))
      (⇓ _ st' => ⌜st'.forkQuery = st₀.forkQuery ∧
                   st'.replacement = st₀.replacement ∧
                   st'.trace = st₀.trace⌝) :=
  triple_stateT_iff_forall_support .. |>.mpr fun _ hst v st' hmem =>
    OracleComp.replayOracle_immutable_params (i := i) (t := t) (z := (v, st')) (hst ▸ hmem)

/-! ### Whole-program corollaries via `simulateQ_triple_preserves_invariant` -/

/-- Whole-program preservation: `simulateQ (replayOracle i) oa` preserves the
replay prefix invariant for any `oa`. Direct corollary of
`simulateQ_triple_preserves_invariant` and `replayOracle_triple_prefix`. -/
theorem simulateQ_replayOracle_preserves_prefix {α : Type}
    (i : ι) (oa : OracleComp spec α) :
    Std.Do.Triple
      (simulateQ (replayOracle i) oa :
        StateT (ReplayForkState spec i) (OracleComp spec) α)
      (spred(fun st => ⌜ReplayPrefixInvariant i st⌝))
      (⇓ _ st' => ⌜ReplayPrefixInvariant i st'⌝) :=
  simulateQ_triple_preserves_invariant
    (handler := replayOracle i) (I := ReplayPrefixInvariant i)
    (fun t => replayOracle_triple_prefix i t) oa

/-- Whole-program preservation: `simulateQ (replayOracle i) oa` preserves the
replay replacement invariant for any `oa`. -/
theorem simulateQ_replayOracle_preserves_replacement {α : Type}
    (i : ι) (oa : OracleComp spec α) :
    Std.Do.Triple
      (simulateQ (replayOracle i) oa :
        StateT (ReplayForkState spec i) (OracleComp spec) α)
      (spred(fun st => ⌜ReplayReplacementInvariant i st⌝))
      (⇓ _ st' => ⌜ReplayReplacementInvariant i st'⌝) :=
  simulateQ_triple_preserves_invariant
    (handler := replayOracle i) (I := ReplayReplacementInvariant i)
    (fun t => replayOracle_triple_replacement i t) oa

/-- Whole-program immutability: `simulateQ (replayOracle i) oa` never mutates
`forkQuery`, `replacement`, or `trace`, relative to a fixed initial state
`st₀`. -/
theorem simulateQ_replayOracle_preserves_immutable {α : Type}
    (i : ι) (oa : OracleComp spec α) (st₀ : ReplayForkState spec i) :
    Std.Do.Triple
      (simulateQ (replayOracle i) oa :
        StateT (ReplayForkState spec i) (OracleComp spec) α)
      (spred(fun st => ⌜st = st₀⌝))
      (⇓ _ st' => ⌜st'.forkQuery = st₀.forkQuery ∧
                   st'.replacement = st₀.replacement ∧
                   st'.trace = st₀.trace⌝) := by
  refine simulateQ_triple_of_state_and_invariant (handler := replayOracle i)
    (I := fun st => st.forkQuery = st₀.forkQuery ∧ st.replacement = st₀.replacement ∧
      st.trace = st₀.trace) (fun t => ?_) oa st₀ ⟨rfl, rfl, rfl⟩
  rw [triple_stateT_iff_forall_support]
  intro st ⟨hfq, hrep, htr⟩ v st' hmem
  obtain ⟨h₁, h₂, h₃⟩ := OracleComp.replayOracle_immutable_params (i := i) (t := t)
    (z := (v, st')) hmem
  exact ⟨h₁.trans hfq, h₂.trans hrep, h₃.trans htr⟩

/-! ### Worked examples -/

/-- `mvcgen` example: a 3-query `replayOracle i` block preserves
`ReplayPrefixInvariant`. Discharged in a single line. -/
example (i t₁ t₂ t₃ : ι) :
    Std.Do.Triple
      (do
        let _ ← replayOracle i t₁
        let _ ← replayOracle i t₂
        replayOracle i t₃ :
        StateT (ReplayForkState spec i) (OracleComp spec) (spec.Range t₃))
      (spred(fun st => ⌜ReplayPrefixInvariant i st⌝))
      (⇓ _ st' => ⌜ReplayPrefixInvariant i st'⌝) := by
  mvcgen [replayOracle_triple_prefix]

/-- `mvcgen` example: replacement-invariant preservation through a bind.
Composes `replayOracle_triple_replacement` across two queries in one line. -/
example (i t₁ t₂ : ι) :
    Std.Do.Triple
      (do let _ ← replayOracle i t₁; replayOracle i t₂ :
        StateT (ReplayForkState spec i) (OracleComp spec) (spec.Range t₂))
      (spred(fun st => ⌜ReplayReplacementInvariant i st⌝))
      (⇓ _ st' => ⌜ReplayReplacementInvariant i st'⌝) := by
  mvcgen [replayOracle_triple_replacement]

/-- Recover the public theorem
`replayRunWithTraceValue_preservesPrefixInvariant` from the `Std.Do.Triple`
spec `simulateQ_replayOracle_preserves_prefix`. This demonstrates that the
support-based theorems already in `ReplayFork.lean` are direct corollaries
of the new `Std.Do` infrastructure. -/
example {α : Type} (main : OracleComp spec α) (i : ι) (trace : QueryLog spec)
    (forkQuery : Nat) (replacement : spec.Range i)
    {z : α × ReplayForkState spec i}
    (hz : z ∈ support (replayRunWithTraceValue main i trace forkQuery replacement)) :
    ReplayPrefixInvariant i z.2 :=
  triple_stateT_iff_forall_support .. |>.mp
    (simulateQ_replayOracle_preserves_prefix (i := i) main)
    (ReplayForkState.init trace forkQuery replacement)
    (ReplayPrefixInvariant.init trace forkQuery replacement)
    z.1 z.2 hz

end replayOracle

end OracleComp.ProgramLogic.StdDo
