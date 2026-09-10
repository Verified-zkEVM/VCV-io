/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Defs.Basic

/-!
# Sampling blocks for event probabilities

With `open scoped ProbabilityTheory`, write
```
Pr_{
  let x ← mx
  let y ← f x
}[R x y]
```
for the probability of the final event after the indicated computations. The sampling block uses
Lean's `doSeq` parser. It is joined with the event into one ordinary `do` block, so dependent
bindings, patterns, local declarations, and mutable variables have their usual Lean scope.

The notation expands to `Pr{...}[...]`, which appends `return R x y` and observes the probability
of returning `True`. The event has type `Prop`; Boolean events use Lean's usual coercion. Ordinary
control flow is preserved: an early `return` supplies the result proposition directly and skips
the appended event. The braces therefore contain the prelude of the combined block, rather than
a separately elaborated computation whose result must be destructured by the event.

The probability semantics and typeclass assumptions are those of `probOutput`; no normalization
on successful termination is performed. `probOutput_true_eq_probEvent` identifies a single-sample
block with `probEvent`, and the measure compatibility lemmas relate that event to `𝒟[mx]` under
their measurability and interpretation hypotheses. The notation is independent of the concrete
monad and does not select an initial state or a probability interpretation.
-/

public meta section

open Lean Parser Term

namespace ProbabilityTheory

/-- Probability of the event at the end of an ordinary Lean sampling block. -/
scoped syntax (name := probabilityBlock) "Pr_{" doSeq "}[" term "]" : term

scoped macro_rules (kind := probabilityBlock)
  | `(Pr_{{$items*}}[$event]) => `(Pr{{$items*}}[$event])
  | `(Pr_{$items*}[$event]) => `(Pr{$items*}[$event])

end ProbabilityTheory
