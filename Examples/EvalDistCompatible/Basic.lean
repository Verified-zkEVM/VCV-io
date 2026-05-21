/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.Instances.OptionT

/-!
# Compositional probability reasoning via `MonadLiftT`

This example demonstrates the lift-based design of the `EvalDist` stack.
`OptionT ProbComp` inherits `support`, `Pr[= _ | _]`, and `Pr[⊥ | _]` by
composing the standard `MonadLiftT _ SetM` and `MonadLiftT _ SPMF`
instances from `VCVio.EvalDist.Instances.OptionT` and
`VCVio.OracleComp.EvalDist`.

No `OptionT`-specific data class is registered. Every probability operation
routes through `MonadLiftT _ SetM` (for `support`) and `MonadLiftT _ SPMF`
(for `Pr[…]`), with the propositional `EvalDistCompatible` class connecting
the two views where needed — and without introducing a diamond.

The example: sample a Boolean uniformly and `guard` on heads, so half of
the runs succeed with `()` and the other half fail.
-/

open OracleComp ENNReal

namespace EvalDistCompatibleExample

/-- Sample a Boolean uniformly; commit only on heads. -/
noncomputable def maybeHeads : OptionT ProbComp Unit := do
  let b ← (liftM ($ᵗ Bool) : OptionT ProbComp Bool)
  guard (b = true)

/-- The success branch has probability `1/2`. The proof routes
`Pr[…]` through `MonadLiftT (OptionT ProbComp) SPMF` and reduces to the
generic `OracleComp` lemma `probOutput_uniformSample`. -/
theorem probOutput_maybeHeads : Pr[= () | maybeHeads] = 1 / 2 := by
  change Pr[= () | (do
      let b ← (liftM ($ᵗ Bool) : OptionT ProbComp Bool)
      guard (b = true) : OptionT ProbComp Unit)] = _
  rw [probOutput_bind_eq_tsum]
  simp only [OptionT.probOutput_liftM, probOutput_guard]
  rw [tsum_fintype (L := .unconditional _), Fintype.sum_bool]
  simp [probOutput_uniformSample, Fintype.card_bool]

/-- The failure mass has probability `1/2`. Because `maybeHeads` returns
`Unit`, the total support mass at `()` plus the failure mass is `1`. -/
theorem probFailure_maybeHeads : Pr[⊥ | maybeHeads] = 1 / 2 := by
  rw [probFailure_eq_sub_tsum,
      tsum_eq_single () (fun x hx => absurd (Subsingleton.elim x ()) hx),
      probOutput_maybeHeads, ENNReal.sub_half ENNReal.one_ne_top]

/-- Sanity check: success and failure mass sum to one. The lemma uses no
`OptionT`-specific machinery — just the generic identity from
[`tsum_probOutput_add_probFailure`]. -/
theorem probOutput_add_probFailure_maybeHeads :
    Pr[= () | maybeHeads] + Pr[⊥ | maybeHeads] = 1 := by
  rw [probOutput_maybeHeads, probFailure_maybeHeads, ENNReal.add_halves]

end EvalDistCompatibleExample
