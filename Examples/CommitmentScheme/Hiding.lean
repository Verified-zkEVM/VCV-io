/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import Examples.CommitmentScheme.Hiding.Defs
import Examples.CommitmentScheme.Hiding.CountBounds
import Examples.CommitmentScheme.Hiding.LoggingBounds
import Examples.CommitmentScheme.Hiding.Main

/-!
# Hiding security for the random-oracle commitment scheme

Re-exports the four submodules that together prove the textbook
hiding bound `tvDist(real, sim) ≤ t / |S|` (averaged over the salt
`s ← $ᵗ S`) for the ROM commitment scheme `Commit(m) = (H(m, s), s)`.

The main result is `hiding_bound_finite` in `Hiding.Main`.

## Submodule layout

* `Defs` — hiding adversary, the four oracle implementations
  (`hidingImpl₁` real, `hidingImpl₂` bridge, `hidingImplSim` simulator,
  `hidingImplCountAll` shared per-salt counter), and basic step-bound
  lemmas.
* `CountBounds` — per-salt counter invariants for `hidingImplCountAll`
  (monotonicity, totals, fresh-salt projections, weakest-precondition
  bounds).
* `LoggingBounds` — re-exports `Average` and `QuerySalt`.
* `LoggingBounds/Average` — averaged hiding experiment definitions
  (`HidingAvgSpec`, `hidingAvgComp`, `hidingMixed{Real,Sim}`) and the
  per-salt → averaged passes.
* `LoggingBounds/QuerySalt` — `Pr[adversary ever queries salt s] ≤ t / |S|`
  after averaging, via counting-oracle projections and indicator analysis.
* `Main` — the packaged theorems `hiding_bound_avg` (per-salt sum form)
  and `hiding_bound_finite` (textbook-facing form).

## Proof technique in one paragraph

Identical-until-bad with the bad event `saltCount(s) ≥ 2`. For each fixed
salt `s`, the real game `hidingImpl₁ s` and the simulator `hidingImplSim s`
agree until the adversary makes a second salt-`s` query (the first being
the mandatory challenge query). The TVD between real and simulator games
is therefore bounded by `Pr[bad(s)]`. Averaging `Pr[bad(s)]` over `s` and
using the fact that the adversary makes at most `t` total salt-bearing
queries gives the `t / |S|` bound. The bound is *intrinsically averaged*:
the per-salt version is false. -/
