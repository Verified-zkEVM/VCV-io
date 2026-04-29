/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import Examples.CommitmentScheme.Hiding.Defs
import Examples.CommitmentScheme.Hiding.CountBounds
import Examples.CommitmentScheme.Hiding.LoggingBounds
import Examples.CommitmentScheme.Hiding.Main

/-!
# Hiding Security — re-exports all submodules.

The main result is `hiding_bound_finite` in `Hiding.Main`:
the statistical distance between real and simulated hiding games is at most `t / |S|`.
-/
