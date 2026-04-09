/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import Examples.CommitmentScheme.Support.MainCompat
import Examples.CommitmentScheme.Support.Collision
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Support Lemmas — re-exports `MainCompat`, query-bound infrastructure, and `Collision`.

These provide generic oracle infrastructure (TV distance bounds, query bound tracking,
collision analysis) used by the commitment scheme security proofs.
-/
