/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.PRFReductions.Reductions
import Examples.PRFTagReader.PRFReductions.IdealHandlers
import Examples.PRFTagReader.PRFReductions.Structural

/-!
# PRF Tag/Reader Protocol — PRF Reductions and Composed Ideal Handlers

The PRF reductions for the multiple-session and single-session unlinkability worlds, together
with the composed ideal-world handlers (`multipleIdealQueryImpl`, `singleIdealQueryImpl`,
`unlinkBadQueryImpl`), per-query reduction lemmas, structural `query_bind` reductions, and the
pairwise-distinct-reader-nonce predicate `HasDistinctUnlinkReaderNonces`.

This is the first module of the unlinkability reduction split; downstream modules
(`Table`, `Hybrid`, `HybridToSingle`, `MultipleToHybrid.Setup`,
`MultipleToHybrid.EagerSetup`, `MultipleToHybrid.EagerReader`, `MultipleToHybrid.Eager`,
`MultipleBadCollision`) extend this
infrastructure to the eager-table coupling chain culminating in
`unlinkabilityAdvantage_le_two_prf_plus_collision`.

This file is a thin umbrella re-exporting the three sub-modules
[`PRFReductions.Reductions`], [`PRFReductions.IdealHandlers`], and
[`PRFReductions.Structural`].
-/
