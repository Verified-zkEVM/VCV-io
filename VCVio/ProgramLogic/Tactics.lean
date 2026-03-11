/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Unary
import VCVio.ProgramLogic.Tactics.Relational

/-!
# VCGen-Style Tactics for Probabilistic Program Logic

This is the canonical user-facing umbrella import for tactic-based program-logic proofs.

- `VCVio.ProgramLogic.Tactics.Unary` contains unary / quantitative tactics such as
  `wp_step`, `qvcgen_step`, `qvcgen`, `exp_norm`, and `by_hoare`.
- `VCVio.ProgramLogic.Tactics.Relational` contains relational proof-mode tactics such as
  `rvcgen_step`, `rvcgen`, `by_equiv`, `rel_dist`, `game_trans`, `by_dist`, and `by_upto`.

For probability equalities, use `qvcgen_step` directly:
- plain `qvcgen_step` keeps the heuristic swap/congruence dispatcher;
- `qvcgen_step rw` / `qvcgen_step rw under n` expose explicit bind-swap rewrites;
- `qvcgen_step rw congr` / `qvcgen_step rw congr'` expose one shared bind explicitly.

For unary theorem-driven steps:
- `qvcgen_step with thm` forces one explicit unary theorem/assumption step;
- `@[vcgen]` registers an explicit opt-in theorem for bounded head-symbol lookup by
  `qvcgen_step` / `qvcgen`.

For tactic-choice debugging, enable `set_option vcvio.vcgen.traceSteps true`.

For normal proof work, import `VCVio.ProgramLogic.Tactics` and treat it as the default
interactive tactic surface.
-/
