/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean.Elab.Tactic
import VCVio.OracleComp.QueryTracking.HandlerSimp

/-!
# Handler Normalization Tactic

`handler_step` performs one small normalization pass using the `handler_simp`
set. It is intentionally thin: use it to expose the next handler body or
run-shape, then continue with `mvcgen`, `vcstep`, `rvcstep`, or direct proof
steps.
-/

open Lean Elab Tactic

namespace OracleComp.ProgramLogic

syntax "handler_step" : tactic

elab_rules : tactic
  | `(tactic| handler_step) => do
      evalTactic (← `(tactic| simp only [handler_simp]))

end OracleComp.ProgramLogic
