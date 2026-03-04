/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Std.Tactic.Do
import VCVio.ProgramLogic.Unary.StdDoBridge

/-!
# `Std.Do` / `mvcgen` examples for `OracleComp`
-/

open Std.Do

universe u

set_option mvcgen.warning false

namespace OracleComp.ProgramLogic.StdDo

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α : Type}

example (x : α) :
    Std.Do.Triple (pure x : OracleComp spec α) (spred(⌜True⌝)) (⇓ y => ⌜y = x⌝) := by
  mvcgen

example (t : spec.Domain) {Q : Std.Do.PostCond (spec.Range t) .pure} :
    Std.Do.Triple (OracleComp.query t : OracleComp spec (spec.Range t))
      (⌜wpProp (spec := spec) (OracleComp.query t) (fun a => (Q.1 a).down)⌝)
      Q := by
  unfold Std.Do.Triple
  intro h
  mspec

example (oa : OracleComp spec α) (p : α → Prop) :
    wpProp (spec := spec) oa p ↔ Pr[p | oa] = 1 :=
  wpProp_iff_probEvent_eq_one (spec := spec) oa p

end OracleComp.ProgramLogic.StdDo
