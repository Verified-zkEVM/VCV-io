/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Examples for quantitative `OracleComp` triples
-/

open ENNReal

universe u

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β : Type}

example (x : α) (post : α → ℝ≥0∞) :
    wp (spec := spec) (pure x) post = post x :=
  wp_pure (spec := spec) x post

example (pre : ℝ≥0∞) (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (cut : α → ℝ≥0∞) (post : β → ℝ≥0∞)
    (hoa : Triple (spec := spec) pre oa cut)
    (hob : ∀ x, Triple (cut x) (ob x) post) :
    Triple pre (oa >>= ob) post :=
  triple_bind (spec := spec) hoa hob

example (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Pr[p | oa] = wp oa (fun x => if p x then 1 else 0) :=
  probEvent_eq_wp_indicator (spec := spec) oa p

end OracleComp.ProgramLogic
