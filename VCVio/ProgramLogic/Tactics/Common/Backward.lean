/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Common.Registry

/-!
# Backward application for VCSpec entries

Shared native application helpers for `@[vcspec]` entries.
-/

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

/-- Try to apply a registered `@[vcspec]` entry directly to a goal metavariable.

This is the VCVio-native counterpart of the experimental `lspec_spike` backward
path: instantiate the stored `SpecProof`, apply it with fresh metavariables, and
return the generated subgoals. Goal-specific close passes remain in the unary and
relational planners because they know which leaf rules are cheap and valid for
their logic. -/
def VCSpecEntry.tryApplyBackward (entry : VCSpecEntry) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  let (_xs, _bis, prf, _type) ← entry.proof.instantiate
  try
    let subgoals ← mvarId.apply prf
    return some subgoals
  catch _ =>
    return none

/-- Apply a `@[vcspec]` entry to the current main goal, preserving the tail goals.

This helper performs only the theorem application. Callers should run their
existing cheap close pass afterwards. -/
def runVCSpecEntryBackward (entry : VCSpecEntry) : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      match ← liftMetaM <| entry.tryApplyBackward goal with
      | none => return false
      | some subgoals =>
          setGoals (subgoals ++ rest)
          return true

end OracleComp.ProgramLogic
