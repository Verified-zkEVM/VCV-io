/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Gate for the `StateT` invariant rules

A handler written in `do` notation is checked clause by clause: `get` binds the state under the
invariant, `set` needs the invariant at the new state, lifted samplers and `pure` change nothing,
and a `mapM` over a preserving step preserves. A sum of implementations preserves an invariant
exactly when both summands do. Each entry is one term against a small unit-test handler.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.PreservesInv

/-- Bump a counter on every query. -/
def bumpImpl : QueryImpl (Unit →ₒ Unit) (StateT ℕ ProbComp) := fun _ => do
  let n ← get
  set (n + 1)

/-- Replace the counter by a fresh coin's value, read as a number. -/
def coinImpl : QueryImpl (Unit →ₒ Unit) (StateT ℕ ProbComp) := fun _ => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  set (if b then 1 else 2)

example : QueryImpl.PreservesInv bumpImpl (0 < ·) := fun _ =>
  StateT.preservesInv_get_bind _ fun n _ => StateT.preservesInv_set_of _ (Nat.succ_pos n)

example : QueryImpl.PreservesInv coinImpl (0 < ·) := fun _ =>
  StateT.preservesInv_bind _ _ _ (StateT.preservesInv_monadLift _ _) fun b =>
    StateT.preservesInv_set_of _ (by cases b <;> decide)

example : QueryImpl.PreservesInv (bumpImpl + coinImpl) (0 < ·) :=
  QueryImpl.PreservesInv.add
    (fun _ => StateT.preservesInv_get_bind _ fun n _ =>
      StateT.preservesInv_set_of _ (Nat.succ_pos n))
    (fun _ => StateT.preservesInv_bind _ _ _ (StateT.preservesInv_monadLift _ _) fun b =>
      StateT.preservesInv_set_of _ (by cases b <;> decide))

example (h : QueryImpl.PreservesInv (bumpImpl + coinImpl) (0 < ·)) :
    QueryImpl.PreservesInv coinImpl (0 < ·) :=
  ((QueryImpl.preservesInv_add_iff _ _ _).1 h).2

example (l : List Unit) : StateT.PreservesInv (l.mapM fun _ => bumpImpl ()) (0 < ·) :=
  StateT.preservesInv_mapM _ (fun _ =>
    StateT.preservesInv_get_bind _ fun n _ => StateT.preservesInv_set_of _ (Nat.succ_pos n)) l

example (n : ℕ) : StateT.PreservesInv ((fun _ => n) <$> bumpImpl ()) (0 < ·) :=
  StateT.preservesInv_map _
    (StateT.preservesInv_get_bind _ fun n _ => StateT.preservesInv_set_of _ (Nat.succ_pos n))

end VCVioTest.PreservesInv
