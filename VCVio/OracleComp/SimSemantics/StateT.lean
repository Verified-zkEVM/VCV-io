/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Query Implementations with State Monads

This file gives lemmas about `QueryImpl spec m` when `m` is something like `StateT σ n`.

TODO: should generalize things to `MonadState` once laws for it exist.
-/

universe u v w

open OracleSpec

namespace OracleComp

variable {ι : Type*} {spec : OracleSpec ι} {m : Type u → Type v} [AlternativeMonad m]
  [LawfulAlternative m]
  {σ : Type u} [Subsingleton σ] (so : QueryImpl spec (StateT σ m))

/-- If the state type is `Subsingleton`, then we can represent simulation in terms of `simulate'`,
adding back any state at the end of the computation. -/
lemma StateT_run_simulateQ_eq_map_run'_simulateQ {α} (oa : OracleComp spec α) (s s' : σ) :
    (simulateQ so oa).run s = (·, s') <$> (simulateQ so oa).run' s := by
  have : (fun x : α × σ ↦ (x.1, s')) = id := funext fun x ↦ Prod.ext rfl (Subsingleton.elim ..)
  simp [this]

lemma StateT_run'_simulateQ_eq_self {α} (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ α (q : OracleQuery spec α) s, (so.impl q).run' s = q)
    (oa : OracleComp spec α) (s : σ) : (simulateQ so oa).run' s = oa := by
  induction' oa using OracleComp.inductionOn with x q oa ihx ihq
  · rfl
  · convert congr_arg (fun x ↦ x >>= ihx) (h (spec.range q) (.query q oa) s) using 1
    simp only [simulateQ_bind, simulateQ_query, StateT.run'_eq, StateT.run_bind,
      Function.comp_apply, map_bind, bind_map_left]
    simp [Subsingleton.elim _ s, ← StateT.run'_eq, ihq]
  · rfl

end OracleComp
