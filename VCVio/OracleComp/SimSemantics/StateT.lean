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
  have : (λ x : α × σ ↦ (x.1, s')) = id :=
    funext λ (x, s) ↦ Prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, Subsingleton.elim _ _⟩
  simp [this]

lemma StateT_run'_simulateQ_eq_self {α} (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ α (q : OracleQuery spec α) s, (so.impl q).run' s = q)
    (oa : OracleComp spec α) (s : σ) : (simulateQ so oa).run' s = oa := by
  sorry

end OracleComp
