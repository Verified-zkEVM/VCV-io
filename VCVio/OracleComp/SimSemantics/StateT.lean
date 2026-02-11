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

namespace QueryImpl

/-- Given implementations for oracles in `spec₁` and `spec₂` in terms of state monads for
two different contexts `σ₁` and `σ₂`, implement the combined set `spec₁ + spec₂` in terms
of a combined `σ₁ × σ₂` state. -/
def prodStateT {ι₁ ι₂ : Type _}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type _ → Type _} [Functor m] {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec₁ (StateT σ₁ m))
    (impl₂ : QueryImpl spec₂ (StateT σ₂ m)) :
    QueryImpl (spec₁ + spec₂) (StateT (σ₁ × σ₂) m)
  | .inl t => StateT.mk fun | (s₁, s₂) => Prod.map id (·, s₂) <$> (impl₁ t).run s₁
  | .inr t => StateT.mk fun | (s₁, s₂) => Prod.map id (s₁, ·) <$> (impl₂ t).run s₂

/-- Indexed version of `QueryImpl.prodStateT`. Note that `m` cannot vary with `t`.
dtumad: The `Function.update` thing is nice but forces `DecidableEq`. -/
def piStateT {τ : Type} [DecidableEq τ] {ι : τ → Type _}
    {spec : (t : τ) → OracleSpec (ι t)}
    {m : Type _ → Type _} [Monad m] {σ : τ → Type _}
    (impl : (t : τ) → QueryImpl (spec t) (StateT (σ t) m)) :
    QueryImpl (OracleSpec.sigma spec) (StateT ((t : τ) → σ t) m)
  | ⟨t, q⟩ => StateT.mk fun s => Prod.map id (Function.update s t) <$> (impl t q).run (s t)

end QueryImpl

namespace OracleComp

variable {ι : Type*} {spec : OracleSpec ι} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  {σ : Type u} (so : QueryImpl spec (StateT σ m))

/-- If the state type is `Subsingleton`, then we can represent simulation in terms of `simulate'`,
adding back any state at the end of the computation. -/
lemma StateT_run_simulateQ_eq_map_run'_simulateQ {α} [Subsingleton σ]
    (oa : OracleComp spec α) (s s' : σ) :
    (simulateQ so oa).run s = (·, s') <$> (simulateQ so oa).run' s := by
  have : (λ x : α × σ ↦ (x.1, s')) = id :=
    funext λ (x, s) ↦ Prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, Subsingleton.elim _ _⟩
  simp [this]

lemma StateT_run'_simulateQ_eq_self {α} (so : QueryImpl spec (StateT σ (OracleComp spec)))
    (h : ∀ t s, (so t).run' s = query t)
    (oa : OracleComp spec α) (s : σ) : (simulateQ so oa).run' s = oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
      intro s
      simp at ih
      have := congr_arg (· >>= oa) (h t s)
      simpa [ih] using this

end OracleComp
