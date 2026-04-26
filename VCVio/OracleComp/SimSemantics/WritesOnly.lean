/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.SimSemantics.StateProjection

/-!
# State-field write footprints

Small reusable predicates for handlers whose state updates preserve a chosen
projection. These lemmas are intentionally lightweight: concrete game files
state their handler-specific projection facts once, then use the generic
`run_preserves` / `step_preserves` projections instead of repeating
field-by-field support arguments.
-/

open OracleSpec

namespace QueryImpl

variable {ι : Type} {spec : OracleSpec ι}
variable {σ ρ : Type} {m : Type → Type*} [Monad m] [HasEvalSet m]

/-- A stateful oracle implementation preserves a projection `π` on every
single oracle step. -/
def WritesOnlyField (impl : QueryImpl spec (StateT σ m)) (π : σ → ρ) : Prop :=
  ∀ t s z, z ∈ support ((impl t).run s) → π z.2 = π s

namespace WritesOnlyField

/-- Pointwise projection preservation for one handler step. -/
theorem step_preserves {impl : QueryImpl spec (StateT σ m)} {π : σ → ρ}
    (h : WritesOnlyField impl π) {t : spec.Domain} {s : σ}
    {z : spec.Range t × σ} (hz : z ∈ support ((impl t).run s)) :
    π z.2 = π s :=
  h t s z hz

/-- Projection preservation is stable under weakening by equality of
implementations. -/
theorem of_eq {impl impl' : QueryImpl spec (StateT σ m)} {π : σ → ρ}
    (himpl : impl = impl') (h : WritesOnlyField impl π) :
    WritesOnlyField impl' π := by
  subst himpl
  exact h

end WritesOnlyField

section OracleCompState

variable {ι' : Type} {spec' : OracleSpec ι'}

/-- A per-query projection footprint lifts to the whole simulated computation. -/
theorem WritesOnlyField.run_preserves
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))} {π : σ → ρ}
    {α : Type} (h : WritesOnlyField impl π) (oa : OracleComp spec α)
    (s : σ) {z : α × σ}
    (hz : z ∈ support ((simulateQ impl oa).run s)) :
    π z.2 = π s := by
  have hpres := OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := impl) (inv := fun s' => π s' = π s)
    (hinv := by
      intro t s' hs' y hy
      exact (h.step_preserves hy).trans hs')
    oa s rfl
  exact hpres z hz

end OracleCompState

end QueryImpl
