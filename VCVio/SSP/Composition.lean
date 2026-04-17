/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.SSP.Package
import VCVio.OracleComp.Coercions.Add

/-!
# State-Separating Proofs: Composition

This file defines the two basic composition operators on `Package`s and proves the
program-level reduction lemmas relating their `simulateQ` and `run` to nested calls.

* `Package.link` — sequential composition. Given an outer package importing `M` and exporting
  `E`, and an inner package importing `I` and exporting `M`, produce a single package importing
  `I` and exporting `E`, with state `σ₁ × σ₂`.
* `Package.par` — parallel composition. Given two packages with disjoint export and import
  interfaces, combine them into a single package on the disjoint sums `I₁ + I₂` and `E₁ + E₂`,
  with state `σ₁ × σ₂`.
* `Package.simulateQ_link_run`, `Package.run_link`, `Package.run_link_ofStateless` — the
  unbundled and bundled program-equivalence forms of the SSP "reduction lemma" for `link`.

These correspond to SSProve's `link` and `par`. Disjointness of the two state factors is
structural: each side's handler can only modify its own factor, so non-interference is a
type-level fact rather than a separation predicate that needs to be proved.

## Universe layout

All five "module" universes (the indices `uᵢ, uₘ, uₑ` and the import-range universe `vᵢ`)
are independent. Both packages on either side of `link` must agree on the universe `v` of
their export ranges and state, since `link`'s product state lives in `Type v`. Likewise
`par` requires the import ranges of `p₁` and `p₂` to share a universe (so `+` for
`OracleSpec` typechecks), and similarly for the export ranges.
-/

universe uᵢ uₘ uₑ vᵢ v

open OracleSpec OracleComp

namespace VCVio.SSP

namespace Package

variable {ιᵢ : Type uᵢ} {ιₘ : Type uₘ} {ιₑ : Type uₑ}
  {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {M : OracleSpec.{uₘ, v} ιₘ} {E : OracleSpec.{uₑ, v} ιₑ}
  {σ₁ σ₂ : Type v}

/-! ### Sequential composition (`link`) -/

/-- The `Prod` reshape `(α × s₁) × s₂ → α × (s₁ × s₂)` used by the linked package's handler to
splice the outer state onto the left of the inner state. All three type arguments are implicit
so that the pointfree `linkReshape <$> _` reads cleanly at use sites. -/
@[reducible]
def linkReshape {α : Type v} {s₁ : Type v} {s₂ : Type v} :
    (α × s₁) × s₂ → α × (s₁ × s₂) := fun p => (p.1.1, (p.1.2, p.2))

/-- Sequential composition of two packages: `outer ∘ inner`.

The outer package exports `E` and imports `M`. The inner package exports `M` and imports `I`.
The composite exports `E` and imports `I`, with state `σ₁ × σ₂` (outer state on the left,
inner state on the right). Each export query of the composite runs the outer handler in
state `σ₁`, then re-interprets every import-query in `M` it issues by running the inner
handler in state `σ₂`. -/
@[simps init]
def link (outer : Package M E σ₁) (inner : Package I M σ₂) : Package I E (σ₁ × σ₂) where
  init := (outer.init, inner.init)
  impl t := StateT.mk fun (s₁, s₂) =>
    let outerStep : OracleComp M (E.Range t × σ₁) := (outer.impl t).run s₁
    let innerStep : OracleComp I ((E.Range t × σ₁) × σ₂) :=
      (simulateQ inner.impl outerStep).run s₂
    linkReshape <$> innerStep

/-- Sanity check: linking with the identity package on the right keeps the outer state, with
a `PUnit` placeholder on the right. The full state-isomorphism `σ × PUnit ≃ σ` is left to
follow-up files; this lemma only requires the `Package`'s import / export range universes to
agree with the identity package's range universe. -/
@[simp]
lemma link_id_init {ι : Type uₘ} (M' : OracleSpec.{uₘ, v} ι) (P : Package M' E σ₁) :
    (P.link (Package.id M')).init = (P.init, PUnit.unit) := rfl

/-! ### `link` reduction lemmas -/

/-- Structural fact: running `(P.link Q).impl` is the same as nesting the simulations,
threaded through both states. This is the unbundled form from which the SSP reduction
lemma follows.

Statement:
`(simulateQ (P.link Q).impl A).run (s₁, s₂) =`
`  reshape <$> (simulateQ Q.impl ((simulateQ P.impl A).run s₁)).run s₂`. -/
theorem simulateQ_link_run {α : Type v}
    (P : Package M E σ₁) (Q : Package I M σ₂)
    (A : OracleComp E α) (s₁ : σ₁) (s₂ : σ₂) :
    (simulateQ (P.link Q).impl A).run (s₁, s₂) =
      linkReshape <$>
        (simulateQ Q.impl ((simulateQ P.impl A).run s₁)).run s₂ := by
  induction A using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure x =>
    -- Both sides reduce to `pure (x, (s₁, s₂)) : OracleComp I _`.
    change (pure (x, (s₁, s₂)) : OracleComp I (α × (σ₁ × σ₂))) =
      linkReshape <$> (simulateQ Q.impl (pure (x, s₁))).run s₂
    rw [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    -- Step 1: rewrite LHS using the definition of `(P.link Q).impl t` and StateT bind.
    have hLHS : (simulateQ (P.link Q).impl (liftM (query t) >>= k)).run (s₁, s₂) =
        (simulateQ Q.impl ((P.impl t).run s₁)).run s₂ >>=
          fun (p : (E.Range t × σ₁) × σ₂) =>
            (simulateQ (P.link Q).impl (k p.1.1)).run (p.1.2, p.2) := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change ((P.link Q).impl t >>= fun a => simulateQ (P.link Q).impl (k a)).run (s₁, s₂) = _
      rw [StateT.run_bind]
      change (linkReshape <$>
          (simulateQ Q.impl ((P.impl t).run s₁)).run s₂) >>= _ = _
      rw [bind_map_left]
    -- Step 2: rewrite RHS using simulateQ_bind for both monads and StateT bind.
    have hRHS : (simulateQ Q.impl ((simulateQ P.impl (liftM (query t) >>= k)).run s₁)).run s₂ =
        (simulateQ Q.impl ((P.impl t).run s₁)).run s₂ >>=
          fun (p : (E.Range t × σ₁) × σ₂) =>
            (simulateQ Q.impl ((simulateQ P.impl (k p.1.1)).run p.1.2)).run p.2 := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change (simulateQ Q.impl ((P.impl t >>=
          fun a => simulateQ P.impl (k a)).run s₁)).run s₂ = _
      rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
    -- Step 3: combine, then map and use the IH pointwise.
    rw [hLHS, hRHS, map_bind]
    refine bind_congr fun p => ?_
    exact ih p.1.1 p.1.2 p.2

/-- The SSP **reduction lemma** in its program-equivalence form: linking the outer reduction
package `P` to game `Q` and running against adversary `A` produces the same `OracleComp`
output distribution as running `Q` against `simulateQ P.impl A` (the "outer-shifted"
adversary).

This is the analogue of SSProve's `swap_link_left` / `link_assoc`-driven move that turns
`A ∘ (P ∘ Q)` into `(A ∘ P) ∘ Q` at the level of distributions. -/
theorem run_link {α : Type v}
    (P : Package M E σ₁) (Q : Package I M σ₂) (A : OracleComp E α) :
    (P.link Q).run A =
      (Prod.fst : α × σ₁ → α) <$>
        (simulateQ Q.impl ((simulateQ P.impl A).run P.init)).run' Q.init := by
  change (Prod.fst : α × (σ₁ × σ₂) → α) <$>
      (simulateQ (P.link Q).impl A).run (P.init, Q.init) = _
  rw [simulateQ_link_run, StateT.run'_eq, ← Functor.map_map]
  simp [linkReshape]

/-- Specialization of `run_link` when only the *outer* (left) package is stateless. The
`PUnit` factor on the outer side collapses, leaving only the inner package's state to thread.

This is the key reduction lemma for SSP-style proofs where the reduction package is stateless
but the underlying game package carries non-trivial state (such as a lazily sampled secret
key or a cached oracle output).

Not marked `@[simp]`: the data premise `hP : QueryImpl E (OracleComp M)` cannot be pattern-
matched on, so a `@[simp]` tag here would loop with `run_link`. Use explicitly. -/
theorem run_link_left_ofStateless {α : Type v}
    (hP : QueryImpl E (OracleComp M)) (Q : Package I M σ₂) (A : OracleComp E α) :
    ((Package.ofStateless hP).link Q).run A =
      (Prod.fst : α × σ₂ → α) <$>
        (simulateQ Q.impl (simulateQ hP A)).run Q.init := by
  rw [run_link]
  have h1 : (simulateQ (Package.ofStateless hP).impl A).run (Package.ofStateless hP).init
      = (·, PUnit.unit.{v + 1}) <$> simulateQ hP A := runState_ofStateless hP A
  rw [h1, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

/-- Specialization of `run_link` for two stateless packages. The link of two `ofStateless`
packages reduces to nested `simulateQ` calls without any state to thread. -/
@[simp]
theorem run_link_ofStateless {α : Type v}
    (hP : QueryImpl E (OracleComp M)) (hQ : QueryImpl M (OracleComp I))
    (A : OracleComp E α) :
    ((Package.ofStateless hP).link (Package.ofStateless hQ)).run A =
      simulateQ hQ (simulateQ hP A) := by
  -- Direct induction on `A`. Both sides are functorial in `A`; the only base case is
  -- `pure x`, which trivially gives `pure x` on both sides; the inductive case threads
  -- through a query then continues by induction.
  induction A using OracleComp.inductionOn with
  | pure x =>
    simp only [Package.run, Package.link, Package.ofStateless, simulateQ_pure]
    rfl
  | query_bind t k ih =>
    -- LHS: rewrite via `run_link` and the runState facts for stateless packages.
    have hLHS := run_link (Package.ofStateless hP) (Package.ofStateless hQ)
      (liftM (query t) >>= k)
    -- Rewrite the inner `simulateQ` of the outer stateless package using
    -- `runState_ofStateless` (which is exactly `(simulateQ ... ).run PUnit.unit`).
    have hP_runState : ∀ (β : Type v) (B : OracleComp E β),
        (simulateQ (Package.ofStateless hP).impl B).run PUnit.unit
          = (·, PUnit.unit.{v + 1}) <$> simulateQ hP B := fun _ B => runState_ofStateless hP B
    have hQ_runState : ∀ (β : Type v) (B : OracleComp M β),
        (simulateQ (Package.ofStateless hQ).impl B).run PUnit.unit
          = (·, PUnit.unit.{v + 1}) <$> simulateQ hQ B := fun _ B => runState_ofStateless hQ B
    rw [hLHS]
    -- Now the goal involves `(simulateQ Q.impl ((simulateQ P.impl _).run PUnit.unit)).run'
    -- PUnit.unit`. Apply `hP_runState` to the inner term.
    change Prod.fst <$> (simulateQ (Package.ofStateless hQ).impl
        ((simulateQ (Package.ofStateless hP).impl (liftM (query t) >>= k)).run
          PUnit.unit)).run' PUnit.unit = _
    rw [hP_runState]
    -- Now `simulateQ (ofStateless hQ).impl ((·, PUnit.unit) <$> simulateQ hP _)`.
    -- Use `simulateQ_map` to pull the map out, then `runState_ofStateless` again.
    rw [simulateQ_map]
    -- Now we have a `(·, PUnit.unit) <$> simulateQ ...` inside `StateT PUnit (OracleComp I)`.
    -- Reduce `.run' PUnit.unit` of that to a plain `OracleComp I` map.
    rw [StateT.run'_eq, StateT.run_map, hQ_runState]
    simp [Functor.map_map]

/-! ### Parallel composition (`par`)

The two summed specs in `par` must share the import range universe and the export range
universe (otherwise the disjoint sums `I₁ + I₂` and `E₁ + E₂` cannot share a single
`OracleSpec` type). To keep `par` mostly universe polymorphic, we additionally collapse the
import and export range universes to the same `v`; this matches the typing pattern induced by
`liftComp` from `OracleComp Iᵢ` into `OracleComp (I₁ + I₂)`. The index universes remain
independent. -/

variable {ιᵢ₁ : Type uᵢ} {ιᵢ₂ : Type uᵢ} {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
  {I₁ : OracleSpec.{uᵢ, v} ιᵢ₁} {I₂ : OracleSpec.{uᵢ, v} ιᵢ₂}
  {E₁ : OracleSpec.{uₑ, v} ιₑ₁} {E₂ : OracleSpec.{uₑ, v} ιₑ₂}

/-- Parallel composition of two packages.

Given `p₁` exporting `E₁` and importing `I₁`, and `p₂` exporting `E₂` and importing `I₂`, the
parallel composite exports the disjoint sum `E₁ + E₂` and imports the disjoint sum `I₁ + I₂`.
Each side's handler is lifted along the obvious `OracleComp Iᵢ ⊂ₒ OracleComp (I₁ + I₂)` and
the resulting state is the product `σ₁ × σ₂`.

State separation is automatic: each side's handler can only access its own state component, so
modifications to the other side are behaviorally invisible. This is the structural-typing
counterpart of SSProve's `fseparate` side-condition.

We do not use `QueryImpl.prodStateT` here because of awkward universe unification through
`OracleSpec` sums; the body is the same up to the obvious lifts. -/
def par (p₁ : Package I₁ E₁ σ₁) (p₂ : Package I₂ E₂ σ₂) :
    Package (I₁ + I₂) (E₁ + E₂) (σ₁ × σ₂) where
  init := (p₁.init, p₂.init)
  impl
    | .inl t => StateT.mk fun (s₁, s₂) =>
        (Prod.map _root_.id (·, s₂)) <$> liftComp ((p₁.impl t).run s₁) (I₁ + I₂)
    | .inr t => StateT.mk fun (s₁, s₂) =>
        (Prod.map _root_.id (s₁, ·)) <$> liftComp ((p₂.impl t).run s₂) (I₁ + I₂)

@[simp]
lemma par_init (p₁ : Package I₁ E₁ σ₁) (p₂ : Package I₂ E₂ σ₂) :
    (p₁.par p₂).init = (p₁.init, p₂.init) := rfl

end Package

/-! ### Universe-polymorphism sanity checks for `link` and `par` -/

section UniverseTests

/-- `link` accepts independent index universes for `I`, `M`, `E` and an independent import
range universe `vᵢ`. -/
example {ιᵢ : Type uᵢ} {ιₘ : Type uₘ} {ιₑ : Type uₑ}
    {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {M : OracleSpec.{uₘ, v} ιₘ} {E : OracleSpec.{uₑ, v} ιₑ}
    {σ₁ σ₂ : Type v} (P : Package M E σ₁) (Q : Package I M σ₂) :
    Package I E (σ₁ × σ₂) := P.link Q

/-- `par` accepts independent index universes for `I₁, I₂, E₁, E₂` provided the import range
universe and the export range universe each match within their pair (and equal each other). -/
example {ιᵢ₁ : Type uᵢ} {ιᵢ₂ : Type uᵢ} {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
    {I₁ : OracleSpec.{uᵢ, v} ιᵢ₁} {I₂ : OracleSpec.{uᵢ, v} ιᵢ₂}
    {E₁ : OracleSpec.{uₑ, v} ιₑ₁} {E₂ : OracleSpec.{uₑ, v} ιₑ₂}
    {σ₁ σ₂ : Type v} (p₁ : Package I₁ E₁ σ₁) (p₂ : Package I₂ E₂ σ₂) :
    Package (I₁ + I₂) (E₁ + E₂) (σ₁ × σ₂) := p₁.par p₂

end UniverseTests

end VCVio.SSP
