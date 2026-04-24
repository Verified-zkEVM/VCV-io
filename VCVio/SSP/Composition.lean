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
* `Package.shiftLeft` — the SSP "absorb the outer reduction into the adversary" move, from
  which the program-level reduction lemma `run_link_eq_run_shiftLeft` follows.
* `Package.simulateQ_link_run`, `Package.run_link_eq_run_shiftLeft`,
  `Package.run_link_ofStateless`, `Package.run_link_left_ofStateless` — the program-equivalence
  forms of the SSP "reduction lemma" for `link`.

These correspond to SSProve's `link` and `par`. Disjointness of the two state factors is
structural: each side's handler can only modify its own factor, so non-interference is a
type-level fact rather than a separation predicate that needs to be proved.

Making `init : OracleComp I σ` monadic (rather than a raw `σ`) means that `link`'s composite
init must *shift* the outer package's init through the inner handler: running `outer.init` is a
computation in `M`, but the composite lives in `I`, so we simulate it against `inner.impl`
starting from `inner.init`. This is the init-level analogue of the handler-level shift carried
out by `simulateQ_link_run`. Similarly `par`'s composite init is the pair of both inits lifted
to the sum spec `I₁ + I₂`.

## Universe layout

The index universes `uᵢ, uₘ, uₑ` for the three specs and the import range universe `vᵢ` (for
the outer composition's innermost imports) are all independent. The intermediate range
`M.Range`, export range `E.Range`, and state factors `σ₁, σ₂` share a single universe `v`,
because the handlers produce values of type `StateT σᵢ (OracleComp _) (·.Range _)` and the
reduction lemmas need to identify the two sides. The monadic `init : OracleComp I σ` adds no
extra constraint, since `OracleComp I` is universe-polymorphic in its value type.

For `par` the same pattern repeats with two disjoint imports `I₁, I₂` sharing a common range
universe `v` (tied to `E₁ + E₂` and the states).
-/

universe uᵢ uₘ uₑ vᵢ v

open OracleSpec OracleComp

/-! Locally rebind `query` to the primitive `OracleSpec.query` form. See
the same construct in `VCVio.OracleComp.OracleComp`. -/
local notation "query" => OracleSpec.query

namespace VCVio.SSP

namespace Package

variable {ιᵢ : Type uᵢ} {ιₘ : Type uₘ} {ιₑ : Type uₑ}
  {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {M : OracleSpec.{uₘ, v} ιₘ} {E : OracleSpec.{uₑ, v} ιₑ}
  {σ₁ σ₂ : Type v}

/-! ### Sequential composition (`link`) -/

/-- The `Prod` reshape `(α × s₁) × s₂ → α × (s₁ × s₂)` used by the linked package's handler to
splice the outer state onto the left of the inner state. All three type arguments are implicit
so that the pointfree `linkReshape <$> _` reads cleanly at use sites.

`private` because this function is a purely internal gadget used by `link` and its reduction
lemmas; external callers should use `Package.link` / `Package.run_link_eq_run_shiftLeft`
directly. -/
@[reducible]
private def linkReshape {α : Type v} {s₁ : Type v} {s₂ : Type v} :
    (α × s₁) × s₂ → α × (s₁ × s₂) := fun p => (p.1.1, (p.1.2, p.2))

/-- Sequential composition of two packages: `outer ∘ inner`.

The outer package exports `E` and imports `M`. The inner package exports `M` and imports `I`.
The composite exports `E` and imports `I`, with state `σ₁ × σ₂` (outer state on the left,
inner state on the right).

* **Init.** The composite init lives in `OracleComp I (σ₁ × σ₂)`. The outer init
  `outer.init : OracleComp M σ₁` may query `M`, so we simulate it against `inner.impl` starting
  from `inner.init`'s initial state, threading the inner state and producing the composite
  state pair.
* **Handler.** Each export query of the composite runs the outer handler in state `σ₁`, then
  re-interprets every import-query in `M` it issues by running the inner handler in state
  `σ₂`. -/
def link (outer : Package M E σ₁) (inner : Package I M σ₂) : Package I E (σ₁ × σ₂) where
  init := do
    let s₂₀ ← inner.init
    (simulateQ inner.impl outer.init).run s₂₀
  impl t := StateT.mk fun (s₁, s₂) =>
    let outerStep : OracleComp M (E.Range t × σ₁) := (outer.impl t).run s₁
    let innerStep : OracleComp I ((E.Range t × σ₁) × σ₂) :=
      (simulateQ inner.impl outerStep).run s₂
    linkReshape <$> innerStep

@[simp]
lemma link_init (outer : Package M E σ₁) (inner : Package I M σ₂) :
    (outer.link inner).init =
      inner.init >>= fun s₂₀ => (simulateQ inner.impl outer.init).run s₂₀ := rfl

/-- Sanity check: linking with the identity package on the right keeps the outer init's
distribution, paired with a `PUnit` placeholder for the inner state. The full state-isomorphism
`σ × PUnit ≃ σ` is left to follow-up files. -/
lemma link_id_init {ι : Type uₘ} (M' : OracleSpec.{uₘ, v} ι) (P : Package M' E σ₁) :
    (P.link (Package.id M')).init =
      (fun s₁ => (s₁, PUnit.unit)) <$> P.init := by
  -- `(Package.id M').init = pure PUnit.unit`, so the outer bind over the inner init collapses.
  -- The remaining `simulateQ (Package.id M').impl P.init` is pointwise the identity on
  -- `OracleComp M'`, and `StateT.run` on a `PUnit` state just tags each value with `PUnit.unit`.
  simp only [link_init, Package.id_init, pure_bind]
  -- Reduce `(simulateQ (Package.id M').impl P.init).run PUnit.unit` to
  -- `(·, PUnit.unit) <$> P.init`.
  induction P.init using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, Package.id_impl,
      OracleQuery.input_query, monadLift_self, StateT.run_monadLift,
      bind_assoc, pure_bind, map_bind]
    refine bind_congr fun u => ?_
    exact ih u

/-! ### `link` reduction lemmas -/

/-- Structural fact: running `(P.link Q).impl` is the same as nesting the simulations,
threaded through both states. This is the unbundled handler-level form from which the SSP
reduction lemma follows. It does not mention `init`, so it is unaffected by the move to monadic
init.

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
    change (pure (x, (s₁, s₂)) : OracleComp I (α × (σ₁ × σ₂))) =
      linkReshape <$> (simulateQ Q.impl (pure (x, s₁))).run s₂
    rw [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
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
    have hRHS : (simulateQ Q.impl ((simulateQ P.impl (liftM (query t) >>= k)).run s₁)).run s₂ =
        (simulateQ Q.impl ((P.impl t).run s₁)).run s₂ >>=
          fun (p : (E.Range t × σ₁) × σ₂) =>
            (simulateQ Q.impl ((simulateQ P.impl (k p.1.1)).run p.1.2)).run p.2 := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change (simulateQ Q.impl ((P.impl t >>=
          fun a => simulateQ P.impl (k a)).run s₁)).run s₂ = _
      rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
    rw [hLHS, hRHS, map_bind]
    refine bind_congr fun p => ?_
    exact ih p.1.1 p.1.2 p.2

/-! ### Shifted adversary and the program-level SSP reduction -/

/-- The **shifted adversary** obtained by absorbing the outer reduction package `P` into the
adversary. Given an outer reduction `P : Package M E σ₁` and an external adversary
`A : OracleComp E α` querying the export interface `E`, this returns an adversary against the
intermediate interface `M` by first running `P.init`, then simulating `A` through `P.impl` and
projecting away the final outer state.

This is the SSP "reduction-to-the-distinguisher" move: the outer package (both its init and
its handler) becomes part of the adversary, so a fresh round of analysis only needs to
consider the inner game. -/
def shiftLeft (P : Package M E σ₁) {α : Type v} (A : OracleComp E α) :
    OracleComp M α :=
  P.init >>= fun s₁ => Prod.fst <$> (simulateQ P.impl A).run s₁

/-- Running `shiftLeft` on a pure adversary `pure x` still executes `P.init` (the monadic init
is observed), then returns `x`. This is the monadic-init weakening of the old
`P.shiftLeft (pure x) = pure x`: under any probabilistic interpretation of `P.init` the result
distribution is still `pure x`, but the two sides are no longer propositionally equal as
`OracleComp` programs. -/
@[simp]
lemma shiftLeft_pure (P : Package M E σ₁) {α : Type v} (x : α) :
    P.shiftLeft (pure x) = P.init >>= fun _ => pure x := by
  simp [shiftLeft, simulateQ_pure, StateT.run_pure, bind_pure_comp]

/-- **SSP reduction (program form).** Running the linked game `(P.link Q)` against adversary
`A` produces the same `OracleComp` distribution as running the inner game `Q` against the
*shifted* adversary `P.shiftLeft A`.

This identity is preserved verbatim under monadic init: `(P.link Q).init` bakes the "run
`P.init`'s `M`-queries through `Q.impl`" move into the composite init (definitionally equal
to `Q.runState P.init`), and `P.shiftLeft` bakes the "run `P.init`" move into the adversary.
The two moves commute exactly, so the advantage-level corollary in `VCVio.SSP.Hybrid` goes
through with the same proof structure as before. -/
theorem run_link_eq_run_shiftLeft {α : Type v}
    (P : Package M E σ₁) (Q : Package I M σ₂) (A : OracleComp E α) :
    (P.link Q).run A = Q.run (P.shiftLeft A) := by
  -- Normalise both sides to `Q.runState P.init >>= F` where `F` is the "extract `α` from the
  -- inner-nested simulation" map.
  set F : σ₁ × σ₂ → OracleComp I α := fun sPs_Q =>
    (fun x : (α × σ₁) × σ₂ => x.1.1) <$>
      (simulateQ Q.impl ((simulateQ P.impl A).run sPs_Q.1)).run sPs_Q.2 with hF
  have hLHS : (P.link Q).run A = Q.runState P.init >>= F := by
    change (P.link Q).init >>= (fun s₀ => (simulateQ (P.link Q).impl A).run' s₀) = _
    rw [show (P.link Q).init = Q.runState P.init from rfl]
    refine bind_congr fun sPs_Q => ?_
    rw [StateT.run'_eq,
        show (simulateQ (P.link Q).impl A).run sPs_Q
          = (simulateQ (P.link Q).impl A).run (sPs_Q.1, sPs_Q.2) from rfl,
        simulateQ_link_run]
    simp [hF, Functor.map_map]
  have hRHS : Q.run (P.shiftLeft A) = Q.runState P.init >>= F := by
    change Q.init >>= (fun s_Q₀ => (simulateQ Q.impl (P.shiftLeft A)).run' s_Q₀) = _
    unfold Package.shiftLeft
    simp only [StateT.run'_eq, simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
      map_bind, Package.runState, bind_assoc]
    refine bind_congr fun s_Q => ?_
    refine bind_congr fun sPs_Q => ?_
    simp [hF, Functor.map_map]
  rw [hLHS, hRHS]

/-- Specialization of `run_link_eq_run_shiftLeft` when only the *outer* (left) package is
stateless. The `PUnit` factor on the outer side collapses, leaving only the inner game's run
against the bare simulation `simulateQ hP A`.

This is the key reduction lemma for SSP-style proofs where the reduction package is stateless
but the underlying game package carries non-trivial state (such as a lazily sampled secret
key or a cached oracle output).

Not marked `@[simp]`: the data premise `hP : QueryImpl E (OracleComp M)` cannot be pattern-
matched on, so a `@[simp]` tag here would loop with `run_link_eq_run_shiftLeft`. Use
explicitly. -/
theorem run_link_left_ofStateless {α : Type v}
    (hP : QueryImpl E (OracleComp M)) (Q : Package I M σ₂) (A : OracleComp E α) :
    ((Package.ofStateless hP).link Q).run A = Q.run (simulateQ hP A) := by
  rw [run_link_eq_run_shiftLeft]
  -- `shiftLeft` on `ofStateless hP` collapses: init is `pure PUnit.unit`, and the handler's
  -- `simulateQ` reduces to `simulateQ hP` with a spurious PUnit tag that is then projected away.
  have hshift : (Package.ofStateless hP).shiftLeft A = simulateQ hP A := by
    simp only [shiftLeft, ofStateless_init, pure_bind]
    -- Goal: `Prod.fst <$> (simulateQ (ofStateless hP).impl A).run PUnit.unit = simulateQ hP A`.
    have hrun := runState_ofStateless hP A
    rw [show (Package.ofStateless hP).runState A
          = (simulateQ (Package.ofStateless hP).impl A).run PUnit.unit from by
        simp [Package.runState, Package.ofStateless_init]] at hrun
    rw [hrun, ← Functor.map_map]
    simp
  rw [hshift]

/-- Specialization of `run_link_eq_run_shiftLeft` for two stateless packages. The link of two
`ofStateless` packages reduces to nested `simulateQ` calls without any state to thread. -/
@[simp]
theorem run_link_ofStateless {α : Type v}
    (hP : QueryImpl E (OracleComp M)) (hQ : QueryImpl M (OracleComp I))
    (A : OracleComp E α) :
    ((Package.ofStateless hP).link (Package.ofStateless hQ)).run A =
      simulateQ hQ (simulateQ hP A) := by
  rw [run_link_left_ofStateless, run_ofStateless]

/-! ### Parallel composition (`par`)

The two summed specs in `par` must share the import range universe and the export range
universe (otherwise the disjoint sums `I₁ + I₂` and `E₁ + E₂` cannot share a single
`OracleSpec` type). The state factors then live in this same universe `v` because the
handlers produce values in `StateT σᵢ (OracleComp _) (·.Range _)`. The index universes
remain independent. -/

variable {ιᵢ₁ : Type uᵢ} {ιᵢ₂ : Type uᵢ} {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
  {I₁ : OracleSpec.{uᵢ, v} ιᵢ₁} {I₂ : OracleSpec.{uᵢ, v} ιᵢ₂}
  {E₁ : OracleSpec.{uₑ, v} ιₑ₁} {E₂ : OracleSpec.{uₑ, v} ιₑ₂}

/-- Parallel composition of two packages.

Given `p₁` exporting `E₁` and importing `I₁`, and `p₂` exporting `E₂` and importing `I₂`, the
parallel composite exports the disjoint sum `E₁ + E₂` and imports the disjoint sum `I₁ + I₂`.
Each side's handler is lifted along the obvious `OracleComp Iᵢ ⊂ₒ OracleComp (I₁ + I₂)` and
the resulting state is the product `σ₁ × σ₂`.

The composite init runs each side's init under the sum import spec, in order; since the two
inits touch disjoint imports (and in particular no shared state), the order is immaterial from
the distributional point of view.

State separation is automatic: each side's handler can only access its own state component, so
modifications to the other side are behaviorally invisible. This is the structural-typing
counterpart of SSProve's `fseparate` side-condition.

We do not use `QueryImpl.prodStateT` here because of awkward universe unification through
`OracleSpec` sums; the body is the same up to the obvious lifts. -/
def par (p₁ : Package I₁ E₁ σ₁) (p₂ : Package I₂ E₂ σ₂) :
    Package (I₁ + I₂) (E₁ + E₂) (σ₁ × σ₂) where
  init := do
    let s₁ ← liftComp p₁.init (I₁ + I₂)
    let s₂ ← liftComp p₂.init (I₁ + I₂)
    pure (s₁, s₂)
  impl
    | .inl t => StateT.mk fun (s₁, s₂) =>
        (Prod.map id (·, s₂)) <$> liftComp ((p₁.impl t).run s₁) (I₁ + I₂)
    | .inr t => StateT.mk fun (s₁, s₂) =>
        (Prod.map id (s₁, ·)) <$> liftComp ((p₂.impl t).run s₂) (I₁ + I₂)

@[simp]
lemma par_init (p₁ : Package I₁ E₁ σ₁) (p₂ : Package I₂ E₂ σ₂) :
    (p₁.par p₂).init =
      liftComp p₁.init (I₁ + I₂) >>= fun s₁ =>
      liftComp p₂.init (I₁ + I₂) >>= fun s₂ =>
      pure (s₁, s₂) := rfl

end Package

/-! ### Universe-polymorphism sanity checks for `link` and `par` -/

section UniverseTests

/-- `link` accepts independent index universes for `I`, `M`, `E`, and an independent import
range universe `vᵢ` for `I`. Only the intermediate / export ranges and the state factors share
the universe `v`, because the handler and the composite state type tie them together. -/
example {ιᵢ : Type uᵢ} {ιₘ : Type uₘ} {ιₑ : Type uₑ}
    {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {M : OracleSpec.{uₘ, v} ιₘ} {E : OracleSpec.{uₑ, v} ιₑ}
    {σ₁ σ₂ : Type v} (P : Package M E σ₁) (Q : Package I M σ₂) :
    Package I E (σ₁ × σ₂) := P.link Q

/-- `par` accepts independent index universes for `I₁, I₂, E₁, E₂`. As with `link`, the range
and state universe is shared across all four specs and both state factors. -/
example {ιᵢ₁ : Type uᵢ} {ιᵢ₂ : Type uᵢ} {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
    {I₁ : OracleSpec.{uᵢ, v} ιᵢ₁} {I₂ : OracleSpec.{uᵢ, v} ιᵢ₂}
    {E₁ : OracleSpec.{uₑ, v} ιₑ₁} {E₂ : OracleSpec.{uₑ, v} ιₑ₂}
    {σ₁ σ₂ : Type v} (p₁ : Package I₁ E₁ σ₁) (p₂ : Package I₂ E₂ σ₂) :
    Package (I₁ + I₂) (E₁ + E₂) (σ₁ × σ₂) := p₁.par p₂

end UniverseTests

end VCVio.SSP
