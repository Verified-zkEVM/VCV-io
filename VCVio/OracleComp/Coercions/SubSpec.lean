/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.EvalDist
import ToMathlib.General

/-!
# Coercions Between Computations With Additional Oracles

This file defines the `SubSpec` relation between pairs of `OracleSpec`s. An
instance `spec ⊂ₒ superSpec` packages the data of a polynomial-functor lens
between the underlying `PFunctor`s, given by

* `onQuery : spec.Domain → superSpec.Domain` --- forward translation on query
  inputs (oracle indices), and
* `onResponse : (t : spec.Domain) → superSpec.Range (onQuery t) → spec.Range t`
  --- fiberwise backward translation on query responses.

By the Yoneda lemma this lens data is in bijection with natural transformations
`OracleQuery spec → OracleQuery superSpec`. The class therefore `extends
MonadLift (OracleQuery spec) (OracleQuery superSpec)`. Concrete instances
spell `monadLift` out alongside the lens data and discharge the
propositional coherence `liftM_eq_lift` (typically `rfl`); see the class
docstring for why the `monadLift` field is not defaulted.

We use the notation `spec ⊂ₒ spec'` to represent this inclusion. The
non-inclusive subset symbol reflects that we avoid defining `SubSpec`
reflexively, since `MonadLiftT.refl` already handles the identity case.

`LawfulSubSpec` refines `SubSpec` with the requirement that `onResponse` is
bijective on every fiber. This is exactly the data of a `PFunctor.Equiv`-style
embedding and is what is needed to preserve the uniform distribution under
lifting.
-/

open OracleSpec OracleComp BigOperators ENNReal

universe u u' v v' w w'

variable {ι : Type u} {τ : Type v}
  {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α β γ : Type w}

namespace OracleSpec

/-- Inclusion of one set of oracles into another, packaged as a polynomial-functor
lens between the underlying `OracleSpec`s. Carries the forward translation
`onQuery` on query inputs and the fiberwise backward translation `onResponse`
on query responses, plus the resulting `MonadLift` action.

We `extends MonadLift (OracleQuery spec) (OracleQuery superSpec)` so that
typeclass synthesis can derive `MonadLift` (and therefore `MonadLiftT`)
through the structure projection `SubSpec.toMonadLift`. The `monadLift`
field is **not** defaulted: each concrete `SubSpec` instance must spell it
out, alongside `onQuery` / `onResponse`, and discharge the propositional
coherence `liftM_eq_lift` (typically by `rfl`).

Spelling `monadLift` out explicitly (rather than defaulting it from the
lens data) is what makes the lifted query fully reduce during `rw` / `simp`
pattern matching against lemmas like `probEvent_liftComp`. A defaulted
`monadLift` field becomes opaque to `isDefEq` once it travels through the
`MonadLiftT` instance chain, which silently breaks rewriting.

Informally, `spec ⊂ₒ superSpec` says that any query to an oracle of `spec`
can be perfectly simulated by a query to an oracle of `superSpec`. We avoid
the built-in `Subset` notation because we care about the actual data of the
mapping (it is needed when defining type coercions), not just its existence. -/
class SubSpec (spec : OracleSpec.{u, w} ι) (superSpec : OracleSpec.{v, w} τ)
    extends MonadLift (OracleQuery spec) (OracleQuery superSpec) where
  /-- Forward translation on query inputs (oracle indices). -/
  onQuery : spec.Domain → superSpec.Domain
  /-- Fiberwise backward translation on query responses. -/
  onResponse : (t : spec.Domain) → superSpec.Range (onQuery t) → spec.Range t
  /-- Coherence between the `MonadLift` action and the lens data: lifting a
  query is the lens applied to that query. Concrete instances supply
  `monadLift` directly in the lens form, making this `rfl`. -/
  liftM_eq_lift : ∀ {β : Type w} (q : OracleQuery spec β),
      monadLift q = ⟨onQuery q.input, q.cont ∘ onResponse q.input⟩ := by
    intros; rfl

@[inherit_doc] infix : 50 " ⊂ₒ " => SubSpec

namespace SubSpec

variable {κ : Type w'} {spec₃ : OracleSpec κ}

/-- The lens action on a single query: forward on the input, post-compose the
backward fiber on the continuation. Used as the canonical reduced form of
`liftM q` for proofs that need to inspect the resulting query. -/
@[reducible] def liftQuery [h : SubSpec spec superSpec] (q : OracleQuery spec α) :
    OracleQuery superSpec α :=
  ⟨h.onQuery q.input, q.cont ∘ h.onResponse q.input⟩

/-- Transitivity of `SubSpec`: lens composition. -/
@[reducible] def trans (h₁ : spec ⊂ₒ superSpec) (h₂ : superSpec ⊂ₒ spec₃) :
    spec ⊂ₒ spec₃ where
  monadLift q :=
    ⟨h₂.onQuery (h₁.onQuery q.input),
      q.cont ∘ h₁.onResponse q.input ∘ h₂.onResponse (h₁.onQuery q.input)⟩
  onQuery t := h₂.onQuery (h₁.onQuery t)
  onResponse t r := h₁.onResponse t (h₂.onResponse (h₁.onQuery t) r)

end SubSpec

/-- `LawfulSubSpec` extends `SubSpec` with the requirement that the backward
translation `onResponse` is bijective on every fiber. Equivalently: the
continuation of each lifted base query `liftM (spec.query t)` is a bijection
from the super-range to the sub-range. This is what is needed to preserve the
uniform distribution under the lift. -/
class LawfulSubSpec (spec : OracleSpec.{u, w} ι) (superSpec : OracleSpec.{v, w} τ)
    [h : SubSpec spec superSpec] : Prop where
  /-- The backward translation is bijective on every fiber. -/
  onResponse_bijective (t : spec.Domain) :
    Function.Bijective (h.onResponse t)

namespace LawfulSubSpec

variable {ι : Type u} {τ : Type v} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [h : spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec]

/-- Pushing the uniform distribution on `superSpec.Range` through the lens's
backward fiber recovers the uniform distribution on `spec.Range`. Load-bearing
for `evalDist_liftComp` below. -/
lemma evalDist_liftM_query [superSpec.Fintype] [superSpec.Inhabited]
    [spec.Fintype] [spec.Inhabited] (t : spec.Domain) :
    (PMF.uniformOfFintype (superSpec.Range
      ((liftM (n := OracleQuery superSpec) (spec.query t)).fst))).map
      ((liftM (n := OracleQuery superSpec) (spec.query t)).snd) =
      PMF.uniformOfFintype (spec.Range t) := by
  have lift_eq : (liftM (spec.query t) : OracleQuery superSpec (spec.Range t)) =
      ⟨h.onQuery t, h.onResponse t⟩ := h.liftM_eq_lift _
  rw [lift_eq]
  exact PMF.uniformOfFintype_map_of_bijective _ (onResponse_bijective t)

end LawfulSubSpec

end OracleSpec


namespace OracleComp

section liftComp

/-- Lift a computation from `spec` to `superSpec` using a `SubSpec` instance on queries.
Usually `liftM` should be preferred but this can allow more explicit annotation. -/
def liftComp (mx : OracleComp spec α) (superSpec : OracleSpec τ)
    [h : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] :
    OracleComp superSpec α :=
    simulateQ (fun t => liftM (spec.query t)) mx

variable (superSpec : OracleSpec τ)
    [h : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]

@[grind =, aesop unsafe norm]
lemma liftComp_def (mx : OracleComp spec α) : liftComp mx superSpec =
    simulateQ (fun t => liftM (spec.query t)) mx := rfl

@[simp]
lemma liftComp_pure (x : α) : liftComp (pure x : OracleComp spec α) superSpec = pure x := rfl

@[simp]
lemma liftComp_query (q : OracleQuery spec α) :
    liftComp (q : OracleComp spec _) superSpec =
      q.cont <$> (liftM (spec.query q.input) : OracleComp superSpec _) := by
  simp [liftComp]

@[simp]
lemma liftComp_bind (mx : OracleComp spec α) (ob : α → OracleComp spec β) :
    liftComp (mx >>= ob) superSpec =
      liftComp mx superSpec >>= fun x ↦ liftComp (ob x) superSpec := by
  grind

@[simp]
lemma liftComp_map (mx : OracleComp spec α) (f : α → β) :
    liftComp (f <$> mx) superSpec = f <$> liftComp mx superSpec := by
  simp [liftComp]

@[simp]
lemma liftComp_seq (og : OracleComp spec (α → β)) (mx : OracleComp spec α) :
    liftComp (og <*> mx) superSpec = liftComp og superSpec <*> liftComp mx superSpec := by
  simp [liftComp, seq_eq_bind_map]

-- NOTE: `liftComp_failure` cannot be stated for `OracleComp spec` because `failure` only exists
-- in `OptionT (OracleComp spec)`, not in `OracleComp spec` itself. `OracleComp` is
-- `PFunctor.FreeM` which has no `Alternative` instance. Use `liftM_failure` in the OptionT
-- section below for the analogous result.

end liftComp

section liftComp_evalDist

variable {ι : Type u} {τ : Type v}
  {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α : Type w}
variable [spec.Fintype] [spec.Inhabited] [superSpec.Fintype] [superSpec.Inhabited]
    [h : spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec]

@[simp] lemma evalDist_liftComp (mx : OracleComp spec α) :
    evalDist (liftComp mx superSpec) = evalDist mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query]
    rw [evalDist_bind, evalDist_bind]; simp_rw [ih]
    congr 1
    simp only [evalDist_eq_simulateQ (spec := superSpec), evalDist_eq_simulateQ (spec := spec),
      simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    congr 1
    exact LawfulSubSpec.evalDist_liftM_query t

@[simp] lemma probOutput_liftComp (mx : OracleComp spec α) (x : α) :
    Pr[= x | liftComp mx superSpec] = Pr[= x | mx] :=
  congrFun (congrArg DFunLike.coe (evalDist_liftComp mx)) x

@[simp] lemma probEvent_liftComp (mx : OracleComp spec α) (p : α → Prop) :
    Pr[ p | liftComp mx superSpec] = Pr[ p | mx] := by
  simp only [probEvent_eq_tsum_indicator]
  congr 1; funext x
  simp only [probOutput_liftComp]

end liftComp_evalDist

/-- Extend a lifting on `OracleQuery` to a lifting on `OracleComp`.

Registered as a low-priority `MonadLift` (not `MonadLiftT`) so that:

* For `spec = superSpec`, Lean's built-in `MonadLiftT.refl` (which is
  definitionally `id`) wins typeclass resolution. This is what
  `Std.Do.Spec.UnfoldLift.monadLift_refl` (a `rfl`-based lemma) needs in
  order to peel off spurious self-lifts inside `mvcgen`-elaborated terms.

* For `MonadLiftT (OracleQuery spec) (OracleComp superSpec)`, the built-in
  high-priority `MonadLift (OracleQuery superSpec) (OracleComp superSpec)` is
  tried first by `monadLiftTrans` and succeeds via the `SubSpec` chain on
  `OracleQuery`, never reaching this instance. Single-query lifts therefore
  go through the standard "lift query then embed" path with no spurious
  walk through `liftComp`.

* For `MonadLiftT (OracleComp spec) (OracleComp superSpec)` with
  `spec ≠ superSpec`, the high-priority built-in fails (no
  `MonadLiftT (OracleComp _) (OracleQuery _)`), Lean backtracks to this
  low-priority instance, and the recursive subgoal collapses via
  `MonadLiftT.refl`. The result is a single `liftComp mx superSpec`. -/
instance (priority := low) [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (OracleComp spec) (OracleComp superSpec) where
  monadLift mx := liftComp mx superSpec

/-- We choose to actively rewrite `liftComp` as `liftM` to enable `LawfulMonadLift` lemmas. -/
@[simp, aesop safe norm]
lemma liftComp_eq_liftM [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : OracleComp spec α) : liftComp mx superSpec = (liftM mx : OracleComp superSpec α) := rfl

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    LawfulMonadLift (OracleComp spec) (OracleComp superSpec) where
  monadLift_pure x := liftComp_pure superSpec x
  monadLift_bind mx my := liftComp_bind superSpec mx my

/-- Self-lift on `OracleComp` is definitionally `id`, supplied by Lean's
built-in `MonadLiftT.refl` thanks to the low-priority `MonadLift` instance
above (which causes the parametric path to lose typeclass resolution to
`MonadLiftT.refl` when `spec = superSpec`). -/
@[simp]
lemma monadLift_eq_self {α} (mx : OracleComp spec α) :
    (monadLift mx : OracleComp spec α) = mx := rfl

/-! Regression smoke-tests for the instance-priority invariants above. The
`rfl` proofs are the load-bearing signal: if priority drifts so that the
parametric `MonadLift` beats `MonadLiftT.refl`, the self-lift stops being
definitionally `id` and the `rfl` below breaks. Similarly, the
`MonadLiftT` synthesis check guards against future refactors that would
remove the transitive lift chain. -/

example (mx : OracleComp spec Nat) :
    (monadLift mx : OracleComp spec Nat) = mx := rfl

example : MonadLiftT (OracleComp spec) (OracleComp spec) :=
  inferInstance

example [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLiftT (OracleComp spec) (OracleComp superSpec) :=
  inferInstance

-- NOTE: With constant universal levels it is fairly easy to abstract the below in a class
-- Getting a similar level of generality as the manual instances below would be useful,
--    might require some more general framework about monad transformers.

section OptionT

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (OptionT (OracleComp spec)) (OptionT (OracleComp superSpec)) where
  monadLift mx := OptionT.mk (simulateQ (fun t => liftM (query t)) (OptionT.run mx))

@[simp]
lemma liftM_OptionT_eq [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : OptionT (OracleComp spec) α) : (liftM mx : OptionT (OracleComp superSpec) α) =
      let impl : QueryImpl spec (OracleComp superSpec) := fun t => liftM (query t)
      simulateQ impl mx := rfl

@[simp]
lemma liftM_failure [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    (liftM (failure : OptionT (OracleComp spec) α) : OptionT (OracleComp superSpec) α) =
      failure := by
  rw [OracleComp.failure_def, liftM_OptionT_eq, OptionT.fail]
  simp only [OptionT.mk, simulateQ_pure]
  rfl

instance [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    LawfulMonadLift (OptionT (OracleComp spec)) (OptionT (OracleComp superSpec)) where
  monadLift_pure _ := by
    simp [MonadLift.monadLift]
    rfl
  monadLift_bind mx my := by
    apply OptionT.ext
    simp only [MonadLift.monadLift, OptionT.run_bind, Option.elimM, simulateQ_bind, OptionT.mk_bind,
      OptionT.run_monadLift, monadLift_self, OptionT.run_mk, bind_map_left, Option.elim_some]
    refine bind_congr ?_
    intro x
    cases x <;> simp

/-- Coherence: lifting an `OracleComp` to a superspec and then into `OptionT` via the standard
  `MonadLift` equals lifting directly through the transitive `MonadLiftT` chain (which goes
  through the `simulateQ`-based `OptionT` MonadLift instance). -/
@[simp]
lemma monadLift_liftM_OptionT [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : OracleComp spec α) :
    (monadLift (liftM mx : OracleComp superSpec α) : OptionT (OracleComp superSpec) α) =
    (liftM mx : OptionT (OracleComp superSpec) α) := by
  apply OptionT.ext
  simp only [OptionT.run_monadLift, monadLift_eq_self]
  conv_rhs => dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  simp only [OptionT.run_mk, OptionT.lift]
  erw [simulateQ_bind]
  simp only [simulateQ_pure, ← map_eq_pure_bind]
  congr 1

end OptionT

section StateT

instance {σ : Type _} [MonadLift (OracleQuery spec) (OracleQuery superSpec)] :
    MonadLift (StateT σ (OracleComp spec)) (StateT σ (OracleComp superSpec)) where
  monadLift mx := StateT.mk fun s => liftComp (StateT.run mx s) superSpec

@[simp]
lemma liftM_StateT_eq {σ : Type _} [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (mx : StateT σ (OracleComp spec) α) : (liftM mx : StateT σ (OracleComp superSpec) α) =
      StateT.mk fun s => liftM (StateT.run mx s) := rfl

end StateT

end OracleComp
