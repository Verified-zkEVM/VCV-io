/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions
import VCVio.OracleComp.Coercions.Add

/-!
# Append/Add Operation for Simulation Oracles
-/

universe u v w

namespace QueryImpl

variable {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {m n r : Type u → Type*}

/-- Simplest version of adding queries when all implementations are in the same monad.
The actual add notation for `QueryImpl` uses `QueryImpl.addLift` which adds monad lifting
to this definition for greater flexibility. -/
protected def add (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m) :
    QueryImpl (spec₁ + spec₂) m | .inl t => impl₁ t | .inr t => impl₂ t

/-- Add two `QueryImpl` to get an implementation on the sum of the two `OracleSpec`. -/
instance : HAdd (QueryImpl spec₁ m) (QueryImpl spec₂ m) (QueryImpl (spec₁ + spec₂) m) where
  hAdd := QueryImpl.add

lemma add_apply (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : OracleSpec.Domain (spec₁ + spec₂)) : (impl₁ + impl₂) t =
      match t with | .inl t => impl₁ t | .inr t => impl₂ t := rfl

@[simp] lemma add_apply_inl (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : spec₁.Domain) : (impl₁ + impl₂) (.inl t) = impl₁ t := rfl

@[simp] lemma add_apply_inr (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : spec₂.Domain) : (impl₁ + impl₂) (.inr t) = impl₂ t := rfl

/-- Version of `QueryImpl.add` that also lifts the two implementations to a shared lift monad. -/
def addLift {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m n r : Type u → Type*} [MonadLiftT m r] [MonadLiftT n r]
    (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ n) : QueryImpl (spec₁ + spec₂) r :=
  (impl₁.liftTarget r) + (impl₂.liftTarget r)

@[simp] lemma addLift_def {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m n r : Type u → Type*} [MonadLiftT m r] [MonadLiftT n r]
    (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ n) :
    (impl₁.addLift impl₂ : QueryImpl (spec₁ + spec₂) r) =
      (impl₁.liftTarget r) + (impl₂.liftTarget r) := rfl

section simulateQ_add_liftComp

variable {ι₁' : Type} {ι₂' : Type}
  {spec₁' : OracleSpec ι₁'} {spec₂' : OracleSpec ι₂'}
  {α : Type} {m' : Type → Type v} [Monad m'] [LawfulMonad m']
  (impl₁' : QueryImpl spec₁' m') (impl₂' : QueryImpl spec₂' m')

private lemma simulateQ_add_liftM_query_left (t : spec₁'.Domain) :
    simulateQ (impl₁' + impl₂')
      (liftM (spec₁'.query t) : OracleComp (spec₁' + spec₂') _) =
    impl₁' t := by
  change simulateQ (impl₁' + impl₂')
    (liftM (liftM (spec₁'.query t) : OracleQuery (spec₁' + spec₂') _)) = _
  simp [simulateQ_query]

private lemma simulateQ_add_liftM_query_right (t : spec₂'.Domain) :
    simulateQ (impl₁' + impl₂')
      (liftM (spec₂'.query t) : OracleComp (spec₁' + spec₂') _) =
    impl₂' t := by
  change simulateQ (impl₁' + impl₂')
    (liftM (liftM (spec₂'.query t) : OracleQuery (spec₁' + spec₂') _)) = _
  simp [simulateQ_query]

@[simp]
lemma simulateQ_add_liftComp_left (oa : OracleComp spec₁' α) :
    simulateQ (impl₁' + impl₂') (OracleComp.liftComp oa (spec₁' + spec₂')) =
      simulateQ impl₁' oa := by
  rw [OracleComp.liftComp_def, ← simulateQ_compose]
  congr 1
  funext t
  exact simulateQ_add_liftM_query_left impl₁' impl₂' t

@[simp]
lemma simulateQ_add_liftComp_right (ob : OracleComp spec₂' α) :
    simulateQ (impl₁' + impl₂') (OracleComp.liftComp ob (spec₁' + spec₂')) =
      simulateQ impl₂' ob := by
  rw [OracleComp.liftComp_def, ← simulateQ_compose]
  congr 1
  funext t
  exact simulateQ_add_liftM_query_right impl₁' impl₂' t

/-- `liftM`-normal-form companion of `simulateQ_add_liftComp_left`. Because `liftComp_eq_liftM`
normalizes `liftComp → liftM` under `simp`, the `liftComp`-keyed lemma never fires inside `simp`;
this `liftM`-keyed form is what `simp` actually needs.

Deliberately **not** `@[simp]`: as a global rule it shifts the normal form of `simulateQ` over an
added handler applied to a lifted-in computation, which pre-empts and breaks existing proofs that
manage that reduction themselves. Pass it explicitly, e.g.
`simp [myHandler, simulateQ_add_liftM_left, simulateQ_toQueryImpl]`. -/
lemma simulateQ_add_liftM_left (oa : OracleComp spec₁' α) :
    simulateQ (impl₁' + impl₂') (liftM oa : OracleComp (spec₁' + spec₂') α) =
      simulateQ impl₁' oa := by
  rw [← OracleComp.liftComp_eq_liftM]
  exact simulateQ_add_liftComp_left impl₁' impl₂' oa

/-- `liftM`-normal-form companion of `simulateQ_add_liftComp_right`; opt-in, see
`simulateQ_add_liftM_left`. -/
lemma simulateQ_add_liftM_right (ob : OracleComp spec₂' α) :
    simulateQ (impl₁' + impl₂') (liftM ob : OracleComp (spec₁' + spec₂') α) =
      simulateQ impl₂' ob := by
  rw [← OracleComp.liftComp_eq_liftM]
  exact simulateQ_add_liftComp_right impl₁' impl₂' ob

lemma simulateQ_liftComp_left_eq_of_apply
    (impl : QueryImpl (spec₁' + spec₂') m') (impl₁ : QueryImpl spec₁' m')
    (h : ∀ t, impl (Sum.inl t) = impl₁ t) (oa : OracleComp spec₁' α) :
    simulateQ impl (OracleComp.liftComp oa (spec₁' + spec₂')) =
      simulateQ impl₁ oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      rw [OracleComp.liftComp_bind, simulateQ_bind, simulateQ_bind]
      have hq :
          simulateQ impl
            (OracleComp.liftComp
              (liftM (spec₁'.query t) : OracleComp spec₁' (spec₁'.Range t))
              (spec₁' + spec₂')) = impl₁ t := by
        rw [OracleComp.liftComp_query]
        change simulateQ impl
          (liftM ((spec₁' + spec₂').query (Sum.inl t))) = impl₁ t
        rw [simulateQ_spec_query]
        exact h t
      rw [hq, simulateQ_spec_query]
      exact bind_congr fun u => ih u

lemma simulateQ_liftComp_right_eq_of_apply
    (impl : QueryImpl (spec₁' + spec₂') m') (impl₂ : QueryImpl spec₂' m')
    (h : ∀ t, impl (Sum.inr t) = impl₂ t) (oa : OracleComp spec₂' α) :
    simulateQ impl (OracleComp.liftComp oa (spec₁' + spec₂')) =
      simulateQ impl₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      rw [OracleComp.liftComp_bind, simulateQ_bind, simulateQ_bind]
      have hq :
          simulateQ impl
            (OracleComp.liftComp
              (liftM (spec₂'.query t) : OracleComp spec₂' (spec₂'.Range t))
              (spec₁' + spec₂')) = impl₂ t := by
        rw [OracleComp.liftComp_query]
        change simulateQ impl
          (liftM ((spec₁' + spec₂').query (Sum.inr t))) = impl₂ t
        rw [simulateQ_spec_query]
        exact h t
      rw [hq, simulateQ_spec_query]
      exact bind_congr fun u => ih u

end simulateQ_add_liftComp

/-- Simulating the trivial `HasQuery.toQueryImpl` handler back into `OracleComp spec` is the
identity (the composite of `HasQuery.toQueryImpl_eq_id'` and `simulateQ_id'`).

Like `toQueryImpl_eq_id'`, this is deliberately **not** `@[simp]`: globally it lets `simulateQ`
of a `unifFwdImpl`-style `toQueryImpl.liftTarget` handler fully reduce, which can re-enable a
backward induction-hypothesis rewrite and diverge. Pass it explicitly to `simp` (alongside the
opaque handler definition) to discharge a lifted-in computation, e.g.
`simp [myHandler, simulateQ_toQueryImpl]`; the `simulateQ_add_liftM_left`/`_right` and
`simulateQ_liftTarget` rungs are `@[simp]` and fire on their own. -/
lemma simulateQ_toQueryImpl {ι : Type*} {spec : OracleSpec ι} {α : Type u}
    (mx : OracleComp spec α) :
    simulateQ (HasQuery.toQueryImpl : QueryImpl spec (OracleComp spec)) mx = mx := by
  rw [HasQuery.toQueryImpl_eq_id', simulateQ_id']

section simulateQ_liftM

variable {ι₁' : Type} {ι₂' : Type}
  {spec₁' : OracleSpec ι₁'} {spec₂' : OracleSpec ι₂'}
  {α : Type} {m' : Type → Type v} [Monad m'] [LawfulMonad m']
  [MonadLiftT (OracleComp spec₁') (OracleComp spec₂')]
  [LawfulMonadLiftT (OracleComp spec₁') (OracleComp spec₂')]

lemma simulateQ_liftM_eq_of_query
    (impl : QueryImpl spec₂' m') (impl₁ : QueryImpl spec₁' m')
    (h : ∀ t, simulateQ impl
      (liftM (liftM (spec₁'.query t) :
        OracleComp spec₁' (spec₁'.Range t)) :
        OracleComp spec₂' (spec₁'.Range t)) = impl₁ t)
    (oa : OracleComp spec₁' α) :
    simulateQ impl (liftM oa : OracleComp spec₂' α) =
      simulateQ impl₁ oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t k ih =>
      rw [liftM_bind, simulateQ_bind, simulateQ_bind, h t, simulateQ_spec_query]
      exact bind_congr fun u => ih u

end simulateQ_liftM

section simulateQ_add_add_liftM

/-! ### Query routing through a right-nested sum implementation

Routing lemmas for the `spec + (spec₁ + spec₂)` layout used by stateless protocol
simulation oracles (e.g. a base spec plus a pair of message/statement oracle families,
the `simOracle2` layout): a single query lifted from one component — either at the
*query* level (`OracleQuery`) or pre-embedded in its own *computation* monad
(`OracleComp`, the shape produced by reusable query helpers) — resolves under
`simulateQ` to the implementation at the routed index.

Each left-hand side spells the canonical `MonadLiftT` chain that typeclass resolution
synthesizes for that lift (through the intermediate `spec + spec₂` etc.), which is what
lets these fire by `simp` on goals produced by elaborated protocol definitions. All six
are definitional modulo `simulateQ_spec_query`: the `show … from rfl` bridges re-express
the chained lift as the canonical embedded query at the routed index. -/

variable {ι' ι₁' ι₂' : Type} {spec : OracleSpec ι'} {spec₁ : OracleSpec ι₁'}
  {spec₂ : OracleSpec ι₂'} {m' : Type → Type v} [Monad m'] [LawfulMonad m']
  (implA : QueryImpl spec m') (implB : QueryImpl (spec₁ + spec₂) m')

@[simp]
lemma simulateQ_add_add_liftM_query_base (t : spec.Domain) :
    simulateQ (implA + implB)
      (liftM (spec.query t) : OracleComp (spec + (spec₁ + spec₂)) (spec.Range t)) =
      implA t :=
  (simulateQ_spec_query (implA + implB) (Sum.inl t)).trans rfl

@[simp]
lemma simulateQ_add_add_liftM_query_left (t : spec₁.Domain) :
    simulateQ (implA + implB)
      (liftM (spec₁.query t) : OracleComp (spec + (spec₁ + spec₂)) (spec₁.Range t)) =
      implB (Sum.inl t) :=
  (simulateQ_spec_query (implA + implB) (Sum.inr (Sum.inl t))).trans rfl

@[simp]
lemma simulateQ_add_add_liftM_query_right (t : spec₂.Domain) :
    simulateQ (implA + implB)
      (liftM (spec₂.query t) : OracleComp (spec + (spec₁ + spec₂)) (spec₂.Range t)) =
      implB (Sum.inr t) :=
  (simulateQ_spec_query (implA + implB) (Sum.inr (Sum.inr t))).trans rfl

@[simp]
lemma simulateQ_add_add_liftM_comp_base (t : spec.Domain) :
    simulateQ (implA + implB)
      (liftM (liftM (spec.query t) : OracleComp spec (spec.Range t)) :
        OracleComp (spec + (spec₁ + spec₂)) (spec.Range t)) =
      implA t :=
  (simulateQ_spec_query (implA + implB) (Sum.inl t)).trans rfl

@[simp]
lemma simulateQ_add_add_liftM_comp_left (t : spec₁.Domain) :
    simulateQ (implA + implB)
      (liftM (liftM (spec₁.query t) : OracleComp spec₁ (spec₁.Range t)) :
        OracleComp (spec + (spec₁ + spec₂)) (spec₁.Range t)) =
      implB (Sum.inl t) :=
  (simulateQ_spec_query (implA + implB) (Sum.inr (Sum.inl t))).trans rfl

@[simp]
lemma simulateQ_add_add_liftM_comp_right (t : spec₂.Domain) :
    simulateQ (implA + implB)
      (liftM (liftM (spec₂.query t) : OracleComp spec₂ (spec₂.Range t)) :
        OracleComp (spec + (spec₁ + spec₂)) (spec₂.Range t)) =
      implB (Sum.inr t) :=
  (simulateQ_spec_query (implA + implB) (Sum.inr (Sum.inr t))).trans rfl

end simulateQ_add_add_liftM

section simulateQ_liftM_query_tests

/-! Unit tests: a query lifted from a component of a sum spec routes through a sum
implementation by `simp` alone, via the `simulateQ_add_add_liftM_*` routing lemmas.
The shape `spec + (spec₁ + spec₂)` with an `addLift`ed pair is the `simOracle2`
layout used by oracle-reduction verifiers downstream. -/

variable {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {m : Type → Type} [Monad m] [LawfulMonad m]

example (impl : QueryImpl spec m) (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : spec₁.Domain) :
    simulateQ (impl + (impl₁ + impl₂))
      (liftM (spec₁.query t) : OracleComp (spec + (spec₁ + spec₂)) (spec₁.Range t)) =
      impl₁ t := by
  simp

example (impl : QueryImpl spec m) (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : spec₂.Domain) :
    simulateQ (impl + (impl₁ + impl₂))
      (liftM (spec₂.query t) : OracleComp (spec + (spec₁ + spec₂)) (spec₂.Range t)) =
      impl₂ t := by
  simp

example {m₀ n : Type → Type} [Monad m₀] [Monad n] [MonadLiftT m₀ m] [MonadLiftT n m]
    (impl : QueryImpl spec m₀) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    (t : spec₂.Domain) :
    simulateQ (impl.addLift (impl₁.add impl₂) : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (spec₂.query t) : OracleComp (spec + (spec₁ + spec₂)) (spec₂.Range t)) =
      liftM (impl₂ t) := by
  simp [QueryImpl.add]

-- computation-level lifts (query helpers defined in their own `OracleComp` monad)
example (impl : QueryImpl spec m) (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : spec₂.Domain) :
    simulateQ (impl + (impl₁ + impl₂))
      (liftM (liftM (spec₂.query t) : OracleComp spec₂ (spec₂.Range t)) :
        OracleComp (spec + (spec₁ + spec₂)) (spec₂.Range t)) =
      impl₂ t := by
  simp

example {m₀ n : Type → Type} [Monad m₀] [Monad n] [MonadLiftT m₀ m] [MonadLiftT n m]
    (impl : QueryImpl spec m₀) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    (t : spec₁.Domain) :
    simulateQ (impl.addLift (impl₁.add impl₂) : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM (spec₁.query t) : OracleComp spec₁ (spec₁.Range t)) :
        OracleComp (spec + (spec₁ + spec₂)) (spec₁.Range t)) =
      liftM (impl₁ t) := by
  simp [QueryImpl.add]

end simulateQ_liftM_query_tests

end QueryImpl

section simulateQ_addLift_add_liftM

open OracleSpec

variable {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {m : Type → Type} [Monad m] [LawfulMonad m]
  {m₀ : Type → Type} [MonadLiftT m₀ m]
  {n : Type → Type} [Monad n] [LawfulMonad n] [MonadLiftT n m] [LawfulMonadLiftT n m]

/-- Resolve a `simulateQ` over a three-way `addLift impl (impl₁ + impl₂)` applied to a
computation `x : OracleComp spec₁ α` that has been double-`liftM`'d — first into the inner
sum `spec₁ + spec₂`, then into the outer sum `spec + (spec₁ + spec₂)`. The query routes to
the *left* inner implementation `impl₁`, leaving `liftM (simulateQ impl₁ x)`.

This is the computation-level sibling of `QueryImpl.simulateQ_add_add_liftM_comp_left`: it
peels the outer `addLift` (`simulateQ_add_liftComp_right`), commutes the inner `simulateQ`
past the target lift (`simulateQ_liftTarget`), then peels the inner sum
(`simulateQ_add_liftComp_left`). Stated for the inner pair living in a possibly-different
monad `n` lifted into the target `m`. -/
lemma simulateQ_addLift_add_liftM_left
    (impl : QueryImpl spec m₀) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    {α : Type} (x : OracleComp spec₁ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)
        : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM x : OracleComp (spec₁ + spec₂) α) :
        OracleComp (spec + (spec₁ + spec₂)) α)
      = (liftM (simulateQ impl₁ x) : m α) := by
  rw [show QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ from rfl,
    ← OracleComp.liftComp_eq_liftM, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_liftTarget, QueryImpl.simulateQ_add_liftComp_left]

/-- Resolve a `simulateQ` over a three-way `addLift impl (impl₁ + impl₂)` applied to a
computation `x : OracleComp spec₂ α` that has been double-`liftM`'d — first into the inner
sum `spec₁ + spec₂`, then into the outer sum `spec + (spec₁ + spec₂)`. The query routes to
the *right* inner implementation `impl₂`, leaving `liftM (simulateQ impl₂ x)`.

The `right` companion of `simulateQ_addLift_add_liftM_left`. -/
lemma simulateQ_addLift_add_liftM_right
    (impl : QueryImpl spec m₀) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    {α : Type} (x : OracleComp spec₂ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)
        : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM x : OracleComp (spec₁ + spec₂) α) :
        OracleComp (spec + (spec₁ + spec₂)) α)
      = (liftM (simulateQ impl₂ x) : m α) := by
  rw [show QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ from rfl,
    ← OracleComp.liftComp_eq_liftM, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_liftTarget, QueryImpl.simulateQ_add_liftComp_right]

end simulateQ_addLift_add_liftM

section simulateQ_optionT_liftM_run

open OracleSpec

/-- `OptionT` companion to `QueryImpl.simulateQ_liftM_eq_of_query`: simulating an
`OracleComp`-computation `oa` lifted into `OptionT (OracleComp spec₂')` (the shape produced by
an `OptionT`-monadic verifier's `let _ ← liftM (queryHelper)` binds) agrees, at the run
(`Option`) level, with `some`-mapping the simulation of `oa` through a per-query-bridged
handler `impl₁`.

The key step is that the `OptionT.run` of a lifted `OracleComp` is `some <$> (the OracleComp
lift)` *definitionally* (`hrun` below is `rfl`), which collapses the `OptionT` lift chain to a
plain `OracleComp` lift; the chain-agnostic `QueryImpl.simulateQ_liftM_eq_of_query` then
resolves it. -/
lemma simulateQ_optionT_liftM_run_eq_of_query
    {ι₁' ι₂' : Type} {spec₁' : OracleSpec ι₁'} {spec₂' : OracleSpec ι₂'}
    {α : Type} {m' : Type → Type} [Monad m'] [LawfulMonad m']
    [MonadLiftT (OracleComp spec₁') (OracleComp spec₂')]
    [LawfulMonadLiftT (OracleComp spec₁') (OracleComp spec₂')]
    (impl : QueryImpl spec₂' m') (impl₁ : QueryImpl spec₁' m')
    (h : ∀ t, simulateQ impl
      (liftM (liftM (spec₁'.query t) : OracleComp spec₁' (spec₁'.Range t)) :
        OracleComp spec₂' (spec₁'.Range t)) = impl₁ t)
    (oa : OracleComp spec₁' α) :
    simulateQ impl ((liftM oa : OptionT (OracleComp spec₂') α) :
        OracleComp spec₂' (Option α))
      = (some <$> simulateQ impl₁ oa : m' (Option α)) := by
  have hrun : ((liftM oa : OptionT (OracleComp spec₂') α) : OracleComp spec₂' (Option α))
      = some <$> (liftM oa : OracleComp spec₂' α) := rfl
  rw [hrun, simulateQ_map, QueryImpl.simulateQ_liftM_eq_of_query impl impl₁ h oa]

end simulateQ_optionT_liftM_run
