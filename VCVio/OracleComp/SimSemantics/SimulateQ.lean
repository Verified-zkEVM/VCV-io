/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
import VCVio.Prelude
import ToMathlib.Control.OptionT

/-!
# Simulation Semantics for Oracles in a Computation

-/

open OracleComp Prod

universe u v w

variable {α β γ : Type u}

section simulateQ

/-- Given an implementation of `spec` in the monad `r`, convert an `OracleComp spec α` to a
implementation in `r α` by substituting `impl t` for `query t` throughout. -/
def simulateQ {ι} {spec : OracleSpec ι} {r : Type u → Type _} [Monad r]
    (impl : QueryImpl spec r) {α : Type u} (mx : OracleComp spec α) : r α :=
  PFunctor.FreeM.mapM impl mx

variable {ι} {spec : OracleSpec ι} {r m n : Type u → Type*}
    [Monad r] (impl : QueryImpl spec r)

@[simp, grind =, game_rule]
lemma simulateQ_pure (x : α) :
    simulateQ impl (pure x : OracleComp spec α) = pure x := rfl

@[simp, grind =, game_rule]
lemma simulateQ_bind [LawfulMonad r] (mx : OracleComp spec α) (my : α → OracleComp spec β) :
    simulateQ impl (mx >>= my) = simulateQ impl mx >>= fun x => simulateQ impl (my x) := by
  unfold simulateQ; exact PFunctor.FreeM.mapM_bind' impl mx my

/-- Version of `simulateQ` that bundles into a monad hom. -/
@[reducible]
def simulateQ' [LawfulMonad r] (impl : QueryImpl spec r) : OracleComp spec →ᵐ r where
  toFun {_α} mx := simulateQ impl mx
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

@[simp, grind =, game_rule]
lemma simulateQ_query [LawfulMonad r] (q : OracleQuery spec α) :
    simulateQ impl (liftM q) = q.cont <$> (impl q.input) := by
  simp [simulateQ, OracleComp.liftM_def]

/-- Specialized form of `simulateQ_query` for the canonical `spec.query t`
constructor: `simulateQ impl (liftM (spec.query t)) = impl t`.

The general `simulateQ_query` rewrite leaves an `id <$>` artifact when applied
to `spec.query t` (because `(spec.query t).cont = id`). That artifact is
harmless when `spec.Range t` is concrete (it disappears under definitional
reduction), but in *parametric* sum-spec contexts (`(E₁ + E₂).Range (Sum.inl t)`
vs `E₁.Range t`, both abstract atoms) the type annotations diverge and
`id_map` no longer fires under `simp only`. This lemma sidesteps the artifact
entirely and is the canonical entry point for simplifying `simulateQ` over an
explicit `spec.query t`. -/
@[simp, grind =]
lemma simulateQ_spec_query [LawfulMonad r] (t : spec.Domain) :
    simulateQ impl (liftM (spec.query t)) = impl t := by
  simp [simulateQ_query]

/-- Companion to `simulateQ_query` for a query entering the computation through a
*query-level lift chain*: simulating a query lifted from a sub-spec `spec'` applies the
implementation to the lifted query.

The `(liftM q : OracleComp spec α)` on the left elaborates through the canonical
`MonadLift (OracleQuery spec) (OracleComp spec)` composed (via `instMonadLiftTOfMonadLift`)
with the given `MonadLiftT (OracleQuery spec') (OracleQuery spec)` — e.g. a `SubSpec`
embedding chain such as `spec₂ ⊂ₒ spec₁ + spec₂ ⊂ₒ spec + (spec₁ + spec₂)`. This is the
term shape produced by lifting a query helper (`liftM (liftM (spec'.query t))`) into a
larger interface, as `OracleSpec.SubSpec`-based protocol verifiers do. `simulateQ_query`
itself cannot match it: its query's spec is forced to equal the simulated spec, while here
the query lives in `spec'`.

The right-hand side is deliberately `mapQuery` of the *single* term `liftM q` rather than
the unbundled `(liftM q).cont <$> impl (liftM q).input`: the type of `.cont` depends on
`.input`, so the unbundled form blocks all further `simp` rewriting of the lifted query
(the dependent-motive trap). With `mapQuery`, the lifted query can then be normalized in
place (everything in the `SubSpec` lift chain is definitional) and landed on the
implementation with `mapQuery_mk`.

Not `@[simp]`: for the common sum-spec layouts the specialized routing lemmas
(`QueryImpl.simulateQ_add_add_liftM_query_left` and friends in `SimSemantics/Append.lean`)
resolve the routed query in one step; this general form would preempt them and strand the
goal at an un-normalized `mapQuery (liftM q)`. Use it manually for bespoke lift chains. -/
lemma simulateQ_liftM_query [LawfulMonad r] {ι' : Type*} {spec' : OracleSpec ι'}
    [MonadLiftT (OracleQuery spec') (OracleQuery spec)] (q : OracleQuery spec' α) :
    simulateQ impl (liftM q : OracleComp spec α) =
      impl.mapQuery (liftM q : OracleQuery spec α) :=
  simulateQ_query impl (liftM q)

/-- Evaluate an oracle computation by answering each query with a total answer function.

This is the `Id`-valued specialization of `simulateQ`: each query in `mx` is replaced by the
corresponding value returned by `f`. -/
def evalWithAnswerFn {ι} {spec : OracleSpec ι} (f : QueryImpl spec Id)
    {α : Type u} (mx : OracleComp spec α) : α :=
  simulateQ f mx

@[simp]
theorem evalWithAnswerFn_pure {ι} {spec : OracleSpec ι} (f : QueryImpl spec Id) (a : α) :
    evalWithAnswerFn f (pure a : OracleComp spec α) = a := rfl

@[simp]
theorem evalWithAnswerFn_bind {ι} {spec : OracleSpec ι} (f : QueryImpl spec Id)
    (mx : OracleComp spec α) (my : α → OracleComp spec β) :
    evalWithAnswerFn f (mx >>= my) = evalWithAnswerFn f (my (evalWithAnswerFn f mx)) := by
  change simulateQ f (mx >>= my) = simulateQ f (my (simulateQ f mx))
  rw [simulateQ_bind]; rfl

@[simp]
theorem evalWithAnswerFn_query {ι} {spec : OracleSpec ι} (f : QueryImpl spec Id)
    (t : spec.Domain) :
    evalWithAnswerFn f (query t : OracleComp spec _) = f t := by
  simp [evalWithAnswerFn]

@[simp]
lemma simulateQ_query_bind [LawfulMonad r] (q : OracleQuery spec α)
    (ou : α → OracleComp spec β) : simulateQ impl (liftM q >>= ou) =
      liftM (impl q.input) >>= fun u => simulateQ impl (ou (q.cont u)) := by aesop

@[simp, grind =]
lemma simulateQ_map [LawfulMonad r] (mx : OracleComp spec α) (f : α → β) :
    simulateQ impl (f <$> mx) = f <$> simulateQ impl mx := by
  simp [monad_norm]

@[simp]
theorem evalWithAnswerFn_map {ι} {spec : OracleSpec ι} (f : QueryImpl spec Id)
    (g : α → β) (mx : OracleComp spec α) :
    evalWithAnswerFn f (g <$> mx) = g (evalWithAnswerFn f mx) := by
  change simulateQ f (g <$> mx) = g (simulateQ f mx)
  rw [simulateQ_map]; rfl

/-- Two `simulateQ`'d binds whose bodies agree up to a pure post-map `f` agree up to mapping
`f` over the whole simulation. Companion to `simulateQ_bind` for establishing map-relations
between two simulations without unfolding the shared leading computation `oa`. -/
lemma simulateQ_bind_map_eq_of_body [LawfulMonad r]
    (oa : OracleComp spec α) (body₁ : α → OracleComp spec β)
    (body₂ : α → OracleComp spec γ) (f : γ → β)
    (hBody : ∀ a, simulateQ impl (body₁ a) = f <$> simulateQ impl (body₂ a)) :
    simulateQ impl (oa >>= body₁) = f <$> simulateQ impl (oa >>= body₂) := by
  rw [← simulateQ_map]
  simp only [map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure, bind_assoc,
    Function.comp]
  congr 1
  funext a
  exact (hBody a).trans (map_eq_bind_pure_comp _ _ _)

@[simp]
lemma simulateQ_seq [LawfulMonad r] (og : OracleComp spec (α → β)) (mx : OracleComp spec α) :
    simulateQ impl (og <*> mx) = simulateQ impl og <*> simulateQ impl mx := by
  simp [monad_norm]

@[simp]
lemma simulateQ_seqLeft [LawfulMonad r] (mx : OracleComp spec α) (my : OracleComp spec β) :
    simulateQ impl (mx <* my) = simulateQ impl mx <* simulateQ impl my := by
  simp [seqLeft_eq_bind]

@[simp]
lemma simulateQ_seqRight [LawfulMonad r] (mx : OracleComp spec α) (my : OracleComp spec β) :
    simulateQ impl (mx *> my) = simulateQ impl mx *> simulateQ impl my := by
  simp [seqRight_eq_bind]

@[simp]
lemma simulateQ_ite (p : Prop) [Decidable p] (mx mx' : OracleComp spec α) :
    simulateQ impl (ite p mx mx') = ite p (simulateQ impl mx) (simulateQ impl mx') := by
  split_ifs <;> rfl

@[simp]
lemma simulateQ_dite (p : Prop) [Decidable p]
    (mx : p → OracleComp spec α) (mx' : ¬p → OracleComp spec α) :
    simulateQ impl (dite p mx mx') =
      dite p (fun h => simulateQ impl (mx h)) (fun h => simulateQ impl (mx' h)) := by
  split <;> rfl

@[simp]
lemma simulateQ_liftTarget {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    (impl : QueryImpl spec m) (comp : OracleComp spec α) :
    simulateQ (impl.liftTarget n) comp = liftM (simulateQ impl comp) := by
  induction comp using OracleComp.inductionOn with
  | pure x => simp [liftM_pure]
  | query_bind t k ih => simp [ih, liftM_bind]

end simulateQ

variable {ι} {spec : OracleSpec ι} {n : Type u → Type v}
  [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)

lemma simulateQ_def (impl : QueryImpl spec n) (mx : OracleComp spec α) :
    simulateQ impl mx = PFunctor.FreeM.mapMHom impl mx := rfl

/-- `QueryImpl.id'` is an identity for `simulateQ` with implementation in `OracleComp spec`. -/
@[simp, grind =]
lemma simulateQ_id' (mx : OracleComp spec α) :
    simulateQ (QueryImpl.id' spec) mx = mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h]

/-- Lifting queries to their original implementation has no effect on a computation. -/
lemma simulateQ_ofLift_eq_self {α} (mx : OracleComp spec α) :
    simulateQ (QueryImpl.ofLift spec (OracleComp spec)) mx = mx := by simp

section tests

variable {ι₁ ι₂ ι₃ ι₄}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄}

example (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₂))) :
    OptionT (OracleComp spec₂) α :=
  simulateQ impl₂ <|
    simulateQ impl₁ mx

example (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₃)))
    (impl₃ : QueryImpl spec₃ (OptionT (OracleComp spec₄))) :
    OptionT (OptionT (OracleComp spec₄)) α :=
  simulateQ impl₃ <| simulateQ impl₂ <| simulateQ impl₁ mx

example (mx : OptionT (OracleComp spec₁) α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OracleComp spec₃)) :
    OptionT (OracleComp spec₃) α :=
  simulateQ impl₂ <| simulateQ impl₁ <| mx

end tests

/-! ## List / ForM distributivity -/

section List

/-- `simulateQ` distributes over `List.mapM`: simulating a mapped list is the same as
mapping the simulated function over the list. -/
@[simp]
lemma simulateQ_list_mapM (f : α → OracleComp spec β) (xs : List α) :
    simulateQ impl (xs.mapM f) = xs.mapM (fun a => simulateQ impl (f a)) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.mapM_cons, simulateQ_bind, ih]

/-- `simulateQ` distributes over `List.forM`. -/
@[simp]
lemma simulateQ_list_forM (f : α → OracleComp spec PUnit) (xs : List α) :
    simulateQ impl (xs.forM f) = xs.forM (fun a => simulateQ impl (f a)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : (x :: xs).forM f = f x >>= fun _ => xs.forM f := rfl
    rw [h, simulateQ_bind]; congr 1; funext; exact ih

/-- `simulateQ` distributes over `forIn` on a list: a monad morphism commutes with `forIn`.

This is the `forIn` (early-exit / accumulating loop) sibling of `simulateQ_list_mapM` and
`simulateQ_list_forM`. It lets a `simulateQ` pushed in front of a verifier-style loop
`forIn (List.finRange t) init (fun j acc => …)` be moved inside the loop body, after which the
individual simulated query steps can be discharged. -/
@[simp]
lemma simulateQ_list_forIn {β : Type u} (xs : List α) (init : β)
    (f : α → β → OracleComp spec (ForInStep β)) :
    simulateQ impl (forIn xs init f) = forIn xs init (fun a b => simulateQ impl (f a b)) := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons, simulateQ_bind]
    congr 1
    funext step
    cases step with
    | done b => simp
    | yield b => exact ih b

end List

/-! ## Composition of simulations via a per-query bridge -/

section Compose

universe u' v'

variable {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

/-- Two-stage simulation: if a "reduction" `red : QueryImpl spec₁ (StateT σ (OracleComp spec₂))`
followed by an inner `impl : QueryImpl spec₂ n` agrees per-query with a "combined" handler
`game : QueryImpl spec₁ (StateT σ n)`, then the agreement extends to every outer computation by
structural induction. This packages the boilerplate induction reused across PRF-style reductions. -/
theorem simulateQ_StateT_compose
    {σ : Type u'} {n : Type u' → Type v'} [Monad n] [LawfulMonad n]
    (red : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (impl : QueryImpl spec₂ n)
    (game : QueryImpl spec₁ (StateT σ n))
    (bridge : ∀ (q : spec₁.Domain) (s : σ),
      simulateQ impl ((red q).run s) = (game q).run s)
    {α : Type u'} (oa : OracleComp spec₁ α) (s : σ) :
    simulateQ impl ((simulateQ red oa).run s) = (simulateQ game oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [StateT.run_pure]
  | query_bind t f ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, bridge t s]
    exact bind_congr fun p => ih p.1 p.2

/-- Three-layer simulation collapse: if a "reduction" `red : QueryImpl spec₁ (StateT σ
(OracleComp spec₂))` followed by an inner cached `impl : QueryImpl spec₂ (StateT τ n)` agrees
per-query with a single "combined" handler `combined : QueryImpl spec₁ (StateT (σ × τ) n)` up to
the natural reassociation `α × σ × τ ≃ (α × σ) × τ`, then the agreement extends to every outer
computation. This packages the boilerplate induction used by lazy-random-oracle / cached-PRF
collapses. -/
theorem simulateQ_StateT_StateT_compose
    {σ τ : Type u'} {n : Type u' → Type v'} [Monad n] [LawfulMonad n]
    (red : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (impl : QueryImpl spec₂ (StateT τ n))
    (combined : QueryImpl spec₁ (StateT (σ × τ) n))
    (bridge : ∀ (q : spec₁.Domain) (s : σ) (c : τ),
      (simulateQ impl ((red q).run s)).run c =
        (fun r : spec₁.Range q × σ × τ => ((r.1, r.2.1), r.2.2)) <$> combined q (s, c))
    {α : Type u'} (oa : OracleComp spec₁ α) (s : σ) (c : τ) :
    (simulateQ impl ((simulateQ red oa).run s)).run c =
      (fun r : α × σ × τ => ((r.1, r.2.1), r.2.2)) <$> (simulateQ combined oa).run (s, c) := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure x => simp [StateT.run_pure]
  | query_bind t f ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    rw [bridge t s c, bind_map_left, map_bind]
    exact bind_congr fun r => ih r.1 r.2.1 r.2.2

end Compose
