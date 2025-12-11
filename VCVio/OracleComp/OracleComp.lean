/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.Control.Monad.Free
import ToMathlib.Control.WriterT
import ToMathlib.Control.AlternativeMonad
import ToMathlib.Control.OptionT
import Mathlib.Control.Lawful
import VCVio.OracleComp.OracleSpec

/-!
# Computations with Oracle Access

A value `oa : OracleComp spec α` represents a computation with return type `α`,
with access to any of the oracles specified by `spec : OracleSpec`.
Returning a value `x` corresponds to the computation `pure' α x`.
The computation `queryBind' i t α ou` represents querying the oracle corresponding to index `i`
on input `t`, getting a result `u : spec.range i`, and then running `ou u`.
We also allow for a `failure'` operation for quitting out.
These operations induce `Monad` and `Alternative` instances on `OracleComp spec`.

`pure' α a` gives a monadic `pure` operation, while a more general `>>=` operator
is derived by induction on the first computation (see `OracleComp.bind`).
This importantly allows us to define a `LawfulMonad` instance on `OracleComp spec`,
which isn't possible if a general bind operator is included in the main syntax.

We also define simple operations like `coin : OracleComp coinSpec Bool` for flipping a fair coin,
and `$[0..n] : ProbComp (Fin (n + 1))` for selecting from an inclusive range.

Note that the monadic structure on `OracleComp` exists only for a fixed `OracleSpec`,
so it isn't possible to combine computations where one has a superset of oracles of the other.
We later introduce a set of type coercions that mitigate this for most common cases,
such as calling a computation with `spec` as part of a computation with `spec ++ spec'`.
-/

universe u v w z

namespace OracleSpec

/-- An `OracleQuery` to one of the oracles in `spec`, bundling an index and the input to
use for querying that oracle, implemented as a dependent pair.
Implemented as a functor with the oracle output type as the constructor result. -/
inductive OracleQuery {ι : Type u} (spec : OracleSpec.{u,v} ι) : Type v → Type (max u v)
  | query (i : ι) (t : spec.domain i) : OracleQuery spec (spec.range i)

namespace OracleQuery

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type v}

def defaultOutput [∀ i, Inhabited (spec.range i)] : (q : OracleQuery spec α) → α
  | query i t => default

def index : (q : OracleQuery spec α) → ι | query i t => i

@[simp] lemma index_query (i : ι) (t : spec.domain i) : (query i t).index = i := rfl

def input : (q : OracleQuery spec α) → spec.domain q.index | query i t => t

@[simp] lemma input_query (i : ι) (t : spec.domain i) : (query i t).input = t := rfl

@[simp]
lemma range_index : (q : OracleQuery spec α) → spec.range q.index = α | query i t => rfl

lemma eq_query_index_input : (q : OracleQuery spec α) →
    q = q.range_index ▸ OracleQuery.query q.index q.input | query i t => rfl

def rangeDecidableEq [spec.DecidableEq] : OracleQuery spec α → DecidableEq α
  | query i t => inferInstance

def rangeFintype [spec.FiniteRange] : OracleQuery spec α → Fintype α
  | query i t => inferInstance

def rangeInhabited [spec.FiniteRange] : OracleQuery spec α → Inhabited α
  | query i t => inferInstance

instance isEmpty : IsEmpty (OracleQuery []ₒ α) where false | query i t => i.elim

instance [hι : DecidableEq ι] [hd : ∀ i, DecidableEq (spec.domain i)] {α : Type u} :
    DecidableEq (OracleQuery spec α)
  | query i t => λ q ↦ match hι i q.index with
    | isTrue h => by
        have : q = query i (h ▸ q.input) := by
          refine q.eq_query_index_input.trans (eq_of_heq (eqRec_heq_iff_heq.2 ?_))
          congr
          · exact h.symm
          · exact HEq.symm (eqRec_heq (Eq.symm h) q.input)
        rw [this, query.injEq]
        exact hd i t _
    | isFalse h => isFalse λ h' ↦ h (congr_arg index h')

end OracleQuery

-- Put `query` in the main `OracleSpec` namespace
export OracleQuery (query)

end OracleSpec

open OracleSpec

/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`.
The basic computation is just an `OracleQuery`, augmented with `pure` and `bind` by `FreeMonad`,
and `failure` is also added after by the `OptionT` transformer.

In practive computations in `OracleComp spec α` have have one of three forms:
* `return x` to succeed with some `x : α` as the result.
* `do u ← query i t; oa u` where `oa` is a continutation to run with the query result
* `failure` which terminates the computation early
See `OracleComp.inductionOn` for an explicit induction principle. -/
def OracleComp {ι : Type u} (spec : OracleSpec.{u,v} ι) :
    Type w → Type (max u (v + 1) w) :=
  OptionT (FreeMonad (OracleQuery.{u,v} spec))

/-- Simplified notation for computations with no oracles besides random inputs. -/
abbrev ProbComp : Type z → Type (max z 1) := OracleComp unifSpec

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type v}

instance : AlternativeMonad (OracleComp spec) :=
  inferInstanceAs (AlternativeMonad (OptionT (FreeMonad (OracleQuery spec))))

instance : LawfulMonad (OracleComp spec) :=
  inferInstanceAs (LawfulMonad (OptionT (FreeMonad (OracleQuery spec))))

instance : LawfulAlternative (OracleComp spec) :=
  inferInstanceAs (LawfulAlternative (OptionT (FreeMonad (OracleQuery spec))))

instance : Inhabited (OracleComp spec α) := ⟨failure⟩

section lift

/-- Lift a query by first lifting to the free moand and then to the option. -/
def lift (q : OracleQuery spec α) : OracleComp spec α :=
  OptionT.lift (FreeMonad.lift q)

/-- Automatically coerce an `OracleQuery spec α` to an `OracleComp spec α`. -/
instance : MonadLift (OracleQuery spec) (OracleComp spec) where
  monadLift := lift

/-- Lift a function on oracle queries to one on oracle computations. -/
instance : MonadFunctor (OracleQuery spec) (OracleComp spec) where
  monadMap f := (OptionT.instMonadFunctor).monadMap
    ((FreeMonad.instMonadFunctor).monadMap f)

protected lemma liftM_def (q : OracleQuery spec α) :
    (q : OracleComp spec α) = OptionT.lift (FreeMonad.lift q) := rfl
alias lift_query_def := OracleComp.liftM_def

--@[simp] -- Usually this is a better simp pathway but occasionally bad. Simp specific cases below
lemma liftM_query_eq_liftM_liftM {m : Type v → Type z} [MonadLift (OracleComp spec) m] {α : Type v}
    (q : OracleQuery spec α) : (liftM q : m α) = liftM (liftM q : OracleComp spec α) := rfl

@[simp]
lemma liftM_query_stateT {σ : Type v} {α : Type v} (q : OracleQuery spec α) :
  (liftM q : StateT σ (OracleComp spec) α) = liftM (liftM q : OracleComp spec α) := rfl

@[simp]
lemma liftM_query_writerT {ω : Type v} [Monoid ω] {α : Type v} (q : OracleQuery spec α) :
  (liftM q : WriterT ω (OracleComp spec) α) = liftM (liftM q : OracleComp spec α) := rfl

@[simp]
lemma liftM_query_readerT {ρ : Type v} {α : Type v} (q : OracleQuery spec α) :
  (liftM q : ReaderT ρ (OracleComp spec) α) = liftM (liftM q : OracleComp spec α) := rfl

lemma query_bind_eq_roll (q : OracleQuery spec α) (ob : α → OracleComp spec β) :
    (q : OracleComp spec α) >>= ob = OptionT.mk (FreeMonad.roll q ob) := rfl

end lift

protected lemma pure_def (x : α) : (pure x : OracleComp spec α) = OptionT.pure x := rfl

protected lemma bind_def (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    oa >>= ob = OptionT.bind oa ob := rfl

protected lemma failure_def : (failure : OracleComp spec α) = OptionT.fail := rfl

protected lemma orElse_def (oa oa' : OracleComp spec α) : (oa <|> oa') = OptionT.mk
      (do match ← OptionT.run oa with | some a => pure (some a) | _  => OptionT.run oa') := rfl

protected lemma bind_congr' {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
    (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' := h ▸ bind_congr h'

/-- `coin` is the computation representing a coin flip, given a coin flipping oracle. -/
@[reducible, inline] def coin : OracleComp coinSpec Bool :=
  coinSpec.query () ()

/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range. -/
@[reducible, inline] def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) :=
  unifSpec.query n ()

@[reducible, inline] def uniformFin' (n m : ℕ) : OracleComp probSpec (Fin (m + 1)) :=
  probSpec.query m n

notation "$[0.." n "]" => uniformFin n

-- TODO: could consider this notation if we switch to probspec
notation:50 "$[" n "⋯" m "]" => uniformFin' n m

example : OracleComp probSpec ℕ := do
  let x ← $[314⋯31415]; let y ← $[0⋯x]
  return x + 2 * y

@[simp] -- NOTE: debatable if this should be simp
lemma guard_eq {ι : Type} {spec : OracleSpec ι} (p : Prop) [Decidable p] :
    (guard p : OracleComp spec Unit) = if p then pure () else failure := rfl

-- NOTE: This should maybe be a `@[simp]` lemma? `apply_ite` can't be a simp lemma in general.
lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
    (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
  apply_ite (· >>= ob) p oa oa'

/-- Nicer induction rule for `OracleComp` that uses monad notation.
Allows inductive definitions on compuations by considering the three cases:
* `return x` / `pure x` for any `x`
* `do let u ← query i t; oa u` (with inductive results for `oa u`)
* `failure`
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.
If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected def inductionOn {C : OracleComp spec α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (i : ι) → (t : spec.domain i) →
      (oa : spec.range i → OracleComp spec α) → (∀ u, C (oa u)) → C (query i t >>= oa))
    (failure : C failure) (oa : OracleComp spec α) : C oa :=
  FreeMonad.inductionOn (Option.rec failure pure) (λ (query i t) ↦ query_bind i t) oa

@[elab_as_elim]
protected def induction {C : OracleComp spec α → Prop}
    (oa : OracleComp spec α) (pure : (a : α) → C (pure a))
    (query_bind : (i : ι) → (t : spec.domain i) →
      (oa : spec.range i → OracleComp spec α) → (∀ u, C (oa u)) → C (query i t >>= oa))
    (failure : C failure) : C oa :=
  FreeMonad.inductionOn (Option.rec failure pure) (λ (query i t) ↦ query_bind i t) oa

section construct

/-- NOTE: if `inductionOn` could work with `Sort u` instead of `Prop` we wouldn't need this,
not clear to me why lean doesn't like unifying the `Prop` and `Type` cases.

If the output type of `C` is a monad then `OracleComp.mapM` is usually preferable. -/
@[elab_as_elim]
protected def construct {C : OracleComp spec α → Type*}
    (pure : (a : α) → C (pure a))
    (query_bind : {β : Type v} → (q : OracleQuery spec β) →
      (oa : β → OracleComp spec α) → ((u : β) → C (oa u)) → C (q >>= oa))
    (failure : C failure) (oa : OracleComp spec α) : C oa :=
  FreeMonad.construct (Option.rec failure pure) query_bind oa

/-- Version of `construct` with automatic induction on the `query` in when defining the
`query_bind` case. Can be useful with `spec.DecidableEq` and `spec.FiniteRange`.
NOTE: may be better to just use this universally in all cases? avoids duplicating lemmas below. -/
@[elab_as_elim]
protected def construct' {C : OracleComp spec α → Type*}
    (pure : (a : α) → C (pure a))
    (query_bind : (i : ι) → (t : spec.domain i) →
      (oa : spec.range i → OracleComp spec α) →
      ((u : spec.range i) → C (oa u)) → C (query i t >>= oa))
    (failure : C failure) (oa : OracleComp spec α) : C oa :=
  oa.construct pure (λ (query i t) ↦ query_bind i t) failure

variable {C : OracleComp spec α → Type w}
  (h_pure : (a : α) → C (pure a))
  (h_query_bind : {β : Type v} → (q : OracleQuery spec β) →
      (oa : β → OracleComp spec α) → ((u : β) → C (oa u)) → C (q >>= oa))
  (h_failure : C failure) (oa : OracleComp spec α)

@[simp]
lemma construct_pure (x : α) :
    OracleComp.construct h_pure h_query_bind h_failure (pure x) = h_pure x := rfl

@[simp]
lemma construct_failure :
    OracleComp.construct h_pure h_query_bind h_failure failure = h_failure := rfl

@[simp]
lemma construct_query (q : OracleQuery spec α) :
    (OracleComp.construct h_pure h_query_bind h_failure (q : OracleComp spec α) : C q) =
      h_query_bind q pure h_pure := rfl
alias construct_liftM := construct_query

@[simp]
lemma construct_query_bind (q : OracleQuery spec β) (oa : β → OracleComp spec α) :
    (OracleComp.construct h_pure h_query_bind h_failure ((q : OracleComp spec β) >>= oa)) =
      h_query_bind q oa (λ u ↦ (oa u).construct h_pure h_query_bind h_failure) := rfl

@[simp]
lemma construct_roll (q : OracleQuery spec β) (oa : β → OracleComp spec α) :
    (OracleComp.construct h_pure h_query_bind h_failure (OptionT.mk (FreeMonad.roll q oa)) :
      C (OptionT.mk (FreeMonad.roll q oa))) = h_query_bind q oa
        (λ u ↦ (oa u).construct h_pure h_query_bind h_failure) := rfl

end construct

section noConfusion

variable (x : α) (y : β) (q : OracleQuery spec β) (oa : β → OracleComp spec α)

/-- Returns `true` for computations that don't query any oracles or fail, else `false`. -/
def isPure {α : Type v} : OracleComp spec α → Bool
  | FreeMonad.pure x => Option.isSome x
  | _ => false

/-- Returns `true` for computations that fail else `false`. -/
def isFailure {α : Type v} : OracleComp spec α → Bool
  | FreeMonad.pure x => Option.isNone x
  | _ => false

@[simp] lemma isPure_pure : isPure (pure x : OracleComp spec α) = true := rfl
@[simp] lemma isPure_query_bind : isPure ((q : OracleComp spec β) >>= oa) = false := rfl
@[simp] lemma isPure_failure : isPure (failure : OracleComp spec α) = false := rfl
@[simp] lemma isFailure_pure : isFailure (pure x : OracleComp spec α) = false := rfl
@[simp] lemma isFailure_query_bind : isFailure ((q : OracleComp spec β) >>= oa) = false := rfl
@[simp] lemma isFailure_failure : isFailure (failure : OracleComp spec α) = true := rfl

lemma exists_eq_of_isPure {oa : OracleComp spec α} (h : isPure oa) : ∃ x, oa = pure x := by
  induction oa using OracleComp.inductionOn with
  | pure => apply exists_apply_eq_apply' | query_bind => simp at h | failure => simp at h

lemma eq_failure_of_isFailure {oa : OracleComp spec α} (h : isFailure oa) : oa = failure := by
  induction oa using OracleComp.inductionOn with
  | pure => simp at h | query_bind => simp at h | failure => rfl

@[simp] lemma pure_ne_query : pure y ≠ (q : OracleComp spec β) := nofun
@[simp] lemma query_ne_pure : (q : OracleComp spec β) ≠ pure y := nofun

@[simp] lemma pure_ne_query_bind : pure x ≠ (q : OracleComp spec β) >>= oa := nofun
@[simp] lemma query_bind_ne_pure : (q : OracleComp spec β) >>= oa ≠ pure x := nofun

@[simp] lemma pure_ne_failure : (pure x : OracleComp spec α) ≠ failure := nofun
@[simp] lemma failure_ne_pure : failure ≠ (pure x : OracleComp spec α) := nofun

@[simp] lemma failure_ne_query_bind : failure ≠ (q : OracleComp spec β) >>= oa := nofun
@[simp] lemma query_bind_ne_failure : (q : OracleComp spec β) >>= oa ≠ failure := nofun

@[simp] lemma query_ne_failure : (q : OracleComp spec β) ≠ failure := nofun
@[simp] lemma failure_ne_query : failure ≠ (q : OracleComp spec β) := nofun

lemma pure_eq_query_iff_false : pure y = (q : OracleComp spec β) ↔ False := by simp
lemma query_eq_pure_iff_false : (q : OracleComp spec β) = pure y ↔ False := by simp

end noConfusion

section mapM

/-- Implement all queries in a computation using some other monad `m`,
preserving the pure and bind operations, giving a computation in the new monad.
The function `qm` specifies how to replace the queries in the computation,
and `fail` is used whenever `failure` is encountered.
If the final output type has an `Alternative` instance then `simulate` is usually preffered. -/
protected def mapM {m : Type v → Type w} [Monad m]
    (fail : {α : Type v} → m α)
    (query_map : {α : Type v} → OracleQuery spec α → m α)
    (oa : OracleComp spec α) : m α :=
  OracleComp.construct pure (λ q _ r ↦ query_map q >>= r) fail oa

variable {m : Type v → Type w} [Monad m]
  (fail : {α : Type v} → m α) (qm : {α : Type v} → OracleQuery spec α → m α)

@[simp] lemma mapM_pure (x : α) : (pure x : OracleComp spec α).mapM fail qm = pure x := rfl

@[simp] lemma mapM_failure : (failure : OracleComp spec α).mapM fail qm = fail := rfl

@[simp]
lemma mapM_query [LawfulMonad m] (q : OracleQuery spec α) :
    (q : OracleComp spec α).mapM fail qm = qm q :=
  by simp only [OracleComp.mapM, construct_query, bind_pure]

@[simp]
lemma mapM_query_bind (q : OracleQuery spec α) (ob : α → OracleComp spec β) :
    ((q : OracleComp spec α) >>= ob).mapM fail qm =
      (do let x ← qm q; (ob x).mapM fail qm) := rfl

lemma mapM_bind [LawfulMonad m] (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (hfail : ∀ f : α → m β, fail >>= f = fail) :
    (oa >>= ob).mapM fail qm =
      oa.mapM fail qm >>= λ x ↦ (ob x).mapM fail qm := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa h => simp [h]
  | failure => simp [hfail]

@[simp]
lemma mapM_bind' {m : Type v → Type w} [AlternativeMonad m] [LawfulMonad m]
    [LawfulAlternative m] (qm : {α : Type v} → OracleQuery spec α → m α)
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).mapM failure qm =
      oa.mapM failure qm >>= λ x ↦ (ob x).mapM failure qm :=
  mapM_bind _ _ _ _ failure_bind

lemma mapM_map [LawfulMonad m] (oa : OracleComp spec α) (f : α → β)
    (hfail : ∀ f : α → β, f <$> fail = fail) :
    (f <$> oa).mapM fail qm = f <$> oa.mapM fail qm := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa h => simp [h]
  | failure => simp [hfail]

@[simp]
lemma mapM_map' {m : Type v → Type w} [AlternativeMonad m] [LawfulAlternative m]
    [LawfulMonad m] (qm : {α : Type v} → OracleQuery spec α → m α)
    (oa : OracleComp spec α) (f : α → β) :
    (f <$> oa).mapM failure qm = f <$> oa.mapM failure qm := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i t oa h => simp [h]
  | failure => simp

lemma mapM_seq [LawfulMonad m] (og : OracleComp spec (α → β)) (oa : OracleComp spec α)
    (hfail : ∀ f : (α → β) → m β, fail >>= f = fail)
    (hfail' : ∀ f : α → β, f <$> fail = fail) :
    (og <*> oa).mapM fail qm = og.mapM fail qm <*> oa.mapM fail qm := by
  rw [seq_eq_bind, seq_eq_bind]
  exact (mapM_bind _ _ _ _ hfail).trans
    (congr_arg (_ >>= ·) (funext λ f ↦ (mapM_map _ _ _ _ hfail')))

@[simp]
lemma mapM_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    (ite p oa oa').mapM fail qm = ite p (oa.mapM fail qm) (oa'.mapM fail qm) := by
  split_ifs <;> rfl

end mapM

/-- Given a computation `oa : OracleComp spec α`, construct a value `x : α`,
by assuming each query returns the `default` value given by the `Inhabited` instance.
Returns `none` if the default path would lead to failure. -/
def defaultResult [spec.FiniteRange] (oa : OracleComp spec α) : Option α :=
  oa.mapM (fail := none) (query_map := some ∘ OracleQuery.defaultOutput)

/-- Total number of queries in a computation across all possible execution paths.
Can be a helpful alternative to `sizeOf` when proving recursive calls terminate. -/
def totalQueries [FiniteRange spec] {α : Type v} (oa : OracleComp spec α) : ℕ := by
  induction oa using OracleComp.construct' with
  | pure x => exact 0
  | failure => exact 0
  | query_bind i t oa rec_n =>
    exact 1 + ∑ x, rec_n x

section inj

@[simp]
lemma pure_inj (x y : α) : (pure x : OracleComp spec α) = pure y ↔ x = y := by
  simp [OracleComp.pure_def, OptionT.pure, OptionT.mk]
  rw [FreeMonad.pure.injEq, Option.some_inj]

@[simp]
lemma liftM_inj (q q' : OracleQuery spec α) : (q : OracleComp spec α) = q' ↔ q = q' := by
  simp only [OracleComp.liftM_def, OptionT.lift, OptionT.mk, FreeMonad.monad_pure_def,
    FreeMonad.monad_bind_def, FreeMonad.bind_lift]
  rw [FreeMonad.roll.injEq]
  simp only [heq_eq_eq, and_true, true_and]

@[simp]
lemma query_inj (i : ι) (t t' : spec.domain i) :
    (query i t : OracleComp spec (spec.range i)) = query i t' ↔ t = t' := by
  simp only [liftM_inj, OracleQuery.query.injEq]

@[simp]
lemma queryBind_inj (q q' : OracleQuery spec α) (ob ob' : α → OracleComp spec β) :
    (q : OracleComp spec α) >>= ob = (q' : OracleComp spec α) >>= ob' ↔ q = q' ∧ ob = ob' := by
  simp only [OracleComp.liftM_def, OptionT.lift, OptionT.mk, FreeMonad.monad_pure_def,
    FreeMonad.monad_bind_def, FreeMonad.bind_lift, OracleComp.bind_def, OptionT.bind,
    FreeMonad.bind_roll, FreeMonad.bind_pure]
  rw [FreeMonad.roll.injEq]
  simp only [heq_eq_eq, true_and]

@[simp]
lemma bind_eq_pure_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    oa >>= ob = pure y ↔ ∃ x : α, oa = pure x ∧ ob x = pure y := by
  refine ⟨λ h ↦ ?_, λ h ↦ let ⟨x, ⟨h, h'⟩⟩ := h; h ▸ h'⟩
  induction oa using OracleComp.induction with
  | pure x => simp [← h]
  | _ => simp at h

@[simp]
lemma pure_eq_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    pure y = oa >>= ob ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  eq_comm.trans (bind_eq_pure_iff oa ob y)

alias ⟨_, bind_eq_pure⟩ := bind_eq_pure_iff
alias ⟨_, pure_eq_bind⟩ := pure_eq_bind_iff

end inj

/-- If the oracle indexing-type `ι`, output type `α`, and domains of all oracles have `DecidableEq`
then `OracleComp spec α` also has `DecidableEq`. -/
protected instance instDecidableEq [spec.FiniteRange] [hd : ∀ i, DecidableEq (spec.domain i)]
    [hι : DecidableEq ι] [h : DecidableEq α] : DecidableEq (OracleComp spec α) := fun
  | FreeMonad.pure (Option.some x), FreeMonad.pure (Option.some y) =>
    match h x y with
    | isTrue rfl => isTrue rfl
    | isFalse h => isFalse λ h' ↦ h (by rwa [FreeMonad.pure.injEq, Option.some_inj] at h')
  | FreeMonad.pure Option.none, FreeMonad.pure (Option.some y) => isFalse λ h ↦
      Option.some_ne_none y (by rwa [FreeMonad.pure.injEq, eq_comm] at h)
  | FreeMonad.pure (Option.some x), FreeMonad.pure Option.none => isFalse λ h ↦
      Option.some_ne_none x (by rwa [FreeMonad.pure.injEq] at h)
  | FreeMonad.pure Option.none, FreeMonad.pure Option.none => isTrue rfl
  | FreeMonad.pure x, FreeMonad.roll q r => isFalse <| by simp
  | FreeMonad.roll q r, FreeMonad.pure x => isFalse <| by simp
  | FreeMonad.roll (OracleQuery.query i t) r, FreeMonad.roll (OracleQuery.query i' t') s =>
    match hι i i' with
    | isTrue h => by
        induction h
        rw [FreeMonad.roll.injEq, heq_eq_eq, OracleQuery.query.injEq, eq_self, true_and, heq_eq_eq]
        refine @instDecidableAnd _ _ (hd i t t') ?_
        suffices Decidable (∀ u, r u = s u) from decidable_of_iff' _ funext_iff
        suffices ∀ u, Decidable (r u = s u) from Fintype.decidableForallFintype
        exact λ u ↦ OracleComp.instDecidableEq (r u) (s u)
    | isFalse h => isFalse λ h' ↦ h <|
        match FreeMonad.roll.inj h' with
        | ⟨h1, h2, _⟩ => @congr_heq _ _ ι OracleQuery.index OracleQuery.index
            (query i t) (query i' t') (h1 ▸ HEq.rfl) h2

end OracleComp
