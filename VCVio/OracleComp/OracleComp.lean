/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.OracleQuery
import ToMathlib.PFunctor.Free

/-!
# Computations with Oracle Access

-/

universe u v w

/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`, represented as a free monad over the `PFunctor`
corresponding to `spec.` -/
def OracleComp {ι : Type u} (spec : OracleSpec.{u, v} ι) :
    Type w → Type (max u v w) :=
  PFunctor.FreeM spec.toPFunctor

variable {α β γ : Type v} {ι} {spec : OracleSpec.{u, v} ι}

namespace OracleComp

export OracleQuery (query query_def)

instance (spec : OracleSpec ι) : Monad (OracleComp spec) :=
  inferInstanceAs (Monad (PFunctor.FreeM spec.toPFunctor))

instance (spec : OracleSpec ι) : LawfulMonad (OracleComp spec) :=
  inferInstanceAs (LawfulMonad (PFunctor.FreeM spec.toPFunctor))

instance : MonadLift (OracleQuery spec) (OracleComp spec) :=
  inferInstanceAs (MonadLift (PFunctor.Obj spec.toPFunctor) (PFunctor.FreeM spec.toPFunctor))

/-- Manually lift an `OracleQuery` to an `OracleComp`. -/
@[reducible]
protected def lift {ι} {spec : OracleSpec ι} {α} (q : OracleQuery spec α) :
    OracleComp spec α := liftM q

protected lemma liftM_def (q : OracleQuery spec α) :
    liftM (n := OracleComp spec) q = PFunctor.FreeM.lift q := rfl

@[simp, grind .]
lemma liftM_ne_pure (q : OracleQuery spec α) (x : α) :
    liftM (n := OracleComp spec) q ≠ pure x := by aesop

@[simp, grind .]
lemma pure_ne_liftM (x : α) (q : OracleQuery spec α) :
    pure x ≠ liftM (n := OracleComp spec) q := by aesop

@[simp, grind =]
protected lemma liftM_map (q : OracleQuery spec α) (f : α → β) :
    liftM (n := OracleComp spec) (f <$> q) = f <$> liftM q := rfl

/-- `coin` is the computation representing a coin flip, given a coin flipping oracle. -/
@[inline]
def coin : OracleComp coinSpec Bool := query (spec := coinSpec) ()

@[grind =, aesop unsafe norm]
lemma coin_def : coin = query (spec := coinSpec) () := rfl

protected lemma pure_def (x : α) :
    (pure x : OracleComp spec α) = PFunctor.FreeM.pure x := rfl

protected lemma bind_def (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    oa >>= ob = PFunctor.FreeM.bind oa ob := rfl

protected lemma failure_def : (failure : OptionT (OracleComp spec) α) = OptionT.fail := rfl

protected lemma orElse_def (oa oa' : OptionT (OracleComp spec) α) : (oa <|> oa') = OptionT.mk
    (do match ← OptionT.run oa with | some a => pure (some a) | _  => OptionT.run oa') := by
  simp only [HOrElse.hOrElse, OrElse.orElse, Alternative.orElse, OptionT.orElse]
  refine congr_arg OptionT.mk <| bind_congr fun x => by aesop

@[aesop unsafe apply, grind =>]
protected lemma bind_congr' {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
    (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' := h ▸ bind_congr h'

@[simp] -- NOTE: debatable if this should be simp
lemma guard_eq {spec : OracleSpec ι} (p : Prop) [Decidable p] :
    (guard p : OptionT (OracleComp spec) Unit) = if p then pure () else failure := rfl

-- NOTE: This should maybe be a `@[simp]` lemma? `apply_ite` can't be a simp lemma in general.
lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
    (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
  apply_ite (· >>= ob) p oa oa'

/-- Nicer induction rule for `OracleComp` that uses monad notation.
Allows inductive definitions on computations by considering the two cases:
* `return x` / `pure x` for any `x`
* `do let u ← query i t; oa u` (with inductive results for `oa u`)
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.
If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected def inductionOn {α} {C : OracleComp spec α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OracleComp spec α) →
        (∀ u, C (oa u)) → C (query t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  PFunctor.FreeM.inductionOn pure query_bind oa

/-- Version of `OracleComp.inductionOn` that includes an `OptionT` in the monad stack
and requires an explicit case to handle `failure`. -/
@[elab_as_elim]
protected def inductionOnOptional {α} {C : OptionT (OracleComp spec) α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OptionT (OracleComp spec) α) → (∀ u, C (oa u)) →
      C (query t >>= oa))
    (failure : C failure)
    (oa : OptionT (OracleComp spec) α) : C oa :=
  PFunctor.FreeM.inductionOn
    (fun | some x => pure x | none => failure)
    (fun t => query_bind t) oa

/-- Version of `OracleComp.inductionOn` with the computation at the start. -/
@[elab_as_elim]
protected def induction {α} {C : OracleComp spec α → Prop}
    (oa : OracleComp spec α) (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OracleComp spec α) → (∀ u, C (oa u)) → C (query t >>= oa)) : C oa :=
  PFunctor.FreeM.inductionOn pure query_bind oa

/-- Version of `OracleComp.inductionOnOptional` with the computation at the start. -/
@[elab_as_elim]
protected def inductionOptional {α} {C : OptionT (OracleComp spec) α → Prop}
    (oa : OptionT (OracleComp spec) α) (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OptionT (OracleComp spec) α) → (∀ u, C (oa u)) →
      C (query t >>= oa))
    (failure : C failure) : C oa :=
  PFunctor.FreeM.inductionOn
    (fun | some x => pure x | none => failure)
    query_bind oa

section construct

/-- Version of `construct` with automatic induction on the `query` in when defining the
`query_bind` case. Can be useful with `spec.DecidableEq` and `spec.FiniteRange`.
`mapM`/`simulateQ` is usually preferable to this if the object being constructed is a monad. -/
@[elab_as_elim]
protected def construct {α}
    {C : OracleComp spec α → Type*}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OracleComp spec α) →
      ((u : spec.Range t) → C (oa u)) → C (query t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  PFunctor.FreeM.construct pure query_bind oa

@[simp] lemma construct_pure {α} (x : α)
    {C : OracleComp spec α → Type*} (h_pure : (a : α) → C (pure a))
    (h_query_bind : (t : spec.Domain) →
        (oa : spec.Range t → OracleComp spec α) →
        ((u : spec.Range t) → C (oa u)) → C (query t >>= oa)) :
    OracleComp.construct h_pure h_query_bind (pure x) = h_pure x := rfl

@[simp] lemma construct_query (t : spec.Domain)
    {C : OracleComp spec (spec.Range t) → Type*} (h_pure : (u : spec.Range t) → C (pure u))
    (h_query_bind : (t' : spec.Domain) →
      (oa : spec.Range t' → OracleComp spec (spec.Range t)) →
      ((u : spec.Range t') → C (oa u)) → C (query t' >>= oa)) :
    (OracleComp.construct h_pure h_query_bind
        (query t : OracleComp spec (spec.Range t)) : C (query t)) =
      h_query_bind t pure h_pure := rfl

@[simp] lemma construct_query_bind {α} (t : spec.Domain) (mx : spec.Range t → OracleComp spec α)
    {C : OracleComp spec α → Type*} (h_pure : (a : α) → C (pure a))
    (h_query_bind : (t : spec.Domain) →
        (mx : spec.Range t → OracleComp spec α) →
        ((u : spec.Range t) → C (mx u)) → C (liftM (query t) >>= mx)) :
    OracleComp.construct h_pure h_query_bind (liftM (query t) >>= mx) =
      h_query_bind t mx fun u => OracleComp.construct h_pure h_query_bind (mx u) := rfl

end construct

section noConfusion

variable (x : α) (y : β) (t : spec.Domain) (u : spec.Range t)
  (oa : β → OracleComp spec α) (ou : spec.Range t → OracleComp spec α)

/-- Returns `true` for computations that don't query any oracles or fail, else `false`. -/
def isPure {α : Type _} : OracleComp spec α → Bool
  | PFunctor.FreeM.pure _ => true
  | PFunctor.FreeM.roll _ _ => false

@[simp] lemma isPure_pure : isPure (pure x : OracleComp spec α) = true := rfl
@[simp] lemma isPure_query : isPure (query t : OracleComp spec _) = false := rfl
@[simp] lemma isPure_query_bind : isPure (liftM (query t) >>= ou) = false := rfl

@[simp] lemma pure_ne_query : (pure u : OracleComp spec _) ≠ query t := by simp [query_def]
@[simp] lemma query_ne_pure : (query t : OracleComp spec _) ≠ pure u := by simp [query_def]

lemma pure_eq_query_iff_false : pure u = (query t : OracleComp spec _) ↔ False := by simp
lemma query_eq_pure_iff_false : (query t : OracleComp spec _) = pure u ↔ False := by simp

end noConfusion

/-- Given a computation `oa : OracleComp spec α`, construct a value `x : α`,
by assuming each query returns the `default` value given by the `Inhabited` instance. -/
def defaultResult [spec.Inhabited] (oa : OracleComp spec α) : α :=
  PFunctor.FreeM.mapM (m := Id) (fun _ => default) oa

/-- Total number of queries in a computation across all possible execution paths.
Can be a helpful alternative to `sizeOf` when proving recursive calls terminate. -/
def totalQueries [spec.Fintype] {α : Type v} (oa : OracleComp spec α) : ℕ := by
  induction oa using OracleComp.construct with
  | pure x => exact 0
  | query_bind t oa rec_n => exact 1 + ∑ x, rec_n x

section inj

/-- Two `pure` computations are equal iff they return the same value. -/
@[simp] lemma pure_inj (x y : α) : pure (f := OracleComp spec) x = pure y ↔ x = y :=
  PFunctor.FreeM.pure_inj x y

/-- Binding two computations gives a pure operation iff the first computation is pure
and the second computation does something pure with the result. -/
@[simp] lemma bind_eq_pure_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    oa >>= ob = pure y ↔ ∃ x : α, oa = pure x ∧ ob x = pure y := by
  refine ⟨fun h ↦ ?_, fun h ↦ let ⟨x, ⟨h, h'⟩⟩ := h; h ▸ h'⟩
  simp only [PFunctor.FreeM.monad_bind_def, OracleComp.pure_def] at h
  rwa [PFunctor.FreeM.bind_eq_pure_iff] at h

/-- Binding two computations gives a pure operation iff the first computation is pure
and the second computation does something pure with the result. -/
@[simp] lemma pure_eq_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    pure y = oa >>= ob ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  eq_comm.trans (bind_eq_pure_iff oa ob y)

alias ⟨_, bind_eq_pure⟩ := bind_eq_pure_iff
alias ⟨_, pure_eq_bind⟩ := pure_eq_bind_iff

end inj

end OracleComp
