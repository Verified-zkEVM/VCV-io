/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleSpec

universe u v w z

open OracleSpec

/-- Functor to represent queries to oracles specified by an `OracleSpec ι`,
defined to be the object type of the corresponding `PFunctor`.
In particular an element of `OracleQuery spec α` consists of an input value `t : spec.Domain`,
and a continuation `f : spec.Range t → α` specifying what to do with the result.
See `OracleQuery.query` for the case when the continuation `f` just returns the query result. -/
def OracleQuery {ι : Type u} (spec : OracleSpec.{u,v} ι) :
    Type w → Type (max u v w) :=
  PFunctor.Obj spec.toPFunctor

@[reducible] protected def OracleQuery.mk {ι α} {spec : OracleSpec ι}
    (t : spec.Domain) (f : spec.Range t → α) : OracleQuery spec α := ⟨t, f⟩

namespace OracleQuery

variable {ι} {spec : OracleSpec ι}

/-- `OracleQuery spec` inherets the functorial structure from `PFunctor.Obj`. -/
instance {spec : OracleSpec ι} : Functor (OracleQuery spec) where
  map := spec.toPFunctor.map

instance {spec : OracleSpec ι} : LawfulFunctor (OracleQuery spec) :=
  inferInstanceAs (LawfulFunctor (PFunctor.Obj spec.toPFunctor))

/-- The oracle input used in an oracle query. -/
@[inline, reducible]
def input {α} (q : OracleQuery spec α) : spec.Domain := q.1

@[simp] lemma input_apply {α} (t : spec.Domain) (f : spec.Range t → α) :
    input ⟨t, f⟩ = t := rfl

@[simp] lemma input_map {α β} (q : OracleQuery spec α) (f : α → β) :
    (f <$> q).input = q.input := rfl

@[simp] lemma input_map' {α β} (q : OracleQuery spec α) (f : α → β) :
    OracleQuery.input (PFunctor.map spec.toPFunctor f q) = q.input := rfl

/-- The continutation used for the result of an oracle query. -/
@[inline, reducible]
def cont {α} (q : OracleQuery spec α) (f : spec.Range q.input) : α := q.2 f

@[simp] lemma cont_apply {α} (t : spec.Domain) (f : spec.Range t → α) :
    cont ⟨t, f⟩ = f := rfl

@[simp] lemma cont_map {α β} (q : OracleQuery spec α) (f : α → β) :
    (f <$> q).cont = f ∘ q.cont := rfl

@[simp] lemma cont_map' {α β} (q : OracleQuery spec α) (f : α → β) :
    OracleQuery.cont (PFunctor.map spec.toPFunctor f q) = f ∘ q.cont := rfl

/-- Two oracles queries are equal if they query for the same input and run
extensionally equal continuation on the results of the query. -/
@[ext] lemma ext {α} {q q' : OracleQuery spec α}
    (h : q.input = q'.input) (h' : q.cont ≍ q'.cont) : q = q' := Sigma.ext h h'

/-- If an oracle exists and the output type is non-empty then the type of queries is non-empty. -/
instance {α} [Inhabited ι] [Inhabited α] : Inhabited (OracleQuery spec α) :=
  inferInstanceAs (Inhabited ((t : spec.Domain) × (spec.Range t → α)))

/-- If there are no oracles available then the type of queries is empty. -/
instance {α} [h : IsEmpty ι] : IsEmpty (OracleQuery spec α) :=
  inferInstanceAs (IsEmpty ((t : spec.Domain) × (spec.Range t → α)))

/-- If there is a at most one oracle and output, then ther is at most one query.-/
instance {α} [h : Subsingleton ι] [h' : Subsingleton α] :
    Subsingleton (OracleQuery spec α) where
  allEq := fun ⟨t, f⟩ ⟨u, g⟩ => by
    cases h.allEq t u
    simp [OracleQuery.ext_iff, funext_iff]
    refine fun x => h'.allEq (f x) (g x)

/-- Query an oracle on in input `t` to get a result in the corresponding `range t`.
Note: could consider putting this in the `OracleQuery` monad, type inference struggles tho. -/
def query (t : spec.Domain) : OracleQuery spec (spec.Range t) := OracleQuery.mk t id

lemma query_def (t : spec.Domain) : query t = ⟨t, id⟩ := rfl

@[simp] lemma input_query (t : spec.Domain) : (query t).input = t := rfl
@[simp] lemma cont_query (t : spec.Domain) : (query t).cont = id := rfl

@[simp] lemma fst_query (t : spec.Domain) : (query t).1 = t := rfl
@[simp] lemma snd_query (t : spec.Domain) : (query t).2 = id := rfl

@[simp] lemma cont_map_query_input {α} (q : OracleQuery spec α) :
    q.cont <$> (query q.input) = q := rfl

@[simp] lemma cont_map_query_input' {α} (q : OracleQuery spec α) :
    PFunctor.map spec.toPFunctor q.cont (query q.input) = q := rfl

@[simp] lemma query_eq_mk_iff (t : spec.Domain) (cont : spec.Range t → spec.Range t) :
    query t = OracleQuery.mk t cont ↔ cont = id := by
  rw [OracleQuery.ext_iff]
  aesop

@[simp] lemma mk_eq_query_iff (t : spec.Domain) (cont : spec.Range t → spec.Range t) :
    OracleQuery.mk t cont = query t ↔ cont = id := by
  rw [OracleQuery.ext_iff]
  aesop

end OracleQuery
