/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.HasQuery.Morphism

/-!
# Query-Preserving Monad Morphism Canaries

Producer-level tests for identity, composition, and free-oracle interpretation through
`HasQuery.QueryHom`. The reader examples distinguish composition order, while the state example
checks that `QueryHom.ofSimulateQ` preserves a nontrivial handler's state evolution.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.QueryHom

universe uι uQuery uM uN uO

section UniversePolymorphism

variable {ι : Type uι} {spec : OracleSpec.{uι, uQuery} ι}
  {m : Type uQuery → Type uM} [Monad m] [HasQuery spec m]
  {n : Type uQuery → Type uN} [Monad n] [HasQuery spec n]
  {o : Type uQuery → Type uO} [Monad o] [HasQuery spec o]
  {α : Type uQuery}

/-- `QueryHom.id` remains available when the query and target monads live in nonzero,
independently quantified universes. -/
example : HasQuery.QueryHom spec m m := HasQuery.QueryHom.id spec m

example (mx : m α) :
    (HasQuery.QueryHom.id spec m).toMonadHom mx = mx := by simp

/-- `QueryHom.comp` has the same universe generality as its constituent morphisms. -/
example (G : HasQuery.QueryHom spec n o) (F : HasQuery.QueryHom spec m n) :
    HasQuery.QueryHom spec m o := G.comp F

/-- Composition applies the right-hand morphism first. -/
example (G : HasQuery.QueryHom spec n o) (F : HasQuery.QueryHom spec m n) (mx : m α) :
    (G.comp F).toMonadHom mx = G.toMonadHom (F.toMonadHom mx) := by simp

example {p : Type uQuery → Type*} [Monad p] [HasQuery spec p]
    (H : HasQuery.QueryHom spec o p) (G : HasQuery.QueryHom spec n o)
    (F : HasQuery.QueryHom spec m n) :
    (H.comp G).comp F = H.comp (G.comp F) := HasQuery.QueryHom.comp_assoc H G F

end UniversePolymorphism

/-! ## Composition order -/

abbrev ConstSpec : OracleSpec Unit := Unit →ₒ Nat
abbrev Reader := ReaderT Nat Id

instance : HasQuery ConstSpec Reader where
  query _ := pure 0

/-- Reindex a reader environment. Noncommuting reindexings distinguish composition order. -/
def reindex (f : Nat → Nat) : Reader →ᵐ Reader where
  toFun _ mx := fun r => mx (f r)
  toFun_pure' _ := rfl
  toFun_bind' _ _ := rfl

def reindexQueryHom (f : Nat → Nat) : HasQuery.QueryHom ConstSpec Reader Reader where
  toMonadHom := reindex f
  map_query' _ := rfl

def observe : Reader Nat := fun r => pure r

/-- With doubling as `G` and successor as `F`, `G.comp F` observes `2 * 3 + 1 = 7`. This rejects
a swapped implementation of `QueryHom.comp`. -/
example : ((reindexQueryHom (fun n => n * 2)).comp
    (reindexQueryHom (fun n => n + 1))).toMonadHom observe 3 = 7 := rfl

/-- Reversing the morphisms observes `2 * (3 + 1) = 8`, so the preceding canary is not accidentally
commutative. -/
example : ((reindexQueryHom (fun n => n + 1)).comp
    (reindexQueryHom (fun n => n * 2))).toMonadHom observe 3 = 8 := rfl

/-! ## Stateful free-oracle interpretation -/

abbrev CountSpec : OracleSpec Unit := Unit →ₒ Nat

def countImpl : QueryImpl CountSpec (StateM Nat) := fun _ => do
  let s ← get
  set (s + 1)
  pure s

def twoQueries : OracleComp CountSpec (Nat × Nat) := do
  let x ← HasQuery.query (spec := CountSpec) ()
  let y ← HasQuery.query (spec := CountSpec) ()
  pure (x, y)

/-- The `ofSimulateQ` producer uses the installed query handler and threads its state across
successive free-oracle queries. A constant, reset-per-query, or state-discarding interpreter fails
this canary. -/
example :
    letI : HasQuery CountSpec (StateM Nat) := countImpl.toHasQuery
    StateT.run ((HasQuery.QueryHom.ofSimulateQ
      (spec := CountSpec) (m := StateM Nat)).toMonadHom twoQueries) 3 = ((3, 4), 5) := by
  rfl

end VCVioTest.QueryHom
