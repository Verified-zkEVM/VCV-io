/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Primitives
public import VCVio.OracleComp.HasQuery.Morphism
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Explicit public-hash oracle for SLH-DSA

This module gives the public SLH-DSA hash operations an explicit oracle syntax.  `F`, `H = T₂`,
and `T_l` are arity-specific wrappers around one tweakable-hash collection query.  Its identity
retains the public seed, the instantiation's canonical encoded address, and the full ordered input
list.  Thus the ideal model has exactly the aliases of the concrete address serialization.

The query domain depends only on `CorePrimitives`, which contains no implementation of either
public operation. `PublicHash.impl` separately packages the deterministic `Thash` and `Hmsg`
fields of a full `Primitives` bundle as a `QueryImpl`.
`PublicHash.randomOracle` instead samples each previously unseen tagged query once and caches the
answer.  Both handlers interpret the same canonical `OracleComp` programs.

The keyed operations `PRF` and `PRF_msg` are intentionally not part of this public interface:
security games may expose this oracle to an adversary without exposing secret-key operations.
This is a modular tweakable-hash/PRF model, not a claim that every named operation is an
independent domain of one raw SHA/XOF random oracle.  A proof connecting the model to a concrete
hash instantiation must discharge the corresponding PRF and public-collection assumptions.

## References

- NIST FIPS 205, Section 4.1 (`F`, `H`, `T_l`, and `H_msg`)
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA

variable {p : Params}

/-- A query to the public SLH-DSA hash collection.  The carrier types are explicit
parameters so the generated decidable-equality instance uses the caller's concrete instances. -/
inductive PublicHashQuery (PkSeed AdrsKey Y : Type) where
  /-- `T_l(PK.seed, encodedADRS, xs)`.  `F` and `H` use lists of length one and two. -/
  | thash (pkSeed : PkSeed) (adrsKey : AdrsKey) (xs : List Y)
  /-- `H_msg(R, PK.seed, PK.root, M)`. -/
  | hmsg (r : Y) (pkSeed : PkSeed) (pkRoot : Y) (msg : List Byte)
deriving DecidableEq

/-- The dependent public-hash specification.  Reducibility is intentional: consumers must see
that `thash` returns a node while `H_msg` returns a digest. -/
@[reducible] def publicHashSpec (core : CorePrimitives p) :
    OracleSpec (PublicHashQuery core.PkSeed core.AdrsKey core.Y)
  | .thash _ _ _ => core.Y
  | .hmsg _ _ _ _ => Bytes p.m

namespace PublicHash

/-- Issue an explicit `F` query. -/
def f (core : CorePrimitives p) {m : Type → Type*} [HasQuery (publicHashSpec core) m]
    (pkSeed : core.PkSeed) (adrs : Adrs) (x : core.Y) : m core.Y :=
  query (spec := publicHashSpec core)
    (PublicHashQuery.thash pkSeed (core.adrsToKey adrs) [x])

/-- Issue an explicit ordered binary-node `H` query. -/
def h (core : CorePrimitives p) {m : Type → Type*} [HasQuery (publicHashSpec core) m]
    (pkSeed : core.PkSeed) (adrs : Adrs) (left right : core.Y) : m core.Y :=
  query (spec := publicHashSpec core)
    (PublicHashQuery.thash pkSeed (core.adrsToKey adrs) [left, right])

/-- Issue an explicit variable-arity `T_l` query. -/
def tl (core : CorePrimitives p) {m : Type → Type*} [HasQuery (publicHashSpec core) m]
    (pkSeed : core.PkSeed) (adrs : Adrs) (xs : List core.Y) : m core.Y :=
  query (spec := publicHashSpec core)
    (PublicHashQuery.thash pkSeed (core.adrsToKey adrs) xs)

/-- Issue an explicit `H_msg` query. -/
def hmsg (core : CorePrimitives p) {m : Type → Type*} [HasQuery (publicHashSpec core) m]
    (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    m (Bytes p.m) :=
  query (spec := publicHashSpec core) (PublicHashQuery.hmsg r pkSeed pkRoot msg)

/-- Deterministically interpret the public-hash syntax using the functions in `Primitives`. -/
def impl (prims : Primitives p) : QueryImpl (publicHashSpec prims.core) Id
  | .thash pkSeed encodedAdrs xs => prims.Thash pkSeed encodedAdrs xs
  | .hmsg r pkSeed pkRoot msg => prims.Hmsg r pkSeed pkRoot msg

/-- Extend an implementation-independent context with an arbitrary deterministic public-hash
handler. This packages a fixed answer table as a `Primitives` bundle for deterministic
interpretation proofs; oracle-parametric developments use the `PublicHash` programs directly. -/
@[reducible] def withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) :
    Primitives p where
  toCorePrimitives := core
  Thash pkSeed encodedAdrs xs := answer (.thash pkSeed encodedAdrs xs)
  Hmsg r pkSeed pkRoot msg := answer (.hmsg r pkSeed pkRoot msg)

/-- Packaging an answer function and then taking its deterministic interpreter recovers the
same public-hash handler. -/
@[simp] theorem impl_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) :
    impl (withPublicHash core answer) = answer := by
  funext q
  cases q <;> rfl

@[simp] theorem simulateQ_f (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.f prims.core pkSeed adrs x :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      prims.F pkSeed adrs x := by
  simp only [f, simulateQ_HasQuery_query, impl]

@[simp] theorem simulateQ_h (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (left right : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.h prims.core pkSeed adrs left right :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      prims.H pkSeed adrs left right := by
  simp only [h, simulateQ_HasQuery_query, impl]

@[simp] theorem simulateQ_tl (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (xs : List prims.Y) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.tl prims.core pkSeed adrs xs :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      prims.Tl pkSeed adrs xs := by
  simp only [tl, simulateQ_HasQuery_query, impl]

@[simp] theorem simulateQ_hmsg (prims : Primitives p) (r : prims.Y)
    (pkSeed : prims.PkSeed) (pkRoot : prims.Y) (msg : List Byte) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.hmsg prims.core r pkSeed pkRoot msg :
          OracleComp (publicHashSpec prims.core) (Bytes p.m)) =
      prims.Hmsg r pkSeed pkRoot msg := by
  simp only [hmsg, simulateQ_HasQuery_query, impl]

/-! ### Query-preserving morphisms

A `HasQuery.QueryHom` fixes every explicit query, hence each arity-specific public-hash wrapper.
These equations are the leaves of every `*M_natural` theorem over `publicHashSpec`. -/

/-- Query-preserving monad morphisms fix an explicit `F` query. -/
theorem f_natural (core : CorePrimitives p) {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (pkSeed : core.PkSeed) (adrs : Adrs) (x : core.Y) :
    F.toMonadHom (f core pkSeed adrs x) = f core pkSeed adrs x :=
  HasQuery.map_query F (PublicHashQuery.thash pkSeed (core.adrsToKey adrs) [x])

/-- Query-preserving monad morphisms fix an explicit `H` query. -/
theorem h_natural (core : CorePrimitives p) {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (pkSeed : core.PkSeed) (adrs : Adrs) (left right : core.Y) :
    F.toMonadHom (h core pkSeed adrs left right) = h core pkSeed adrs left right :=
  HasQuery.map_query F (PublicHashQuery.thash pkSeed (core.adrsToKey adrs) [left, right])

/-- Query-preserving monad morphisms fix an explicit `T_l` query. -/
theorem tl_natural (core : CorePrimitives p) {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (pkSeed : core.PkSeed) (adrs : Adrs) (xs : List core.Y) :
    F.toMonadHom (tl core pkSeed adrs xs) = tl core pkSeed adrs xs :=
  HasQuery.map_query F (PublicHashQuery.thash pkSeed (core.adrsToKey adrs) xs)

/-- Query-preserving monad morphisms fix an explicit `H_msg` query. -/
theorem hmsg_natural (core : CorePrimitives p) {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    F.toMonadHom (hmsg core r pkSeed pkRoot msg) = hmsg core r pkSeed pkRoot msg :=
  HasQuery.map_query F (PublicHashQuery.hmsg r pkSeed pkRoot msg)

/-! ### One-query budgets

Each wrapper is a single explicit query, so it has total query budget `1` in the free
public-hash program. These are the leaves of every structural `*M_isTotalQueryBound` theorem. -/

/-- An explicit `F` query is one public-hash query. -/
theorem f_isTotalQueryBound (core : CorePrimitives p) (pkSeed : core.PkSeed) (adrs : Adrs)
    (x : core.Y) :
    IsTotalQueryBound (f core pkSeed adrs x : OracleComp (publicHashSpec core) core.Y) 1 := by
  simp [f, IsTotalQueryBound]

/-- An explicit `H` query is one public-hash query. -/
theorem h_isTotalQueryBound (core : CorePrimitives p) (pkSeed : core.PkSeed) (adrs : Adrs)
    (left right : core.Y) :
    IsTotalQueryBound
      (h core pkSeed adrs left right : OracleComp (publicHashSpec core) core.Y) 1 := by
  simp [h, IsTotalQueryBound]

/-- An explicit `T_l` query is one public-hash query. -/
theorem tl_isTotalQueryBound (core : CorePrimitives p) (pkSeed : core.PkSeed) (adrs : Adrs)
    (xs : List core.Y) :
    IsTotalQueryBound (tl core pkSeed adrs xs : OracleComp (publicHashSpec core) core.Y) 1 := by
  simp [tl, IsTotalQueryBound]

/-- An explicit `H_msg` query is one public-hash query. -/
theorem hmsg_isTotalQueryBound (core : CorePrimitives p) (r : core.Y) (pkSeed : core.PkSeed)
    (pkRoot : core.Y) (msg : List Byte) :
    IsTotalQueryBound
      (hmsg core r pkSeed pkRoot msg : OracleComp (publicHashSpec core) (Bytes p.m)) 1 := by
  simp [hmsg, IsTotalQueryBound]

/-- The cache used by the lazy public random oracle. -/
abbrev Cache (core : CorePrimitives p) := (publicHashSpec core).QueryCache

/-- Lazy random-oracle interpretation of the tagged public hash syntax. -/
@[reducible] def randomOracle (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.Y] [SampleableType (Bytes p.m)] :
    QueryImpl (publicHashSpec core) (StateT (PublicHash.Cache core) ProbComp) := by
  letI : ∀ t : PublicHashQuery core.PkSeed core.AdrsKey core.Y,
      SampleableType ((publicHashSpec core).Range t) := fun t => by
    cases t <;> exact inferInstance
  exact (publicHashSpec core).randomOracle

end PublicHash

end SLHDSA
