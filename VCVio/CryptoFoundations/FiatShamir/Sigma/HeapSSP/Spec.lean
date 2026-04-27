/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.OracleSpec
import VCVio.OracleComp.QueryTracking.Structures
import ToMathlib.Data.Heap

/-!
# Oracle interfaces and heap-cell directories for the HeapSSP Fiat-Shamir proof

The oracle interfaces (`OracleSpec`s) and heap-cell identifier sets
(`CellSpec`) that the HeapSSP reformulation of the Fiat-Shamir Σ-protocol
EUF-CMA proof is typed against. Every game, component package, and
reduction adversary in `Sigma/HeapSSP/*` exports/imports along one of the
oracle specs defined here and owns one of the cell directories defined
here.

## Oracle specs

Mirrors `Sigma/CmaToNma.lean`: five single-oracle specs plus two combined
adversary-facing parallel sums.

* `roSpec M Commit Chal` — random-oracle interface: `(M × Commit) →ₒ Chal`.
* `signSpec M Commit Resp` — signing-oracle interface:
  `M →ₒ (Commit × Resp)`.
* `pkSpec Stmt` — public-key interface: `Unit →ₒ Stmt`.
* `progSpec M Commit Chal` — programming interface, used internally by
  the programmable-RO package between the Σ-simulator and the cache:
  `(M × Commit × Chal) →ₒ Unit`.
* `cmaSpec M Commit Chal Resp Stmt` — CMA adversary's view, the parallel
  sum `unifSpec + roSpec + signSpec + pkSpec`.
* `nmaSpec M Commit Chal Stmt` — NMA adversary's view, the parallel sum
  `unifSpec + roSpec + progSpec + pkSpec`.

## Heap-cell directories

The HeapSSP restructure expresses game state as `Heap Ident` for an
identifier set `Ident`. For Fiat-Shamir we take:

* `OuterCell M` (singleton) — owns the signed-message log `List M`.
* `InnerCell M Commit Chal Stmt Wit` — owns the three "inner" cells:
    - `.roCache` : `(roSpec M Commit Chal).QueryCache`
    - `.keypair` : `Option (Stmt × Wit)`
    - `.bad`     : `Bool`
* `CmaCells M Commit Chal Stmt Wit := OuterCell M ⊕ InnerCell …` — the
  composite directory shared by `cmaReal` (monolithic) and
  `cmaSim := cmaToNma.link nma` (link-composite), see
  `VCVio/CryptoFoundations/FiatShamir/Sigma/HeapSSP/Games.lean`.

The designated `bad` flag is `InnerCell.bad`; the bridge bijection in
`Hops.lean` reads it out via `Heap.get (.inr .bad)`.
-/

open OracleSpec

namespace FiatShamir.HeapSSP

/-! ### Single-oracle specs -/

/-- Random-oracle interface for the Fiat-Shamir transform. -/
@[reducible] def roSpec (M Commit Chal : Type) : OracleSpec (M × Commit) :=
  (M × Commit) →ₒ Chal

/-- Signing-oracle interface presented to the CMA adversary. -/
@[reducible] def signSpec (M Commit Resp : Type) : OracleSpec M :=
  M →ₒ (Commit × Resp)

/-- Public-key oracle interface: a single `GetPK` query returning the
challenger's public key. -/
@[reducible] def pkSpec (Stmt : Type) : OracleSpec Unit :=
  Unit →ₒ Stmt

/-- Programming interface for the programmable random oracle. Private to
the simulator side of the CMA-to-NMA reduction. -/
@[reducible] def progSpec (M Commit Chal : Type) : OracleSpec (M × Commit × Chal) :=
  (M × Commit × Chal) →ₒ Unit

/-! ### Combined adversary-facing specs -/

/-- The CMA adversary's complete oracle view: uniform sampling, RO,
signing, and public-key oracles. Order:
`unifSpec + roSpec + signSpec + pkSpec`. -/
@[reducible] def cmaSpec (M Commit Chal Resp Stmt : Type) :
    OracleSpec (((ℕ ⊕ M × Commit) ⊕ M) ⊕ Unit) :=
  unifSpec + roSpec M Commit Chal + signSpec M Commit Resp + pkSpec Stmt

/-- The NMA-game oracle interface used internally by the HeapSSP-level
CMA-to-NMA reduction. Includes `unifSpec`, `roSpec`, `progSpec`, and
`pkSpec`. Order: `unifSpec + roSpec + progSpec + pkSpec`. -/
@[reducible] def nmaSpec (M Commit Chal Stmt : Type) :
    OracleSpec (((ℕ ⊕ M × Commit) ⊕ M × Commit × Chal) ⊕ Unit) :=
  unifSpec + roSpec M Commit Chal + progSpec M Commit Chal + pkSpec Stmt

/-! ### Heap-cell directories

`OuterCell M` and `InnerCell M Commit Chal Stmt Wit` are phantom-typed by
the underlying payload's type parameters, so that their `CellSpec`
instances can reference those parameters without requiring `section
variable`-indirection at every use site. -/

/-- Outer cell directory for `cmaToNma` (and for the outer half of
`cmaReal`): a single `log` cell holding the signed-message list.

The `M` parameter is phantom: it pins down the `CellSpec` instance
below, but the constructor itself carries no data. The explicit
`DecidableEq` instance side-steps typeclass-synthesis timeouts that the
machine-generated `deriving` instance would otherwise induce when
`Heap.update` is called on the composite cell directory `CmaCells`. -/
inductive OuterCell (M : Type) where
  | log

instance (M : Type) : DecidableEq (OuterCell M) := fun a b =>
  match a, b with
  | .log, .log => .isTrue rfl

instance (M : Type) : CellSpec.{0, 0} (OuterCell M) where
  type
    | .log => List M
  default
    | .log => []

/-- Inner cell directory for `nma` (and for the inner half of `cmaReal`):
RO cache, optional keypair, and a Boolean bad flag.

As with `OuterCell`, the type parameters are phantom and the
`DecidableEq` instance is supplied explicitly to keep typeclass
synthesis lightweight on the composite cell directory `CmaCells`. -/
inductive InnerCell (M Commit Chal Stmt Wit : Type) where
  | roCache
  | keypair
  | bad

instance (M Commit Chal Stmt Wit : Type) :
    DecidableEq (InnerCell M Commit Chal Stmt Wit) := fun a b =>
  match a, b with
  | .roCache, .roCache => .isTrue rfl
  | .keypair, .keypair => .isTrue rfl
  | .bad,     .bad     => .isTrue rfl
  | .roCache, .keypair => .isFalse (fun h => by cases h)
  | .roCache, .bad     => .isFalse (fun h => by cases h)
  | .keypair, .roCache => .isFalse (fun h => by cases h)
  | .keypair, .bad     => .isFalse (fun h => by cases h)
  | .bad,     .roCache => .isFalse (fun h => by cases h)
  | .bad,     .keypair => .isFalse (fun h => by cases h)

instance (M Commit Chal Stmt Wit : Type) :
    CellSpec.{0, 0} (InnerCell M Commit Chal Stmt Wit) where
  type
    | .roCache => (roSpec M Commit Chal).QueryCache
    | .keypair => Option (Stmt × Wit)
    | .bad => Bool
  default
    | .roCache => ∅
    | .keypair => none
    | .bad => false

/-- Composite cell directory for `cmaReal` (monolithic) and
`cmaSim := cmaToNma.link nma` (link-composite). By construction of
`Package.link`, the two shapes have state type `Heap (CmaCells …)`
verbatim, so H4 (`cmaSim = cmaToNma.link nma`) is *definitionally* true.
-/
abbrev CmaCells (M Commit Chal Stmt Wit : Type) : Type :=
  OuterCell M ⊕ InnerCell M Commit Chal Stmt Wit

end FiatShamir.HeapSSP
