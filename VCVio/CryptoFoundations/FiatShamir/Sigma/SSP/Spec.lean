/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.OracleSpec

/-!
# Oracle interfaces for the SSP-style Fiat-Shamir EUF-CMA proof

The oracle interfaces (`OracleSpec`s) used by the State-Separating Proofs
(SSP) reformulation of the Fiat-Shamir Σ-protocol EUF-CMA proof. Every game,
component package, and reduction adversary in `Sigma/SSP/*` types its imports
or exports against one of the specs defined here.

The naming follows the Lean / Mathlib convention `xSpec` and matches existing
specs in `VCVio` (`unifSpec`, `coinSpec`, `lrSpec`, `dhSpec`, …).

## Specs

* `roSpec M Commit Chal` — random-oracle interface: `(M × Commit) →ₒ Chal`.
* `signSpec M Commit Resp` — signing-oracle interface: `M →ₒ (Commit × Resp)`.
* `pkSpec Stmt` — key-distribution interface: `Unit →ₒ Stmt`.
* `progSpec M Commit Chal` — programming interface, used internally by the
  programmable-RO package between the Σ-simulator and the cache:
  `(M × Commit × Chal) →ₒ Unit`.
* `cmaSpec M Commit Chal Resp Stmt` — CMA adversary's view, the parallel sum
  `roSpec + signSpec + pkSpec`.
* `nmaSpec M Commit Chal Stmt` — NMA adversary's view, the parallel sum
  `roSpec + pkSpec` (no signing oracle).

The CMA-to-NMA reduction is then a `Package nmaSpec cmaSpec PUnit` (no state)
that forwards `roSpec` and `pkSpec` queries unchanged and re-implements
`signSpec` queries by inlining the HVZK simulator.
-/

universe u

open OracleSpec

namespace FiatShamir.SSP

/-! ### Single-oracle specs -/

/-- Random-oracle interface for the Fiat-Shamir transform.

The oracle is indexed by `(message, commitment)` pairs; each query returns a
challenge in `Chal`. This is the same interface as the implicit RO carried by
`FiatShamir.runtime`; the SSP packages just expose it as a first-class spec
instead of embedding it in the runtime monad. -/
@[reducible] def roSpec (M Commit Chal : Type) : OracleSpec (M × Commit) :=
  (M × Commit) →ₒ Chal

/-- Signing-oracle interface presented to the CMA adversary.

The adversary calls `Sign m` and receives the full FS signature
`(commitment, response) : Commit × Resp`. The freshness post-check (whether
`m` was previously signed) is applied externally to the adversary's output;
see `Sigma/SSP/Bridge.lean`. -/
@[reducible] def signSpec (M Commit Resp : Type) : OracleSpec M :=
  M →ₒ (Commit × Resp)

/-- Public-key oracle interface: a single `GetPK` query that returns the
challenger's public key.

Lazily-sampled keypair is held in the `keyGen` package's state; the secret
key never leaves the package. -/
@[reducible] def pkSpec (Stmt : Type) : OracleSpec Unit :=
  Unit →ₒ Stmt

/-- Programming interface for the programmable random oracle.

A `Program (m, c, ch)` query asks the RO package to commit its answer at the
hash point `(m, c)` to the value `ch`; if the point is already cached with a
different value the package raises its `bad` flag. This interface is private
to the simulator-side of the CMA-to-NMA reduction and is **not** exposed to
the adversary. -/
@[reducible] def progSpec (M Commit Chal : Type) : OracleSpec (M × Commit × Chal) :=
  (M × Commit × Chal) →ₒ Unit

/-! ### Combined adversary-facing specs -/

/-- The CMA adversary's complete oracle view: random-oracle queries on
`(M × Commit) →ₒ Chal`, signing-oracle queries on `M →ₒ (Commit × Resp)`, and
the public-key oracle on `Unit →ₒ Stmt`.

The order `roSpec + signSpec + pkSpec` is fixed for the rest of the SSP
hops; the CMA-to-NMA reduction's stateless package
(`Sigma/SSP/Games.lean::cmaToNma`) is typed to convert from `nmaSpec` (which
omits `signSpec`) to this spec by re-implementing the middle component. -/
@[reducible] def cmaSpec (M Commit Chal Resp Stmt : Type) :
    OracleSpec ((M × Commit ⊕ M) ⊕ Unit) :=
  roSpec M Commit Chal + signSpec M Commit Resp + pkSpec Stmt

/-- The NMA adversary's complete oracle view: random-oracle queries on
`(M × Commit) →ₒ Chal` and the public-key oracle on `Unit →ₒ Stmt`. There is
no signing oracle.

Used as the export interface of the `nma` game package and as the import
interface of the CMA-to-NMA reduction. -/
@[reducible] def nmaSpec (M Commit Chal Stmt : Type) :
    OracleSpec ((M × Commit) ⊕ Unit) :=
  roSpec M Commit Chal + pkSpec Stmt

end FiatShamir.SSP
