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
* `pkSpec Stmt` — public-key interface: `Unit →ₒ Stmt`.
* `progSpec M Commit Chal` — programming interface, used internally by the
  programmable-RO package between the Σ-simulator and the cache:
  `(M × Commit × Chal) →ₒ Unit`.
* `cmaSpec M Commit Chal Resp Stmt` — CMA adversary's view, the parallel sum
  `unifSpec + roSpec + signSpec + pkSpec`. Includes `unifSpec` so that the
  external `unforgeableAdv`'s `OracleComp (unifSpec + roSpec + signSpec)` lifts
  cleanly into `OracleComp cmaSpec` via `SubSpec`.
* `nmaSpec M Commit Chal Stmt` — NMA adversary's view, the parallel sum
  `unifSpec + roSpec + progSpec + pkSpec`. Includes `unifSpec` so that the
  CMA-to-NMA reduction can sample the HVZK simulator transcript, and `progSpec`
  so the reduction can program the random oracle. The external NMA adversary
  (used in the H5 forking-lemma bridge) uses only the `unifSpec + roSpec + pkSpec`
  sub-portion; `progSpec` is an internal channel between the reduction and the
  programmable-RO game.

The CMA-to-NMA reduction is then a `Package nmaSpec cmaSpec _` (with a small
shadow-cache state) that forwards `unifSpec`, `roSpec`, and `pkSpec` queries
unchanged and re-implements `signSpec` queries by inlining the HVZK simulator,
using `progSpec` to install the simulator's challenge into the random oracle.
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

/-- The CMA adversary's complete oracle view: uniform sampling, random-oracle
queries on `(M × Commit) →ₒ Chal`, signing-oracle queries on `M →ₒ (Commit × Resp)`,
and the public-key oracle on `Unit →ₒ Stmt`.

The order `unifSpec + roSpec + signSpec + pkSpec` is fixed for the rest of the
SSP hops. The bridge layer in `Sigma/SSP/Bridge.lean` lifts the existing
`unforgeableAdv` (which queries `unifSpec + roSpec + signSpec`) into this spec
by initializing the public-key channel from the lazily-sampled keypair. -/
@[reducible] def cmaSpec (M Commit Chal Resp Stmt : Type) :
    OracleSpec (((ℕ ⊕ M × Commit) ⊕ M) ⊕ Unit) :=
  unifSpec + roSpec M Commit Chal + signSpec M Commit Resp + pkSpec Stmt

/-- The NMA-game oracle interface used internally by the SSP-level CMA-to-NMA
reduction. Includes `unifSpec` (so the reduction can sample the HVZK simulator
transcript), the random-oracle channel `roSpec`, the programming channel
`progSpec` (so the reduction can install the simulator's challenge into the
RO), and the public-key channel `pkSpec`.

The external NMA adversary used by the forking-lemma bridge sees only the
`unifSpec + roSpec + pkSpec` sub-portion of this spec; `progSpec` is private
to the simulator-side of the reduction and never exposed to a real NMA
adversary. The split is enforced at the `Sigma/SSP/Hops.lean::H5` boundary
where the external NMA adversary is wrapped into an `OracleComp nmaSpec` that
simply never queries the `progSpec` summand. -/
@[reducible] def nmaSpec (M Commit Chal Stmt : Type) :
    OracleSpec (((ℕ ⊕ M × Commit) ⊕ M × Commit × Chal) ⊕ Unit) :=
  unifSpec + roSpec M Commit Chal + progSpec M Commit Chal + pkSpec Stmt

end FiatShamir.SSP
