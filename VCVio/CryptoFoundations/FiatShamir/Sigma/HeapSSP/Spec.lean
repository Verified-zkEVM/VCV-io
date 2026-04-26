/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.OracleSpec

/-!
# Oracle interfaces for the HeapSSP Fiat-Shamir proof

The oracle interfaces (`OracleSpec`s) used by the HeapSSP reformulation of
the Fiat-Shamir Sigma-protocol EUF-CMA proof. State ownership is deliberately
kept out of this file; see
`VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.CmaState` for the package
cell directories and record-style projections.

The combined interfaces mirror `Sigma/CmaToNma.lean`:

* `roSpec M Commit Chal` is the random-oracle interface `(M × Commit) →ₒ Chal`.
* `signSpec M Commit Resp` is the signing interface `M →ₒ (Commit × Resp)`.
* `pkSpec Stmt` is a public-key oracle `Unit →ₒ Stmt`.
* `progSpec M Commit Chal` is the simulator's private programming interface.
* `cmaSpec M Commit Chal Resp Stmt` is the CMA adversary view.
* `nmaSpec M Commit Chal Stmt` is the managed-RO NMA view.
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

end FiatShamir.HeapSSP
