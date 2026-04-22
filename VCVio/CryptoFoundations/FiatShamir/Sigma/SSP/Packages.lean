/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.SSP.Spec
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.Coercions.Add
import VCVio.SSP.Package

/-!
# Component packages for the SSP-style Fiat-Shamir EUF-CMA proof

This file packages each "atomic" piece of the EUF-CMA experiment into its
own SSP `Package`, following the plan in `.ignore/fs-ssp-plan.md` §4.2.
The full game packages (`cmaReal`, `cmaSim`, `nma`, `cmaToNma`) are then
defined in `Sigma/SSP/Games.lean`. They monolithically combine the
structure exposed here, since the standard SSP `link`/`par` operators do
not by themselves expose internal imports as exports.

The components live here primarily for documentation and to enable reuse
in future hash-and-sign EUF-CMA proofs (Falcon-GPV, MLDSA-Sig, …) which
share the same component shapes.

## Components

* `roLazy` — lazy random oracle. Caches Hash queries on first access; on a
  miss, samples uniformly from `Chal` and writes the new entry. State:
  `QueryCache (roSpec M Commit Chal)`.
* `roProg` — programmable random oracle with a per-package collision flag.
  Hash queries behave like `roLazy`; `Program (m, c, ch)` queries write
  the entry, raising the flag if `(m, c)` was already cached. State:
  `QueryCache (roSpec M Commit Chal) × Bool` (the right component is the
  bad flag, in the canonical SSP shape `σ × Bool`).
* `keyGen` — lazy keypair generator. Samples `(pk, sk) ← hr.gen` on the
  first `GetPK` query and caches both halves; only the public part is
  returned to callers. State: `Option (Stmt × Wit)`.
* `signReal` — real Σ-protocol signer, parameterized by a fixed keypair
  `(pk, sk)`. On `Sign m`: commit, query `Hash (m, c)`, respond. Tracks
  the signed-message log in state. Imports `roSpec`, exports `signSpec`.
* `signSim` — simulator-based signer, parameterized by a fixed `pk` and
  the HVZK transcript simulator. On `Sign m`: sample
  `(c, ch, π) ← simT pk`, program `Hash (m, c) := ch`, return `(c, π)`.
  Imports `roSpec + progSpec` (programs through `progSpec`); exports
  `signSpec`.

The keypair is intentionally passed to `signReal`/`signSim` as a direct
parameter rather than as an oracle import, so each game package
(`Games.lean`) can sample the keypair once at start-of-game and share it
between the signer and the public-key oracle without forcing a
non-existent "passthrough" composition operator.
-/

universe u

open OracleSpec OracleComp ProbComp VCVio.SSP

namespace FiatShamir.SSP

/-! ### Random-oracle packages -/

variable (M : Type) [DecidableEq M]
variable (Commit : Type) [DecidableEq Commit]
variable (Chal : Type) [SampleableType Chal]

/-- Lazy random oracle, packaged as a stateful SSP `Package`.

`init` starts with an empty cache. The handler is the standard
`OracleSpec.randomOracle`: cache-hits return the stored value; cache-misses
sample uniformly from `Chal` and write the result. -/
@[reducible] noncomputable def roLazy :
    Package unifSpec (roSpec M Commit Chal)
      ((roSpec M Commit Chal).QueryCache) where
  init := pure ∅
  impl := randomOracle

/-- Programmable random oracle with bad-on-collision flag.

The state is `cache × bad`, in the canonical SSP "package state +
bad-flag" shape used by `Package.advantage_le_qSeps_plus_probEvent_bad`.

* `Hash (m, c)`: behaves exactly as `roLazy` — return cached value on hit;
  sample fresh on miss and write the entry. Does not touch the bad flag.
* `Program (m, c, ch)`: if `cache (m, c) = some _`, set `bad := true`
  (the simulator wanted to install `ch` at a point that was already
  determined; this is the source of the FS programming-collision bound).
  If `cache (m, c) = none`, write the entry `(m, c) ↦ ch`. -/
@[reducible] noncomputable def roProg :
    Package unifSpec (roSpec M Commit Chal + progSpec M Commit Chal)
      ((roSpec M Commit Chal).QueryCache × Bool) where
  init := pure (∅, false)
  impl
    | Sum.inl mc => fun st =>
        match st.1 mc with
        | some r => pure (r, st)
        | none => do
            let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
            pure (r, st.1.cacheQuery mc r, st.2)
    | Sum.inr mch => fun st =>
        let mc : M × Commit := (mch.1, mch.2.1)
        let ch : Chal := mch.2.2
        match st.1 mc with
        | some _ => pure ((), st.1, true)
        | none => pure ((), st.1.cacheQuery mc ch, st.2)

/-! ### Key-generation package -/

variable {Stmt Wit : Type} {rel : Stmt → Wit → Bool}

/-- Lazy keypair generator. Samples `(pk, sk) ← hr.gen` on the first
`GetPK` query and caches both halves; subsequent calls return the cached
public key. The secret key never leaves the package state.

In the SSP games of `Games.lean`, the keypair is held inside the larger
game-state record and the secret key is read out by the signing handler.
This standalone `keyGen` package serves as the conceptual building block
and is the right shape for an `nma`-style game where no signer needs the
secret key. -/
@[reducible] noncomputable def keyGen
    (hr : GenerableRelation Stmt Wit rel) :
    Package unifSpec (pkSpec Stmt) (Option (Stmt × Wit)) where
  init := pure none
  impl _ := fun st =>
    match st with
    | some (pk, sk) => pure (pk, some (pk, sk))
    | none => do
        let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
        pure (pk, some (pk, sk))

/-! ### Signing-oracle packages -/

variable {Resp PrvState : Type}

/-- Real Σ-protocol signer at a fixed keypair `(pk, sk)`.

On `Sign m`:
* sample a commitment `(c, prvSt) ← σ.commit pk sk`;
* query the random oracle for the FS challenge `ch ← Hash (m, c)`;
* respond `π ← σ.respond pk sk prvSt ch` and return `(c, π)`.

Tracks the list of signed messages in state for the freshness post-check
in `Sigma/SSP/Bridge.lean`.

Imports `unifSpec + roSpec`: `unifSpec` provides the randomness needed by
`σ.commit` / `σ.respond` (which are `ProbComp`-valued); `roSpec` exposes
the random oracle used to derive the FS challenge. -/
@[reducible] noncomputable def signReal
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (sk : Wit) :
    Package (unifSpec + roSpec M Commit Chal)
      (signSpec M Commit Resp) (List M) where
  init := pure []
  impl m := fun log => do
    let (c, prvSt) ← (liftM (σ.commit pk sk) :
      OracleComp (unifSpec + roSpec M Commit Chal) (Commit × PrvState))
    let ch ← (((unifSpec + roSpec M Commit Chal).query (Sum.inr (m, c))) :
      OracleComp (unifSpec + roSpec M Commit Chal) Chal)
    let π ← (liftM (σ.respond pk sk prvSt ch) :
      OracleComp (unifSpec + roSpec M Commit Chal) Resp)
    pure ((c, π), m :: log)

/-- Simulator-based signer at a fixed `pk`, parameterized by the HVZK
transcript simulator.

On `Sign m`:
* sample a full transcript `(c, ch, π) ← simT pk`;
* program the random oracle so that `Hash (m, c) = ch` via a
  `progSpec` query;
* return `(c, π)`.

Imports `unifSpec + (roSpec + progSpec)`: `unifSpec` provides randomness
for the simulator transcript; the right summand exposes both the read
side (`roSpec`) and the write side (`progSpec`) of the programmable RO,
matching the exports of `roProg`. The `roSpec` import is unused by the
signer body itself but is kept in the spec so that future composition
with `roProg` lines up exactly. -/
@[reducible] noncomputable def signSim
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    Package (unifSpec + (roSpec M Commit Chal + progSpec M Commit Chal))
      (signSpec M Commit Resp) (List M) where
  init := pure []
  impl m := fun log => do
    let (c, ch, π) ← (liftM (simT pk) :
      OracleComp (unifSpec + (roSpec M Commit Chal + progSpec M Commit Chal))
        (Commit × Chal × Resp))
    let _ ← (((unifSpec +
        (roSpec M Commit Chal + progSpec M Commit Chal)).query
        (Sum.inr (Sum.inr (m, c, ch)))) :
      OracleComp (unifSpec + (roSpec M Commit Chal + progSpec M Commit Chal)) Unit)
    pure ((c, π), m :: log)

end FiatShamir.SSP
