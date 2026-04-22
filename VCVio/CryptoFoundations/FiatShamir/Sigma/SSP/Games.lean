/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.SSP.Packages
import VCVio.OracleComp.SimSemantics.Append

/-!
# Game packages for the SSP-style Fiat-Shamir EUF-CMA proof

The four "monolithic" SSP packages that take part in the EUF-CMA hop chain
of `.ignore/fs-ssp-plan.md` §4.3:

* `cmaReal` — the real CMA game. Imports `unifSpec`, exports `cmaSpec`. The
  signing oracle uses the actual Σ-protocol (`σ.commit` / Hash query / `σ.respond`).
  State: lazy random-oracle cache, lazy keypair, signed-message log.
* `cmaSim` — the simulated CMA game. Imports `unifSpec`, exports `cmaSpec`. The
  signing oracle uses the HVZK simulator and programs the random oracle to be
  consistent with the simulated transcript.
  State: programmable RO cache plus bad flag, lazy keypair, signed-message log.
* `nma` — the no-message-attack game. Imports `unifSpec`, exports `nmaSpec`.
  No signing oracle; only the random oracle, the programming channel (used
  internally by the CMA-to-NMA reduction), and the public-key oracle.
  State: programmable RO cache plus bad flag, lazy keypair.
* `cmaToNma` — the CMA-to-NMA reduction package. Imports `nmaSpec`, exports
  `cmaSpec`. Forwards `unifSpec`, `roSpec`, and `pkSpec` queries unchanged;
  re-implements `signSpec` queries by sampling the HVZK simulator transcript
  (via `unifSpec` from `nmaSpec`) and programming the random oracle (via
  `progSpec` from `nmaSpec`). State: signed-message log.

These are all written as monolithic packages rather than parallel composites
(`signReal.par roLazy.par keyGen` etc.) because the standard SSP `link` /
`par` operators do not by themselves expose internal imports as exports, and
the signing handler needs to share its lazy keypair with the public-key
oracle. The component packages in `Sigma/SSP/Packages.lean` document the
intended decomposition; the games here re-implement that structure inline.

The key game-hop bound in `Sigma/SSP/Hops.lean` then connects these packages:

* `H3`: `cmaReal.advantage cmaSim adv ≤ qS · ζ_zk + qS · (qS + qH) · β`
  (tight HVZK + collision via `Package.advantage_le_qSeps_plus_bad`).
* `H4`: `cmaSim.runProb adv = nma.runProb (cmaToNma.shiftLeft adv)`
  (program-equivalence via `run_link_left_ofStateless`-style reasoning).
* `H5`: bound the NMA game's forgery probability via the existing
  `Fork.replayForkingBound`.
-/

universe u

open OracleSpec OracleComp ProbComp VCVio.SSP

namespace FiatShamir.SSP

variable (M : Type) [DecidableEq M]
variable (Commit : Type) [DecidableEq Commit]
variable (Chal : Type) [SampleableType Chal]
variable {Stmt Wit : Type} {rel : Stmt → Wit → Bool}
variable {Resp PrvState : Type}

/-! ### Common state for `cmaReal` / `cmaSim`

Both games thread the same three pieces of bookkeeping (random-oracle cache,
lazily-sampled keypair, signed-message log) plus a top-level `Bool` bad flag
tracking programming-collision events. For `cmaReal` the bad flag is vacuously
`false` (real signing never programs the RO); for `cmaSim` the flag is set on
a cache-hit during simulator-driven programming.

Wrapping the common bookkeeping in `cmaInnerState` and the bad flag at the
top gives both packages the canonical SSP "identical-until-bad" shape
`σ × Bool`, which is the shape consumed by
`Package.advantage_le_expectedSCost_plus_probEvent_bad` in
`VCVio/SSP/IdenticalUntilBad.lean`. -/

/-- Common inner state for the real and simulated CMA games:
random-oracle cache, lazily-sampled keypair, signed-message log. -/
@[reducible] def cmaInnerState (M : Type) [DecidableEq M]
    (Commit : Type) [DecidableEq Commit] (Chal : Type) (Stmt Wit : Type) : Type :=
  (roSpec M Commit Chal).QueryCache × Option (Stmt × Wit) × List M

/-- Full SSP state for the real and simulated CMA games: the common inner
state plus a top-level `Bool` bad flag. -/
@[reducible] def cmaGameState (M : Type) [DecidableEq M]
    (Commit : Type) [DecidableEq Commit] (Chal : Type) (Stmt Wit : Type) : Type :=
  cmaInnerState M Commit Chal Stmt Wit × Bool

/-! ### Real CMA game: `cmaReal`

The real CMA game's state is `cmaInnerState × Bool`. The bad flag is vacuously
`false` (real signing samples fresh challenges and never programs the RO);
it is carried along only so the package state matches `cmaSim`'s and the
SSP identical-until-bad bridge applies uniformly to both sides.

Init starts the inner state empty and the bad flag `false`. The signing
handler runs the actual Σ-protocol transcript: commit, query Hash to derive
the FS challenge through the same RO cache as the adversary's direct Hash
queries, then respond.

The implementation is split along the sum
`cmaSpec = ((unifSpec + roSpec) + signSpec) + pkSpec` into three handlers
that match the three "kinds" of access the adversary has:

* `cmaRealUnifRoImpl` handles uniform sampling and hash queries, the
  queries the Fiat-Shamir `verify` routine itself issues (since
  `verify` lives in `OracleComp (unifSpec + roSpec)`).
* `cmaRealSignImpl` handles signing queries, internally hitting the same
  RO cache as `cmaRealUnifRoImpl`.
* `cmaRealPkImpl` handles the public-key oracle (lazy keypair sampling).

The two finer sub-handlers combine into the `(unifSpec + roSpec) + signSpec`
portion as `cmaRealSubImpl := cmaRealUnifRoImpl + cmaRealSignImpl`, and
the full `impl` is `cmaRealSubImpl + cmaRealPkImpl`. The bridge in
`Sigma/SSP/Bridge.lean` uses this double factoring to apply
`simulateQ_add_liftComp_left` twice: once to strip the lift of
`adv.main pk` through `+ pkSpec`, and again (for the `verify` call) to
strip the additional lift through `+ signSpec`. -/

/-- The `unifSpec + roSpec`-handling portion of `cmaReal.impl`. Uniform
queries return a fresh uniform sample and leave the state untouched; hash
queries hit the internal cache, resample on miss, and leave the rest of
the state untouched. -/
@[reducible] noncomputable def cmaRealUnifRoImpl (Stmt Wit : Type) :
    QueryImpl (unifSpec + roSpec M Commit Chal)
      (StateT (cmaGameState M Commit Chal Stmt Wit) (OracleComp unifSpec))
  | Sum.inl n => fun st => do
      let r ← (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
      pure (r, st)
  | Sum.inr mc => fun st =>
      match st.1.1 mc with
      | some r => pure (r, st)
      | none => do
          let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
          pure (r, (st.1.1.cacheQuery mc r, st.1.2), st.2)

/-- The `signSpec`-handling portion of `cmaReal.impl`. Runs the real
Σ-protocol signer (`σ.commit` / RO-derived challenge / `σ.respond`),
sharing the RO cache with `cmaRealUnifRoImpl` and appending the signed
message to the log. The bad flag is carried through unchanged. -/
@[reducible] noncomputable def cmaRealSignImpl
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl (signSpec M Commit Resp)
      (StateT (cmaGameState M Commit Chal Stmt Wit)
        (OracleComp unifSpec)) := fun msg st => do
  let (pk, sk, kp) ← match st.1.2.1 with
    | some (pk, sk) => (pure (pk, sk, some (pk, sk)) :
        OracleComp unifSpec (Stmt × Wit × Option (Stmt × Wit)))
    | none => do
        let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
        pure (pk, sk, some (pk, sk))
  let (c, prvSt) ← (liftM (σ.commit pk sk) :
    OracleComp unifSpec (Commit × PrvState))
  let (ch, cache') ← match st.1.1 (msg, c) with
    | some r => (pure (r, st.1.1) :
        OracleComp unifSpec (Chal × (roSpec M Commit Chal).QueryCache))
    | none => do
        let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
        pure (r, st.1.1.cacheQuery (msg, c) r)
  let π ← (liftM (σ.respond pk sk prvSt ch) :
    OracleComp unifSpec Resp)
  pure ((c, π), (cache', kp, st.1.2.2 ++ [msg]), st.2)

/-- The `(unifSpec + roSpec) + signSpec`-handling portion of `cmaReal.impl`,
obtained as the sum `cmaRealUnifRoImpl + cmaRealSignImpl`. -/
@[reducible] noncomputable def cmaRealSubImpl
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl ((unifSpec + roSpec M Commit Chal) + signSpec M Commit Resp)
      (StateT (cmaGameState M Commit Chal Stmt Wit)
        (OracleComp unifSpec)) :=
  cmaRealUnifRoImpl M Commit Chal Stmt Wit +
    cmaRealSignImpl M Commit Chal σ hr

/-- The `pkSpec`-handling portion of `cmaReal.impl`. -/
@[reducible] noncomputable def cmaRealPkImpl
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl (pkSpec Stmt)
      (StateT (cmaGameState M Commit Chal Stmt Wit)
        (OracleComp unifSpec)) := fun _ st =>
  match st.1.2.1 with
  | some (pk, _) => pure (pk, st)
  | none => do
      let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
      pure (pk, (st.1.1, some (pk, sk), st.1.2.2), st.2)

@[reducible] noncomputable def cmaReal
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    Package unifSpec (cmaSpec M Commit Chal Resp Stmt)
      (cmaGameState M Commit Chal Stmt Wit) where
  init := pure ((∅, none, []), false)
  impl := cmaRealSubImpl M Commit Chal σ hr + cmaRealPkImpl M Commit Chal hr

/-! ### Simulated CMA game: `cmaSim`

The simulated CMA game's state is `cmaInnerState × Bool` (same shape as
`cmaReal`): cache, lazily-sampled keypair, signed-message log, and a
top-level bad flag. The bad flag tracks programming-collision events: it
is set to `true` whenever the simulator-driven handler attempts to program
`(m, c) ↦ ch` into the RO cache but `(m, c)` is already cached (with a
possibly-different value). On the `coincide` / cache-miss branch the flag
stays `false`, and the cache is programmed with the simulator's `ch`.

Init starts everything empty and `false`. The signing handler samples a
full HVZK transcript `(c, ch, π) ← simT pk` and programs the RO so that
`Hash (m, c) = ch`; if `(m, c)` was already cached the bad flag is set
(this is the only source of distributional disagreement with `cmaReal`
beyond the per-step HVZK gap on the transcript triple). -/

@[reducible] noncomputable def cmaSim
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    Package unifSpec (cmaSpec M Commit Chal Resp Stmt)
      (cmaGameState M Commit Chal Stmt Wit) where
  init := pure ((∅, none, []), false)
  impl
    | Sum.inl (Sum.inl (Sum.inl n)) => fun st => do
        let r ← (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
        pure (r, st)
    | Sum.inl (Sum.inl (Sum.inr mc)) => fun st =>
        match st.1.1 mc with
        | some r => pure (r, st)
        | none => do
            let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
            pure (r, (st.1.1.cacheQuery mc r, st.1.2), st.2)
    | Sum.inl (Sum.inr m) => fun st => do
        let (pk, kp) ← match st.1.2.1 with
          | some (pk, sk) => (pure (pk, some (pk, sk)) :
              OracleComp unifSpec (Stmt × Option (Stmt × Wit)))
          | none => do
              let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
              pure (pk, some (pk, sk))
        let (c, ch, π) ← (liftM (simT pk) :
          OracleComp unifSpec (Commit × Chal × Resp))
        let (cache', bad') := match st.1.1 (m, c) with
          | some _ => (st.1.1, true)
          | none => (st.1.1.cacheQuery (m, c) ch, st.2)
        pure ((c, π), (cache', kp, st.1.2.2 ++ [m]), bad')
    | Sum.inr () => fun st =>
        match st.1.2.1 with
        | some (pk, _) => pure (pk, st)
        | none => do
            let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
            pure (pk, (st.1.1, some (pk, sk), st.1.2.2), st.2)

/-! ### NMA game: `nma`

The NMA game exposes the random oracle, the programming channel (used
internally by `cmaToNma`), and the public-key oracle. There is no signing
oracle; the external NMA adversary in the H5 forking-lemma bridge interacts
with this game through the `unifSpec + roSpec + pkSpec` sub-portion of
`nmaSpec` only.

State: `(cache × Bool) × Option (Stmt × Wit)`. The `Bool` is the
programming-collision flag; it is touched only by `progSpec` queries and is
the source of the `qS · (qS + qH) · β` collision term in the H3 / H4 bound. -/

@[reducible] noncomputable def nma
    (hr : GenerableRelation Stmt Wit rel) :
    Package unifSpec (nmaSpec M Commit Chal Stmt)
      ((roSpec M Commit Chal).QueryCache × Bool × Option (Stmt × Wit)) where
  init := pure (∅, false, none)
  impl
    | Sum.inl (Sum.inl (Sum.inl n)) => fun st => do
        let r ← (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
        pure (r, st)
    | Sum.inl (Sum.inl (Sum.inr mc)) => fun st =>
        match st.1 mc with
        | some r => pure (r, st)
        | none => do
            let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
            pure (r, st.1.cacheQuery mc r, st.2)
    | Sum.inl (Sum.inr mch) => fun st =>
        let mc : M × Commit := (mch.1, mch.2.1)
        let ch : Chal := mch.2.2
        match st.1 mc with
        | some _ => pure ((), st.1, true, st.2.2)
        | none => pure ((), st.1.cacheQuery mc ch, st.2)
    | Sum.inr () => fun st =>
        match st.2.2 with
        | some (pk, _) => pure (pk, st)
        | none => do
            let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
            pure (pk, st.1, st.2.1, some (pk, sk))

/-! ### CMA-to-NMA reduction: `cmaToNma`

The reduction package that turns the CMA adversary's interface (`cmaSpec`)
into a sequence of queries to the NMA game's interface (`nmaSpec`). The
reduction is parameterized by the same HVZK simulator as `cmaSim`: on a
`Sign m` query, it samples a full transcript `(c, ch, π) ← simT pk` and
installs the FS challenge into the random oracle by issuing a `progSpec`
query, then returns `(c, π)`. All other CMA queries (uniform sampling,
random-oracle Hash, public-key GetPK) are forwarded straight to the
corresponding `nmaSpec` channel.

State: `List M`, the running list of signed messages. The freshness
post-check in `Sigma/SSP/Bridge.lean` reads this log out via `runState`.

The reduction is *stateful only* in the trivial sense of accumulating the
log; the random-oracle cache and the keypair both live inside the underlying
NMA game (`nma`), so re-using `cmaToNma` against different `nma` instances
just re-uses the existing `nma` state through `link`. -/

@[reducible] noncomputable def cmaToNma
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    Package (nmaSpec M Commit Chal Stmt) (cmaSpec M Commit Chal Resp Stmt) (List M) where
  init := pure []
  impl
    | Sum.inl (Sum.inl (Sum.inl n)) => fun log => do
        let r ← (((nmaSpec M Commit Chal Stmt).query (Sum.inl (Sum.inl (Sum.inl n)))) :
          OracleComp (nmaSpec M Commit Chal Stmt) (Fin (n + 1)))
        pure (r, log)
    | Sum.inl (Sum.inl (Sum.inr mc)) => fun log => do
        let r ← (((nmaSpec M Commit Chal Stmt).query (Sum.inl (Sum.inl (Sum.inr mc)))) :
          OracleComp (nmaSpec M Commit Chal Stmt) Chal)
        pure (r, log)
    | Sum.inl (Sum.inr m) => fun log => do
        let pk ← (((nmaSpec M Commit Chal Stmt).query (Sum.inr ())) :
          OracleComp (nmaSpec M Commit Chal Stmt) Stmt)
        let (c, ch, π) ← (liftM (simT pk) :
          OracleComp (nmaSpec M Commit Chal Stmt) (Commit × Chal × Resp))
        let _ ← (((nmaSpec M Commit Chal Stmt).query (Sum.inl (Sum.inr (m, c, ch)))) :
          OracleComp (nmaSpec M Commit Chal Stmt) Unit)
        pure ((c, π), log ++ [m])
    | Sum.inr () => fun log => do
        let pk ← (((nmaSpec M Commit Chal Stmt).query (Sum.inr ())) :
          OracleComp (nmaSpec M Commit Chal Stmt) Stmt)
        pure (pk, log)

end FiatShamir.SSP
