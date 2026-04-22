/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.SSP.Spec
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT
import VCVio.SSP.Package

/-!
# Game packages for the SSP-style Fiat-Shamir EUF-CMA proof

The four SSP packages that take part in the EUF-CMA hop chain of
`.ignore/fs-ssp-plan.md` §4.3:

* `cmaReal` — the real CMA game. Imports `unifSpec`, exports `cmaSpec`. The
  signing oracle runs the actual Σ-protocol (`σ.commit` / Hash query / `σ.respond`).
  State: `cmaInnerState × Bool` where the `Bool` is vacuously `false`
  (real signing never programs the RO).
* `cmaSim` — the simulated CMA game. Imports `unifSpec`, exports `cmaSpec`. The
  signing oracle uses the HVZK simulator and programs the random oracle to be
  consistent with the simulated transcript; the bad flag fires on programming
  collisions.
  State: `cmaInnerState × Bool`, same shape as `cmaReal`.
* `nma` — the no-message-attack game. Imports `unifSpec`, exports `nmaSpec`.
  No signing oracle; only the random oracle, the programming channel (used
  internally by the CMA-to-NMA reduction), and the public-key oracle.
* `cmaToNma` — the CMA-to-NMA reduction package. Imports `nmaSpec`, exports
  `cmaSpec`. Forwards non-signing queries and re-implements `signSpec` via
  `simT` + `progSpec`.

## Composition structure

The `cmaReal` / `cmaSim` games are built from four *atomic* sub-handlers on
`cmaInnerState` (no bad flag):

* `unifRoInnerImpl` — uniform sampling + lazy random oracle
* `signRealInnerImpl` — real Σ-protocol signer
* `signSimInnerImpl` — HVZK-simulator-based signer (conditional cache programming)
* `pkInnerImpl` — lazy public-key generator

The bad flag is attached by the generic combinators `QueryImpl.withBadFlag`
(preserves the flag) and `QueryImpl.withBadUpdate` (OR-updates with a
predicate), both defined in `VCVio/OracleComp/SimSemantics/StateT.lean`.
The programming-collision predicate `progCollision` fires exactly on the
`cmaSim` sign branch when `(m, c)` is already cached. Putting it together:

* `cmaReal.impl = (unifRoInnerImpl.withBadFlag + signRealInnerImpl.withBadFlag)
                  + pkInnerImpl.withBadFlag`
* `cmaSim.impl  = (unifRoInnerImpl.withBadFlag
                    + signSimInnerImpl.withBadUpdate progCollision)
                  + pkInnerImpl.withBadFlag`

This factoring makes the SSP identical-until-bad hypotheses
(`h_step_eq_nS`, `h_mono₀`) hold by a generic argument on `withBadFlag`/
`withBadUpdate` alone, rather than by case-splitting through every query
branch.

The key game-hops in `Sigma/SSP/Hops.lean` connect these packages:

* `H3`: `cmaReal.advantage cmaSim adv ≤ qS · ζ_zk + qS · (qS + qH) · β`,
  via `Package.advantage_le_expectedSCost_plus_probEvent_bad` at
  `G₀ = cmaReal`, `G₁ = cmaSim`.
* `H4`: `cmaSim.runProb adv = nma.runProb (cmaToNma.shiftLeft adv)`
  (program-equivalence).
* `H5`: bound the NMA forgery probability via `Fork.replayForkingBound`.
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
lazily-sampled keypair, signed-message log) plus a top-level `Bool` bad flag.
For `cmaReal` the bad flag is vacuously `false` (real signing never programs
the RO); for `cmaSim` the flag is set on a cache-hit during simulator-driven
programming.

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

/-! ### Atomic inner handlers on `cmaInnerState`

Each of the four CMA sub-interfaces (`unifSpec + roSpec`, `signSpec`,
`pkSpec`) gets an inner handler that acts on `cmaInnerState` alone,
without touching the `Bool` bad flag. The bad flag is attached at the
game level via `QueryImpl.withBadFlag` (cmaReal: preserve; cmaSim on
non-sign branches: preserve) or `QueryImpl.withBadUpdate progCollision`
(cmaSim on the sign branch: OR in the programming-collision predicate).

Keeping the inner handlers bad-flag-free lets generic lemmas on
`withBadFlag` / `withBadUpdate` discharge all of the bad-preservation and
identical-until-bad obligations of the SSP bridge — no per-branch case
analysis is needed in `Sigma/SSP/Hops.lean`. -/

/-- Shared uniform-sampling + lazy-random-oracle inner handler. Uniform
queries sample freshly and leave the inner state untouched; hash queries
hit the cache on a match and cache-and-return-fresh on a miss. Shared by
`cmaReal` and `cmaSim`.

Intentionally *not* marked `@[reducible]`: we want the atomic inner
handlers to be opaque to definitional unfolding so that the cmaReal /
cmaSim wrappers stay in `*.withBadFlag` / `*.withBadUpdate` syntactic form.
This lets the simp lemmas
`QueryImpl.withBadFlag_apply_run` / `QueryImpl.withBadUpdate_apply_run`
fire when proving identical-until-bad side conditions in
`Sigma/SSP/Hops.lean`. -/
noncomputable def unifRoInnerImpl (Stmt Wit : Type) :
    QueryImpl (unifSpec + roSpec M Commit Chal)
      (StateT (cmaInnerState M Commit Chal Stmt Wit) (OracleComp unifSpec))
  | Sum.inl n => fun st => do
      let r ← (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
      pure (r, st)
  | Sum.inr mc => fun st =>
      match st.1 mc with
      | some r => pure (r, st)
      | none => do
          let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
          pure (r, st.1.cacheQuery mc r, st.2)

/-- Real-Σ-protocol signer inner handler. On a `Sign m` query, fetches
the keypair (via lazy `hr.gen` if empty), runs `σ.commit`, queries the
shared RO cache at `(m, c)` (caching on miss), runs `σ.respond`, and
returns `(c, π)`. Used by `cmaReal` only.

Kept opaque for the same simp-control reason as `unifRoInnerImpl`. -/
noncomputable def signRealInnerImpl
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl (signSpec M Commit Resp)
      (StateT (cmaInnerState M Commit Chal Stmt Wit)
        (OracleComp unifSpec)) := fun msg st => do
  let (pk, sk, kp) ← match st.2.1 with
    | some (pk, sk) => (pure (pk, sk, some (pk, sk)) :
        OracleComp unifSpec (Stmt × Wit × Option (Stmt × Wit)))
    | none => do
        let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
        pure (pk, sk, some (pk, sk))
  let (c, prvSt) ← (liftM (σ.commit pk sk) :
    OracleComp unifSpec (Commit × PrvState))
  let (ch, cache') ← match st.1 (msg, c) with
    | some r => (pure (r, st.1) :
        OracleComp unifSpec (Chal × (roSpec M Commit Chal).QueryCache))
    | none => do
        let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
        pure (r, st.1.cacheQuery (msg, c) r)
  let π ← (liftM (σ.respond pk sk prvSt ch) :
    OracleComp unifSpec Resp)
  pure ((c, π), cache', kp, st.2.2 ++ [msg])

/-- HVZK-simulator signer inner handler. On a `Sign m` query, fetches
the keypair (via lazy `hr.gen` if empty), samples a full simulated
transcript `(c, ch, π) ← simT pk`, and conditionally programs the RO:
if `(m, c)` is already cached the cache is left alone (this is the
programming-collision event, tracked externally by `progCollision`); if
`(m, c)` is fresh the cache is extended by `(m, c) ↦ ch`. Used by
`cmaSim` only.

Kept opaque for the same simp-control reason as `unifRoInnerImpl`. -/
noncomputable def signSimInnerImpl
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl (signSpec M Commit Resp)
      (StateT (cmaInnerState M Commit Chal Stmt Wit)
        (OracleComp unifSpec)) := fun msg st => do
  let (pk, kp) ← match st.2.1 with
    | some (pk, sk) => (pure (pk, some (pk, sk)) :
        OracleComp unifSpec (Stmt × Option (Stmt × Wit)))
    | none => do
        let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
        pure (pk, some (pk, sk))
  let (c, ch, π) ← (liftM (simT pk) :
    OracleComp unifSpec (Commit × Chal × Resp))
  let cache' := match st.1 (msg, c) with
    | some _ => st.1
    | none => st.1.cacheQuery (msg, c) ch
  pure ((c, π), cache', kp, st.2.2 ++ [msg])

/-- Public-key lazy-generator inner handler. On a `GetPK` query, fetches
the cached keypair if present, or runs `hr.gen` and caches it otherwise;
returns only the public component. Shared by `cmaReal` and `cmaSim`.

Kept opaque for the same simp-control reason as `unifRoInnerImpl`. -/
noncomputable def pkInnerImpl
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl (pkSpec Stmt)
      (StateT (cmaInnerState M Commit Chal Stmt Wit)
        (OracleComp unifSpec)) := fun _ st =>
  match st.2.1 with
  | some (pk, _) => pure (pk, st)
  | none => do
      let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
      pure (pk, st.1, some (pk, sk), st.2.2)

/-- Programming-collision predicate for `cmaSim`'s sign branch.

`progCollision m s (c, π)` is `true` iff the RO cache at the pre-call
state `s` already contained a value at `(m, c)` — i.e. the simulator's
programming attempt would overwrite an existing entry. This is the only
event on which `cmaReal` and `cmaSim` diverge beyond the per-step HVZK
gap, and it is exactly the SSP "bad event" for the H3 hop.

Used via `QueryImpl.withBadUpdate` to attach the bad-flag update to
`signSimInnerImpl`; see `cmaSim` below. -/
@[reducible] def progCollision {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal Stmt Wit Resp : Type} :
    (t : (signSpec M Commit Resp).Domain) →
      cmaInnerState M Commit Chal Stmt Wit →
      (signSpec M Commit Resp).Range t → Bool :=
  fun m s cπ => (s.1 (m, cπ.1)).isSome

/-! ### `cmaReal`: real CMA game

The full real-game handler is the sum of the three atomic inner handlers
along `cmaSpec = ((unifSpec + roSpec) + signSpec) + pkSpec`, lifted in one
shot through `QueryImpl.withBadFlag` so that the bad flag is threaded
through every query verbatim. The intermediate wrappers
`cmaRealUnifRoImpl`, `cmaRealSignImpl`, `cmaRealPkImpl`, `cmaRealSubImpl`
pre-apply `withBadFlag` so the bridge in `Sigma/SSP/Bridge.lean` can
factor-out the `pkSpec`-lift via `simulateQ_add_liftComp_left` once and
the `signSpec`-lift again, matching the two-level lift structure of
`signedAdv`. -/

/-- The bad-flag-free sum of the three atomic `cmaReal` inner handlers
along `cmaSpec = ((unifSpec + roSpec) + signSpec) + pkSpec`. This is the
"inner" handler that gets lifted to the full CMA state via a single
application of `QueryImpl.withBadFlag`. -/
noncomputable def cmaRealInnerImpl
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (cmaInnerState M Commit Chal Stmt Wit) (OracleComp unifSpec)) :=
  (unifRoInnerImpl M Commit Chal Stmt Wit + signRealInnerImpl M Commit Chal σ hr) +
    pkInnerImpl M Commit Chal hr

/-- The `unifSpec + roSpec`-handling portion of `cmaReal.impl`: the
inner handler `unifRoInnerImpl` lifted with the bad flag preserved. -/
@[reducible] noncomputable def cmaRealUnifRoImpl (Stmt Wit : Type) :
    QueryImpl (unifSpec + roSpec M Commit Chal)
      (StateT (cmaGameState M Commit Chal Stmt Wit) (OracleComp unifSpec)) :=
  (unifRoInnerImpl M Commit Chal Stmt Wit).withBadFlag

/-- The `signSpec`-handling portion of `cmaReal.impl`: the inner real-Σ
signer lifted with the bad flag preserved. -/
@[reducible] noncomputable def cmaRealSignImpl
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl (signSpec M Commit Resp)
      (StateT (cmaGameState M Commit Chal Stmt Wit) (OracleComp unifSpec)) :=
  (signRealInnerImpl M Commit Chal σ hr).withBadFlag

/-- The `(unifSpec + roSpec) + signSpec`-handling portion of `cmaReal.impl`,
obtained as the sum of the two finer sub-handlers. -/
@[reducible] noncomputable def cmaRealSubImpl
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl ((unifSpec + roSpec M Commit Chal) + signSpec M Commit Resp)
      (StateT (cmaGameState M Commit Chal Stmt Wit) (OracleComp unifSpec)) :=
  cmaRealUnifRoImpl M Commit Chal Stmt Wit +
    cmaRealSignImpl M Commit Chal σ hr

/-- The `pkSpec`-handling portion of `cmaReal.impl`: the inner pk handler
lifted with the bad flag preserved. -/
@[reducible] noncomputable def cmaRealPkImpl
    (hr : GenerableRelation Stmt Wit rel) :
    QueryImpl (pkSpec Stmt)
      (StateT (cmaGameState M Commit Chal Stmt Wit) (OracleComp unifSpec)) :=
  (pkInnerImpl M Commit Chal hr).withBadFlag

/-- The real CMA game. Handler is the sum of the three atomic sub-handlers
along `cmaSpec = ((unifSpec + roSpec) + signSpec) + pkSpec`, each with the
bad flag threaded verbatim. Init starts the inner state empty and the bad
flag `false`. -/
@[reducible] noncomputable def cmaReal
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    Package unifSpec (cmaSpec M Commit Chal Resp Stmt)
      (cmaGameState M Commit Chal Stmt Wit) where
  init := pure ((∅, none, []), false)
  impl := cmaRealSubImpl M Commit Chal σ hr + cmaRealPkImpl M Commit Chal hr

/-- `cmaReal.impl` factored as a single `withBadFlag` lift of the inner
handler `cmaRealInnerImpl`. Holds by case-analysis on the query variant
plus `rfl`. This alternate factorization is what enables short
identical-until-bad proofs in `Sigma/SSP/Hops.lean`: every query reduces
via `QueryImpl.withBadFlag_apply_run` to a `Prod.mk b <$>`-like shape,
from which bad-flag preservation is a `Set.mem_image` step. -/
lemma cmaReal_impl_eq_withBadFlag
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    (cmaReal M Commit Chal σ hr).impl =
      (cmaRealInnerImpl M Commit Chal σ hr).withBadFlag := by
  funext t; rcases t with ((_ | _) | _) | ⟨⟩ <;> rfl

/-- Pointwise `run`-form of `cmaReal_impl_eq_withBadFlag`: every query
branch of `cmaReal.impl` evaluated at state `(s, b)` equals the inner
handler's run-result tagged with the unchanged bad flag `b`. This is the
form actually used to drive simp in `Sigma/SSP/Hops.lean` — the
`@[reducible]` attribute on `cmaReal` would otherwise eagerly unfold
`.impl` to `cmaRealSubImpl + cmaRealPkImpl`, which blocks
`QueryImpl.withBadFlag_apply_run` from firing. -/
lemma cmaReal_impl_apply_run
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (s : cmaInnerState M Commit Chal Stmt Wit) (b : Bool) :
    (((cmaReal M Commit Chal σ hr).impl t).run (s, b)) =
      (fun (vs : (cmaSpec M Commit Chal Resp Stmt).Range t ×
          cmaInnerState M Commit Chal Stmt Wit) => (vs.1, vs.2, b)) <$>
        (((cmaRealInnerImpl M Commit Chal σ hr) t).run s) := by
  rcases t with ((_ | _) | _) | ⟨⟩ <;> rfl

/-! ### `cmaSim`: simulated CMA game

Same shape as `cmaReal`, but the sign branch is lifted through
`QueryImpl.withBadUpdate progCollision` instead of `withBadFlag`. The
predicate `progCollision` fires on exactly the programming-collision
event, OR-accumulating it into the bad flag. Every other branch is
identical to `cmaReal`'s corresponding branch. -/

/-- The simulated CMA game. Handler is the sum

  `(unifRoInnerImpl.withBadFlag
    + signSimInnerImpl.withBadUpdate progCollision)
    + pkInnerImpl.withBadFlag`

along `cmaSpec = ((unifSpec + roSpec) + signSpec) + pkSpec`. Init starts
the inner state empty and the bad flag `false`. -/
@[reducible] noncomputable def cmaSim
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    Package unifSpec (cmaSpec M Commit Chal Resp Stmt)
      (cmaGameState M Commit Chal Stmt Wit) where
  init := pure ((∅, none, []), false)
  impl :=
    ((unifRoInnerImpl M Commit Chal Stmt Wit).withBadFlag +
        (signSimInnerImpl M Commit Chal hr simT).withBadUpdate progCollision) +
      (pkInnerImpl M Commit Chal hr).withBadFlag

/-- `cmaSim.impl` on a uniform-or-RO query, pointwise-run form: runs the
shared inner handler `unifRoInnerImpl` on the inner state and tags with
the unchanged bad flag `b`. Auxiliary for bad-flag reasoning in
`Sigma/SSP/Hops.lean`. -/
lemma cmaSim_impl_unifRo_apply_run
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (t : (unifSpec + roSpec M Commit Chal).Domain)
    (s : cmaInnerState M Commit Chal Stmt Wit) (b : Bool) :
    (((cmaSim M Commit Chal hr simT).impl (Sum.inl (Sum.inl t))).run (s, b)) =
      (fun (vs : (unifSpec + roSpec M Commit Chal).Range t ×
          cmaInnerState M Commit Chal Stmt Wit) => (vs.1, vs.2, b)) <$>
        (((unifRoInnerImpl M Commit Chal Stmt Wit) t).run s) := rfl

/-- `cmaSim.impl` on a sign query, pointwise-run form: runs the HVZK
simulator `signSimInnerImpl` on the inner state and OR-updates the bad
flag with the programming-collision predicate. -/
lemma cmaSim_impl_sign_apply_run
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (m : (signSpec M Commit Resp).Domain)
    (s : cmaInnerState M Commit Chal Stmt Wit) (b : Bool) :
    (((cmaSim M Commit Chal hr simT).impl (Sum.inl (Sum.inr m))).run (s, b)) =
      (fun (vs : (signSpec M Commit Resp).Range m ×
          cmaInnerState M Commit Chal Stmt Wit) =>
        (vs.1, vs.2, b || progCollision m s vs.1)) <$>
        (((signSimInnerImpl M Commit Chal hr simT) m).run s) := rfl

/-- `cmaSim.impl` on a `pkSpec` query, pointwise-run form: runs the lazy
pk generator `pkInnerImpl` and tags with the unchanged bad flag. -/
lemma cmaSim_impl_pk_apply_run
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (s : cmaInnerState M Commit Chal Stmt Wit) (b : Bool) :
    (((cmaSim M Commit Chal hr simT).impl (Sum.inr ())).run (s, b)) =
      (fun (vs : (pkSpec Stmt).Range () ×
          cmaInnerState M Commit Chal Stmt Wit) => (vs.1, vs.2, b)) <$>
        (((pkInnerImpl M Commit Chal hr) ()).run s) := rfl

/-! ### `nma`: no-message-attack game -/

/-- The no-message-attack game. No signing oracle; only random-oracle,
programming channel (used internally by `cmaToNma`), and public-key
oracle. State is
`(roSpec M Commit Chal).QueryCache × Bool × Option (Stmt × Wit)`;
`progSpec` queries OR-update the bad flag on cache-hit.

The external NMA adversary used by H5's forking-lemma bridge interacts
with this game through only the `unifSpec + roSpec + pkSpec` sub-portion
of `nmaSpec`; `progSpec` is private to the CMA-to-NMA reduction. -/
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

/-! ### `cmaToNma`: CMA-to-NMA reduction -/

/-- The CMA-to-NMA reduction package, parameterized by the HVZK simulator
`simT`. Forwards uniform sampling, `roSpec` hash queries, and `pkSpec`
public-key queries unchanged; on a `Sign m` query, samples a full
simulator transcript and installs the FS challenge into the RO via
`progSpec`. State is just `List M` (the signed-message log, read out
post-run by the freshness check in `Sigma/SSP/Bridge.lean`). -/
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
