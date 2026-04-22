/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.SSP.Games
import VCVio.SSP.Advantage

/-!
# Bridge between `unforgeableExp` and `cmaReal.runProb`

The adapter layer that ties the existing `SignatureAlg.unforgeableAdv`-based
EUF-CMA experiment for the Fiat-Shamir scheme to the SSP-style `cmaReal`
game from `Sigma/SSP/Games.lean`. This file contributes hops H1 and H2 of
the SSP plan in `.ignore/fs-ssp-plan.md` §5:

* H1 (drop-fresh): wraps `SignatureAlg.unforgeableAdv.advantage_le_unforgeableExpNoFresh`
  for the FS scheme.
* H2 (`unforgeableExp` ↔ `cmaReal.runProb`): expresses the unforgeability
  experiment as `cmaReal.runState`-with-post-check by lifting the source
  adversary into `OracleComp cmaSpec` via the standard SSP `SubSpec`
  embedding `(unifSpec + roSpec) + signSpec ⊂ₒ cmaSpec` and reading the
  signed-message log out of `cmaReal`'s state.

## Headline statements

* `signedAdv` — the SSP-side adversary obtained from a CMA `unforgeableAdv`.
  Queries `pkSpec` first, lifts the source adversary's main routine into
  `cmaSpec`, then runs FS verification and returns
  `((forgery), verified)`.
* `cmaRealRun` — the joint output of running `cmaReal` against `signedAdv`,
  bundled with the signed-message log read out of `cmaReal`'s state.
* `bridge_evalDist_cmaRealRun` — the equality
  `evalDist (cmaRealRun) = evalDist (the joint of unforgeableExp's body)`.
* `cmaRealAdvantage_eq_unforgeableExp` — the projection of the joint bridge
  to the freshness-and-verified bool, matching `unforgeableExp`'s output.
* `cmaRealNoFreshAdvantage_eq_unforgeableExpNoFresh` — the projection of
  the joint bridge to the verified-only bool.
* `unforgeableAdv.advantage_le_runProb_cmaRealNoFresh` — the H1+H2
  composition: `adv.advantage ≤ Pr[cmaReal wins, ignoring freshness]`.

The detailed equality `bridge_evalDist_cmaRealRun` is presently `sorry`'d;
its proof is the main content of Phase D1.b. It reduces to:

1. Pull the keypair sampling out of `cmaReal`'s lazy `pkSpec` handler via
   `Package.run`'s definition + the `signedAdv`-queries-`GetPK`-first
   structure (so the lazy keygen happens at the start, matching
   `unforgeableExp`'s eager keygen).
2. Match the random-oracle handling: `cmaReal`'s lazy `roSpec` handler
   coincides with `runtime`'s `randomOracle` impl, since both use the same
   `cacheQuery`-on-miss / cached-on-hit logic.
3. Match the signing oracle: `cmaReal`'s `signSpec` handler runs the
   actual FS signing through the same RO cache as the adversary's direct
   hash queries. The OLD `unforgeableExp` does the same via
   `signingOracle pk sk` in a `WriterT` log; the equivalence is the FS
   instance of `Security.lean`'s
   `map_run_withLogging_inputs_eq_run_signedAppend`.
4. Match the verify call: both sides issue one `Hash (msg, c)` query
   through the same RO cache, then run the deterministic `σ.verify`.
-/

universe u v

open OracleSpec OracleComp ProbComp VCVio.SSP

namespace FiatShamir.SSP

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit]
variable [SampleableType Chal]

/-! ### SSP-side adversary -/

/-- Lift a CMA-style `unforgeableAdv` for the Fiat-Shamir scheme into an
adversary against the SSP `cmaReal` game.

The wrapper:
1. Issues a `pkSpec` query to obtain the public key from `cmaReal`'s
   lazily-sampled keypair.
2. Lifts the source adversary's `main pk` from
   `OracleComp ((unifSpec + roSpec) + signSpec) (M × (Commit × Resp))`
   into `OracleComp cmaSpec ...` via the standard
   `(unifSpec + roSpec) + signSpec ⊂ₒ cmaSpec` `SubSpec` instance.
3. Runs FS verification on the forgery, which issues one further
   `roSpec` (`Hash (msg, c)`) query through the same RO cache that the
   signing handler and the adversary's direct hash queries use.
4. Returns the forgery paired with the verification bit; the freshness
   post-check is read off `cmaReal`'s signed-message log externally
   (see `cmaRealRun`). -/
@[reducible] noncomputable def signedAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) ((M × (Commit × Resp)) × Bool) := do
  let pk ← (((cmaSpec M Commit Chal Resp Stmt).query (Sum.inr ())) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Stmt)
  let (msg, sig) ← (liftM (adv.main pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)))
  let verified ← (liftM
    ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
      pk msg sig) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure ((msg, sig), verified)

/-! ### Joint output of `cmaReal` -/

/-- Run `cmaReal` against `signedAdv` and pack the resulting forgery,
verification bit, and signed-message log into a single `ProbComp`.

The signed-message log lives in the third component of `cmaReal`'s state
(`(cache, Option (pk, sk), List M)`); it is the freshness witness that
the OLD `unforgeableExp` carries in a `WriterT` instead. -/
@[reducible] noncomputable def cmaRealRun
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    ProbComp ((M × (Commit × Resp)) × Bool × List M) := do
  let p ← (cmaReal M Commit Chal σ hr).runState (signedAdv σ hr M adv)
  pure (p.1.1, p.1.2, p.2.2.2)

/-! ### Bridge equalities (Phase D1.b)

`cmaReal.impl` is, by construction in `Sigma/SSP/Games.lean`, the sum
`cmaRealSubImpl σ hr + cmaRealPkImpl hr` along the decomposition
`cmaSpec = (unifSpec + roSpec + signSpec) + pkSpec`. The `cmaRealSubImpl`
half handles the parts the adversary drives (uniform sampling, hash queries,
signing that internally hits the RO cache); the `cmaRealPkImpl` half
handles the public-key oracle (lazy keypair sampling). This factoring lets
the bridge proof apply `simulateQ_add_liftComp_left` directly to
`simulateQ cmaReal.impl (liftM oa)` for an adversary `oa` that does not
touch `pkSpec`. -/

/-- The headline bridge: the joint distribution of `cmaRealRun` matches the
joint distribution of the `unforgeableExp` body before the final freshness
check. Phase D1.b will replace the `sorry` with the structural proof
sketched in the module docstring; the statement is what downstream phases
consume. -/
theorem bridge_evalDist_cmaRealRun
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    evalDist (cmaRealRun σ hr M adv) =
      (FiatShamir.runtime M).evalDist (do
        let (pk, sk) ←
          (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
            σ hr M).keygen
        let impl :
            QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ (Commit × Resp)))
              (WriterT (QueryLog (M →ₒ (Commit × Resp)))
                (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) :=
          (HasQuery.toQueryImpl
              (spec := unifSpec + (M × Commit →ₒ Chal))
              (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Commit × Resp)))
              (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) +
            (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
              σ hr M).signingOracle pk sk
        let sim_adv :
            WriterT (QueryLog (M →ₒ (Commit × Resp)))
              (OracleComp (unifSpec + (M × Commit →ₒ Chal))) (M × (Commit × Resp)) :=
          simulateQ impl (adv.main pk)
        let ((msg, sig), log) ← sim_adv.run
        let verified ←
          (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
            σ hr M).verify pk msg sig
        pure ((msg, sig), verified, log.map (fun e => e.1))) := by
  sorry

/-! ### Corollaries: scalar-bool projections -/

/-- Project the joint bridge to the freshness-and-verified bool: matches
`unforgeableExp`'s output. -/
theorem cmaRealAdvantage_eq_unforgeableExp
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    Pr[= true |
        (fun p : (M × (Commit × Resp)) × Bool × List M =>
          !(p.2.2.contains p.1.1) && p.2.1) <$>
            cmaRealRun σ hr M adv] =
      adv.advantage (FiatShamir.runtime M) := by
  sorry

/-- Project the joint bridge to the verified-only bool: matches
`unforgeableExpNoFresh`'s output. -/
theorem cmaRealNoFreshAdvantage_eq_unforgeableExpNoFresh
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    Pr[= true |
        (fun p : (M × (Commit × Resp)) × Bool × List M => p.2.1) <$>
            cmaRealRun σ hr M adv] =
      Pr[= true | SignatureAlg.unforgeableExpNoFresh
        (FiatShamir.runtime M) adv] := by
  sorry

/-! ### Phase D2: H1 + H2 composition -/

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M] [DecidableEq Commit] in
/-- The `runtime`-side instance of `SignatureAlg.unforgeableAdv.advantage_le_unforgeableExpNoFresh`,
applied to the Fiat-Shamir scheme. This is hop H1 of the SSP plan: the CMA
advantage is bounded above by the freshness-dropped no-fresh experiment. -/
theorem cma_advantage_le_unforgeableExpNoFresh
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    adv.advantage (FiatShamir.runtime M) ≤
      Pr[= true | SignatureAlg.unforgeableExpNoFresh
        (FiatShamir.runtime M) adv] :=
  SignatureAlg.unforgeableAdv.advantage_le_unforgeableExpNoFresh
    (FiatShamir.runtime M)
    (fun {_ _} f mx => FiatShamir.runtime_evalDist_bind_pure M mx f) adv

/-- Composition of H1 (drop-fresh) and H2 (the bridge): the CMA advantage is
bounded by the probability that `cmaReal` accepts a forgery, ignoring
freshness. This is the entry point for the rest of the SSP hop chain
(`cmaReal → cmaSim → nma → Fork`). -/
theorem cma_advantage_le_runProb_cmaRealNoFresh
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    adv.advantage (FiatShamir.runtime M) ≤
      Pr[= true |
        (fun p : (M × (Commit × Resp)) × Bool × List M => p.2.1) <$>
            cmaRealRun σ hr M adv] := by
  rw [cmaRealNoFreshAdvantage_eq_unforgeableExpNoFresh]
  exact cma_advantage_le_unforgeableExpNoFresh σ hr M adv

end FiatShamir.SSP
