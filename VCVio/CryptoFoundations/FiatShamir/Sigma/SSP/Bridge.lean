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
* `cmaRealNoFreshAdvantage_eq_unforgeableExpNoFresh` — hop H2 of the SSP
  plan (`Pr[unforgeableExpNoFresh] = Pr[cmaReal accepts forgery]`, the
  projection to the verified bit, no freshness check).
* `unforgeableAdv.advantage_le_runProb_cmaRealNoFresh` — the H1+H2
  composition: `adv.advantage ≤ Pr[cmaReal wins, ignoring freshness]`.

`cmaRealNoFreshAdvantage_eq_unforgeableExpNoFresh` is presently `sorry`'d;
the proof reduces to:

1. Pull the keypair sampling out of `cmaReal`'s lazy `pkSpec` handler via
   `Package.run`'s definition + the `signedAdv`-queries-`GetPK`-first
   structure (so the lazy keygen happens at the start, matching
   `unforgeableExp`'s eager keygen). This step is captured in the private
   lemma `cmaRealRun_eq_keygen_bind`.
2. Match the random-oracle handling: `cmaReal`'s lazy `roSpec` handler
   coincides with `runtime`'s `randomOracle` impl, since both use the same
   `cacheQuery`-on-miss / cached-on-hit logic.
3. Match the signing oracle: `cmaReal`'s `signSpec` handler runs the
   actual FS signing through the same RO cache as the adversary's direct
   hash queries. The OLD `unforgeableExp` does the same via
   `signingOracle pk sk` in a `WriterT` log; the equivalence is the FS
   instance of `Security.lean`'s
   `map_run_withLogging_inputs_eq_run_signedAppend`. For the no-fresh
   projection the `WriterT` log is discarded, so we only need the
   distribution of the adversary's output + final cache to coincide.
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

The signed-message log lives in the third component of `cmaReal`'s inner
state (`cmaInnerState = cache × Option (pk, sk) × List M`), under the
top-level bad-flag slot of `cmaGameState`; it is the freshness witness
that the OLD `unforgeableExp` carries in a `WriterT` instead. -/
@[reducible] noncomputable def cmaRealRun
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    ProbComp ((M × (Commit × Resp)) × Bool × List M) := do
  let p ← (cmaReal M Commit Chal σ hr).runState (signedAdv σ hr M adv)
  pure (p.1.1, p.1.2, p.2.1.2.2)

/-! ### Bridge equalities (Phase D1.b)

`cmaReal.impl` is, by construction in `Sigma/SSP/Games.lean`, the sum
`(cmaRealUnifRoImpl + cmaRealSignImpl) + cmaRealPkImpl` along the
decomposition `cmaSpec = ((unifSpec + roSpec) + signSpec) + pkSpec`. The
bridge proof uses this factoring to strip the two lifts in `signedAdv`:
`adv.main pk` is lifted through `+ pkSpec`, and Fiat-Shamir's `verify` is
lifted through `+ signSpec` on top of that; applying
`simulateQ_add_liftComp_left` twice reduces the simulations to
`simulateQ cmaRealSubImpl (adv.main pk)` and
`simulateQ cmaRealUnifRoImpl (verify pk msg sig)` respectively. -/

/-! #### Factor-out-keygen helpers

The first step of the bridge strips the `pkSpec` query from the start of
`signedAdv`. Since `cmaReal` starts with no keypair (`none` in its state),
the first query forces the lazy generator to run, and every subsequent
query sees `some (pk, sk)`; the keypair never changes afterwards. We
capture this in `cmaRealRun_eq_keygen_bind` below. -/

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] in
/-- Running `cmaRealPkImpl` from the empty keypair is `hr.gen` followed by a
pure state update. The top-level bad flag is unchanged. -/
private lemma cmaRealPkImpl_empty_run
    (cache : (roSpec M Commit Chal).QueryCache) (log : List M) (bad : Bool) :
    (cmaRealPkImpl M Commit Chal hr ()).run ((cache, none, log), bad) =
      (fun p : Stmt × Wit => (p.1, (cache, some (p.1, p.2), log), bad)) <$> hr.gen := by
  simp [cmaRealPkImpl, StateT.run, map_eq_bind_pure_comp]

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] in
/-- Running `cmaRealPkImpl` with a pre-existing keypair just returns the public
key, leaving state untouched. -/
private lemma cmaRealPkImpl_some_run
    (cache : (roSpec M Commit Chal).QueryCache) (pk : Stmt) (sk : Wit)
    (log : List M) (bad : Bool) :
    (cmaRealPkImpl M Commit Chal hr ()).run ((cache, some (pk, sk), log), bad) =
      pure (pk, (cache, some (pk, sk), log), bad) := by
  simp [cmaRealPkImpl, StateT.run]

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] in
/-- Threading a continuation through `cmaRealPkImpl` from the empty keypair state
extracts the `hr.gen` step. -/
private lemma cmaRealPkImpl_bind_run_empty {α : Type}
    (f : Stmt → StateT (cmaGameState M Commit Chal Stmt Wit)
      (OracleComp unifSpec) α)
    (cache : (roSpec M Commit Chal).QueryCache) (log : List M) (bad : Bool) :
    (cmaRealPkImpl M Commit Chal hr () >>= f) ((cache, none, log), bad) =
      hr.gen >>= fun ps : Stmt × Wit => f ps.1 ((cache, some ps, log), bad) := by
  change (StateT.bind _ _) _ = _
  simp [cmaRealPkImpl, StateT.bind]

/-- The "post-keygen" portion of `signedAdv`: the adversary's main routine
followed by FS verification, with `pk` already fixed. All queries are through
`cmaSpec`; the `pkSpec` summand is never touched. -/
@[reducible] noncomputable def postKeygenAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) ((M × (Commit × Resp)) × Bool) := do
  let (msg, sig) ← (liftM (adv.main pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)))
  let verified ← (liftM
    ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
      pk msg sig) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure ((msg, sig), verified)

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The first `pkSpec` query in `signedAdv` forces `cmaReal` to run its lazy
keygen, leaving every subsequent query to see a stable `some (pk, sk)` in the
state slot. The rest of `signedAdv` (the adversary's main routine plus FS
verification) never touches `pkSpec`, so every subsequent query is handled
by `cmaRealSubImpl = cmaRealUnifRoImpl + cmaRealSignImpl`. -/
private lemma cmaRealRun_eq_keygen_bind
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    cmaRealRun σ hr M adv =
      (hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
        (simulateQ (cmaReal M Commit Chal σ hr).impl
            (postKeygenAdv σ hr M adv ps.1)).run ((∅, some ps, []), false) >>=
          fun p => pure (p.1.1, p.1.2, p.2.1.2.2) := by
  unfold cmaRealRun signedAdv Package.runState postKeygenAdv
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, QueryImpl.add_apply_inr,
    id_map, StateT.run, pure_bind]
  change (cmaRealPkImpl M Commit Chal hr () >>= _) ((∅, none, []), false) >>= _ = _ >>= _
  rw [cmaRealPkImpl_bind_run_empty (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
    _ ∅ [] false]
  simp only [bind_assoc]

/-- Hop **H2** (freshness-dropped): the probability that `cmaReal` accepts
the adversary's forgery (without the freshness post-check) equals the
probability that the FS freshness-dropped experiment accepts. This is the
one equality consumed by `cma_advantage_le_runProb_cmaRealNoFresh` below;
the with-freshness and full-joint variants are not needed for the H1-H5
chain and are therefore not stated. -/
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
